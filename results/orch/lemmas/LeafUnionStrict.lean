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

section Main

variable {n : ℕ} {C : Circuit}


lemma agree (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (x y : Fin n → Bool)
    (hxy : ∀ i (hi : i < n), i ∈ (slots n C j).image (slotW C) → x ⟨i, hi⟩ = y ⟨i, hi⟩) :
    ∀ g ∈ PEqualNP.Core.coneSet n C j, W C n x (n + g) = W C n y (n + g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hK
  have hg := K_lt hC hj hK
  have hop : ∀ b : Fin 2, W C n x (opnd C g b) = W C n y (opnd C g b) := by
    intro b
    by_cases hn : opnd C g b < n
    · rw [W_input C n x _ hn, W_input C n y _ hn]
      apply hxy
      exact Finset.mem_image.2 ⟨(g, b), Finset.mem_product.2 ⟨hK, Finset.mem_univ _⟩, rfl⟩
    · obtain ⟨hK', hlt⟩ := K_opnd hC hj hK b (by omega)
      have he : n + (opnd C g b - n) = opnd C g b := by omega
      rw [← he]
      exact ih _ hlt hK'
  rw [W_gate C n x g hg (hC.2.1 g hg), W_gate C n y g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil, hop 0, hop 1]

lemma pairInput_comm (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w; unfold pairInput; simp [or_comm]


lemma end_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hbelow : BelowF G C j) {u v : Fin n} (huv : G.Adj u v)
    (hacc : gateVal n C j (pairInput u v) = true) :
    u.val ∈ (slots n C j).image (slotW C) := by
  by_contra hu
  have hjK : j ∈ PEqualNP.Core.coneSet n C j := Finset.mem_insert_self _ _
  have hag := agree hC hj (pairInput u v) (fun w => decide (w = v)) (by
    intro i hi hI
    have hne : (⟨i, hi⟩ : Fin n) ≠ u := by
      rintro rfl; exact hu hI
    unfold pairInput
    simp [hne]) j hjK
  have hy : gateVal n C j (fun w => decide (w = v)) = true := by
    have e1 : gateVal n C j (fun w => decide (w = v)) = W C n (fun w => decide (w = v)) (n + j) := rfl
    have e2 : gateVal n C j (pairInput u v) = W C n (pairInput u v) (n + j) := rfl
    rw [e1, ← hag, ← e2]; exact hacc
  have := hbelow _ hy
  unfold graphFun at this
  simp at this

lemma core_leaf_count (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC : IsAO2 n C)
    {j : ℕ} (hcore : PEqualNP.Core.IsCore G C j) :
    (Finset.univ.filter (fun w : Fin n => w.val ∈ (slots n C j).image (slotW C))).card ≤
      (PEqualNP.Core.coneSet n C j).card := by
  classical
  obtain ⟨hj, ⟨hbelow, _⟩, _, u0, v0, huv0, hacc0, hrt⟩ := hcore
  set K := PEqualNP.Core.coneSet n C j with hKdef
  set I := (slots n C j).image (slotW C) with hIdef
  have hjK : j ∈ K := Finset.mem_insert_self _ _
  have hS : (Finset.univ.filter (fun w : Fin n => w.val ∈ I)).card ≤
      (I.filter (fun w => w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun w : Fin n => w.val)
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨hw, w.isLt⟩
    · intro a _ b _ h; exact Fin.ext h
  have hG : (K.erase j).card ≤ (I.filter (fun w => ¬ w < n)).card := by
    apply Finset.card_le_card_of_injOn (fun g => n + g)
    · intro g hg
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hg
      obtain ⟨h, hh, b, hb⟩ := K_cover hC hj hg.1 hg.2
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      refine ⟨Finset.mem_image.2 ⟨(h, b), Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩, hb⟩, ?_⟩
      omega
    · intro a _ b _ h; simp only at h; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
  have hslots : (slots n C j).card = K.card * 2 := by
    unfold slots; rw [Finset.card_product]; simp [hKdef]
  have hnotinj : ¬ Set.InjOn (slotW C) (slots n C j) := by
    intro hinj
    have hjK' : j ∈ PEqualNP.Core.coneSet n C j := hjK
    have hne := vec_ne hC u0 v0 (n + j) (by omega) hacc0
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    have hle := vec_le_one hC hj hinj u0.val v0.val u0.isLt v0.isLt j hjK' w hw
    apply absurd hrt
    unfold PEqualNP.Core.ReadTwiceAt readsAtMost
    simp only [Bool.not_eq_false]
    rw [List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [List.all_eq_true]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have := hle i
    rw [List.getD_eq_getElem _ _ hi] at this
    simpa using this
  have hlt : I.card < (slots n C j).card :=
    lt_of_le_of_ne Finset.card_image_le (fun h => hnotinj (Finset.card_image_iff.1 h))
  have herase := Finset.card_erase_of_mem hjK
  have hpos : 0 < K.card := Finset.card_pos.2 ⟨j, hjK⟩
  omega
end Main

def allSlots (U : Finset ℕ) : Finset (ℕ × Fin 2) := U ×ˢ Finset.univ

def allInputs (n : ℕ) (C : Circuit) (U : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ (allSlots U).image (slotW C)

lemma mem_allInputs {n : ℕ} {C : Circuit} {U : Finset ℕ} {v : Fin n} :
    v ∈ allInputs n C U ↔ ∃ g ∈ U, ∃ b : Fin 2, opnd C g b = v.val := by
  simp only [allInputs, Finset.mem_univ,
    Finset.mem_image, allSlots, Finset.mem_product, Prod.exists, slotW]
  simp [slotW]

lemma allInputs_union {n : ℕ} (C : Circuit) (U K : Finset ℕ) :
    allInputs n C (U ∪ K) = allInputs n C U ∪ allInputs n C K := by
  ext v
  simp only [mem_allInputs, Finset.mem_union]
  aesop

lemma allInputs_mono {n : ℕ} (C : Circuit) {U K : Finset ℕ} (h : U ⊆ K) :
    allInputs n C U ⊆ allInputs n C K := by
  intro v hv
  obtain ⟨g, hg, b, hb⟩ := mem_allInputs.mp hv
  exact mem_allInputs.mpr ⟨g, h hg, b, hb⟩

lemma cone_subset_of_mem {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    {i j : ℕ} (hj : j < C.gates.length) (hij : i ∈ PEqualNP.Core.coneSet n C j) :
    PEqualNP.Core.coneSet n C i ⊆ PEqualNP.Core.coneSet n C j := by
  have hi := K_lt hC hj hij
  intro g hg
  obtain ⟨hgl, hr⟩ := (mem_coneSet n C hC.2.1 hi g).mp hg
  exact K_reach hC hj hij hr hgl

lemma cone_crosses {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (U : Finset ℕ)
    (i : ℕ) (hiU : i ∈ U) : ∀ j, j < C.gates.length → j ∉ U →
    i ∈ PEqualNP.Core.coneSet n C j →
    ∃ g ∈ PEqualNP.Core.coneSet n C j, g ∉ U ∧
      ∃ k ∈ U, ∃ b : Fin 2, opnd C g b = n + k := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hjU hij
  have hi := K_lt hC hj hij
  have hne : i ≠ j := fun h => hjU (h ▸ hiU)
  have hc : InCone n C i j := by
    rcases Finset.mem_insert.mp hij with h | h
    · exact (hne h).elim
    · exact (Finset.mem_filter.mp h).2
  obtain ⟨w, hw, hnw, hwc⟩ := (inCone_iff n C hC.2.1 hj).mp hc
  have hwl := hC.2.1 j hj w hw
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, w = opnd C j b := by
    rw [ao_inputs hC hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  by_cases hwU : w - n ∈ U
  · exact ⟨j, Finset.mem_insert_self _ _, hjU, w - n, hwU, b, by omega⟩
  · have hwi : i ∈ PEqualNP.Core.coneSet n C (w - n) := by
      rcases hwc with h | h
      · exact (hwU (h ▸ hiU)).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h⟩)
    obtain ⟨g, hg, hgU, k, hk, b', hb'⟩ := ih (w - n) (by omega) (by omega) hwU hwi
    have hwj : w - n ∈ PEqualNP.Core.coneSet n C j := by
      rw [hb] at hnw ⊢
      exact (K_opnd hC hj (Finset.mem_insert_self _ _) b hnw).1
    exact ⟨g, cone_subset_of_mem hC hj hwj hg, hgU, k, hk, b', hb'⟩

lemma fresh_inputs_le_fresh_gates {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (U : Finset ℕ)
    (closed : ∀ g ∈ U, ∀ b : Fin 2, n ≤ opnd C g b → opnd C g b - n ∈ U)
    {j : ℕ} (hj : j < C.gates.length) (hjU : j ∉ U)
    (shared : (PEqualNP.Core.coneSet n C j ∩ U).Nonempty) :
    (allInputs n C (PEqualNP.Core.coneSet n C j) \ allInputs n C U).card ≤
      (PEqualNP.Core.coneSet n C j \ U).card := by
  classical
  let K := PEqualNP.Core.coneSet n C j
  let J := K \ U
  let I := (allSlots J).image (slotW C)
  obtain ⟨i, hi⟩ := shared
  obtain ⟨g, hgK, hgU, k, hkU, b, hb⟩ :=
    cone_crosses hC U i (Finset.mem_inter.mp hi).2 j hj hjU (Finset.mem_inter.mp hi).1
  have hkJ : k ∉ J := fun h => (Finset.mem_sdiff.mp h).2 hkU
  have hjJ : j ∈ J := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hjU⟩
  have hS : (allInputs n C K \ allInputs n C U).card ≤ (I.filter fun w => w < n).card := by
    apply Finset.card_le_card_of_injOn (fun v : Fin n => v.val)
    · intro v hv
      obtain ⟨hvK, hvU⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨g', hg'K, b', hb'⟩ := mem_allInputs.mp hvK
      have hg'U : g' ∉ U := fun h => hvU (mem_allInputs.mpr ⟨g', h, b', hb'⟩)
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨Finset.mem_image.mpr ⟨(g', b'),
        Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hg'K, hg'U⟩, Finset.mem_univ _⟩,
          hb'⟩, v.isLt⟩
    · intro a _ b _ h
      exact Fin.ext h
  have hG : (insert k (J.erase j)).card ≤ (I.filter fun w => ¬ w < n).card := by
    apply Finset.card_le_card_of_injOn (fun g' => n + g')
    · intro g' hg'
      have named : n + g' ∈ I := by
        rcases Finset.mem_insert.mp hg' with h | h
        · subst g'
          exact Finset.mem_image.mpr ⟨(g, b),
            Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hgK, hgU⟩, Finset.mem_univ _⟩, hb⟩
        · obtain ⟨hne, hg'J⟩ := Finset.mem_erase.mp h
          obtain ⟨h, hhK, b', hb'⟩ := K_cover hC hj (Finset.mem_sdiff.mp hg'J).1 hne
          have hhU : h ∉ U := by
            intro hhU
            have hx := closed h hhU b' (by omega)
            rw [hb', Nat.add_sub_cancel_left] at hx
            exact (Finset.mem_sdiff.mp hg'J).2 hx
          exact Finset.mem_image.mpr ⟨(h, b'),
            Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hhK, hhU⟩, Finset.mem_univ _⟩, hb'⟩
      exact Finset.mem_filter.mpr ⟨named, by dsimp; omega⟩
    · intro a _ b _ h
      simp only at h
      omega
  have hGcard : (insert k (J.erase j)).card = J.card := by
    rw [Finset.card_insert_of_notMem (fun h => hkJ (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hjJ]
    have := Finset.card_pos.mpr ⟨j, hjJ⟩
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
  have hslots : (allSlots J).card = J.card * 2 := by simp [allSlots]
  have himage : I.card ≤ (allSlots J).card := Finset.card_image_le
  change (allInputs n C K \ allInputs n C U).card ≤ J.card
  omega

lemma core_family_leaf_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C) (M : Finset ℕ)
    (hM : ∀ j ∈ M, PEqualNP.Core.IsCore G C j) :
    (allInputs n C (M.biUnion (PEqualNP.Core.coneSet n C))).card ≤
      (M.biUnion (PEqualNP.Core.coneSet n C)).card := by
  classical
  induction M using Finset.induction_on with
  | empty => simp [allInputs, allSlots]
  | @insert j M hjM ih =>
    have hj := hM j (Finset.mem_insert_self _ _)
    have hM' : ∀ i ∈ M, PEqualNP.Core.IsCore G C i :=
      fun i hi => hM i (Finset.mem_insert_of_mem hi)
    have hcount := ih hM'
    let U := M.biUnion (PEqualNP.Core.coneSet n C)
    let K := PEqualNP.Core.coneSet n C j
    change (allInputs n C U).card ≤ U.card at hcount
    have closed : ∀ g ∈ U, ∀ b : Fin 2, n ≤ opnd C g b → opnd C g b - n ∈ U := by
      intro g hg b hb
      obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.mp hg
      exact Finset.mem_biUnion.mpr ⟨i, hi, (K_opnd hC (hM' i hi).1 hgi b hb).1⟩
    have fresh : (allInputs n C K \ allInputs n C U).card ≤ (K \ U).card := by
      by_cases hjU : j ∈ U
      · obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hjU
        have hKU : K ⊆ U := by
          intro g hg
          exact Finset.mem_biUnion.mpr ⟨i, hi,
            cone_subset_of_mem hC (hM' i hi).1 hji hg⟩
        have hinput := allInputs_mono (n := n) C hKU
        rw [Finset.sdiff_eq_empty_iff_subset.mpr hinput]
        simp
      · by_cases shared : (K ∩ U).Nonempty
        · exact fresh_inputs_le_fresh_gates hC U closed hj.1 hjU shared
        · have disjoint : Disjoint K U := Finset.disjoint_left.mpr (by
            intro i hiK hiU
            exact shared ⟨i, Finset.mem_inter.mpr ⟨hiK, hiU⟩⟩)
          rw [Finset.sdiff_eq_self_of_disjoint disjoint]
          have hsmall : (allInputs n C K).card ≤ K.card := by
            convert core_leaf_count G hC hj using 1
            congr 1
          exact Nat.le_trans (Finset.card_le_card Finset.sdiff_subset) hsmall
    rw [Finset.biUnion_insert]
    change (allInputs n C (K ∪ U)).card ≤ (K ∪ U).card
    rw [allInputs_union]
    calc
      (allInputs n C K ∪ allInputs n C U).card =
          (allInputs n C K \ allInputs n C U).card + (allInputs n C U).card :=
        (Finset.card_sdiff_add_card _ _).symm
      _ ≤ (K \ U).card + U.card := Nat.add_le_add fresh hcount
      _ = (K ∪ U).card := Finset.card_sdiff_add_card _ _

lemma core_family_endpoints_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C) (M : Finset ℕ)
    (hM : ∀ j ∈ M, PEqualNP.Core.IsCore G C j) :
    ((M.biUnion (gammaE G C)).biUnion Sym2.toFinset).card ≤
      (M.biUnion (PEqualNP.Core.coneSet n C)).card := by
  classical
  apply le_trans ?_ (core_family_leaf_count G C hC M hM)
  apply Finset.card_le_card
  intro v hv
  obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
  have hcore := hM j hj
  obtain ⟨heG, a, b, rfl, hab⟩ := Finset.mem_filter.mp hej
  have hadj : G.Adj a b := by simpa using heG
  have slot : v.val ∈ (slots n C j).image (slotW C) := by
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl | rfl
    · exact end_mem G hC hcore.1 hcore.2.1.1 hadj hab
    · exact end_mem G hC hcore.1 hcore.2.1.1 hadj.symm
        (by rw [pairInput_comm]; exact hab)
  obtain ⟨⟨g, b⟩, hgb, heq⟩ := Finset.mem_image.mp slot
  exact mem_allInputs.mpr ⟨g,
    Finset.mem_biUnion.mpr ⟨j, hj, (Finset.mem_product.mp hgb).1⟩, b, heq⟩

lemma maximal_core_endpoints_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C) :
    (((PEqualNP.Core.maximalCores G C).biUnion (gammaE G C)).biUnion Sym2.toFinset).card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card := by
  apply core_family_endpoints_count G C hC
  intro j hj
  exact (Finset.mem_filter.mp hj).2.1

end PEqualNP.Outside.L_meta_2962_aux.StrictLeaf
