import PEqualNP.Defs

-- Fold and count-vector lemmas adapted from ReadTwoBridge and LeafBound.

namespace PEqualNP.Outside.L_meta_2585.CleanNF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.CircuitMoves

theorem foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

theorem foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

theorem foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
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

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl
      (fun R g => R ++ [rvG S k (g.inputs.map fun i => R.getD i []) g])
      ((List.range n).map (leafVectors S k)) := rfl

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem mem_insertNew {B : List (List ℕ)} {v a : List ℕ} :
    v ∈ insertNew B a ↔ v ∈ B ∨ v = a := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp

theorem mem_foldl_insertNew (l acc : List (List ℕ)) (v : List ℕ) :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, mem_insertNew]; simp; tauto

theorem mem_orFold (ins : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ B ∈ ins, v ∈ B := by
  induction ins generalizing acc with
  | nil => simp
  | cons B ins ih => rw [List.foldl_cons, ih, mem_foldl_insertNew]; simp; tauto

theorem mem_andStep (k : ℕ) (P Q : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k P Q ↔ ∃ a ∈ P, ∃ b ∈ Q, v = capAdd k a b := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

variable {n : Nat} {C : Circuit}

theorem list_two {l : List ℕ} (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  match l, h with
  | [a, b], _ => rfl

theorem ao_inputs (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).inputs = [opnd C g 0, opnd C g 1] := by
  have hl : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq C g hg]; exact hC.2.2 _ (List.getElem_mem hg)
  exact list_two hl

theorem ao_op (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
  rw [gateAt_eq C g hg]; exact hC.1 _ (List.getElem_mem hg)

theorem opnd_mem (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := by
  rw [ao_inputs hC hg]; fin_cases b <;> simp

theorem opnd_lt (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b < n + g := hC.2.1 g hg _ (opnd_mem hC hg b)

abbrev AV (n : ℕ) (C : Circuit) (k : ℕ) (S : List ℕ) (x : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD x []

theorem AV_input (k : ℕ) (S : List ℕ) (x : ℕ) (hx : x < n) :
    AV n C k S x = leafVectors S k x := by
  unfold AV
  rw [rv_eq, foldl_snoc_init _ _ _ _ _ (by simpa using hx)]
  simp [List.getD_eq_getElem?_getD, hx]

theorem AV_gate (k : ℕ) (S : List ℕ) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    AV n C k S (n + j) = rvG S k ((gateAt C j).inputs.map (AV n C k S)) (gateAt C j) := by
  unfold AV
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (rvG S k) [] ((List.range n).map (leafVectors S k)) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_map, List.length_range] at this
  rw [rv_eq, this]

theorem mem_rvG_or (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.or)
    (v : List ℕ) : v ∈ rvG S k [A, B] g ↔ v ∈ A ∨ v ∈ B := by
  unfold rvG
  rw [hg]
  simp only
  rw [mem_orFold]
  simp

theorem mem_rvG_and (S : List ℕ) (k : ℕ) (A B : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.and)
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

theorem gate_vec (hC : IsAO2 n C) (k : ℕ) (S : List ℕ) {g : ℕ} (hg : g < C.gates.length) (v : List ℕ) :
    v ∈ AV n C k S (n + g) ↔
      ((gateAt C g).op = GateOp.or ∧ (v ∈ AV n C k S (opnd C g 0) ∨ v ∈ AV n C k S (opnd C g 1))) ∨
      ((gateAt C g).op = GateOp.and ∧ ∃ a ∈ AV n C k S (opnd C g 0), ∃ b ∈ AV n C k S (opnd C g 1),
        v = capAdd k (capAdd k (S.map fun _ => 0) a) b) := by
  rw [AV_gate k S g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil]
  rcases ao_op hC hg with h | h
  · rw [mem_rvG_and _ _ _ _ _ h]; simp [h]
  · rw [mem_rvG_or _ _ _ _ _ h]; simp [h]

abbrev W (C : Circuit) (n : Nat) (x : Fin n → Bool) (i : Nat) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem W_input (C : Circuit) (n : Nat) (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem W_gate (C : Circuit) (n : Nat) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

def NF (n : Nat) (C : Circuit) : Prop :=
  ∀ g < C.gates.length, WireBelowOutput n C (n + g) →
    ∀ j < C.gates.length, n + g ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.or ∧ WireBelowOutput n C (n + j)

def Clean (n : Nat) (C : Circuit) : Prop :=
  ∀ g < C.gates.length, (gateAt C g).op = GateOp.and →
    WireBelowOutput n C (n + g)

def OneHot (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def UnitVec (S : List Nat) (i : Nat) : List Nat :=
  S.map fun j => if j = i then 1 else 0

lemma W_beyond (x : Fin n → Bool) (i : Nat) (hi : n + C.gates.length ≤ i) :
    W C n x i = false := by
  unfold W
  rw [wires_eq]
  exact foldl_snoc_beyond (fun ins (g : Gate) => g.op.eval ins) false
    (List.ofFn x) C.gates i (by simpa using hi)

lemma W_or (hC : IsAO2 n C) {g : Nat} (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) (x : Fin n → Bool) :
    W C n x (n + g) = (W C n x (opnd C g 0) || W C n x (opnd C g 1)) := by
  rw [W_gate C n x g hg (hC.2.1 g hg), ao_inputs hC hg, hop]
  simp [GateOp.eval]

lemma W_and (hC : IsAO2 n C) {g : Nat} (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.and) (x : Fin n → Bool) :
    W C n x (n + g) = (W C n x (opnd C g 0) && W C n x (opnd C g 1)) := by
  rw [W_gate C n x g hg (hC.2.1 g hg), ao_inputs hC hg, hop]
  simp [GateOp.eval]

lemma input_not_below
    (hone : ∀ i : Fin n, circuitFun n C (OneHot i) = false)
    (w : Nat) (hw : w < n) : ¬ WireBelowOutput n C w := by
  intro h
  have hv : W C n (OneHot ⟨w, hw⟩) w = true := by
    rw [W_input C n _ w hw]
    simp [OneHot]
  have hout := h (OneHot ⟨w, hw⟩) hv
  change circuitFun n C (OneHot ⟨w, hw⟩) = true at hout
  rw [hone] at hout
  contradiction

lemma opnd_not_below (hC : IsAO2 n C) (hnf : NF n C)
    (hone : ∀ i : Fin n, circuitFun n C (OneHot i) = false)
    {g : Nat} (hg : g < C.gates.length) (b : Fin 2)
    (hbad : (gateAt C g).op = GateOp.and ∨ ¬ WireBelowOutput n C (n + g)) :
    ¬ WireBelowOutput n C (opnd C g b) := by
  intro hb
  by_cases hinput : opnd C g b < n
  · exact input_not_below hone _ hinput hb
  · obtain ⟨j, hj⟩ : ∃ j, opnd C g b = n + j :=
      ⟨opnd C g b - n, by omega⟩
    have hlt := opnd_lt hC hg b
    have hjC : j < C.gates.length := by omega
    have below : WireBelowOutput n C (n + j) := hj ▸ hb
    have edge : n + j ∈ (gateAt C g).inputs := hj ▸ opnd_mem hC hg b
    have h := hnf j hjC below g hg edge
    rcases hbad with ha | hn
    · rw [ha] at h
      cases h.1
    · exact hn h.2

lemma unit_mem_leaf (S : List Nat) {i : Nat} (hi : i ∈ S) :
    UnitVec S i ∈ leafVectors S 1 i := by
  simp [leafVectors, hi, UnitVec]

lemma unit_all (S : List Nat) (i : Nat) :
    (UnitVec S i).all (fun a => decide (a ≤ 1)) = true := by
  simp only [UnitVec, List.all_eq_true, List.mem_map]
  rintro a ⟨j, _, rfl⟩
  split_ifs <;> decide

lemma units_all (S : List Nat) (i j : Nat) (hij : i ≠ j) :
    (capAdd 1 (capAdd 1 (S.map fun _ => 0) (UnitVec S i))
      (UnitVec S j)).all (fun a => decide (a ≤ 1)) = true := by
  induction S with
  | nil => simp [capAdd, UnitVec]
  | cons a S ih =>
    simp only [capAdd, UnitVec, List.map_cons, List.zipWith_cons_cons,
      List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    by_cases hai : a = i <;> by_cases haj : a = j <;> simp_all

lemma pure_vector (hC : IsAO2 n C) (hnf : NF n C) (hclean : Clean n C)
    (hone : ∀ i : Fin n, circuitFun n C (OneHot i) = false)
    (S : List Nat) (x : Fin n → Bool)
    (hx : ∀ i : Fin n, x i = true → i.val ∈ S) :
    ∀ w, w < n + C.gates.length → ¬ WireBelowOutput n C w → W C n x w = true →
      ∃ i : Fin n, i.val ∈ S ∧ W C n (OneHot i) w = true ∧
        UnitVec S i.val ∈ AV n C 1 S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hnb hv
    by_cases hi : w < n
    · have hxi : x ⟨w, hi⟩ = true := by
        rw [W_input C n x w hi] at hv
        exact hv
      refine ⟨⟨w, hi⟩, hx _ hxi, ?_, ?_⟩
      · rw [W_input C n _ w hi]
        simp [OneHot]
      · rw [AV_input 1 S w hi]
        exact unit_mem_leaf S (hx _ hxi)
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      rcases ao_op hC hg with ha | ho
      · exact False.elim (hnb (hclean g hg ha))
      · rw [W_or hC hg ho, Bool.or_eq_true] at hv
        obtain ⟨b, hb⟩ : ∃ b : Fin 2, W C n x (opnd C g b) = true := by
          rcases hv with hv | hv
          · exact ⟨0, hv⟩
          · exact ⟨1, hv⟩
        have hlt := opnd_lt hC hg b
        obtain ⟨i, hiS, hit, hiv⟩ := ih _ hlt (by omega)
          (opnd_not_below hC hnf hone hg b (Or.inr hnb)) hb
        refine ⟨i, hiS, ?_, ?_⟩
        · rw [W_or hC hg ho, Bool.or_eq_true]
          fin_cases b
          · exact Or.inl hit
          · exact Or.inr hit
        · apply (gate_vec hC 1 S hg _).2
          refine Or.inl ⟨ho, ?_⟩
          fin_cases b
          · exact Or.inl hiv
          · exact Or.inr hiv

lemma good_vector (hC : IsAO2 n C) (hnf : NF n C) (hclean : Clean n C)
    (hone : ∀ i : Fin n, circuitFun n C (OneHot i) = false)
    (S : List Nat) (x : Fin n → Bool)
    (hx : ∀ i : Fin n, x i = true → i.val ∈ S) :
    ∀ w, w < n + C.gates.length → W C n x w = true →
      ∃ v ∈ AV n C 1 S w, v.all (fun a => decide (a ≤ 1)) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hi : w < n
    · refine ⟨UnitVec S w, ?_, unit_all S w⟩
      rw [AV_input 1 S w hi]
      apply unit_mem_leaf
      apply hx ⟨w, hi⟩
      rw [W_input C n x w hi] at hv
      exact hv
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      rcases ao_op hC hg with ha | ho
      · rw [W_and hC hg ha, Bool.and_eq_true] at hv
        have hl0 := opnd_lt hC hg (0 : Fin 2)
        have hl1 := opnd_lt hC hg (1 : Fin 2)
        obtain ⟨i, hiS, hiw, hiv⟩ := pure_vector hC hnf hclean hone S x hx _ (by omega)
          (opnd_not_below hC hnf hone hg 0 (Or.inl ha)) hv.1
        obtain ⟨j, hjS, hjw, hjv⟩ := pure_vector hC hnf hclean hone S x hx _ (by omega)
          (opnd_not_below hC hnf hone hg 1 (Or.inl ha)) hv.2
        have hij : i.val ≠ j.val := by
          intro heq
          have heq' : i = j := Fin.ext heq
          subst j
          have ht : W C n (OneHot i) (n + g) = true := by
            rw [W_and hC hg ha, Bool.and_eq_true]
            exact ⟨hiw, hjw⟩
          have hout := hclean g hg ha (OneHot i) ht
          change circuitFun n C (OneHot i) = true at hout
          rw [hone] at hout
          contradiction
        refine ⟨_, (gate_vec hC 1 S hg _).2 (Or.inr ⟨ha, _, hiv, _, hjv, rfl⟩), ?_⟩
        exact units_all S i.val j.val hij
      · rw [W_or hC hg ho, Bool.or_eq_true] at hv
        obtain ⟨b, hb⟩ : ∃ b : Fin 2, W C n x (opnd C g b) = true := by
          rcases hv with hv | hv
          · exact ⟨0, hv⟩
          · exact ⟨1, hv⟩
        have hlt := opnd_lt hC hg b
        obtain ⟨v, hv, hvall⟩ := ih _ hlt (by omega) hb
        refine ⟨v, ?_, hvall⟩
        apply (gate_vec hC 1 S hg v).2
        refine Or.inl ⟨ho, ?_⟩
        fin_cases b
        · exact Or.inl hv
        · exact Or.inr hv

lemma clean_nf_read1 (hC : IsAO2 n C) (hnf : NF n C) (hclean : Clean n C)
    (hone : ∀ i : Fin n, circuitFun n C (OneHot i) = false) :
    IsReadK n C 1 := by
  intro S hS
  have hv : W C n (setInput S) C.output = true := hS.1
  have hw : C.output < n + C.gates.length := by
    by_contra h
    rw [W_beyond _ _ (by omega)] at hv
    contradiction
  have hm : ∀ i : Fin n, setInput S i = true → i.val ∈ setList S := by
    intro i hi
    simp only [setInput, decide_eq_true_eq] at hi
    simp only [setList, List.mem_map, List.mem_filter, List.mem_finRange,
      decide_eq_true_eq, true_and]
    exact ⟨i, hi, rfl⟩
  obtain ⟨v, hv, hvall⟩ := good_vector hC hnf hclean hone (setList S) (setInput S) hm
    C.output hw hv
  exact List.any_eq_true.2 ⟨v, hv, hvall⟩

lemma incidence_singleton_false (P L : Nat) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hfun : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (i : Fin (P + L)) : circuitFun (P + L) C (OneHot i) = false := by
  rw [hfun]
  apply decide_eq_false_iff_not.mpr
  rintro ⟨p, l, _, hp, hl⟩
  simp only [OneHot, decide_eq_true_eq] at hp hl
  have heq : Fin.castAdd L p = Fin.natAdd P l := hp.trans hl.symm
  have hv := congrArg Fin.val heq
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := p.isLt
  omega

lemma incidence_clean_nf_read1 (P L : Nat) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hAO : IsAO2 (P + L) C) (hnf : NF (P + L) C) (hclean : Clean (P + L) C)
    (hfun : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    IsReadK (P + L) C 1 :=
  clean_nf_read1 hAO hnf hclean (incidence_singleton_false P L I C hfun)

lemma incidence_clean_nf_replacement (P L : Nat) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hAO : IsAO2 (P + L) C) (hnf : NF (P + L) C) (hclean : Clean (P + L) C)
    (hfun : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + L) D 1 :=
  ⟨C, hAO, hfun, le_rfl, incidence_clean_nf_read1 P L I C hAO hnf hclean hfun⟩

end PEqualNP.Outside.L_meta_2585.CleanNF
