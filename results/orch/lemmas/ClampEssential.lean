import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.Derivative

open PEqualNP.CircuitLowerBounds

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

def Proper (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

def DerivativeRules (n : ℕ) (C : Circuit) (v d : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (n + j) = (v a && d b || d a && v b)) ∧
    (g.op = .or → d (n + j) = (d a || d b))

def ValueRules (n : ℕ) (C : Circuit) (v : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → v (n + j) = (v a && v b)) ∧
    (g.op = .or → v (n + j) = (v a || v b))

lemma derivative_unique (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v d e : ℕ → Bool) (hd : DerivativeRules n C v d)
    (he : DerivativeRules n C v e) (hinit : ∀ i < n, d i = e i) :
    ∀ w < n + C.gates.length, d w = e w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · exact hinit w hwn
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hC j _ hg
      have ea := ih a ha (by omega)
      have eb := ih b hb (by omega)
      rcases hop with hop | hop
      · rw [(hd j _ a b hg hin).1 hop, (he j _ a b hg hin).1 hop, ea, eb]
      · rw [(hd j _ a b hg hin).2 hop, (he j _ a b hg hin).2 hop, ea, eb]

lemma derivative_zero_forces_repeated_and (n : ℕ) (C : Circuit)
    (hC : Proper n C) (v b d : ℕ → Bool)
    (hv : ValueRules n C v) (hb : ValueRules n C b)
    (hd : DerivativeRules n C b d)
    (hinit : ∀ i < n, v i = true → b i = false → d i = true) :
    ∀ w < n + C.gates.length, v w = true → b w = false → d w = false →
      ∃ j g a c, n + j ≤ w ∧ C.gates[j]? = some g ∧ g.op = .and ∧
        g.inputs = [a, c] ∧ v a = true ∧ v c = true ∧ b a = false ∧ b c = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hvt hbf hdf
    by_cases hwn : w < n
    · have := hinit w hwn hvt hbf
      simp_all
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, c, hin, _, ha, hc⟩ := hC j _ hg
      have lift (z : ℕ) (hz : z < n + j) (hzt : v z = true)
          (hzf : b z = false) (hzd : d z = false) :
          ∃ k g a c, n + k ≤ n + j ∧ C.gates[k]? = some g ∧ g.op = .and ∧
            g.inputs = [a, c] ∧ v a = true ∧ v c = true ∧ b a = false ∧ b c = false := by
        obtain ⟨k, g, a, c, hk, hs⟩ := ih z hz (by omega) hzt hzf hzd
        exact ⟨k, g, a, c, by omega, hs⟩
      rcases hop with hop | hop
      · rw [(hv j _ a c hg hin).1 hop] at hvt
        rw [(hb j _ a c hg hin).1 hop] at hbf
        rw [(hd j _ a c hg hin).1 hop] at hdf
        have ⟨hva, hvc⟩ : v a = true ∧ v c = true := by simpa using hvt
        cases hba : b a <;> cases hbc : b c
        · exact ⟨j, _, a, c, le_rfl, hg, hop, hin, hva, hvc, hba, hbc⟩
        · apply lift a ha hva hba
          simpa [hba, hbc] using hdf
        · apply lift c hc hvc hbc
          simpa [hba, hbc] using hdf
        · simp [hba, hbc] at hbf
      · rw [(hv j _ a c hg hin).2 hop] at hvt
        rw [(hb j _ a c hg hin).2 hop] at hbf
        rw [(hd j _ a c hg hin).2 hop] at hdf
        obtain ⟨hba, hbc⟩ := Bool.or_eq_false_iff.mp hbf
        obtain ⟨hda, hdc⟩ := Bool.or_eq_false_iff.mp hdf
        have hor : v a = true ∨ v c = true := by simpa using hvt
        rcases hor with hva | hvc
        · exact lift a ha hva hba hda
        · exact lift c hc hvc hbc hdc

def WireValue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma wire_value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n) : WireValue C x i = x ⟨i, hi⟩ := by
  unfold WireValue Circuit.wires
  rw [foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _
    (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wire_value_rules {n : ℕ} (C : Circuit) (hC : Proper n C)
    (x : Fin n → Bool) : ValueRules n C (WireValue C x) := by
  intro j g a b hg hin
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    contradiction
  have hget : C.gates[j] = g := by simpa [List.getElem?_eq_getElem hj] using hg
  obtain ⟨_, c, d, hcd, _, hc, hd⟩ := hC j g hg
  have hab : a = c ∧ b = d := by simpa [hin] using hcd
  obtain ⟨rfl, rfl⟩ := hab
  have earlier : ∀ i ∈ C.gates[j].inputs, i < (List.ofFn x).length + j := by
    intro i hi
    rw [hget, hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simpa using hc
    · simpa using hd
  have hrec := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins)
    false (List.ofFn x) C.gates j hj earlier
  simp only [List.length_ofFn] at hrec
  change WireValue C x (n + j) = C.gates[j].op.eval
    (C.gates[j].inputs.map (WireValue C x)) at hrec
  rw [hget, hin] at hrec
  constructor
  · intro hop
    simpa [hop, GateOp.eval] using hrec
  · intro hop
    simpa [hop, GateOp.eval] using hrec

lemma output_lt_of_eval_true (C : Circuit) (x : List Bool) (h : C.eval x = true) :
    C.output < x.length + C.gates.length := by
  have len : (C.wires x).length = x.length + C.gates.length :=
    foldl_snoc_length (fun w (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)) _ _
  by_contra hbound
  have hf : C.eval x = false := by
    apply List.getD_eq_default
    rw [len]
    omega
  rw [hf] at h
  contradiction

lemma repeated_and_of_pair (n : ℕ) (C : Circuit) (hC : Proper n C)
    (p q : ℕ) (d : ℕ → Bool)
    (hd : DerivativeRules n C (WireValue C (fun i : Fin n => decide (i.val = p))) d)
    (hinit : ∀ i < n, d i = decide (i = q))
    (hpair : C.eval (List.ofFn fun i : Fin n => decide (i.val = p ∨ i.val = q)) = true)
    (hbase : C.eval (List.ofFn fun i : Fin n => decide (i.val = p)) = false)
    (hzero : d C.output = false) :
    ∃ j g a b, n + j ≤ C.output ∧ C.gates[j]? = some g ∧ g.op = .and ∧
      g.inputs = [a, b] ∧
      WireValue C (fun i : Fin n => decide (i.val = p ∨ i.val = q)) a = true ∧
      WireValue C (fun i : Fin n => decide (i.val = p ∨ i.val = q)) b = true ∧
      WireValue C (fun i : Fin n => decide (i.val = p)) a = false ∧
      WireValue C (fun i : Fin n => decide (i.val = p)) b = false := by
  apply derivative_zero_forces_repeated_and n C hC _ _ d
    (wire_value_rules C hC _) (wire_value_rules C hC _) hd
  · intro i hi hp hb
    rw [wire_value_input C _ i hi] at hp hb
    have hpq : i = p ∨ i = q := of_decide_eq_true hp
    have hnp : i ≠ p := of_decide_eq_false hb
    have hiq : i = q := hpq.resolve_left hnp
    rw [hinit i hi, hiq]
    simp
  · simpa using output_lt_of_eval_true C _ hpair
  · exact hpair
  · exact hbase
  · exact hzero

def DerivativeStep (n : ℕ) (C : Circuit) (v : ℕ → Bool) (a w : ℕ) : Prop :=
  ∃ j g b, w = n + j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ (g.op = .or ∨ v b = true)

lemma derivative_step_true (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v d : ℕ → Bool) (hd : DerivativeRules n C v d)
    {a w : ℕ} (hs : DerivativeStep n C v a w) (ha : d a = true) : d w = true := by
  obtain ⟨j, g, b, rfl, hg, hin, hgood⟩ := hs
  rcases (hC j g hg).1 with hop | hop
  · have hb : v b = true := hgood.resolve_left (by intro ho; rw [hop] at ho; cases ho)
    rcases hin with hin | hin
    · rw [(hd j g a b hg hin).1 hop]
      simp [ha, hb]
    · rw [(hd j g b a hg hin).1 hop]
      simp [ha, hb]
  · rcases hin with hin | hin
    · rw [(hd j g a b hg hin).2 hop]
      simp [ha]
    · rw [(hd j g b a hg hin).2 hop]
      simp [ha]

lemma derivative_walk_true (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v d : ℕ → Bool) (hd : DerivativeRules n C v d)
    {a w : ℕ} (hs : Relation.ReflTransGen (DerivativeStep n C v) a w)
    (ha : d a = true) : d w = true := by
  induction hs with
  | refl => exact ha
  | tail _ ht ih => exact derivative_step_true n C hC v d hd ht ih

lemma derivative_true_iff_walk (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v d : ℕ → Bool) (q : ℕ) (hq : q < n)
    (hd : DerivativeRules n C v d) (hinit : ∀ i < n, d i = decide (i = q)) :
    ∀ w < n + C.gates.length,
      d w = true ↔ Relation.ReflTransGen (DerivativeStep n C v) q w := by
  have forward : ∀ w < n + C.gates.length, d w = true →
      Relation.ReflTransGen (DerivativeStep n C v) q w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw ht
      by_cases hwn : w < n
      · rw [hinit w hwn] at ht
        have hwq : w = q := of_decide_eq_true ht
        subst w
        exact Relation.ReflTransGen.refl
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := List.getElem?_eq_getElem (l := C.gates) hj
        obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hC j _ hg
        rcases hop with hop | hop
        · rw [(hd j _ a b hg hin).1 hop] at ht
          have hor : (v a = true ∧ d b = true) ∨ (d a = true ∧ v b = true) := by
            simpa using ht
          rcases hor with ⟨hva, hdb⟩ | ⟨hda, hvb⟩
          · exact (ih b hb (by omega) hdb).tail
              ⟨j, _, a, rfl, hg, Or.inr hin, Or.inr hva⟩
          · exact (ih a ha (by omega) hda).tail
              ⟨j, _, b, rfl, hg, Or.inl hin, Or.inr hvb⟩
        · rw [(hd j _ a b hg hin).2 hop] at ht
          have hor : d a = true ∨ d b = true := by simpa using ht
          rcases hor with hda | hdb
          · exact (ih a ha (by omega) hda).tail
              ⟨j, _, b, rfl, hg, Or.inl hin, Or.inl hop⟩
          · exact (ih b hb (by omega) hdb).tail
              ⟨j, _, a, rfl, hg, Or.inr hin, Or.inl hop⟩
  intro w hw
  constructor
  · exact forward w hw
  · intro hwalk
    apply derivative_walk_true n C hC v d hd hwalk
    rw [hinit q hq]
    simp

end PEqualNP.Outside.L_meta_2602_aux.Derivative

namespace PEqualNP.Outside.L_meta_2602_aux.DeadGate

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative

def down (m w : ℕ) : ℕ := if w < m then w else w - 1

def up (m w : ℕ) : ℕ := if w < m then w else w + 1

def renameGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (down m)⟩

def erase (n : ℕ) (C : Circuit) (k : ℕ) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (renameGate (n + k)), down (n + k) C.output⟩

lemma up_down (m w : ℕ) (hw : w ≠ m) : up m (down m w) = w := by
  unfold up down
  split_ifs <;> omega

lemma down_up (m w : ℕ) : down m (up m w) = w := by
  unfold up down
  split_ifs <;> omega

lemma down_inj (m a b : ℕ) (ha : a ≠ m) (hb : b ≠ m)
    (h : down m a = down m b) : a = b := by
  have := congrArg (up m) h
  simpa [up_down m a ha, up_down m b hb] using this

lemma up_gate (n k j : ℕ) : up (n + k) (n + j) = n + up k j := by
  unfold up
  split_ifs <;> omega

lemma down_lt_gate (n k j a : ℕ) (ha : a < n + up k j) (hne : a ≠ n + k) :
    down (n + k) a < n + j := by
  unfold up down at *
  split_ifs at * <;> omega

lemma erase_length (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    (erase n C k).gates.length + 1 = C.gates.length := by
  simp only [erase, List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma erase_get (n : ℕ) (C : Circuit) (k j : ℕ) (g : Gate)
    (hg : (erase n C k).gates[j]? = some g) :
    ∃ g0, C.gates[up k j]? = some g0 ∧ g = renameGate (n + k) g0 := by
  have hmap : Option.map (renameGate (n + k)) (C.gates[up k j]?) = some g := by
    simpa only [erase, List.getElem?_map, List.getElem?_eraseIdx, up,
      apply_ite] using hg
  cases hs : C.gates[up k j]? with
  | none => simp [hs] at hmap
  | some g0 =>
    refine ⟨g0, rfl, ?_⟩
    simpa only [hs, Option.map_some, Option.some.injEq] using hmap.symm

lemma erase_proper (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs) : Proper n (erase n C k) := by
  intro j g hg
  obtain ⟨g0, hget, rfl⟩ := erase_get n C k j g hg
  obtain ⟨hop, a, b, hin, hab, ha, hb⟩ := hC (up k j) g0 hget
  have hdead := hun g0 (List.mem_of_getElem? hget)
  have hna : a ≠ n + k := by intro he; apply hdead; simp [hin, he]
  have hnb : b ≠ n + k := by intro he; apply hdead; simp [hin, he]
  refine ⟨hop, down (n + k) a, down (n + k) b, ?_, ?_, ?_, ?_⟩
  · simp [renameGate, hin]
  · intro he
    exact hab (down_inj (n + k) a b hna hnb he)
  · exact down_lt_gate n k j a ha hna
  · exact down_lt_gate n k j b hb hnb

lemma value_unique (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v e : ℕ → Bool) (hv : ValueRules n C v)
    (he : ValueRules n C e) (hinit : ∀ i < n, v i = e i) :
    ∀ w < n + C.gates.length, v w = e w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · exact hinit w hwn
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hC j _ hg
      have ea := ih a ha (by omega)
      have eb := ih b hb (by omega)
      rcases hop with hop | hop
      · rw [(hv j _ a b hg hin).1 hop, (he j _ a b hg hin).1 hop, ea, eb]
      · rw [(hv j _ a b hg hin).2 hop, (he j _ a b hg hin).2 hop, ea, eb]

lemma erase_value_rules (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs)
    (v : ℕ → Bool) (hv : ValueRules n C v) :
    ValueRules n (erase n C k) (fun w => v (up (n + k) w)) := by
  intro j g a b hg hin
  obtain ⟨g0, hget, rfl⟩ := erase_get n C k j g hg
  obtain ⟨_, a0, b0, hin0, _, _, _⟩ := hC (up k j) g0 hget
  have hdead := hun g0 (List.mem_of_getElem? hget)
  have hna : a0 ≠ n + k := by intro he; apply hdead; simp [hin0, he]
  have hnb : b0 ≠ n + k := by intro he; apply hdead; simp [hin0, he]
  have hargs : down (n + k) a0 = a ∧ down (n + k) b0 = b := by
    simpa [renameGate, hin0] using hin
  obtain ⟨rfl, rfl⟩ := hargs
  constructor
  · intro hop
    simpa only [up_gate, up_down _ _ hna, up_down _ _ hnb] using
      (hv (up k j) g0 a0 b0 hget hin0).1 hop
  · intro hop
    simpa only [up_gate, up_down _ _ hna, up_down _ _ hnb] using
      (hv (up k j) g0 a0 b0 hget hin0).2 hop

lemma erase_derivative_rules (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs)
    (v d : ℕ → Bool) (hd : DerivativeRules n C v d) :
    DerivativeRules n (erase n C k) (fun w => v (up (n + k) w))
      (fun w => d (up (n + k) w)) := by
  intro j g a b hg hin
  obtain ⟨g0, hget, rfl⟩ := erase_get n C k j g hg
  obtain ⟨_, a0, b0, hin0, _, _, _⟩ := hC (up k j) g0 hget
  have hdead := hun g0 (List.mem_of_getElem? hget)
  have hna : a0 ≠ n + k := by intro he; apply hdead; simp [hin0, he]
  have hnb : b0 ≠ n + k := by intro he; apply hdead; simp [hin0, he]
  have hargs : down (n + k) a0 = a ∧ down (n + k) b0 = b := by
    simpa [renameGate, hin0] using hin
  obtain ⟨rfl, rfl⟩ := hargs
  constructor
  · intro hop
    simpa only [up_gate, up_down _ _ hna, up_down _ _ hnb] using
      (hd (up k j) g0 a0 b0 hget hin0).1 hop
  · intro hop
    simpa only [up_gate, up_down _ _ hna, up_down _ _ hnb] using
      (hd (up k j) g0 a0 b0 hget hin0).2 hop

lemma erase_wire_value_up (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + (erase n C k).gates.length) :
    WireValue (erase n C k) x w = WireValue C x (up (n + k) w) := by
  apply value_unique n (erase n C k) (erase_proper n C k hC hun)
    (WireValue (erase n C k) x) (fun w => WireValue C x (up (n + k) w))
    (wire_value_rules _ (erase_proper n C k hC hun) x)
    (erase_value_rules n C k hC hun (WireValue C x) (wire_value_rules C hC x))
    ?_ w hw
  intro i hi
  have hu : up (n + k) i = i := by simp [up, show i < n + k by omega]
  rw [hu, wire_value_input _ x i hi, wire_value_input _ x i hi]

lemma erase_wire_value (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hk : k < C.gates.length) (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + C.gates.length) (hne : w ≠ n + k) :
    WireValue (erase n C k) x (down (n + k) w) = WireValue C x w := by
  have hl := erase_length n C k hk
  have hbound : down (n + k) w < n + (erase n C k).gates.length := by
    unfold down
    split_ifs <;> omega
  simpa only [up_down _ _ hne] using erase_wire_value_up n C k hC hun x _ hbound

lemma wire_value_beyond (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (hw : n + C.gates.length ≤ w) : WireValue C x w = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    unfold Circuit.wires
    rw [foldl_snoc_length]
    simp
  apply List.getD_eq_default
  simpa only [hlen] using hw

lemma erase_eval (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hk : k < C.gates.length) (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs)
    (hout : C.output ≠ n + k) (x : Fin n → Bool) :
    (erase n C k).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  change WireValue (erase n C k) x (down (n + k) C.output) = WireValue C x C.output
  by_cases hb : C.output < n + C.gates.length
  · exact erase_wire_value n C k hC hk hun x C.output hb hout
  · have hl := erase_length n C k hk
    have hbound : n + (erase n C k).gates.length ≤ down (n + k) C.output := by
      unfold down
      split_ifs <;> omega
    rw [wire_value_beyond n (erase n C k) x _ hbound,
      wire_value_beyond n C x _ (by omega)]

lemma derivative_rules_congr_base (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v e d : ℕ → Bool) (hd : DerivativeRules n C v d)
    (heq : ∀ w < n + C.gates.length, v w = e w) : DerivativeRules n C e d := by
  intro j g a b hg hin
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    contradiction
  obtain ⟨_, a0, b0, hin0, _, ha, hb⟩ := hC j g hg
  have hargs : a = a0 ∧ b = b0 := by simpa [hin] using hin0
  obtain ⟨rfl, rfl⟩ := hargs
  have hstep := hd j g a b hg hin
  rw [heq a (by omega), heq b (by omega)] at hstep
  exact hstep

lemma erase_actual_derivative_rules (n : ℕ) (C : Circuit) (k : ℕ)
    (hC : Proper n C) (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs)
    (base : Fin n → Bool) (d : ℕ → Bool)
    (hd : DerivativeRules n C (WireValue C base) d) :
    DerivativeRules n (erase n C k) (WireValue (erase n C k) base)
      (fun w => d (up (n + k) w)) := by
  apply derivative_rules_congr_base n (erase n C k) (erase_proper n C k hC hun)
    (fun w => WireValue C base (up (n + k) w))
    (WireValue (erase n C k) base) (fun w => d (up (n + k) w))
    (erase_derivative_rules n C k hC hun (WireValue C base) d hd)
  intro w hw
  exact (erase_wire_value_up n C k hC hun base w hw).symm

lemma erase_witness (n : ℕ) (C : Circuit) (k : ℕ) (hC : Proper n C)
    (hun : ∀ g ∈ C.gates, n + k ∉ g.inputs) (hout : C.output ≠ n + k)
    (base : Fin n → Bool) (initial d : ℕ → Bool)
    (hinit : ∀ i < n, d i = initial i)
    (hd : DerivativeRules n C (WireValue C base) d) (hzero : d C.output = false) :
    ∃ d', (∀ i < n, d' i = initial i) ∧
      DerivativeRules n (erase n C k) (WireValue (erase n C k) base) d' ∧
      d' (erase n C k).output = false := by
  refine ⟨fun w => d (up (n + k) w), ?_,
    erase_actual_derivative_rules n C k hC hun base d hd, ?_⟩
  · intro i hi
    have hu : up (n + k) i = i := by simp [up, show i < n + k by omega]
    change d (up (n + k) i) = initial i
    rw [hu]
    exact hinit i hi
  · change d (up (n + k) (down (n + k) C.output)) = false
    simpa only [up_down _ _ hout] using hzero

end PEqualNP.Outside.L_meta_2602_aux.DeadGate

namespace PEqualNP.Outside.L_meta_2602_aux.FirstDirty

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative

def OrStep (n : ℕ) (C : Circuit) (a w : ℕ) : Prop :=
  ∃ j g, w = n + j ∧ C.gates[j]? = some g ∧ g.op = .or ∧ a ∈ g.inputs

lemma or_step_true (n : ℕ) (C : Circuit) (hC : Proper n C) (x : Fin n → Bool)
    {a w : ℕ} (hs : OrStep n C a w) (ha : WireValue C x a = true) :
    WireValue C x w = true := by
  obtain ⟨j, g, rfl, hg, hop, mem⟩ := hs
  obtain ⟨_, u, v, ins, _⟩ := hC j g hg
  rw [(wire_value_rules C hC x j g u v hg ins).2 hop]
  rw [ins] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> simp [ha]

lemma or_walk_true (n : ℕ) (C : Circuit) (hC : Proper n C) (x : Fin n → Bool)
    {a w : ℕ} (hs : Relation.ReflTransGen (OrStep n C) a w)
    (ha : WireValue C x a = true) : WireValue C x w = true := by
  induction hs with
  | refl => exact ha
  | tail _ ht ih => exact or_step_true n C hC x ht ih

lemma wire_value_mono (n : ℕ) (C : Circuit) (hC : Proper n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, WireValue C x w = true → WireValue C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    have hw : w < n + C.gates.length := by
      simpa using output_lt_of_eval_true (⟨C.gates, w⟩ : Circuit) (List.ofFn x) hx
    by_cases hwn : w < n
    · rw [wire_value_input C x w hwn] at hx
      rw [wire_value_input C y w hwn]
      exact hxy _ hx
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, ins, _, ha, hb⟩ := hC j _ hg
      rcases hop with hop | hop
      · rw [(wire_value_rules C hC x j _ a b hg ins).1 hop] at hx
        rw [(wire_value_rules C hC y j _ a b hg ins).1 hop]
        obtain ⟨hxa, hxb⟩ := Bool.and_eq_true_iff.mp hx
        exact Bool.and_eq_true_iff.mpr ⟨ih a ha hxa, ih b hb hxb⟩
      · rw [(wire_value_rules C hC x j _ a b hg ins).2 hop] at hx
        rw [(wire_value_rules C hC y j _ a b hg ins).2 hop]
        have hor : WireValue C x a = true ∨ WireValue C x b = true := by simpa using hx
        rcases hor with hxa | hxb
        · simp [ih a ha hxa]
        · simp [ih b hb hxb]

lemma prefix_or_path (n : ℕ) (C : Circuit) (hC : Proper n C)
    (k : ℕ) (hk : k ≤ C.gates.length) (x : Fin n → Bool)
    (hoff : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = .and →
      WireValue C x (n + j) = false) :
    ∀ w < n + k, WireValue C x w = true →
      ∃ i : Fin n, x i = true ∧ Relation.ReflTransGen (OrStep n C) i.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, Relation.ReflTransGen.refl⟩
      rwa [wire_value_input C x w hwn] at ht
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hjk : j < k := by omega
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, ins, _, ha, hb⟩ := hC j _ hg
      rcases hop with hop | hop
      · rw [hoff j hjk _ hg hop] at ht
        contradiction
      · rw [(wire_value_rules C hC x j _ a b hg ins).2 hop] at ht
        have hor : WireValue C x a = true ∨ WireValue C x b = true := by simpa using ht
        rcases hor with hta | htb
        · obtain ⟨i, hi, walk⟩ := ih a ha (by omega) hta
          exact ⟨i, hi, walk.tail ⟨j, _, rfl, hg, hop, by simp [ins]⟩⟩
        · obtain ⟨i, hi, walk⟩ := ih b hb (by omega) htb
          exact ⟨i, hi, walk.tail ⟨j, _, rfl, hg, hop, by simp [ins]⟩⟩

lemma first_dirty_pair (n : ℕ) (C : Circuit) (hC : Proper n C)
    (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) (hop : g.op = .and)
    (hclean : ∀ j < k, ∀ h, C.gates[j]? = some h → h.op = .and →
      ∀ x : Fin n → Bool, WireValue C x (n + j) = true → C.eval (List.ofFn x) = true)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = false)
    (hgate : WireValue C x (n + k) = true) :
    ∃ p q : Fin n, x p = true ∧ x q = true ∧
      C.eval (List.ofFn fun i => decide (i = p ∨ i = q)) = false ∧
        WireValue C (fun i => decide (i = p ∨ i = q)) (n + k) = true := by
  have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hoff : ∀ j < k, ∀ h, C.gates[j]? = some h → h.op = .and →
      WireValue C x (n + j) = false := by
    intro j hj h hh ho
    apply Bool.eq_false_iff.mpr
    intro ht
    have bad := hclean j hj h hh ho x ht
    rw [hx] at bad
    contradiction
  obtain ⟨_, a, b, ins, _, ha, hb⟩ := hC k g hg
  rw [(wire_value_rules C hC x k g a b hg ins).1 hop] at hgate
  obtain ⟨hva, hvb⟩ := Bool.and_eq_true_iff.mp hgate
  obtain ⟨p, hp, pa⟩ := prefix_or_path n C hC k (Nat.le_of_lt hk) x hoff a ha hva
  obtain ⟨q, hq, qb⟩ := prefix_or_path n C hC k (Nat.le_of_lt hk) x hoff b hb hvb
  let y : Fin n → Bool := fun i => decide (i = p ∨ i = q)
  have hyx : ∀ i, y i = true → x i = true := by
    intro i hi
    have h : i = p ∨ i = q := of_decide_eq_true hi
    rcases h with rfl | rfl
    · exact hp
    · exact hq
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro ht
    have bad := wire_value_mono n C hC y x hyx C.output ht
    change C.eval (List.ofFn x) = true at bad
    rw [hx] at bad
    contradiction
  · rw [(wire_value_rules C hC y k g a b hg ins).1 hop]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply or_walk_true n C hC y pa
      rw [wire_value_input C y p.val p.isLt]
      simp [y]
    · apply or_walk_true n C hC y qb
      rw [wire_value_input C y q.val q.isLt]
      simp [y]

end PEqualNP.Outside.L_meta_2602_aux.FirstDirty

namespace PEqualNP.Outside.L_meta_2602_aux.DerivativeSuper

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative

lemma derivative_true_implies_super_value (n : ℕ) (C : Circuit) (hC : Proper n C)
    (base pair : Fin n → Bool) (d : ℕ → Bool)
    (hbase : ∀ i, base i = true → pair i = true)
    (hinit : ∀ i (hi : i < n), d i = true → pair ⟨i, hi⟩ = true)
    (hd : DerivativeRules n C (WireValue C base) d) :
    ∀ w < n + C.gates.length, d w = true → WireValue C pair w = true := by
  have mono := FirstDirty.wire_value_mono n C hC base pair hbase
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hwn : w < n
    · rw [wire_value_input C pair w hwn]
      exact hinit w hwn ht
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, ins, _, ha, hb⟩ := hC j _ hg
      rcases hop with hop | hop
      · rw [(hd j _ a b hg ins).1 hop] at ht
        rw [(wire_value_rules C hC pair j _ a b hg ins).1 hop]
        simp only [Bool.or_eq_true, Bool.and_eq_true] at ht
        rcases ht with ⟨va, db⟩ | ⟨da, vb⟩
        · exact Bool.and_eq_true_iff.mpr ⟨mono a va, ih b hb (by omega) db⟩
        · exact Bool.and_eq_true_iff.mpr ⟨ih a ha (by omega) da, mono b vb⟩
      · rw [(hd j _ a b hg ins).2 hop] at ht
        rw [(wire_value_rules C hC pair j _ a b hg ins).2 hop]
        simp only [Bool.or_eq_true] at ht
        rcases ht with da | db
        · simp [ih a ha (by omega) da]
        · simp [ih b hb (by omega) db]

lemma super_value_false (n : ℕ) (C : Circuit) (hC : Proper n C)
    (base pair : Fin n → Bool) (d : ℕ → Bool)
    (hbase : ∀ i, base i = true → pair i = true)
    (hinit : ∀ i (hi : i < n), d i = true → pair ⟨i, hi⟩ = true)
    (hd : DerivativeRules n C (WireValue C base) d)
    (w : ℕ) (hw : w < n + C.gates.length) (hoff : WireValue C pair w = false) :
    WireValue C base w = false ∧ d w = false := by
  constructor
  · cases hv : WireValue C base w with
    | false => rfl
    | true =>
      have yes := FirstDirty.wire_value_mono n C hC base pair hbase w hv
      rw [hoff] at yes
      cases yes
  · cases hv : d w with
    | false => rfl
    | true =>
      have yes := derivative_true_implies_super_value n C hC base pair d hbase hinit hd w hw hv
      rw [hoff] at yes
      cases yes

end PEqualNP.Outside.L_meta_2602_aux.DerivativeSuper

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

inductive Rule (n c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ j a b : ℕ)
    (op : GateOp) (rep : ℕ → Option ℕ) (g : Gate) : Prop
  | source (hc : j = c) (hr : rep (n + j) = none)
      (hg : g = ⟨.and, [z₀, z₁]⟩) : Rule n c pad z₀ z₁ j a b op rep g
  | zero (hc : j ≠ c)
      (hz : (op = .and ∧ (rep a = none ∨ rep b = none)) ∨
        (op = .or ∧ rep a = none ∧ rep b = none))
      (hr : rep (n + j) = none) (hg : g = ⟨.and, [z₀, z₁]⟩) :
      Rule n c pad z₀ z₁ j a b op rep g
  | orAlias (q : ℕ) (hc : j ≠ c) (hop : op = .or)
      (ha : rep a = none ∨ rep a = some q)
      (hb : rep b = none ∨ rep b = some q)
      (hn : rep a = some q ∨ rep b = some q)
      (hr : rep (n + j) = some q) (hg : g = ⟨.or, [q, pad q]⟩) :
      Rule n c pad z₀ z₁ j a b op rep g
  | binary (u v : ℕ) (hc : j ≠ c)
      (ha : rep a = some u) (hb : rep b = some v) (hne : u ≠ v)
      (hr : rep (n + j) = some (n + j)) (hg : g = ⟨op, [u, v]⟩) :
      Rule n c pad z₀ z₁ j a b op rep g
  | andAlias (q w : ℕ) (hc : j ≠ c) (hop : op = .and)
      (ha : rep a = some q) (hb : rep b = some q)
      (hw : w = a ∨ w = b) (hne : w ≠ q)
      (hr : rep (n + j) = some (n + j)) (hg : g = ⟨.and, [q, w]⟩) :
      Rule n c pad z₀ z₁ j a b op rep g

structure Plan (n : ℕ) (C : Circuit) (c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ : ℕ) where
  circuit : Circuit
  rep : ℕ → Option ℕ
  length_eq : circuit.gates.length = C.gates.length
  inputs : ∀ i < n, rep i = some i
  bounded : ∀ w < n + C.gates.length, ∀ q, rep w = some q → q ≤ w
  fixed : ∀ w < n + C.gates.length, ∀ q, rep w = some q → rep q = some q
  source : rep (n + c) = none
  proper : ∀ j g, circuit.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j
  unread : ∀ g ∈ circuit.gates, n + c ∉ g.inputs
  strictAlias : ∀ w < n + C.gates.length, ∀ q, rep w = some q → w ≠ q →
    ∃ j < circuit.gates.length, w = n + j ∧
      gateAt circuit j = ⟨.or, [q, pad q]⟩ ∧ q < w
  rule : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    Rule n c pad z₀ z₁ j a b g.op rep (gateAt circuit j)

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds

lemma rule_shape (n c j a b : ℕ) (op : GateOp) (rep : ℕ → Option ℕ)
    (pad : ℕ → ℕ) (z₀ z₁ : ℕ) (g : Gate)
    (hop : op = .and ∨ op = .or) (ha : a < n + j) (hb : b < n + j)
    (hrep : ∀ w < n + j, ∀ q, rep w = some q → q ≤ w ∧ rep q = some q)
    (hsource : rep (n + c) = none)
    (hpad : ∀ q, pad q < n ∧ pad q ≠ q)
    (hz₀ : z₀ < n) (hz₁ : z₁ < n) (hz : z₀ ≠ z₁)
    (rule : Rule n c pad z₀ z₁ j a b op rep g) :
    (g.op = .and ∨ g.op = .or) ∧
      ∃ u v, g.inputs = [u, v] ∧ u ≠ v ∧ u < n + j ∧ v < n + j ∧
        n + c ∉ g.inputs := by
  have repfacts (w q : ℕ) (hw : w < n + j) (hr : rep w = some q) :
      q < n + j ∧ q ≠ n + c := by
    obtain ⟨hq, hf⟩ := hrep w hw q hr
    refine ⟨hq.trans_lt hw, ?_⟩
    intro eq
    rw [eq, hsource] at hf
    cases hf
  cases rule with
  | source hc hr he =>
    rw [he]
    refine ⟨.inl rfl, z₀, z₁, rfl, hz, by omega, by omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  | zero hc hzero hr he =>
    rw [he]
    refine ⟨.inl rfl, z₀, z₁, rfl, hz, by omega, by omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  | orAlias q hc op ea eb en hr he =>
    have qf : q < n + j ∧ q ≠ n + c := by
      rcases en with eq | eq
      · exact repfacts a q ha eq
      · exact repfacts b q hb eq
    obtain ⟨pq, pne⟩ := hpad q
    rw [he]
    refine ⟨.inr rfl, q, pad q, rfl, Ne.symm pne, qf.1, by omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  | binary u v hc ea eb ne hr he =>
    obtain ⟨hu, uno⟩ := repfacts a u ha ea
    obtain ⟨hv, vno⟩ := repfacts b v hb eb
    rw [he]
    refine ⟨hop, u, v, rfl, ne, hu, hv, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  | andAlias q w hc op ea eb ew ne hr he =>
    obtain ⟨hq, qno⟩ := repfacts a q ha ea
    have hw : w < n + j := ew.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    have wr : rep w = some q := ew.elim (fun h => h.symm ▸ ea) (fun h => h.symm ▸ eb)
    have wno : w ≠ n + c := by
      intro eq
      rw [eq, hsource] at wr
      cases wr
    rw [he]
    refine ⟨.inl rfl, q, w, rfl, Ne.symm ne, hq, hw, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

lemma rule_strict_alias (n c j a b : ℕ) (op : GateOp) (rep : ℕ → Option ℕ)
    (pad : ℕ → ℕ) (z₀ z₁ : ℕ) (g : Gate)
    (ha : a < n + j) (hb : b < n + j)
    (hrep : ∀ w < n + j, ∀ q, rep w = some q → q ≤ w)
    (rule : Rule n c pad z₀ z₁ j a b op rep g)
    (q : ℕ) (hout : rep (n + j) = some q) (hne : n + j ≠ q) :
    g = ⟨.or, [q, pad q]⟩ ∧ q < n + j := by
  cases rule with
  | source hc hr he => rw [hr] at hout; cases hout
  | zero hc hz hr he => rw [hr] at hout; cases hout
  | orAlias r hc op ea eb en hr he =>
    have rq : r = q := Option.some.inj (hr.symm.trans hout)
    subst r
    refine ⟨he, ?_⟩
    rcases en with eq | eq
    · exact (hrep a ha q eq).trans_lt ha
    · exact (hrep b hb q eq).trans_lt hb
  | binary u v hc ea eb ne hr he =>
    exact (hne (Option.some.inj (hr.symm.trans hout))).elim
  | andAlias r w hc op ea eb ew ne hr he =>
    exact (hne (Option.some.inj (hr.symm.trans hout))).elim

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.ClampPlan

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative

def pad (q : ℕ) : ℕ := if q = 1 then 2 else 1

lemma pad_lt (q : ℕ) : pad q < 26 := by
  unfold pad
  split <;> omega

lemma pad_ne (q : ℕ) : pad q ≠ q := by
  unfold pad
  split <;> omega

lemma pad_unmarked (q : ℕ) : pad q ≠ 0 ∧ pad q ≠ 13 := by
  unfold pad
  split <;> omega

lemma collision_alias (a b q w : ℕ) (hab : a ≠ b)
    (ha : a < w) (hb : b < w) (hqa : q ≤ a) (hqb : q ≤ b) :
    ∃ r, (r = a ∨ r = b) ∧ q < r ∧ r < w := by
  by_cases hqa' : q = a
  · exact ⟨b, Or.inr rfl, by omega, hb⟩
  · exact ⟨a, Or.inl rfl, by omega, ha⟩

def nextRep (op : GateOp) (w : ℕ) (ra rb : Option ℕ) : Option ℕ :=
  match op, ra, rb with
  | .and, some _, some _ => some w
  | .or, some a, some b => if a = b then some a else some w
  | .or, some a, none => some a
  | .or, none, some b => some b
  | _, _, _ => none

def represent (n : ℕ) (C : Circuit) (c : ℕ) (w : ℕ) : Option ℕ :=
  if w < n then some w else
  if w = c then none else
  match C.gates[w - n]? with
  | none => none
  | some g =>
    match g.inputs with
    | [a, b] =>
      if _h : a < w ∧ b < w then
        nextRep g.op w (represent n C c a) (represent n C c b)
      else none
    | _ => none
termination_by w
decreasing_by all_goals omega

lemma nextRep_some (op : GateOp) (w q : ℕ) (ra rb : Option ℕ)
    (h : nextRep op w ra rb = some q) : q = w ∨ ra = some q ∨ rb = some q := by
  cases op <;> cases ra <;> cases rb <;> simp_all [nextRep]
  split at h <;> simp_all

lemma represent_input (n : ℕ) (C : Circuit) (c i : ℕ) (hi : i < n) :
    represent n C c i = some i := by rw [represent]; simp [hi]

lemma represent_source (n : ℕ) (C : Circuit) (c : ℕ) (hc : n ≤ c) :
    represent n C c c = none := by
  rw [represent, if_neg (Nat.not_lt.mpr hc), if_pos rfl]

lemma represent_gate (n : ℕ) (C : Circuit) (c j : ℕ) (g : Gate) (a b : ℕ)
    (hc : n + j ≠ c) (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) :
    represent n C c (n + j) = nextRep g.op (n + j)
      (represent n C c a) (represent n C c b) := by
  rw [represent]
  simp [hc, hg, hin, ha, hb]

lemma represent_bounded (n : ℕ) (C : Circuit) (hC : Proper n C) (c : ℕ)
    (hc : n ≤ c) : ∀ w < n + C.gates.length, ∀ q,
    represent n C c w = some q → q ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw q hr
    by_cases hwn : w < n
    · rw [represent_input n C c w hwn] at hr
      cases hr
      omega
    · by_cases hcw : w = c
      · subst w
        rw [represent_source n C c hc] at hr
        contradiction
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := List.getElem?_eq_getElem (l := C.gates) hj
        obtain ⟨_, a, b, hin, _, ha, hb⟩ := hC j _ hg
        rw [represent_gate n C c j _ a b hcw hg hin ha hb] at hr
        rcases nextRep_some _ _ _ _ _ hr with hq | hqa | hqb
        · omega
        · exact (ih a ha (by omega) q hqa).trans (Nat.le_of_lt ha)
        · exact (ih b hb (by omega) q hqb).trans (Nat.le_of_lt hb)

lemma represent_fixed (n : ℕ) (C : Circuit) (hC : Proper n C) (c : ℕ)
    (hc : n ≤ c) : ∀ w < n + C.gates.length, ∀ q,
    represent n C c w = some q → represent n C c q = some q := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw q hr
    by_cases hwn : w < n
    · rw [represent_input n C c w hwn] at hr
      cases hr
      exact represent_input n C c w hwn
    · by_cases hcw : w = c
      · subst w
        rw [represent_source n C c hc] at hr
        contradiction
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := List.getElem?_eq_getElem (l := C.gates) hj
        obtain ⟨_, a, b, hin, _, ha, hb⟩ := hC j _ hg
        have he := represent_gate n C c j _ a b hcw hg hin ha hb
        have hr' := hr
        rw [he] at hr'
        rcases nextRep_some _ _ _ _ _ hr' with hq | hqa | hqb
        · simpa [hq] using hr
        · exact ih a ha (by omega) q hqa
        · exact ih b hb (by omega) q hqb

lemma represent_avoids_source (n : ℕ) (C : Circuit) (hC : Proper n C) (c : ℕ)
    (hc : n ≤ c) (w q : ℕ) (hw : w < n + C.gates.length)
    (hr : represent n C c w = some q) : w ≠ c ∧ q ≠ c := by
  have hs := represent_source n C c hc
  have hf := represent_fixed n C hC c hc w hw q hr
  constructor
  · intro he
    rw [he, hs] at hr
    contradiction
  · intro he
    rw [he, hs] at hf
    contradiction

def aliasOperand (a b q : ℕ) : ℕ := if a = q then b else a

lemma aliasOperand_mem (a b q : ℕ) : aliasOperand a b q = a ∨ aliasOperand a b q = b := by
  unfold aliasOperand
  split <;> simp

lemma aliasOperand_ne (a b q : ℕ) (hab : a ≠ b) : aliasOperand a b q ≠ q := by
  unfold aliasOperand
  split <;> omega

def localGate (pad : ℕ → ℕ) (z₀ z₁ a b : ℕ) (op : GateOp)
    (ra rb : Option ℕ) : Gate :=
  match op, ra, rb with
  | .and, some u, some v =>
    if u = v then ⟨.and, [u, aliasOperand a b u]⟩ else ⟨.and, [u, v]⟩
  | .or, some u, some v =>
    if u = v then ⟨.or, [u, pad u]⟩ else ⟨.or, [u, v]⟩
  | .or, some u, none => ⟨.or, [u, pad u]⟩
  | .or, none, some v => ⟨.or, [v, pad v]⟩
  | _, _, _ => ⟨.and, [z₀, z₁]⟩

lemma localGate_rule (n c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ j a b : ℕ)
    (op : GateOp) (rep : ℕ → Option ℕ) (hc : j ≠ c)
    (hop : op = .and ∨ op = .or) (hab : a ≠ b)
    (hr : rep (n + j) = nextRep op (n + j) (rep a) (rep b)) :
    PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule n c pad z₀ z₁ j a b op rep
      (localGate pad z₀ z₁ a b op (rep a) (rep b)) := by
  rcases hop with rfl | rfl
  · cases ha : rep a with
    | none =>
      apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.zero hc
      · exact Or.inl ⟨rfl, Or.inl ha⟩
      · simpa [nextRep, ha] using hr
      · simp [localGate]
    | some u =>
      cases hb : rep b with
      | none =>
        apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.zero hc
        · exact Or.inl ⟨rfl, Or.inr hb⟩
        · simpa [nextRep, ha, hb] using hr
        · simp [localGate]
      | some v =>
        by_cases huv : u = v
        · subst v
          apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.andAlias u (aliasOperand a b u) hc rfl ha hb
          · exact aliasOperand_mem a b u
          · exact aliasOperand_ne a b u hab
          · simpa [nextRep, ha, hb] using hr
          · simp [localGate]
        · apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.binary u v hc ha hb huv
          · simpa [nextRep, ha, hb] using hr
          · simp [localGate, huv]
  · cases ha : rep a with
    | none =>
      cases hb : rep b with
      | none =>
        apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.zero hc
        · exact Or.inr ⟨rfl, ha, hb⟩
        · simpa [nextRep, ha, hb] using hr
        · simp [localGate]
      | some v =>
        apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.orAlias v hc rfl
        · exact Or.inl ha
        · exact Or.inr hb
        · exact Or.inr hb
        · simpa [nextRep, ha, hb] using hr
        · simp [localGate]
    | some u =>
      cases hb : rep b with
      | none =>
        apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.orAlias u hc rfl
        · exact Or.inr ha
        · exact Or.inl hb
        · exact Or.inl ha
        · simpa [nextRep, ha, hb] using hr
        · simp [localGate]
      | some v =>
        by_cases huv : u = v
        · subst v
          apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.orAlias u hc rfl
          · exact Or.inr ha
          · exact Or.inr hb
          · exact Or.inl ha
          · simpa [nextRep, ha, hb] using hr
          · simp [localGate]
        · apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.binary u v hc ha hb huv
          · simpa [nextRep, ha, hb, huv] using hr
          · simp [localGate, huv]

def replacement (n : ℕ) (C : Circuit) (c : ℕ) (pad : ℕ → ℕ)
    (z₀ z₁ j : ℕ) : Gate :=
  if j = c then ⟨.and, [z₀, z₁]⟩ else
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
  match g.inputs with
  | [a, b] => localGate pad z₀ z₁ a b g.op
      (represent n C (n + c) a) (represent n C (n + c) b)
  | _ => ⟨.and, [z₀, z₁]⟩

def rewritten (n : ℕ) (C : Circuit) (c : ℕ) (pad : ℕ → ℕ)
    (z₀ z₁ : ℕ) : Circuit :=
  ⟨List.ofFn fun j : Fin C.gates.length => replacement n C c pad z₀ z₁ j.val,
    C.output⟩

lemma rewritten_length (n : ℕ) (C : Circuit) (c : ℕ) (pad : ℕ → ℕ)
    (z₀ z₁ : ℕ) : (rewritten n C c pad z₀ z₁).gates.length = C.gates.length := by
  simp [rewritten]

lemma rewritten_gate (n : ℕ) (C : Circuit) (c : ℕ) (pad : ℕ → ℕ)
    (z₀ z₁ j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt (rewritten n C c pad z₀ z₁) j =
      replacement n C c pad z₀ z₁ j := by
  simp [rewritten, PEqualNP.MetaComplexity.NestedCover.gateAt,
    List.getD_eq_getElem?_getD, hj]

lemma replacement_rule (n : ℕ) (C : Circuit) (hC : Proper n C)
    (c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b]) :
    PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule n c pad z₀ z₁ j a b g.op
      (represent n C (n + c)) (replacement n C c pad z₀ z₁ j) := by
  by_cases hc : j = c
  · apply PEqualNP.Outside.L_meta_2602_aux.Clamp.Rule.source hc
    · subst j
      exact represent_source n C (n + c) (by omega)
    · simp [replacement, hc]
  · have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
    obtain ⟨hop, a', b', hins, hne, ha, hb⟩ := hC j g hg
    have heq : a' = a ∧ b' = b := by simpa using hins.symm.trans hin
    have hea := heq.1
    have heb := heq.2
    subst a'
    subst b'
    have hre := represent_gate n C (n + c) j g a b (by omega) hg hin ha hb
    simpa [replacement, hc, hgat, hin] using
      localGate_rule n c pad z₀ z₁ j a b g.op (represent n C (n + c)) hc hop hne hre

lemma rewritten_shape (n : ℕ) (C : Circuit) (hC : Proper n C)
    (c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ j : ℕ) (hj : j < C.gates.length)
    (hpad : ∀ q, pad q < n ∧ pad q ≠ q)
    (hz₀ : z₀ < n) (hz₁ : z₁ < n) (hz : z₀ ≠ z₁) :
    let g := PEqualNP.MetaComplexity.NestedCover.gateAt (rewritten n C c pad z₀ z₁) j
    (g.op = .and ∨ g.op = .or) ∧
      ∃ u v, g.inputs = [u, v] ∧ u ≠ v ∧ u < n + j ∧ v < n + j ∧
        n + c ∉ g.inputs := by
  dsimp only
  rw [rewritten_gate n C c pad z₀ z₁ j hj]
  have hg := List.getElem?_eq_getElem (l := C.gates) hj
  obtain ⟨hop, a, b, hin, _, ha, hb⟩ := hC j _ hg
  apply PEqualNP.Outside.L_meta_2602_aux.Clamp.rule_shape n c j a b _
    (represent n C (n + c)) pad z₀ z₁ _ hop ha hb
  · intro w hw q hr
    exact ⟨represent_bounded n C hC (n + c) (by omega) w (by omega) q hr,
      represent_fixed n C hC (n + c) (by omega) w (by omega) q hr⟩
  · exact represent_source n C (n + c) (by omega)
  · exact hpad
  · exact hz₀
  · exact hz₁
  · exact hz
  · exact replacement_rule n C hC c pad z₀ z₁ j _ a b hg hin

def buildPlan (n : ℕ) (C : Circuit) (hC : Proper n C)
    (c : ℕ) (pad : ℕ → ℕ) (z₀ z₁ : ℕ)
    (hpad : ∀ q, pad q < n ∧ pad q ≠ q)
    (hz₀ : z₀ < n) (hz₁ : z₁ < n) (hz : z₀ ≠ z₁) :
    PEqualNP.Outside.L_meta_2602_aux.Clamp.Plan n C c pad z₀ z₁ where
  circuit := rewritten n C c pad z₀ z₁
  rep := represent n C (n + c)
  length_eq := rewritten_length n C c pad z₀ z₁
  inputs := represent_input n C (n + c)
  bounded := represent_bounded n C hC (n + c) (by omega)
  fixed := represent_fixed n C hC (n + c) (by omega)
  source := represent_source n C (n + c) (by omega)
  proper := by
    intro j g hg
    have hj : j < C.gates.length := by
      have hj' := (List.getElem?_eq_some_iff.mp hg).1
      rwa [rewritten_length] at hj'
    have he : PEqualNP.MetaComplexity.NestedCover.gateAt (rewritten n C c pad z₀ z₁) j = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
    have hs := rewritten_shape n C hC c pad z₀ z₁ j hj hpad hz₀ hz₁ hz
    rw [he] at hs
    obtain ⟨hop, u, v, hin, hne, hu, hv, _⟩ := hs
    exact ⟨hop, u, v, hin, hne, hu, hv⟩
  unread := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hjC : j < C.gates.length := by rwa [rewritten_length] at hj
    have hs := rewritten_shape n C hC c pad z₀ z₁ j hjC hpad hz₀ hz₁ hz
    obtain ⟨_, u, v, _, _, _, _, hno⟩ := hs
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj] using hno
  strictAlias := by
    intro w hw q hr hne
    by_cases hwn : w < n
    · rw [represent_input n C (n + c) w hwn] at hr
      exact (hne (Option.some.inj hr)).elim
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨_, a, b, hin, _, ha, hb⟩ := hC j _ hg
      have hru := replacement_rule n C hC c pad z₀ z₁ j _ a b hg hin
      have hs := PEqualNP.Outside.L_meta_2602_aux.Clamp.rule_strict_alias n c j a b _
        (represent n C (n + c)) pad z₀ z₁ _ ha hb (by
          intro u hu r hur
          exact represent_bounded n C hC (n + c) (by omega) u (by omega) r hur)
        hru q hr hne
      refine ⟨j, ?_, rfl, ?_, hs.2⟩
      · rw [rewritten_length]
        exact hj
      · rw [rewritten_gate n C c pad z₀ z₁ j hj]
        exact hs.1
  rule := by
    intro j g a b hg hin
    have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
    rw [rewritten_gate n C c pad z₀ z₁ j hj]
    exact replacement_rule n C hC c pad z₀ z₁ j g a b hg hin

end PEqualNP.Outside.L_meta_2602_aux.ClampPlan

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Derivative

def repValue (V : ℕ → Bool) (r : Option ℕ) : Bool :=
  match r with
  | none => false
  | some q => V q

lemma gateAt_some {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  congr 1
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma plan_gate_values {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (V : ℕ → Bool)
    (hV : ValueRules n P.circuit V) (j : ℕ) (hj : j < P.circuit.gates.length)
    (op : GateOp) (a b : ℕ) (hg : gateAt P.circuit j = ⟨op, [a, b]⟩) :
    (op = .and → V (n + j) = (V a && V b)) ∧
    (op = .or → V (n + j) = (V a || V b)) := by
  have get := gateAt_some hj
  rw [hg] at get
  exact hV j _ a b get rfl

lemma rep_value_rules {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C)
    (V : ℕ → Bool) (hV : ValueRules n P.circuit V) :
    ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] → j ≠ c →
      (g.op = .and → repValue V (P.rep (n + j)) =
        (repValue V (P.rep a) && repValue V (P.rep b))) ∧
      (g.op = .or → repValue V (P.rep (n + j)) =
        (repValue V (P.rep a) || repValue V (P.rep b))) := by
  intro j g a b hj hab hjc
  have hjC : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjD : j < P.circuit.gates.length := by rw [P.length_eq]; exact hjC
  obtain ⟨hop, aa, bb, hab', _, haa, hbb⟩ := hC j g hj
  have eab : a = aa ∧ b = bb := by simpa [hab] using hab'
  have bounds : a < n + C.gates.length ∧ b < n + C.gates.length := by omega
  cases P.rule j g a b hj hab with
  | source hc _ _ => exact (hjc hc).elim
  | zero _ hz hr _ =>
    rw [hr]
    rcases hz with ⟨hand, ha | hb⟩ | ⟨hor, ha, hb⟩ <;>
      simp_all [repValue]
  | orAlias q _ hor ha hb hn hr _ =>
    rw [hr]
    constructor
    · intro hand; rw [hor] at hand; cases hand
    · intro _
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp_all [repValue]
  | binary u v _ ha hb _ hr hg =>
    rw [hr, ha, hb]
    simpa only [repValue] using plan_gate_values P V hV j hjD g.op u v hg
  | andAlias q w _ hand ha hb hw hne hr hg =>
    have hwr : P.rep w = some q := by rcases hw with rfl | rfl <;> assumption
    have hwlt : w < n + C.gates.length := by rcases hw with rfl | rfl <;> omega
    obtain ⟨k, hk, hwk, hpad, _⟩ := P.strictAlias w hwlt q hwr hne
    have vw := (plan_gate_values P V hV k hk .or q (pad q) hpad).2 rfl
    have vo := (plan_gate_values P V hV j hjD .and q w hg).1 rfl
    have ident : V (n + j) = V q := by
      rw [vo, hwk, vw]
      cases V q <;> cases V (pad q) <;> rfl
    rw [hr, ha, hb]
    constructor
    · intro _; simpa [repValue] using ident
    · intro hor; rw [hand] at hor; cases hor

lemma plan_value_relation {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C)
    (v V : ℕ → Bool) (hv : ValueRules n C v) (hV : ValueRules n P.circuit V)
    (hinput : ∀ i < n, V i = v i) :
    ∀ w < n + C.gates.length,
      (repValue V (P.rep w) = true → v w = true) ∧
      (v (n + c) = false → repValue V (P.rep w) = v w) := by
  have rules := rep_value_rules P hC V hV
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases low : w < n
    · rw [P.inputs w low]
      simp only [repValue, hinput w low]
      exact ⟨fun h => h, fun _ => trivial⟩
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨op, a, b, hab, _, ha, hb⟩ := hC j g hg
    by_cases jc : j = c
    · subst j
      rw [P.source]
      simp only [repValue, Bool.false_eq_true, false_implies, true_and]
      intro h; exact h.symm
    have ia := ih a ha (by omega)
    have ib := ih b hb (by omega)
    rcases op with op | op
    · rw [(rules j g a b hg hab jc).1 op, (hv j g a b hg hab).1 op]
      constructor
      · intro h
        exact Bool.and_eq_true_iff.mpr
          ⟨ia.1 (Bool.and_eq_true_iff.mp h).1, ib.1 (Bool.and_eq_true_iff.mp h).2⟩
      · intro h; rw [ia.2 h, ib.2 h]
    · rw [(rules j g a b hg hab jc).2 op, (hv j g a b hg hab).2 op]
      constructor
      · intro h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ia.1 h))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (ib.1 h))
      · intro h; rw [ia.2 h, ib.2 h]

lemma plan_value_eq {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C)
    (v V : ℕ → Bool) (hv : ValueRules n C v) (hV : ValueRules n P.circuit V)
    (hinput : ∀ i < n, V i = v i)
    (hsource : v (n + c) = false)
    (hz₀ : V z₀ = false) (hz₁ : V z₁ = false)
    (hpad : ∀ q, V (pad q) = false) :
    ∀ w < n + C.gates.length, V w = v w := by
  have rel := plan_value_relation P hC v V hv hV hinput
  intro w hw
  by_cases low : w < n
  · exact hinput w low
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < C.gates.length := by omega
  have hjD : j < P.circuit.gates.length := by rw [P.length_eq]; exact hj
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  obtain ⟨_, a, b, hab, _, _, _⟩ := hC j g hg
  have eq := (rel (n + j) hw).2 hsource
  cases P.rule j g a b hg hab with
  | source _ hr hp | zero _ _ hr hp =>
    rw [hr] at eq
    rw [(plan_gate_values P V hV j hjD .and z₀ z₁ hp).1 rfl, hz₀, hz₁]
    exact eq
  | orAlias q _ _ _ _ _ hr hp =>
    rw [hr] at eq
    rw [(plan_gate_values P V hV j hjD .or q (pad q) hp).2 rfl, hpad q]
    simpa only [repValue, Bool.or_false] using eq
  | binary _ _ _ _ _ _ hr _ | andAlias _ _ _ _ _ _ _ _ hr _ =>
    simpa only [hr, repValue] using eq

lemma plan_wire_relation {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      (repValue (WireValue P.circuit x) (P.rep w) = true → WireValue C x w = true) ∧
      (WireValue C x (n + c) = false →
        repValue (WireValue P.circuit x) (P.rep w) = WireValue C x w) := by
  apply plan_value_relation P hC _ _ (wire_value_rules C hC x)
    (wire_value_rules P.circuit P.proper x)
  intro i hi
  rw [wire_value_input _ _ _ hi, wire_value_input _ _ _ hi]

lemma plan_output_exists {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C) (x : Fin n → Bool)
    (hy : C.eval (List.ofFn x) = true) (hz : WireValue C x (n + c) = false) :
    ∃ q, P.rep C.output = some q ∧ q < n + C.gates.length ∧ q ≠ n + c := by
  have ho : C.output < n + C.gates.length := by
    simpa using output_lt_of_eval_true C (List.ofFn x) hy
  have eq := (plan_wire_relation P hC x C.output ho).2 hz
  change repValue (WireValue P.circuit x) (P.rep C.output) = C.eval (List.ofFn x) at eq
  rw [hy] at eq
  cases hr : P.rep C.output with
  | none => simp [hr, repValue] at eq
  | some q =>
    refine ⟨q, rfl, lt_of_le_of_lt (P.bounded C.output ho q hr) ho, ?_⟩
    intro hq
    have fixed := P.fixed C.output ho q hr
    rw [hq, P.source] at fixed
    contradiction

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2602_aux.Derivative

lemma plan_derivative_relation (n : ℕ) (C : Circuit) (c : ℕ)
    (pad : ℕ → ℕ) (z₀ z₁ : ℕ) (P : Plan n C c pad z₀ z₁)
    (hC : Proper n C) (v d : ℕ → Bool) (hd : DerivativeRules n C v d)
    (hsource : d (n + c) = false)
    (hNone : ∀ w < n + C.gates.length, P.rep w = none → v w = false) :
    ∀ w < n + C.gates.length,
      (P.rep w = none → d w = false) ∧
      (∀ q, P.rep w = some q → d w = d q) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    have fresh (hr : P.rep w = some w) :
        (P.rep w = none → d w = false) ∧
        (∀ q, P.rep w = some q → d w = d q) := by
      constructor
      · intro hn
        rw [hr] at hn
        cases hn
      · intro q hq
        have eq : w = q := Option.some.inj (hr.symm.trans hq)
        exact congrArg d eq
    by_cases hwn : w < n
    · exact fresh (P.inputs w hwn)
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop, a, b, ins, _, ha, hb⟩ := hC j _ hg
      have ia := ih a ha (by omega)
      have ib := ih b hb (by omega)
      have va := hNone a (by omega)
      have vb := hNone b (by omega)
      have rule := P.rule j _ a b hg ins
      cases rule with
      | source hc hr he =>
        constructor
        · intro _
          simpa only [hc] using hsource
        · intro q hq
          rw [hr] at hq
          cases hq
      | zero hc hz hr he =>
        have zero : d (n + j) = false := by
          rcases hz with ⟨op, ea | eb⟩ | ⟨op, ea, eb⟩
          · rw [(hd j _ a b hg ins).1 op]
            simp [va ea, ia.1 ea]
          · rw [(hd j _ a b hg ins).1 op]
            simp [vb eb, ib.1 eb]
          · rw [(hd j _ a b hg ins).2 op]
            simp [ia.1 ea, ib.1 eb]
        constructor
        · exact fun _ => zero
        · intro q hq
          rw [hr] at hq
          cases hq
      | orAlias q hc op ea eb en hr he =>
        have da : d a = false ∨ d a = d q := ea.imp ia.1 (ia.2 q)
        have db : d b = false ∨ d b = d q := eb.imp ib.1 (ib.2 q)
        have dn : d a = d q ∨ d b = d q := en.imp (ia.2 q) (ib.2 q)
        have eq : d (n + j) = d q := by
          rw [(hd j _ a b hg ins).2 op]
          rcases da with da | da <;> rcases db with db | db <;>
            rcases dn with dn | dn <;> cases dq : d q <;> simp_all
        constructor
        · intro hn
          rw [hr] at hn
          cases hn
        · intro r er
          have qr : q = r := Option.some.inj (hr.symm.trans er)
          exact eq.trans (congrArg d qr)
      | binary u vv hc ea eb ne hr he => exact fresh hr
      | andAlias q r hc op ea eb er ne hr he => exact fresh hr

lemma plan_derivative_rules (n : ℕ) (C : Circuit) (c : ℕ)
    (pad : ℕ → ℕ) (z₀ z₁ : ℕ) (P : Plan n C c pad z₀ z₁)
    (hC : Proper n C) (v V d : ℕ → Bool) (hd : DerivativeRules n C v d)
    (hsource : d (n + c) = false)
    (hNone : ∀ w < n + C.gates.length, P.rep w = none → v w = false)
    (hSome : ∀ w < n + C.gates.length, ∀ q, P.rep w = some q → v w = v q)
    (hPhysical : ∀ w < n + C.gates.length, V w = v w)
    (hpad : ∀ q, d (pad q) = false) (hz₀ : d z₀ = false) (hz₁ : d z₁ = false) :
    DerivativeRules n P.circuit V d := by
  have repd := plan_derivative_relation n C c pad z₀ z₁ P hC v d hd hsource hNone
  intro j g u vv hg hin
  have hj : j < P.circuit.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
  have oldj : j < C.gates.length := by rw [P.length_eq] at hj; exact hj
  have oldg := List.getElem?_eq_getElem (l := C.gates) oldj
  obtain ⟨hop, a, b, oldins, _, ha, hb⟩ := hC j _ oldg
  have haB : a < n + C.gates.length := by omega
  have hbB : b < n + C.gates.length := by omega
  have hnew : gateAt P.circuit j = g := by simp [gateAt, hg]
  have rule := P.rule j _ a b oldg oldins
  rw [hnew] at rule
  have known (q : ℕ) (w : ℕ) (hw : w < n + C.gates.length) (hq : P.rep w = some q) :
      V q = v w ∧ d q = d w := by
    have qb : q < n + C.gates.length := (P.bounded w hw q hq).trans_lt hw
    exact ⟨(hPhysical q qb).trans (hSome w hw q hq).symm, ((repd w hw).2 q hq).symm⟩
  cases rule with
  | source hc hr he =>
    have eq : z₀ = u ∧ z₁ = vv := by simpa [he] using hin
    rcases eq with ⟨rfl, rfl⟩
    constructor
    · intro _
      simpa only [hc, hz₀, hz₁, Bool.and_false, Bool.false_and, Bool.or_self] using hsource
    · intro op
      simp [he] at op
  | zero hc hz hr he =>
    have eq : z₀ = u ∧ z₁ = vv := by simpa [he] using hin
    rcases eq with ⟨rfl, rfl⟩
    have dz := (repd (n + j) (by omega)).1 hr
    constructor
    · intro _
      simpa only [hz₀, hz₁, Bool.and_false, Bool.false_and, Bool.or_self] using dz
    · intro op
      simp [he] at op
  | orAlias q hc op ea eb en hr he =>
    have eq : q = u ∧ pad q = vv := by simpa [he] using hin
    rcases eq with ⟨rfl, rfl⟩
    have dz := (repd (n + j) (by omega)).2 q hr
    constructor
    · intro op'
      simp [he] at op'
    · intro _
      simpa only [hpad, Bool.or_false] using dz
  | binary r s hc ea eb ne hr he =>
    have eq : r = u ∧ s = vv := by simpa [he] using hin
    rcases eq with ⟨rfl, rfl⟩
    obtain ⟨vu, du⟩ := known r a haB ea
    obtain ⟨vvv, dv⟩ := known s b hbB eb
    constructor
    · intro op
      have oo : C.gates[j].op = .and := by simpa [he] using op
      rw [vu, vvv, du, dv]
      exact (hd j _ a b oldg oldins).1 oo
    · intro op
      have oo : C.gates[j].op = .or := by simpa [he] using op
      rw [du, dv]
      exact (hd j _ a b oldg oldins).2 oo
  | andAlias q w hc op ea eb ew ne hr he =>
    have eq : q = u ∧ w = vv := by simpa [he] using hin
    rcases eq with ⟨rfl, rfl⟩
    obtain ⟨vu, du⟩ := known q a haB ea
    have abv : v b = v a := (hSome b hbB q eb).trans (hSome a haB q ea).symm
    have abd : d b = d a := ((repd b hbB).2 q eb).trans ((repd a haB).2 q ea).symm
    have wv : V w = v a := by
      rcases ew with ew | ew
      · rw [ew]
        exact hPhysical a haB
      · rw [ew]
        exact (hPhysical b hbB).trans abv
    have wd : d w = d a := by
      rcases ew with ew | ew
      · exact congrArg d ew
      · exact (congrArg d ew).trans abd
    constructor
    · intro _
      rw [vu, wv, du, wd]
      simpa only [abv, abd] using (hd j _ a b oldg oldins).1 op
    · intro op'
      simp [he] at op'

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.ClampSemantic

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative
open PEqualNP.Outside.L_meta_2602_aux.FirstDirty

lemma semantics_from_minterms (n : ℕ) (C D : Circuit) (hD : Proper n D)
    (c : ℕ)
    (hdown : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true →
      C.eval (List.ofFn x) = true)
    (hagree : ∀ x : Fin n → Bool, WireValue C x c = false →
      D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hcover : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ y : Fin n → Bool, C.eval (List.ofFn y) = true ∧
        (∀ i, y i = true → x i = true) ∧ WireValue C y c = false) :
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hdown x
  · intro hx
    obtain ⟨y, hy, hyx, hc⟩ := hcover x hx
    have hDy : D.eval (List.ofFn y) = true := by rw [hagree y hc]; exact hy
    exact wire_value_mono n D hD y x hyx D.output hDy

def incident (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def edgeInput (p l : Fin 13) : Fin 26 → Bool :=
  fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

def PlaneSpec (C : Circuit) : Prop :=
  ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, incident p l ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

lemma edge_positive (C : Circuit) (hC : PlaneSpec C)
    (p l : Fin 13) (hpl : incident p l) :
    C.eval (List.ofFn (edgeInput p l)) = true := by
  apply (hC _).2
  exact ⟨p, l, hpl, by simp [edgeInput], by simp [edgeInput]⟩

lemma edge_le (x : Fin 26 → Bool) (p l : Fin 13)
    (hp : x (Fin.castAdd 13 p) = true) (hl : x (Fin.natAdd 13 l) = true) :
    ∀ i, edgeInput p l i = true → x i = true := by
  intro i hi
  have he : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l := of_decide_eq_true hi
  rcases he with rfl | rfl
  · exact hp
  · exact hl

lemma plane_semantics_from_edges (C D : Circuit) (hC : PlaneSpec C)
    (hD : Proper 26 D)
    (hdown : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true →
      C.eval (List.ofFn x) = true)
    (hedge : ∀ p l : Fin 13, incident p l →
      D.eval (List.ofFn (edgeInput p l)) = true) : PlaneSpec D := by
  intro x
  constructor
  · intro hx
    exact (hC x).1 (hdown x hx)
  · intro hx
    obtain ⟨p, l, hpl, hp, hl⟩ := hx
    exact wire_value_mono 26 D hD (edgeInput p l) x (edge_le x p l hp hl)
      D.output (hedge p l hpl)

lemma plane_clamp_semantics (C D : Circuit) (hC : PlaneSpec C)
    (hD : Proper 26 D) (c : ℕ)
    (hdown : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true →
      C.eval (List.ofFn x) = true)
    (hagree : ∀ x : Fin 26 → Bool, WireValue C x c = false →
      D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (hzero : ∀ p l : Fin 13, incident p l →
      WireValue C (edgeInput p l) c = false) : PlaneSpec D := by
  apply plane_semantics_from_edges C D hC hD hdown
  intro p l hpl
  rw [hagree (edgeInput p l) (hzero p l hpl)]
  exact edge_positive C hC p l hpl

end PEqualNP.Outside.L_meta_2602_aux.ClampSemantic

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Derivative

lemma realize_plan (n : ℕ) (C : Circuit) (c : ℕ)
    (pad : ℕ → ℕ) (z₀ z₁ : ℕ) (P : Plan n C c pad z₀ z₁)
    (hC : Proper n C) (hc : c < C.gates.length)
    (hpadLt : ∀ q, pad q < n) (hz₀Lt : z₀ < n) (hz₁Lt : z₁ < n)
    (hpos : ∃ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ∧ WireValue C x (n + c) = false)
    (hcover : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ y : Fin n → Bool, C.eval (List.ofFn y) = true ∧
        (∀ i, y i = true → x i = true) ∧ WireValue C y (n + c) = false)
    (base : Fin 2 → Fin n → Bool) (initial d : Fin 2 → ℕ → Bool)
    (hinit : ∀ q i, i < n → d q i = initial q i)
    (hd : ∀ q, DerivativeRules n C (WireValue C (base q)) (d q))
    (hzero : ∀ q, d q C.output = false)
    (hsource : ∀ q, WireValue C (base q) (n + c) = false ∧ d q (n + c) = false)
    (hpad : ∀ q r, WireValue C (base q) (pad r) = false ∧ d q (pad r) = false)
    (hz₀ : ∀ q, WireValue C (base q) z₀ = false ∧ d q z₀ = false)
    (hz₁ : ∀ q, WireValue C (base q) z₁ = false ∧ d q z₁ = false) :
    ∃ D : Circuit, Proper n D ∧ D.size + 1 = C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      ∀ q : Fin 2, ∃ e : ℕ → Bool, (∀ i < n, e i = initial q i) ∧
        DerivativeRules n D (WireValue D (base q)) e ∧ e D.output = false := by
  obtain ⟨x, hx, hxc⟩ := hpos
  have ho : C.output < n + C.gates.length := by
    simpa using output_lt_of_eval_true C (List.ofFn x) hx
  obtain ⟨out, hout, _, hne⟩ := plan_output_exists P hC x hx hxc
  let E : Circuit := ⟨P.circuit.gates, out⟩
  have hE : Proper n E := P.proper
  have hlen : E.gates.length = C.gates.length := P.length_eq
  have hEc : c < E.gates.length := by rw [hlen]; exact hc
  have hdead : ∀ g ∈ E.gates, n + c ∉ g.inputs := P.unread
  have heval : ∀ x : Fin n → Bool,
      E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    apply ClampSemantic.semantics_from_minterms n C E hE (n + c)
    · intro x hy
      have r := (plan_wire_relation P hC x C.output ho).1
      rw [hout] at r
      exact r hy
    · intro x hxc
      have r := (plan_wire_relation P hC x C.output ho).2 hxc
      change WireValue P.circuit x out = WireValue C x C.output
      simpa only [hout, repValue] using r
    · exact hcover
  have input_eq (q : Fin 2) (i : ℕ) (hi : i < n) :
      WireValue P.circuit (base q) i = WireValue C (base q) i := by
    rw [wire_value_input _ _ _ hi, wire_value_input _ _ _ hi]
  have phys (q : Fin 2) : ∀ w < n + C.gates.length,
      WireValue P.circuit (base q) w = WireValue C (base q) w := by
    apply plan_value_eq P hC _ _ (wire_value_rules C hC (base q))
      (wire_value_rules P.circuit P.proper (base q)) (input_eq q) (hsource q).1
    · exact (input_eq q z₀ hz₀Lt).trans (hz₀ q).1
    · exact (input_eq q z₁ hz₁Lt).trans (hz₁ q).1
    · intro r
      exact (input_eq q (pad r) (hpadLt r)).trans (hpad q r).1
  have hNone (q : Fin 2) (w : ℕ) (hw : w < n + C.gates.length)
      (hr : P.rep w = none) : WireValue C (base q) w = false := by
    have r := (plan_wire_relation P hC (base q) w hw).2 (hsource q).1
    simpa only [hr, repValue] using r.symm
  have hSome (q : Fin 2) (w : ℕ) (hw : w < n + C.gates.length)
      (r : ℕ) (hr : P.rep w = some r) :
      WireValue C (base q) w = WireValue C (base q) r := by
    have e := (plan_wire_relation P hC (base q) w hw).2 (hsource q).1
    rw [hr] at e
    exact e.symm.trans (phys q r ((P.bounded w hw r hr).trans_lt hw))
  have hdE (q : Fin 2) : DerivativeRules n E (WireValue E (base q)) (d q) := by
    exact plan_derivative_rules n C c pad z₀ z₁ P hC _ _ _ (hd q)
      (hsource q).2 (hNone q) (hSome q) (phys q)
      (fun r => (hpad q r).2) (hz₀ q).2 (hz₁ q).2
  have hzE (q : Fin 2) : d q E.output = false := by
    have r := (plan_derivative_relation n C c pad z₀ z₁ P hC _ _ (hd q)
      (hsource q).2 (hNone q) C.output ho).2 out hout
    exact r.symm.trans (hzero q)
  refine ⟨DeadGate.erase n E c, DeadGate.erase_proper n E c hE hdead, ?_, ?_, ?_⟩
  · change (DeadGate.erase n E c).gates.length + 1 = C.gates.length
    rw [DeadGate.erase_length n E c hEc, hlen]
  · intro y
    exact (DeadGate.erase_eval n E c hE hEc hdead hne y).trans (heval y)
  · intro q
    exact DeadGate.erase_witness n E c hE hdead hne (base q) (initial q) (d q)
      (hinit q) (hdE q) (hzE q)

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds Derivative ClampSemantic

def markedBase (q : Fin 2) (i : Fin 26) : Bool :=
  decide (i.val = if q = 0 then 0 else 13)

def markedInitial (q : Fin 2) (i : ℕ) : Bool :=
  decide (i = if q = 0 then 13 else 0)

lemma inactive_gate_smaller (C : Circuit) (hC : Proper 26 C) (hF : PlaneSpec C)
    (c : ℕ) (hc : c < C.gates.length)
    (hinactive : ∀ p l : Fin 13, incident p l →
      WireValue C (edgeInput p l) (26 + c) = false)
    (d : Fin 2 → ℕ → Bool)
    (hinit : ∀ q i, i < 26 → d q i = markedInitial q i)
    (hd : ∀ q, DerivativeRules 26 C (WireValue C (markedBase q)) (d q))
    (hzero : ∀ q, d q C.output = false) :
    ∃ D : Circuit, Proper 26 D ∧ D.size + 1 = C.size ∧ PlaneSpec D ∧
      ∀ q : Fin 2, ∃ e : ℕ → Bool, (∀ i < 26, e i = markedInitial q i) ∧
        DerivativeRules 26 D (WireValue D (markedBase q)) e ∧ e D.output = false := by
  let P := ClampPlan.buildPlan 26 C hC c ClampPlan.pad 1 2
    (fun r => ⟨ClampPlan.pad_lt r, ClampPlan.pad_ne r⟩) (by decide) (by decide) (by decide)
  have edge00 : incident (0 : Fin 13) 0 := Or.inl rfl
  have base_support : ∀ q i, markedBase q i = true → edgeInput 0 0 i = true := by decide
  have tangent_support (q : Fin 2) (i : ℕ) (hi : i < 26)
      (ht : d q i = true) : edgeInput 0 0 ⟨i, hi⟩ = true := by
    rw [hinit q i hi] at ht
    have et := of_decide_eq_true ht
    by_cases hq : q = 0
    · have ei : i = 13 := by simpa only [markedInitial, hq, ite_true] using et
      simp only [edgeInput, decide_eq_true_eq]
      right
      exact Fin.ext ei
    · have ei : i = 0 := by simpa only [markedInitial, hq, ite_false] using et
      simp only [edgeInput, decide_eq_true_eq]
      left
      exact Fin.ext ei
  have source_zero (q : Fin 2) :
      WireValue C (markedBase q) (26 + c) = false ∧ d q (26 + c) = false := by
    exact DerivativeSuper.super_value_false 26 C hC (markedBase q) (edgeInput 0 0)
      (d q) (base_support q) (tangent_support q) (hd q) (26 + c) (by omega)
      (hinactive 0 0 edge00)
  have input_zero (q : Fin 2) (i : ℕ) (hi : i = 1 ∨ i = 2) :
      WireValue C (markedBase q) i = false ∧ d q i = false := by
    have ilt : i < 26 := by rcases hi with rfl | rfl <;> decide
    rw [wire_value_input C (markedBase q) i ilt, hinit q i ilt]
    rcases hi with rfl | rfl <;> by_cases hq : q = 0 <;>
      simp [markedBase, markedInitial, hq]
  have pad_zero (q : Fin 2) (r : ℕ) :
      WireValue C (markedBase q) (ClampPlan.pad r) = false ∧
        d q (ClampPlan.pad r) = false := by
    apply input_zero
    by_cases hr : r = 1 <;> simp [ClampPlan.pad, hr]
  obtain ⟨D, hD, hsize, hsem, hder⟩ := realize_plan 26 C c ClampPlan.pad 1 2 P hC hc
    ClampPlan.pad_lt (by decide) (by decide)
    ⟨edgeInput 0 0, edge_positive C hF 0 0 edge00, hinactive 0 0 edge00⟩
    (by
      intro x hx
      obtain ⟨p, l, hpl, hp, hl⟩ := (hF x).1 hx
      exact ⟨edgeInput p l, edge_positive C hF p l hpl, edge_le x p l hp hl,
        hinactive p l hpl⟩)
    markedBase markedInitial d hinit hd hzero source_zero pad_zero
    (fun q => input_zero q 1 (Or.inl rfl)) (fun q => input_zero q 2 (Or.inr rfl))
  refine ⟨D, hD, hsize, ?_, hder⟩
  intro x
  rw [hsem x]
  exact hF x

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds Derivative ClampSemantic

def MarkedZero (C : Circuit) : Prop :=
  ∃ d : Fin 2 → ℕ → Bool,
    (∀ q i, i < 26 → d q i = markedInitial q i) ∧
    (∀ q, DerivativeRules 26 C (WireValue C (markedBase q)) (d q)) ∧
    ∀ q, d q C.output = false

def AllActive (C : Circuit) : Prop :=
  ∀ c < C.gates.length, ∃ p l : Fin 13, incident p l ∧
    WireValue C (edgeInput p l) (26 + c) = true

lemma minimum_all_active (C : Circuit) (hC : Proper 26 C)
    (hF : PlaneSpec C) (hZ : MarkedZero C) :
    ∃ D : Circuit, Proper 26 D ∧ PlaneSpec D ∧ MarkedZero D ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, Proper 26 E → PlaneSpec E → MarkedZero E → D.size ≤ E.size) ∧
      AllActive D := by
  classical
  let Q (k : ℕ) := ∃ D : Circuit,
    D.size = k ∧ Proper 26 D ∧ PlaneSpec D ∧ MarkedZero D
  have hex : ∃ k, Q k := ⟨C.size, C, rfl, hC, hF, hZ⟩
  obtain ⟨D, hsize, hD, hDF, hDZ⟩ := Nat.find_spec hex
  have hmin (E : Circuit) (hE : Proper 26 E) (hEF : PlaneSpec E)
      (hEZ : MarkedZero E) : D.size ≤ E.size := by
    rw [hsize]
    exact Nat.find_min' hex ⟨E, rfl, hE, hEF, hEZ⟩
  refine ⟨D, hD, hDF, hDZ, hmin C hC hF hZ, hmin, ?_⟩
  intro c hc
  by_contra no
  have inactive : ∀ p l : Fin 13, incident p l →
      WireValue D (edgeInput p l) (26 + c) = false := by
    intro p l hpl
    cases hv : WireValue D (edgeInput p l) (26 + c) with
    | false => rfl
    | true => exact (no ⟨p, l, hpl, hv⟩).elim
  obtain ⟨d, hinit, hd, hz⟩ := hDZ
  obtain ⟨E, hE, hsm, hEF, hder⟩ := inactive_gate_smaller D hD hDF c hc inactive d hinit hd hz
  let e (q : Fin 2) : ℕ → Bool := Classical.choose (hder q)
  have ep (q : Fin 2) :
      (∀ i < 26, e q i = markedInitial q i) ∧
      DerivativeRules 26 E (WireValue E (markedBase q)) (e q) ∧
      e q E.output = false := Classical.choose_spec (hder q)
  have hEZ : MarkedZero E :=
    ⟨e, fun q i hi => (ep q).1 i hi, fun q => (ep q).2.1, fun q => (ep q).2.2⟩
  have small := hmin E hE hEF hEZ
  omega

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.DerivativeWitness

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2602_aux.Derivative

def gateDerivative (v : ℕ → Bool) (ins : List Bool) (g : Gate) : Bool :=
  match g.op, g.inputs, ins with
  | .and, [a, b], [da, db] => v a && db || da && v b
  | .or, _, [da, db] => da || db
  | _, _, _ => false

def canonical (n : ℕ) (C : Circuit) (v seed : ℕ → Bool) (w : ℕ) : Bool :=
  (C.gates.foldl (fun R g =>
    R ++ [gateDerivative v (g.inputs.map fun i => R.getD i false) g])
    (List.ofFn fun i : Fin n => seed i.val)).getD w false

lemma canonical_input (n : ℕ) (C : Circuit) (v seed : ℕ → Bool)
    (i : ℕ) (hi : i < n) : canonical n C v seed i = seed i := by
  unfold canonical
  rw [foldl_snoc_init (gateDerivative v) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma canonical_rules (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v seed : ℕ → Bool) : DerivativeRules n C v (canonical n C v seed) := by
  intro j g a b hg hin
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hget : C.gates[j] = g := by simpa [List.getElem?_eq_getElem hj] using hg
  obtain ⟨_, c, d, hcd, _, hc, hd⟩ := hC j g hg
  have hab : a = c ∧ b = d := by simpa [hin] using hcd
  obtain ⟨rfl, rfl⟩ := hab
  have earlier : ∀ i ∈ C.gates[j].inputs,
      i < (List.ofFn fun k : Fin n => seed k.val).length + j := by
    intro i hi
    rw [hget, hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simpa using hc
    · simpa using hd
  have hrec := foldl_snoc_gate (gateDerivative v) false
    (List.ofFn fun i : Fin n => seed i.val) C.gates j hj earlier
  simp only [List.length_ofFn] at hrec
  change canonical n C v seed (n + j) = gateDerivative v
    (C.gates[j].inputs.map (canonical n C v seed)) C.gates[j] at hrec
  rw [hget, hin] at hrec
  constructor
  · intro hop
    simpa [gateDerivative, hop, hin] using hrec
  · intro hop
    simpa [gateDerivative, hop, hin] using hrec

lemma exists_derivative (n : ℕ) (C : Circuit) (hC : Proper n C)
    (v seed : ℕ → Bool) :
    ∃ d : ℕ → Bool, (∀ i < n, d i = seed i) ∧ DerivativeRules n C v d :=
  ⟨canonical n C v seed, canonical_input n C v seed, canonical_rules n C hC v seed⟩

end PEqualNP.Outside.L_meta_2602_aux.DerivativeWitness

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Derivative

lemma plan_gate_derivatives {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (V e : ℕ → Bool)
    (he : DerivativeRules n P.circuit V e) (j : ℕ) (hj : j < P.circuit.gates.length)
    (op : GateOp) (a b : ℕ) (hg : gateAt P.circuit j = ⟨op, [a, b]⟩) :
    (op = .and → e (n + j) = (V a && e b || e a && V b)) ∧
    (op = .or → e (n + j) = (e a || e b)) := by
  have get := gateAt_some hj
  rw [hg] at get
  exact he j _ a b get rfl

lemma plan_derivative_le {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C)
    (v V d e : ℕ → Bool)
    (hv : ValueRules n C v) (hV : ValueRules n P.circuit V)
    (hd : DerivativeRules n C v d) (he : DerivativeRules n P.circuit V e)
    (hinputV : ∀ i < n, V i = v i) (hinputD : ∀ i < n, e i = d i)
    (hpadV : ∀ q, V (pad q) = false) (hpadD : ∀ q, e (pad q) = false) :
    ∀ w < n + C.gates.length, repValue e (P.rep w) = true → d w = true := by
  have values := plan_value_relation P hC v V hv hV hinputV
  have vup (w : ℕ) (hw : w < n + C.gates.length) (q : ℕ)
      (hr : P.rep w = some q) : V q = true → v w = true := by
    simpa only [hr, repValue] using (values w hw).1
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ht
    by_cases low : w < n
    · rw [P.inputs w low] at ht
      simpa only [repValue, hinputD w low] using ht
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjD : j < P.circuit.gates.length := by rw [P.length_eq]; exact hj
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨op, a, b, hab, _, ha, hb⟩ := hC j g hg
    have habound : a < n + C.gates.length := by omega
    have hbbound : b < n + C.gates.length := by omega
    have ia := ih a ha habound
    have ib := ih b hb hbbound
    cases P.rule j g a b hg hab with
    | source _ hr _ | zero _ _ hr _ => simp [hr, repValue] at ht
    | orAlias q _ hor _ _ hn hr _ =>
      rw [hr] at ht
      change e q = true at ht
      rw [(hd j g a b hg hab).2 hor]
      rcases hn with ea | eb
      · have da := ia (by simpa only [ea, repValue] using ht)
        simp [da]
      · have db := ib (by simpa only [eb, repValue] using ht)
        simp [db]
    | binary u t _ ea eb _ hr hgate =>
      rw [hr] at ht
      change e (n + j) = true at ht
      rcases op with op | op
      · rw [(plan_gate_derivatives P V e he j hjD g.op u t hgate).1 op] at ht
        rw [(hd j g a b hg hab).1 op]
        rcases Bool.or_eq_true_iff.mp ht with ht | ht
        · obtain ⟨vu, et⟩ := Bool.and_eq_true_iff.mp ht
          have va := vup a habound u ea vu
          have db := ib (by simpa only [eb, repValue] using et)
          simp [va, db]
        · obtain ⟨eu, vt⟩ := Bool.and_eq_true_iff.mp ht
          have da := ia (by simpa only [ea, repValue] using eu)
          have vb := vup b hbbound t eb vt
          simp [da, vb]
      · rw [(plan_gate_derivatives P V e he j hjD g.op u t hgate).2 op] at ht
        rw [(hd j g a b hg hab).2 op]
        rcases Bool.or_eq_true_iff.mp ht with eu | et
        · have da := ia (by simpa only [ea, repValue] using eu)
          simp [da]
        · have db := ib (by simpa only [eb, repValue] using et)
          simp [db]
    | andAlias q u _ hand ea eb hu hne hr hgate =>
      have hurep : P.rep u = some q := by rcases hu with rfl | rfl <;> assumption
      have hubound : u < n + C.gates.length := by rcases hu with rfl | rfl <;> omega
      obtain ⟨k, hk, huk, hkpad, _⟩ := P.strictAlias u hubound q hurep hne
      have vu : V u = V q := by
        rw [huk, (plan_gate_values P V hV k hk .or q (pad q) hkpad).2 rfl, hpadV q]
        exact Bool.or_false _
      have eu : e u = e q := by
        rw [huk, (plan_gate_derivatives P V e he k hk .or q (pad q) hkpad).2 rfl, hpadD q]
        exact Bool.or_false _
      rw [hr] at ht
      change e (n + j) = true at ht
      rw [(plan_gate_derivatives P V e he j hjD .and q u hgate).1 rfl, vu, eu] at ht
      have pair : V q = true ∧ e q = true := by
        cases vq : V q <;> cases eq : e q <;> simp_all
      have va := vup a habound q ea pair.1
      have db := ib (by simpa only [eb, repValue] using pair.2)
      rw [(hd j g a b hg hab).1 hand]
      simp [va, db]

lemma plan_new_derivative_zero {n c z₀ z₁ : ℕ} {C : Circuit} {pad : ℕ → ℕ}
    (P : Plan n C c pad z₀ z₁) (hC : Proper n C)
    (base : Fin n → Bool) (initial d : ℕ → Bool)
    (hinit : ∀ i < n, d i = initial i)
    (hd : DerivativeRules n C (WireValue C base) d)
    (hpadLt : ∀ q, pad q < n)
    (hpadV : ∀ q, base ⟨pad q, hpadLt q⟩ = false)
    (hpadD : ∀ q, initial (pad q) = false)
    (out : ℕ) (ho : C.output < n + C.gates.length)
    (hout : P.rep C.output = some out) (hzero : d C.output = false) :
    ∃ e : ℕ → Bool, (∀ i < n, e i = initial i) ∧
      DerivativeRules n P.circuit (WireValue P.circuit base) e ∧ e out = false := by
  obtain ⟨e, hei, he⟩ := DerivativeWitness.exists_derivative n P.circuit P.proper
    (WireValue P.circuit base) initial
  refine ⟨e, hei, he, ?_⟩
  have le := plan_derivative_le P hC (WireValue C base) (WireValue P.circuit base) d e
    (wire_value_rules C hC base) (wire_value_rules P.circuit P.proper base) hd he
    (by intro i hi; rw [wire_value_input _ _ _ hi, wire_value_input _ _ _ hi])
    (fun i hi => (hei i hi).trans (hinit i hi).symm)
    (fun q => (wire_value_input _ _ _ (hpadLt q)).trans (hpadV q))
    (fun q => (hei _ (hpadLt q)).trans (hpadD q)) C.output ho
  cases hz : e out with
  | false => rfl
  | true =>
    have bad := le (by simpa only [hout, repValue] using hz)
    rw [hzero] at bad
    cases bad

end PEqualNP.Outside.L_meta_2602_aux.Clamp

namespace PEqualNP.Outside.L_meta_2602_aux.Clamp

open PEqualNP.CircuitLowerBounds Derivative ClampSemantic

def residualValue (C : Circuit) (c : ℕ) (x : Fin 26 → Bool) : Bool :=
  repValue (WireValue (ClampPlan.rewritten 26 C c ClampPlan.pad 1 2) x)
    (ClampPlan.represent 26 C (26 + c) C.output)

lemma residual_smaller (C : Circuit) (hC : Proper 26 C) (hF : PlaneSpec C)
    (c : ℕ) (hc : c < C.gates.length)
    (hkeep : ∀ p l : Fin 13, incident p l → residualValue C c (edgeInput p l) = true)
    (d : Fin 2 → ℕ → Bool)
    (hinit : ∀ q i, i < 26 → d q i = markedInitial q i)
    (hd : ∀ q, DerivativeRules 26 C (WireValue C (markedBase q)) (d q))
    (hzero : ∀ q, d q C.output = false) :
    ∃ D : Circuit, Proper 26 D ∧ D.size + 1 = C.size ∧ PlaneSpec D ∧ MarkedZero D := by
  let P := ClampPlan.buildPlan 26 C hC c ClampPlan.pad 1 2
    (fun r => ⟨ClampPlan.pad_lt r, ClampPlan.pad_ne r⟩) (by decide) (by decide) (by decide)
  have keep (p l : Fin 13) (hpl : incident p l) :
      repValue (WireValue P.circuit (edgeInput p l)) (P.rep C.output) = true := hkeep p l hpl
  have edge00 : incident (0 : Fin 13) 0 := Or.inl rfl
  have ho : C.output < 26 + C.gates.length := by
    simpa using output_lt_of_eval_true C (List.ofFn (edgeInput 0 0)) (edge_positive C hF 0 0 edge00)
  obtain ⟨out, hout⟩ : ∃ out, P.rep C.output = some out := by
    have k := keep 0 0 edge00
    cases hrep : P.rep C.output with
    | none => simp [hrep, repValue] at k
    | some out => exact ⟨out, rfl⟩
  have hne : out ≠ 26 + c := by
    intro h
    have fixed := P.fixed C.output ho out hout
    rw [h, P.source] at fixed
    contradiction
  let E : Circuit := ⟨P.circuit.gates, out⟩
  have hE : Proper 26 E := P.proper
  have hlen : E.gates.length = C.gates.length := P.length_eq
  have hEc : c < E.gates.length := by rw [hlen]; exact hc
  have hdead : ∀ g ∈ E.gates, 26 + c ∉ g.inputs := P.unread
  have hEF : PlaneSpec E := by
    apply plane_semantics_from_edges C E hF hE
    · intro x hy
      have up := (plan_wire_relation P hC x C.output ho).1
      rw [hout] at up
      exact up hy
    · intro p l hpl
      change WireValue P.circuit (edgeInput p l) out = true
      simpa only [hout, repValue] using keep p l hpl
  have newDerivatives (q : Fin 2) : ∃ e : ℕ → Bool,
      (∀ i < 26, e i = markedInitial q i) ∧
      DerivativeRules 26 E (WireValue E (markedBase q)) e ∧ e E.output = false := by
    apply plan_new_derivative_zero P hC (markedBase q) (markedInitial q) (d q)
      (hinit q) (hd q) ClampPlan.pad_lt
    · intro r
      by_cases hq : q = 0 <;> by_cases hr : r = 1 <;>
        simp [markedBase, ClampPlan.pad, hq, hr]
    · intro r
      by_cases hq : q = 0 <;> by_cases hr : r = 1 <;>
        simp [markedInitial, ClampPlan.pad, hq, hr]
    · exact ho
    · exact hout
    · exact hzero q
  let D := DeadGate.erase 26 E c
  have hD : Proper 26 D := DeadGate.erase_proper 26 E c hE hdead
  have hsize : D.size + 1 = C.size := by
    change (DeadGate.erase 26 E c).gates.length + 1 = C.gates.length
    rw [DeadGate.erase_length 26 E c hEc, hlen]
  have hDF : PlaneSpec D := by
    intro x
    rw [DeadGate.erase_eval 26 E c hE hEc hdead hne x]
    exact hEF x
  have witnesses (q : Fin 2) : ∃ e : ℕ → Bool,
      (∀ i < 26, e i = markedInitial q i) ∧
      DerivativeRules 26 D (WireValue D (markedBase q)) e ∧ e D.output = false := by
    obtain ⟨e, hei, her, hez⟩ := newDerivatives q
    exact DeadGate.erase_witness 26 E c hE hdead hne (markedBase q) (markedInitial q) e hei her hez
  let e (q : Fin 2) : ℕ → Bool := Classical.choose (witnesses q)
  have ep (q : Fin 2) := Classical.choose_spec (witnesses q)
  exact ⟨D, hD, hsize, hDF,
    e, fun q i hi => (ep q).1 i hi, fun q => (ep q).2.1, fun q => (ep q).2.2⟩

def AllEssential (C : Circuit) : Prop :=
  ∀ c < C.gates.length, ∃ p l : Fin 13, incident p l ∧
    residualValue C c (edgeInput p l) = false

lemma minimum_all_essential (C : Circuit) (hC : Proper 26 C)
    (hF : PlaneSpec C) (hZ : MarkedZero C) :
    ∃ D : Circuit, Proper 26 D ∧ PlaneSpec D ∧ MarkedZero D ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, Proper 26 E → PlaneSpec E → MarkedZero E → D.size ≤ E.size) ∧
      AllActive D ∧ AllEssential D := by
  classical
  obtain ⟨D, hD, hDF, hDZ, hsize, hmin, hactive⟩ := minimum_all_active C hC hF hZ
  refine ⟨D, hD, hDF, hDZ, hsize, hmin, hactive, ?_⟩
  intro c hc
  by_contra no
  have keep : ∀ p l : Fin 13, incident p l → residualValue D c (edgeInput p l) = true := by
    intro p l hpl
    cases hv : residualValue D c (edgeInput p l) with
    | false => exact (no ⟨p, l, hpl, hv⟩).elim
    | true => rfl
  obtain ⟨d, hinit, hd, hz⟩ := hDZ
  obtain ⟨E, hE, hsm, hEF, hEZ⟩ := residual_smaller D hD hDF c hc keep d hinit hd hz
  have small := hmin E hE hEF hEZ
  omega

end PEqualNP.Outside.L_meta_2602_aux.Clamp
