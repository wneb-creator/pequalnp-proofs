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

namespace PEqualNP.Outside.L_meta_2602_aux.GlobalRewire.Eval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- The wire evaluation and gate monotonicity lemmas are adapted from L_meta_1766.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma wire_relation {n : ℕ} {C : Circuit} {u : ℕ} {sigma : ℕ → ℕ} {x : Fin n → Bool}
    (R : Bool → Bool → Prop) (reflR : ∀ b, R b b)
    (transR : ∀ {a b c}, R a b → R b c → R a c) (mono : OpMono R)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + u)
    (reads : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      R (val C (List.ofFn x) (sigma r)) (val C (List.ofFn x) (n + u))) :
    ∀ i, R (val (PEqualNP.FactorSubst.substReads C n u sigma) (List.ofFn x) i)
      (val C (List.ofFn x) i) := by
  let D := PEqualNP.FactorSubst.substReads C n u sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  change ∀ i, R (val D z i) (val C z i)
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
      exact reflR _
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
      exact reflR _
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    let sub := fun j : ℕ => if j = n + u then sigma r else j
    have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
      rw [gateAt_eq hd, gateAt_eq hr]
      simp [D, PEqualNP.FactorSubst.substReads, sub]
    rw [hi, val_gate hz hd, val_gate hz hr, atD, List.map_map]
    apply mono _ (hC.1 _ (gateAt_mem hr))
    intro j hj
    have hjlt := hC.2.1 r hr j hj
    have hsig := hs r
    have hsub : sub j < n + r := by
      dsimp [sub]
      split <;> omega
    simp only [Function.comp_apply, ite_eq_left hsub, ite_eq_left hjlt]
    by_cases he : j = n + u
    · subst j
      simpa only [sub, ite_eq_left rfl] using transR (ih (sigma r) (by omega)) (reads r hr hj)
    · simpa [sub, he] using ih j (by omega)

end PEqualNP.Outside.L_meta_2602_aux.GlobalRewire.Eval

namespace PEqualNP.Outside.L_meta_2602_aux.GlobalRewire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Eval

def changeWire (n c : ℕ) (sigma : ℕ → ℕ) (j i : ℕ) : ℕ :=
  if i = n + c then sigma j else i

def ProposedValue (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (x : Fin n → Bool) (j : ℕ) : Bool :=
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
    val C (List.ofFn x) (changeWire n c sigma j i))

lemma wire_eq_on_false (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (x : Fin n → Bool)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      val C (List.ofFn x) (n + c) = true → val C (List.ofFn x) (sigma r) = true)
    (hfalse : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ProposedValue n C c sigma x r = false) :
    ∀ i, val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) i =
      val C (List.ofFn x) i := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    let sub := changeWire n c sigma r
    have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
      rw [gateAt_eq hd, gateAt_eq hr]
      simp [D, PEqualNP.FactorSubst.substReads, sub, changeWire]
    have small (j : ℕ) (hj : j ∈ (gateAt C r).inputs) : sub j < n + r := by
      have hlt := hC.2.1 r hr j hj
      have hsig := hs r
      dsimp [sub, changeWire]
      split <;> omega
    have left : val D z (n + r) = ProposedValue n C c sigma x r := by
      rw [val_gate hz hd, atD, List.map_map]
      unfold ProposedValue
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_apply, ite_eq_left (small j hj)]
      exact ih (sub j) (by rw [hi]; exact small j hj)
    have right : val C z (n + r) =
        (gateAt C r).op.eval ((gateAt C r).inputs.map (val C z)) := by
      rw [val_gate hz hr]
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      exact ite_eq_left (hC.2.1 r hr j hj)
    rw [hi, left, right]
    by_cases read : n + c ∈ (gateAt C r).inputs
    · rw [hfalse r hr read]
      have mono := opMono_imp (gateAt C r).op (hC.1 _ (gateAt_mem hr))
        (gateAt C r).inputs (val C z) (fun j => val C z (sub j))
        (by
          intro j hj
          by_cases eq : j = n + c
          · subst j
            simpa [sub, changeWire] using hgrow r hr read
          · simp [sub, changeWire, eq])
      cases old : (gateAt C r).op.eval ((gateAt C r).inputs.map (val C z)) with
      | false => rfl
      | true =>
        have bad := mono old
        change ProposedValue n C c sigma x r = true at bad
        rw [hfalse r hr read] at bad
        cases bad
    · unfold ProposedValue
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      have ne : j ≠ n + c := fun h => read (h ▸ hj)
      simp [changeWire, ne, z]

lemma rewire_computes (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (n + c) = true →
        val C (List.ofFn x) (sigma r) = true)
    (hclean : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, ProposedValue n C c sigma x r = true → F x = true) :
    ∀ x, (PEqualNP.FactorSubst.substReads C n c sigma).eval (List.ofFn x) = F x := by
  intro x
  cases hf : F x with
  | false =>
    have eq := wire_eq_on_false n C c sigma hC hs x
      (fun r hr mem => hgrow r hr mem x) (by
        intro r hr mem
        cases hp : ProposedValue n C c sigma x r with
        | false => rfl
        | true => have bad := hclean r hr mem x hp; rw [hf] at bad; cases bad)
      C.output
    exact eq.trans (hF x |>.trans hf)
  | true =>
    have mono := wire_relation (n := n) (C := C) (u := c) (sigma := sigma) (x := x)
      (fun a b => b = true → a = true) (fun _ h => h)
      (fun h₁ h₂ v => h₁ (h₂ v))
      (fun op hop l f g h => opMono_imp op hop l g f h) hC hs
      (fun r hr mem => hgrow r hr mem x)
    exact mono C.output (hF x |>.trans hf)

def Proper (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

def DerivativeRules (n : ℕ) (C : Circuit) (v d : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (n + j) = (v a && d b || d a && v b)) ∧
    (g.op = .or → d (n + j) = (d a || d b))

lemma rewire_proper (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hs : ∀ r, sigma r < n + c)
    (hne : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      changeWire n c sigma j a ≠ changeWire n c sigma j b) :
    Proper n (PEqualNP.FactorSubst.substReads C n c sigma) := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  intro j gg hgg
  have hjD : j < D.gates.length := List.getElem?_eq_some_iff.mp hgg |>.1
  have hj : j < C.gates.length := by omega
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  let sub := changeWire n c sigma j
  have hmap : D.gates[j]? = some ⟨g.op, g.inputs.map sub⟩ := by
    rw [List.getElem?_eq_getElem hjD]
    simp [D, PEqualNP.FactorSubst.substReads, g, sub, changeWire]
  have eg : gg = ⟨g.op, g.inputs.map sub⟩ := Option.some.inj (hgg.symm.trans hmap)
  subst gg
  obtain ⟨hop, a, b, hab, _, ha, hb⟩ := hC j g hg
  refine ⟨hop, sub a, sub b, by simp [hab], hne j g a b hg hab, ?_, ?_⟩
  · have hsig := hs j
    dsimp [sub, changeWire]
    split <;> omega
  · have hsig := hs j
    dsimp [sub, changeWire]
    split <;> omega

lemma rewire_dead (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hs : ∀ r, sigma r < n + c) :
    ∀ g ∈ (PEqualNP.FactorSubst.substReads C n c sigma).gates, n + c ∉ g.inputs := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  simp only [PEqualNP.FactorSubst.substReads, List.getElem_mapIdx]
  intro mem
  obtain ⟨i, _, heq⟩ := List.mem_map.mp mem
  split at heq
  · have hsig := hs j
    omega
  · contradiction

lemma rewire_derivative (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hA : PEqualNP.TopForm.IsAO2 n C)
    (hs : ∀ r, sigma r < n + c) (x : Fin n → Bool) (d : ℕ → Bool)
    (hd : DerivativeRules n C (val C (List.ofFn x)) d)
    (hval : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs →
      val C (List.ofFn x) (sigma j) = val C (List.ofFn x) (n + c))
    (hder : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs → d (sigma j) = d (n + c)) :
    DerivativeRules n (PEqualNP.FactorSubst.substReads C n c sigma)
      (val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x)) d := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  have veq : ∀ i, val D (List.ofFn x) i = val C (List.ofFn x) i := by
    apply wire_relation Eq (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂) opMono_eq hA hs
    intro j hj mem
    exact hval j (gateAt C j) (by rw [gateAt_eq hj]; exact List.getElem?_eq_getElem hj) mem
  intro j gg aa bb hgg hin
  have hjD : j < D.gates.length := List.getElem?_eq_some_iff.mp hgg |>.1
  have hj : j < C.gates.length := by omega
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
  let sub := changeWire n c sigma j
  have hmap : D.gates[j]? = some ⟨g.op, g.inputs.map sub⟩ := by
    rw [List.getElem?_eq_getElem hjD]
    simp [D, PEqualNP.FactorSubst.substReads, g, sub, changeWire]
  have eg : gg = ⟨g.op, g.inputs.map sub⟩ := Option.some.inj (hgg.symm.trans hmap)
  obtain ⟨_, a, b, hab, _, _, _⟩ := hC j g hg
  have ins : gg.inputs = [sub a, sub b] := by simp [eg, hab]
  rw [ins] at hin
  have ea : aa = sub a := (List.cons.inj hin).1.symm
  have eb : bb = sub b := (List.cons.inj (List.cons.inj hin).2).1.symm
  subst aa
  subst bb
  have sv (k : ℕ) (hk : k ∈ g.inputs) :
      val D (List.ofFn x) (sub k) = val C (List.ofFn x) k := by
    rw [veq]
    by_cases eq : k = n + c
    · subst k
      simpa [sub, changeWire] using hval j g hg hk
    · simp [sub, changeWire, eq]
  have sd (k : ℕ) (hk : k ∈ g.inputs) : d (sub k) = d k := by
    by_cases eq : k = n + c
    · subst k
      simpa [sub, changeWire] using hder j g hg hk
    · simp [sub, changeWire, eq]
  rw [sv a (by simp [hab]), sv b (by simp [hab]), sd a (by simp [hab]), sd b (by simp [hab])]
  have old := hd j g a b hg hab
  simpa only [eg] using old

lemma and_value (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + c) = (val C (List.ofFn x) a && val C (List.ofFn x) b) := by
  have ha := hC.2.1 c hc a (by simp [hin])
  have hb := hC.2.1 c hc b (by simp [hin])
  rw [val_gate (by simp) hc, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma factor_grows (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b s : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (hs : s = a ∨ s = b) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + c) = true → val C (List.ofFn x) s = true := by
  rw [and_value n C hC c a b hc hop hin x]
  intro h
  rcases hs with rfl | rfl
  · exact (Bool.and_eq_true_iff.mp h).1
  · exact (Bool.and_eq_true_iff.mp h).2

lemma zero_factor_equal (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (c a b s : ℕ) (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b]) (hs : s = a ∨ s = b) (x : Fin n → Bool)
    (d : ℕ → Bool) (hd : DerivativeRules n C (val C (List.ofFn x)) d)
    (hv : val C (List.ofFn x) s = false) (hds : d s = false) :
    val C (List.ofFn x) s = val C (List.ofFn x) (n + c) ∧ d s = d (n + c) := by
  have hg : C.gates[c]? = some (gateAt C c) := by
    rw [gateAt_eq hc]
    exact List.getElem?_eq_getElem hc
  rw [and_value n C hC c a b hc hop hin x, (hd c _ a b hg hin).1 hop]
  rcases hs with rfl | rfl <;> simp [hv, hds]

end PEqualNP.Outside.L_meta_2602_aux.GlobalRewire

namespace PEqualNP.Outside.L_meta_2602_aux.CombinedElimination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma eliminate_factor (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hC : Derivative.Proper n C) (hA : PEqualNP.TopForm.IsAO2 n C)
    (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b])
    (hs : ∀ r, sigma r = a ∨ sigma r = b)
    (hne : ∀ j g a0 b0, C.gates[j]? = some g → g.inputs = [a0, b0] →
      GlobalRewire.changeWire n c sigma j a0 ≠ GlobalRewire.changeWire n c sigma j b0)
    (hout : C.output ≠ n + c) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hclean : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, GlobalRewire.ProposedValue n C c sigma x r = true → F x = true)
    (base : Fin 2 → Fin n → Bool) (initial d : Fin 2 → ℕ → Bool)
    (hinit : ∀ q i, i < n → d q i = initial q i)
    (hd : ∀ q, Derivative.DerivativeRules n C (Derivative.WireValue C (base q)) (d q))
    (hzero : ∀ q, d q C.output = false)
    (hkept : ∀ r g, C.gates[r]? = some g → n + c ∈ g.inputs →
      ∀ q, Derivative.WireValue C (base q) (sigma r) = false ∧ d q (sigma r) = false) :
    ∃ D : Circuit, Derivative.Proper n D ∧ D.size + 1 = C.size ∧
      (∀ x, D.eval (List.ofFn x) = F x) ∧
      ∀ q : Fin 2, ∃ e : ℕ → Bool, (∀ i < n, e i = initial q i) ∧
        Derivative.DerivativeRules n D (Derivative.WireValue D (base q)) e ∧
        e D.output = false := by
  have ha := hA.2.1 c hc a (by simp [hin])
  have hb := hA.2.1 c hc b (by simp [hin])
  have hsig : ∀ r, sigma r < n + c := by
    intro r
    rcases hs r with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb
  let E := PEqualNP.FactorSubst.substReads C n c sigma
  have hE : Derivative.Proper n E := GlobalRewire.rewire_proper n C c sigma hC hsig hne
  have hdead : ∀ g ∈ E.gates, n + c ∉ g.inputs := GlobalRewire.rewire_dead n C c sigma hsig
  have hEc : c < E.gates.length := by simpa [E, PEqualNP.FactorSubst.substReads] using hc
  have hEout : E.output ≠ n + c := hout
  have eqv (q : Fin 2) (r : ℕ) (g : Gate) (hr : C.gates[r]? = some g)
      (mem : n + c ∈ g.inputs) :
      GlobalRewire.Eval.val C (List.ofFn (base q)) (sigma r) =
        GlobalRewire.Eval.val C (List.ofFn (base q)) (n + c) ∧
        d q (sigma r) = d q (n + c) := by
    exact GlobalRewire.zero_factor_equal n C hA c a b (sigma r) hc hop hin (hs r)
      (base q) (d q) (hd q) (hkept r g hr mem q).1 (hkept r g hr mem q).2
  have hEd (q : Fin 2) :
      Derivative.DerivativeRules n E (Derivative.WireValue E (base q)) (d q) :=
    GlobalRewire.rewire_derivative n C c sigma hC hA hsig (base q) (d q) (hd q)
      (fun r g hr mem => (eqv q r g hr mem).1) (fun r g hr mem => (eqv q r g hr mem).2)
  have hEF : ∀ x, E.eval (List.ofFn x) = F x := by
    apply GlobalRewire.rewire_computes n C c sigma hA hsig F hF
    · intro r _ _ x
      exact GlobalRewire.factor_grows n C hA c a b (sigma r) hc hop hin (hs r) x
    · exact hclean
  refine ⟨DeadGate.erase n E c, DeadGate.erase_proper n E c hE hdead, ?_, ?_, ?_⟩
  · change (DeadGate.erase n E c).gates.length + 1 = C.gates.length
    rw [DeadGate.erase_length n E c hEc]
    simp [E, PEqualNP.FactorSubst.substReads]
  · intro x
    exact (DeadGate.erase_eval n E c hE hEc hdead hEout x).trans (hEF x)
  · intro q
    exact DeadGate.erase_witness n E c hE hdead hEout (base q) (initial q) (d q)
      (hinit q) (hEd q) (hzero q)

end PEqualNP.Outside.L_meta_2602_aux.CombinedElimination

namespace PEqualNP.Outside.L_meta_2602_aux.GlobalRewire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Eval

def OrAffected (n : ℕ) (C : Circuit) (c w : ℕ) : Prop :=
  Relation.ReflTransGen (fun u v : ℕ => ∃ j < C.gates.length,
    v = n + j ∧ (gateAt C j).op = .or ∧ u ∈ (gateAt C j).inputs) (n + c) w

lemma affected_source (n : ℕ) (C : Circuit) (c : ℕ) :
    OrAffected n C c (n + c) := Relation.ReflTransGen.refl

lemma affected_or (n : ℕ) (C : Circuit) (c j u : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .or)
    (hu : u ∈ (gateAt C j).inputs) (h : OrAffected n C c u) :
    OrAffected n C c (n + j) :=
  Relation.ReflTransGen.tail h ⟨j, hj, rfl, hop, hu⟩

lemma affected_value (n : ℕ) (C : Circuit) (c : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    (hc : val C (List.ofFn x) (n + c) = true) :
    ∀ w, OrAffected n C c w → val C (List.ofFn x) w = true := by
  intro w h
  induction h with
  | refl => exact hc
  | tail _ step ih =>
    obtain ⟨j, hj, rfl, hop, hu⟩ := step
    rw [val_gate (by simp) hj, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨_, hu, by rw [ite_eq_left (hC.2.1 j hj _ hu)]; exact ih⟩

lemma dirty_output_outside (n : ℕ) (C : Circuit) (c : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hdirty : ∃ x, val C (List.ofFn x) (n + c) = true ∧ F x = false) :
    ¬ OrAffected n C c C.output := by
  intro h
  obtain ⟨x, hc, hf⟩ := hdirty
  have bad := affected_value n C c hC x hc C.output h
  change C.eval (List.ofFn x) = true at bad
  rw [hF x, hf] at bad
  cases bad

lemma outside_eq_on_false (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (x : Fin n → Bool)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      val C (List.ofFn x) (n + c) = true → val C (List.ofFn x) (sigma r) = true)
    (hfront : ∀ r < C.gates.length, (gateAt C r).op = .and →
      (∃ u ∈ (gateAt C r).inputs, OrAffected n C c u) →
      val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) (n + r) = false) :
    ∀ i, ¬ OrAffected n C c i →
      val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) i =
        val C (List.ofFn x) i := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  let z := List.ofFn x
  have hz : z.length = n := by simp [z]
  have len : D.gates.length = C.gates.length := by simp [D, PEqualNP.FactorSubst.substReads]
  have mono := wire_relation (n := n) (C := C) (u := c) (sigma := sigma) (x := x)
    (fun a b => b = true → a = true) (fun _ h => h)
    (fun h₁ h₂ v => h₁ (h₂ v))
    (fun op hop l f g h => opMono_imp op hop l g f h) hC hs hgrow
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro houtside
    by_cases hin : i < n
    · rw [val_input hz hin, val_input hz hin]
    by_cases hout : n + C.gates.length ≤ i
    · rw [val_ge hz (show n + D.gates.length ≤ i by omega), val_ge hz hout]
    let r := i - n
    have hi : i = n + r := by dsimp [r]; omega
    have hr : r < C.gates.length := by omega
    have hd : r < D.gates.length := by omega
    by_cases hit : ∃ u ∈ (gateAt C r).inputs, OrAffected n C c u
    · have hop : (gateAt C r).op = .and := by
        rcases hC.1 _ (gateAt_mem hr) with h | h
        · exact h
        · obtain ⟨u, hu, hcone⟩ := hit
          exact (houtside (hi.symm ▸ affected_or n C c r u hr h hu hcone)).elim
      have df := hfront r hr hop hit
      have cf : val C z (n + r) = false := by
        cases old : val C z (n + r) with
        | false => rfl
        | true =>
          have bad := mono (n + r) old
          rw [df] at bad
          cases bad
      rw [hi]
      exact df.trans cf.symm
    · have outside (j : ℕ) (hj : j ∈ (gateAt C r).inputs) :
          ¬ OrAffected n C c j := fun h => hit ⟨j, hj, h⟩
      have unchanged (j : ℕ) (hj : j ∈ (gateAt C r).inputs) :
          changeWire n c sigma r j = j := by
        have ne : j ≠ n + c := fun he => outside j hj (he.symm ▸ affected_source n C c)
        simp [changeWire, ne]
      let sub := changeWire n c sigma r
      have atD : gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map sub⟩ := by
        rw [gateAt_eq hd, gateAt_eq hr]
        simp [D, PEqualNP.FactorSubst.substReads, sub, changeWire]
      rw [hi, val_gate hz hd, val_gate hz hr, atD, List.map_map]
      apply congrArg (gateAt C r).op.eval
      apply List.map_congr_left
      intro j hj
      have hlt := hC.2.1 r hr j hj
      change (if sub j < n + r then val D z (sub j) else false) =
        (if j < n + r then val C z j else false)
      rw [show sub j = j from unchanged j hj]
      simp only [ite_eq_left hlt]
      exact ih j (by omega) (outside j hj)

lemma frontier_rewire_computes (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hs : ∀ r, sigma r < n + c)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hdirty : ∃ x, val C (List.ofFn x) (n + c) = true ∧ F x = false)
    (hgrow : ∀ r < C.gates.length, n + c ∈ (gateAt C r).inputs →
      ∀ x : Fin n → Bool, val C (List.ofFn x) (n + c) = true →
        val C (List.ofFn x) (sigma r) = true)
    (hclean : ∀ r < C.gates.length, (gateAt C r).op = .and →
      (∃ u ∈ (gateAt C r).inputs, OrAffected n C c u) →
      ∀ x : Fin n → Bool,
        val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) (n + r) = true →
        F x = true) :
    ∀ x, (PEqualNP.FactorSubst.substReads C n c sigma).eval (List.ofFn x) = F x := by
  intro x
  cases hf : F x with
  | false =>
    have eq := outside_eq_on_false n C c sigma hC hs x
      (fun r hr mem => hgrow r hr mem x) (by
        intro r hr hop hit
        cases hp : val (PEqualNP.FactorSubst.substReads C n c sigma) (List.ofFn x) (n + r) with
        | false => rfl
        | true => have bad := hclean r hr hop hit x hp; rw [hf] at bad; cases bad)
      C.output (dirty_output_outside n C c hC F hF hdirty)
    exact eq.trans (hF x |>.trans hf)
  | true =>
    have mono := wire_relation (n := n) (C := C) (u := c) (sigma := sigma) (x := x)
      (fun a b => b = true → a = true) (fun _ h => h)
      (fun h₁ h₂ v => h₁ (h₂ v))
      (fun op hop l f g h => opMono_imp op hop l g f h) hC hs
      (fun r hr mem => hgrow r hr mem x)
    exact mono C.output (hF x |>.trans hf)

end PEqualNP.Outside.L_meta_2602_aux.GlobalRewire

namespace PEqualNP.Outside.L_meta_2602_aux.CombinedElimination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma eliminate_factor_frontier (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hC : Derivative.Proper n C) (hA : PEqualNP.TopForm.IsAO2 n C)
    (hc : c < C.gates.length) (hop : (gateAt C c).op = .and)
    (hin : (gateAt C c).inputs = [a, b])
    (hs : ∀ r, sigma r = a ∨ sigma r = b)
    (hne : ∀ j g a0 b0, C.gates[j]? = some g → g.inputs = [a0, b0] →
      GlobalRewire.changeWire n c sigma j a0 ≠ GlobalRewire.changeWire n c sigma j b0)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ x, C.eval (List.ofFn x) = F x)
    (hdirty : ∃ x, GlobalRewire.Eval.val C (List.ofFn x) (n + c) = true ∧ F x = false)
    (hclean : ∀ r < C.gates.length, (gateAt C r).op = .and →
      (∃ u ∈ (gateAt C r).inputs, GlobalRewire.OrAffected n C c u) →
      ∀ x : Fin n → Bool,
        GlobalRewire.Eval.val (PEqualNP.FactorSubst.substReads C n c sigma)
          (List.ofFn x) (n + r) = true → F x = true)
    (base : Fin 2 → Fin n → Bool) (initial d : Fin 2 → ℕ → Bool)
    (hinit : ∀ q i, i < n → d q i = initial q i)
    (hd : ∀ q, Derivative.DerivativeRules n C (Derivative.WireValue C (base q)) (d q))
    (hzero : ∀ q, d q C.output = false)
    (hkept : ∀ r g, C.gates[r]? = some g → n + c ∈ g.inputs →
      ∀ q, Derivative.WireValue C (base q) (sigma r) = false ∧ d q (sigma r) = false) :
    ∃ D : Circuit, Derivative.Proper n D ∧ D.size + 1 = C.size ∧
      (∀ x, D.eval (List.ofFn x) = F x) ∧
      ∀ q : Fin 2, ∃ e : ℕ → Bool, (∀ i < n, e i = initial q i) ∧
        Derivative.DerivativeRules n D (Derivative.WireValue D (base q)) e ∧
        e D.output = false := by
  have ha := hA.2.1 c hc a (by simp [hin])
  have hb := hA.2.1 c hc b (by simp [hin])
  have hsig : ∀ r, sigma r < n + c := by
    intro r
    rcases hs r with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb
  let E := PEqualNP.FactorSubst.substReads C n c sigma
  have hE : Derivative.Proper n E := GlobalRewire.rewire_proper n C c sigma hC hsig hne
  have hdead : ∀ g ∈ E.gates, n + c ∉ g.inputs := GlobalRewire.rewire_dead n C c sigma hsig
  have hEc : c < E.gates.length := by simpa [E, PEqualNP.FactorSubst.substReads] using hc
  have hEout : E.output ≠ n + c := by
    intro he
    change C.output = n + c at he
    exact GlobalRewire.dirty_output_outside n C c hA F hF hdirty
      (he.symm ▸ GlobalRewire.affected_source n C c)
  have eqv (q : Fin 2) (r : ℕ) (g : Gate) (hr : C.gates[r]? = some g)
      (mem : n + c ∈ g.inputs) :
      GlobalRewire.Eval.val C (List.ofFn (base q)) (sigma r) =
        GlobalRewire.Eval.val C (List.ofFn (base q)) (n + c) ∧
        d q (sigma r) = d q (n + c) := by
    exact GlobalRewire.zero_factor_equal n C hA c a b (sigma r) hc hop hin (hs r)
      (base q) (d q) (hd q) (hkept r g hr mem q).1 (hkept r g hr mem q).2
  have hEd (q : Fin 2) :
      Derivative.DerivativeRules n E (Derivative.WireValue E (base q)) (d q) :=
    GlobalRewire.rewire_derivative n C c sigma hC hA hsig (base q) (d q) (hd q)
      (fun r g hr mem => (eqv q r g hr mem).1) (fun r g hr mem => (eqv q r g hr mem).2)
  have hEF : ∀ x, E.eval (List.ofFn x) = F x := by
    apply GlobalRewire.frontier_rewire_computes n C c sigma hA hsig F hF hdirty
    · intro r _ _ x
      exact GlobalRewire.factor_grows n C hA c a b (sigma r) hc hop hin (hs r) x
    · exact hclean
  refine ⟨DeadGate.erase n E c, DeadGate.erase_proper n E c hE hdead, ?_, ?_, ?_⟩
  · change (DeadGate.erase n E c).gates.length + 1 = C.gates.length
    rw [DeadGate.erase_length n E c hEc]
    simp [E, PEqualNP.FactorSubst.substReads]
  · intro x
    exact (DeadGate.erase_eval n E c hE hEc hdead hEout x).trans (hEF x)
  · intro q
    exact DeadGate.erase_witness n E c hE hdead hEout (base q) (initial q) (d q)
      (hinit q) (hEd q) (hzero q)

end PEqualNP.Outside.L_meta_2602_aux.CombinedElimination
