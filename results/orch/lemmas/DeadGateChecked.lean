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

end PEqualNP.Outside.L_meta_2602_aux.DeadGate
