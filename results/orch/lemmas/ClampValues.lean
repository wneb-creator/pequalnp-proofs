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
