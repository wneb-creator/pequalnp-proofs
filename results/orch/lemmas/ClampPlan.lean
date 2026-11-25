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
