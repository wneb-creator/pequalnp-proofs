import PEqualNP.Defs
import Mathlib.Tactic.Tauto

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

namespace PEqualNP.Outside.L_meta_2602


namespace Flat

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma gateAt_some {C : Circuit} {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) :
    gateAt C k = g := by
  simp [gateAt, List.getD_eq_getElem?_getD, h]

lemma no_pair (C : Circuit) (h : PEqualNP.TopForm.andPairs 26 C = 0) (i j : ℕ)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hc : InCone 26 C i j) : False := by
  have hlt := inCone_lt 26 C i j hc
  unfold PEqualNP.TopForm.andPairs at h
  rw [Finset.card_eq_zero] at h
  have hm := Finset.eq_empty_iff_forall_notMem.mp h (i, j)
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
  exact hm ⟨⟨by omega, by omega⟩, hi, hj, hc⟩

def NoAnd (C : Circuit) (k : ℕ) : Prop :=
  (gateAt C k).op ≠ GateOp.and ∧ ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and

def AF (C : Circuit) (w : ℕ) : Prop := ∀ k, w = 26 + k → NoAnd C k

lemma af_opnd (C : Circuit) (k a : ℕ) (hk : k < C.gates.length)
    (ha : a ∈ (gateAt C k).inputs) (halt : a < 26 + k)
    (hno : ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and) : AF C a := by
  intro i hi
  subst hi
  have hc : InCone 26 C i k := (inCone_iff 26 C i k).2 ⟨hk, i, by omega, ha, Or.inl rfl⟩
  exact ⟨hno i hc, fun i2 hc2 => hno i2 (inCone_trans 26 C i2 i hc2 k hc)⟩

def xP (p : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p)
def xL (l : Fin 13) : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l)
def xPL (p l : Fin 13) : Fin 26 → Bool :=
  fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

lemma base (p l : Fin 13) (f : ℕ → Bool) (C : Circuit)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (w : ℕ) (hw : w < 26) :
    (wv 26 C (xPL p l) w = true → wv 26 C (xP p) w = true ∨ f w = true) ∧
    (f w = true → wv 26 C (xL l) w = true) := by
  rw [wv_input _ _ _ _ hw, wv_input _ _ _ _ hw, wv_input _ _ _ _ hw]
  simp only [xPL, xP, xL, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have hp := p.isLt
  have hl := l.isLt
  rcases Nat.lt_or_ge w 13 with h | h
  · have h5 : f w = false := (H5 ⟨w, h⟩).1
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · omega
    · intro h1
      rw [h5] at h1
      exact absurd h1 (by simp)
  · have h5 := (H5 ⟨w - 13, by omega⟩).2
    have e : 13 + (w - 13) = w := by omega
    simp only [e, Fin.ext_iff] at h5
    constructor
    · rintro (h1 | h1)
      · omega
      · right
        rw [h5]
        simp only [decide_eq_true_eq]
        omega
    · intro h1
      rw [h5] at h1
      simp only [decide_eq_true_eq] at h1
      omega

lemma gate_val (C : Circuit) (hC : AOB 26 C) (x : Fin 26 → Bool) (k : ℕ) (g : Gate)
    (hg : C.gates[k]? = some g) (a b : ℕ) (hin : g.inputs = [a, b]) :
    (g.op = GateOp.and → wv 26 C x (26 + k) = (wv 26 C x a && wv 26 C x b)) ∧
    (g.op = GateOp.or → wv 26 C x (26 + k) = (wv 26 C x a || wv 26 C x b)) := by
  have hk : k < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hg
    exact absurd hg (by simp)
  have h := wv_rec 26 C x hC k hk
  rw [gateAt_some hg, hin] at h
  constructor
  · intro hop
    rw [h, hop]
    simp [GateOp.eval]
  · intro hop
    rw [h, hop]
    simp [GateOp.eval]

lemma and_case (va vb pa pb fa fb la lb : Bool)
    (qa : (va = true → pa = true ∨ fa = true) ∧ (fa = true → la = true))
    (qb : (vb = true → pb = true ∨ fb = true) ∧ (fb = true → lb = true)) :
    (va && vb) = true →
      (pa && pb) = true ∨ (pa && fb || fa && pb) = true ∨ (la && lb) = true := by
  intro h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rcases qa.1 h1 with x | x <;> rcases qb.1 h2 with y | y
  · left; simp [x, y]
  · right; left; simp [x, y]
  · right; left; simp [x, y]
  · right; right; simp [qa.2 x, qb.2 y]

lemma or_case1 (va vb pa pb fa fb la lb : Bool)
    (qa : (va = true → pa = true ∨ fa = true) ∧ (fa = true → la = true))
    (qb : (vb = true → pb = true ∨ fb = true) ∧ (fb = true → lb = true)) :
    ((va || vb) = true → (pa || pb) = true ∨ (fa || fb) = true) ∧
      ((fa || fb) = true → (la || lb) = true) := by
  constructor
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rcases qa.1 h with x | x
      · left; simp [x]
      · right; simp [x]
    · rcases qb.1 h with x | x
      · left; simp [x]
      · right; simp [x]
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simp [qa.2 h]
    · simp [qb.2 h]

lemma or_case2 (va vb pa pb fa fb la lb : Bool)
    (qa : va = true → pa = true ∨ fa = true ∨ la = true)
    (qb : vb = true → pb = true ∨ fb = true ∨ lb = true) :
    (va || vb) = true →
      (pa || pb) = true ∨ (fa || fb) = true ∨ (la || lb) = true := by
  intro h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rcases qa h with x | x | x
    · left; simp [x]
    · right; left; simp [x]
    · right; right; simp [x]
  · rcases qb h with x | x | x
    · left; simp [x]
    · right; left; simp [x]
    · right; right; simp [x]

lemma main (C : Circuit) (p l : Fin 13) (f : ℕ → Bool)
    (H1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k)
    (H3 : PEqualNP.TopForm.andPairs 26 C = 0)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (H6 : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → f (26 + k) =
        (wv 26 C (xP p) a && f b || f a && wv 26 C (xP p) b)) ∧
      (g.op = GateOp.or → f (26 + k) = (f a || f b))) :
    ∀ w, w < 26 + C.gates.length →
      (AF C w → (wv 26 C (xPL p l) w = true → wv 26 C (xP p) w = true ∨ f w = true) ∧
        (f w = true → wv 26 C (xL l) w = true)) ∧
      (wv 26 C (xPL p l) w = true →
        wv 26 C (xP p) w = true ∨ f w = true ∨ wv 26 C (xL l) w = true) := by
  have hC : AOB 26 C := by
    intro j hj
    have hg : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
    obtain ⟨hop, a, b, hin, _, ha, hb⟩ := H1 j _ hg
    rw [gateAt_some hg]
    refine ⟨hop, ?_⟩
    intro i hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · omega
    · omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases Nat.lt_or_ge w 26 with h | h
    · have hb := base p l f C H5 w h
      exact ⟨fun _ => hb, fun hv => by
        rcases hb.1 hv with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < C.gates.length := by omega
      have hg : C.gates[k]? = some (C.gates[k]) := List.getElem?_eq_getElem hk
      obtain ⟨hop, a, b, hin, _, ha, hb⟩ := H1 k _ hg
      have hgk := gateAt_some hg
      have hain : a ∈ (gateAt C k).inputs := by rw [hgk, hin]; simp
      have hbin : b ∈ (gateAt C k).inputs := by rw [hgk, hin]; simp
      have iha := ih a ha (by omega)
      have ihb := ih b hb (by omega)
      have e1 := gate_val C hC (xPL p l) k _ hg a b hin
      have e2 := gate_val C hC (xP p) k _ hg a b hin
      have e3 := gate_val C hC (xL l) k _ hg a b hin
      have e4 := H6 k _ a b hg hin
      rcases hop with hop | hop
      · have hno : ∀ i, InCone 26 C i k → (gateAt C i).op ≠ GateOp.and := by
          intro i hc hi
          exact no_pair C H3 i k hi (by rw [hgk]; exact hop) hc
        have qa := iha.1 (af_opnd C k a hk hain ha hno)
        have qb := ihb.1 (af_opnd C k b hk hbin hb hno)
        rw [e1.1 hop, e2.1 hop, e3.1 hop, e4.1 hop]
        constructor
        · intro haf
          exact absurd (by rw [hgk]; exact hop) (haf k rfl).1
        · exact and_case _ _ _ _ _ _ _ _ qa qb
      · rw [e1.2 hop, e2.2 hop, e3.2 hop, e4.2 hop]
        constructor
        · intro haf
          have hno := (haf k rfl).2
          have qa := iha.1 (af_opnd C k a hk hain ha hno)
          have qb := ihb.1 (af_opnd C k b hk hbin hb hno)
          exact or_case1 _ _ _ _ _ _ _ _ qa qb
        · exact or_case2 _ _ _ _ _ _ _ _ iha.2 ihb.2

lemma core (S : Finset (Fin 13)) (C : Circuit) (p l : Fin 13) (f : ℕ → Bool)
    (H1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k)
    (H2 : ∀ (x : Fin 26 → Bool), C.eval (List.ofFn x) = true ↔
      ∃ (u : Fin 13) (v : Fin 13), u - v ∈ S ∧ x (Fin.castAdd 13 u) = true ∧
        x (Fin.natAdd 13 v) = true)
    (H3 : PEqualNP.TopForm.andPairs 26 C = 0)
    (H4 : p - l ∈ S)
    (H5 : ∀ x10 : Fin 13, f ↑x10 = false ∧ f (13 + ↑x10) = decide (x10 = l))
    (H6 : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → f (26 + k) =
        (wv 26 C (xP p) a && f b || f a && wv 26 C (xP p) b)) ∧
      (g.op = GateOp.or → f (26 + k) = (f a || f b))) :
    f C.output = true := by
  have hV : wv 26 C (xPL p l) C.output = true := by
    have := (H2 (xPL p l)).2 ⟨p, l, H4, by simp [xPL], by simp [xPL]⟩
    exact this
  have hV0 : ¬ wv 26 C (xP p) C.output = true := by
    intro h
    obtain ⟨u, v, _, _, hv⟩ := (H2 (xP p)).1 h
    simp only [xP, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hv
    have := p.isLt
    omega
  have hVL : ¬ wv 26 C (xL l) C.output = true := by
    intro h
    obtain ⟨u, v, _, hu, _⟩ := (H2 (xL l)).1 h
    simp only [xL, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hu
    have := u.isLt
    omega
  have hout := out_lt 26 C (xPL p l) hV
  rcases (main C p l f H1 H3 H5 H6 C.output hout).2 hV with h | h | h
  · exact absurd h hV0
  · exact h
  · exact absurd h hVL

end Flat

lemma flat_positive : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (13 : ℕ)) (x5 : ℕ → Bool),   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 ≠ x10 ∧ x9 < (26 : ℕ) + x6 ∧ x10 < (26 : ℕ) + x6) →     (∀ (x7 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →       PEqualNP.TopForm.andPairs (26 : ℕ) x2 = (0 : ℕ) →         x3 - x4 ∈ x1 →           (∀ (x10 : Fin (13 : ℕ)), x5 ↑x10 = Bool.false ∧ x5 ((13 : ℕ) + ↑x10) = Decidable.decide (x10 = x4)) →             (have x11 : List Bool := x2.wires (List.ofFn fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x3));               ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x2.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x12) = (x11.getD x14 Bool.false && x5 x15 || x5 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x12) = (x5 x14 || x5 x15))) →               x5 x2.output = Bool.true := by
  intro x1 C p l f H1 H2 H3 H4 H5 H6
  exact PEqualNP.Outside.L_meta_2602.Flat.core x1 C p l f H1 H2 H3 H4 H5 H6


namespace CleanCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

lemma mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

lemma adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

lemma adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

lemma hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by decide +kernel

lemma degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

lemma adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

lemma k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)


lemma cost (B : Finset (Finset (Fin 26))) (T : Finset (Finset (Fin 26)))
    (hT : ∀ X ∈ T, X.card ≤ 1 ∨ X ∈ B)
    (hB : ∀ X ∈ B, ∃ U V : Finset (Fin 26), X = U ∪ V ∧ U.card < X.card ∧ V.card < X.card ∧
      (U.card ≤ 1 ∨ U ∈ B) ∧ (V.card ≤ 1 ∨ V ∈ B)) :
    (T.biUnion id).card ≤ T.card + B.card := by
  classical
  induction B using Finset.strongInductionOn generalizing T with
  | _ B ih =>
    by_cases h : B.Nonempty
    · obtain ⟨X,hX,hmax⟩ := Finset.exists_max_image B Finset.card h
      obtain ⟨U,V,he,hu,hv,hU,hV⟩ := hB X hX
      have carry (Y : Finset (Fin 26)) (hn : Y ≠ X) (hy : Y.card ≤ 1 ∨ Y ∈ B) :
          Y.card ≤ 1 ∨ Y ∈ B.erase X :=
        hy.imp_right (fun hh => Finset.mem_erase.mpr ⟨hn,hh⟩)
      have split' : ∀ Y ∈ B.erase X, ∃ U V : Finset (Fin 26), Y = U ∪ V ∧ U.card < Y.card ∧
          V.card < Y.card ∧ (U.card ≤ 1 ∨ U ∈ B.erase X) ∧ (V.card ≤ 1 ∨ V ∈ B.erase X) := by
        intro Y hy
        have hY := Finset.mem_of_mem_erase hy
        obtain ⟨u,v,e,hu',hv',a,b⟩ := hB Y hY
        have hm := hmax Y hY
        exact ⟨u,v,e,hu',hv',carry u (fun eq => by rw [eq] at hu'; omega) a,
          carry v (fun eq => by rw [eq] at hv'; omega) b⟩
      have dec := Finset.erase_ssubset hX
      have hc := Finset.card_erase_add_one hX
      by_cases inT : X ∈ T
      · let D := insert U (insert V (T.erase X))
        have result :=  ih (B.erase X) dec D (by
          intro Y hY
          change Y ∈ insert U (insert V (T.erase X)) at hY
          simp only [Finset.mem_insert,Finset.mem_erase] at hY
          rcases hY with rfl | rfl | ⟨hn,hm⟩
          · exact carry _ (fun eq => by rw [eq] at hu; omega) hU
          · exact carry _ (fun eq => by rw [eq] at hv; omega) hV
          · exact carry _ hn (hT _ hm)) split'
        have sub : T.biUnion id ⊆ D.biUnion id := by
          intro y hy
          obtain ⟨Z,hZ,hyZ⟩ := Finset.mem_biUnion.mp hy
          by_cases e : Z = X
          · change y ∈ Z at hyZ
            rw [e,he,Finset.mem_union] at hyZ
            rcases hyZ with z | z
            · exact Finset.mem_biUnion.mpr ⟨U,by simp [D],z⟩
            · exact Finset.mem_biUnion.mpr ⟨V,by simp [D],z⟩
          · exact Finset.mem_biUnion.mpr ⟨Z,by simp [D,e,hZ],hyZ⟩
        have c := Finset.card_le_card sub
        have c1 := Finset.card_insert_le U (insert V (T.erase X))
        have c2 := Finset.card_insert_le V (T.erase X)
        have c3 := Finset.card_erase_add_one inT
        dsimp [D] at result c
        omega
      · have result :=  ih (B.erase X) dec T (fun Y hY => carry Y (fun eq => inT (eq ▸ hY)) (hT Y hY)) split'
        omega
    · have B0 := Finset.not_nonempty_iff_eq_empty.mp h
      subst B
      apply Finset.card_biUnion_le.trans
      simpa using (Finset.sum_le_sum (s := T) (g := fun _ => (1 : ℕ)) (fun X hX => by simpa using hT X hX))

abbrev Vtx := Fin 26
abbrev Sup := Finset Vtx

def W {m : ℕ} (j : Fin m) : ℕ := 26+j.val

lemma W_inj {m : ℕ} : Function.Injective (@W m) := by
  intro a b h
  exact Fin.ext (Nat.add_left_cancel h)

def Needed {m : ℕ} (a b : Fin m → ℕ) (o w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o → (∀ j : Fin m, S (W j) → S (a j) ∧ S (b j)) → S w

lemma parent {m : ℕ} {a b : Fin m → ℕ} {o w} (h : Needed a b o w) :
    w = o ∨ ∃ j, Needed a b o (W j) ∧ (a j = w ∨ b j = w) := by
  apply h
  · exact .inl rfl
  · intro j hj
    have base : Needed a b o (W j) := by
      rcases hj with eq | ⟨i,hi,eq | eq⟩
      · rw [eq]; exact fun _ h _ => h
      · exact fun S ho hs => eq ▸ (hs i (hi S ho hs)).1
      · exact fun S ho hs => eq ▸ (hs i (hi S ho hs)).2
    exact ⟨.inr ⟨j,base,.inl rfl⟩, .inr ⟨j,base,.inr rfl⟩⟩

lemma children {m : ℕ} {a b : Fin m → ℕ} {o j} (h : Needed a b o (W j)) :
    Needed a b o (a j) ∧ Needed a b o (b j) :=
  ⟨fun S ho hs => (hs j (h S ho hs)).1, fun S ho hs => (hs j (h S ho hs)).2⟩

def fork {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) :=
  (S (a j)).Nonempty ∧ (S (b j)).Nonempty

open Classical in
noncomputable def roots {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => Needed a b o (W j) ∧ S (W j) = ∅ ∧ fork a b S j

open Classical in
noncomputable def merges {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) : Finset (Fin m) :=
  Finset.univ.filter fun j => S (W j) ≠ ∅ ∧ fork a b S j

open Classical in
noncomputable def darks {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => Needed a b o (W j) ∧ S (W j) = ∅

open Classical in
def pins {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) : Finset ℕ :=
  ({a j,b j} : Finset ℕ).filter fun w => S w = ∅

open Classical in
noncomputable def usedPins {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (j : Fin m) :=
  if Needed a b o (W j) then pins a b S j else ∅

open Classical in
lemma pc {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (j : Fin m)
    (step : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    (usedPins a b S o j).card + 2 * (if j ∈ roots a b S o then 1 else 0) +
      (if j ∈ merges a b S then 1 else 0) ≤ 1 + (if j ∈ darks a b S o then 1 else 0) := by
  classical
  have bd := Finset.card_insert_le (a j) ({b j} : Finset ℕ)
  simp only [Finset.card_singleton] at bd
  rcases step with h | h <;>
    by_cases ha : S (a j) = ∅ <;> by_cases hb : S (b j) = ∅ <;>
    by_cases nu : Needed a b o (W j) <;>
    simp [usedPins,pins,roots,merges,darks,fork,h,nu,ha,hb,Finset.filter_insert,
      Finset.filter_singleton,Finset.nonempty_iff_ne_empty,bd]

lemma pairDis {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] (P : ι → Finset α)
    (eq : (Finset.univ.biUnion P).card = ∑ j, (P j).card) :
    ∀ j k : ι, j ≠ k → Disjoint (P j) (P k) := by
  classical
  intro j k ne
  let E := (Finset.univ : Finset (ι)).erase j
  have hj : j ∉ E := Finset.notMem_erase _ _
  have de : insert j E = Finset.univ := Finset.insert_erase (Finset.mem_univ _)
  rw [← de, Finset.biUnion_insert, Finset.sum_insert hj] at eq
  have hle := Finset.card_biUnion_le (s := E) (t := P)
  have hcard := Finset.card_union_add_card_inter (P j) (E.biUnion P)
  have hz : (P j ∩ E.biUnion P).card = 0 := by omega
  have dis := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
  exact dis.mono_right (Finset.subset_biUnion_of_mem P (Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ k⟩))

lemma budget {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    let U := roots a b S o
    let M := merges a b S
    let D := darks a b S o
    let P := usedPins a b S o
    2*U.card + M.card ≤ m+1 ∧
    (2*U.card + M.card = m+1 →
      (∀ j k : Fin m, j ≠ k → Disjoint (P j) (P k)) ∧
      ∀ j ∈ D, ¬ fork a b S j → (P j).card = 2) := by
  classical
  intro U M D P
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => pc a b S o j (step j))
  change (∑ j, ((P j).card + 2 * (if j ∈ U then 1 else 0) + (if j ∈ M then 1 else 0))) ≤
    ∑ j, (1 + (if j ∈ D then 1 else 0)) at bound
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at bound
  simp at bound
  have sub : D.image W ⊆ insert o (Finset.univ.biUnion P) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨_,nu,h0⟩ := Finset.mem_filter.mp hj
    rcases parent nu with eq | ⟨k,nk,pk⟩
    · exact eq ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k,Finset.mem_univ _,?_⟩
      change W j ∈ usedPins a b S o k
      simp only [usedPins,ite_eq_left nk,pins,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
      exact ⟨pk.imp Eq.symm Eq.symm,h0⟩
  have dsub := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ W_inj] at dsub
  have ins := Finset.card_insert_le o (Finset.univ.biUnion P)
  have uni := Finset.card_biUnion_le (s := Finset.univ) (t := P)
  refine ⟨by omega,?_⟩
  intro tight
  have eq : (Finset.univ.biUnion P).card = ∑ j, (P j).card := by omega
  refine ⟨pairDis P eq,?_⟩
  intro j hj nf
  have hp := pc a b S o j (step j)
  have notU : j ∉ U := fun h => nf (Finset.mem_filter.mp h).2.2.2
  have notM : j ∉ M := fun h => nf (Finset.mem_filter.mp h).2.2
  have allEq : ∀ k : Fin m,
      (P k).card + 2*(if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0) =
        1 + (if k ∈ D then 1 else 0) := by
    intro k
    apply (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun k _ => pc a b S o k (step k))).mp ?_ _ (Finset.mem_univ _)
    change (∑ k, ((P k).card + 2 * (if k ∈ U then 1 else 0) + (if k ∈ M then 1 else 0))) =
      ∑ k, (1 + (if k ∈ D then 1 else 0))
    simp only [Finset.sum_add_distrib,← Finset.mul_sum]
    simp
    omega
  simpa [notU,notM,hj] using allEq j

lemma pieceWire {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup)
    (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) :
    ∀ w < 26+m, 2 ≤ (S w).card →
    ∃ j ∈ merges a b S, S (W j) = S w ∧
      S (W j) = S (a j) ∪ S (b j) ∧ (S (a j)).card < (S w).card ∧ (S (b j)).card < (S w).card := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hc
    by_cases hlo : w < 26
    · have := low w hlo
      omega
    let j : Fin m := ⟨w-26,by omega⟩
    have eq : W j = w := by dsimp [W,j]; omega
    have h1 := ha j
    have h2 := hb j
    rw [eq] at h1 h2
    rcases step j with he | he
    · rw [← eq,he] at hc
      simp at hc
    rw [eq] at he
    by_cases xa : S (a j) = S w
    · obtain ⟨k,hk,hk',hku,hka,hkb⟩ := ih _ h1 (by omega) (by rwa [xa])
      exact ⟨k,hk,hk'.trans xa,hku,xa ▸ hka,xa ▸ hkb⟩
    by_cases xb : S (b j) = S w
    · obtain ⟨k,hk,hk',hku,hka,hkb⟩ := ih _ h2 (by omega) (by rwa [xb])
      exact ⟨k,hk,hk'.trans xb,hku,xb ▸ hka,xb ▸ hkb⟩
    have ac := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨he ▸ Finset.subset_union_left,xa⟩)
    have bc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨he ▸ Finset.subset_union_right,xb⟩)
    refine ⟨j,?_,congrArg S eq,eq ▸ he,ac,bc⟩
    simp only [merges,Finset.mem_filter,Finset.mem_univ,true_and,eq,fork,Finset.nonempty_iff_ne_empty]
    refine ⟨fun e => by simp [e] at hc,fun e => xb (by simpa [e] using he.symm),
      fun e => xa (by simpa [e] using he.symm)⟩

noncomputable def bucket {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (v : Vtx) :=
  (merges a b S).filter fun j => 2 ≤ (S (W j)).card ∧ S (W j) ⊆ N v

lemma groupCost {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup)
    (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j)
    (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j)) (v : Vtx)
    (G : Finset (Fin m)) (leaf : Fin m → ℕ)
    (bd : ∀ j ∈ G, leaf j < 26+m) (sub : ∀ j ∈ G, S (leaf j) ⊆ N v) :
    (G.biUnion (fun j => S (leaf j))).card ≤ G.card + (bucket a b S v).card := by
  classical
  let B := (bucket a b S v).image (fun j => S (W j))
  let T := G.image (fun j => S (leaf j))
  have piece (w : ℕ) (hw : w < 26+m) (hs : S w ⊆ N v) :
      (S w).card ≤ 1 ∨ S w ∈ B := by
    by_cases h : (S w).card ≤ 1
    · exact Or.inl h
    have h2 : 2 ≤ (S w).card := by omega
    obtain ⟨k,hk,eq,_⟩ := pieceWire a b S low ha hb step w hw h2
    exact Or.inr (Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨hk,eq ▸ h2,eq ▸ hs⟩,eq⟩)
  have calcH := cost B T (by
    intro X hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact piece _ (bd _ hj) (sub _ hj)) (by
    intro X hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_,h2,hs⟩ := Finset.mem_filter.mp hj
    have wlt (k : Fin m) : W k < 26 + m := Nat.add_lt_add_left k.isLt _
    obtain ⟨k,hk,eq,he,e1,e2⟩ := pieceWire a b S low ha hb step _ (wlt j) h2
    have hu := eq.symm.trans he
    rw [hu] at hs
    exact ⟨_,_,hu,e1,e2,piece _ ((ha k).trans (wlt k)) (Finset.subset_union_left.trans hs),
      piece _ ((hb k).trans (wlt k)) (Finset.subset_union_right.trans hs)⟩)
  have ct : T.card ≤ G.card := Finset.card_image_le
  have cb : B.card ≤ (bucket a b S v).card := Finset.card_image_le
  have eq : T.biUnion id = G.biUnion (fun j => S (leaf j)) := by
    ext y
    simp [T]
  rw [eq] at calcH
  omega

def tag (x y : Vtx) := (min x y,max x y)

def edges := (Finset.univ : Finset (Vtx × Vtx)).filter fun e => e.1 < e.2 ∧ adjb e.1 e.2 = true

lemma ecard : edges.card = 52 := by decide +kernel

lemma geom : ∀ x y : Vtx, adjb x y = true ↔ tag x y ∈ edges := by decide +kernel

lemma avoid : ∀ x z : Vtx, ∃ y ∈ N x, ∀ a ∈ ({x,y,z} : Sup), ∀ b ∈ ({x,y,z} : Sup),
    adjb a b = true → a = x ∨ b = x := by
  intro x z
  by_cases eq : x = z
  · subst z
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (by rw [degN]; decide : 0 < (N x).card)
    refine ⟨y,hy,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    intro a ha b hb h
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all [adj_irr]
  · have h : ¬ N x ⊆ N z := by
      intro sub
      have hc := hLN x z eq
      rw [Finset.inter_eq_left.mpr sub,degN] at hc
      omega
    obtain ⟨y,hy,hn⟩ := Finset.not_subset.mp h
    have hz : adjb z y = false := by simpa [mem_N] using hn
    have hyz : adjb y z = false := (adj_symm y z).trans hz
    refine ⟨y,hy,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    intro a ha b hb h
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all [adj_irr]

lemma tallyRoots {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ) (z : Fin m → Vtx)
    (leaf : Fin m → ℕ) (low : ∀ w < 26, (S w).card ≤ 1) (ha : ∀ j, a j < W j)
    (hb : ∀ j, b j < W j) (step : ∀ j, S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j))
    (bd : ∀ j, leaf j < 26+m) (hsz : m ≤ 64)
    (sub : ∀ j ∈ roots a b S o, S (leaf j) ⊆ N (z j))
    (cover : ∀ e ∈ edges, ∃ j ∈ roots a b S o, ∃ y ∈ S (leaf j), e = tag (z j) y) :
    let U := roots a b S o
    let M := merges a b S
    let E := fun j => (S (leaf j)).image (tag (z j))
    2*U.card+M.card = m+1 ∧ (∀ j ∈ U, S (leaf j) = N (z j)) ∧
      ∀ j ∈ U, ∀ k ∈ U, j ≠ k → Disjoint (E j) (E k) := by
  classical
  intro U M E
  let G := fun v => U.filter (fun j => z j = v)
  let L := fun v => (G v).biUnion (fun j => S (leaf j))
  have costs (v) : (L v).card ≤ (G v).card + (bucket a b S v).card := by
    apply groupCost a b S low ha hb step v (G v) leaf (fun j _ => bd j)
    intro j hj
    obtain ⟨hu,hz⟩ := Finset.mem_filter.mp hj
    exact hz ▸ sub j hu
  have unionE : edges ⊆ Finset.univ.biUnion (fun v => (L v).image (tag v)) := by
    intro e he
    obtain ⟨j,hj,y,hy,rfl⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨z j,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨y,Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,rfl⟩,hy⟩,rfl⟩⟩
  have c52 : 52 ≤ ∑ v, (L v).card := ecard ▸ (Finset.card_le_card unionE).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)))
  have dis : (↑(Finset.univ : Finset Vtx) : Set Vtx).PairwiseDisjoint (bucket a b S) := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro k hi hj
    obtain ⟨_,hc,si⟩ := Finset.mem_filter.mp hi
    have sj := (Finset.mem_filter.mp hj).2.2
    have hcard := Finset.card_le_card (Finset.subset_inter si sj)
    have hsmall := hLN i j ne
    omega
  have cb : (∑ v, (bucket a b S v).card) ≤ M.card := by
    rw [← Finset.card_biUnion dis]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun _ _ => Finset.filter_subset _ _))
  have cg : ∑ v, (G v).card = U.card :=
    (Finset.card_eq_sum_card_fiberwise (fun j (_ : j ∈ U) => Finset.mem_univ (z j))).symm
  have sumc := Finset.sum_le_sum (s := Finset.univ) (fun v _ => costs v)
  rw [Finset.sum_add_distrib,cg] at sumc
  let F := fun j => if j ∈ U then E j else ∅
  have all : edges ⊆ Finset.univ.biUnion F := by
    intro e he
    obtain ⟨j,hj,y,hy,rfl⟩ := cover e he
    change j ∈ U at hj
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,by simpa [F,hj,E] using Finset.mem_image_of_mem (tag (z j)) hy⟩
  have mass (j) : (F j).card ≤ (if j ∈ U then 4 else 0) := by
    by_cases hj : j ∈ U
    · simp only [F,ite_eq_left hj,E]
      exact Finset.card_image_le.trans ((Finset.card_le_card (sub j hj)).trans_eq (degN _))
    · simp [F,hj]
  have cm := Finset.sum_le_sum (s := Finset.univ) (fun j _ => mass j)
  have sf : (∑ j : Fin m, (if j ∈ U then 4 else 0 : ℕ)) = U.card*4 := by simp
  rw [sf] at cm
  have cAll := Finset.card_le_card all
  rw [ecard] at cAll
  have cbi := Finset.card_biUnion_le (s := Finset.univ) (t := F)
  have budgetH := (budget a b S o step).1
  change 2*U.card + M.card ≤ m+1 at budgetH
  refine ⟨by omega,?_,?_⟩
  · intro j hj
    have sumEq : (∑ j, (F j).card) = ∑ j : Fin m, (if j ∈ U then 4 else 0 : ℕ) := by rw [sf]; omega
    have eq := (Finset.sum_eq_sum_iff_of_le (fun j _ => mass j)).mp sumEq j (Finset.mem_univ j)
    simp only [F,ite_eq_left hj,E] at eq
    apply Finset.eq_of_subset_of_card_le (sub j hj)
    rw [degN,← eq]
    exact Finset.card_image_le
  · intro j hj k hk ne
    have eq : (Finset.univ.biUnion F).card = ∑ j, (F j).card := by omega
    simpa [F,hj,hk] using pairDis F eq j k ne

def Cross {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (j : Fin m) (x y : Vtx) :=
  (x ∈ S (a j) ∧ y ∈ S (b j)) ∨ (y ∈ S (a j) ∧ x ∈ S (b j))

lemma tag_symm (x y : Vtx) : tag x y = tag y x := by simp [tag,min_comm,max_comm]

lemma starChoice {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (o : ℕ)
    (sound : ∀ j ∈ roots a b S o, ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true) :
    ∃ (z : Fin m → Vtx) (leaf : Fin m → ℕ), (∀ j, leaf j = a j ∨ leaf j = b j) ∧
      ∀ j ∈ roots a b S o, S (leaf j) ⊆ N (z j) ∧ ∀ x y, Cross a b S j x y →
        ∃ t ∈ S (leaf j), tag x y = tag (z j) t := by
  classical
  suffices h : ∀ j : Fin m, ∃ (z : Vtx) (w : ℕ), (w = a j ∨ w = b j) ∧
      (j ∈ roots a b S o → S w ⊆ N z ∧ ∀ x y, Cross a b S j x y →
        ∃ t ∈ S w, tag x y = tag z t) by
    choose z w hw hz using h
    exact ⟨z,w,hw,hz⟩
  intro j
  by_cases hj : j ∈ roots a b S o
  · obtain ⟨_,_,⟨u,hu⟩,v,hv⟩ := (Finset.mem_filter.mp hj).2
    by_cases one : ∀ x ∈ S (a j), x = u
    · refine ⟨u,b j,Or.inr rfl,fun _ => ⟨fun y hy => (mem_N _ _).2 (sound j hj u hu y hy),?_⟩⟩
      intro x y cr
      rcases cr with ⟨h,k⟩ | ⟨h,k⟩
      · exact ⟨y,k,by rw [one x h]⟩
      · exact ⟨x,k,by rw [one y h,tag_symm]⟩
    · push Not at one
      obtain ⟨u',hu',ne⟩ := one
      have only (y) (hy : y ∈ S (b j)) : y = v :=
        k22 u' u y v (sound j hj _ hu' _ hy) (sound j hj _ hu' _ hv)
          (sound j hj _ hu _ hy) (sound j hj _ hu _ hv) ne
      refine ⟨v,a j,Or.inl rfl,fun _ => ⟨fun x hx => (mem_N _ _).2 ((adj_symm v x).trans (sound j hj _ hx _ hv)),?_⟩⟩
      intro x y cr
      rcases cr with ⟨h,k⟩ | ⟨h,k⟩
      · exact ⟨x,h,by rw [only y k,tag_symm]⟩
      · exact ⟨y,h,by rw [only x k]⟩
  · exact ⟨0,a j,Or.inl rfl,fun h => (hj h).elim⟩

def Holds (S : ℕ → Sup) (T : Sup) (w : ℕ) := ∃ t ∈ T, t ∈ S w

def ClosedAt {m : ℕ} (a b : Fin m → ℕ) (A : Fin m → Prop) (o : ℕ) (r : Fin m)
    (H : ℕ → Prop) :=
  ∀ j : Fin m, Needed a b o (W j) → j ≠ r →
    (A j → H (a j) → H (b j) → H (W j)) ∧ (¬ A j → H (a j) ∨ H (b j) → H (W j))

def Force {m : ℕ} (a b : Fin m → ℕ) (A : Fin m → Prop) (o : ℕ) (r : Fin m)
    (p : Vtx) (w : ℕ) :=
  ∀ l ∈ N p, ∀ H : ℕ → Prop, H p.val → H l.val → ClosedAt a b A o r H → H w → H o

lemma route {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (inputs : ∀ t : Vtx, t ∈ S t.val)
    (out0 : S o = ∅) (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (z : Fin m → Vtx) (leaf : Fin m → ℕ)
    (hs : ∀ j ∈ roots a b S o, S (leaf j) = N (z j))
    (origin : ∀ j ∈ roots a b S o, ∀ x y, Cross a b S j x y →
      adjb x y = true ∧ ∃ t ∈ S (leaf j), tag x y = tag (z j) t)
    (dis : ∀ j ∈ roots a b S o, ∀ k ∈ roots a b S o, j ≠ k →
      Disjoint ((S (leaf j)).image (tag (z j))) ((S (leaf k)).image (tag (z k))))
    (tight : 2*(roots a b S o).card + (merges a b S).card = m+1)
    (r : Fin m) (hr : r ∈ roots a b S o)
    (start : Force a b A o r (z r) (W r)) (D : ℕ → Prop)
    (dr : D (W r)) (dOr : ∀ j, ¬ A j → D (a j) ∨ D (b j) → D (W j)) : D o := by
  classical
  have step (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases h : A j
    · exact .inl ((ops j).1 h)
    · exact .inr ((ops j).2 h)
  obtain ⟨uniq,two⟩ := (budget a b S o step).2 tight
  let p := z r
  have shield (v : Vtx) : ∃ l ∈ N p, ∃ H : ℕ → Prop, H p.val ∧ H l.val ∧
      ClosedAt a b A o r H ∧ ¬ H o ∧ (∀ w, S w = ∅ → ¬ H w) ∧ ∀ w, v ∈ S w → H w := by
    obtain ⟨l,hl,good⟩ := avoid p v
    let T : Sup := {p,l,v}
    refine ⟨l,hl,Holds S T,⟨p,by simp [T],inputs p⟩,⟨l,by simp [T],inputs l⟩,?_,
      by simp [Holds,out0],fun w h => by simp [Holds,h],fun w h => ⟨v,by simp [T],h⟩⟩
    intro k nk ne
    constructor
    · intro ak ⟨s,hsT,hsa⟩ ⟨t,htT,htb⟩
      have hk : k ∈ roots a b S o := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,nk,(ops k).1 ak,⟨s,hsa⟩,⟨t,htb⟩⟩
      obtain ⟨adj,y,hy,ey⟩ := origin k hk s t (.inl ⟨hsa,htb⟩)
      have mk : tag s t ∈ (S (leaf k)).image (tag (z k)) :=
        Finset.mem_image.mpr ⟨y,hy,ey.symm⟩
      have mr : tag s t ∈ (S (leaf r)).image (tag (z r)) := by
        rw [hs r hr]
        rcases good s hsT t htT adj with hh | hh
        · exact Finset.mem_image.mpr ⟨t,(mem_N _ _).mpr (by change adjb p t = true; rwa [← hh]),by rw [hh]⟩
        · exact Finset.mem_image.mpr ⟨s,(mem_N _ _).mpr (by change adjb p s = true; rw [← hh]; exact (adj_symm t s).trans adj),
              by rw [hh,tag_symm]⟩
      exact (Finset.disjoint_left.mp (dis k hk r hr ne) mk mr).elim
    · intro no ab
      rw [show Holds S T (W k) ↔ ∃ x ∈ T, x ∈ S (W k) from Iff.rfl,(ops k).2 no]
      rcases ab with ⟨x,hx,h⟩ | ⟨x,hx,h⟩
      · exact ⟨x,hx,Finset.mem_union_left _ h⟩
      · exact ⟨x,hx,Finset.mem_union_right _ h⟩
  have walk : ∀ n w, 26+m-w = n → Needed a b o w → D w → Force a b A o r p w → D o := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro w en nw dw fw
      by_cases eo : w = o
      · exact eo ▸ dw
      have zero : S w = ∅ := by
        by_contra h
        obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
        obtain ⟨l,hl,H,hp,hL,hc,hn,_,lift⟩ := shield v
        exact hn (fw l hl H hp hL hc (lift w hv))
      obtain ⟨k,nk,readW⟩ := (parent nw).resolve_left eo
      have member (g : Fin m) (ng : Needed a b o (W g)) (rg : a g = w ∨ b g = w) :
          w ∈ usedPins a b S o g := by
        simp only [usedPins,ite_eq_left ng,pins,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
        exact ⟨rg.imp Eq.symm Eq.symm,zero⟩
      have only (g : Fin m) (ng : Needed a b o (W g)) (rg : a g = w ∨ b g = w) : g = k := by
        by_contra neq
        exact Finset.disjoint_left.mp (uniq g k neq) (member g ng rg) (member k nk readW)
      have relay (H : ℕ → Prop) (hc : ClosedAt a b A o r H)
          (hk : (A k → (H (a k) ∨ a k = w) → (H (b k) ∨ b k = w) → H (W k)) ∧
            (¬A k → H (a k) ∨ a k = w ∨ H (b k) ∨ b k = w → H (W k))) :
          ClosedAt a b A o r (fun t => H t ∨ t = w) := by
        intro g ng nr
        by_cases e : g = k
        · subst g
          constructor
          · intro op h1 h2
            exact .inl (hk.1 op h1 h2)
          · intro op h
            apply Or.inl
            apply hk.2 op
            tauto
        · have na : a g ≠ w := fun h => e (only g ng (.inl h))
          have nb : b g ≠ w := fun h => e (only g ng (.inr h))
          simp only [na,nb,or_false]
          exact ⟨fun op h1 h2 => .inl ((hc g ng nr).1 op h1 h2),
            fun op h => .inl ((hc g ng nr).2 op h)⟩
      by_cases op : A k
      · have dk : k ∈ darks a b S o := Finset.mem_filter.mpr ⟨Finset.mem_univ _,nk,(ops k).1 op⟩
        have nf : ¬fork a b S k := by
          rcases readW with e | e <;> simp [fork,e,zero]
        have htwo := two k dk nf
        have both : S (a k) = ∅ ∧ S (b k) = ∅ := by
          by_cases za : S (a k) = ∅ <;> by_cases zb : S (b k) = ∅ <;>
            simp_all [usedPins,pins,Finset.filter_insert,Finset.filter_singleton]
        obtain ⟨l,hl,H,hp,hL,hc,hn,off,_⟩ := shield p
        have hk := relay H hc ⟨by
          intro _ h1 h2
          have e1 := h1.resolve_left (off _ both.1)
          have e2 := h2.resolve_left (off _ both.2)
          exact (neab k (e1.trans e2.symm)).elim,fun no => (no op).elim⟩
        have bad := fw l hl _ (Or.inl hp) (Or.inl hL) hk (Or.inr rfl)
        exact (bad.elim hn (fun e => eo e.symm)).elim
      · have fk : Force a b A o r p (W k) := by
          intro l hl H hP hL hc hW
          have h := fw l hl _ (Or.inl hP) (Or.inl hL)
            (relay H hc ⟨fun _ _ _ => hW,fun _ _ => hW⟩) (Or.inr rfl)
          exact h.resolve_right (Ne.symm eo)
        have lt : w < W k := readW.elim (fun e => e ▸ ha k) (fun e => e ▸ hb k)
        have bd : W k < 26+m := Nat.add_lt_add_left k.isLt _
        exact ih _ (by omega : 26+m-W k < n) _ rfl nk
          (dOr k op (by rcases readW with h | h; exact .inl (h.symm ▸ dw); exact .inr (h.symm ▸ dw))) fk
  exact walk _ _ rfl (Finset.mem_filter.mp hr).2.1 dr start

lemma decomp {m w : ℕ} (h : w < 26+m) : w < 26 ∨ ∃ j : Fin m, w = W j := by
  by_cases hw : w < 26
  · exact .inl hw
  · exact .inr ⟨⟨w-26,by omega⟩,by dsimp [W]; omega⟩

set_option maxHeartbeats 2000000 in
lemma assemble {m : ℕ} (a b : Fin m → ℕ) (S : ℕ → Sup) (A : Fin m → Prop) (o : ℕ)
    (ha : ∀ j, a j < W j) (hb : ∀ j, b j < W j) (neab : ∀ j, a j ≠ b j)
    (hsz : m ≤ 64) (hout : o < 26+m)
    (inp : ∀ t : Vtx, S t.val = {t}) (out0 : S o = ∅)
    (ops : ∀ j, (A j → S (W j) = ∅) ∧ (¬ A j → S (W j) = S (a j) ∪ S (b j)))
    (Q : Vtx → Vtx → ℕ → Prop)
    (qIn : ∀ x y t : Vtx, Q x y t.val → t = x ∨ t = y)
    (qOut : ∀ x y, adjb x y = true → Q x y o)
    (qStep : ∀ x y j, Q x y (W j) →
      (A j → Q x y (a j) ∧ Q x y (b j)) ∧ (¬ A j → Q x y (a j) ∨ Q x y (b j)))
    (sound : ∀ j, A j → ∀ x ∈ S (a j), ∀ y ∈ S (b j), adjb x y = true)
    (x y : Vtx) (edge : adjb x y = true) (D : ℕ → Prop) (dy : D y.val)
    (dAnd : ∀ j, A j → ((x ∈ S (a j) ∧ D (b j)) ∨ (D (a j) ∧ x ∈ S (b j))) → D (W j))
    (dOr : ∀ j, ¬ A j → D (a j) ∨ D (b j) → D (W j)) : D o := by
  classical
  let U := roots a b S o
  have rootAnd (j : Fin m) (hj : j ∈ U) : A j := by
    by_contra no
    obtain ⟨_,h0,f⟩ := (Finset.mem_filter.mp hj).2
    rw [(ops j).2 no,Finset.union_eq_empty] at h0
    exact f.1.ne_empty h0.1
  have sov (j : Fin m) (hj : j ∈ U) := sound j (rootAnd j hj)
  obtain ⟨z,leaf,hside,hstar⟩ := starChoice a b S o sov
  have wlt (j : Fin m) : W j < 26+m := Nat.add_lt_add_left j.isLt _
  have seek (s t : Vtx) (h : adjb s t = true) : ∃ j ∈ U, Cross a b S j s t := by
    suffices run : ∀ w < 26+m, Needed a b o w → Q s t w →
        (s ∈ S w ∨ t ∈ S w) ∨ ∃ j ∈ U, Cross a b S j s t by
      simpa [out0] using run o hout (fun _ ho _ => ho) (qOut s t h)
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw qw
      rcases decomp hw with lo | ⟨j,rfl⟩
      · let v : Vtx := ⟨w,lo⟩
        have eq : S w = {v} := inp v
        rcases qIn s t v qw with e | e
        · exact .inl (.inl (by rw [eq,Finset.mem_singleton]; exact e.symm))
        · exact .inl (.inr (by rw [eq,Finset.mem_singleton]; exact e.symm))
      obtain ⟨na,nb⟩ := children nw
      by_cases aj : A j
      · obtain ⟨qa,qb⟩ := (qStep s t j qw).1 aj
        rcases ih _ (ha j) ((ha j).trans hw) na qa with hitsA | got
        · rcases ih _ (hb j) ((hb j).trans hw) nb qb with hitsB | got
          · right
            have single (v) (h1 : v ∈ S (a j)) (h2 : v ∈ S (b j)) : False := by
              have e := sound j aj v h1 v h2
              rw [adj_irr] at e
              contradiction
            rcases hitsA with aa | aa <;> rcases hitsB with bb | bb
            · exact (single s aa bb).elim
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨s,aa⟩,⟨t,bb⟩⟩,.inl ⟨aa,bb⟩⟩
            · exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,nw,(ops j).1 aj,⟨t,aa⟩,⟨s,bb⟩⟩,.inr ⟨aa,bb⟩⟩
            · exact (single t aa bb).elim
          · exact .inr got
        · exact .inr got
      · rcases (qStep s t j qw).2 aj with qa | qb
        · have hh := ih _ (ha j) ((ha j).trans hw) na qa
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
        · have hh := ih _ (hb j) ((hb j).trans hw) nb qb
          rw [(ops j).2 aj]
          simp only [Finset.mem_union]
          tauto
  have st (j) : S (W j) = ∅ ∨ S (W j) = S (a j) ∪ S (b j) := by
    by_cases aj : A j
    · exact .inl ((ops j).1 aj)
    · exact .inr ((ops j).2 aj)
  have low (w : ℕ) (hw : w < 26) : (S w).card ≤ 1 := by
    rw [inp (⟨w,hw⟩ : Vtx)]
    simp
  have bound (j) : leaf j < 26+m := (hside j).elim (fun e => e.symm ▸ (ha j).trans (wlt j))
    (fun e => e.symm ▸ (hb j).trans (wlt j))
  obtain ⟨tight,full,apart⟩ := tallyRoots a b S o z leaf low ha hb st bound hsz
    (fun j hj => (hstar j hj).1) (by
      rintro ⟨s,t⟩ he
      obtain ⟨_,hst,adj⟩ := Finset.mem_filter.mp he
      obtain ⟨j,hj,hcr⟩ := seek s t adj
      obtain ⟨u,hu,eq⟩ := (hstar j hj).2 s t hcr
      exact ⟨j,hj,u,hu,by simpa [tag,min_eq_left hst.le,max_eq_right hst.le] using eq⟩)
  obtain ⟨r,hr,cr⟩ := seek x y edge
  have ys : ∀ w < 26+m, y ∈ S w → D w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hy
      rcases decomp hw with lo | ⟨k,rfl⟩
      · have ht : y = (⟨w,lo⟩ : Vtx) := Finset.mem_singleton.mp ((inp ⟨w,lo⟩) ▸ hy)
        have e : y.val = w := congrArg Fin.val ht
        exact e ▸ dy
      by_cases ak : A k
      · simp [(ops k).1 ak] at hy
      · rw [(ops k).2 ak,Finset.mem_union] at hy
        exact dOr k ak (hy.imp (ih _ (ha k) ((ha k).trans hw)) (ih _ (hb k) ((hb k).trans hw)))
  apply route a b S A o ha hb neab (fun t => by rw [inp]; simp) out0 ops z leaf full
      (fun j hj s t hc => ⟨by
        rcases hc with ⟨aa,bb⟩ | ⟨aa,bb⟩
        · exact sov j hj s aa t bb
        · exact (adj_symm s t).trans (sov j hj t aa s bb),(hstar j hj).2 s t hc⟩)
      apart tight r hr ?_ D ?_ dOr
  · intro l hl H hp hl' hc hroot
    suffices hh : ∀ w < 26+m, Needed a b o w → Q (z r) l w → H w from
      hh o hout (fun _ ho _ => ho) (qOut _ _ ((mem_N _ _).mp hl))
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw nw hq
      rcases decomp hw with lo | ⟨j,rfl⟩
      · rcases qIn _ _ ⟨w,lo⟩ hq with eq | eq
        · have e : w = (z r).val := congrArg Fin.val eq
          exact e.symm ▸ hp
        · have e : w = l.val := congrArg Fin.val eq
          exact e.symm ▸ hl'
      by_cases e : j = r
      · exact e.symm ▸ hroot
      obtain ⟨na,nb⟩ := children nw
      have ia := ih _ (ha j) ((ha j).trans hw) na
      have ib := ih _ (hb j) ((hb j).trans hw) nb
      by_cases aj : A j
      · obtain ⟨q1,q2⟩ := (qStep _ _ _ hq).1 aj
        exact (hc j nw e).1 aj (ia q1) (ib q2)
      · exact (hc j nw e).2 aj (((qStep _ _ _ hq).2 aj).imp ia ib)
  · apply dAnd r (rootAnd r hr)
    rcases cr with ⟨aa,bb⟩ | ⟨aa,bb⟩
    · exact .inl ⟨aa,ys _ ((hb r).trans (wlt r)) bb⟩
    · exact .inr ⟨ys _ ((ha r).trans (wlt r)) aa,bb⟩

def Jset : Finset (Fin 13) := {0,1,3,9}

lemma adjSide : ∀ p l : Fin 13, adjb (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true ↔ p-l ∈ Jset := by
  decide +kernel

lemma pairSpec (s t : Vtx) : adjb s t = true ↔ ∃ p l : Fin 13, p-l ∈ Jset ∧
    pr s t (Fin.castAdd 13 p) = true ∧ pr s t (Fin.natAdd 13 l) = true := by
  constructor
  · have hc : ∀ s t : Vtx, adjb s t = true →
        (let p : Fin 13 := ⟨(min s.val t.val)%13,by omega⟩
         let l : Fin 13 := ⟨(max s.val t.val-13)%13,by omega⟩
         p-l ∈ Jset ∧ pr s t (Fin.castAdd 13 p) = true ∧ pr s t (Fin.natAdd 13 l) = true) := by
      decide +kernel
    intro h
    exact ⟨_,_,hc s t h⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    have h := (adjSide p l).2 edge
    have ep : Fin.castAdd 13 p = s ∨ Fin.castAdd 13 p = t := of_decide_eq_true hp
    have el : Fin.natAdd 13 l = s ∨ Fin.natAdd 13 l = t := of_decide_eq_true hl
    have ne : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro eq
      have h1 := congrArg Fin.val eq
      change p.val = 13 + l.val at h1
      omega
    rcases ep with eq | eq <;> rcases el with eq' | eq'
    · exact (ne (eq.trans eq'.symm)).elim
    · simpa only [eq,eq'] using h
    · rw [adj_symm]
      simpa only [eq,eq'] using h
    · exact (ne (eq.trans eq'.symm)).elim

end CleanCase

open PEqualNP.Outside.L_meta_2602.CleanCase PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 2000000 in
lemma clean_positive : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.or; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (13 : ℕ)) (x7 x8 : ℕ → Bool),   have x9 : Fin (26 : ℕ) → ℕ → (ℕ → Bool) → Prop := fun (x9 : Fin (26 : ℕ)) (x10 : ℕ) (x11 : ℕ → Bool) =>     (∀ x12 < (26 : ℕ), x11 x12 = Decidable.decide (x12 = x10)) ∧       have x12 : List Bool := x4.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9));       ∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 x16 : ℕ), x4.gates[x13]? = Option.some x14 → x14.inputs = [x15, x16] → (x14.op = x2 → x11 ((26 : ℕ) + x13) = (x12.getD x15 Bool.false && x11 x16 || x11 x15 && x12.getD x16 Bool.false)) ∧ (x14.op = x3 → x11 ((26 : ℕ) + x13) = (x11 x15 || x11 x16));   x4.size ≤ (64 : ℕ) → (∀ (x11 : ℕ) (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x11]? = Option.some x12 → (x12.op = x2 ∨ x12.op = x3) ∧ ∃ (x14 : ℕ) (x15 : ℕ), x12.inputs = [x14, x15] ∧ x14 ≠ x15 ∧ x14 < (26 : ℕ) + x11 ∧ x15 < (26 : ℕ) + x11) → (∀ (x12 : Fin (26 : ℕ) → Bool), x4.eval (List.ofFn x12) = Bool.true ↔ ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 ∧ x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true ∧ x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x14 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = x2 → ∀ (x17 : Fin (26 : ℕ) → Bool), (x4.wires (List.ofFn x17)).getD ((26 : ℕ) + x14) Bool.false = Bool.true → x4.eval (List.ofFn x17) = Bool.true) → x5 - x6 ∈ x1 → x9 (Fin.castAdd (13 : ℕ) x5) ((13 : ℕ) + ↑x6) x7 → x9 (Fin.natAdd (13 : ℕ) x6) (↑x5) x8 → x7 x4.output = Bool.true ∨ x8 x4.output = Bool.true := by
  dsimp only
  intro C p l dP dL size gates correct _ clean incidence traceP traceL
  classical
  let m := C.gates.length
  let g (j : Fin m) := C.gates[j.val]
  have hg (j : Fin m) : C.gates[j.val]? = some (g j) := List.getElem?_eq_getElem j.isLt
  have raw (j : Fin m) := (gates j (g j) (hg j)).2
  choose a b pins ne ha hb using raw
  let A (j : Fin m) := (g j).op = GateOp.and
  have orOp (j : Fin m) (no : ¬ A j) : (g j).op = GateOp.or :=
    ((gates j (g j) (hg j)).1).resolve_left no
  let V (f : Vtx → Bool) w := val C.gates w f = true
  let one (v : Vtx) (u : Vtx) := decide (u=v)
  let S (w : ℕ) : Sup := Finset.univ.filter fun v => V (one v) w
  have mem (w : ℕ) (u : Vtx) : u ∈ S w ↔ V (one u) w := by simp [S]
  have andEv (f : Vtx → Bool) (j : Fin m) (op : A j) :
      V f (W j) ↔ V f (a j) ∧ V f (b j) := by
    have h := val_and C.gates f j.val j.isLt op
    change _ ↔ ∀ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have orEv (f : Vtx → Bool) (j : Fin m) (op : ¬A j) :
      V f (W j) ↔ V f (a j) ∨ V f (b j) := by
    have h := val_or C.gates f j.val j.isLt (orOp j op)
    change _ ↔ ∃ k ∈ (g j).inputs, _ at h
    simpa [V,W,pins j,ha j,hb j] using h
  have same (s t : Vtx) : V (pr s t) C.output ↔ adjb s t = true :=
    (correct (pr s t)).trans (pairSpec s t).symm
  have off (s : Vtx) : ¬V (one s) C.output := by
    intro h
    have eq : one s = pr s s := by funext v; simp [one,pr]
    rw [eq] at h
    have h1 := (same s s).1 h
    simp [adj_irr] at h1
  have cleanG (f : Vtx → Bool) (j : Fin m) (op : A j) (h : V f (W j)) : V f C.output := by
    apply clean j j.isLt _ f h
    change (C.gates[j.val]?.getD ⟨.or,[]⟩).op = .and
    rw [hg]
    exact op
  have legal : ∀ h ∈ C.gates, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
    intro h hh
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hh
    obtain ⟨op,a',b',eq,_⟩ := gates j h hj
    exact ⟨op,by simp [eq]⟩
  have up (s t u : Vtx) (hu : u = s ∨ u = t) (w : ℕ) (hw : u ∈ S w) : V (pr s t) w := by
    apply val_mono C.gates legal (one u) (pr s t) _ w ((mem w u).1 hw)
    intro v hv
    have eq : v = u := of_decide_eq_true hv
    exact decide_eq_true (eq.symm ▸ hu)
  let X : Vtx := Fin.castAdd 13 p
  let Y : Vtx := Fin.natAdd 13 l
  have edge : adjb X Y = true := (adjSide p l).2 incidence
  have hout : C.output < 26+m := by
    by_contra! h
    have yes := (same X Y).2 edge
    change val C.gates C.output (pr X Y) = true at yes
    rw [val_big _ _ _ h] at yes
    contradiction
  left
  apply assemble a b S A C.output ha hb ne size hout ?_ ?_ ?_
    (fun s t w => V (pr s t) w) ?_ (fun s t => (same s t).2) ?_ ?_
    X Y edge (fun w => dP w = true) ?_ ?_ ?_
  · intro t
    ext s
    rw [mem]
    change val C.gates t.val (one s) = true ↔ _
    rw [val_input _ _ _ t.isLt]
    simp [one,eq_comm]
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    exact fun v hv => off v ((mem _ _).mp hv)
  · intro j
    constructor
    · intro aj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun v hv => off v (cleanG _ j aj ((mem _ _).mp hv))
    · intro no
      ext v
      rw [Finset.mem_union,mem,mem,mem,orEv _ j no]
  · intro s t v h
    change val C.gates v.val (pr s t) = true at h
    rw [val_input _ _ _ v.isLt] at h
    exact of_decide_eq_true h
  · intro s t j h
    exact ⟨fun op => (andEv _ j op).1 h,fun op => (orEv _ j op).1 h⟩
  · intro j op s hsa t htb
    exact (same s t).1 (cleanG _ j op ((andEv _ j op).2
      ⟨up s t s (.inl rfl) _ hsa,up s t t (.inr rfl) _ htb⟩))
  · rw [traceP.1 _ Y.isLt]
    simp [Y,Nat.add_comm]
  · intro j op h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).1 op]
    simp only [Bool.or_eq_true,Bool.and_eq_true]
    exact h.imp (fun hh => ⟨(mem _ _).mp hh.1,hh.2⟩) (fun hh => ⟨hh.1,(mem _ _).mp hh.2⟩)
  · intro j no h
    change dP (26+j.val) = true
    rw [(traceP.2 j (g j) (a j) (b j) (hg j) (pins j)).2 (orOp _ no),Bool.or_eq_true]
    exact h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def incidence (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def wellFormed (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j

def computes (C : Circuit) : Prop :=
  ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, incidence p l ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true

def directional (C : Circuit) (base tangent : ℕ) (d : ℕ → Bool) : Prop :=
  (∀ i < 26, d i = decide (i = tangent)) ∧
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (26 + j) =
      ((C.wires (List.ofFn fun k : Fin 26 => decide (k.val = base))).getD a false && d b ||
        d a && (C.wires (List.ofFn fun k : Fin 26 => decide (k.val = base))).getD b false)) ∧
    (g.op = .or → d (26 + j) = (d a || d b))

def cleanAnd (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = .and → ∀ x : Fin 26 → Bool,
    (C.wires (List.ofFn x)).getD (26 + j) false = true → C.eval (List.ofFn x) = true

lemma counterexample_shape (C : Circuit) (hs : C.size ≤ 64)
    (hg : wellFormed C) (hc : computes C) (v u : ℕ → Bool)
    (hv : directional C 0 13 v) (hu : directional C 13 0 u)
    (hvo : v C.output = false) (huo : u C.output = false) :
    0 < PEqualNP.TopForm.andPairs 26 C ∧
      ∃ j < C.gates.length, (gateAt C j).op = .and ∧ ∃ x : Fin 26 → Bool,
        (C.wires (List.ofFn x)).getD (26 + j) false = true ∧
          C.eval (List.ofFn x) = false := by
  classical
  have diff : ∀ p l : Fin 13, incidence p l ↔
      p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    unfold incidence
    decide
  have spec : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    rw [hc x]
    simp only [diff]
  have seed0 : (fun k : Fin 26 => decide (k.val = 0)) =
      (fun k : Fin 26 => decide (k = Fin.castAdd 13 (0 : Fin 13))) := by
    funext k
    revert k
    decide
  have seed13 : (fun k : Fin 26 => decide (k.val = 13)) =
      (fun k : Fin 26 => decide (k = Fin.natAdd 13 (0 : Fin 13))) := by
    funext k
    revert k
    decide
  have vi : ∀ m : Fin 13, v m.val = false ∧ v (13 + m.val) = decide (m = 0) := by
    intro m
    constructor
    · rw [hv.1 m.val (by have := m.isLt; omega)]
      simp only [decide_eq_false_iff_not]
      have := m.isLt
      omega
    · rw [hv.1 (13 + m.val) (by have := m.isLt; omega)]
      revert m
      decide
  have hvrec := hv.2
  rw [seed0] at hvrec
  have hurec := hu.2
  rw [seed13] at hurec
  have nest : 0 < PEqualNP.TopForm.andPairs 26 C := by
    by_contra! no
    have eq0 : PEqualNP.TopForm.andPairs 26 C = 0 := Nat.eq_zero_of_le_zero no
    have yes := flat_positive C 0 0 v hg spec eq0 (by decide) vi hvrec
    rw [hvo] at yes
    cases yes
  refine ⟨nest, ?_⟩
  by_contra! no
  have clean : cleanAnd C := by
    intro j hj op x hx
    cases h : C.eval (List.ofFn x) with
    | false => exact False.elim (no j hj op x hx h)
    | true => rfl
  have yes := clean_positive C 0 0 v u hs hg spec nest clean (by decide)
    ⟨hv.1, hvrec⟩ ⟨hu.1, hurec⟩
  rcases yes with yes | yes
  · rw [hvo] at yes
    cases yes
  · rw [huo] at yes
    cases yes

end PEqualNP.Outside.L_meta_2602

namespace PEqualNP.Outside.L_meta_2602_aux.Geometry

abbrev incident (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

lemma incident_self (p : Fin 13) : incident p p := Or.inl rfl

lemma point_degree : ∀ p : Fin 13,
    (Finset.univ.filter fun l => incident p l).card = 4 := by decide

lemma line_degree : ∀ l : Fin 13,
    (Finset.univ.filter fun p => incident p l).card = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma point_common_line : ∀ p q : Fin 13, p ≠ q →
    (Finset.univ.filter fun l => incident p l ∧ incident q l).card = 1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma line_common_point : ∀ l m : Fin 13, l ≠ m →
    (Finset.univ.filter fun p => incident p l ∧ incident p m).card = 1 := by decide

lemma edge_count :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => incident e.1 e.2).card = 52 := by
  decide

lemma face_edge_count :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 =>
      e.1 ≠ 0 ∧ e.2 ≠ 0 ∧ incident e.1 e.2).card = 45 := by decide

lemma face_matching_count : (Finset.univ.erase (0 : Fin 13)).card = 12 := by decide

lemma vertex_cover_bound (A B : Finset (Fin 13))
    (h : ∀ p l, incident p l → p ∈ A ∨ l ∈ B) : 13 ≤ A.card + B.card := by
  have hs : Finset.univ ⊆ A ∪ B := by
    intro p _
    exact Finset.mem_union.mpr (h p p (incident_self p))
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le A B)
  simpa using hc

lemma face_vertex_cover_bound (A B : Finset (Fin 13))
    (h : ∀ p l, p ≠ 0 → l ≠ 0 → incident p l → p ∈ A ∨ l ∈ B) :
    12 ≤ A.card + B.card := by
  have hs : Finset.univ.erase (0 : Fin 13) ⊆ A ∪ B := by
    intro p hp
    have hp0 := (Finset.mem_erase.mp hp).1
    exact Finset.mem_union.mpr (h p p hp0 hp0 (incident_self p))
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le A B)
  rwa [face_matching_count] at hc

lemma face_point_degree : ∀ p : Fin 13, p ≠ 0 →
    (Finset.univ.filter fun l => l ≠ 0 ∧ incident p l).card =
      if incident p 0 then 3 else 4 := by decide

lemma face_line_degree : ∀ l : Fin 13, l ≠ 0 →
    (Finset.univ.filter fun p => p ≠ 0 ∧ incident p l).card =
      if incident 0 l then 3 else 4 := by decide

lemma no_rectangle (p q l m : Fin 13) (hpq : p ≠ q)
    (hpl : incident p l) (hql : incident q l)
    (hpm : incident p m) (hqm : incident q m) : l = m := by
  have hc := point_common_line p q hpq
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hl : l ∈ ({a} : Finset (Fin 13)) := by
    rw [← ha]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpl, hql⟩
  have hm : m ∈ ({a} : Finset (Fin 13)) := by
    rw [← ha]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpm, hqm⟩
  exact (Finset.mem_singleton.mp hl).trans (Finset.mem_singleton.mp hm).symm

lemma deleted_neighbourhood_no_edge (p l : Fin 13) (hp : p ≠ 0) (hl : l ≠ 0)
    (hp0 : incident p 0) (h0l : incident 0 l) : ¬ incident p l := by
  intro hpl
  have e := no_rectangle p 0 0 l hp hp0 (incident_self 0) hpl h0l
  exact hl e.symm

end PEqualNP.Outside.L_meta_2602_aux.Geometry

namespace PEqualNP.Outside.L_meta_2602_aux.Transform

open PEqualNP.CircuitLowerBounds

def Proper (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j

def ValueRules (n : ℕ) (C : Circuit) (v : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → v (n + j) = (v a && v b)) ∧
    (g.op = .or → v (n + j) = (v a || v b))

def DerivativeRules (n : ℕ) (C : Circuit) (v d : ℕ → Bool) : Prop :=
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (n + j) = (v a && d b || d a && v b)) ∧
    (g.op = .or → d (n + j) = (d a || d b))

lemma and_mono {a b c d : Bool} (ha : a = true → c = true)
    (hb : b = true → d = true) : a && b = true → c && d = true := by
  intro h
  exact Bool.and_eq_true_iff.mpr ⟨ha (Bool.and_eq_true_iff.mp h).1,
    hb (Bool.and_eq_true_iff.mp h).2⟩

lemma or_mono {a b c d : Bool} (ha : a = true → c = true)
    (hb : b = true → d = true) : a || b = true → c || d = true := by
  intro h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Bool.or_eq_true_iff.mpr (Or.inl (ha h))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (hb h))

lemma product_mono {a b c d da db dc dd : Bool}
    (ha : a = true → c = true) (hb : b = true → d = true)
    (hda : da = true → dc = true) (hdb : db = true → dd = true) :
    (a && db || da && b) = true → (c && dd || dc && d) = true :=
  or_mono (and_mono ha hdb) (and_mono hda hb)

lemma substitution_monotone (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hs : ∀ r, sigma r < n + c)
    (v d w e : ℕ → Bool) (hv : ValueRules n C v) (hd : DerivativeRules n C v d)
    (hw : ValueRules n (PEqualNP.FactorSubst.substReads C n c sigma) w)
    (he : DerivativeRules n (PEqualNP.FactorSubst.substReads C n c sigma) w e)
    (hi : ∀ i < n, (w i = true → v i = true) ∧ (e i = true → d i = true))
    (hr : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs →
      (v (sigma j) = true → v (n + c) = true) ∧
        (d (sigma j) = true → d (n + c) = true)) :
    ∀ i < n + C.gates.length, (w i = true → v i = true) ∧
      (e i = true → d i = true) := by
  let D := PEqualNP.FactorSubst.substReads C n c sigma
  have len : D.gates.length = C.gates.length := by
    simp [D, PEqualNP.FactorSubst.substReads]
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hib
    by_cases hin : i < n
    · exact hi i hin
    obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    have hj : j < C.gates.length := by omega
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨hop, a, b, hab, ha, hb⟩ := hC j g hg
    let sub := fun k : ℕ => if k = n + c then sigma j else k
    let gg : Gate := ⟨g.op, g.inputs.map sub⟩
    have hgg : D.gates[j]? = some gg := by
      rw [List.getElem?_eq_getElem (by omega)]
      simp [D, PEqualNP.FactorSubst.substReads, gg, g, sub]
    have hggab : gg.inputs = [sub a, sub b] := by simp [gg, hab]
    have source (k : ℕ) (hk : k ∈ g.inputs) (hlt : k < n + j) :
        (w (sub k) = true → v k = true) ∧ (e (sub k) = true → d k = true) := by
      by_cases heq : k = n + c
      · subst k
        have hsig := hs j
        have hprev := ih (sigma j) (by omega) (by omega)
        have carry := hr j g hg hk
        simp only [sub, ite_eq_left rfl]
        exact ⟨fun h => carry.1 (hprev.1 h), fun h => carry.2 (hprev.2 h)⟩
      · simpa only [sub, ite_eq_right heq] using ih k hlt (by omega)
    have sa := source a (by simp [hab]) ha
    have sb := source b (by simp [hab]) hb
    have vr := hv j g a b hg hab
    have dr := hd j g a b hg hab
    have wr := hw j gg (sub a) (sub b) hgg hggab
    have er := he j gg (sub a) (sub b) hgg hggab
    rcases hop with hop | hop
    · have hop' : gg.op = .and := hop
      rw [vr.1 hop, dr.1 hop, wr.1 hop', er.1 hop']
      exact ⟨and_mono sa.1 sb.1, product_mono sa.1 sb.1 sa.2 sb.2⟩
    · have hop' : gg.op = .or := hop
      rw [vr.2 hop, dr.2 hop, wr.2 hop', er.2 hop']
      exact ⟨or_mono sa.1 sb.1, or_mono sa.2 sb.2⟩

lemma active_factor (n : ℕ) (C : Circuit) (v d : ℕ → Bool)
    (hv : ValueRules n C v) (hd : DerivativeRules n C v d)
    (c : ℕ) (g : Gate) (a b : ℕ) (hg : C.gates[c]? = some g)
    (hab : g.inputs = [a, b]) (hop : g.op = .and) (ha : v a = true) :
    (v b = true → v (n + c) = true) ∧ (d b = true → d (n + c) = true) := by
  rw [(hv c g a b hg hab).1 hop, (hd c g a b hg hab).1 hop, ha]
  constructor
  · intro h
    simpa only [Bool.true_and] using h
  · intro h
    simp [h]

lemma substitution_keeps_zero (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ)
    (hC : Proper n C) (hs : ∀ r, sigma r < n + c)
    (v d w e : ℕ → Bool) (hv : ValueRules n C v) (hd : DerivativeRules n C v d)
    (hw : ValueRules n (PEqualNP.FactorSubst.substReads C n c sigma) w)
    (he : DerivativeRules n (PEqualNP.FactorSubst.substReads C n c sigma) w e)
    (hi : ∀ i < n, (w i = true → v i = true) ∧ (e i = true → d i = true))
    (hr : ∀ j g, C.gates[j]? = some g → n + c ∈ g.inputs →
      (v (sigma j) = true → v (n + c) = true) ∧
        (d (sigma j) = true → d (n + c) = true))
    (ho : C.output < n + C.gates.length) (hz : d C.output = false) :
    e C.output = false := by
  have h := (substitution_monotone n C c sigma hC hs v d w e hv hd hw he hi hr C.output ho).2
  cases heq : e C.output with
  | false => rfl
  | true => have bad := h heq; rw [hz] at bad; cases bad

end PEqualNP.Outside.L_meta_2602_aux.Transform

namespace PEqualNP.Outside.L_meta_2602.Canonical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def input (a : Fin 13 → Bool) : Fin 26 → Bool :=
  @Fin.addCases 13 13 (fun _ => Bool) a (fun l => decide (∀ p : Fin 13,
    (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → a p = false))

lemma input_left (a : Fin 13 → Bool) (p : Fin 13) :
    input a (Fin.castAdd 13 p) = a p := by
  simp [input]

lemma input_right (a : Fin 13 → Bool) (l : Fin 13) :
    input a (Fin.natAdd 13 l) = true ↔ ∀ p : Fin 13, incidence p l → a p = false := by
  simp only [input, Fin.addCases_right, decide_eq_true_eq, incidence]

lemma input_false (C : Circuit) (hc : computes C) (a : Fin 13 → Bool) :
    C.eval (List.ofFn (input a)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨p, l, edge, hp, hl⟩ := (hc _).mp h
  rw [input_left] at hp
  have hf := (input_right a l).mp hl p edge
  rw [hp] at hf
  contradiction

lemma extends_false_input (C : Circuit) (hc : computes C) (x : Fin 26 → Bool)
    (hx : C.eval (List.ofFn x) = false) :
    ∀ i : Fin 26, x i = true → input (fun p => x (Fin.castAdd 13 p)) i = true := by
  intro i
  refine @Fin.addCases 13 13
    (fun i => x i = true → input (fun p => x (Fin.castAdd 13 p)) i = true)
    (fun p hp => ?_) (fun l hl => ?_) i
  · simpa only [input_left] using hp
  · apply (input_right _ l).mpr
    intro p edge
    apply Bool.eq_false_iff.mpr
    intro hp
    have ht := (hc x).mpr ⟨p, l, edge, hp, hl⟩
    rw [hx] at ht
    contradiction

lemma dirty_witness (C : Circuit) (hg : wellFormed C) (hc : computes C)
    (j : ℕ) (x : Fin 26 → Bool)
    (hgate : (C.wires (List.ofFn x)).getD (26 + j) false = true)
    (hout : C.eval (List.ofFn x) = false) :
    ∃ a : Fin 13 → Bool,
      (C.wires (List.ofFn (input a))).getD (26 + j) false = true ∧
        C.eval (List.ofFn (input a)) = false := by
  let a := fun p : Fin 13 => x (Fin.castAdd 13 p)
  refine ⟨a, ?_, input_false C hc a⟩
  have legal : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g mem
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨ops, u, v, ins, _⟩ := hg k g hk
    exact ⟨ops, by simp [ins]⟩
  exact CleanCase.val_mono C.gates legal x (input a)
    (extends_false_input C hc x hout) (26 + j) hgate

lemma counterexample_canonical_shape (C : Circuit) (hs : C.size ≤ 64)
    (hg : wellFormed C) (hc : computes C) (v u : ℕ → Bool)
    (hv : directional C 0 13 v) (hu : directional C 13 0 u)
    (hvo : v C.output = false) (huo : u C.output = false) :
    0 < PEqualNP.TopForm.andPairs 26 C ∧
      ∃ j < C.gates.length, (gateAt C j).op = .and ∧ ∃ a : Fin 13 → Bool,
        (C.wires (List.ofFn (input a))).getD (26 + j) false = true ∧
          C.eval (List.ofFn (input a)) = false := by
  obtain ⟨nest, j, hj, op, x, hgate, hout⟩ :=
    counterexample_shape C hs hg hc v u hv hu hvo huo
  exact ⟨nest, j, hj, op, dirty_witness C hg hc j x hgate hout⟩

end PEqualNP.Outside.L_meta_2602.Canonical

namespace PEqualNP.Outside.L_meta_2602_aux.Structural

open PEqualNP.Outside.L_meta_2602_aux.Geometry

def commonLines (A : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ A, incident p l

def guardedLines (A B : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ A, ∀ q ∈ B, incident p l ∨ incident q l

lemma guarded_lines_eq (A B : Finset (Fin 13)) :
    guardedLines A B = commonLines A ∪ commonLines B := by
  classical
  ext l
  simp only [guardedLines, commonLines, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    by_cases ha : ∀ p ∈ A, incident p l
    · exact Or.inl ha
    · right
      push_neg at ha
      obtain ⟨p, hp, hn⟩ := ha
      intro q hq
      exact (h p hp q hq).resolve_left (by simpa only [incident, not_or] using hn)
  · rintro (ha | hb) p hp q hq
    · exact Or.inl (ha p hp)
    · exact Or.inr (hb q hq)

lemma common_lines_card_le_one (A : Finset (Fin 13)) (hA : 2 ≤ A.card) :
    (commonLines A).card ≤ 1 := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  apply Finset.card_le_one.mpr
  intro l hl m hm
  have hl' : ∀ v ∈ A, incident v l := (Finset.mem_filter.mp hl).2
  have hm' : ∀ v ∈ A, incident v m := (Finset.mem_filter.mp hm).2
  exact no_rectangle p q l m hpq (hl' p hp) (hl' q hq) (hm' p hp) (hm' q hq)

lemma guarded_lines_card_le_two (A B : Finset (Fin 13))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    (guardedLines A B).card ≤ 2 := by
  rw [guarded_lines_eq]
  have h := Finset.card_union_le (commonLines A) (commonLines B)
  have ha := common_lines_card_le_one A hA
  have hb := common_lines_card_le_one B hB
  omega

end PEqualNP.Outside.L_meta_2602_aux.Structural

namespace PEqualNP.Outside.L_meta_2602_aux.Structural

open PEqualNP.Outside.L_meta_2602_aux.Geometry

def twoPointsOneLine (p q l : Fin 13) : Fin 26 → Bool :=
  @Fin.addCases 13 13 (fun _ => Bool)
    (fun r => decide (r = p ∨ r = q)) (fun s => decide (s = l))

lemma clean_flag_implies_guarded (A B : Finset (Fin 13)) (l : Fin 13)
    (h : ∀ x : Fin 26 → Bool,
      (∃ p ∈ A, x (Fin.castAdd 13 p) = true) →
      (∃ q ∈ B, x (Fin.castAdd 13 q) = true) → x (Fin.natAdd 13 l) = true →
      ∃ p q : Fin 13, incident p q ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 q) = true) : l ∈ guardedLines A B := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro p hp q hq
  have hleft : twoPointsOneLine p q l (Fin.castAdd 13 p) = true := by
    simp [twoPointsOneLine, Fin.addCases_left]
  have hright : twoPointsOneLine p q l (Fin.castAdd 13 q) = true := by
    simp [twoPointsOneLine, Fin.addCases_left]
  have hline : twoPointsOneLine p q l (Fin.natAdd 13 l) = true := by
    simp only [twoPointsOneLine, Fin.addCases_right, decide_eq_true_eq]
  obtain ⟨r, s, hrs, hr, hs⟩ := h (twoPointsOneLine p q l)
    ⟨p, hp, hleft⟩ ⟨q, hq, hright⟩ hline
  have hsl : s = l := of_decide_eq_true (by
    simpa only [twoPointsOneLine, Fin.addCases_right] using hs)
  have hrpq : r = p ∨ r = q := of_decide_eq_true (by
    simpa only [twoPointsOneLine, Fin.addCases_left] using hr)
  subst s
  rcases hrpq with rfl | rfl
  · exact Or.inl hrs
  · exact Or.inr hrs

lemma safe_factor_of_clean_flag (A B : Finset (Fin 13)) (l : Fin 13)
    (h : ∀ x : Fin 26 → Bool,
      (∃ p ∈ A, x (Fin.castAdd 13 p) = true) →
      (∃ q ∈ B, x (Fin.castAdd 13 q) = true) → x (Fin.natAdd 13 l) = true →
      ∃ p q : Fin 13, incident p q ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 q) = true) :
    (∀ p ∈ A, incident p l) ∨ ∀ q ∈ B, incident q l := by
  have hl := clean_flag_implies_guarded A B l h
  rw [guarded_lines_eq, Finset.mem_union] at hl
  exact hl.imp (fun h => (Finset.mem_filter.mp h).2)
    (fun h => (Finset.mem_filter.mp h).2)

end PEqualNP.Outside.L_meta_2602_aux.Structural

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

namespace PEqualNP.Outside.L_meta_2602_aux

open PEqualNP.CircuitLowerBounds

def tightCircuit : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [26, 27]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [30, 31]⟩,
    ⟨.and, [15, 32]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.and, [16, 36]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [7, 0]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.and, [17, 40]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [8, 1]⟩,
    ⟨.or, [42, 43]⟩,
    ⟨.and, [18, 44]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 2]⟩,
    ⟨.or, [46, 47]⟩,
    ⟨.and, [19, 48]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [50, 51]⟩,
    ⟨.and, [20, 52]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [54, 55]⟩,
    ⟨.and, [21, 56]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.or, [58, 59]⟩,
    ⟨.and, [22, 60]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [62, 63]⟩,
    ⟨.and, [23, 64]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [66, 67]⟩,
    ⟨.and, [24, 68]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [70, 71]⟩,
    ⟨.and, [25, 72]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [74, 37]⟩,
    ⟨.or, [75, 41]⟩,
    ⟨.or, [76, 45]⟩,
    ⟨.or, [77, 49]⟩,
    ⟨.or, [78, 53]⟩,
    ⟨.or, [79, 57]⟩,
    ⟨.or, [80, 61]⟩,
    ⟨.or, [81, 65]⟩,
    ⟨.or, [82, 69]⟩,
    ⟨.or, [83, 73]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [85, 86]⟩,
    ⟨.or, [84, 14]⟩,
    ⟨.or, [84, 87]⟩,
    ⟨.and, [88, 89]⟩
  ], 90⟩

def tightColumns : List (Fin 13) := [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1]

def tightStar (x : Fin 26 → Bool) (j : Fin 13) : Bool :=
  x (Fin.natAdd 13 j) &&
    ((x (Fin.castAdd 13 j) || x (Fin.castAdd 13 (j+1))) ||
      (x (Fin.castAdd 13 (j+3)) || x (Fin.castAdd 13 (j+9))))

def tightPlane (x : Fin 26 → Bool) : Bool :=
  (tightColumns.map (tightStar x)).any id

lemma tightSize : tightCircuit.size = 65 := rfl

lemma tightColumns_mem (j : Fin 13) : j ∈ tightColumns := by
  revert j
  decide

lemma tight_bool_eta (b : Bool) : Bool.rec false true b = b := by
  cases b <;> rfl

lemma tight_distrib (a b c : Bool) : ((a || b) && (a || c)) = (a || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tight_eval_formula (x : Fin 26 → Bool) :
  tightCircuit.eval (List.ofFn x) = ((((((((((((((x 13 && ((x 0 || x 1) || (x 3 || x 9))) || (x 15 && ((x 2 || x 3) || (x 5 || x 11)))) || (x 16 && ((x 3 || x 4) || (x 6 || x 12)))) || (x 17 && ((x 4 || x 5) || (x 7 || x 0)))) || (x 18 && ((x 5 || x 6) || (x 8 || x 1)))) || (x 19 && ((x 6 || x 7) || (x 9 || x 2)))) || (x 20 && ((x 7 || x 8) || (x 10 || x 3)))) || (x 21 && ((x 8 || x 9) || (x 11 || x 4)))) || (x 22 && ((x 9 || x 10) || (x 12 || x 5)))) || (x 23 && ((x 10 || x 11) || (x 0 || x 6)))) || (x 24 && ((x 11 || x 12) || (x 1 || x 7)))) || (x 25 && ((x 12 || x 0) || (x 2 || x 8)))) || x 14) && (((((((((((((x 13 && ((x 0 || x 1) || (x 3 || x 9))) || (x 15 && ((x 2 || x 3) || (x 5 || x 11)))) || (x 16 && ((x 3 || x 4) || (x 6 || x 12)))) || (x 17 && ((x 4 || x 5) || (x 7 || x 0)))) || (x 18 && ((x 5 || x 6) || (x 8 || x 1)))) || (x 19 && ((x 6 || x 7) || (x 9 || x 2)))) || (x 20 && ((x 7 || x 8) || (x 10 || x 3)))) || (x 21 && ((x 8 || x 9) || (x 11 || x 4)))) || (x 22 && ((x 9 || x 10) || (x 12 || x 5)))) || (x 23 && ((x 10 || x 11) || (x 0 || x 6)))) || (x 24 && ((x 11 || x 12) || (x 1 || x 7)))) || (x 25 && ((x 12 || x 0) || (x 2 || x 8)))) || ((x 1 || x 2) || (x 4 || x 10)))) := by
  cbv
  simp only [tight_bool_eta]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tight_eval_plane (x : Fin 26 → Bool) :
    tightCircuit.eval (List.ofFn x) = tightPlane x := by
  rw [tight_eval_formula, tight_distrib]
  simp only [tightPlane, tightColumns, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id_eq, tightStar, Bool.or_false, Bool.or_assoc]
  rfl

lemma tightPlane_spec (x : Fin 26 → Bool) : tightPlane x = true ↔
    ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  constructor
  · intro h
    obtain ⟨v, hv, hvtrue⟩ := List.any_eq_true.mp h
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    change tightStar x j = true at hvtrue
    simp only [tightStar, Bool.and_eq_true, Bool.or_eq_true] at hvtrue
    obtain ⟨hj, hp⟩ := hvtrue
    rcases hp with (h | h) | (h | h)
    · exact ⟨j, j, Or.inl rfl, h, hj⟩
    · exact ⟨j+1, j, Or.inr (Or.inl rfl), h, hj⟩
    · exact ⟨j+3, j, Or.inr (Or.inr (Or.inl rfl)), h, hj⟩
    · exact ⟨j+9, j, Or.inr (Or.inr (Or.inr rfl)), h, hj⟩
  · rintro ⟨p, l, hp, hx, hy⟩
    apply List.any_eq_true.mpr
    refine ⟨tightStar x l, List.mem_map.mpr ⟨l, tightColumns_mem l, rfl⟩, ?_⟩
    change tightStar x l = true
    simp only [tightStar, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨hy, ?_⟩
    rcases hp with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)

lemma tightCorrect (x : Fin 26 → Bool) : tightCircuit.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [tight_eval_plane]
  exact tightPlane_spec x

def tightTraceLeft (i : ℕ) : Bool := decide (i ∈ ([13, 29, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 88, 89] : List ℕ))

def tightTraceRight (i : ℕ) : Bool := decide (i ∈ ([0, 26, 28, 29, 39, 40, 63, 64, 70, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 88, 89] : List ℕ))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tight_wf_table : ∀ j : Fin tightCircuit.gates.length,
    let g := tightCircuit.gates[j.val]
    (g.op = .and ∨ g.op = .or) ∧
    g.inputs = [g.inputs.getD 0 0, g.inputs.getD 1 0] ∧
    g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 ∧
    g.inputs.getD 0 0 < 26+j.val ∧ g.inputs.getD 1 0 < 26+j.val := by
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decide

lemma tightProper : ∀ j g, tightCircuit.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
    g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j := by
  intro j g hg
  obtain ⟨hj, hval⟩ := List.getElem?_eq_some_iff.mp hg
  have h := tight_wf_table ⟨j,hj⟩
  dsimp only at h
  rw [hval] at h
  exact ⟨h.1, g.inputs.getD 0 0, g.inputs.getD 1 0, h.2⟩

def TightTrace (base target : ℕ) (d : ℕ → Bool) : Prop :=
  (∀ i < 26, d i = decide (i=target)) ∧
  (∀ j g a b, tightCircuit.gates[j]? = some g → g.inputs = [a,b] →
    (g.op = .and → d (26+j) =
      ((tightCircuit.wires (List.ofFn fun i : Fin 26 => decide (i.val=base))).getD a false && d b ||
      d a && (tightCircuit.wires (List.ofFn fun i : Fin 26 => decide (i.val=base))).getD b false)) ∧
    (g.op = .or → d (26+j) = (d a || d b))) ∧
  d tightCircuit.output = false

lemma tight_trace_of_table (base target : ℕ) (d : ℕ → Bool)
    (init : ∀ i : Fin 26, d i.val = decide (i.val=target))
    (step : ∀ j : Fin tightCircuit.gates.length,
      let g := tightCircuit.gates[j.val]
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = .and → d (26+j.val) =
        ((tightCircuit.wires (List.ofFn fun i : Fin 26 => decide (i.val=base))).getD a false && d b ||
        d a && (tightCircuit.wires (List.ofFn fun i : Fin 26 => decide (i.val=base))).getD b false)) ∧
      (g.op = .or → d (26+j.val) = (d a || d b)))
    (last : d tightCircuit.output = false) : TightTrace base target d := by
  refine ⟨fun i hi => init ⟨i,hi⟩, ?_, last⟩
  intro j g a b hg hab
  obtain ⟨hj, hval⟩ := List.getElem?_eq_some_iff.mp hg
  have h := step ⟨j,hj⟩
  dsimp only at h
  rw [hval, hab] at h
  simpa using h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tightTraceLeft_correct : TightTrace 0 13 tightTraceLeft := by
  apply tight_trace_of_table
  · decide
  · letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    decide
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma tightTraceRight_correct : TightTrace 13 0 tightTraceRight := by
  apply tight_trace_of_table
  · decide
  · letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    decide
  · decide

lemma tightness65 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (65 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  refine ⟨tightCircuit, ?_, ?_, tightProper, tightCorrect, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨tightTraceLeft, tightTraceLeft_correct⟩
  · exact ⟨tightTraceRight, tightTraceRight_correct⟩

end PEqualNP.Outside.L_meta_2602_aux

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

namespace PEqualNP.Outside.L_meta_2602_aux.Normalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Derivative Clamp ClampSemantic

lemma minimum_obstruction (C : Circuit) (hs : C.size ≤ 64)
    (hC : Proper 26 C) (hF : PlaneSpec C) (hZ : MarkedZero C) :
    ∃ D : Circuit, Proper 26 D ∧ PlaneSpec D ∧ MarkedZero D ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, Proper 26 E → PlaneSpec E → MarkedZero E → D.size ≤ E.size) ∧
      AllActive D ∧ 0 < PEqualNP.TopForm.andPairs 26 D ∧
      ∃ j < D.gates.length, (gateAt D j).op = .and ∧ ∃ x : Fin 26 → Bool,
        (D.wires (List.ofFn x)).getD (26 + j) false = true ∧
          D.eval (List.ofFn x) = false := by
  obtain ⟨D, hD, hDF, hDZ, hsize, hmin, hactive⟩ := minimum_all_active C hC hF hZ
  obtain ⟨d, hinit, hd, hz⟩ := hDZ
  have hleft : PEqualNP.Outside.L_meta_2602.directional D 0 13 (d 0) := by
    constructor
    · simpa [markedInitial] using hinit (0 : Fin 2)
    · simpa [DerivativeRules, WireValue, markedBase] using hd (0 : Fin 2)
  have hright : PEqualNP.Outside.L_meta_2602.directional D 13 0 (d 1) := by
    constructor
    · simpa [markedInitial] using hinit (1 : Fin 2)
    · simpa [DerivativeRules, WireValue, markedBase] using hd (1 : Fin 2)
  have shape := PEqualNP.Outside.L_meta_2602.counterexample_shape D
    (hsize.trans hs) hD hDF (d 0) (d 1) hleft hright (hz 0) (hz 1)
  exact ⟨D, hD, hDF, ⟨d, hinit, hd, hz⟩, hsize, hmin, hactive, shape⟩

end PEqualNP.Outside.L_meta_2602_aux.Normalized
