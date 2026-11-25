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
