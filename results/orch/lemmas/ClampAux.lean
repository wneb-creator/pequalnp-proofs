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
