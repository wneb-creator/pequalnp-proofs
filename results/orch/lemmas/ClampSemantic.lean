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
