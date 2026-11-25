import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.PrimeReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire monotonicity infrastructure adapted from the checked L_meta_610 proof.
def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk


lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma append_signal_le (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases he : i = w.length
  · subst i
    rw [getD_append_last_eq w a _ rfl] at hi
    rw [getD_append_last_eq v b _ hlen.symm]
    exact hab hi
  · rw [getD_snoc_ne _ _ _ he] at hi
    rw [getD_snoc_ne _ _ _ (by omega)]
    exact h i hi

def MonoFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def edgeInput {n : ℕ} (e : Fin n × Fin n) : Fin n → Bool :=
  fun i => decide (i = e.1 ∨ i = e.2)

def edgeValue {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)

lemma edgeInput_le {n : ℕ} (e : Fin n × Fin n) (x : Fin n → Bool)
    (ha : x e.1 = true) (hb : x e.2 = true) :
    ∀ i, edgeInput e i = true → x i = true := by
  intro i hi
  have h : i = e.1 ∨ i = e.2 := of_decide_eq_true hi
  rcases h with rfl | rfl
  · exact ha
  · exact hb

lemma edgeValue_pair {n : ℕ} (E : Finset (Fin n × Fin n)) (e : Fin n × Fin n)
    (he : e ∈ E) : edgeValue E (edgeInput e) = true := by
  apply decide_eq_true
  exact ⟨e, he, by simp [edgeInput], by simp [edgeInput]⟩

lemma lowered_eq_on_edges {n : ℕ} (E : Finset (Fin n × Fin n))
    (f : (Fin n → Bool) → Bool) (mono : MonoFn f)
    (below : ∀ x, f x = true → edgeValue E x = true)
    (edges : ∀ e ∈ E, f (edgeInput e) = true) :
    ∀ x, f x = edgeValue E x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact below x
  · intro hx
    obtain ⟨e, he, ha, hb⟩ := of_decide_eq_true hx
    exact mono (edgeInput e) x (edgeInput_le e x ha hb) (edges e he)

lemma input_list_le {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hil : i < n
  · rw [getD_ofFn x i hil] at hi
    rw [getD_ofFn y i hil]
    exact h ⟨i, hil⟩ hi
  · rw [getD_ge_length _ _ (by simp; omega)] at hi
    cases hi

def replacedValue {n : ℕ} (A B : List Gate) (r : (Fin n → Bool) → Bool) (o : ℕ)
    (x : Fin n → Bool) : Bool :=
  (B.foldl wiresStep (A.foldl wiresStep (List.ofFn x) ++ [r x])).getD o false

lemma replaced_mono {n : ℕ} (A B : List Gate)
    (hA : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r) (o : ℕ) :
    MonoFn (replacedValue A B r o) := by
  intro x y hxy
  apply monotone_foldl_wiresStep B hB _ _
    (by simp [foldl_wiresStep_length])
  apply append_signal_le _ _ _ _ (by simp [foldl_wiresStep_length])
  · exact monotone_foldl_wiresStep A hA _ _ (by simp) (input_list_le x y hxy)
  · exact hr x y hxy

-- A lower monotone replacement that agrees on every accepted edge preserves the whole function.
theorem lower_wire_preserves {n : ℕ} (E : Finset (Fin n × Fin n))
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hA : ∀ t ∈ A, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ t ∈ B, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r)
    (below : ∀ x, r x = true →
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn x)).getD i false) = true)
    (same : ∀ e ∈ E, r (edgeInput e) =
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false))
    (computes : ∀ x : Fin n → Bool, Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x) :
    ∀ x, replacedValue A B r o x = edgeValue E x := by
  apply lowered_eq_on_edges E _ (replaced_mono A B hA hB r hr o)
  · intro x hx
    have hle := monotone_foldl_wiresStep B hB
      (A.foldl wiresStep (List.ofFn x) ++ [r x])
      (wiresStep (A.foldl wiresStep (List.ofFn x)) g)
      (by simp [wiresStep])
      (append_signal_le _ _ _ _ rfl (fun _ h => h) (below x)) o hx
    have horig : (B.foldl wiresStep (wiresStep (A.foldl wiresStep (List.ofFn x)) g)).getD o false
        = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes x] at hle
    exact hle
  · intro e he
    rw [replacedValue, same e he]
    have horig :
        (B.foldl wiresStep (A.foldl wiresStep (List.ofFn (edgeInput e)) ++
          [g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false)])).getD o false
          = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn (edgeInput e)) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes]
    exact edgeValue_pair E e he

end PEqualNP.Outside.L_meta_2583_aux.PrimeReplacement
