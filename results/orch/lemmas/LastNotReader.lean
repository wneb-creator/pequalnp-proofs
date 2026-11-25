import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W {n : ℕ} (gates : List Gate) (t : ℕ) (x : Fin n → Bool) : List Bool :=
  Circuit.wires ⟨gates.take t, 0⟩ (List.ofFn x)

theorem W_zero {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : W gates 0 x = List.ofFn x := by
  simp [W, Circuit.wires]

theorem W_succ {n : ℕ} (gates : List Gate) (t : ℕ) (ht : t < gates.length)
    (x : Fin n → Bool) :
    W gates (t + 1) x = W gates t x ++
      [gates[t].op.eval (gates[t].inputs.map fun k => (W gates t x).getD k false)] := by
  unfold W Circuit.wires
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_length {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    ∀ t : ℕ, t ≤ gates.length → (W gates t x).length = n + t := by
  intro t
  induction t with
  | zero => intro _; simp [W_zero]
  | succ t ih =>
    intro ht
    rw [W_succ gates t (by omega), List.length_append, ih (by omega)]
    simp
    omega

theorem W_prefix {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (t : ℕ) :
    ∀ u : ℕ, t + u ≤ gates.length → W gates t x <+: W gates (t + u) x := by
  intro u
  induction u with
  | zero => intro _; exact List.prefix_refl _
  | succ u ih =>
    intro h
    rw [← Nat.add_assoc, W_succ gates (t + u) (by omega)]
    exact (ih (by omega)).trans (List.prefix_append _ _)

theorem getD_of_prefix {l1 l2 : List Bool} (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l1.getD i false = l2.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem all_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).all id = true → (ks.map g).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id]
  rintro h b ⟨k, hk, rfl⟩
  exact hfg k (h (f k) ⟨k, hk, rfl⟩)

theorem any_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).any id = true → (ks.map g).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id]
  rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
  exact ⟨g k, ⟨k, hk, rfl⟩, hfg k hb⟩

theorem W_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ t : ℕ, t ≤ gates.length →
      ∀ k, (W gates t x).getD k false = true → (W gates t y).getD k false = true := by
  intro t
  induction t with
  | zero =>
    intro _ k hk
    rw [W_zero, ofFn_getD] at hk ⊢
    split_ifs at hk ⊢ with h
    exact hxy _ hk
  | succ t ih =>
    intro ht k hk
    have htl : t < gates.length := by omega
    have ih' := ih (by omega)
    rw [W_succ gates t htl, getD_snoc] at hk ⊢
    rw [W_length gates x t (by omega)] at hk
    rw [W_length gates y t (by omega)]
    split_ifs at hk ⊢ with h1 h2
    · exact ih' k hk
    · rcases hops _ (List.getElem_mem htl) with hop | hop
      · rw [hop] at hk ⊢
        exact all_mono _ _ _ ih' hk
      · rw [hop] at hk ⊢
        exact any_mono _ _ _ ih' hk

theorem eval_eq {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = (W gates gates.length x).getD w false := by
  simp [Circuit.eval, W, Circuit.wires]

theorem eval_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  rw [eval_eq, eval_eq]
  exact W_mono gates hops x y hxy gates.length le_rfl w


lemma snoc_not_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates ++ [⟨GateOp.not, [C.output]⟩], n + C.size⟩ (List.ofFn x) =
      !C.eval (List.ofFn x) := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  change (C.wires (List.ofFn x) ++ [!C.eval (List.ofFn x)]).getD (n + C.size) false = _
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    simpa [W, Circuit.wires, Circuit.size] using W_length C.gates x C.gates.length le_rfl
  rw [getD_snoc, hlen]
  simp only [Nat.lt_irrefl, ite_false, ite_true]
  rfl

lemma terminal_not_impossible {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (zero : f (fun _ => false) = false)
    (one : f (fun _ => true) = true) :
    ¬∀ x : Fin n → Bool,
      Circuit.eval ⟨C.gates ++ [⟨GateOp.not, [C.output]⟩], n + C.size⟩ (List.ofFn x) = f x := by
  intro correct
  have hz := correct (fun _ => false)
  have ho := correct (fun _ => true)
  rw [snoc_not_eval, zero] at hz
  rw [snoc_not_eval, one] at ho
  have hz' : C.eval (List.ofFn fun _ : Fin n => false) = true := by
    cases h : C.eval (List.ofFn fun _ : Fin n => false) <;> simp_all
  have ho' : C.eval (List.ofFn fun _ : Fin n => true) = false := by
    cases h : C.eval (List.ofFn fun _ : Fin n => true) <;> simp_all
  have hmono := eval_mono C.gates (fun g hg => by
    have hop := (mono g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop)
    (fun _ : Fin n => false) (fun _ => true) (by simp) C.output hz'
  change C.eval (List.ofFn fun _ : Fin n => true) = true at hmono
  exact Bool.false_ne_true (ho'.symm.trans hmono)


def gateAt (gates : List Gate) (t : ℕ) : Gate := gates.getD t ⟨GateOp.or, []⟩

lemma gateAt_get (gates : List Gate) (t : ℕ) (ht : t < gates.length) :
    gateAt gates t = gates[t] := by
  simp [gateAt, List.getD_eq_getElem?_getD, ht]

lemma W_succ_gate {n : ℕ} (gates : List Gate) (t : ℕ) (ht : t < gates.length)
    (x : Fin n → Bool) :
    W gates (t + 1) x = W gates t x ++
      [(gateAt gates t).op.eval ((gateAt gates t).inputs.map fun k =>
        (W gates t x).getD k false)] := by
  rw [W_succ gates t ht, gateAt_get gates t ht]

lemma W_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t ≤ gates.length) (i : Fin n) :
    (W gates t x).getD i.val false = x i := by
  have h := getD_of_prefix (W_prefix gates x 0 t (by simpa using ht)) i.val
    (by simpa [W_zero] using i.isLt)
  simpa [W_zero, ofFn_getD, i.isLt] using h.symm

lemma all_mono_on (ks : List ℕ) (f g : ℕ → Bool)
    (hfg : ∀ k ∈ ks, f k = true → g k = true) :
    (ks.map f).all id = true → (ks.map g).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id]
  rintro h b ⟨k, hk, rfl⟩
  exact hfg k hk (h (f k) ⟨k, hk, rfl⟩)

lemma any_mono_on (ks : List ℕ) (f g : ℕ → Bool)
    (hfg : ∀ k ∈ ks, f k = true → g k = true) :
    (ks.map f).any id = true → (ks.map g).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id]
  rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
  exact ⟨g k, ⟨k, hk, rfl⟩, hfg k hk hb⟩

lemma not_flip (a b : Bool) (h : a = true → b = true) :
    !b = true → !a = true := by
  cases a <;> cases b <;> simp_all

lemma W_before_eq {n : ℕ} (gates : List Gate) (q : ℕ) (hq : q < gates.length)
    (i : Fin n) (avoid : ∀ t, t < q → i.val ∉ (gateAt gates t).inputs)
    (x y : Fin n → Bool) (same : ∀ j, j ≠ i → x j = y j) :
    ∀ t, t ≤ q → ∀ k, k ≠ i.val →
      (W gates t x).getD k false = (W gates t y).getD k false := by
  intro t
  induction t with
  | zero =>
    intro ht k hki
    rw [W_zero, W_zero, ofFn_getD, ofFn_getD]
    split_ifs with hk
    · exact same ⟨k, hk⟩ (fun e => hki (congrArg Fin.val e))
    · rfl
  | succ t ih =>
    intro ht k hki
    have htl : t < gates.length := by omega
    have ih' := ih (by omega)
    rw [W_succ_gate gates t htl, W_succ_gate gates t htl,
      getD_snoc, getD_snoc, W_length gates x t (by omega),
      W_length gates y t (by omega)]
    split_ifs with hk hke
    · exact ih' k hki
    · congr 1
      apply List.map_congr_left
      intro j hj
      exact ih' j (fun e => avoid t (by omega) (e ▸ hj))
    · rfl

lemma last_not_reader_reverse {n : ℕ} (gates : List Gate) (q : ℕ)
    (hq : q < gates.length) (qnot : (gateAt gates q).op = GateOp.not)
    (i : Fin n)
    (others : ∀ t, t < gates.length → t ≠ q →
      (q < t → (gateAt gates t).op = GateOp.and ∨ (gateAt gates t).op = GateOp.or) ∧
      i.val ∉ (gateAt gates t).inputs)
    (x y : Fin n → Bool) (same : ∀ j, j ≠ i → x j = y j)
    (xy : x i = true → y i = true) (out : ℕ) (out_ne : out ≠ i.val) :
    Circuit.eval ⟨gates, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨gates, out⟩ (List.ofFn x) = true := by
  have pre := W_before_eq gates q hq i
    (fun t ht => (others t (by omega) (by omega)).2) x y same
  have increasing (k : ℕ) : (W gates q x).getD k false = true →
      (W gates q y).getD k false = true := by
    by_cases hk : k = i.val
    · subst k
      simpa only [W_input gates x q hq.le i, W_input gates y q hq.le i] using xy
    · rw [pre q le_rfl k hk]
      exact id
  have flip :
      (gateAt gates q).op.eval ((gateAt gates q).inputs.map fun k =>
        (W gates q y).getD k false) = true →
      (gateAt gates q).op.eval ((gateAt gates q).inputs.map fun k =>
        (W gates q x).getD k false) = true := by
    rw [qnot]
    cases h : (gateAt gates q).inputs with
    | nil => simp [h, GateOp.eval]
    | cons k ks =>
      simpa [h, GateOp.eval] using not_flip _ _ (increasing k)
  have base : ∀ k, k ≠ i.val → (W gates (q + 1) y).getD k false = true →
      (W gates (q + 1) x).getD k false = true := by
    intro k hki hk
    rw [W_succ_gate gates q hq, getD_snoc, W_length gates y q hq.le] at hk
    rw [W_succ_gate gates q hq, getD_snoc, W_length gates x q hq.le]
    split_ifs at hk ⊢ with h1 h2
    · rwa [pre q le_rfl k hki]
    · exact flip hk
  have after : ∀ s, q + 1 + s ≤ gates.length → ∀ k, k ≠ i.val →
      (W gates (q + 1 + s) y).getD k false = true →
      (W gates (q + 1 + s) x).getD k false = true := by
    intro s
    induction s with
    | zero => intro _; exact base
    | succ s ih =>
      intro hs k hki hk
      have ht : q + 1 + s < gates.length := by omega
      have ih' := ih (by omega)
      have hop := others (q + 1 + s) ht (by omega)
      rw [← Nat.add_assoc, W_succ_gate gates (q + 1 + s) ht,
        getD_snoc, W_length gates y (q + 1 + s) (by omega)] at hk
      rw [← Nat.add_assoc, W_succ_gate gates (q + 1 + s) ht,
        getD_snoc, W_length gates x (q + 1 + s) (by omega)]
      split_ifs at hk ⊢ with h1 h2
      · exact ih' k hki hk
      · have reads : ∀ j ∈ (gateAt gates (q + 1 + s)).inputs,
            (W gates (q + 1 + s) y).getD j false = true →
            (W gates (q + 1 + s) x).getD j false = true := by
          intro j hj
          exact ih' j (fun e => hop.2 (e ▸ hj))
        rcases hop.1 (by omega) with ha | ho
        · rw [ha] at hk ⊢
          exact all_mono_on _ _ _ reads hk
        · rw [ho] at hk ⊢
          exact any_mono_on _ _ _ reads hk
  rw [eval_eq, eval_eq]
  have finish := after (gates.length - (q + 1)) (by omega) out out_ne
  have length : q + 1 + (gates.length - (q + 1)) = gates.length := by omega
  simpa only [length] using finish


def petersenF (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ([1, 0, 1, 2, 0, 0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0

def lowInput (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = neighbor i)
def highInput (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i ∨ j = neighbor i)

lemma petersen_witness : ∀ i : Fin 10,
    petersenF (lowInput i) = false ∧ petersenF (highInput i) = true ∧
    (∀ j, j ≠ i → lowInput i j = highInput i j) ∧
    (lowInput i i = true → highInput i i = true) := by
  decide +kernel

lemma petersen_singleton : ∀ i : Fin 10,
    petersenF (fun j => decide (j = i)) = false := by
  decide +kernel

lemma petersen_last_not_only_reader (gates : List Gate) (q : ℕ)
    (hq : q < gates.length) (qnot : (gateAt gates q).op = GateOp.not)
    (i : Fin 10)
    (others : ∀ t, t < gates.length → t ≠ q →
      (q < t → (gateAt gates t).op = GateOp.and ∨ (gateAt gates t).op = GateOp.or) ∧
      i.val ∉ (gateAt gates t).inputs)
    (out : ℕ) :
    ¬ ∀ x : Fin 10 → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = petersenF x := by
  intro correct
  have out_ne : out ≠ i.val := by
    intro equal
    have h := correct (fun j => decide (j = i))
    rw [eval_eq, equal, W_input gates _ gates.length le_rfl i, petersen_singleton] at h
    simp at h
  have witness := petersen_witness i
  have reverse := last_not_reader_reverse gates q hq qnot i others
    (lowInput i) (highInput i) witness.2.2.1 witness.2.2.2 out out_ne
    (by rw [correct, witness.2.1])
  rw [correct, witness.1] at reverse
  contradiction

end PEqualNP.Outside.L_meta_2592_aux.OneNotInput
