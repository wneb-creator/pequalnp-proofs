import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Endpoints

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

end PEqualNP.Outside.L_meta_2592_aux.Endpoints
