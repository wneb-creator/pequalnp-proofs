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

def advance (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]

def run (gates : List Gate) (xs : List Bool) : List Bool :=
  gates.foldl advance xs

lemma append_value_mono (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true)
    (a b : Bool) (hab : a = true → b = true) :
    ∀ k, (xs ++ [a]).getD k false = true → (ys ++ [b]).getD k false = true := by
  intro k hk
  rw [getD_snoc, hlen] at hk
  rw [getD_snoc]
  split_ifs at hk ⊢ with h1 h2
  · exact hxy k hk
  · exact hab hk

lemma advance_mono (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ k, (advance xs g).getD k false = true → (advance ys g).getD k false = true := by
  apply append_value_mono xs ys hlen hxy
  rcases hop with ha | ho
  · rw [ha]
    exact all_mono _ _ _ hxy
  · rw [ho]
    exact any_mono _ _ _ hxy

lemma run_mono (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hxy : ∀ k, xs.getD k false = true → ys.getD k false = true) :
    ∀ k, (run gates xs).getD k false = true → (run gates ys).getD k false = true := by
  induction gates generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    have hop := hops g (by simp)
    have tail : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact hops h (by simp [hh])
    exact ih tail (advance xs g) (advance ys g)
      (by simp [advance, hlen]) (advance_mono xs ys hlen hxy g hop)

lemma eval_split (pre post : List Gate) (g : Gate) (out : ℕ) (xs : List Bool) :
    Circuit.eval ⟨pre ++ g :: post, out⟩ xs =
      (run post (advance (run pre xs) g)).getD out false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  rfl

lemma run_input {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (i : Fin n) :
    (run pre (List.ofFn x)).getD i.val false = x i := by
  change (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i.val false = x i
  simpa only [W, List.take_length] using W_input pre x pre.length le_rfl i

lemma bypass_nand_mask {n : ℕ} (pre post : List Gate) (i : Fin n)
    (wire out : ℕ) (edge f : (Fin n → Bool) → Bool)
    (post_mono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (mask : ∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD wire false = !(edge x))
    (edge_sound : ∀ x : Fin n → Bool, edge x = true → f x = true)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, [i.val, wire]⟩ :: post, out⟩ (List.ofFn x) = f x) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, [i.val]⟩ :: post, out⟩ (List.ofFn x) = f x := by
  intro x
  have old := correct x
  rw [eval_split] at old
  rw [eval_split]
  have old_start : advance (run pre (List.ofFn x)) ⟨GateOp.and, [i.val, wire]⟩ =
      run pre (List.ofFn x) ++ [x i && !(edge x)] := by
    change _ ++ [GateOp.and.eval [(run pre (List.ofFn x)).getD i.val false,
      (run pre (List.ofFn x)).getD wire false]] = _
    rw [run_input pre x i, mask x]
    simp [GateOp.eval]
  have new_start : advance (run pre (List.ofFn x)) ⟨GateOp.or, [i.val]⟩ =
      run pre (List.ofFn x) ++ [x i] := by
    change _ ++ [GateOp.or.eval [(run pre (List.ofFn x)).getD i.val false]] = _
    rw [run_input pre x i]
    simp [GateOp.eval]
  rw [old_start] at old
  rw [new_start]
  cases he : edge x with
  | false => simpa [he] using old
  | true =>
    have target := edge_sound x he
    rw [target] at old ⊢
    exact run_mono post post_mono _ _ (by simp)
      (append_value_mono _ _ rfl (fun _ => id) _ _ (by
        cases hx : x i <;> simp [hx])) out old


lemma run_prefix (gates : List Gate) (xs : List Bool) : xs <+: run gates xs := by
  induction gates generalizing xs with
  | nil => exact List.prefix_refl _
  | cons g gs ih =>
    exact (List.prefix_append xs _).trans (ih (advance xs g))

lemma snoc_or_eval {n : ℕ} (C : Circuit) (wire : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates ++ [⟨GateOp.or, [C.output, wire]⟩], n + C.size⟩
      (List.ofFn x) = (C.eval (List.ofFn x) || (C.wires (List.ofFn x)).getD wire false) := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (C.wires (List.ofFn x) ++
    [GateOp.or.eval [(C.wires (List.ofFn x)).getD C.output false,
      (C.wires (List.ofFn x)).getD wire false]]).getD (n + C.size) false = _
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    simpa [W, Circuit.wires, Circuit.size] using W_length C.gates x C.gates.length le_rfl
  rw [getD_snoc, hlen]
  simp only [Nat.lt_irrefl, ite_false, ite_true]
  change GateOp.or.eval [(C.wires (List.ofFn x)).getD C.output false,
    (C.wires (List.ofFn x)).getD wire false] =
      ((C.wires (List.ofFn x)).getD C.output false ||
        (C.wires (List.ofFn x)).getD wire false)
  simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]

lemma move_or_mask_to_output {n : ℕ} (pre post : List Gate) (i : Fin n)
    (wire out : ℕ) (wire_back : wire < n + pre.length)
    (edge f : (Fin n → Bool) → Bool)
    (mask : ∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD wire false = edge x)
    (edge_sound : ∀ x : Fin n → Bool, edge x = true → f x = true)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post, out⟩ (List.ofFn x) = f x) :
    let copied : Circuit := ⟨pre ++ ⟨GateOp.or, [i.val]⟩ :: post, out⟩
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨copied.gates ++ [⟨GateOp.or, [copied.output, wire]⟩], n + copied.size⟩
        (List.ofFn x) = f x := by
  dsimp only
  intro x
  rw [snoc_or_eval (C := ⟨pre ++ ⟨GateOp.or, [i.val]⟩ :: post, out⟩) wire x]
  have wire_eq :
      (Circuit.wires ⟨pre ++ ⟨GateOp.or, [i.val]⟩ :: post, out⟩ (List.ofFn x)).getD wire false =
        edge x := by
    have hp := run_prefix (⟨GateOp.or, [i.val]⟩ :: post) (run pre (List.ofFn x))
    have hlen : (run pre (List.ofFn x)).length = n + pre.length := by
      change (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).length = n + pre.length
      simpa only [W, List.take_length] using W_length pre x pre.length le_rfl
    have hv := getD_of_prefix hp wire (by rw [hlen]; exact wire_back)
    change (run (pre ++ ⟨GateOp.or, [i.val]⟩ :: post) (List.ofFn x)).getD wire false = _
    rw [run, List.foldl_append]
    exact hv.symm.trans (mask x)
  rw [wire_eq]
  cases he : edge x with
  | true => simp [edge_sound x he]
  | false =>
    simp only [Bool.or_false]
    have old := correct x
    rw [eval_split] at old ⊢
    have old_start : advance (run pre (List.ofFn x)) ⟨GateOp.or, [i.val, wire]⟩ =
        run pre (List.ofFn x) ++ [x i] := by
      change _ ++ [GateOp.or.eval [(run pre (List.ofFn x)).getD i.val false,
        (run pre (List.ofFn x)).getD wire false]] = _
      rw [run_input pre x i, mask x, he]
      simp [GateOp.eval]
    have new_start : advance (run pre (List.ofFn x)) ⟨GateOp.or, [i.val]⟩ =
        run pre (List.ofFn x) ++ [x i] := by
      change _ ++ [GateOp.or.eval [(run pre (List.ofFn x)).getD i.val false]] = _
      rw [run_input pre x i]
      simp [GateOp.eval]
    rw [old_start] at old
    rwa [new_start]

end PEqualNP.Outside.L_meta_2592_aux.OneNotInput
