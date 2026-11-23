import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951.Deletion

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

/-- `Circuit.wires` is the fold `wiresFrom`. -/
lemma on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

/-- The wire list has one wire per input bit and one per gate. -/
lemma on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

/-- Reading at or beyond the length gives `false`. -/
lemma on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

/-- The same for `wiresFrom`. -/
lemma on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

/-- The wires of `l1 ++ l2`: run `l2` on the wires of `l1`. -/
lemma on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

/-- One gate on a wire list: the old wires, then the gate's value. -/
lemma on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

/-- Input wire `i < n` of `List.ofFn x` reads `x i`, whatever the gates. -/
lemma on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

/-- The wire a gate reads in a list `w`, read through a list that extends `w`. -/
lemma on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

lemma on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

/-- The generic simulation, with the invariant on every index. -/
lemma on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

/-- The generic simulation: it is enough that `r` is right on the start wires. -/
lemma on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

def deleteMap (p a : ℕ) (i : ℕ) : ℕ :=
  if i < p then i else if i = p then a else i - 1

lemma delete_alias (n : ℕ) (pre post : List Gate) (g : Gate) (a : ℕ)
    (ha : a < n + pre.length ∨ n + pre.length + post.length ≤ a)
    (o : ℕ) (x : Fin n → Bool)
    (hval : g.op.eval (g.inputs.map fun i =>
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false) =
      (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false) :
    Circuit.eval
      ⟨pre ++ post.map (on1_relabel (deleteMap (n + pre.length) a)),
        deleteMap (n + pre.length) a o⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  set p := n + pre.length with hp
  set r := deleteMap p a with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = p := by rw [hv, length_wiresFrom]; simp [hp]
  set gv := g.op.eval (g.inputs.map fun i => v.getD i false) with hgv
  have hgv' : gv = v.getD a false := hval
  unfold Circuit.eval
  rw [on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0, on1_wiresFrom_cons]
  change (wiresFrom (post.map (on1_relabel r)) v).getD (r o) false =
    (wiresFrom post (v ++ [gv])).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi
    by_cases hlt : i < p
    · simp only [hr, deleteMap, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hi' : i = p := by omega
      subst i
      simp only [hr, deleteMap, lt_irrefl, ite_false, ite_true]
      rw [← hvl, getD_snoc_eq, hgv']
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < p
    · left
      simp [hr, deleteMap, hlt]
    · have hi' : i = p := by omega
      subst i
      simpa [hr, deleteMap, hp] using ha
  · intro k _
    simp only [List.length_append, List.length_singleton, hvl, hr, deleteMap]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr, deleteMap]
    split_ifs <;> omega

lemma delete_false (n : ℕ) (pre post : List Gate) (g : Gate)
    (o : ℕ) (x : Fin n → Bool)
    (hval : g.op.eval (g.inputs.map fun i =>
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false) = false) :
    Circuit.eval
      ⟨pre ++ post.map (on1_relabel
          (deleteMap (n + pre.length) (n + pre.length + post.length))),
        deleteMap (n + pre.length) (n + pre.length + post.length) o⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  apply delete_alias n pre post g _ (Or.inr (le_refl _)) o x
  rw [hval]
  symm
  apply on1_getD_wires_of_ge
  simp

lemma delete_length (n : ℕ) (pre post : List Gate) (g : Gate) (a : ℕ) :
    (pre ++ post.map (on1_relabel (deleteMap (n + pre.length) a))).length + 1 =
      (pre ++ g :: post).length := by simp; omega

lemma delete_allowed (pre post : List Gate) (g : Gate) (r : ℕ → ℕ)
    (hops : ∀ h ∈ pre ++ g :: post,
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2) :
    ∀ h ∈ pre ++ post.map (on1_relabel r),
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
        h.inputs.length ≤ 2 := by
  intro h hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hops h (List.mem_append_left _ hh)
  · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
    have hs := hops h' (List.mem_append_right _ (List.mem_cons_of_mem _ hh'))
    simpa [on1_relabel] using hs

lemma positive_zero_alias (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (hins : ins.length ≤ 2) (v : ℕ) (hv : v ∈ ins) :
    ∃ a : Option ℕ, ∀ f : ℕ → Bool, f v = false →
      op.eval (ins.map f) = match a with | none => false | some j => f j := by
  rcases hop with rfl | rfl
  · refine ⟨none, ?_⟩
    intro f hf
    change (ins.map f).all id = false
    cases he : (ins.map f).all id with
    | false => rfl
    | true =>
      have hh := List.all_eq_true.mp he (f v) (List.mem_map.mpr ⟨v,hv,rfl⟩)
      simp [hf] at hh
  · cases ins with
    | nil => simp at hv
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [List.mem_singleton] at hv
        subst v
        refine ⟨none, ?_⟩
        intro f hf
        simp [GateOp.eval, hf]
      | cons b tail =>
        have htail : tail = [] := by
          apply List.length_eq_zero_iff.mp
          have hh : tail.length + 1 + 1 ≤ 2 := hins
          omega
        subst tail
        rcases List.mem_cons.mp hv with hva | hvb
        · subst v
          refine ⟨some b, ?_⟩
          intro f hf
          simp [GateOp.eval, hf]
        · simp only [List.mem_singleton] at hvb
          subst v
          refine ⟨some a, ?_⟩
          intro f hf
          simp [GateOp.eval, hf]

lemma direct_zero_alias {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hmem : v.val ∈ g.inputs) :
    ∃ a : ℕ, (a < n + pre.length ∨ n + pre.length + post.length ≤ a) ∧
      ∀ x : Fin n → Bool, x v = false →
        g.op.eval (g.inputs.map fun j =>
          (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD j false) =
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false := by
  obtain ⟨a,ha⟩ := positive_zero_alias g.op hop g.inputs hlen v.val hmem
  have hv (x : Fin n → Bool) (hx : x v = false) :
      (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD v.val false = false := by
    rw [on1_getD_wires_input _ _ _ v.isLt]
    exact hx
  cases a with
  | none =>
    refine ⟨n + pre.length + post.length, Or.inr (le_refl _), ?_⟩
    intro x hx
    rw [ha _ (hv x hx)]
    symm
    apply on1_getD_wires_of_ge
    simp
  | some a =>
    by_cases hlt : a < n + pre.length
    · exact ⟨a, Or.inl hlt, fun x hx => ha _ (hv x hx)⟩
    · refine ⟨n + pre.length + post.length, Or.inr (le_refl _), ?_⟩
      intro x hx
      rw [ha _ (hv x hx)]
      change (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD a false =
        (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD (n + pre.length + post.length) false
      rw [on1_getD_wires_of_ge _ _ a (by simpa using Nat.le_of_not_gt hlt),
        on1_getD_wires_of_ge _ _ (n + pre.length + post.length) (by simp)]

lemma delete_positive_zero {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (hmem : v.val ∈ g.inputs) :
    ∃ r : ℕ → ℕ,
      (pre ++ post.map (on1_relabel r)).length + 1 = (pre ++ g :: post).length ∧
      ∀ (o : ℕ) (x : Fin n → Bool), x v = false →
        Circuit.eval ⟨pre ++ post.map (on1_relabel r), r o⟩ (List.ofFn x) =
          Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) := by
  obtain ⟨a, ha, hval⟩ := direct_zero_alias pre post g v hop hlen hmem
  refine ⟨deleteMap (n + pre.length) a, delete_length n pre post g a, ?_⟩
  intro o x hx
  exact delete_alias n pre post g a ha o x (hval x hx)

lemma delete_not_unique (pre post : List Gate) (g : Gate) (r : ℕ → ℕ)
    (huniq : ∀ i j : Fin (pre ++ g :: post).length,
      ((pre ++ g :: post).get i).op = GateOp.not →
      ((pre ++ g :: post).get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (pre ++ post.map (on1_relabel r)).length,
      ((pre ++ post.map (on1_relabel r)).get i).op = GateOp.not →
      ((pre ++ post.map (on1_relabel r)).get j).op = GateOp.not → i = j := by
  let emb : Fin (pre ++ post.map (on1_relabel r)).length → Fin (pre ++ g :: post).length :=
    fun k => ⟨if k.val < pre.length then k.val else k.val + 1, by
      have hk := k.isLt
      simp only [List.length_append, List.length_map, List.length_cons] at hk ⊢
      split_ifs <;> omega⟩
  have hinj : Function.Injective emb := by
    intro i j hij
    have hh := congrArg Fin.val hij
    dsimp [emb] at hh
    apply Fin.ext
    split_ifs at hh <;> omega
  have hop (k : Fin (pre ++ post.map (on1_relabel r)).length) :
      ((pre ++ post.map (on1_relabel r)).get k).op =
        ((pre ++ g :: post).get (emb k)).op := by
    simp only [List.get_eq_getElem]
    by_cases hk : k.val < pre.length
    · simp [emb, hk, List.getElem_append_left]
    · have hk' : pre.length ≤ k.val := by omega
      simp only [emb, hk, ite_false]
      rw [List.getElem_append_right hk', List.getElem_append_right (by omega)]
      simp only [show k.val + 1 - pre.length = (k.val - pre.length) + 1 by omega,
        List.getElem_cons_succ, List.getElem_map, on1_relabel]
  intro i j hi hj
  apply hinj
  apply huniq
  · rw [← hop i]
    exact hi
  · rw [← hop j]
    exact hj

lemma not_unique_cover (gs : List Gate) (hpos : 0 < gs.length)
    (huniq : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) :
    ∃ ι : Fin 1 → Fin gs.length, ∀ i : Fin gs.length,
      (gs.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i := by
  classical
  by_cases hex : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not
  · obtain ⟨i, hi⟩ := hex
    refine ⟨fun _ => i, ?_⟩
    intro j hj
    exact ⟨0, huniq i j hi hj⟩
  · refine ⟨fun _ => ⟨0, hpos⟩, ?_⟩
    intro j hj
    exact False.elim (hex ⟨j,hj⟩)

end PEqualNP.Outside.L_meta_951.Deletion
