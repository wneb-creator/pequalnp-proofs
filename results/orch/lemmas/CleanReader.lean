import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.CleanReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma snoc_lt (w : List Bool) (b : Bool) (i : Nat) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

lemma snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma snoc_gt (w : List Bool) (b : Bool) (i : Nat) (hi : w.length < i) :
    (w ++ [b]).getD i false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma two_members (xs : List Nat) (i n : Nat) (hne : i ≠ n)
    (hlen : xs.length ≤ 2) (hi : i ∈ xs) (hn : n ∈ xs) :
    xs = [i,n] ∨ xs = [n,i] := by
  rcases xs with _ | ⟨a,xs⟩
  · simp at hi
  rcases xs with _ | ⟨b,xs⟩
  · simp only [List.mem_singleton] at hi hn
    exact False.elim (hne (hi.trans hn.symm))
  have hx : xs = [] := by
    have : xs.length = 0 := by simpa using hlen
    simpa using this
  subst xs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi hn
  rcases hi with rfl | rfl <;> rcases hn with rfl | rfl
  · exact False.elim (hne rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (hne rfl)

lemma paired_eval (op : GateOp) (hop : op = .and ∨ op = .or)
    (xs : List Nat) (i n : Nat) (hne : i ≠ n) (hlen : xs.length ≤ 2)
    (hi : i ∈ xs) (hn : n ∈ xs) (u v : List Bool)
    (hu : u.getD n false = !(u.getD i false))
    (hv : v.getD n false = !(v.getD i false)) :
    op.eval (xs.map fun k => u.getD k false) =
      op.eval (xs.map fun k => v.getD k false) := by
  rcases two_members xs i n hne hlen hi hn with rfl | rfl <;>
    rcases hop with rfl | rfl <;>
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
      List.any_cons,List.any_nil,id_eq,hu,hv] <;> simp

lemma step_antitone (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (hlen : g.inputs.length ≤ 2) (i n : Nat) (hne : i ≠ n)
    (paired : i ∈ g.inputs → n ∈ g.inputs) (u v : List Bool)
    (hu : u.getD n false = !(u.getD i false))
    (hv : v.getD n false = !(v.getD i false))
    (rel : ∀ k, k ≠ i → u.getD k false = true → v.getD k false = true) :
    g.op.eval (g.inputs.map fun k => u.getD k false) = true →
      g.op.eval (g.inputs.map fun k => v.getD k false) = true := by
  by_cases hi : i ∈ g.inputs
  · rw [paired_eval g.op hop g.inputs i n hne hlen hi (paired hi) u v hu hv]
    exact id
  · have hrel : ∀ k ∈ g.inputs, u.getD k false = true → v.getD k false = true := by
      intro k hk
      exact rel k (by rintro rfl; exact hi hk)
    rcases hop with hop | hop <;> rw [hop]
    · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_def,id]
      exact fun hall k hk => hrel k hk (hall k hk)
    · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_def,id]
      exact fun ⟨k,hk,hval⟩ => ⟨k,hk,hrel k hk hval⟩

lemma wf_antitone (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlens : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (i n : Nat) (hne : i ≠ n)
    (paired : ∀ g ∈ gs, i ∈ g.inputs → n ∈ g.inputs)
    (u v : List Bool) (hlen : u.length = v.length)
    (hi : i < u.length) (hn : n < u.length)
    (hu : u.getD n false = !(u.getD i false))
    (hv : v.getD n false = !(v.getD i false))
    (rel : ∀ k, k ≠ i → u.getD k false = true → v.getD k false = true) :
    ∀ k, k ≠ i → (wf gs u).getD k false = true → (wf gs v).getD k false = true := by
  induction gs generalizing u v with
  | nil => exact rel
  | cons g gs ih =>
    change ∀ k, k ≠ i →
      (wf gs (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD k false = true →
      (wf gs (v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)])).getD k false = true
    apply ih (fun a ha => hops a (List.mem_cons_of_mem _ ha))
      (fun a ha => hlens a (List.mem_cons_of_mem _ ha))
      (fun a ha => paired a (List.mem_cons_of_mem _ ha)) _ _
      (by simp [hlen]) (by simp; omega) (by simp; omega)
    · simpa only [snoc_lt _ _ _ hn,snoc_lt _ _ _ hi] using hu
    · simpa only [snoc_lt _ _ _ (show n < v.length by omega),
        snoc_lt _ _ _ (show i < v.length by omega)] using hv
    · intro k hki hk
      rcases lt_trichotomy k u.length with h | rfl | h
      · rw [snoc_lt _ _ _ h] at hk
        rw [snoc_lt _ _ _ (by omega)]
        exact rel k hki hk
      · rw [snoc_eq] at hk
        rw [hlen,snoc_eq]
        exact step_antitone g (hops g (List.mem_cons_self ..))
          (hlens g (List.mem_cons_self ..)) i n hne (paired g (List.mem_cons_self ..))
          u v hu hv rel hk
      · rw [snoc_gt _ _ _ h] at hk
        cases hk

lemma wf_initial (gs : List Gate) (u : List Bool) (k : Nat) (hk : k < u.length) :
    (wf gs u).getD k false = u.getD k false := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (u ++ [g.op.eval (g.inputs.map fun a => u.getD a false)])).getD k false = _
    rw [ih _ (by simp;omega),snoc_lt _ _ _ hk]

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def seed (i j : Fin 10) (x : Fin 10 → Bool) : List Bool :=
  List.ofFn x ++ [!x i,!x j,(!x i && !x j)]

def chosen (i j : Fin 10) (s : Bool) : Fin 10 := if s then j else i
def negative (s : Bool) : Nat := if s then 11 else 10
def neighbor : Fin 10 → Fin 10 := ![1,2,3,4,0,7,8,9,5,6]
def low (i : Fin 10) : Fin 10 → Bool := fun k => decide (k = neighbor i)
def high (i : Fin 10) : Fin 10 → Bool := fun k => decide (k = i) || low i k
def single (i : Fin 10) : Fin 10 → Bool := fun k => decide (k = i)

lemma seed_length (i j : Fin 10) (x : Fin 10 → Bool) : (seed i j x).length = 13 := by
  simp [seed]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma witness_facts : ∀ (i j : Fin 10) (s : Bool), i ≠ j →
    let k := chosen i j s
    pet (low k) = false ∧ pet (high k) = true ∧ pet (single k) = false ∧
    (seed i j (single k)).getD k.val false = true ∧
    (seed i j (high k)).getD (negative s) false =
      !((seed i j (high k)).getD k.val false) ∧
    (seed i j (low k)).getD (negative s) false =
      !((seed i j (low k)).getD k.val false) ∧
    (∀ r : Fin 13, r.val ≠ k.val →
      (seed i j (high k)).getD r.val false = true →
      (seed i j (low k)).getD r.val false = true) := by
  decide

lemma clean_reader (i j : Fin 10) (hne : i ≠ j) (s : Bool) (gs : List Gate) (out : Nat)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlens : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 10 → Bool, (wf gs (seed i j x)).getD out false = pet x) :
    ∃ g ∈ gs, (chosen i j s).val ∈ g.inputs ∧ negative s ∉ g.inputs := by
  obtain ⟨hlo,hhi,hsingle,hinput,hpairhi,hpairlo,hrel⟩ := witness_facts i j s hne
  have hout : out ≠ (chosen i j s).val := by
    intro heq
    have h := hc (single (chosen i j s))
    rw [heq,wf_initial _ _ _ (by rw [seed_length]; exact lt_trans (chosen i j s).isLt (by decide)),
      hsingle,hinput] at h
    cases h
  by_contra hnone
  have paired : ∀ g ∈ gs, (chosen i j s).val ∈ g.inputs → negative s ∈ g.inputs := by
    intro g hg hgi
    by_contra hgn
    exact hnone ⟨g,hg,hgi,hgn⟩
  have hnk : (chosen i j s).val ≠ negative s := by
    have := (chosen i j s).isLt
    cases s <;> simp only [negative,Bool.false_eq_true,ite_false,ite_true] <;> omega
  have hnlen : negative s < 13 := by cases s <;> decide
  have result := wf_antitone gs hops hlens (chosen i j s).val (negative s) hnk paired
    (seed i j (high (chosen i j s))) (seed i j (low (chosen i j s)))
    (by simp only [seed_length]) (by rw [seed_length]; omega)
    (by rw [seed_length]; exact hnlen) hpairhi hpairlo
    (fun r hr hval => ?_) out hout
  · rw [hc,hc,hlo,hhi] at result
    exact Bool.noConfusion (result rfl)
  · by_cases hrlen : r < 13
    · exact hrel ⟨r,hrlen⟩ hr hval
    · rw [List.getD_eq_default _ _ (by rw [seed_length];omega)] at hval
      cases hval

end PEqualNP.Outside.L_meta_2592.CleanReader
