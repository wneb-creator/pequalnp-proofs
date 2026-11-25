import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma monoW : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g t ih =>
    intro hop U V hlen hUV i
    rw [wf_cons, wf_cons]
    refine ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) ?_ i
    intro j hj
    rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
    · rw [getD_snoc_lt _ _ _ hj'] at hj
      rw [getD_snoc_lt _ _ _ (by omega)]
      exact hUV j hj
    · rw [hj', getD_snoc_eq] at hj
      rw [hj', hlen, getD_snoc_eq]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs U V hUV hj
    · rw [getD_snoc_gt _ _ _ hj'] at hj
      exact absurd hj (by simp)


def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma wf_length (gs : List Gate) (x : List Bool) :
    (wf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wf_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma and_true_agreement : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and) →
    ∀ U V W : List Bool, U.length = V.length → V.length = W.length →
      (∀ i, U.getD i false = true → V.getD i false = W.getD i false) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = (wf gs W).getD i false := by
  intro gs
  induction gs with
  | nil => intro _ U V W _ _ h i; exact h i
  | cons g gs ih =>
    intro hops U V W hUV hVW same i
    rw [wf_cons, wf_cons, wf_cons]
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) _ _ _
      (by simp [hUV]) (by simp [hVW])
    intro j hj
    rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
    · rw [getD_snoc_lt _ _ _ hj'] at hj
      rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
      exact same j hj
    · rw [hj', getD_snoc_eq] at hj
      rw [hj', hUV, getD_snoc_eq, hVW, getD_snoc_eq]
      have hop := hops g (List.mem_cons_self ..)
      rw [hop] at hj ⊢
      have args : ∀ k ∈ g.inputs, U.getD k false = true := by
        simpa only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] using hj
      have eqArgs : g.inputs.map (fun k => V.getD k false) =
          g.inputs.map (fun k => W.getD k false) := by
        apply List.map_congr_left
        intro k hk
        exact same k (args k hk)
      rw [eqArgs]
    · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]

lemma and_tail_irrelevant (gs : List Gate) (hops : ∀ g ∈ gs, g.op = GateOp.and)
    (U V : List Bool) (sameLength : U.length = V.length) (out : ℕ)
    (one : (wf gs (U ++ [false])).getD out false = true) (b : Bool) :
    (wf gs (V ++ [b])).getD out false = (wf gs (V ++ [true])).getD out false := by
  apply and_true_agreement gs hops (U ++ [false]) (V ++ [b]) (V ++ [true])
    (by simp [sameLength]) (by simp) _ out one
  intro i hi
  rcases Nat.lt_trichotomy i U.length with h | h | h
  · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
  · rw [h, getD_snoc_eq] at hi
    contradiction
  · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]

lemma one_not_and_suffix_constant (pre post : List Gate)
    (mono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (onlyAnd : ∀ g ∈ post, g.op = GateOp.and) (wire out : ℕ)
    (correct : ∀ x : Fin 10 → Bool,
      (wf post (wf pre (List.ofFn x) ++ [!((wf pre (List.ofFn x)).getD wire false)])).getD out false = pet x) :
    ∀ x : Fin 10 → Bool,
      (wf post (wf pre (List.ofFn x) ++ [true])).getD out false = pet x := by
  intro x
  have hone := correct (fun _ => true)
  have hz : pet (fun _ => true) = true := by decide
  rw [hz] at hone
  cases h : (wf pre (List.ofFn (fun _ : Fin 10 => true))).getD wire false with
  | false =>
    have hx : (wf pre (List.ofFn x)).getD wire false = false := by
      cases hx' : (wf pre (List.ofFn x)).getD wire false with
      | false => rfl
      | true =>
        have up := monoW pre mono _ _ (by simp)
          (ofFn_mono 10 x (fun _ => true) (by simp)) wire hx'
        rw [h] at up
        contradiction
    have hc := correct x
    simpa only [hx, Bool.not_false] using hc
  | true =>
    simp only [h, Bool.not_true] at hone
    have eq := and_tail_irrelevant post onlyAnd (wf pre (List.ofFn (fun _ : Fin 10 => true)))
      (wf pre (List.ofFn x)) (by simp only [wf_length, List.length_ofFn]) out hone
      (!((wf pre (List.ofFn x)).getD wire false))
    exact eq.symm.trans (correct x)

end PEqualNP.Outside.L_meta_2592_aux
