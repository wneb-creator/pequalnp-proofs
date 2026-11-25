import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.SingletonBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

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

lemma wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

lemma getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

lemma mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i


def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

lemma inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

lemma oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

def graph : Fin 33 → Fin 33 → Bool := (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val))))

lemma graph_diag : ∀ u : Fin 33, graph u u = false := by decide +kernel

lemma graph_pos : graph 0 1 = true := by decide +kernel

lemma eval_inp_mono (C : Circuit) (hm : Monotone2 C) {P Q : Finset ℕ}
    (hPQ : P ⊆ Q) : C.eval (inp 66 P) = true → C.eval (inp 66 Q) = true := by
  change (wiresFrom C.gates (inp 66 P)).getD C.output false = true →
    (wiresFrom C.gates (inp 66 Q)).getD C.output false = true
  apply mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp [inp]) _ C.output
  intro i hi
  rw [inp_getD, decide_eq_true_eq] at hi ⊢
  exact ⟨hi.1, hPQ hi.2⟩

lemma singleton_inp_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) (w : Fin 66) :
    C.eval (inp 66 {(w : ℕ)}) = false := by
  by_contra hn
  have ht : C.eval (inp 66 {(w : ℕ)}) = true := by
    cases h : C.eval (inp 66 {(w : ℕ)}) <;> simp_all
  let u : Fin 33 := ⟨w.val % 33, Nat.mod_lt _ (by decide)⟩
  have hsub : ({(w : ℕ)} : Finset ℕ) ⊆ {(u : ℕ), 33 + (u : ℕ)} := by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hw := w.isLt
    dsimp [u]
    omega
  have hout := eval_inp_mono C hm hsub ht
  have hz : C.eval (inp 66 {(u : ℕ), 33 + (u : ℕ)}) = false := by
    rw [← oneEach_eq u u]
    exact (hr u u).trans (graph_diag u)
  rw [hz] at hout
  exact Bool.noConfusion hout

lemma singleton_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) (w : Fin 66) :
    C.eval (List.ofFn (fun i : Fin 66 => decide (i = w))) = false := by
  simpa only [inp, Finset.mem_singleton, Fin.ext_iff] using singleton_inp_false C hm hr w

lemma zero_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) :
    C.eval (List.ofFn (fun _ : Fin 66 => false)) = false := by
  have hz : C.eval (inp 66 (∅ : Finset ℕ)) = false := by
    by_contra hn
    have ht : C.eval (inp 66 (∅ : Finset ℕ)) = true := by
      cases h : C.eval (inp 66 (∅ : Finset ℕ)) <;> simp_all
    have hout := eval_inp_mono C hm (Finset.empty_subset ({0} : Finset ℕ)) ht
    have hs := singleton_inp_false C hm hr 0
    change C.eval (inp 66 {0}) = false at hs
    rw [hs] at hout
    exact Bool.noConfusion hout
  simpa [inp] using hz

lemma function_ne_zero (C : Circuit) (hr : PEqualNP.Represents.Represents graph C) :
    (fun x : Fin 66 → Bool => C.eval (List.ofFn x)) ≠ (fun _ => false) := by
  intro h
  have hz := congrFun h (fun i : Fin 66 => decide ((i : ℕ) ∈ ({0,34} : Finset ℕ)))
  change C.eval (inp 66 {0,34}) = false at hz
  have hp := hr 0 1
  rw [graph_pos, oneEach_eq] at hp
  change C.eval (inp 66 {0,34}) = true at hp
  rw [hz] at hp
  exact Bool.noConfusion hp

lemma function_ne_one (C : Circuit) (hr : PEqualNP.Represents.Represents graph C) :
    (fun x : Fin 66 → Bool => C.eval (List.ofFn x)) ≠ (fun _ => true) := by
  intro h
  have ho := congrFun h (fun i : Fin 66 => decide ((i : ℕ) ∈ ({0,33} : Finset ℕ)))
  change C.eval (inp 66 {0,33}) = true at ho
  have hn := hr 0 0
  rw [graph_diag, oneEach_eq] at hn
  change C.eval (inp 66 {0,33}) = false at hn
  rw [hn] at ho
  exact Bool.noConfusion ho

end PEqualNP.Outside.L_meta_9502.SingletonBridge
