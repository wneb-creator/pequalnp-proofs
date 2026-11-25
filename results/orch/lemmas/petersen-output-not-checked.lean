import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1884.OutputNot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w++[g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma gate_eval_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro h i hi
    exact hxy i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i h⟩

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma step_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (step w g).getD i false = true → (step v g).getD i false = true := by
  intro i hi
  rw [step_getD] at hi ⊢
  rw [← hlen]
  split_ifs at hi ⊢ with h
  · exact gate_eval_monotone g hg _ _ hle hi
  · exact hle i hi

lemma fold_state_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step,hlen]
    · exact step_monotone g (hg g List.mem_cons_self) w v hlen hle


lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega

lemma fold_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
    (gs.foldl step w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step]; omega),step_getD]
    rw [ite_eq_right (by omega)]

lemma output_not_eval (pre post : List Gate) (ins : List ℕ) (xs : List Bool) :
    ({gates := pre++⟨GateOp.not,ins⟩::post,output := xs.length+pre.length} : Circuit).eval xs=
      GateOp.not.eval (ins.map fun i => (pre.foldl step xs).getD i false) := by
  simp only [Circuit.eval,Circuit.wires,List.foldl_append,List.foldl_cons]
  change (post.foldl step (step (pre.foldl step xs) ⟨GateOp.not,ins⟩)).getD
    (xs.length+pre.length) false = _
  rw [fold_old post _ _ (by simp [step,fold_length]),step_getD]
  simp [fold_length]

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def low : Fin 10 → Bool := fun i => decide (i.val=2)
def high : Fin 10 → Bool := fun i => decide (i.val=1 ∨ i.val=2)
def input (x : Fin 10 → Bool) : List Bool := List.ofFn x++[!x 0]

lemma input_length (x : Fin 10 → Bool) : (input x).length=11 := by simp [input]
lemma input_order : ∀ i, (input low).getD i false=true → (input high).getD i false=true := by
  intro i
  by_cases hi : i<11
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by rw [input_length]; omega)]
    simp
lemma low_value : target low=false := by decide
lemma high_value : target high=true := by decide

lemma output_not_cannot_compute (pre post : List Gate) (ins : List ℕ)
    (hpre : ∀ g∈pre,g.op=GateOp.and ∨ g.op=GateOp.or)
    (hfun : ∀ x : Fin 10 → Bool,
      ({gates := pre++⟨GateOp.not,ins⟩::post,output := 11+pre.length} : Circuit).eval (input x)=target x) :
    False := by
  have hl := hfun low
  have hh := hfun high
  have el := output_not_eval pre post ins (input low)
  have eh := output_not_eval pre post ins (input high)
  rw [input_length] at el eh
  rw [el,low_value] at hl
  rw [eh,high_value] at hh
  have hm := fold_state_monotone pre hpre (input low) (input high)
    (by rw [input_length,input_length]) input_order
  cases ins with
  | nil => simp [GateOp.eval] at hl
  | cons a ins =>
    have la : (pre.foldl step (input low)).getD a false=true := by
      simpa [GateOp.eval] using hl
    have ha := hm a la
    have hb : (pre.foldl step (input high)).getD a false=false := by
      simpa [GateOp.eval] using hh
    exact Bool.noConfusion (ha.symm.trans hb)

lemma unique_not_cannot_output (pre post : List Gate) (ins : List ℕ)
    (hfan : FanInTwo ⟨pre++⟨GateOp.not,ins⟩::post,11+pre.length⟩)
    (hcount : (pre++⟨GateOp.not,ins⟩::post).countP (fun g => g.op.eval [false])≤1)
    (hfun : ∀ x : Fin 10 → Bool,
      ({gates := pre++⟨GateOp.not,ins⟩::post,output := 11+pre.length} : Circuit).eval (input x)=target x) :
    False := by
  apply output_not_cannot_compute pre post ins _ hfun
  intro g hg
  have hop := (hfan g (List.mem_append_left _ hg)).1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with ha | ho | hn
  · exact Or.inl ha
  · exact Or.inr ho
  · have positivity (ls : List Gate) : ∀ a∈ls,a.op=GateOp.not →
        1≤ls.countP (fun g => g.op.eval [false]) := by
      induction ls with
      | nil => simp
      | cons b ls ih =>
        intro a ha hna
        rcases List.mem_cons.mp ha with rfl | ha
        · have hb : a.op.eval [false]=true := by rw [hna]; rfl
          simp only [List.countP_cons,hb,ite_true]
          omega
        · have h := ih a ha hna
          simp only [List.countP_cons]
          omega
    have hp := positivity pre g hg hn
    have hb : (⟨GateOp.not,ins⟩ : Gate).op.eval [false]=true := rfl
    simp only [List.countP_append,List.countP_cons,hb,ite_true] at hcount
    omega

end PEqualNP.Outside.L_meta_1884.OutputNot
