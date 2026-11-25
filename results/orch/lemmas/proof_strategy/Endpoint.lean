import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot110Endpoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma all_drop (w : List Bool) (b : Bool) (pins : List ℕ)
    (neutral : w.length ∈ pins → b = true) :
    (pins.map fun i => (w ++ [b]).getD i false).all id =
      ((pins.filter (fun i => i != w.length)).map fun i => w.getD i false).all id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]
  constructor
  · intro h a ha
    obtain ⟨ha, hn⟩ := List.mem_filter.mp ha
    have ne : a ≠ w.length := by simpa using hn
    rw [← getD_snoc_ne w b a ne]
    exact h a ha
  · intro h a ha
    by_cases ne : a = w.length
    · subst a
      rw [getD_append_last_eq w b _ rfl, neutral ha]
    · rw [getD_snoc_ne w b a ne]
      exact h a (List.mem_filter.mpr ⟨ha, by simpa using ne⟩)

lemma any_drop (w : List Bool) (b : Bool) (pins : List ℕ)
    (neutral : w.length ∈ pins → b = false) :
    (pins.map fun i => (w ++ [b]).getD i false).any id =
      ((pins.filter (fun i => i != w.length)).map fun i => w.getD i false).any id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map, Function.comp_def, id_eq, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hv⟩
    by_cases ne : a = w.length
    · subst a
      rw [getD_append_last_eq w b _ rfl, neutral ha] at hv
      cases hv
    · exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa using ne⟩,
        (getD_snoc_ne w b a ne).symm.trans hv⟩
  · rintro ⟨a, ha, hv⟩
    obtain ⟨ha, hn⟩ := List.mem_filter.mp ha
    have ne : a ≠ w.length := by simpa using hn
    exact ⟨a, ha, (getD_snoc_ne w b a ne).trans hv⟩

lemma input_order {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ k, (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
  intro k hk
  by_cases hlt : k < n
  · rw [getD_ofFn _ _ hlt] at hk ⊢
    exact hxy _ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at hk
    cases hk

lemma mono_wire {n : ℕ} (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (k : ℕ) :
    (gs.foldl wiresStep (List.ofFn x)).getD k false = true →
      (gs.foldl wiresStep (List.ofFn y)).getD k false = true :=
  monotone_foldl_wiresStep gs mono _ _ (by simp) (input_order x y hxy) k

lemma output_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [g]) (n + gs.length)).eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (gs.foldl wiresStep (List.ofFn x)).getD i false) := by
  change ((gs ++ [g]).foldl wiresStep (List.ofFn x)).getD _ false = _
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, wiresStep]
  apply getD_append_last_eq
  rw [foldl_wiresStep_length, List.length_ofFn]

lemma output_not_snoc {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun j =>
        (gs.foldl wiresStep (List.ofFn x) ++
          [!((gs.foldl wiresStep (List.ofFn x)).getD i false)]).getD j false) := by
  have h := output_snoc (gs ++ [⟨.not, [i]⟩]) g x
  simpa [List.append_assoc, List.foldl_append, wiresStep, GateOp.eval, Nat.add_assoc] using h

lemma remove_terminal_not {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate)
    (mono : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (op : g.op = .and ∨ g.op = .or)
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) :
    ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨g.op, g.inputs.filter (fun j => j != n + gs.length)⟩])
        (n + gs.length)).eval (List.ofFn x) =
      (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) := by
  intro x
  rw [output_snoc, output_not_snoc]
  have len (y : Fin n → Bool) : (gs.foldl wiresStep (List.ofFn y)).length = n + gs.length := by
    rw [foldl_wiresStep_length, List.length_ofFn]
  rcases op with hand | hor
  · rw [output_not_snoc, hand] at one
    rw [hand]
    change ((g.inputs.filter (fun j => j != n + gs.length)).map
      (fun j => (gs.foldl wiresStep (List.ofFn x)).getD j false)).all id = _
    symm
    convert all_drop (gs.foldl wiresStep (List.ofFn x))
      (!((gs.foldl wiresStep (List.ofFn x)).getD i false)) g.inputs ?_ using 1 <;> try { rw [len] } <;> try rfl
    intro hm
    have hm' : n + gs.length ∈ g.inputs := by simpa [len] using hm
    have atOne := (List.all_eq_true.mp one) _ (List.mem_map.mpr ⟨n + gs.length, hm', rfl⟩)
    have sourceOne : (gs.foldl wiresStep (List.ofFn (fun _ : Fin n => true))).getD i false = false := by
      simpa [← len (fun _ : Fin n => true)] using atOne
    have source : (gs.foldl wiresStep (List.ofFn x)).getD i false = false := by
      cases hx : (gs.foldl wiresStep (List.ofFn x)).getD i false
      · rfl
      · have contra := mono_wire gs mono x (fun _ => true) (by simp) i hx
        rw [sourceOne] at contra
        cases contra
    rw [source]
    rfl
  · rw [output_not_snoc, hor] at zero
    rw [hor]
    change ((g.inputs.filter (fun j => j != n + gs.length)).map
      (fun j => (gs.foldl wiresStep (List.ofFn x)).getD j false)).any id = _
    symm
    convert any_drop (gs.foldl wiresStep (List.ofFn x))
      (!((gs.foldl wiresStep (List.ofFn x)).getD i false)) g.inputs ?_ using 1 <;> try { rw [len] } <;> try rfl
    intro hm
    have hm' : n + gs.length ∈ g.inputs := by simpa [len] using hm
    have atZero := (List.any_eq_false.mp zero) _ (List.mem_map.mpr ⟨n + gs.length, hm', rfl⟩)
    have sourceZero : (gs.foldl wiresStep (List.ofFn (fun _ : Fin n => false))).getD i false = true := by
      simpa [← len (fun _ : Fin n => false)] using atZero
    have source := mono_wire gs mono (fun _ => false) x (by simp) i sourceZero
    rw [source]
    rfl

lemma final_not_impossible {n : ℕ} (gs : List Gate) (i : ℕ)
    (mono : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩]) (n + gs.length)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩]) (n + gs.length)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) : False := by
  rw [output_snoc] at zero one
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_false'] at zero
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_true'] at one
  have h := mono_wire gs mono (fun _ : Fin n => false) (fun _ => true) (by simp) i zero
  rw [one] at h
  cases h

lemma penultimate_not_smaller {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate)
    (mono : Monotone2 ⟨gs, 0⟩)
    (op : g.op = .and ∨ g.op = .or)
    (arity : g.inputs.length ≤ 2)
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = gs.length + 2 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) := by
  refine ⟨⟨gs ++ [⟨g.op, g.inputs.filter (fun j => j != n + gs.length)⟩], n + gs.length⟩,
    ?_, by simp [Circuit.size], ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with before | last
    · exact mono q before
    · rw [List.mem_singleton.mp last]
      refine ⟨by simpa using op, (List.length_filter_le _ _).trans arity⟩
  · exact remove_terminal_not gs i g (fun q hq => (mono q hq).1) op zero one

end PEqualNP.Outside.Pilot110Endpoint
