import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.Move

open PEqualNP.CircuitLowerBounds

def redirect (m a i : ℕ) : ℕ :=
  if i < m then i else if i = m then a else i - 1

lemma redirect_of_lt (m a i : ℕ) (hi : i < m) : redirect m a i = i := by
  simp [redirect, hi]

lemma redirect_at (m a : ℕ) : redirect m a m = a := by
  simp [redirect]

lemma redirect_of_gt (m a i : ℕ) (hi : m < i) : redirect m a i = i - 1 := by
  simp [redirect, show ¬i < m by omega, show i ≠ m by omega]

lemma redirect_lt_length (m a l i : ℕ) (ha : a < m) (hm : m ≤ l)
    (hi : i < l + 1) : redirect m a i < l := by
  unfold redirect
  split_ifs <;> omega

lemma alias_start (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ∀ i, (w ++ [w.getD a false]).getD i false =
      w.getD (redirect w.length a i) false := by
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, redirect_of_lt _ _ _ hi]
  · by_cases he : i = w.length
    · subst i
      rw [redirect_at, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hg : w.length < i := by omega
      rw [redirect_of_gt _ _ _ hg]
      rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma alias_extend (m a : ℕ) (v w : List Bool) (b : Bool)
    (ha : a < m) (hm : m ≤ w.length) (hlen : v.length = w.length + 1)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    ∀ i, (v ++ [b]).getD i false = (w ++ [b]).getD (redirect m a i) false := by
  intro i
  by_cases hi : i < v.length
  · have hr : redirect m a i < w.length :=
      redirect_lt_length m a w.length i ha hm (by omega)
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hr]
    exact agree i
  · by_cases he : i = v.length
    · subst i
      have hg : m < v.length := by omega
      rw [redirect_of_gt _ _ _ hg]
      have hv : v.length - 1 = w.length := by omega
      rw [hv, List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hg : m < i := by omega
      rw [redirect_of_gt _ _ _ hg,
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

def renameGate (m a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect m a)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma alias_gate (m a : ℕ) (v w : List Bool) (g : Gate)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    g.op.eval (g.inputs.map fun i => v.getD i false) =
      (renameGate m a g).op.eval
        ((renameGate m a g).inputs.map fun i => w.getD i false) := by
  simp only [renameGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact agree i

lemma alias_fold (m a : ℕ) (gs : List Gate) (v w : List Bool)
    (ha : a < m) (hm : m ≤ w.length) (hlen : v.length = w.length + 1)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    ∀ i, (gs.foldl step v).getD i false =
      ((gs.map (renameGate m a)).foldl step w).getD (redirect m a i) false := by
  induction gs generalizing v w with
  | nil => exact agree
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · have hg := alias_gate m a v w g agree
      unfold step
      rw [← hg]
      exact alias_extend m a v w _ ha hm hlen agree


lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp only [step,
      List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

def bypass (C : Circuit) (n k a : ℕ) : Circuit :=
  ⟨C.gates.take k ++ (C.gates.drop (k + 1)).map (renameGate (n + k) a),
    redirect (n + k) a C.output⟩

lemma bypass_size (C : Circuit) (n k a : ℕ) (hk : k < C.size) :
    (bypass C n k a).size + 1 = C.size := by
  simp only [bypass, Circuit.size, List.length_append, List.length_map,
    List.length_take, List.length_drop]
  change k < C.gates.length at hk
  omega

lemma bypass_prefix (C : Circuit) (n k a i : ℕ) (x : List Bool)
    (hk : k < C.size) (hx : x.length = n) (hi : i < n + k) :
    ((bypass C n k a).wires x).getD i false =
      ((C.gates.take k).foldl step x).getD i false := by
  change ((C.gates.take k ++ (C.gates.drop (k + 1)).map
    (renameGate (n + k) a)).foldl step x).getD i false = _
  rw [List.foldl_append]
  apply run_preserves
  rw [run_length, hx, List.length_take]
  change k < C.gates.length at hk
  omega

lemma bypass_eval (C : Circuit) (n k a : ℕ) (x : List Bool)
    (hk : k < C.size) (ha : a < n + k) (hx : x.length = n)
    (value : (C.gates.get ⟨k, hk⟩).op.eval
      ((C.gates.get ⟨k, hk⟩).inputs.map fun i =>
        ((C.gates.take k).foldl step x).getD i false) =
      ((C.gates.take k).foldl step x).getD a false) :
    (bypass C n k a).eval x = C.eval x := by
  let w := (C.gates.take k).foldl step x
  have hw : w.length = n + k := by
    dsimp only [w]
    rw [run_length, hx, List.length_take]
    change k < C.gates.length at hk
    omega
  have splitC : C.gates = C.gates.take k ++
      C.gates.get ⟨k, hk⟩ :: C.gates.drop (k + 1) := by simp
  change ((C.gates.take k ++ (C.gates.drop (k + 1)).map
    (renameGate (n + k) a)).foldl step x).getD (redirect (n + k) a C.output) false =
      (C.gates.foldl step x).getD C.output false
  conv_rhs => rw [splitC, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  change (((C.gates.drop (k + 1)).map (renameGate (n + k) a)).foldl step w).getD
      (redirect (n + k) a C.output) false =
    ((C.gates.drop (k + 1)).foldl step
      (w ++ [(C.gates.get ⟨k, hk⟩).op.eval
        ((C.gates.get ⟨k, hk⟩).inputs.map fun i => w.getD i false)])).getD
      C.output false
  change (C.gates.get ⟨k, hk⟩).op.eval
    ((C.gates.get ⟨k, hk⟩).inputs.map fun i => w.getD i false) =
      w.getD a false at value
  rw [value]
  apply Eq.symm
  apply alias_fold (n + k) a (C.gates.drop (k + 1)) _ w ha (by omega)
  · simp
  · have h := alias_start w a (by omega)
    simpa only [hw] using h

def appendOr (C : Circuit) (n b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [C.output, b]⟩], n + C.size⟩

lemma appendOr_eval (C : Circuit) (n b : ℕ) (x : List Bool) (hx : x.length = n) :
    (appendOr C n b).eval x = (C.eval x || (C.wires x).getD b false) := by
  have hw : (C.wires x).length = n + C.size := by
    exact (run_length C.gates x).trans (by rw [hx]; rfl)
  change ((C.gates ++ [(⟨GateOp.or, [C.output, b]⟩ : Gate)]).foldl step x).getD
    (n + C.size) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold step
  rw [List.getD_append_right _ _ _ _ (by change (C.wires x).length ≤ n + C.size; omega)]
  change ([GateOp.or.eval ([C.output, b].map fun i => (C.wires x).getD i false)]).getD
    (n + C.size - (C.wires x).length) false = _
  rw [hw]
  simp [GateOp.eval, Circuit.eval]

lemma appendOr_size (C : Circuit) (n b : ℕ) :
    (appendOr C n b).size = C.size + 1 := by
  simp [appendOr, Circuit.size]

lemma renameGate_fan (g : Gate) (m a : ℕ)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    (renameGate m a g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (renameGate m a g).inputs.length ≤ 2 := by
  exact ⟨h.1, by simpa only [renameGate, List.length_map] using h.2⟩

lemma bypass_fan (C : Circuit) (n k a : ℕ) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (bypass C n k a) := by
  intro g hg
  change g ∈ C.gates.take k ++
    (C.gates.drop (k + 1)).map (renameGate (n + k) a) at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
    exact renameGate_fan old _ _ (h old (List.mem_of_mem_drop hold))

lemma appendOr_fan (C : Circuit) (n b : ℕ) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (appendOr C n b) := by
  intro g hg
  change g ∈ C.gates ++ [⟨GateOp.or, [C.output, b]⟩] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · simp only [List.mem_singleton] at hg
    subst g
    simp

lemma move_or (C : Circuit) (n k a b : ℕ)
    (hk : k < C.size) (ha : a < n + k) (hb : b < n + k)
    (gate : C.gates.get ⟨k, hk⟩ = ⟨GateOp.or, [a, b]⟩)
    (certifies : ∀ x : List Bool, x.length = n →
      ((C.gates.take k).foldl step x).getD b false = true → C.eval x = true) :
    ∃ D : Circuit, D.size = C.size ∧
      (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo D) ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let D := appendOr (bypass C n k a) n b
  refine ⟨D, ?_, fun h => appendOr_fan _ _ _ (bypass_fan _ _ _ _ h), ?_⟩
  · exact (appendOr_size _ _ _).trans (bypass_size C n k a hk)
  · intro x hx
    change (appendOr (bypass C n k a) n b).eval x = _
    rw [appendOr_eval _ _ _ _ hx, bypass_prefix C n k a b x hk hx hb]
    by_cases hval : ((C.gates.take k).foldl step x).getD b false = false
    · rw [hval, Bool.or_false]
      apply bypass_eval C n k a x hk ha hx
      rw [gate]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, id_eq, hval, Bool.or_false]
    · have htrue : ((C.gates.take k).foldl step x).getD b false = true :=
        Bool.eq_true_of_not_eq_false hval
      rw [htrue, Bool.or_true, certifies x hx htrue]


lemma move_certified (C : Circuit) (n k a b : ℕ)
    (hk : k < C.size) (ha : a < n + k) (hb : b < n + k)
    (copies : ∀ x : List Bool, x.length = n →
      ((C.gates.take k).foldl step x).getD b false = false →
      (C.gates.get ⟨k, hk⟩).op.eval
        ((C.gates.get ⟨k, hk⟩).inputs.map fun i =>
          ((C.gates.take k).foldl step x).getD i false) =
        ((C.gates.take k).foldl step x).getD a false)
    (certifies : ∀ x : List Bool, x.length = n →
      ((C.gates.take k).foldl step x).getD b false = true → C.eval x = true) :
    ∃ D : Circuit, D.size = C.size ∧
      (PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.FanInTwo D) ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  let D := appendOr (bypass C n k a) n b
  refine ⟨D, ?_, fun h => appendOr_fan _ _ _ (bypass_fan _ _ _ _ h), ?_⟩
  · exact (appendOr_size _ _ _).trans (bypass_size C n k a hk)
  · intro x hx
    change (appendOr (bypass C n k a) n b).eval x = _
    rw [appendOr_eval _ _ _ _ hx, bypass_prefix C n k a b x hk hx hb]
    by_cases hval : ((C.gates.take k).foldl step x).getD b false = false
    · rw [hval, Bool.or_false]
      exact bypass_eval C n k a x hk ha hx (copies x hx hval)
    · have htrue : ((C.gates.take k).foldl step x).getD b false = true :=
        Bool.eq_true_of_not_eq_false hval
      rw [htrue, Bool.or_true, certifies x hx htrue]

end PEqualNP.Outside.L_meta_1884_aux.Move
