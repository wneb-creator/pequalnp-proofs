import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17709

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem spec : ∀ (gs : List Gate) (x : List Bool) (val : ℕ → Bool),
    (∀ i, i < x.length → x.getD i false = val i) →
    (∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < x.length + j) →
    (∀ j (hj : j < gs.length), (gs[j]).op.eval ((gs[j]).inputs.map val) = val (x.length + j)) →
    ∀ i, i < x.length + gs.length → (gs.foldl step x).getD i false = val i := by
  intro gs
  induction gs with
  | nil => intro x val hx _ _ i hi; simpa using hx i (by simpa using hi)
  | cons g gs ih =>
    intro x val hx hr hv i hi
    simp only [List.foldl_cons]
    have hlen : (step x g).length = x.length + 1 := by simp [step]
    apply ih (step x g) val
    · intro i hi'
      rw [hlen] at hi'
      simp only [step, getD_snoc]
      split_ifs with h
      · subst h
        have h0 := hv 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        rw [← h0]
        congr 1
        apply List.map_congr_left
        intro k hk
        have := hr 0 (by simp) k (by simpa using hk)
        exact hx k (by simpa using this)
      · exact hx i (by omega)
    · intro j hj k hk
      have := hr (j + 1) (by simp; omega) k (by simpa using hk)
      rw [hlen]
      omega
    · intro j hj
      have := hv (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this, hlen]
      congr 1
      omega
    · rw [hlen]; simp at hi; omega

def zv (n u v i : ℕ) : Bool := decide (i = u) || decide (n + i = v)
def wv (n u v i : ℕ) : Bool := decide (i = v) || decide (n + i = u)
def Pv (n u v k : ℕ) : Bool := (List.range k).any (wv n u v)
def Qv (n u v k : ℕ) : Bool := (List.range (n - k)).any (fun t => wv n u v (k + t))
def Sv (n u v i : ℕ) : Bool := Pv n u v i || Qv n u v (i + 1)
def Tv (n u v i : ℕ) : Bool := zv n u v i && Sv n u v i
def Ov (n u v k : ℕ) : Bool := (List.range (k + 1)).any (Tv n u v)

def val (n u v i : ℕ) : Bool :=
  if i < 2 * n then decide (i = u)
  else if i < 4 * n then decide (i - 2 * n = v)
  else if i < 5 * n then zv n u v (i - 4 * n)
  else if i < 6 * n then wv n u v (i - 5 * n)
  else if i < 7 * n - 2 then Pv n u v (i - 6 * n + 2)
  else if i < 8 * n - 4 then Qv n u v (n - 2 - (i - (7 * n - 2)))
  else if i < 9 * n - 6 then Sv n u v (i - (8 * n - 4) + 1)
  else if i < 10 * n - 6 then Tv n u v (i - (9 * n - 6))
  else Ov n u v (i - (10 * n - 6) + 1)

def pw (n k : ℕ) : ℕ := if k = 1 then 5 * n else 6 * n + (k - 2)
def qw (n k : ℕ) : ℕ := if k = n - 1 then 6 * n - 1 else 7 * n - 2 + (n - 2 - k)
def sw (n i : ℕ) : ℕ := if i = 0 then qw n 1 else if i = n - 1 then pw n (n - 1) else 8 * n - 4 + (i - 1)

def gt (n j : ℕ) : Gate :=
  if j < n then ⟨GateOp.or, [j, 3 * n + j]⟩
  else if j < 2 * n then ⟨GateOp.or, [2 * n + (j - n), n + (j - n)]⟩
  else if j < 3 * n - 2 then ⟨GateOp.or, [pw n (j - 2 * n + 1), 5 * n + (j - 2 * n + 1)]⟩
  else if j < 4 * n - 4 then
    ⟨GateOp.or, [5 * n + (n - 2 - (j - (3 * n - 2))), qw n (n - 1 - (j - (3 * n - 2)))]⟩
  else if j < 5 * n - 6 then ⟨GateOp.or, [pw n (j - (4 * n - 4) + 1), qw n (j - (4 * n - 4) + 2)]⟩
  else if j < 6 * n - 6 then ⟨GateOp.and, [4 * n + (j - (5 * n - 6)), sw n (j - (5 * n - 6))]⟩
  else if j = 6 * n - 6 then ⟨GateOp.or, [9 * n - 6, 9 * n - 5]⟩
  else ⟨GateOp.or, [10 * n - 6 + (j - (6 * n - 6)) - 1, 9 * n - 6 + (j - (6 * n - 6) + 1)]⟩

theorem pw_lt (n k : ℕ) (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ n - 1) : pw n k < 7 * n - 2 := by
  unfold pw; split_ifs <;> omega

theorem qw_lt (n k : ℕ) (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ n - 1) : qw n k < 8 * n - 4 := by
  unfold qw; split_ifs <;> omega

theorem reads (n j : ℕ) (hn : 2 ≤ n) (hj : j < 7 * n - 7) : ∀ i ∈ (gt n j).inputs, i < 4 * n + j := by
  intro i hi
  unfold gt at hi
  split_ifs at hi with h1 h2 h3 h4 h5 h6 h7 <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;> rcases hi with rfl | rfl
  all_goals first
    | omega
    | (unfold pw; split_ifs <;> omega)
    | (unfold qw; split_ifs <;> omega)
    | (unfold sw qw pw; split_ifs <;> omega)

theorem val_left (n u v i : ℕ) (h : i < 2 * n) : val n u v i = decide (i = u) := by
  unfold val; rw [if_pos h]

theorem val_right (n u v k : ℕ) (h : k < 2 * n) : val n u v (2 * n + k) = decide (k = v) := by
  unfold val; rw [if_neg (by omega), if_pos (by omega)]; congr 1; simp

theorem val_z (n u v i : ℕ) (h : i < n) : val n u v (4 * n + i) = zv n u v i := by
  unfold val; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem val_w (n u v i : ℕ) (h : i < n) : val n u v (5 * n + i) = wv n u v i := by
  unfold val; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 1; omega

theorem val_P (n u v t : ℕ) (h : t + 2 < n) : val n u v (6 * n + t) = Pv n u v (t + 2) := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem val_Q (n u v t : ℕ) (h : t + 2 < n) : val n u v (7 * n - 2 + t) = Qv n u v (n - 2 - t) := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  congr 1; omega

theorem val_S (n u v t : ℕ) (h : t + 2 < n) : val n u v (8 * n - 4 + t) = Sv n u v (t + 1) := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem val_T (n u v i : ℕ) (hn : 2 ≤ n) (h : i < n) : val n u v (9 * n - 6 + i) = Tv n u v i := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem val_O (n u v k : ℕ) (hn : 2 ≤ n) (h1 : 1 ≤ k) : val n u v (10 * n - 6 + (k - 1)) = Ov n u v k := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega

theorem Pv_succ (n u v k : ℕ) : Pv n u v (k + 1) = (Pv n u v k || wv n u v k) := by
  simp [Pv, List.range_succ, List.any_append]

theorem Pv_one (n u v : ℕ) : Pv n u v 1 = wv n u v 0 := by
  simp [Pv]

theorem Qv_cons (n u v k : ℕ) (h : k < n) : Qv n u v k = (wv n u v k || Qv n u v (k + 1)) := by
  unfold Qv
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, show n - (k + 1) = m by omega, List.range_succ_eq_map, List.any_cons, List.any_map]
  have hf : ((fun t => wv n u v (k + t)) ∘ Nat.succ) = fun t => wv n u v (k + 1 + t) := by
    funext t; simp only [Function.comp_apply]; congr 1; omega
  rw [hf, Nat.add_zero]

theorem Qv_last (n u v : ℕ) (hn : 1 ≤ n) : Qv n u v (n - 1) = wv n u v (n - 1) := by
  unfold Qv
  rw [show n - (n - 1) = 1 by omega]
  simp

theorem Qv_n (n u v : ℕ) : Qv n u v n = false := by
  simp [Qv]

theorem val_pw (n u v k : ℕ) (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ n - 1) :
    val n u v (pw n k) = Pv n u v k := by
  unfold pw
  split_ifs with h
  · subst h
    rw [show 5 * n = 5 * n + 0 by omega, val_w n u v 0 (by omega), Pv_one]
  · rw [val_P n u v (k - 2) (by omega)]
    congr 1; omega

theorem val_qw (n u v k : ℕ) (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ n - 1) :
    val n u v (qw n k) = Qv n u v k := by
  unfold qw
  split_ifs with h
  · subst h
    rw [show 6 * n - 1 = 5 * n + (n - 1) by omega, val_w n u v (n - 1) (by omega), Qv_last n u v (by omega)]
  · rw [val_Q n u v (n - 2 - k) (by omega)]
    congr 1; omega

theorem val_sw (n u v i : ℕ) (hn : 2 ≤ n) (hi : i < n) : val n u v (sw n i) = Sv n u v i := by
  unfold sw
  split_ifs with h1 h2
  · subst h1
    rw [val_qw n u v 1 hn (by omega) (by omega)]
    simp [Sv, Pv]
  · subst h2
    rw [val_pw n u v (n - 1) hn (by omega) (by omega)]
    simp [Sv, show n - 1 + 1 = n by omega, Qv_n]
  · rw [val_S n u v (i - 1) (by omega)]
    congr 1; omega

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

theorem gate_ok (n u v j : ℕ) (hn : 2 ≤ n) (hj : j < 7 * n - 7) :
    (gt n j).op.eval ((gt n j).inputs.map (val n u v)) = val n u v (4 * n + j) := by
  unfold gt
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [val_left n u v j (by omega), show 3 * n + j = 2 * n + (n + j) by omega,
      val_right n u v (n + j) (by omega), val_z n u v j h1]
    rfl
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [val_right n u v (j - n) (by omega), val_left n u v (n + (j - n)) (by omega),
      show 4 * n + j = 5 * n + (j - n) by omega, val_w n u v (j - n) (by omega)]
    simp only [wv]
    try (congr 2 <;> simp only [decide_eq_decide] <;> omega)
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [val_pw n u v (j - 2 * n + 1) hn (by omega) (by omega), show 5 * n + (j - 2 * n + 1) = 5 * n + (j - 2 * n + 1) from rfl,
      val_w n u v (j - 2 * n + 1) (by omega), ← Pv_succ, show 4 * n + j = 6 * n + (j - 2 * n) by omega,
      val_P n u v (j - 2 * n) (by omega)]
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [val_w n u v (n - 2 - (j - (3 * n - 2))) (by omega), val_qw n u v (n - 1 - (j - (3 * n - 2))) hn (by omega) (by omega),
      show 4 * n + j = 7 * n - 2 + (j - (3 * n - 2)) by omega, val_Q n u v (j - (3 * n - 2)) (by omega),
      Qv_cons n u v (n - 2 - (j - (3 * n - 2))) (by omega)]
    congr 2; omega
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [val_pw n u v (j - (4 * n - 4) + 1) hn (by omega) (by omega),
      val_qw n u v (j - (4 * n - 4) + 2) hn (by omega) (by omega),
      show 4 * n + j = 8 * n - 4 + (j - (4 * n - 4)) by omega, val_S n u v (j - (4 * n - 4)) (by omega)]
    rfl
  · simp only [List.map_cons, List.map_nil, eval_and2]
    rw [val_z n u v (j - (5 * n - 6)) (by omega), val_sw n u v (j - (5 * n - 6)) hn (by omega),
      show 4 * n + j = 9 * n - 6 + (j - (5 * n - 6)) by omega, val_T n u v (j - (5 * n - 6)) hn (by omega)]
    rfl
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [show 9 * n - 6 = 9 * n - 6 + 0 by omega, val_T n u v 0 hn (by omega),
      show 9 * n - 5 = 9 * n - 6 + 1 by omega, val_T n u v 1 hn (by omega),
      show 4 * n + j = 10 * n - 6 + (1 - 1) by omega, val_O n u v 1 hn (by omega)]
    simp [Ov, List.range_succ]
  · simp only [List.map_cons, List.map_nil, eval_or2]
    rw [show 10 * n - 6 + (j - (6 * n - 6)) - 1 = 10 * n - 6 + ((j - (6 * n - 6)) - 1) by omega,
      val_O n u v (j - (6 * n - 6)) hn (by omega),
      val_T n u v (j - (6 * n - 6) + 1) hn (by omega),
      show 4 * n + j = 10 * n - 6 + ((j - (6 * n - 6) + 1) - 1) by omega,
      val_O n u v (j - (6 * n - 6) + 1) hn (by omega)]
    simp only [Ov, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    try (congr 2 <;> omega)

theorem Pv_iff (n u v k : ℕ) : Pv n u v k = true ↔ ∃ j, j < k ∧ wv n u v j = true := by
  simp [Pv, List.any_eq_true]

theorem Qv_iff (n u v k : ℕ) : Qv n u v k = true ↔ ∃ j, k ≤ j ∧ j < n ∧ wv n u v j = true := by
  simp only [Qv, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨k + t, by omega, by omega, h⟩
  · rintro ⟨j, h1, h2, h⟩
    exact ⟨j - k, by omega, by rw [show k + (j - k) = j by omega]; exact h⟩

theorem Sv_iff (n u v i : ℕ) (hi : i < n) :
    Sv n u v i = true ↔ ∃ j, j < n ∧ j ≠ i ∧ wv n u v j = true := by
  simp only [Sv, Bool.or_eq_true, Pv_iff, Qv_iff]
  constructor
  · rintro (⟨j, h1, h⟩ | ⟨j, h1, h2, h⟩)
    · exact ⟨j, by omega, by omega, h⟩
    · exact ⟨j, h2, by omega, h⟩
  · rintro ⟨j, h1, h2, h⟩
    rcases Nat.lt_or_gt_of_ne h2 with h3 | h3
    · exact Or.inl ⟨j, h3, h⟩
    · exact Or.inr ⟨j, by omega, h1, h⟩

theorem Ov_iff (n u v : ℕ) (hn : 1 ≤ n) :
    Ov n u v (n - 1) = true ↔ ∃ i, i < n ∧ zv n u v i = true ∧ Sv n u v i = true := by
  simp only [Ov, List.any_eq_true, List.mem_range, Tv, Bool.and_eq_true]
  rw [show n - 1 + 1 = n by omega]

theorem zv_iff (n u v i : ℕ) : zv n u v i = true ↔ (i = u ∨ n + i = v) := by
  simp [zv]

theorem wv_iff (n u v j : ℕ) : wv n u v j = true ↔ (j = v ∨ n + j = u) := by
  simp [wv]

theorem divmod_hi (n u : ℕ) (h1 : n ≤ u) (h2 : u < 2 * n) : u / n = 1 ∧ u % n = u - n := by
  constructor
  · apply Nat.div_eq_of_lt_le <;> omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem semantic (n u v : ℕ) (hn : 2 ≤ n) (hu : u < 2 * n) (hv : v < 2 * n) :
    Ov n u v (n - 1) = decide (u / n = v / n ∧ u % n ≠ v % n) := by
  rw [Bool.eq_iff_iff, Ov_iff n u v (by omega), decide_eq_true_eq]
  rcases Nat.lt_or_ge u n with hu1 | hu1 <;> rcases Nat.lt_or_ge v n with hv1 | hv1
  · rw [Nat.div_eq_of_lt hu1, Nat.div_eq_of_lt hv1, Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hv1]
    constructor
    · rintro ⟨i, hi, hz, hs⟩
      rw [Sv_iff n u v i hi] at hs
      obtain ⟨j, hj, hji, hw⟩ := hs
      rw [zv_iff] at hz; rw [wv_iff] at hw
      omega
    · rintro ⟨-, h⟩
      refine ⟨u, hu1, by rw [zv_iff]; omega, ?_⟩
      rw [Sv_iff n u v u hu1]
      exact ⟨v, hv1, by omega, by rw [wv_iff]; omega⟩
  · obtain ⟨hd, hm⟩ := divmod_hi n v hv1 hv
    rw [Nat.div_eq_of_lt hu1, hd]
    constructor
    · rintro ⟨i, hi, hz, hs⟩
      rw [Sv_iff n u v i hi] at hs
      obtain ⟨j, hj, hji, hw⟩ := hs
      rw [zv_iff] at hz; rw [wv_iff] at hw
      omega
    · rintro ⟨h, -⟩; omega
  · obtain ⟨hd, hm⟩ := divmod_hi n u hu1 hu
    rw [Nat.div_eq_of_lt hv1, hd]
    constructor
    · rintro ⟨i, hi, hz, hs⟩
      rw [zv_iff] at hz
      omega
    · rintro ⟨h, -⟩; omega
  · obtain ⟨hd, hm⟩ := divmod_hi n u hu1 hu
    obtain ⟨hd', hm'⟩ := divmod_hi n v hv1 hv
    rw [hd, hd', hm, hm']
    constructor
    · rintro ⟨i, hi, hz, hs⟩
      rw [Sv_iff n u v i hi] at hs
      obtain ⟨j, hj, hji, hw⟩ := hs
      rw [zv_iff] at hz; rw [wv_iff] at hw
      omega
    · rintro ⟨-, h⟩
      refine ⟨v - n, by omega, by rw [zv_iff]; omega, ?_⟩
      rw [Sv_iff n u v (v - n) (by omega)]
      exact ⟨u - n, by omega, by omega, by rw [wv_iff]; omega⟩

theorem main (n : ℕ) (hn : 2 ≤ n) :
    RepSizeAtMost (fun u v : Fin (2 * n) => decide (u.val / n = v.val / n ∧ u.val % n ≠ v.val % n)) (7 * n - 7) := by
  refine ⟨⟨(List.range (7 * n - 7)).map (gt n), 11 * n - 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨j, _, rfl⟩ := hg
    unfold gt
    split_ifs <;> simp
  · simp [Circuit.size]
  · intro u v
    have hx : (oneEach u v).length = 4 * n := by
      simp only [oneEach, List.length_append, List.length_ofFn]; omega
    have key := spec ((List.range (7 * n - 7)).map (gt n)) (oneEach u v) (val n u.val v.val) ?_ ?_ ?_
      (11 * n - 8) (by simp only [List.length_map, List.length_range]; omega)
    · simp only [Circuit.eval, wires_eq]
      rw [key, show 11 * n - 8 = 10 * n - 6 + ((n - 1) - 1) by omega, val_O n u.val v.val (n - 1) hn (by omega)]
      exact semantic n u.val v.val hn u.isLt v.isLt
    · intro i hi
      rw [hx] at hi
      simp only [oneEach]
      by_cases h : i < 2 * n
      · rw [List.getD_append _ _ _ _ (by simpa using h), val_left n u.val v.val i h]
        simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff]
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_ofFn]
        rw [show i = 2 * n + (i - 2 * n) by omega, val_right n u.val v.val (i - 2 * n) (by omega)]
        simp [List.getD_eq_getElem?_getD, show i - 2 * n < 2 * n by omega, Fin.ext_iff]
    · intro j hj i hi
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range] at hi
      rw [hx]
      exact reads n j hn hj i hi
    · intro j hj
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range]
      rw [hx]
      exact gate_ok n u.val v.val j hn hj

end PEqualNP.Outside.L_meta_17709

theorem PEqualNP.Outside.L_meta_17709 : (∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (2 * n) => decide (u.val / n = v.val / n ∧ u.val % n ≠ v.val % n)) (7 * n - 7)) := by
  intro n hn
  exact PEqualNP.Outside.L_meta_17709.main n hn
