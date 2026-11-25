import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772.Normal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C i k hk).1 h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

open PEqualNP.EdgeOwnership in
lemma pi_symm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

open PEqualNP.EdgeOwnership in
lemma pi_val {n : ℕ} (u v : Fin n) (w : Fin n) : pairInput u v w = true ↔ (w = u ∨ w = v) := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pi_le {n : ℕ} (x u v : Fin n) (h : x = u ∨ x = v) :
    ∀ w, pairInput x x w = true → pairInput u v w = true := by
  intro w hw
  rw [pi_val] at hw ⊢
  rw [or_self] at hw
  rw [hw]
  exact h


open PEqualNP.EdgeOwnership

def F {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def Tb (n : ℕ) (gs : List Gate) (w : ℕ) : Prop :=
  ∃ z : Fin n, val gs w (pairInput z z) = true

def Snd {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].op = GateOp.and →
    ∀ x : Fin n → Bool, val gs (n + j) x = true → F G x

def Cmp {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val gs o x = true ↔ F G x

def Absorb (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ hj : j < gs.length, gs[j].op = GateOp.or ∧ Tb n gs (n + j) ∧
    ∃ h ∈ gs[j].inputs, h < n + j ∧ ¬ Tb n gs h

def BadAnd (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ hj : j < gs.length, gs[j].op = GateOp.and ∧
    ∃ i ∈ gs[j].inputs, ¬ (i < n + j ∧ Tb n gs i)

def Defect (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  Absorb n gs j ∨ BadAnd n gs j

lemma F_single {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) : ¬ F G (pairInput z z) := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [pi_val, or_self] at hu hv
  rw [hu, hv] at huv
  exact huv.ne rfl

lemma soundw {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) :
    ∀ w, ¬ Tb n gs w → ∀ x : Fin n → Bool, val gs w x = true → F G x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hT x h
    by_cases hwn : w < n
    · exfalso
      apply hT
      refine ⟨⟨w, hwn⟩, ?_⟩
      rw [val_input gs _ w hwn, pi_val]
      exact Or.inl rfl
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gs.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h hT
        rcases (legal gs[w - n] (List.getElem_mem hi)).1 with ha | ho
        · exact hs (w - n) hi ha x h
        · obtain ⟨p, hp, hplt, hv⟩ := (val_or gs x (w - n) hi ho).1 h
          apply ih p (by omega) _ x hv
          rintro ⟨z, hz⟩
          exact hT ⟨z, (val_or gs _ (w - n) hi ho).2 ⟨p, hp, hplt, hz⟩⟩

lemma trans_gen {n : ℕ} (gs gs' : List Gate) (hlen : gs'.length = gs.length)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (L : ℕ) (hsame : ∀ k, k ≠ L → gs'[k]? = gs[k]?) (x : Fin n → Bool)
    (hL : (∀ i, i < n + L → val gs i x = true → val gs' i x = true) →
      val gs (n + L) x = true → val gs' (n + L) x = true) :
    ∀ w, val gs w x = true → val gs' w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gs' _ w hwn]
      rw [val_input gs _ w hwn] at h
      exact h
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gs.length := by omega
        have hi' : w - n < gs'.length := by omega
        have he : n + (w - n) = w := by omega
        by_cases hk : w - n = L
        · have key := hL (fun i hi2 hv => ih i (by omega) hv)
          have he2 : n + L = w := by omega
          rw [he2] at key
          exact key h
        · have hg : gs'[w - n] = gs[w - n] := by
            have h1 := hsame (w - n) hk
            rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h1
            exact Option.some.inj h1
          rw [← he] at h ⊢
          rcases (legal gs[w - n] (List.getElem_mem hi)).1 with ha | ho
          · apply (val_and gs' x (w - n) hi' (by rw [hg]; exact ha)).2
            intro j hj
            rw [hg] at hj
            obtain ⟨hjlt, hjv⟩ := (val_and gs x (w - n) hi ha).1 h j hj
            exact ⟨hjlt, ih j (by omega) hjv⟩
          · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gs x (w - n) hi ho).1 h
            exact (val_or gs' x (w - n) hi' (by rw [hg]; exact ho)).2
              ⟨j, by rw [hg]; exact hj, hjlt, ih j (by omega) hv⟩

lemma step_iff {n : ℕ} (A B : List Gate) (ka kb : ℕ) (hka : ka < A.length)
    (hkb : kb < B.length) (hop : A[ka].op = B[kb].op)
    (hlegal : B[kb].op = GateOp.and ∨ B[kb].op = GateOp.or)
    (f : ℕ → ℕ) (hin : A[ka].inputs = B[kb].inputs.map f) (x : Fin n → Bool)
    (hloc : ∀ j ∈ B[kb].inputs,
      ((f j < n + ka ∧ val A (f j) x = true) ↔ (j < n + kb ∧ val B j x = true))) :
    val A (n + ka) x = true ↔ val B (n + kb) x = true := by
  rcases hlegal with ha | ho
  · rw [val_and A x ka hka (by rw [hop]; exact ha), val_and B x kb hkb ha, hin]
    constructor
    · intro H j hj
      exact (hloc j hj).1 (H (f j) (List.mem_map.2 ⟨j, hj, rfl⟩))
    · intro H j' hj'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hj'
      exact (hloc j hj).2 (H j hj)
  · rw [val_or A x ka hka (by rw [hop]; exact ho), val_or B x kb hkb ho, hin]
    constructor
    · rintro ⟨j', hj', H⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hj'
      exact ⟨j, hj, (hloc j hj).1 H⟩
    · rintro ⟨j, hj, H⟩
      exact ⟨f j, List.mem_map.2 ⟨j, hj, rfl⟩, (hloc j hj).2 H⟩

lemma two_mem (l : List ℕ) (hl : l.length ≤ 2) (p h : ℕ) (hp : p ∈ l) (hh : h ∈ l)
    (hne : p ≠ h) : ∀ i ∈ l, i = p ∨ i = h := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hp
  · simp only [List.mem_singleton] at hp hh
    exact absurd (hp.trans hh.symm) hne
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hh hi
    omega
  · simp only [List.length_cons] at hl
    omega

def rd (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def er (n : ℕ) (gs : List Gate) (m p : ℕ) : List Gate :=
  (List.range (gs.length - 1)).map fun j =>
    if j < m then gs.getD j ⟨GateOp.or, []⟩
    else ⟨(gs.getD (j + 1) ⟨GateOp.or, []⟩).op,
      (gs.getD (j + 1) ⟨GateOp.or, []⟩).inputs.map (rd n m p)⟩

lemma er_len (n : ℕ) (gs : List Gate) (m p : ℕ) : (er n gs m p).length = gs.length - 1 := by
  simp [er]

lemma er_lt (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : j < m) (hj : j < gs.length)
    (hj' : j < (er n gs m p).length) : (er n gs m p)[j] = gs[j] := by
  simp [er, hjm, List.getD_eq_getElem?_getD, hj]

lemma er_ge (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : m ≤ j) (hj : j + 1 < gs.length)
    (hj' : j < (er n gs m p).length) :
    (er n gs m p)[j] = ⟨gs[j + 1].op, gs[j + 1].inputs.map (rd n m p)⟩ := by
  simp [er, Nat.not_lt.2 hjm, List.getD_eq_getElem?_getD, hj]

lemma rd_small (n m p a : ℕ) (h : a < n + m) : rd n m p a = a := by
  unfold rd
  split_ifs <;> omega

lemma rd_at (n m p : ℕ) : rd n m p (n + m) = p := by
  simp [rd]

lemma rd_succ (n m p k : ℕ) (h : m ≤ k) : rd n m p (n + (k + 1)) = n + k := by
  unfold rd
  split_ifs <;> omega

lemma rd_lt (n m p a k : ℕ) (hp : p < n + m) (h : m ≤ k) :
    rd n m p a < n + k ↔ a < n + (k + 1) := by
  unfold rd
  split_ifs <;> omega

lemma er_pre {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p : ℕ) (hm : m < gs.length) (x : Fin n → Bool) :
    ∀ i, i < n + m → (val (er n gs m p) i x = true ↔ val gs i x = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · rw [val_input _ _ i hin, val_input _ _ i hin]
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk : k < gs.length := by omega
      have hkE : k < (er n gs m p).length := by rw [er_len]; omega
      have hg := er_lt n gs m p k (by omega) hk hkE
      apply step_iff (er n gs m p) gs k k hkE hk (by rw [hg])
        (legal gs[k] (List.getElem_mem hk)).1 id (by rw [hg]; simp) x
      intro j _
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (ih j (by simpa using h1) (by simp at h1; omega)).1 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (ih j h1 (by omega)).2 h2⟩

lemma erase_iff {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p h : ℕ) (hm : m < gs.length) (hp : p < n + m)
    (hor : gs[m].op = GateOp.or) (hpin : p ∈ gs[m].inputs)
    (two : ∀ i ∈ gs[m].inputs, i = p ∨ i = h)
    (x : Fin n → Bool) (hS : ¬ (val gs h x = true)) :
    ∀ i, i < n + gs.length →
      (val (er n gs m p) (rd n m p i) x = true ↔ val gs i x = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases him : i < n + m
    · rw [rd_small n m p i him]
      exact er_pre gs legal m p hm x i him
    · by_cases hieq : i = n + m
      · subst hieq
        rw [rd_at]
        have e1 := ih p hp (by omega)
        rw [rd_small n m p p hp] at e1
        rw [e1, val_or gs x m hm hor]
        constructor
        · intro hv
          exact ⟨p, hpin, hp, hv⟩
        · rintro ⟨j, hj, hjlt, hv⟩
          rcases two j hj with e | e
          · rw [e] at hv
            exact hv
          · rw [e] at hv
            exact absurd hv hS
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + (k + 1) := ⟨i - n - 1, by omega⟩
        have hmk : m ≤ k := by omega
        have hk : k + 1 < gs.length := by omega
        have hkE : k < (er n gs m p).length := by rw [er_len]; omega
        have hg := er_ge n gs m p k hmk hk hkE
        rw [rd_succ n m p k hmk]
        apply step_iff (er n gs m p) gs k (k + 1) hkE hk (by rw [hg])
          (legal gs[k + 1] (List.getElem_mem hk)).1 (rd n m p) (by rw [hg]) x
        intro j _
        constructor
        · rintro ⟨h1, h2⟩
          have hj := (rd_lt n m p j k hp hmk).1 h1
          exact ⟨hj, (ih j hj (by omega)).1 h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(rd_lt n m p j k hp hmk).2 h1, (ih j h1 (by omega)).2 h2⟩

lemma conv_step {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) (hc : Cmp G gs o) (L : ℕ) (hb : BadAnd n gs L)
    (hno : ∀ j, L < j → ¬ Defect n gs j) :
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, L ≤ j → ¬ Defect n gs1 j := by
  obtain ⟨hL, hand, i0, hi0, hbad⟩ := hb
  obtain ⟨gs1, hlen, ⟨hL1, g1L⟩, same, legal1⟩ : ∃ gs1 : List Gate, gs1.length = gs.length ∧
      (∃ h : L < gs1.length, gs1[L] = ⟨GateOp.or, [i0]⟩) ∧
      (∀ k, k ≠ L → gs1[k]? = gs[k]?) ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
    refine ⟨gs.set L ⟨GateOp.or, [i0]⟩, by simp, ⟨by simpa using hL, by simp⟩, ?_, ?_⟩
    · intro k hk
      exact List.getElem?_set_ne (Ne.symm hk)
    · intro g hg
      rcases List.mem_or_eq_of_mem_set hg with h | h
      · exact legal g h
      · rw [h]
        exact ⟨Or.inr rfl, by simp⟩
  have sameE : ∀ k (hk : k < gs.length) (hk1 : k < gs1.length), k ≠ L → gs1[k] = gs[k] := by
    intro k hk hk1 hne
    have h1 := same k hne
    rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk] at h1
    exact Option.some.inj h1
  have hor1 : gs1[L].op = GateOp.or := by rw [g1L]
  have up : ∀ (x : Fin n → Bool) w, val gs w x = true → val gs1 w x = true := by
    intro x
    apply trans_gen gs gs1 hlen legal L same x
    intro tr h
    obtain ⟨h1, h2⟩ := (val_and gs x L hL hand).1 h i0 hi0
    exact (val_or gs1 x L hL1 hor1).2 ⟨i0, by rw [g1L]; simp, h1, tr i0 h1 h2⟩
  have down : ∀ (x : Fin n → Bool), ¬ F G x → ∀ w, val gs1 w x = true → val gs w x = true := by
    intro x hF
    apply trans_gen gs1 gs hlen.symm legal1 L (fun k hk => (same k hk).symm) x
    intro tr h
    exfalso
    obtain ⟨i, hi, hlt, hv⟩ := (val_or gs1 x L hL1 hor1).1 h
    rw [g1L] at hi
    simp only [List.mem_singleton] at hi
    rw [hi] at hlt hv
    exact hF (soundw G gs legal hs i0 (fun hT => hbad ⟨hlt, hT⟩) x (tr i0 hlt hv))
  have Tbeq : ∀ w, Tb n gs1 w ↔ Tb n gs w := by
    intro w
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, down _ (F_single G z) w hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, up _ w hz⟩
  refine ⟨gs1, o, hlen, legal1, ?_, ?_, ?_⟩
  · intro j hj ha x hv
    by_cases hF : F G x
    · exact hF
    · have hjL : j ≠ L := by
        intro e
        subst e
        rw [hor1] at ha
        exact GateOp.noConfusion ha
      have hj0 : j < gs.length := by omega
      rw [sameE j hj0 hj hjL] at ha
      exact hs j hj0 ha x (down x hF (n + j) hv)
  · intro x
    constructor
    · intro h
      by_contra hF
      exact hF ((hc x).1 (down x hF o h))
    · intro hF
      exact up x o ((hc x).2 hF)
  · intro j hj hd
    by_cases hjL : j = L
    · subst hjL
      rcases hd with ⟨_, _, hT, _⟩ | ⟨_, ha, _⟩
      · obtain ⟨z, hz⟩ := (Tbeq _).1 hT
        exact F_single G z (hs j hL hand _ hz)
      · rw [hor1] at ha
        exact GateOp.noConfusion ha
    · apply hno j (by omega)
      rcases hd with ⟨hj1, hor, hT, h, hh, hlt, hnT⟩ | ⟨hj1, ha, i, hi, hbd⟩
      · have hj0 : j < gs.length := by omega
        rw [sameE j hj0 hj1 hjL] at hor hh
        exact Or.inl ⟨hj0, hor, (Tbeq _).1 hT, h, hh, hlt, fun t => hnT ((Tbeq h).2 t)⟩
      · have hj0 : j < gs.length := by omega
        rw [sameE j hj0 hj1 hjL] at ha hi
        exact Or.inr ⟨hj0, ha, i, hi, fun t => hbd ⟨t.1, (Tbeq i).2 t.2⟩⟩

lemma lift_step {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) (hc : Cmp G gs o) (m : ℕ) (hab : Absorb n gs m)
    (hno : ∀ j, m < j → ¬ Defect n gs j) :
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, m ≤ j → ¬ Defect n gs1 j := by
  obtain ⟨hm, hor, ⟨z0, hz0⟩, h, hh, hlt, hnT⟩ := hab
  obtain ⟨p, hpin, hp, hpv⟩ := (val_or gs _ m hm hor).1 hz0
  have hne : p ≠ h := by
    intro e
    rw [e] at hpv
    exact hnT ⟨z0, hpv⟩
  have two := two_mem gs[m].inputs (legal gs[m] (List.getElem_mem hm)).2 p h hpin hh hne
  have hElen := er_len n gs m p
  have hsh : ∀ x : Fin n → Bool, val gs h x = true → F G x := soundw G gs legal hs h hnT
  have hS0 : ∀ z : Fin n, ¬ (val gs h (pairInput z z) = true) := fun z hz => hnT ⟨z, hz⟩
  have pre1 : ∀ w, w < n + (er n gs m p).length → ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) w x = val (er n gs m p) w x := by
    intro w hw x
    exact wf_prefix (er n gs m p) [(Gate.mk GateOp.or [rd n m p o, h])] (List.ofFn x) w
      (by rw [List.length_ofFn]; exact hw)
  have rdl : ∀ i, i < n + gs.length → rd n m p i < n + (er n gs m p).length := by
    intro i hi
    rw [hElen]
    unfold rd
    split_ifs <;> omega
  have rdl' : ∀ i, rd n m p i < n + (er n gs m p).length → i < n + gs.length := by
    intro i hi
    rw [hElen] at hi
    unfold rd at hi
    split_ifs at hi <;> omega
  have eqv : ∀ x : Fin n → Bool, ¬ (val gs h x = true) → ∀ i, i < n + gs.length →
      (val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p i) x = true ↔
        val gs i x = true) := by
    intro x hS i hi
    rw [pre1 _ (rdl i hi)]
    exact erase_iff gs legal m p h hm hp hor hpin two x hS i hi
  have hval : ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) h x = val gs h x := by
    intro x
    rw [pre1 h (by rw [hElen]; omega)]
    have := er_pre gs legal m p hm x h hlt
    exact Bool.eq_iff_iff.2 this
  have Tbeq : ∀ i, i < n + gs.length →
      (Tb n (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p i) ↔ Tb n gs i) := by
    intro i hi
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, (eqv _ (hS0 z) i hi).1 hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, (eqv _ (hS0 z) i hi).2 hz⟩
  have hlen1 : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length = gs.length := by
    rw [List.length_append, hElen]
    simp
    omega
  have hJlt : (er n gs m p).length <
      (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length := by
    rw [List.length_append]
    simp
  have hJ : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[(er n gs m p).length]'hJlt =
      (Gate.mk GateOp.or [rd n m p o, h]) := by
    simp
  have hJv : ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (n + (er n gs m p).length) x = true ↔
        ((rd n m p o < n + (er n gs m p).length ∧
          val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p o) x = true) ∨
          val gs h x = true) := by
    intro x
    rw [val_or _ x (er n gs m p).length hJlt (by rw [hJ]), hJ]
    constructor
    · rintro ⟨i, hi, h1, h2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e
      · rw [e] at h1 h2
        exact Or.inl ⟨h1, h2⟩
      · rw [e, hval x] at h2
        exact Or.inr h2
    · rintro (⟨h1, h2⟩ | h2)
      · exact ⟨rd n m p o, by simp, h1, h2⟩
      · exact ⟨h, by simp, by rw [hElen]; omega, by rw [hval x]; exact h2⟩
  have hEget : ∀ j (hjE : j < (er n gs m p).length)
      (hj1 : j < (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length),
      (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[j] = (er n gs m p)[j] := by
    intro j hjE hj1
    exact List.getElem_append_left hjE
  refine ⟨er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])], n + (er n gs m p).length, hlen1,
    ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      by_cases hjm : j < m
      · rw [er_lt n gs m p j hjm (by omega) hj]
        exact legal _ (List.getElem_mem _)
      · have hj2 : j + 1 < gs.length := by rw [hElen] at hj; omega
        rw [er_ge n gs m p j (by omega) hj2 hj]
        have := legal gs[j + 1] (List.getElem_mem hj2)
        exact ⟨this.1, by simpa using this.2⟩
    · simp only [List.mem_singleton] at hg
      rw [hg]
      exact ⟨Or.inr rfl, by simp⟩
  · intro j hj ha x hv
    by_cases hS : val gs h x = true
    · exact hsh x hS
    · by_cases hjE : j < (er n gs m p).length
      · rw [hEget j hjE hj] at ha
        by_cases hjm : j < m
        · have hj0 : j < gs.length := by omega
          rw [er_lt n gs m p j hjm hj0 hjE] at ha
          have e := eqv x hS (n + j) (by omega)
          rw [rd_small n m p (n + j) (by omega)] at e
          exact hs j hj0 ha x (e.1 hv)
        · have hj2 : j + 1 < gs.length := by rw [hElen] at hjE; omega
          rw [er_ge n gs m p j (by omega) hj2 hjE] at ha
          have e := eqv x hS (n + (j + 1)) (by omega)
          rw [rd_succ n m p j (by omega)] at e
          exact hs (j + 1) hj2 ha x (e.1 hv)
      · have hje : j = (er n gs m p).length := by rw [hlen1] at hj; rw [hElen] at hjE ⊢; omega
        subst hje
        rw [hJ] at ha
        exact GateOp.noConfusion ha
  · intro x
    rw [hJv x]
    constructor
    · rintro (⟨h1, h2⟩ | h2)
      · by_cases hS : val gs h x = true
        · exact hsh x hS
        · exact (hc x).1 ((eqv x hS o (rdl' o h1)).1 h2)
      · exact hsh x h2
    · intro hF
      by_cases hS : val gs h x = true
      · exact Or.inr hS
      · have hvo := (hc x).2 hF
        have holt : o < n + gs.length := by
          by_contra hcon
          rw [val_big gs x o (by omega)] at hvo
          exact Bool.noConfusion hvo
        exact Or.inl ⟨rdl o holt, (eqv x hS o holt).2 hvo⟩
  · intro j hjm hd
    by_cases hjE : j < (er n gs m p).length
    · have hj2 : j + 1 < gs.length := by rw [hElen] at hjE; omega
      have hj1 : j < (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length := by
        rw [hlen1]; omega
      have hg : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[j] =
          ⟨gs[j + 1].op, gs[j + 1].inputs.map (rd n m p)⟩ := by
        rw [hEget j hjE hj1, er_ge n gs m p j hjm hj2 hjE]
      have hTj : ∀ a, a < n + gs.length →
          (Tb n (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p a) ↔ Tb n gs a) :=
        Tbeq
      apply hno (j + 1) (by omega)
      rcases hd with ⟨_, hor1, hT, h', hh', hlt', hnT'⟩ | ⟨_, ha, i', hi', hbd⟩
      · rw [hg] at hor1 hh'
        obtain ⟨a, ha2, rfl⟩ := List.mem_map.1 hh'
        have halt := (rd_lt n m p a j hp hjm).1 hlt'
        have hT2 := hTj (n + (j + 1)) (by omega)
        rw [rd_succ n m p j hjm] at hT2
        exact Or.inl ⟨hj2, hor1, hT2.1 hT, a, ha2, halt,
          fun t => hnT' ((hTj a (by omega)).2 t)⟩
      · rw [hg] at ha hi'
        obtain ⟨a, ha2, rfl⟩ := List.mem_map.1 hi'
        exact Or.inr ⟨hj2, ha, a, ha2, fun t => hbd
          ⟨(rd_lt n m p a j hp hjm).2 t.1, (hTj a (by omega)).2 t.2⟩⟩
    · rcases hd with ⟨hj1, hor1, ⟨z, hz⟩, _⟩ | ⟨hj1, ha, _⟩
      · have hje : j = (er n gs m p).length := by
          rw [hlen1] at hj1; rw [hElen] at hjE ⊢; omega
        subst hje
        rcases (hJv _).1 hz with ⟨h1, h2⟩ | h2
        · exact F_single G z ((hc _).1 ((eqv _ (hS0 z) o (rdl' o h1)).1 h2))
        · exact hS0 z h2
      · have hje : j = (er n gs m p).length := by
          rw [hlen1] at hj1; rw [hElen] at hjE ⊢; omega
        subst hje
        rw [hJ] at ha
        exact GateOp.noConfusion ha

lemma fix_all {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ (L : ℕ) (gs : List Gate) (o : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    Snd G gs → Cmp G gs o → (∀ j, L ≤ j → ¬ Defect n gs j) →
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, ¬ Defect n gs1 j := by
  intro L
  induction L with
  | zero =>
    intro gs o hl hs hc hno
    exact ⟨gs, o, rfl, hl, hs, hc, fun j => hno j (Nat.zero_le j)⟩
  | succ L ih =>
    intro gs o hl hs hc hno
    by_cases hd : Defect n gs L
    · rcases hd with ha | hb
      · obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
          lift_step G gs o hl hs hc L ha (fun j hj => hno j hj)
        obtain ⟨gs2, o2, hlen2, r⟩ := ih gs1 o1 hl1 hs1 hc1 hno1
        exact ⟨gs2, o2, hlen2.trans hlen, r⟩
      · obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
          conv_step G gs o hl hs hc L hb (fun j hj => hno j hj)
        obtain ⟨gs2, o2, hlen2, r⟩ := ih gs1 o1 hl1 hs1 hc1 hno1
        exact ⟨gs2, o2, hlen2.trans hlen, r⟩
    · apply ih gs o hl hs hc
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with e | hlt
      · rw [← e]
        exact hd
      · exact hno j hlt

lemma pure_cone {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G C.gates) (hno : ∀ j, ¬ Defect n C.gates j) :
    ∀ k, k < C.gates.length → Tb n C.gates (n + k) →
      ∀ i, InCone n C i k → Tb n C.gates (n + i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hT i hc
    obtain ⟨w, hw, hn, hlt, h⟩ := (inCone_iff n C i k hk).1 hc
    rw [gateAt_eq C k hk] at hw
    have hwT : Tb n C.gates w := by
      by_contra hnT
      rcases (legal C.gates[k] (List.getElem_mem hk)).1 with ha | ho
      · obtain ⟨z, hz⟩ := hT
        exact F_single G z (hs k hk ha _ hz)
      · exact hno k (Or.inl ⟨hk, ho, hT, w, hw, hlt, hnT⟩)
    have he : n + (w - n) = w := by omega
    rcases h with h | h
    · rw [h, he]
      exact hwT
    · exact ih (w - n) (by omega) (by omega) (by rw [he]; exact hwT) i h

lemma own_edge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G C.gates) (hno : ∀ j, ¬ Defect n C.gates j) (j : ℕ)
    (hj : j < C.gates.length) (ha : C.gates[j].op = GateOp.and) :
    ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v := by
  have hgood : ∀ i ∈ C.gates[j].inputs, i < n + j ∧ Tb n C.gates i := by
    intro i hi
    by_contra hcon
    exact hno j (Or.inr ⟨hj, ha, i, hi, hcon⟩)
  have hlen := (legal C.gates[j] (List.getElem_mem hj)).2
  rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    have hv : val C.gates (n + j) (fun _ : Fin n => false) = true :=
      (val_and C.gates _ j hj ha).2 (by rw [hin]; intro i hi; simp at hi)
    obtain ⟨u, v, _, hu, _⟩ := hs j hj ha _ hv
    exact Bool.noConfusion hu
  · exfalso
    obtain ⟨hlt, z, hz⟩ := hgood a (by rw [hin]; simp)
    have hv : val C.gates (n + j) (pairInput z z) = true :=
      (val_and C.gates _ j hj ha).2 (by
        rw [hin]
        intro i hi
        simp only [List.mem_singleton] at hi
        rw [hi]
        exact ⟨hlt, hz⟩)
    exact F_single G z (hs j hj ha _ hv)
  · obtain ⟨hlta, za, hza⟩ := hgood a (by rw [hin]; simp)
    obtain ⟨hltb, zb, hzb⟩ := hgood b (by rw [hin]; simp)
    have hva : val C.gates a (pairInput za zb) = true :=
      val_mono C.gates legal _ _ (pi_le za za zb (Or.inl rfl)) a hza
    have hvb : val C.gates b (pairInput za zb) = true :=
      val_mono C.gates legal _ _ (pi_le zb za zb (Or.inr rfl)) b hzb
    have hv : val C.gates (n + j) (pairInput za zb) = true :=
      (val_and C.gates _ j hj ha).2 (by
        rw [hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with e | e
        · rw [e]
          exact ⟨hlta, hva⟩
        · rw [e]
          exact ⟨hltb, hvb⟩)
    obtain ⟨u, v, huv, hu, hv2⟩ := hs j hj ha _ hv
    rw [pi_val] at hu hv2
    have hadj : G.Adj za zb := by
      rcases hu with e1 | e1 <;> rcases hv2 with e2 | e2
      · rw [e1, e2] at huv
        exact absurd rfl huv.ne
      · rw [e1, e2] at huv
        exact huv
      · rw [e1, e2] at huv
        exact huv.symm
      · rw [e1, e2] at huv
        exact absurd rfl huv.ne
    refine ⟨za, zb, hadj, hj, by rw [gateAt_eq C j hj]; exact ha, hv, ?_⟩
    intro i hij hc hai
    exfalso
    obtain ⟨w, hw, hn, hlt, h⟩ := (inCone_iff n C i j hj).1 hc
    rw [gateAt_eq C j hj] at hw
    obtain ⟨_, hwT⟩ := hgood w hw
    have he : n + (w - n) = w := by omega
    have hiT : Tb n C.gates (n + i) := by
      rcases h with h | h
      · rw [h, he]
        exact hwT
      · exact pure_cone G C legal hs hno (w - n) (by omega) (by rw [he]; exact hwT) i h
    obtain ⟨z, hz⟩ := hiT
    have hil : i < C.gates.length := by omega
    rw [gateAt_eq C i hil] at hai
    exact F_single G z (hs i hil hai _ hz)
  · exfalso
    rw [hin] at hlen
    simp only [List.length_cons] at hlen
    omega


lemma normalize_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmono : Monotone2 C)
    (hcomp : circuitFun n C = graphFun G ∅)
    (hsound : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      PEqualNP.TopForm.BelowF G C j) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
      circuitFun n D = graphFun G ∅ ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ Owns n D j u v := by
  have legal := legal_of C hmono
  have hs : Snd G C.gates := by
    intro j hj ha x hv
    have hx := hsound j hj (by rw [gateAt_eq C j hj]; exact ha) x hv
    simpa [graphFun, F] using hx
  have hc : Cmp G C.gates C.output := by
    intro x
    have hx := congrFun hcomp x
    change val C.gates C.output x = graphFun G ∅ x at hx
    rw [hx]
    simp [graphFun, F]
  obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
    fix_all G C.gates.length C.gates C.output legal hs hc (by
      intro j hj hd
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  refine ⟨⟨gs1, o1⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hl1 g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · rw [h]
      exact Or.inl rfl
    · rw [h]
      exact Or.inr rfl
  · show gs1.length ≤ C.gates.length
    omega
  · funext x
    apply Bool.eq_iff_iff.mpr
    simpa [circuitFun, Circuit.eval, Circuit.wires, wf, graphFun, F, val] using hc1 x
  · intro j hj ha
    exact own_edge G ⟨gs1, o1⟩ hl1 hs1 hno1 j hj
      (by rw [gateAt_eq ⟨gs1, o1⟩ j hj] at ha; exact ha)

lemma minimum_sound_to_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hex : ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      circuitFun n C = graphFun G ∅ ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        PEqualNP.TopForm.BelowF G C j) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      circuitFun n C = graphFun G ∅ ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  obtain ⟨C, hmin, hcomp, hs⟩ := hex
  obtain ⟨D, hd, hsize, hcompD, howns⟩ := normalize_sound G C hmin.1 hcomp hs
  refine ⟨D, ⟨hd, ?_⟩, hcompD, howns⟩
  intro E he hcompE
  exact hsize.trans (hmin.2 E he (hcompE.trans (hcompD.trans hcomp.symm)))

end PEqualNP.Outside.L_meta_1772.Normal
