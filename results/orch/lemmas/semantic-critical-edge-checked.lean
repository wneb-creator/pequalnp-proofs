import PEqualNP.Defs

-- Basic monotone semantics and zero-cut compression adapted from the earlier checked
-- normalization component; its compressor follows the accepted L_meta_5138 construction.
namespace PEqualNP.Outside.L_meta_3754.Semantic

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

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

lemma val_monotone {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact hxy ⟨i,h⟩ hi
  | append_singleton gs g ih =>
    have hold := ih (fun v hv => hg v (by simp [hv]))
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact gate_eval_monotone g (hg g (by simp)) _ _ hold hi
    · exact hold i hi


def zeroGate : Gate := ⟨GateOp.or, []⟩

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

lemma val_append_old {n : ℕ} (pre post : List Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + pre.length) : val (pre ++ post) x i = val pre x i := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    have hne : i ≠ n + (pre ++ post).length := by
      simp only [List.length_append]
      omega
    rw [← List.append_assoc, val_snoc, ite_eq_right hne]
    exact ih

lemma cut_zero_agrees {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool)
    (hz : val (pre ++ [g] ++ post) x (n + pre.length) = false) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = val (pre ++ [g] ++ post) x i := by
  have hp : val (pre ++ [g]) x (n + pre.length) = false := by
    have heq := val_append_old (pre ++ [g]) post x (n + pre.length) (by simp)
    exact heq.symm.trans hz
  rw [val_snoc, ite_eq_left rfl] at hp
  have hs : step (pre.foldl step (List.ofFn x)) zeroGate =
      step (pre.foldl step (List.ofFn x)) g := by
    change g.op.eval (g.inputs.map fun j =>
      (pre.foldl step (List.ofFn x)).getD j false) = false at hp
    exact congrArg (fun b => pre.foldl step (List.ofFn x) ++ [b]) hp.symm
  intro i
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hs]

lemma cut_zero_below {n : ℕ} (pre post : List Gate) (g : Gate)
    (hpost : ∀ k ∈ post, k.op = GateOp.and ∨ k.op = GateOp.or)
    (x : Fin n → Bool) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = true →
      val (pre ++ [g] ++ post) x i = true := by
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply fold_state_monotone post hpost
  · simp [step]
  · intro i hi
    rw [step_getD] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp [zeroGate,GateOp.eval] at hi
    · exact hi

end PEqualNP.Outside.L_meta_3754.Semantic

namespace PEqualNP.Outside.L_meta_3754.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section Parameters
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

theorem u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, ite_eq_left h]

theorem u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left h]

theorem u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_left hA, dite_eq_left ha, dite_eq_left hb]

theorem u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_right (by simp [hA]), dite_eq_left ha,
    dite_eq_left hb]
end Parameters

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

theorem chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [ite_eq_right (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
theorem build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [ite_eq_left hpd, ite_eq_right hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [ite_eq_right (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma compress_zero_program (n N : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < N, a j < n+j ∧ b j < n+j) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+N, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range N).filter (· ∈ Del)).card ≤ N := by
  obtain ⟨gs,m,hok,hsem,hdel,hsize,hdirty⟩ :=
    build n A a b Del ∅ (fun _ => []) (fun _ => false) (by simp) (by simp) N hab
  refine ⟨gs,m,hok,hsem,?_⟩
  simpa using hsize


lemma u_matches_run (n : ℕ) (gs : List Gate) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < gs.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < gs.length), gs[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩)
    (x : Fin n → Bool) :
    ∀ w < n+gs.length, u n A a b Del (fun _ => []) (List.ofFn x) w =
      (run gs (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [u_in hin, run_input gs (List.ofFn x) w (by simpa using hin)]
    have hn : n ≤ w := by omega
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < gs.length := by omega
    obtain ⟨ha,hb⟩ := hab j hj
    have hra : u n A a b Del (fun _ => []) (List.ofFn x) (a j) =
        (run gs (List.ofFn x)).getD (a j) false := ih (a j) ha (by omega)
    have hrb : u n A a b Del (fun _ => []) (List.ofFn x) (b j) =
        (run gs (List.ofFn x)).getD (b j) false := ih (b j) hb (by omega)
    have hr := run_gate gs (List.ofFn x) j hj
    simp only [List.length_ofFn] at hr
    rw [hr,hgate j hj]
    by_cases hd : j ∈ Del
    · rw [u_del hd,ite_eq_left hd]
      rfl
    · rw [ite_eq_right hd]
      cases hA : A j with
      | false =>
        rw [u_or hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]
      | true =>
        rw [u_and hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]

lemma compress_zero_circuit (n : ℕ) (C : Circuit) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < C.gates.length), C.gates[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          (C.wires (List.ofFn x)).getD w false) ∧
      gs.length + ((Finset.range C.gates.length).filter (· ∈ Del)).card ≤ C.gates.length := by
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_program n C.gates.length A a b Del hab
  refine ⟨gs,m,hok,?_,hsize⟩
  intro w hw
  obtain ⟨hbound,hval⟩ := hsem w hw
  refine ⟨hbound,?_⟩
  intro x
  rw [hval,u_matches_run n C.gates A a b Del hab hgate x w hw]
  rfl

theorem ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

def zeroCut (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma compress_one_cut {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          ((zeroCut C j).wires (List.ofFn x)).getD w false) ∧
      gs.length+1 ≤ C.gates.length := by
  classical
  let A : ℕ → Bool := fun i => decide ((gateAt C i).op = GateOp.and)
  let a : ℕ → ℕ := fun i => TopForm.opnd C i 0
  let b : ℕ → ℕ := fun i => TopForm.opnd C i 1
  have hab : ∀ i < (zeroCut C j).gates.length, a i < n+i ∧ b i < n+i := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨_,_,ha,hb,_⟩ := gate2 hC hi'
    exact ⟨ha,hb⟩
  have hgate : ∀ i (hi : i < (zeroCut C j).gates.length), (zeroCut C j).gates[i] =
      if i ∈ ({j} : Finset ℕ) then ⟨GateOp.or, []⟩
      else ⟨if A i then GateOp.and else GateOp.or, [a i,b i]⟩ := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨he,hin,ha,hb,hop⟩ := gate2 hC hi'
    by_cases hij : i=j
    · subst i
      simp [zeroCut]
    · simp only [Finset.mem_singleton,ite_eq_right hij]
      have hs : (zeroCut C j).gates[i] = C.gates[i] := by
        simp [zeroCut,List.getElem_set,hij,Ne.symm hij]
      rw [hs,he]
      have hop' : (gateAt C i).op = if A i then GateOp.and else GateOp.or := by
        rcases hop with hop | hop <;> simp [A,hop]
      cases hgc : gateAt C i with
      | mk o ins =>
        simp only [hgc] at hin hop'
        rw [hop',hin]
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_circuit n (zeroCut C j) A a b {j} hab hgate
  refine ⟨gs,m,hok,?_,?_⟩
  · simpa [zeroCut] using hsem
  · have hfilter : ((Finset.range (zeroCut C j).gates.length).filter (· ∈ ({j} : Finset ℕ))) = {j} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro hij
        subst i
        exact ⟨by simpa [zeroCut] using hj,rfl⟩
    rw [hfilter,Finset.card_singleton] at hsize
    simpa [zeroCut] using hsize

end PEqualNP.Outside.L_meta_3754.Compression

namespace PEqualNP.Outside.L_meta_3754.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma zeroCut_decomposition {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1) ∧
    (zeroCut C j).gates = C.gates.take j ++ [Semantic.zeroGate] ++ C.gates.drop (j+1) := by
  have hs : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j+1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  refine ⟨hs, ?_⟩
  have ht : (C.gates.take j).length = j := by simp; omega
  unfold zeroCut
  dsimp
  conv_lhs => rw [hs]
  have hz (pre post : List Gate) (g : Gate) :
      (pre ++ [g] ++ post).set pre.length Semantic.zeroGate =
        pre ++ [Semantic.zeroGate] ++ post := by simp [List.set_append]
  simpa only [ht, Semantic.zeroGate] using hz (C.gates.take j) (C.gates.drop (j+1)) C.gates[j]

lemma zeroCut_or_and {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) :
    ∀ g ∈ (zeroCut C j).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  obtain ⟨hs, hz⟩ := zeroCut_decomposition hj
  rw [hz]
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | rfl) | hg
  · exact hC.1 g (by rw [hs]; exact List.mem_append_left _ (List.mem_append_left _ hg))
  · exact Or.inr rfl
  · exact hC.1 g (by rw [hs]; exact List.mem_append_right _ hg)

lemma zeroCut_le {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    ∀ w, ((zeroCut C j).wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD w false = true := by
  obtain ⟨hs, hz⟩ := zeroCut_decomposition hj
  change ∀ w, Semantic.val (zeroCut C j).gates x w = true → Semantic.val C.gates x w = true
  rw [hs,hz]
  apply Semantic.cut_zero_below
  intro g hg
  exact hC.1 g (by rw [hs]; exact List.mem_append_right _ hg)

lemma graph_eq_of_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hle : ∀ x, f x = true → graphFun G ∅ x = true)
    (hedge : ∀ u v, G.Adj u v → f (pairInput u v) = true) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hle x
  · intro hx
    simp [graphFun] at hx
    obtain ⟨u,v,huv,hxu,hxv⟩ := hx
    apply hmono (pairInput u v) x ?_ (hedge u v huv)
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> assumption

lemma zeroCut_smaller {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hout : C.output < n+C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n (zeroCut C j) := by
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_one_cut C hC j hj
  cases he : m C.output with
  | none =>
    refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,by simpa [Circuit.size] using hsize,?_⟩
    funext x
    have hv := (hsem C.output hout).2 x
    rw [he] at hv
    change false = circuitFun n (zeroCut C j) x at hv
    change (run gs (List.ofFn x)).getD (n+gs.length) false = _
    rw [List.getD_eq_default _ _ (by simp [run_length])]
    exact hv
  | some w =>
    refine ⟨⟨gs,w⟩,ok_ao hok,by simpa [Circuit.size] using hsize,?_⟩
    funext x
    have hv := (hsem C.output hout).2 x
    rw [he] at hv
    exact hv

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output < n+C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧ circuitFun n (zeroCut C j) (pairInput u v) = false := by
  classical
  by_contra h
  have he : ∀ u v, G.Adj u v → circuitFun n (zeroCut C j) (pairInput u v) = true := by
    intro u v huv
    cases hv : circuitFun n (zeroCut C j) (pairInput u v)
    · exact False.elim (h ⟨u,v,huv,hv⟩)
    · rfl
  have hc : circuitFun n (zeroCut C j) = graphFun G ∅ := by
    apply graph_eq_of_edges G _ ?_ ?_ he
    · intro x y hxy
      exact Semantic.val_monotone (zeroCut C j).gates (zeroCut_or_and hC.1 hj) x y hxy C.output
    · intro x hx
      rw [← hC.2.1]
      exact zeroCut_le hC.1 hj x C.output hx
  obtain ⟨D,hD,hs,hf⟩ := zeroCut_smaller C hC.1 j hj hout
  have hm := hC.2.2 D hD (hf.trans hc)
  omega

end PEqualNP.Outside.L_meta_3754.Compression
