import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Normalize

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [ite_eq_left ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [ite_eq_right ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, ite_eq_right hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · by_cases heq : j = k
      · subst k
        refine ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => ?_⟩⟩
        change (W new x).getD j false = (f x && g x)
        rw [← hjv x, ← hkv x]
        simp
      · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl, by simp [heq]⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
          Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
            fun x => ?_⟩⟩
        show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
        rw [W_val, ite_eq_left rfl]
        show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
        rw [hjv x, hkv x]
        simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · by_cases heq : j = k
      · subst k
        refine ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => ?_⟩⟩
        change (W new x).getD j false = (f x || g x)
        rw [← hjv x, ← hkv x]
        simp
      · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl, by simp [heq]⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
          Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
            fun x => ?_⟩⟩
        show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
        rw [W_val, ite_eq_left rfl]
        show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
        rw [hjv x, hkv x]
        simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, ite_eq_left ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, ite_eq_right ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

lemma normalize {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size ≤ C.size ∧
      D.output < n + D.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, hjb, hj⟩
  · obtain ⟨x, y, hxy⟩ := hnc
    exact (hxy ((hev x).trans ((hc x).trans ((hc y).symm.trans (hev y).symm)))).elim
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl, hjb, ?_⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2.1
    · intro g hgm
      exact (hfan g hgm).2.2
    · intro x
      rw [hev x]
      exact hj x

end PEqualNP.Outside.L_meta_2590_aux.Normalize

namespace PEqualNP.Outside.L_meta_2590_aux.Normalize.Prune


open PEqualNP.CircuitLowerBounds


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

lemma getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

lemma getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]


open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover



lemma foldl_set_equiv (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (heq : ∀ w : List Bool, g'.op.eval (g'.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (w0 : List Bool) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _



lemma foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

lemma take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega


lemma wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]




def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1


def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩


def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1


def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

lemma sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega


def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

lemma rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

lemma rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

lemma del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

lemma del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, ite_eq_left hk]
  omega

lemma del_get (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate) (hj : j ≠ k)
    (h : E.gates[j]? = some g) : (del n k u E).gates[sg k j]? = some (rd (n + k) u g) := by
  by_cases h1 : j < k
  · simp only [del, sg, ite_eq_left h1, List.getElem?_map, List.getElem?_eraseIdx, h]; rfl
  · have h2 : ¬ (j - 1 < k) := by omega
    have h3 : j - 1 + 1 = j := by omega
    simp only [del, sg, ite_eq_right h1, List.getElem?_map, List.getElem?_eraseIdx, ite_eq_right h2, h3, h]
    rfl

lemma del_get_inv (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate)
    (h : (del n k u E).gates[j]? = some g) :
    ∃ g0, E.gates[if j < k then j else j + 1]? = some g0 ∧ g = rd (n + k) u g0 := by
  simp only [del, List.getElem?_map, List.getElem?_eraseIdx] at h
  split_ifs at h ⊢ with h1
  · cases hh : E.gates[j]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩
  · cases hh : E.gates[j + 1]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩

lemma del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

lemma gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

lemma readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)

lemma del_readsBack (n k u : ℕ) (E : Circuit) (hE : ReadsBack n E) (hu : u < n + k) :
    ReadsBack n (del n k u E) := by
  apply readsBack_of_get
  intro j g hg
  obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g hg
  have hr := readsBack_get n E hE _ g0 hg0
  intro i hi
  simp only [rd, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have := hr i0 hi0
  unfold sig
  split_ifs at this ⊢ <;> omega

lemma readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

lemma fold_agree (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, m ∉ g.inputs) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, i ≠ m → a.getD i false = b.getD i false) →
      (gs.foldl step a).length = (gs.foldl step b).length ∧
      ∀ i, i ≠ m → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
  induction gs with
  | nil => intro a b hl hab; exact ⟨hl, hab⟩
  | cons g gs ih =>
    intro a b hl hab
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hab i (fun e => hgs g (by simp) (e ▸ hi))
      intro i hi
      unfold step
      by_cases hia : i = a.length
      · subst hia
        rw [getD_append_singleton_last, hl, getD_append_singleton_last]
        exact hv
      · rw [getD_append_singleton _ _ _ hia, getD_append_singleton _ _ _ (by rw [← hl]; exact hia)]
        exact hab i hi

lemma set_unread_fun (n : ℕ) (C : Circuit) (h : ℕ) (X : Gate) (hh : h < C.gates.length)
    (hun : ∀ j < C.gates.length, n + h ∉ (gateAt C j).inputs) (ho : C.output ≠ n + h) :
    circuitFun n ⟨C.gates.set h X, C.output⟩ = circuitFun n C := by
  funext x
  unfold circuitFun Circuit.eval
  simp only [wires_eq]
  have hw0l : (List.ofFn x).length = n := by simp
  have hgk : C.gates[h]? = some C.gates[h] := List.getElem?_eq_getElem hh
  have hsk : (C.gates.set h X)[h]? = some X := by simp [hh]
  rw [foldl_split C.gates h _ hgk, foldl_split (C.gates.set h X) h X hsk,
    List.take_set_of_le (le_refl h), List.drop_set_of_lt (Nat.lt_succ_self h)]
  have hl := take_fold_length C.gates h hh (List.ofFn x)
  set Wp := (C.gates.take h).foldl step (List.ofFn x)
  have hall : ∀ g ∈ C.gates.drop (h + 1), n + h ∉ g.inputs := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_drop hg)
    have := hun j hj
    rwa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  have := fold_agree (n + h) _ hall (step Wp X) (step Wp C.gates[h]) (by simp [step]) (by
    intro i hi
    unfold step
    rw [getD_append_singleton _ _ _ (by omega), getD_append_singleton _ _ _ (by omega)])
  exact this.2 _ ho


lemma erase_unread {n : ℕ} (hn : 0 < n) (C : Circuit) (hm : Monotone2 C)
    (hrb : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (ho : C.output ≠ n + k) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧ circuitFun n D = circuitFun n C := by
  let X : Gate := ⟨GateOp.or, [0]⟩
  let E : Circuit := ⟨C.gates.set k X, C.output⟩
  have hemono : Monotone2 E := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hm g h
    · subst h
      simp [X]
  have hefun : circuitFun n E = circuitFun n C := set_unread_fun n C k X hk hun ho
  have helen : E.gates.length = C.gates.length := by simp [E]
  have hek : E.gates[k]? = some ⟨GateOp.or, [0]⟩ := by
    simp [E, X, hk]
  have hecopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD 0 false := by
    intro x
    simpa using wires_copy E k 0 hek (List.ofFn x) (by simp; omega)
  have hepre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
    change ∀ g ∈ (C.gates.set k X).take k, ∀ i ∈ g.inputs, i < n + k
    rw [List.take_set_of_le (le_refl k)]
    exact readsBack_take n C hrb k
  have heklt : k < E.gates.length := by omega
  refine ⟨del n k 0 E, del_mono n k 0 E hemono, ?_, ?_⟩
  · have hs := del_length n k 0 E heklt
    change (del n k 0 E).gates.length < C.gates.length
    omega
  · rw [del_fun n k 0 E heklt (by omega) hepre hecopy, hefun]

lemma del_AO (n k u : ℕ) (E : Circuit) (hE : PEqualNP.TopForm.IsAO2 n E) (hu : u < n + k) :
    PEqualNP.TopForm.IsAO2 n (del n k u E) := by
  refine ⟨fun g hg => ?_, del_readsBack n k u E hE.2.1 hu, fun g hg => ?_⟩
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

end PEqualNP.Outside.L_meta_2590_aux.Normalize.Prune

namespace PEqualNP.Outside.L_meta_2590_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma normalized_live {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hm : Monotone2 C) (hf : ∀ x, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) (hnp : ∀ i : Fin n, ∃ x, f x ≠ x i) :
    ∃ D : Circuit, IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size ≤ C.size ∧
      ∃ o : Fin D.size, D.output = n + o.val ∧
        (∀ j : Fin D.size, j ≠ o → 1 ≤ (D.gates.flatMap Gate.inputs).count (n + j.val)) ∧
        ∀ x, D.eval (List.ofFn x) = f x := by
  classical
  have hex : ∃ s : ℕ, ∃ E : Circuit, Monotone2 E ∧ (∀ x, E.eval (List.ofFn x) = f x) ∧ E.size = s :=
    ⟨C.size, C, hm, hf, rfl⟩
  obtain ⟨M, hM, hMf, hMs⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, Monotone2 E → (∀ x, E.eval (List.ofFn x) = f x) → M.size ≤ E.size := by
    intro E hE hEf
    rw [hMs]
    exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩
  have hMnc : ∃ x y : Fin n → Bool, M.eval (List.ofFn x) ≠ M.eval (List.ofFn y) := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, by simpa only [hMf] using hxy⟩
  obtain ⟨D, hD, hnodup, hsize, hout, hDf⟩ := normalize M hM hMnc
  have hmono : Monotone2 D := by
    intro g hg
    refine ⟨?_, (hD.2.2 g hg).le⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hD.1 g hg
  have hfun : ∀ x, D.eval (List.ofFn x) = f x := fun x => (hDf x).trans (hMf x)
  have hdmin : ∀ E : Circuit, Monotone2 E → (∀ x, E.eval (List.ofFn x) = f x) → D.size ≤ E.size :=
    fun E hE hEf => hsize.trans (hmin E hE hEf)
  have hlow : n ≤ D.output := by
    by_contra hnout
    have hlt : D.output < n := by omega
    let i : Fin n := ⟨D.output, hlt⟩
    obtain ⟨x, hx⟩ := hnp i
    have hv : D.eval (List.ofFn x) = x i := by
      rw [Circuit.eval, Prune.wires_eq, Prune.foldl_step_getD _ _ _ (by simpa using hlt)]
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp [i]
    exact hx ((hfun x).symm.trans hv)
  let o : Fin D.size := ⟨D.output - n, by omega⟩
  have ho : D.output = n + o.val := by dsimp [o]; omega
  refine ⟨D, hD, hnodup, hsize.trans (hmin C hm hf), o, ho, ?_, hfun⟩
  intro j hj
  by_contra hcount
  have hz : (D.gates.flatMap Gate.inputs).count (n + j.val) = 0 := by omega
  have hnmem : n + j.val ∉ D.gates.flatMap Gate.inputs := List.count_eq_zero.mp hz
  have hun : ∀ k < D.gates.length, n + j.val ∉ (gateAt D k).inputs := by
    intro k hk hi
    apply hnmem
    exact List.mem_flatMap.mpr ⟨gateAt D k, List.mem_of_getElem? (Prune.gateAt_some D k hk), hi⟩
  have hjout : D.output ≠ n + j.val := by
    intro he
    apply hj
    apply Fin.ext
    omega
  obtain ⟨E, hE, hs, heq⟩ := Prune.erase_unread hn D hmono hD.2.1 j.val j.isLt hun hjout
  have hEf : ∀ x, E.eval (List.ofFn x) = f x := by
    intro x
    exact (congrFun heq x).trans (hfun x)
  have := hdmin E hE hEf
  omega

end PEqualNP.Outside.L_meta_2590_aux.Normalize
