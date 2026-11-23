import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone normalization and directed coverage adapted from L_meta_742.


namespace PEqualNP.Outside.L_meta_984.Cert

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}

theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (save : Bool)
    (h : Run inv meet join y s (inv a :: kept save a r)) :
    Run inv meet join y (s + 1) (a :: r) := fun P d q u b => u save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h : Run inv meet join y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k ⟨h', ih⟩ => ⟨Run.one k h', one k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest save _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 : (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [simpStep, List.length_append]
      cases (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : val gs n (n + p) = invF (val gs n j) := by
        funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval, invF]
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one _ IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

open Classical in
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hm]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hm]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k + i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega, show k + i < k + k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl



def MonoL (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

def HasMonoSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = f x

theorem simplify_mono (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpAnd] at hg
    · cases a <;> simp [simplify,simpAnd] at hg
    · cases a <;> cases b <;> simp only [simplify,simpAnd,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inl rfl
    · simp [simplify,simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    · simp [simplify,simpOr] at hg
    · cases a <;> simp [simplify,simpOr] at hg
    · cases a <;> cases b <;> simp only [simplify,simpOr,Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk,ite_false,Option.some.injEq] at hg
        subst hg
        exact Or.inr rfl
    · simp [simplify,simpOr] at hg

theorem simpPass_mono (n : ℕ) (gs : List Gate) (hgs : MonoL gs) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, MonoL acc.2 → MonoL (simpPass n gs acc).2 := by
  induction gs with
  | nil => intro acc hacc; exact hacc
  | cons g gs ih =>
    intro acc hacc
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq)) (simpStep n acc g)
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hacc q hq
    · exact simplify_mono g.op _ _ (hgs g List.mem_cons_self) q (by simpa using hq)

theorem exists_sclean_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    have hm : MonoL acc.2 := simpPass_mono n C.gates
      (fun g hg => (hfan g hg).1) (init,[]) (by intro g hg; simp at hg)
    refine ⟨acc.2, o, hlen, (hinv y).2.1, hm, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl


theorem erase_dead_mono (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ MonoL gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  have hmono' : MonoL gs' := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hmono g (List.mem_of_mem_take hg)
    · obtain ⟨g₀,hg₀,rfl⟩ := List.mem_map.1 hg
      exact hmono g₀ (List.mem_of_mem_drop hg₀)
  refine ⟨gs', o', hlen', hcl', hmono', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)


open Classical in
theorem run_live_mono (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (hmono : MonoL gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (fun a : BFn n => a) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hm := hmono g (List.mem_of_getElem? hg)
      rcases hm with hm | hm <;> rw [hop] at hm <;> cases hm
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
          then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
        funext x
        rw [hvg x, hinp]
        rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, meetF, joinF]
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')


open Classical in
theorem exists_run_mono {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasMonoSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a : BFn n => a) meetF joinF f s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ MonoL gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, hm, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, hm, ho, hev⟩ := exists_sclean_mono f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, hm, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, hmono, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', hmono', ho', hev'⟩ := erase_dead_mono n gs o p hcl hmono ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', hmono', ho', fun x => (hev' x).trans (hev x)⟩
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live_mono n gs o hcl hmono ho hnd gs.length 0 (by omega)


abbrev MonoNatRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

abbrev MonRun := Run (fun a : Nat => a) (· &&& ·) (· ||| ·)

theorem bits_le {y s ws} (h : MonRun y s ws) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save h ih =>
    apply ih
    intro a ha
    cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at ha
    · rcases ha with rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
    · rcases ha with rfl | rfl | ha
      · exact hw _ List.mem_cons_self
      · exact hw _ List.mem_cons_self
      · exact hw _ (by simp [ha])
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;> grind
    · rcases (mem_kept ka _ _ _).1 ht with ⟨_, rfl⟩ | ht
      · exact ha
      · rcases (mem_kept kb _ _ _).1 ht with ⟨_, rfl⟩ | ht
        · exact hb
        · exact hw _ (by simp [ht])


def next (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : MonRun (goal k) s (a :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun (goal k) s ys → f ys = true) :
    next (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : MonRun (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, MonRun (goal k) s ys → f ys = true) →
      next (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : MonRun (goal k) s ws) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k : Nat) (ws : List Nat) : Bool := covUp k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : MonRun (goal k) s ws) : covers k ws = true := by
  simp [covers, required_up h]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(found S N idx s zs))

theorem bar_sound {k S N idx} {s i : Nat} (hb : bar k S N idx s i = true)
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(found S N idx s zs)
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx} {cap : Nat}
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h

theorem extend_run {y s t a r} (h : MonRun y s (a :: r))
    (hle : s ≤ t) : MonRun y t (a :: r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false ih

theorem mono_encoded {n : ℕ} (f : BFn n)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (cap : ℕ)
    (rows : List ℕ) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) (hs : C.size ≤ cap) :
    ∃ s, s ≤ cap ∧ ∃ zs : List ℕ,
      zs.Sublist ((List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
        (fun a => encL a rows)) ∧ MonRun (encL f rows) s zs := by
  obtain ⟨s,hs,ws,hsub,hrun⟩ := exists_run_mono f hnc cap ⟨C,hmono,hs,hev⟩
  refine ⟨s,hs,ws.map (fun a => encL a rows),hsub.map _,?_⟩
  exact Run.map (fun a : BFn n => encL a rows) (fun _ => rfl)
    (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun

theorem encoded_mono_exclusion {n : ℕ} (f : BFn n)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (cap : ℕ)
    (rows xs : List ℕ) (k : ℕ)
    (hinputs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → (covUp k zs &&& lo k) ≠ lo k)
    (hno : ∀ s ≤ cap, ¬ MonRun (goal k) s xs) :
    ¬ HasMonoSize n f cap := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := mono_encoded f hnc cap rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · exact hproper zs (List.mem_sublists.2 hsub) he (required_up hr)

theorem mono_lower {n : ℕ} (f : BFn n) (cap : ℕ)
    (hno : ¬ HasMonoSize n f cap) (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) : cap + 1 ≤ C.size := by
  by_contra hs
  exact hno ⟨C,hmono,by omega,hev⟩

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {y s ws} (h : MonRun y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {y s ws} (h : MonRun y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : MonRun (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : MonRun (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def barScore (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(scr k s pool zs) && !(found S N idx s zs))

theorem barScore_sound {k S N idx pool} {s i : Nat} (hb : barScore k S N idx pool s i = true)
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [barScore, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(scr k s pool zs) && !(found S N idx s zs)
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barScore_all {k S N idx pool} {cap : Nat}
    (hc : ∀ s ≤ cap, ∀ i < N s, barScore k S N idx pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := barScore_sound (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_bar {k S N idx cap i xs}
    (checked : ∀ s ≤ cap, ∀ j < N s, bar k S N idx s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun (goal k) s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact bar_all checked cap (Nat.le_refl _) i hi
      (Run.perm hinit (extend_run hrun hs))

theorem noRun_from_barScore {k S N idx pool cap i xs}
    (checked : ∀ s ≤ cap, ∀ j < N s, barScore k S N idx pool s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun (goal k) s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact barScore_all checked cap (Nat.le_refl _) i hi
      (Run.perm hinit (extend_run hrun hs))


namespace Shard28

def f : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)

def rows : List ℕ := [10, 10, 10, 10, 10, 10, 10, 10, 10, 33, 33, 33, 33, 33, 33, 33, 33, 33, 44, 44, 44, 44, 44, 44, 44, 44, 44, 52, 52, 52, 52, 52, 52, 52, 52, 52, 65, 65, 65, 65, 65, 65, 65, 65, 65, 82, 82, 82, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96, 3, 5, 9, 17, 6, 34, 24, 72, 96]

def xs : List ℕ := [0x1e0f0783c1e0f0780001ff00003fe00, 0x6231188c4623118803fe000000001ff, 0x2412090482412097fc0000ffffc0000, 0x188c46231188c4620000000007fc01ff, 0x9048241209048247fffe00ff8000000, 0x24120904824120900000000ffffffe00, 0x30180c06030180c07ffffff000000000]

theorem hnc : ∃ y z : Fin 7 → Bool, f y ≠ f z :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem enc_inputs : (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a rows) = xs := by decide +kernel

theorem enc_goal : encL f rows = goal 63 := by decide +kernel

theorem proper_fail : ∀ zs ∈ xs.sublists, zs ≠ xs →
    (covUp 63 zs &&& lo 63) ≠ lo 63 := by decide +kernel

theorem xs_ne_nil : xs ≠ [] := by decide

end Shard28


namespace Shard28

def N : Nat → Nat
  | 5 => 50
  | 6 => 671
  | 7 => 3243
  | 8 => 5403
  | 9 => 1855
  | 10 => 48
  | 11 => 1
  | _ => 0

def V : Array Nat := #[
  0x0,
  0x1ff,
  0x3fe00,
  0x3ffff,
  0x7fc0000,
  0x7fc01ff,
  0x7fffe00,
  0xff8000000,
  0xff80001ff,
  0xff803fe00,
  0xffffc0000,
  0xffffc01ff,
  0xffffffe00,
  0x1ff000000000,
  0x1ff0000001ff,
  0x1ff00003fe00,
  0x1ff007fc0000,
  0x1ffff8000000,
  0x1ffffffc0000,
  0x3fe00000000000,
  0x3fe000000001ff,
  0x3fe0000003fe00,
  0x3fe00007fc0000,
  0x3fe00ff8000000,
  0x3fe00ffffc0000,
  0x3fe00ffffc01ff,
  0x3ffff000000000,
  0x7fc0000000000000,
  0x7fc00000000001ff,
  0x7fc000000003fe00,
  0x7fc0000007fc0000,
  0x7fc0000ff8000000,
  0x7fc0000ff80001ff,
  0x7fc0000ff803fe00,
  0x7fc0000ffffc0000,
  0x7fc01ff000000000,
  0x7fc01ffff8000000,
  0x7fc01ffffffffe00,
  0x7fffe00000000000,
  0x7fffe000000001ff,
  0x7fffe0000003fe00,
  0x7fffe00007fc0000,
  0x7fffe00007fc01ff,
  0x7fffe00ff8000000,
  0x7fffe00ffffc0000,
  0x7fffe00ffffc01ff,
  0x7ffffff000000000,
  0x7ffffffff803fe00,
  0x201008040201008000000000000000,
  0x2010080402010080000000000001ff,
  0x20100804020100800000000003fe00,
  0x201008040201008000000007fc0000,
  0x201008040201008000000007ffffff,
  0x201008040201008000000ff8000000,
  0x201008040201008000000ffffc0000,
  0x2010080402010080001ff000000000,
  0x2010080402010080001ff00003fe00,
  0x20100804020100803fe00000000000,
  0x20100804020100803fe000000001ff,
  0x20100804020100803fe00ff803fe00,
  0x20100804020100ffc0000000000000,
  0x20100804020100ffc0000ff8000000,
  0x20100804020100ffffe00000000000,
  0x20100804020100fffffff000000000,
  0x402010080402010000000000000000,
  0x4020100804020100000000000001ff,
  0x40201008040201000000000003fe00,
  0x402010080402010000000007fc0000,
  0x402010080402010000000007fffe00,
  0x402010080402010000000ff8000000,
  0x402010080402010000000ffffc0000,
  0x4020100804020100001ff000000000,
  0x4020100804020100001ff00003fe00,
  0x40201008040201003fe00000000000,
  0x402010080402017fc0000000000000,
  0x402010080402017fc0000007fc0000,
  0x402010080402017fc0000ff8000000,
  0x402010080402017fc0000ff803fe00,
  0x402010080402017fc0000ffffc0000,
  0x402010080402017fffe00000000000,
  0x402010080402017ffffffff8000000,
  0x6030180c0603018000000000000000,
  0x6030180c060301800000000003fe00,
  0x6030180c0603018000000007fc01ff,
  0x6030180c06030180001ff000000000,
  0x6030180c060301ffffe00000000000,
  0x6030180c060301ffffe00ff8000000,
  0x804020100804020000000000000000,
  0x8040201008040200000000000001ff,
  0x80402010080402000000000003fe00,
  0x804020100804020000000007fc0000,
  0x804020100804020000000007fc01ff,
  0x804020100804020000000ff8000000,
  0x804020100804020000000ffffc0000,
  0x804020100804020000000ffffffe00,
  0x8040201008040200001ff000000000,
  0x8040201008040200001ff00003fe00,
  0x80402010080402003fe00000000000,
  0x80402010080402003ffff0000001ff,
  0x804020100804027fc0000000000000,
  0x804020100804027fc0000ff8000000,
  0x804020100804027fc01ff007fc0000,
  0x804020100804027fffe00000000000,
  0xa05028140a05028000000000000000,
  0xa05028140a0502800000000003fe00,
  0xa05028140a050280001ff000000000,
  0xc06030180c06030000000000000000,
  0xc06030180c0603000000000003fe00,
  0xc06030180c06030000000ffffc0000,
  0xc06030180c060300001ff000000000,
  0xe070381c0e07038000000000000000,
  0x1008040201008040000000000000000,
  0x10080402010080400000000000001ff,
  0x100804020100804000000000003fe00,
  0x1008040201008040000000007fc0000,
  0x1008040201008040000000ff8000000,
  0x1008040201008040000000ffffc0000,
  0x10080402010080400001ff000000000,
  0x10080402010080400001ff00003fe00,
  0x100804020100804003fe00000000000,
  0x100804020100804003fe00ff8000000,
  0x100804020100804003ffff000000000,
  0x1008040201008047fc0000000000000,
  0x1008040201008047fc0000ff8000000,
  0x1008040201008047fc0000ffffffe00,
  0x1008040201008047fc01ffff8000000,
  0x1008040201008047fffe00000000000,
  0x1008040201008047fffe00ff8000000,
  0x1209048241209048000000000000000,
  0x120904824120904800000000003fe00,
  0x12090482412090480001ff000000000,
  0x120904824120904ffffe00000000000,
  0x140a05028140a050000000000000000,
  0x140a05028140a05000000000003fe00,
  0x140a05028140a050000000ffffc0000,
  0x140a05028140a0500001ff000000000,
  0x140a05028140a057fffe00000000000,
  0x160b0582c160b058000000000000000,
  0x180c06030180c060000000000000000,
  0x180c06030180c06000000000003fe00,
  0x180c06030180c060000000ffffc0000,
  0x180c06030180c0600001ff000000000,
  0x180c06030180c06003fe000000001ff,
  0x180c06030180c067fc0000ffffc0000,
  0x1a0d068341a0d068000000000000000,
  0x1c0e070381c0e070000000000000000,
  0x1e0f0783c1e0f078000000000000000,
  0x1e0f0783c1e0f0780001ff00003fe00,
  0x1e0f0783c1e0f0780001ff00003ffff,
  0x1e0f0783c1e0f0780001ff007fffe00,
  0x1e0f0783c1e0f0780001ff007ffffff,
  0x1e0f0783c1e0f0780001ffff803fe00,
  0x1e0f0783c1e0f0780001ffffffffe00,
  0x1e0f0783c1e0f07803ffff00003fe00,
  0x1e0f0783c1e0f07803ffff00003ffff,
  0x1e0f0783c1e0f07803ffffff803fe00,
  0x1e0f0783c1e0f07ffc01ff00003fe00,
  0x1e0f0783c1e0f07ffc01ff007fffe00,
  0x1e0f0783c1e0f07ffc01ffff803fe00,
  0x1e0f0783c1e0f07ffc01ffffffffe00,
  0x1e0f0783c1e0f07fffffff00003fe00,
  0x1e0f0783c1e0f07fffffffff803fe00,
  0x2010080402010080000000000000000,
  0x20100804020100800000000000001ff,
  0x201008040201008000000000003fe00,
  0x2010080402010080000000007fc0000,
  0x2010080402010080000000ff8000000,
  0x2010080402010080000000ffffc0000,
  0x2010080402010080000000ffffc01ff,
  0x20100804020100800001ff000000000,
  0x201008040201008003fe00000000000,
  0x201008040201008003fe000000001ff,
  0x201008040201008003fe00ffffc0000,
  0x2010080402010087fc0000000000000,
  0x2010080402010087fc0000007fc0000,
  0x2010080402010087fc0000ff8000000,
  0x2010080402010087fc0000ffffc0000,
  0x2010080402010087fffe00000000000,
  0x2010080402010087fffe00ff8000000,
  0x2211088442211088000000000000000,
  0x22110884422110880000000000001ff,
  0x2211088442211088000000ffffffe00,
  0x221108844221108803fe00000000000,
  0x221108844221108ffc01ff000000000,
  0x2412090482412090000000000000000,
  0x2412090482412090000000007fc0000,
  0x2412090482412090000000ff8000000,
  0x2412090482412090000000ffffc0000,
  0x241209048241209003ffff000000000,
  0x2412090482412097fc0000000000000,
  0x2412090482412097fc0000007fc0000,
  0x2412090482412097fc0000ff8000000,
  0x2412090482412097fc0000ffffc0000,
  0x2412090482412097fc0000ffffc01ff,
  0x2412090482412097fc0000ffffffe00,
  0x2412090482412097fc01ffffffc0000,
  0x2412090482412097fc01ffffffffe00,
  0x2412090482412097fffe00ffffc0000,
  0x2412090482412097fffe00ffffc01ff,
  0x2412090482412097ffffffffffc0000,
  0x26130984c2613098000000000000000,
  0x26130984c261309ffc0000ffffc0000,
  0x26130984c261309ffc0000ffffc01ff,
  0x26130984c261309ffc0000ffffffe00,
  0x26130984c261309ffc01ffffffc0000,
  0x26130984c261309ffffe00ffffc0000,
  0x28140a05028140a0000000000000000,
  0x2a150a8542a150a8000000007fc0000,
  0x2c160b0582c160b0000000000000000,
  0x2c160b0582c160b00000000000001ff,
  0x2c160b0582c160b7fc0000ffffc0000,
  0x2c160b0582c160b7fc0000ffffc01ff,
  0x2c160b0582c160b7fc0000ffffffe00,
  0x2c160b0582c160b7fc01ffffffc0000,
  0x2e170b85c2e170bffc0000ffffc0000,
  0x30180c06030180c0000000000000000,
  0x32190c86432190cffc0000ff8000000,
  0x341a0d068341a0d0000000000000000,
  0x341a0d068341a0d003fe00000000000,
  0x341a0d068341a0d7fc0000ffffc0000,
  0x341a0d068341a0d7fc0000ffffffe00,
  0x341a0d068341a0d7fc01ffffffc0000,
  0x341a0d068341a0d7fffe00ffffc0000,
  0x361b0d86c361b0dffc0000ffffc0000,
  0x3c1e0f0783c1e0f7fc0000ffffc0000,
  0x3e1f0f87c3e1f0f80001ff00003fe00,
  0x3e1f0f87c3e1f0f80001ff00003ffff,
  0x3e1f0f87c3e1f0f80001ff007fffe00,
  0x3e1f0f87c3e1f0f80001ffffffffe00,
  0x3e1f0f87c3e1f0f803ffff00003fe00,
  0x3e1f0f87c3e1f0fffc0000ffffc0000,
  0x3e1f0f87c3e1f0fffc01ff00003fe00,
  0x3e1f0f87c3e1f0fffc01ffff803fe00,
  0x3e1f0f87c3e1f0fffc01ffffffffe00,
  0x3e1f0f87c3e1f0fffc01fffffffffff,
  0x3e1f0f87c3e1f0ffffffffffffffe00,
  0x4020100804020100000000000000000,
  0x40201008040201000000000000001ff,
  0x402010080402010000000000003fe00,
  0x4020100804020100000000007fc0000,
  0x4020100804020100000000007fffe00,
  0x4020100804020100000000ff8000000,
  0x4020100804020100000000ff803fe00,
  0x4020100804020100000000ffffc0000,
  0x4020100804020100000000ffffc01ff,
  0x4020100804020100000000ffffffe00,
  0x40201008040201000001ff000000000,
  0x402010080402010003fe00000000000,
  0x402010080402010003fe000000001ff,
  0x402010080402010003ffff00003fe00,
  0x4020100804020107fc0000000000000,
  0x4020100804020107fc0000ff8000000,
  0x4020100804020107fffe00000000000,
  0x4020100804020107fffe00ff8000000,
  0x4020100804020107fffe00ffffc0000,
  0x4221108844221108000000000000000,
  0x42211088442211080000000000001ff,
  0x422110884422110803fe00000000000,
  0x4422110884422110000000000000000,
  0x46231188c4623118000000ffffc0000,
  0x4824120904824120000000000000000,
  0x482412090482412000000000003ffff,
  0x4a25128944a25128000000007fc0000,
  0x5028140a05028140000000000000000,
  0x5028140a0502814003fe0000003fe00,
  0x5229148a45229148000000ff8000000,
  0x5e2f178bc5e2f1780001ff00003fe00,
  0x5e2f178bc5e2f1780001ff00003ffff,
  0x5e2f178bc5e2f1780001ff007fffe00,
  0x5e2f178bc5e2f1780001ffff803fe00,
  0x5e2f178bc5e2f1780001ffffffffe00,
  0x5e2f178bc5e2f17803ffff00003fe00,
  0x6030180c06030180000000000000000,
  0x6030180c060301800000000000001ff,
  0x6030180c06030180000000007fc0000,
  0x6030180c0603018003fe00000000000,
  0x6030180c06030187fc0000ff8000000,
  0x6231188c46231188000000000000000,
  0x6231188c462311880000000000001ff,
  0x6231188c4623118803fe00000000000,
  0x6231188c4623118803fe000000001ff,
  0x6231188c4623118803fe0000003ffff,
  0x6231188c4623118803fe00007fc01ff,
  0x6231188c4623118803fe00007ffffff,
  0x6231188c4623118803fe00ff80001ff,
  0x6231188c4623118803fe00ff803ffff,
  0x6231188c4623118803fe00ffffc01ff,
  0x6231188c4623118803fe00fffffffff,
  0x6231188c4623118803ffff0000001ff,
  0x6231188c4623118803ffff00003ffff,
  0x6231188c4623118ffffe000000001ff,
  0x6231188c4623118ffffe00007fc01ff,
  0x6231188c4623118ffffe00ff80001ff,
  0x6231188c4623118ffffe00ffffc01ff,
  0x6231188c4623118fffffff0000001ff,
  0x6432190c86432190000000000000000,
  0x6432190c8643219000000000003fe00,
  0x6432190c86432197fc0000ffffc0000,
  0x6432190c86432197fc0000ffffc01ff,
  0x6432190c86432197fc0000ffffffe00,
  0x6432190c86432197fffe00ffffc0000,
  0x6633198cc6633198000000000000000,
  0x6633198cc663319803fe000000001ff,
  0x6633198cc663319803fe0000003ffff,
  0x6633198cc663319803fe00007fc01ff,
  0x6633198cc663319803fe00ffffc01ff,
  0x6633198cc663319803ffff0000001ff,
  0x6633198cc663319ffc0000ffffc0000,
  0x6633198cc663319ffffe000000001ff,
  0x6633198cc663319ffffe00ff80001ff,
  0x6633198cc663319ffffe00ffffc01ff,
  0x6633198cc663319ffffe00fffffffff,
  0x6633198cc663319fffffffffffc01ff,
  0x6a351a8d46a351a803fe000000001ff,
  0x6a351a8d46a351a803fe0000003ffff,
  0x6a351a8d46a351a803fe00007fc01ff,
  0x6a351a8d46a351a803ffff0000001ff,
  0x6c361b0d86c361b7fc0000ffffc0000,
  0x6e371b8dc6e371b803fe000000001ff,
  0x6e371b8dc6e371bffc0000ffffc0000,
  0x6e371b8dc6e371bffffe00ffffc01ff,
  0x72391c8e472391c803fe000000001ff,
  0x72391c8e472391c803fe0000003ffff,
  0x72391c8e472391c803fe00ff80001ff,
  0x72391c8e472391c803ffff0000001ff,
  0x72391c8e472391cffffe000000001ff,
  0x72391c8e472391cffffe00ff80001ff,
  0x743a1d0e8743a1d7fc0000ffffc0000,
  0x763b1d8ec763b1d803fe000000001ff,
  0x763b1d8ec763b1dffc0000ffffc0000,
  0x763b1d8ec763b1dffffe00ffffc01ff,
  0x7a3d1e8f47a3d1e803fe000000001ff,
  0x7e3f1f8fc7e3f1f80001ff00003fe00,
  0x7e3f1f8fc7e3f1f803fe000000001ff,
  0x7e3f1f8fc7e3f1f803ffff00003ffff,
  0x7e3f1f8fc7e3f1f803ffff007ffffff,
  0x7e3f1f8fc7e3f1f803ffffff803ffff,
  0x7e3f1f8fc7e3f1f803fffffffffffff,
  0x7e3f1f8fc7e3f1fffc01ffffffffe00,
  0x7e3f1f8fc7e3f1ffffffff00003ffff,
  0x7e3f1f8fc7e3f1ffffffffff803ffff,
  0x7e3f1f8fc7e3f1fffffffffffffffff,
  0x8040201008040200000000000000000,
  0x80402010080402000000000000001ff,
  0x804020100804020000000000003fe00,
  0x8040201008040200000000007fc0000,
  0x8040201008040200000000007fc01ff,
  0x8040201008040200000000ff8000000,
  0x8040201008040200000000ffffc0000,
  0x80402010080402000001ff000000000,
  0x804020100804020003fe00000000000,
  0x804020100804020003fe00ff8000000,
  0x8040201008040207fc0000000000000,
  0x8040201008040207fc0000ff8000000,
  0x8040201008040207fc0000ffffc0000,
  0x8040201008040207fffe00000000000,
  0x8040201008040207fffe000000001ff,
  0x8040201008040207fffe00007fc0000,
  0x8040201008040207fffe00ff8000000,
  0x8241209048241208000000000000000,
  0x8442211088442210000000000000000,
  0x8844221108844220000000000000000,
  0x88442211088442200000000000001ff,
  0x8844221108844220000000007fc0000,
  0x8844221108844220000000ff803fe00,
  0x8844221108844227ffffff000000000,
  0x8a45229148a4522803fe00000000000,
  0x8c46231188c46237fc0000ff8000000,
  0x9048241209048240000000000000000,
  0x9048241209048240000000007fffe00,
  0x9048241209048240000000ff8000000,
  0x904824120904824003fe00000000000,
  0x904824120904824003fe00ff8000000,
  0x9048241209048247fc0000000000000,
  0x9048241209048247fc0000ff8000000,
  0x9048241209048247fffe00000000000,
  0x9048241209048247fffe00ff8000000,
  0x9048241209048247fffe00ff80001ff,
  0x9048241209048247fffe00ff803fe00,
  0x9048241209048247fffe00ffffc0000,
  0x9048241209048247fffe00ffffc01ff,
  0x9048241209048247fffe00ffffffe00,
  0x9048241209048247ffffffff8000000,
  0x9048241209048247ffffffff803fe00,
  0x9249249249249248000000000000000,
  0x92492492492492480000000000001ff,
  0x924924924924924ffffe00ff8000000,
  0x924924924924924ffffe00ff80001ff,
  0x924924924924924ffffe00ff803fe00,
  0x924924924924924fffffffff8000000,
  0x944a25128944a250000000000000000,
  0x944a25128944a250000000007fc0000,
  0x944a25128944a257fffe00ff8000000,
  0x944a25128944a257fffe00ff803fe00,
  0x944a25128944a257fffe00ffffc0000,
  0x944a25128944a257ffffffff8000000,
  0x964b2592c964b25ffffe00ff8000000,
  0x984c26130984c260000000000000000,
  0x984c26130984c267fffe00ff8000000,
  0x984c26130984c267fffe00ff80001ff,
  0x984c26130984c267fffe00ff803fe00,
  0x984c26130984c267fffe00ffffc0000,
  0x984c26130984c267ffffffff8000000,
  0x9a4d269349a4d26ffffe00ff8000000,
  0x9c4e271389c4e277fffe00ff8000000,
  0x9e4f2793c9e4f2780001ff00003fe00,
  0x9e4f2793c9e4f2780001ff00003ffff,
  0x9e4f2793c9e4f2780001ff007fffe00,
  0x9e4f2793c9e4f2780001ffff803fe00,
  0x9e4f2793c9e4f27803ffff00003fe00,
  0x9e4f2793c9e4f27ffc01ffff803fe00,
  0x9e4f2793c9e4f27ffffe00ff8000000,
  0x9e4f2793c9e4f27fffffff00003fe00,
  0x9e4f2793c9e4f27fffffffff803fe00,
  0x9e4f2793c9e4f27fffffffff803ffff,
  0x9e4f2793c9e4f27fffffffffffffe00,
  0xa05028140a050280000000000000000,
  0xa05028140a05028003fe00007fc0000,
  0xa05028140a050287fc0000ff80001ff,
  0xa45229148a452290000000000000000,
  0xa45229148a452297fc0000ffffc0000,
  0xa45229148a452297fc0000ffffc01ff,
  0xa45229148a452297fffe00ffffc0000,
  0xa6532994ca65329ffc0000ffffc0000,
  0xac562b158ac562b7fc0000ffffc0000,
  0xb0582c160b0582c0000000000000000,
  0xb0582c160b0582c7fffe00ff8000000,
  0xb0582c160b0582c7fffe00ff80001ff,
  0xb0582c160b0582c7fffe00ffffc0000,
  0xb2592c964b2592cffffe00ff8000000,
  0xb45a2d168b45a2d0000000000000000,
  0xb45a2d168b45a2d7fc0000ffffc0000,
  0xb45a2d168b45a2d7fffe00ff8000000,
  0xb45a2d168b45a2d7fffe00ffffc0000,
  0xb45a2d168b45a2d7fffe00ffffc01ff,
  0xb45a2d168b45a2d7fffe00ffffffe00,
  0xb45a2d168b45a2d7ffffffffffc0000,
  0xb65b2d96cb65b2dffc0000ffffc0000,
  0xb65b2d96cb65b2dffffe00ff8000000,
  0xb65b2d96cb65b2dffffe00ffffc0000,
  0xb85c2e170b85c2e7fffe00ff8000000,
  0xbc5e2f178bc5e2f7fc0000ffffc0000,
  0xbc5e2f178bc5e2f7fffe00ff8000000,
  0xbc5e2f178bc5e2f7fffe00ffffc0000,
  0xbe5f2f97cbe5f2f80001ff00003fe00,
  0xbe5f2f97cbe5f2fffc01ffffffffe00,
  0xbe5f2f97cbe5f2ffffffffff803fe00,
  0xbe5f2f97cbe5f2ffffffffffffffe00,
  0xc06030180c060300000000000000000,
  0xc06030180c060300000000ff80001ff,
  0xc06030180c06030003fe00007fc0000,
  0xd068341a0d068340000000000000000,
  0xd068341a0d068347fffe00ff8000000,
  0xd068341a0d068347fffe00ff80001ff,
  0xd068341a0d068347fffe00ff803fe00,
  0xd068341a0d068347fffe00ffffc0000,
  0xd269349a4d26934ffffe00ff8000000,
  0xd46a351a8d46a357fffe00ff8000000,
  0xd86c361b0d86c367fffe00ff8000000,
  0xde6f379bcde6f3780001ff00003fe00,
  0xde6f379bcde6f37fffffffff803fe00,
  0xe271389c4e27138803fe000000001ff,
  0xe271389c4e27138803fe00007fc01ff,
  0xe271389c4e27138803fe00ff80001ff,
  0xe271389c4e27138ffffe000000001ff,
  0xe271389c4e27138ffffe00ff80001ff,
  0xe472391c8e472397fc0000ffffc0000,
  0xe673399cce67339803fe000000001ff,
  0xe673399cce67339ffffe00ffffc01ff,
  0xea753a9d4ea753a803fe000000001ff,
  0xf0783c1e0f0783c7fffe00ff8000000,
  0xf2793c9e4f2793c803fe000000001ff,
  0xf2793c9e4f2793cffffe00ff8000000,
  0xf2793c9e4f2793cffffe00ff80001ff,
  0xf2793c9e4f2793cffffe00ff803ffff,
  0xf2793c9e4f2793cffffe00ffffc01ff,
  0xf2793c9e4f2793cfffffffff80001ff,
  0xf47a3d1e8f47a3d7fffe00ffffc0000,
  0xf67b3d9ecf67b3d803fe000000001ff,
  0xf67b3d9ecf67b3dffffe00ff8000000,
  0xf67b3d9ecf67b3dffffe00ff80001ff,
  0xf67b3d9ecf67b3dffffe00ffffc01ff,
  0xfa7d3e9f4fa7d3e803fe000000001ff,
  0xfa7d3e9f4fa7d3effffe00ff80001ff,
  0xfe7f3f9fcfe7f3f803ffff00003ffff,
  0xfe7f3f9fcfe7f3ffffffffff803ffff,
  0xfe7f3f9fcfe7f3fffffffffffffffff,
  0x10080402010080400000000000000000,
  0x100804020100804000000000000001ff,
  0x1008040201008040000000000003fe00,
  0x10080402010080400000000007fc0000,
  0x10080402010080400000000007fc01ff,
  0x10080402010080400000000ff8000000,
  0x10080402010080400000000ffffc0000,
  0x100804020100804000001ff000000000,
  0x100804020100804000001ff007fffe00,
  0x1008040201008040003fe00000000000,
  0x1008040201008040003ffff000000000,
  0x10080402010080407fc0000000000000,
  0x10080402010080407fc0000ff8000000,
  0x10080402010080407fc0000ffffc0000,
  0x10080402010080407fc01ff000000000,
  0x10080402010080407fffe00000000000,
  0x10080402010080407fffe000000001ff,
  0x10080402010080407fffe00ffffc0000,
  0x10080402010080407ffffff000000000,
  0x1028140a050281408000000000000000,
  0x1028140a0502814080001ff0000001ff,
  0x10482412090482410000000000000000,
  0x104824120904824100001ff007fc0000,
  0x10884422110884420000000000000000,
  0x108844221108844200000000000001ff,
  0x10884422110884420000000007fc0000,
  0x10a8542a150a8542803fe00000000000,
  0x10c86432190c86437fc0000000000000,
  0x11088442211088440000000000000000,
  0x1188c46231188c467fffe00000000000,
  0x11e8f47a3d1e8f4780001ff00003fe00,
  0x11e8f47a3d1e8f4780001ff00003ffff,
  0x11e8f47a3d1e8f4780001ff007fffe00,
  0x11e8f47a3d1e8f47803ffff00003fe00,
  0x11e8f47a3d1e8f47ffc01ff00003fe00,
  0x11e8f47a3d1e8f47fffffff00003fe00,
  0x12090482412090480000000000000000,
  0x1209048241209048003fe00007fc0000,
  0x12090482412090487fc00000000001ff,
  0x12492492492492490000000000000000,
  0x12492492492492497fc0000ffffc0000,
  0x12492492492492497fc0000ffffc01ff,
  0x12492492492492497fc01ffffffc0000,
  0x12492492492492497fffe00ffffc0000,
  0x1269349a4d269349ffc0000ffffc0000,
  0x12c964b2592c964b7fc0000ffffc0000,
  0x1349a4d269349a4d7fc0000ffffc0000,
  0x13e9f4fa7d3e9f4f80001ff00003fe00,
  0x13e9f4fa7d3e9f4fffc01ffffffffe00,
  0x140a05028140a0500000000000000000,
  0x140a05028140a050003fe00007fc0000,
  0x15eaf57abd5eaf5780001ff00003fe00,
  0x162b158ac562b158803fe000000001ff,
  0x162b158ac562b158803fe00007fc01ff,
  0x162b158ac562b158803ffff0000001ff,
  0x162b158ac562b158ffffe000000001ff,
  0x164b2592c964b2597fc0000ffffc0000,
  0x166b359acd66b359803fe000000001ff,
  0x166b359acd66b359ffffe00ffffc01ff,
  0x16ab55aad56ab55a803fe000000001ff,
  0x172b95cae572b95c803fe000000001ff,
  0x17ebf5fafd7ebf5f803ffff00003ffff,
  0x180c06030180c0600000000000000000,
  0x180c06030180c06000000000000001ff,
  0x180c06030180c0600000000007fc0000,
  0x180c06030180c060003fe00000000000,
  0x180c06030180c0607fc0000ff8000000,
  0x188c46231188c4620000000000000000,
  0x188c46231188c46200000000000001ff,
  0x188c46231188c4620000000007fc0000,
  0x188c46231188c4620000000007fc01ff,
  0x188c46231188c4620000000007ffffff,
  0x188c46231188c4620000000ffffc01ff,
  0x188c46231188c4620000000fffffffff,
  0x188c46231188c46200001ff007fc01ff,
  0x188c46231188c46200001ff007ffffff,
  0x188c46231188c462003fe00007fc01ff,
  0x188c46231188c462003fe00ffffc01ff,
  0x188c46231188c462003ffff007fc01ff,
  0x188c46231188c4627fc0000007fc01ff,
  0x188c46231188c4627fc0000ffffc01ff,
  0x188c46231188c4627fc01ff007fc01ff,
  0x188c46231188c4627fffe00007fc01ff,
  0x188c46231188c4627fffe00ffffc01ff,
  0x188c46231188c4627ffffff007fc01ff,
  0x18ac562b158ac5628000000007fc01ff,
  0x18ac562b158ac5628000000007ffffff,
  0x18ac562b158ac56280001ff007fc01ff,
  0x18ac562b158ac562803fe00007fc01ff,
  0x18cc6633198cc6630000000007fc01ff,
  0x18cc6633198cc6630000000007ffffff,
  0x18cc6633198cc6630000000ffffc01ff,
  0x18cc6633198cc66300001ff007fc01ff,
  0x18cc6633198cc6637fc0000007fc01ff,
  0x18cc6633198cc6637fc0000ffffc01ff,
  0x18ec763b1d8ec7638000000007fc01ff,
  0x190c86432190c8640000000000000000,
  0x190c86432190c86400001ff000000000,
  0x190c86432190c8647fffe00ff8000000,
  0x190c86432190c8647fffe00ff80001ff,
  0x190c86432190c8647fffe00ffffc0000,
  0x190c86432190c8647ffffffff8000000,
  0x192c964b2592c964ffffe00ff8000000,
  0x194ca6532994ca657fffe00ff8000000,
  0x198cc6633198cc660000000000000000,
  0x198cc6633198cc660000000007fc01ff,
  0x198cc6633198cc660000000007ffffff,
  0x198cc6633198cc660000000ffffc01ff,
  0x198cc6633198cc6600001ff007fc01ff,
  0x198cc6633198cc66003fe00007fc01ff,
  0x198cc6633198cc667fc0000ffffc01ff,
  0x198cc6633198cc667fffe00007fc01ff,
  0x198cc6633198cc667fffe00ff8000000,
  0x198cc6633198cc667fffe00ffffc01ff,
  0x198cc6633198cc667fffe00fffffffff,
  0x198cc6633198cc667ffffffffffc01ff,
  0x19acd66b359acd668000000007fc01ff,
  0x19acd66b359acd66ffffe00ff8000000,
  0x19acd66b359acd66ffffe00ffffc01ff,
  0x19cce673399cce670000000007fc01ff,
  0x19cce673399cce677fffe00ff8000000,
  0x19cce673399cce677fffe00ffffc01ff,
  0x19ecf67b3d9ecf678000000007fc01ff,
  0x19ecf67b3d9ecf6780001ff00003fe00,
  0x19ecf67b3d9ecf6780001ff007ffffff,
  0x19ecf67b3d9ecf6780001fffffffffff,
  0x19ecf67b3d9ecf67803ffff007ffffff,
  0x19ecf67b3d9ecf67ffc01ff007ffffff,
  0x19ecf67b3d9ecf67ffc01fffffffffff,
  0x19ecf67b3d9ecf67fffffff007ffffff,
  0x19ecf67b3d9ecf67fffffffff803fe00,
  0x19ecf67b3d9ecf67ffffffffffffffff,
  0x1a4d269349a4d2697fc0000ffffc0000,
  0x1a8d46a351a8d46a0000000007fc01ff,
  0x1a8d46a351a8d46a0000000ffffc01ff,
  0x1a8d46a351a8d46a003fe00007fc01ff,
  0x1a8d46a351a8d46a7fc0000007fc01ff,
  0x1a8d46a351a8d46a7fc0000ffffc01ff,
  0x1aad56ab55aad56a8000000007fc01ff,
  0x1acd66b359acd66b0000000007fc01ff,
  0x1acd66b359acd66b7fc0000ffffc0000,
  0x1acd66b359acd66b7fc0000ffffc01ff,
  0x1acd66b359acd66b7fc0000fffffffff,
  0x1acd66b359acd66b7fc01ffffffc01ff,
  0x1acd66b359acd66b7fffe00ffffc01ff,
  0x1aed76bb5daed76b8000000007fc01ff,
  0x1aed76bb5daed76bffc0000ffffc01ff,
  0x1b0d86c361b0d86c7fffe00ff8000000,
  0x1b4da6d369b4da6d7fffe00ffffc0000,
  0x1b8dc6e371b8dc6e0000000007fc01ff,
  0x1b8dc6e371b8dc6e7fffe00ffffc01ff,
  0x1bcde6f379bcde6f0000000007fc01ff,
  0x1bcde6f379bcde6f7fc0000ffffc0000,
  0x1bcde6f379bcde6f7fc0000ffffc01ff,
  0x1bcde6f379bcde6f7fffe00ffffc01ff,
  0x1bedf6fb7dbedf6f80001ff007ffffff,
  0x1bedf6fb7dbedf6fffc01fffffffffff,
  0x1bedf6fb7dbedf6fffffffffffffffff,
  0x1c8e472391c8e4720000000007fc01ff,
  0x1c8e472391c8e4720000000007ffffff,
  0x1c8e472391c8e4720000000ffffc01ff,
  0x1c8e472391c8e472003fe00007fc01ff,
  0x1cae572b95cae5728000000007fc01ff,
  0x1cce673399cce6730000000007fc01ff,
  0x1d0e8743a1d0e8747fffe00ff8000000,
  0x1d8ec763b1d8ec760000000007fc01ff,
  0x1d8ec763b1d8ec767fffe00ffffc01ff,
  0x1deef77bbddeef7780001ff007ffffff,
  0x1e2f178bc5e2f178803fe000000001ff,
  0x1e8f47a3d1e8f47a0000000007fc01ff,
  0x1eaf57abd5eaf57a8000000007fc01ff,
  0x1eaf57abd5eaf57a803fe000000001ff,
  0x1eaf57abd5eaf57a803fe00007fc01ff,
  0x1eaf57abd5eaf57a803fe00007ffffff,
  0x1eaf57abd5eaf57a803fe00ffffc01ff,
  0x1eaf57abd5eaf57a803ffff007fc01ff,
  0x1eaf57abd5eaf57affffe00007fc01ff,
  0x1eaf57abd5eaf57affffe00ffffc01ff,
  0x1ecf67b3d9ecf67b7fc0000ffffc01ff,
  0x1eef77bbddeef77b8000000007fc01ff,
  0x1eef77bbddeef77b803fe00007fc01ff,
  0x1eef77bbddeef77bffffe00ffffc01ff,
  0x1f2f97cbe5f2f97cffffe00ff80001ff,
  0x1fafd7ebf5fafd7e803fe000000001ff,
  0x1fafd7ebf5fafd7e803fe00007fc01ff,
  0x1fafd7ebf5fafd7effffe00ffffc01ff,
  0x1feff7fbfdfeff7f803ffff007ffffff,
  0x1feff7fbfdfeff7fffffe00ffffc01ff,
  0x1feff7fbfdfeff7fffffffffffffffff,
  0x20100804020100800000000000000000,
  0x201008040201008000000000000001ff,
  0x2010080402010080000000000003fe00,
  0x20100804020100800000000007fc0000,
  0x20100804020100800000000007fffe00,
  0x20100804020100800000000ff8000000,
  0x20100804020100800000000ff803fe00,
  0x20100804020100800000000ffffc0000,
  0x20100804020100800000000ffffffe00,
  0x201008040201008000001ff000000000,
  0x2010080402010080003fe00000000000,
  0x2010080402010080003fe00007fc01ff,
  0x2010080402010080003fe00ff8000000,
  0x2010080402010080003ffff000000000,
  0x20100804020100807fc0000000000000,
  0x20100804020100807fc0000007fc0000,
  0x20100804020100807fc0000ff8000000,
  0x20100804020100807fc01ff000000000,
  0x20100804020100807fffe00000000000,
  0x20100804020100807fffe00ffffc0000,
  0x20100804020100807ffffff000000000,
  0x2030180c060301808000000000000000,
  0x2030180c06030180803fe0000003fe00,
  0x205028140a0502810000000000000000,
  0x205028140a05028100001ffffffc0000,
  0x205028140a0502817fc000000003fe00,
  0x20904824120904820000000000000000,
  0x209048241209048200001ff007fc0000,
  0x21108844221108840000000000000000,
  0x211088442211088400001ffff8000000,
  0x21108844221108847fffe0000003fe00,
  0x21f0f87c3e1f0f8780001ff00003fe00,
  0x21f0f87c3e1f0f8780001ff007fffe00,
  0x21f0f87c3e1f0f8780001ffff803fe00,
  0x21f0f87c3e1f0f8780001ffffffffe00,
  0x21f0f87c3e1f0f87803ffff00003fe00,
  0x21f0f87c3e1f0f87ffc01ff00003fe00,
  0x21f0f87c3e1f0f87fffffff00003fe00,
  0x22110884422110880000000000000000,
  0x2211088442211088003fe00ffffc0000,
  0x225128944a2512890000000000000000,
  0x225128944a2512897fc0000ffffc0000,
  0x225128944a2512897fc0000ffffffe00,
  0x225128944a2512897fc01ffffffc0000,
  0x225128944a2512897fffe00ffffc0000,
  0x2271389c4e271389ffc0000ffffc0000,
  0x22d168b45a2d168b7fc0000ffffc0000,
  0x2351a8d46a351a8d7fc0000ffffc0000,
  0x23f1f8fc7e3f1f8f80001ff00003fe00,
  0x23f1f8fc7e3f1f8fffc01ffffffffe00,
  0x24120904824120900000000000000000,
  0x2412090482412090000000000003fe00,
  0x24120904824120900000000007fc0000,
  0x24120904824120900000000007fffe00,
  0x24120904824120900000000ff8000000,
  0x24120904824120900000000ff803fe00,
  0x24120904824120900000000ffffc0000,
  0x24120904824120900000000ffffffe00,
  0x24120904824120900000000fffffffff,
  0x241209048241209000001ffffffffe00,
  0x2412090482412090003fe00ffffffe00,
  0x2412090482412090003fe00fffffffff,
  0x2412090482412090003ffffffffffe00,
  0x24120904824120907fc0000ffffffe00,
  0x24120904824120907fc01ffffffffe00,
  0x24120904824120907fffe00000000000,
  0x24120904824120907fffe00ffffffe00,
  0x24120904824120907ffffffffffffe00,
  0x2432190c864321908000000000000000,
  0x2432190c864321908000000ffffffe00,
  0x2432190c864321908000000fffffffff,
  0x2432190c8643219080001ff000000000,
  0x2432190c8643219080001ffffffffe00,
  0x2432190c86432190803fe00ffffffe00,
  0x245229148a4522910000000000000000,
  0x245229148a4522910000000ffffffe00,
  0x245229148a45229100001ffffffffe00,
  0x245229148a4522917fc0000ffffffe00,
  0x2472391c8e4723918000000ffffffe00,
  0x24924924924924920000000000000000,
  0x24924924924924920000000ffffffe00,
  0x24924924924924920000000fffffffff,
  0x249249249249249200001ffffffffe00,
  0x24b2592c964b25928000000ffffffe00,
  0x24d269349a4d26930000000ffffffe00,
  0x24f2793c9e4f27938000000ffffffe00,
  0x25128944a25128940000000000000000,
  0x25128944a25128940000000ffffffe00,
  0x25128944a251289400001ffffffffe00,
  0x25128944a2512894003fe00ffffffe00,
  0x25128944a25128947fc0000ffffffe00,
  0x25128944a25128947fffe00ffffffe00,
  0x2532994ca65329948000000ffffffe00,
  0x2552a954aa552a950000000ffffffe00,
  0x2572b95cae572b958000000ffffffe00,
  0x2592c964b2592c960000000ffffffe00,
  0x25b2d96cb65b2d968000000ffffffe00,
  0x25d2e974ba5d2e970000000ffffffe00,
  0x25f2f97cbe5f2f9780001ff00003fe00,
  0x25f2f97cbe5f2f9780001ffffffffe00,
  0x25f2f97cbe5f2f9780001fffffffffff,
  0x25f2f97cbe5f2f97803ffffffffffe00,
  0x25f2f97cbe5f2f97ffc01ffffffffe00,
  0x25f2f97cbe5f2f97fffffffffffffe00,
  0x26130984c26130980000000000000000,
  0x26130984c26130980000000ffffffe00,
  0x26130984c26130980000000fffffffff,
  0x26130984c2613098003fe00ffffffe00,
  0x26130984c26130987fc0000000000000,
  0x26130984c26130987fc0000ffffffe00,
  0x2633198cc66331988000000000000000,
  0x2633198cc66331988000000ffffffe00,
  0x2633198cc6633198803fe000000001ff,
  0x2633198cc6633198803fe0000003ffff,
  0x2633198cc6633198803fe00007fc01ff,
  0x2633198cc6633198803fe00ff80001ff,
  0x2633198cc6633198803fe00ffffc01ff,
  0x2633198cc6633198803fe00fffffffff,
  0x2633198cc6633198803ffff0000001ff,
  0x2633198cc6633198803fffffffffffff,
  0x2633198cc6633198ffffe000000001ff,
  0x2633198cc6633198ffffe00fffffffff,
  0x26532994ca6532990000000000000000,
  0x26532994ca6532990000000ffffffe00,
  0x26532994ca6532997fc0000ffffc0000,
  0x26532994ca6532997fc0000ffffffe00,
  0x26532994ca6532997fc0000fffffffff,
  0x26532994ca6532997fc01ffffffffe00,
  0x26532994ca6532997fffe00ffffffe00,
  0x2673399cce6733998000000ffffffe00,
  0x2673399cce673399803fe000000001ff,
  0x2673399cce673399803fe00fffffffff,
  0x2673399cce673399ffc0000ffffc0000,
  0x2673399cce673399ffc0000ffffffe00,
  0x2673399cce673399ffffe00ffffc01ff,
  0x2673399cce673399ffffe00fffffffff,
  0x269349a4d269349a0000000ffffffe00,
  0x26b359acd66b359a8000000ffffffe00,
  0x26b359acd66b359a803fe000000001ff,
  0x26b359acd66b359a803fe00fffffffff,
  0x26d369b4da6d369b7fc0000ffffffe00,
  0x271389c4e271389c0000000ffffffe00,
  0x273399cce673399c803fe000000001ff,
  0x273399cce673399c803fe00fffffffff,
  0x2753a9d4ea753a9d7fc0000ffffffe00,
  0x27f3f9fcfe7f3f9f80001ff00003fe00,
  0x27f3f9fcfe7f3f9f80001ffffffffe00,
  0x27f3f9fcfe7f3f9f803ffff00003ffff,
  0x27f3f9fcfe7f3f9f803fffffffffffff,
  0x27f3f9fcfe7f3f9fffc01ffffffffe00,
  0x27f3f9fcfe7f3f9fffffffffffffffff,
  0x28140a05028140a00000000000000000,
  0x28140a05028140a07fffe00007fc0000,
  0x29148a45229148a40000000000000000,
  0x29148a45229148a47fffe00ff8000000,
  0x29148a45229148a47fffe00ff803fe00,
  0x29148a45229148a47fffe00ffffc0000,
  0x29148a45229148a47ffffffff8000000,
  0x29349a4d269349a4ffffe00ff8000000,
  0x2954aa552a954aa57fffe00ff8000000,
  0x2994ca6532994ca67fffe00ff8000000,
  0x29f4fa7d3e9f4fa780001ff00003fe00,
  0x29f4fa7d3e9f4fa7fffffffff803fe00,
  0x2a552a954aa552a97fc0000ffffc0000,
  0x2b158ac562b158ac7fffe00ff8000000,
  0x2b55aad56ab55aad7fffe00ffffc0000,
  0x2c160b0582c160b00000000000000000,
  0x2c160b0582c160b00000000ffffffe00,
  0x2c160b0582c160b00000000fffffffff,
  0x2c160b0582c160b0003fe00ffffffe00,
  0x2c160b0582c160b07fc0000ffffffe00,
  0x2c160b0582c160b07fffe00ffffffe00,
  0x2c361b0d86c361b08000000ffffffe00,
  0x2c562b158ac562b10000000ffffffe00,
  0x2c964b2592c964b20000000ffffffe00,
  0x2d168b45a2d168b40000000000000000,
  0x2d168b45a2d168b40000000ffffffe00,
  0x2d168b45a2d168b47fffe00ff8000000,
  0x2d168b45a2d168b47fffe00ffffffe00,
  0x2d168b45a2d168b47fffe00fffffffff,
  0x2d168b45a2d168b47ffffffffffffe00,
  0x2d369b4da6d369b4ffffe00ffffffe00,
  0x2d56ab55aad56ab50000000ffffffe00,
  0x2d56ab55aad56ab57fffe00ffffffe00,
  0x2d96cb65b2d96cb67fffe00ffffffe00,
  0x2df6fb7dbedf6fb780001ffffffffe00,
  0x2df6fb7dbedf6fb7fffffffffffffe00,
  0x2e170b85c2e170b80000000ffffffe00,
  0x2e371b8dc6e371b8803fe000000001ff,
  0x2e371b8dc6e371b8803fe00fffffffff,
  0x2e572b95cae572b97fc0000ffffffe00,
  0x2f178bc5e2f178bc7fffe00ff8000000,
  0x2f178bc5e2f178bc7fffe00ffffffe00,
  0x2f379bcde6f379bcffffe00ff80001ff,
  0x2f379bcde6f379bcffffe00fffffffff,
  0x2f57abd5eaf57abd7fffe00ffffffe00,
  0x2f77bbddeef77bbdffffe00fffffffff,
  0x2ff7fbfdfeff7fbffffffffffffffe00,
  0x2ff7fbfdfeff7fbfffffffffffffffff,
  0x30180c06030180c00000000000000000,
  0x30180c06030180c00000000ffffc0000,
  0x30180c06030180c000001ff000000000,
  0x30180c06030180c0003fe00000000000,
  0x30180c06030180c0003ffff000000000,
  0x30180c06030180c07fc0000000000000,
  0x30180c06030180c07fc01ff000000000,
  0x30180c06030180c07fffe00000000000,
  0x30180c06030180c07ffffff000000000,
  0x30180c06030180c07ffffff0000001ff,
  0x30180c06030180c07ffffff00003fe00,
  0x30180c06030180c07ffffff007fc0000,
  0x30180c06030180c07ffffff007fc01ff,
  0x30180c06030180c07ffffff007fffe00,
  0x30180c06030180c07ffffffff8000000,
  0x30180c06030180c07ffffffff803fe00,
  0x30180c06030180c07ffffffffffc0000,
  0x30180c06030180c07ffffffffffffe00,
  0x30381c0e070381c08000000000000000,
  0x30381c0e070381c0fffffff000000000,
  0x30381c0e070381c0fffffff0000001ff,
  0x30381c0e070381c0fffffff00003fe00,
  0x30582c160b0582c10000000000000000,
  0x30582c160b0582c17ffffff000000000,
  0x30582c160b0582c17ffffff00003fe00,
  0x30582c160b0582c17ffffff007fc0000,
  0x30582c160b0582c17ffffffff8000000,
  0x30582c160b0582c17ffffffffffc0000,
  0x30783c1e0f0783c1fffffff000000000,
  0x30984c26130984c20000000000000000,
  0x30984c26130984c2000000000003fe00,
  0x30984c26130984c27ffffff000000000,
  0x30984c26130984c27ffffff0000001ff,
  0x30984c26130984c27ffffff00003fe00,
  0x30984c26130984c27ffffff007fc0000,
  0x30b85c2e170b85c2fffffff000000000,
  0x30d86c361b0d86c37ffffff000000000,
  0x30f87c3e1f0f87c3fffffff000000000,
  0x31188c46231188c40000000000000000,
  0x31188c46231188c47ffffff000000000,
  0x31188c46231188c47ffffff00003fe00,
  0x31188c46231188c47ffffffff8000000,
  0x31389c4e271389c4fffffff000000000,
  0x3158ac562b158ac57ffffff000000000,
  0x3178bc5e2f178bc5fffffff000000000,
  0x3198cc6633198cc67ffffff000000000,
  0x31b8dc6e371b8dc6fffffff000000000,
  0x31d8ec763b1d8ec77ffffff000000000,
  0x31f8fc7e3f1f8fc780001ff00003fe00,
  0x31f8fc7e3f1f8fc7fffffff00003fe00,
  0x31f8fc7e3f1f8fc7fffffff00003ffff,
  0x31f8fc7e3f1f8fc7fffffff007fffe00,
  0x31f8fc7e3f1f8fc7fffffffff803fe00,
  0x31f8fc7e3f1f8fc7fffffffffffffe00,
  0x32190c86432190c80000000000000000,
  0x32190c86432190c87ffffff000000000,
  0x32190c86432190c87ffffff0000001ff,
  0x32190c86432190c87ffffff007fc0000,
  0x32190c86432190c87ffffffff8000000,
  0x32190c86432190c87ffffffffffc0000,
  0x32391c8e472391c8fffffff000000000,
  0x32592c964b2592c90000000000000000,
  0x32592c964b2592c97fc0000ffffc0000,
  0x32592c964b2592c97ffffff000000000,
  0x32592c964b2592c97ffffffffffc0000,
  0x32592c964b2592c97ffffffffffc01ff,
  0x32592c964b2592c97ffffffffffffe00,
  0x32793c9e4f2793c9fffffffffffc0000,
  0x32994ca6532994ca7ffffff000000000,
  0x32d96cb65b2d96cb7ffffffffffc0000,
  0x33198cc6633198cc7ffffff000000000,
  0x3359acd66b359acd7ffffff000000000,
  0x3359acd66b359acd7ffffffffffc0000,
  0x33f9fcfe7f3f9fcffffffff00003fe00,
  0x33f9fcfe7f3f9fcffffffffffffffe00,
  0x341a0d068341a0d00000000000000000,
  0x341a0d068341a0d000000000000001ff,
  0x341a0d068341a0d00000000ffffffe00,
  0x341a0d068341a0d00000000fffffffff,
  0x341a0d068341a0d000001ffffffffe00,
  0x341a0d068341a0d0003fe00ffffffe00,
  0x341a0d068341a0d07fc0000ffffffe00,
  0x341a0d068341a0d07fffe00ffffffe00,
  0x341a0d068341a0d07ffffff000000000,
  0x341a0d068341a0d07ffffff0000001ff,
  0x341a0d068341a0d07ffffff00003fe00,
  0x341a0d068341a0d07ffffff007fc0000,
  0x341a0d068341a0d07ffffffff8000000,
  0x341a0d068341a0d07ffffffffffc0000,
  0x341a0d068341a0d07ffffffffffffe00,
  0x341a0d068341a0d07fffffffffffffff,
  0x343a1d0e8743a1d08000000000000000,
  0x343a1d0e8743a1d08000000ffffffe00,
  0x343a1d0e8743a1d0fffffff000000000,
  0x343a1d0e8743a1d0fffffffffffffe00,
  0x345a2d168b45a2d10000000ffffffe00,
  0x345a2d168b45a2d17ffffff000000000,
  0x345a2d168b45a2d17ffffffffffffe00,
  0x349a4d269349a4d20000000000000000,
  0x349a4d269349a4d20000000ffffffe00,
  0x349a4d269349a4d27ffffff000000000,
  0x349a4d269349a4d27ffffffffffffe00,
  0x351a8d46a351a8d40000000ffffffe00,
  0x351a8d46a351a8d47ffffff000000000,
  0x351a8d46a351a8d47ffffffffffffe00,
  0x35fafd7ebf5fafd780001ff00003fe00,
  0x35fafd7ebf5fafd780001ffffffffe00,
  0x35fafd7ebf5fafd7fffffff00003fe00,
  0x35fafd7ebf5fafd7fffffffffffffe00,
  0x361b0d86c361b0d80000000000000000,
  0x361b0d86c361b0d80000000ffffffe00,
  0x361b0d86c361b0d87ffffff000000000,
  0x361b0d86c361b0d87ffffffffffffe00,
  0x363b1d8ec763b1d88000000000000000,
  0x363b1d8ec763b1d8803fe000000001ff,
  0x363b1d8ec763b1d8803fe00fffffffff,
  0x363b1d8ec763b1d8fffffff000000000,
  0x363b1d8ec763b1d8fffffff0000001ff,
  0x363b1d8ec763b1d8fffffff00003ffff,
  0x363b1d8ec763b1d8fffffff007fc01ff,
  0x363b1d8ec763b1d8fffffffff80001ff,
  0x363b1d8ec763b1d8fffffffffffc01ff,
  0x363b1d8ec763b1d8ffffffffffffffff,
  0x365b2d96cb65b2d97fc0000ffffc0000,
  0x365b2d96cb65b2d97fc0000ffffffe00,
  0x365b2d96cb65b2d97ffffffffffc0000,
  0x365b2d96cb65b2d97ffffffffffffe00,
  0x367b3d9ecf67b3d9fffffff0000001ff,
  0x367b3d9ecf67b3d9fffffffffffc01ff,
  0x367b3d9ecf67b3d9ffffffffffffffff,
  0x36bb5daed76bb5dafffffff0000001ff,
  0x373b9dcee773b9dcfffffff0000001ff,
  0x37fbfdfeff7fbfdffffffff00003ffff,
  0x37fbfdfeff7fbfdffffffffffffffe00,
  0x37fbfdfeff7fbfdfffffffffffffffff,
  0x381c0e070381c0e00000000000000000,
  0x381c0e070381c0e00000000ff8000000,
  0x381c0e070381c0e07ffffff000000000,
  0x381c0e070381c0e07ffffff0000001ff,
  0x381c0e070381c0e07ffffff007fc0000,
  0x381c0e070381c0e07ffffffff8000000,
  0x383c1e0f0783c1e0fffffff000000000,
  0x385c2e170b85c2e17ffffff000000000,
  0x389c4e271389c4e20000000000000000,
  0x389c4e271389c4e20000000007fc01ff,
  0x389c4e271389c4e20000000007ffffff,
  0x389c4e271389c4e20000000ffffc01ff,
  0x389c4e271389c4e200001ff007fc01ff,
  0x389c4e271389c4e2003fe00007fc01ff,
  0x389c4e271389c4e27fc0000007fc01ff,
  0x389c4e271389c4e27fffe00007fc01ff,
  0x389c4e271389c4e27ffffff000000000,
  0x389c4e271389c4e27ffffff007fc01ff,
  0x389c4e271389c4e27ffffff007ffffff,
  0x389c4e271389c4e27ffffffffffc01ff,
  0x38bc5e2f178bc5e28000000007fc01ff,
  0x38bc5e2f178bc5e2fffffff000000000,
  0x38bc5e2f178bc5e2fffffff007fc01ff,
  0x38dc6e371b8dc6e30000000007fc01ff,
  0x38dc6e371b8dc6e37ffffff007fc01ff,
  0x391c8e472391c8e40000000000000000,
  0x391c8e472391c8e47fffe00ff8000000,
  0x391c8e472391c8e47ffffff000000000,
  0x391c8e472391c8e47ffffffff8000000,
  0x391c8e472391c8e47ffffffff80001ff,
  0x391c8e472391c8e47ffffffff803fe00,
  0x391c8e472391c8e47ffffffffffc0000,
  0x393c9e4f2793c9e4fffffffff8000000,
  0x395cae572b95cae57ffffffff8000000,
  0x399cce673399cce60000000007fc01ff,
  0x399cce673399cce67fffe00ff8000000,
  0x399cce673399cce67fffe00ffffc01ff,
  0x399cce673399cce67ffffff000000000,
  0x399cce673399cce67ffffff007fc01ff,
  0x399cce673399cce67ffffffff8000000,
  0x399cce673399cce67ffffffffffc01ff,
  0x39fcfe7f3f9fcfe780001ff00003fe00,
  0x39fcfe7f3f9fcfe780001ff007ffffff,
  0x39fcfe7f3f9fcfe7fffffff00003fe00,
  0x39fcfe7f3f9fcfe7fffffff007ffffff,
  0x39fcfe7f3f9fcfe7fffffffff803fe00,
  0x39fcfe7f3f9fcfe7ffffffffffffffff,
  0x3a1d0e8743a1d0e87ffffff000000000,
  0x3a5d2e974ba5d2e97fc0000ffffc0000,
  0x3a5d2e974ba5d2e97ffffffffffc0000,
  0x3a9d4ea753a9d4ea0000000007fc01ff,
  0x3a9d4ea753a9d4ea7ffffff007fc01ff,
  0x3add6eb75badd6eb7fc0000ffffc01ff,
  0x3add6eb75badd6eb7ffffffffffc01ff,
  0x3b1d8ec763b1d8ec7ffffffff8000000,
  0x3b5daed76bb5daed7ffffffffffc0000,
  0x3bddeef77bbddeef7ffffffffffc01ff,
  0x3bfdfeff7fbfdfeffffffffffffffe00,
  0x3bfdfeff7fbfdfefffffffffffffffff,
  0x3c1e0f0783c1e0f00000000000000000,
  0x3c1e0f0783c1e0f00000000ffffffe00,
  0x3c1e0f0783c1e0f07ffffff000000000,
  0x3c1e0f0783c1e0f07ffffffffffffe00,
  0x3c9e4f2793c9e4f20000000000000000,
  0x3c9e4f2793c9e4f20000000007fc01ff,
  0x3c9e4f2793c9e4f20000000ffffffe00,
  0x3c9e4f2793c9e4f20000000fffffffff,
  0x3c9e4f2793c9e4f200001fffffffffff,
  0x3c9e4f2793c9e4f2003fe00fffffffff,
  0x3c9e4f2793c9e4f27fc0000fffffffff,
  0x3c9e4f2793c9e4f27fffe00fffffffff,
  0x3c9e4f2793c9e4f27ffffff007fc01ff,
  0x3c9e4f2793c9e4f27fffffffffffffff,
  0x3cbe5f2f97cbe5f28000000fffffffff,
  0x3cde6f379bcde6f30000000fffffffff,
  0x3d1e8f47a3d1e8f47fffe00ff8000000,
  0x3d1e8f47a3d1e8f47fffe00ffffffe00,
  0x3d1e8f47a3d1e8f47ffffffff8000000,
  0x3d1e8f47a3d1e8f47ffffffffffffe00,
  0x3d9ecf67b3d9ecf60000000fffffffff,
  0x3d9ecf67b3d9ecf67fffe00fffffffff,
  0x3d9ecf67b3d9ecf67fffffffffffffff,
  0x3dfeff7fbfdfeff780001fffffffffff,
  0x3dfeff7fbfdfeff7fffffffffffffe00,
  0x3dfeff7fbfdfeff7ffffffffffffffff,
  0x3e3f1f8fc7e3f1f8fffffff0000001ff,
  0x3e9f4fa7d3e9f4fa0000000fffffffff,
  0x3ebf5fafd7ebf5fa803fe00007fc01ff,
  0x3ebf5fafd7ebf5fa803fe00fffffffff,
  0x3ebf5fafd7ebf5fafffffff007fc01ff,
  0x3ebf5fafd7ebf5faffffffffffffffff,
  0x3edf6fb7dbedf6fb7fc0000fffffffff,
  0x3edf6fb7dbedf6fb7fffffffffffffff,
  0x3eff7fbfdfeff7fbffffe00fffffffff,
  0x3eff7fbfdfeff7fbfffffffffffc01ff,
  0x3f3f9fcfe7f3f9fcfffffffff80001ff,
  0x3f3f9fcfe7f3f9fcffffffffffffffff,
  0x3f5fafd7ebf5fafd7ffffffffffffe00,
  0x3f7fbfdfeff7fbfdfffffffffffc01ff,
  0x3fbfdfeff7fbfdfeffffe00fffffffff,
  0x3fbfdfeff7fbfdfefffffffffffc01ff,
  0x3fdfeff7fbfdfeff7fffe00fffffffff,
  0x3fffffffffffffff803fffffffffffff,
  0x3fffffffffffffffffc01fffffffffff,
  0x3ffffffffffffffffffffff007ffffff,
  0x3ffffffffffffffffffffffff803ffff
]

def HT : Nat → Nat
  | 5 => 0xfe160e57fb0a0f3bfaf71275f1566c62eea17938e7de987de5cc402ae4553b95dea69943db8cd7faca89e45bc4f1592cbfdb373abc606425bac648cfb4349e6dabdad4dfa3e4dd60a26822cfa18c72eea0c3bece9edec5e79e284a299992e9c1916a541090a56bed834220907ca681ae73ccc8ab72be37716bf3c0f76109dc575f4d57d25ef8e8505935bd91585c5ec94e2d74a53cc4217536487e403135086b2ea8312e2ea197f727e5272c23fdb42d236330e121034dad100030c70ec87cf90391d15600ea4274
  | 6 => 0xffad227fff93c8ecff2809adfee19782fe8ca101fe479801fe218de4fdd2466dfd70655efd648837fb729645fa791e9dfa6b6f0bf9a0a09cf941b34ff7df718bf7cc9cfff76aa35cf715c1b2f6e21223f68003b0f62b9665f60e0efef5aed5eaf5a2d8f6f583eb7bf55cbf94f4c59108f4af6107f4abe3a8f4910781f43ad328f225b767f1de2556f16ada2df11a4c99f06c1719f0569c5bf03824b8ef216efaef135c70ef0f7a30eee70fbeee34e79aedf5e123ecd4555aeccc5ca3ec27ae4cec21921febae46f6eb23bbe5eb187c6beb0c7f77eaf04c98eaa9aedde9a98146e9a2c928e8d905dfe8d6a245e8b0ea7de8034acbe7b1969ce6fc6cfde6f705efe659d90ee62872c3e5c7cca6e583fb3de4bda5fde3c2e3ede3a9a3b3e3694822e307b9bee2b109d9e25cfb1fe19b9339e17dc336e13732ace12c7b34e1014f95e0d007d8e0b8b463e02df81bdfb7c14bdfa7fca4dedfc5cbdec17878dea1385ade78d7e2de035d4eddee20feddad5fd5dc87455cdc58b27bdc5080e8db248a13da7a0066d9c3c675d9076bfcd83991c7d77e2fbad75087f2d6638ff0d6606a6dd65c5c3bd642c3acd5f8ecedd5f41250d5ec7827d598a703d50eabc7d4e7663ed4d800d4d4a9cdead4653d2ed391e5b4d2083772d19ef669d103b1cbd09c5320d076df49d061a4a7d03e6fc2cfed732ecfca44cdcf8e4d2dcf56f9a4ceed3ab3ceda26b2cecd9923cdc4b054cd63dc26cd43eed3cc3f068fcbd292b6cbb6d9cdcb8451bdcb7ae552cb245ef2caf8f375cae81c00ca30dff7c9823753c90acf2ac8d6d1f8c8b2897ac873b209c845b6ebc8277a19c7f11d37c6bc41f5c69c33b3c651cfc4c61e66e9c5f07ab7c5a40397c558a476c555d3c7c538f621c4dc581ec4d0ac1dc495e30ac4659ea7c44f1a13c3eca97ec36b754fc31a3ec1c2d0429ac2a29f9ac2981dd5c2779544c1c191c2c1b07e0bc1a56340c0d5a49cc070ad1bc0634c96bff144b7bfde47f1bf6fe557bf18b12ebe25454ebd9bda9dbbbb7564bb957074bb1b69f8bb161dfdbac218faba0b97bab9d01922b95ccdf9b87c144eb7b09871b70f09c1b6afd0adb6aca87cb6893aa3b60bc81cb5789a96b4f959a7b4d98bd8b4002644b350955cb26bd4f0b19a6ceeafb23b80af5888a6aeedff6aae90c72fadd62643adc2f0ddad1a3ef2acaf41b9ac9a4971ac3d412dac19772eac07b319abfbf677abe001e7abd3f4aeab72ceffaab375a6aa80a150aa40a270a925b55fa913e5aaa90691ffa8786a75a869d4e8a801ea1ba7ee5e2aa7dc6960a7d794d7a7c16a3da7b68bc6a7043d5da6c2f16fa656499da54b5aeaa4c542b2a460bb3ea4535815a411e899a3fece4fa3f0ab15a3db3d77a3629031a3312798a231502ea20b7e70a177a174a1506125a146b082a13826f6a0ff6a2da00242279f2eeaad9efa43249de0ace49d74c4a39cfdcdc49ca16d299b3d9b0e9acfc7869aab62e19a8d57239a4f15d59a36619d9a0391ac99180911989ace19985d47cb97e9ae279797d4e99769b0d6972489c096a5e42494ed6ab994c76db193de7819936ea63b9310352d92df8c2f9267e1f191db41b291b4cc03918a5b419174096c9167f689912eef4590e7796090c8c5c490b4a50a909fe8fb9057f467900de88a900c744c9003d69a8f102f078f0b56028eecdc918ec8d7f18e9573e28e7050858e4da2d38d7a4b598d5c2e898d4fcf078d49d3838c7154f18c44e1658be5d3158be4746c8a94ea988a76fd80891a73c8877bbcb58763571d87285b49871f61ac86c69b9486b3cc0f869cca3086785023867263f686599f398627e13585a4f8a98594b1a28526685c84f0e61683d3d1e983c0eb32839510d583882020838158b88349145f83350485831ddd668173d19280f738d880be0c677ffb1fa07fbd73197f921d197f418ee97f1d07027dc546c87dbbfcd07d9ac39a7d0346e87cc76c207ca66cf57c440b7c7b7cc7137b6378b57ac676737a82eb8c7a3830317a19ee0979864329796cdce3791bd3e978fd370078c6f15b788a98ba784452a277fbbeb177ecf81f77cf36b07732d77f7715f6f776d45af376705f9a7607149675ad13db753f59bc7459a37474199b7873e6584b737c123d7334b9877302996572baef617215215871dcd7d971da2e6071b3a90a71b0da627188feb67040f13c6e90818b6e26f9526db70e766d5c5f036cf237056cdda6d16c7d40256bc812476b1b04256a4ad0b36a47acab6a30268569f18d7c696d8ea56920c3ce68f0c5b868e4c8c468d3ee546826a7f166fafead665a7ac865aaf44a651663ae651315a96505f1b2649feb86643fbe2f6432225b64215b0062c5fc09623f80d761f2a48f614aceae610c710260cb6578603b368d603919885fcbd17e5fafcd665f73b9de5ee683305e9e1b575e7a1f3d5dffd4955de29fdf5dc1c2025daa2fc25cc2bd9d5bb693a55b83b8975b4321765aed50835adf9b275a6ffdfd5a302af359395d6c582584835822c8a65807129e57ef552956724ae85649a98c563113cb553e4b0b55170abc54e675b254892f4753d6683853cd0da9529aef875268f14c522a809852215f3b5207c34251b4ee2351ae1412510ee34d50abe978504efaf4501bfeae4fdad9ac4fc5e7174ea5bfdb4e9cb5ed4e8024264e691f504e1317a14de88cf64d95847a4ce873544c589bd44b5250164a80c4f84a7ea36a4a17a29348d8e31348a4aec14829560c47c79657479d3c6c475d987646b8817f46a4c5794662d29646291db9461ade304538cce044ae22f743f804de43e02c1d43bc87ad438820ca41bce00841aaeb3e4124c60f411e6b9c4106a02240ab20734016f8b13f7c39a93f46a5743dc4121e3dbe8ed73da767b83d932d5e3d7ebbc03d5954a63d0a584a3c8dda623b8cdfec3b6b7ca93b006f333abf247d3a40c0c239a3eedf396056b738d78765387d61ff3877942f382f5f4b37aa0a85373b987b36c518213684984335e1176535c4a23635a270a635440eab33b29ce9339d0bad3390243b3323e94432b1d525329d2c8632510bba322a03ef31eac2b6310a3df730ddca6b3030ad132d30aa5e2cc92c922cc3e0972c6d7ba22bf611b62be190c82bc268482ace8fc32a80983a2a77a6b42a3cb3bc2a3547cb2a09df66292c74db291a0bdd28a4957e2874c5cb28390b6027421612273542d72718fb7c26b0e86b26372a9c25f111d3254a2f5524f9fba323b37727231674a4230aff7422a1a61f21fdbb0f21c6ee9b21c0e3a620f397212060a53920347e9c1fea62881fdc0c041fc646d71fc085eb1f332c101eed2e711ead92751dfb66591dd14a1a1da2b1e11d9f0de91d50158e1c75d71a1c681fb61c4163d91ac1a8441a6c155519fcae4919a3f3eb18895ee7187dbb481817183e1728127e16c15e02167317661544527c151e110f1463b06613e9966213e760b413b3c45212af0ed512ad2cc712753856125ff61d10f1f0b410a2e4ea1025ffec101e993a0ff826b80e9494180e706dbd0e5ff28a0d93cc540d58961c0d54716c0d060c400ce74c5f0c711ffe0c6fe3720c2962df0c236c650b8a886c0b43d27c0a82cb300a707b020a6c2fe00a3a66b009e7f7a109dbed4109471864093c00d9092f4a2d0926802608dd1c0f08d528f708bfa51c083cfc9707f971af07e150720769a51d071bd8f306ca245205a15a7e059788f904bcbb9f02c72d4001ac1b36018e77b0016b5e72010d47e101008bcc00a46882009806f8
  | 7 => 0xffddc016ffd4033bffd2bb5dffc7410fffbfb956ffad227fffa8e1e3ff8799b5ff74b844ff6a6f92ff640649ff5b5e9bff438e51ff2874d8ff27f607ff2049a8ff17a8fbfef3206afee10276fed87374fec7a912fec22846feb57940fea160cafe849d52fe8313a6fe795512fe5a95a2fe5134a5fe4edd1dfe4689edfe462b01fe2d094ffe070b76fdebc924fdcf28d5fdb3e8e8fdaa6766fda69bfdfd862ea6fd7ddd2bfd4f0912fd46986dfd409dbffd1c8fa8fd021c8ffcfbd15bfcf8919efcc00546fca3f898fc955216fc88b176fc80ce54fc66e074fc5d033ffc3ae4d0fc0da761fbe41200fbdda413fbdbed08fba34910fb9d9621fb93fdacfb8607bafb6a58eafb65dc6dfb26b3f1fadf0135fad0e8ebfac0197efaaf7ac5fa89aa6bfa56de4afa46d54bfa318fb9fa28aaaafa1ffcb5f9f368dcf9ee5b0af9d1c9ecf9c39350f9bb5fb0f9a00560f992e3aff97d9ff3f979aa77f972f8f2f9696b93f94af4daf93efa94f93a2cdef8fb35b7f8cc6e12f8c3ac64f8c37a2bf8aedff2f8a58267f89fa178f88aac40f84676eaf8169104f7f4fe94f7efb38ef7d8da7ff7d515bef7d38f33f7951ce2f7919307f78729dbf78727caf755ffe8f754d6e7f730b796f7298e3df7281445f704d0bef6e2369bf6e1d219f6c4ebaef6b4a39af6a3422ff6965a59f67d7ddbf663a63cf66392c0f661fd2af648d015f646912ff637bdfdf633b122f61cc264f614f263f60d27cdf5ec73f7f5eac283f5e22acaf5e14c20f5bb708af5aed5eaf5adf36ef58c0f30f570147ef56e893ef556ce08f54f6967f531321cf50e366bf507e751f4d99235f4baa0a4f474b271f456da9ef44d5bbdf44753a5f444c8ecf43e212ef4264e1df425481bf424c712f3f7c93af3e98ec5f3e31b9df3e2cd44f3e150a9f3dcc145f3d74db5f3d0bd27f3befc22f3b2f5b8f36f6480f33ef590f32471c0f323cfb8f31f6d87f31d8f69f2f82d98f2e29157f2df4ed1f2daa132f2cc800cf2cb2b66f2c60b26f2ae32b9f2aa4440f2907b62f28efb74f282846bf25db89df24608e1f24090c5f23234f7f2290686f22519d5f21fe6a7f203a94af1fb20d9f1f97766f1e31c09f1dadb3ff1d269aaf1c536f9f1a84d43f1910b3bf18c5223f185a11cf1856a89f16c1c82f16ada2df14e84f3f13f73cbf127c95ff11730b5f0f47480f0ef115af0eafc70f0d76d2af0bd962df0ac8a1ff0a4279ff094b70ef08f7409f07d8feff07816c3f04d2a79f041e1d4f00dce5af00d7fcdf00415b0efcfe888efabdbb2ef99bbbbef8365c9ef7aa772ef79d2ffef5f509def4f6875ef39de50ef0f13c1ef05a3e8eef9df89eea3d35fee9e33a0ee8eb799ee8eb495ee8bf923ee809807edff3011edaf520fed8b1146ed80e601ed7d9781ecfcabebecf85bb5ecf0f014ece5988bec6cf711ec2549c7ec0989cdebf78304ebe9fe99ebe3ff11ebd8675aebc45ac5ebae46f6eb85b2b4eb825765eb5a9d7eeb53496beb3f2653eb2fb25deb2d2173eb2347aceb1e0a35eb187c6beafe43aaeaf59afceaebb952eac213fdeabfba80eaa3eea8ea83069eea68a9bfea460bcdea3dac34ea25ce29ea241952ea06b788e9de8deee9d43a21e9c4a3d7e9bc4043e99f3fbfe99ac3aee9903292e98921c9e96d8b43e96b42c5e95d7658e95276afe944d5d9e93d0079e91e5936e8f4932be8e99a75e8d705e9e8d1bb1be8a7a51ae89a343de8713607e84a7c38e8038268e7e94f19e7e789b3e7d23bb0e78c2cf0e7770533e76cac9be74e5667e728dce6e718e166e6df8771e6dad31de6d4e17ce68787c3e65d7ba1e60f8af1e606600ee5ff33c0e5cd112de5aae274e5a772eee552c6f8e539d7d7e5389cace527593be5198b9de4e9ecc6e4abe142e4aa14dae4a99862e4974d87e4802476e45e8d0ee45d8c99e44cfbcde43166c3e42dd5ebe42d214ce41d4258e4187d4ce40eac61e3fb8508e3f7bd90e3c6c3b6e3c3f60de3b74b40e3962609e37d5f40e3782a8be36a38a8e3620af6e35d0138e32ef9f9e329e9efe2bbaed0e2a4218de29d9d9ae297698ae28f008fe27a49bce278f0b9e27266d4e254a18fe245f417e22b744ee20414b8e1d14d1fe1c5b214e17fdcfce16cd623e1614ec5e1555a72e153a51ae1260a0ce1200848e11e8e50e1187dcbe10a2b54e0f82dabe0d007d8e0cb835be0ac046ee0a62e06e08cee2de088e833e081b94ce05f3ea8e043014be02335fce0144866e0048efadff6d5a0dfe906eedfc967f3dfbf8533dfbbb1f8dfb306b3df85e6f2df4fd081df42f666df15af74df111933df10f6bbdf081181defdcab0def169c0deee2a1bdee1c47ddec3d0abdeb4b1cfdeaa12a8de7c7907de6d090ede6b229ade461462de3ec678de3c5e1cde2b2d71de09f22bde035d4eddf2e54edded638cddd930ffddc1c28edd80e891dd7cc236dd7a27b6dd33c12fdd1a49c3dd0e6a53dce8d4eddce2036fdcbdb685dcbda171dcb84607dca9bf1edc9b00a3dc82071fdc6c16f8dc5bcf2adc580866dc4ff2bddc4f3a7ddc4c1384dc37d0e4dc252a75dbf561afdb99ed7bdb94e5f8db86c3d7db4b5067db3c8585db384b8bdb2bae2cdadec09bdacecedddac374fddab915fada7a0066da7669dcda55dfd7da17bf5bda0feccbda098200d9effdd7d9ee5266d9ec9447d9c6fe1ed9c1cec8d9c1c4e1d9ad8f7bd9916812d96fbb00d91ae31cd90c2408d90b783dd90b6caad906a156d8ff6723d8fa8514d8e95ae2d8e77edad8be4a90d8ba3cb1d8b986f6d8a439f4d89b8896d8939070d882e20dd865f562d85391c0d83acae6d837d686d7fc4379d7f3fbeed7ed43c6d7d2c8b2d7c12798d797fc76d781344dd76f45d6d7647f0cd74d36dad742a6cad740e50dd739e41ad6e31b23d6be530ad6aa9b59d679df60d6686d67d66319a9d6551b4ed64b0145d642c3acd61e548cd5f49d25d5f1b16cd5edb146d5e1b1b3d5d820f9d5d007d9d5c811bdd5c5000fd5bad4d0d5b3c62cd58ade65d579c60cd54cf054d51b2530d51a28bbd5006d02d4fee8f4d4ac5335d4a9b931d49b5b50d47aa00dd440ada3d43ef389d4346ea2d434263fd42d772cd4064313d3faa3c9d3f3c390d3e6bf5cd3e63c1ad3a84d0bd3a4fbefd39bba80d3863592d342d780d3354d05d3274c4fd2e3c0dbd2de7b8ed2d9d8d1d2c85bdbd2a0a588d29407ccd2551da1d2454b4fd23a2e0cd2293dc1d2207003d21d7863d2106961d20b2414d209e04dd1fea934d1f4179bd1edb07bd1cf4455d1b3dc4cd18894ded1458233d08a875ad07872a5d061a4a7d05f8f42d0525fb9d04a481dd01e8c03cff96fa3cfdb8680cfa9359dcfa8bee7cf99f326cf8afcb7cf822ab5cf7b5c08cf719312cf6df23acf56f9a4cef5dcb8ceed1652cedfc1fdced96181ced52b12ced367f0ceccebf3cec8822bcec7a0a0cebe29e5cebc9194ceaed33bceaaba24ce7cdf2fce6ba582ce599ef9ce53c31ccdf52ab1cdcf8a8bcdbb7d6ccdabd67acd96cb53cd920d4acd767c31cd6eff4dcd60b2b3cd60106dcd4aef78cd458486cd3a1576cd372e02cd2d8225cd20ffa9cd0eff5acd0ab84acd04d840cd033108cceadc74cce7c15dccdc37c1ccd68327ccd56c82cccdd3e4ccb5c60cccb062feccacad07ccaa8b8ecc9d49dacc9d1690cc86951dcc7e1e79cc5cefb0cc4b00e1cc454bdccc3c6e22cc2fe88acc02a71dcbffc3facbe9a487cbcd3d8fcb7de628cb77cb5bcb728df3cb6c75b1cb5f871ecb3846cfcb2fdd23cb1db683caf63272cadf237ecaaa8eaecaaa6b5aca9d6c13ca9c9071ca9b7231ca82d2d3ca5633bcca257fd1ca1febb4ca068e88c9e48baec9dc422cc9ca0d3dc9aea850c9ab88e1c9a6132dc980a29ec978a9f8c9656f31c939ad52c930f625c8fea1a4c8fca1c8c8f65b86c8f2ab19c8d0959ec8d02c10c8c9d24ac8ba8a0ac8b16063c89f3cfdc8531406c85231e3c82b4a2ac8241cf3c80c529cc7ff10bec7e67b02c7e333a6c7df2587c7c7ef32c7c5c42ec79e7539c7961644c7949c4cc793734bc7927845c78af781c77386cec758975cc757469cc74584eec7445c38c72f3aedc72b802dc718d44bc7120b55c70a6f4dc701ad2cc6fe2a82c6f8a696c6eec1a7c6e1a3f6c6703707c65ae542c645a724c61e66e9c61237ffc5ec8fd2c5ec3307c5d25bfbc5c6aad1c5bcf1c4c5ac34fec58b6003c57e3534c56b27dcc558a476c51846e1c5145376c512a8ebc5082a49c4f93d08c4e9f35ac4e716e0c4de1038c4b9ef08c4b451ebc4b294e0c4989122c489fa3ac4818a52c477d512c4045810c3f70136c3e6978ec3b9a6f0c39057bfc38b37f4c358e711c34b19bbc3429273c33e40f5c2fed7b9c2fde27fc2dfd1dcc29508c3c2938143c27a7ebfc2669aacc265d75ac25d9848c254370ac250493dc1d0d408c1c7c19dc1a2a45ec175c252c142fab9c13b8a30c1361ac1c12c04acc0e84616c0d73a90c0cb4c77c0c62952c0beb0cec0bc82bec08cda26c0875d04c07fe1f0c0629d34c05769c6c055a4c8c03799fac024a22dc021dc8ac01411dbbff7f4fdbff2bca9bfe1c2f8bfdb89a6bfc2022dbfbfda3dbfbb7a1abf971e4dbf7aa7fdbf3c2192bf33e627bf23da69bf011e8ebeef6eb7bea2cd40be555af4be3ca0d0bde75d8abde49c12bdc31ad8bdbebc86bd8997efbd84828abd7c433bbd545061bd4fcfafbd3d30bfbd2c9978bd06f8a1bcf63740bcf13b05bcea1225bca6ff81bc9ef843bc9e8f99bc827accbc7aa0b0bc6b53adbc30e2ccbc1d27a3bc057264bbfbeed5bbc44f18bbc360ecbb8bcbfdbb7213a7bb677cd3bb5dd7a8bb4f53c7bb3e4f92bb305152bb161dfdbaf0f79ebae7501dbacf5f0abac7d9b1baa00a87ba989f50ba7af68dba5d9721ba16bf64ba05a76db9ea998eb9ccb30db9cc4e74b99557bdb98484ddb9600000b95ccdf9b9593003b949f650b929741cb90b542bb8de980ab8ddbe0eb8dc5979b8b4f29db8b4dc75b8b0de72b8a4e861b89f4bbdb89347b6b864035fb8563906b841a774b8107d81b809653eb7fc82c9b7fbacacb7f11c95b7e2dbc7b7c8923eb7c42317b7c03f7eb7b9efbeb7af8943b7a81621b797551cb78937a0b788eab5b771e10eb7648d83b75652eeb71e23d5b71ccd6fb6f4fd7bb6e1ff06b69d04aab69cbbdfb695ab2db663c5bfb65f60d1b65e1316b64f8ea4b62906d7b611bc39b60f920cb57765aab55c6055b55bb61fb54022f8b5394ebcb52748e0b52573c6b519afa4b516313db501b0a7b4f7590db4b84355b4ab10a4b468e191b45d0bbdb42ee2e6b42b8b08b4277b59b418fd36b41536d1b4071b3ab3eefc68b3eddbe2b3d6c0afb3b81085b390e43bb37a90b9b3726c11b35e1ca2b3534f50b3337e8db31ba4eeb3012daab2ed1069b2ec7d38b2e3979bb2bb6cccb2b76f74b2993bf5b2793c6eb24a33f3b24101d6b23fe822b23b39eab1a77ddcb1972347b18cd455b15a4a31b1516ab6b13511c1b1253c60b110a06fb10676f3b0f2531cb0acfbe8b0a5f2adb093b78ab0938f0bb08dd036b066f767b0629da4b057660eb053f95eb0397f72b0392599b01efba2aff4ddf3afe49d0eafba7f75afa845d0af8192caaf7eb28daf79e165af75f4edaf69eeceaf65a496af3b28e8af2f66b9af08f612af002ad4aef5a6d4aedd4397aec6bf00aec2c3f5ae88892dae6869dfae67d16eae4419edae1f167fadfad21bade97ea1ade6ccffaddb259badca719cad959818ad6601aead5ca3cfad55979bad54c960ad4bbf05ad47b45bad453ebcad340988ad260cffad1459fcad0669a5ad02207bacf494e8aceab026acdbbeaaacc6d0f5acc65013acacc401ac9290f7ac8237c7ac7ad1c8ac745ce1ac707f95ac33122bac07531bac016dffabfbf677abd4c5ceabca5a7fabc14e45abbba82babad234faba75fecaba5173cab7b21e9ab68e6abab5c98a7ab470690ab467f58ab2ffd04ab189d61aafccabeaaf9b9f3aaf22d5daaeecb9daad1a11faac6b790aab2ab33aa9e5b33aa76e7b9aa6c3d88aa62e0a3aa5ca58aaa594047aa528646aa24ab77aa1b7423aa14b725a9b1604ea99d7d5da9986fa8a989fbe8a966a511a9599f43a94a090ea91b2cf2a9063460a8fc0a4ba8f863d1a8ecc8c0a8eabecea8e95a24a8e4a6c9a8dbe556a8db27d8a8da24faa863d2e9a85054f9a82bf98ea8197146a80daf03a80c49f8a7f8031da7ee5e2aa7e3b19fa7dc6960a7a31b5fa74095afa6fcef6ea6ccb390a6c6eaeba6b9752aa6a77df9a6694469a64a0946a64114eda63ad953a6318816a6070ea4a600f65fa5fd5e0ba5ea9b6ba5cbd999a5b3ce47a5aeac4ca57a12a5a579ff09a567042ca5624403a54dd013a547a351a5473770a518db3ca4f93bb1a4de05a2a4cdba5fa4c5c55fa4c1ec20a4b72ba2a4a325cda48ca33ca481113ba47fbc13a46f28d3a4681840a452a1e4a4460140a43928d4a4374d1ca434226da40471bea3fe5776a3f9d6d8a3f4cd17a3db25b3a3c68c21a3c5ddaba3b5e526a3afd303a3af61d3a36b38f8a35dac00a3559c52a3391cc2a337ecdaa3312798a32e5d53a328a5d8a3283218a2f334a7a2ea68a5a2e51caaa2d15c65a2c9313aa2b83dd2a2b332dca29d4611a29c83fda293ed00a28fa42fa28bde34a28ab499a27b20f2a25c5329a22e0f11a21a0fa5a1e3a45ba1b9e41ca1a31d77a19e902ca17b4026a16aea3ba16316ffa14698f3a14281a2a0fce1f3a0efcbd6a0da350ba0d89f72a0d3bcb6a0d26692a0cc451fa0b2e715a0a99d0ea0a69067a08b3925a08243e2a07a4ca8a05aa809a043a66ca0319ba6a02429169ff646659fd275909fccd3b19fb44fa39f7318909f71afb49f6431719f3d3d5d9f31bbf99f1daa8f9f00a5779eff6b169ee4ae619ec6a3109e9e3ecd9e83d8b29e7c7d669e6a983f9e3e692f9e2af3a49e0c184c9dfa06ae9dd7d8c19dcfaf9e9db1e9fb9d725d519d643cb79d5539969d4c02429d455f909d41a6289cf43f869cef5bab9ce4e3b39ce431e69ce2d4c19ce0c9ee9cb20f5d9c9f14d39c9f05d79c9ad6c19c93b2e69c7d4f349c7d2d959c6534d39c5e6e809c2efa269c10198e9be36a229bd8fdb89bd4a4d29bbccc039b8b17069b5c89fa9b56889d9b5525949b49a44b9b1eff2a9b1c43ee9af155589aef4d299ae33c1d9abcea779a522dc19a3ad4009a25cd569a00024899e7150799aa9ad599a5b8ad99a28519998925a099800f43996371e3995543ab99537222994f354b994edc829929b07d99211423991a8808990179bd98ff3a8498e7c06f98b63fba98b5f61e9891b06a98901a6998540f26984bd7d1983b62a2982fe85c98223db4981695fb980e0638980bd50197fd20c397e9844f97c3c1a297be58f097ba37fe97a7d45c977f85e59764146c973cc6e6972489c096f83d6f96e8dc4896e5fb4696def1e796c53fbe96c3639e968e26b6964cf0df964c0f48961c8ac1960bd0a19601abc596004d6495fc422595f00c2495e3bbc095de2a2395c1db1395b3663995b16add95b15efb95aab3f495a154199594bc719584cee8957d6bef956adefa9559cb9e950f176c94eea3d894e038449470e017946fb199946b7ac79469cfb89469139d9463dc87944b591a940a876493e0f64093c6725d93c5c26293b257ea9395028f9393aac4937578c093624f53935da38b9341b20b9317349a930d7c7292d25beb92ce2cc092c9fe1e92a52c2792898fa19272db44926e76ce92604c6a924b0ba59228f1ec9227466f921264a5920f63f292065e019205d06f92007a1491fca70391e733d291e457f991a7de81918a5b419186d39b9167f689915f84a6915482b8913a996b91384d22911bda37911bda1191137afe9104c5b690eea30d90d9e3b890d3450190cbf7cb90a422019091bafe906fa1e89064dc379032149e9030ff19901a260a9014319f900de88a9003d69a90022c918feecb9a8fdbd25b8fd8a5018fd50b748fccb5418fb944618fb7ed788fb360748fad9f3f8fa3cfb48f98be148f97e0e78f8b79ec8f4d8db18f2ed5178efcad3e8ef83d8a8ef52f6b8eba4c758ea2becf8e8a1ba08e831d478e7bc7678e67c6be8e3828c58e1d6dae8e0a5e778e042bcb8dd0a99d8dc7e3778dc37bed8dbe93a58dbc99ba8dafc5cd8d96c8d68d593b508d494e918d2434128d23de7f8d1af6088d1ac8ff8d117add8d07c1938d0686eb8cca397c8cbf7b528c6097aa8c54deed8c3382f58c2dd0118c2216808bf7cd378bdf99d08bde681c8bdbd06e8bd8e7c58bbaa5858bb0b00b8bab661d8ba1d0d98b9975978b5f8d198b5c59bc8b2556e58b1b740d8aa8d7fe8a9c33858a9b69118a62f96a8a62ba6e8a5c17e68a568e4b8a444bb68a31b7e48a00da6989d5214889a037c08988c06c896f3fff8955c687892e4bce892b9edc892513be890a70c588e57e4088d1f71688c6bef188b696e288abf440889f6ffc88946e0e8886de80886e07c488523df188511db8884f19e58833f94f8831a74c8819cf0e88149e2887ff3def87f3362287cdb1ef87ca555187bc739187bb67bb87b3c0c9878cbb5a877623d1876f7508872df96087285b49870659b686f5300086ed8a9586e6bae186da055f86958ede867f80c0866f7f138662c5be863185bd8600b01d85fa37cb85efc59385b6d05b859b1a538590b0b88546be59853c1b67851d1ac2850f6435850122b784ecc14c84c89b9a84c04e1084bf86a984afa1fd84a0103d848dfd2d84770312845883a8844ad5588422e2018419a5f184148dab83e4dd0483c96d6283c0471083bee0bb83944c3d83852c2e837c5b5a8372b3d183697fa18354176c832fd9e382fb0f9282f7f3c882f783e582e719b482ce2fe382c3150982be18f782abf5b5829f5c57829810dc8277661882699056823b6a9281fd8bce81f3c6ea81ebe0ee81dbf94681d3da1d81adfdf9819773bd817b366081457a4a813cc40f8121342681200336811d581981150c9e80df334280bed27780b5fd8980b1d873807ceb418079cece80669e70804aad89803bfc4b8026c36e8010491e8008519a7ff91bd97fdb9fa07fc5c5927fbe884d7fa908bd7f7c4b537f6854777f5b8c527f1a19ed7f0132197ed69fc27eb434a77e9b787d7e85482c7e6b87b97e6815767e66d8c87e5164fc7e43b1537dff37927dc546c87d9f8a5c7d74b1d17d61512c7d49fdb87d3ba0267d1d52ac7ced237e7ceb60657ce1b8007cd0bb557cc45d327ca7009a7c95bbfc7c8a30ae7c7439017c6e6cd77c6c6f0a7c69f86f7c5061627c40c5877c2207127c1ad2b27c1362327bee5cfa7be2d00b7b8c8e087b87e0697b8525687b82bc097b7d58ee7b64b1d47b60c4e27b4ff4707b3706cd7b2e56dd7b15cf377b102fee7b01566d7aea03e57ae1bf267aaff21d7aad05587aa73f737a60fac37a5974377a36e09e7a086f7b7a02a71a79e74d5a79c1a42979b5ed6079b4790479aa2d0379a085757999197b79983ba77995a2e37994587e796b92267959c95679590f1979580afc794f9bd17942a237793518017916d3b178fd370078fb8d0e78f013c278ef9aa778e7475878e5918b78dc5a5278d8616078c75f9378bed8fa78b6780d78b290be78b0d42b789181f6788ef15d788a32637883a3b77872834c78619464785bc3a1784ec1ec78498a75783c0bc8783844927837cad8781f1e98780902d877fca7ac77f3984177eb818077e78a5277e0467877d5d02e77b1894677afb3c3779fbdb977675e6a7764b109775201ce7711701376f34ce176e4454276a968de76a43c4976948408767717fb765dd0ba765a89e27636cd7d760187e875fa2f9d75c090f775be0dc17592d7c2758a7940757fca1d7574cb6775641415756367d67561d0b8755daf6d753c31567520c6e7750d991a750386da74f92b4374d1adea74d0348274cf973d74c3dc7d749ee651749e7d8b749313af74913e487481a785747b8b7c7467803c745711557436a7a77425d3c97418adb7740b135373f23ef973e6584b73dce1b873bcd4447396a1e7739331ad736cf9b773638ba773329ac1732a2f5972eb91c172bfc88372a75e3e72809191725163eb7233de3571d039a971b8620671b0da62717a4921715b902d711e400a711a921570eecbe9708cab23708838b37056b20e70547afa70319b8770166d326fee1e476fbb5bb16fb88fb76f8ee5f96f87820f6f835bec6f5b8c3c6f3ebdd16f3a72046f326d7d6f14f58f6f01c8016ee3f4506ed0bc056ecf00686ec8d0f36eb802ac6eacfda06eab68f66e9714016e8303e76e8156fa6e6697286e62567b6e39303f6e1f41196dfc4b226de91b276de4ab326dc6b1576dc3bc876db6538e6d9884de6d9434576d8a7ecb6d5c5f036d5373106d5130d36d4317ee6d410f6e6d3fcaa96d27d7826d24451a6d0b9e846cdf36f46cbbeb986cbb1b266c9bc1356c2d56fa6c2761c86c2600ec6c19eec06c06b6286c01069d6beaacf06bea85c06bea7a9d6bcf33cf6bcbe7926b80cf776b7787e06b58d8cc6b37edb46b1723236b07a8606ab25b116ab0db436a6746066a49f1dd6a1e25246a1d0f526a17a0fa6a004c2a69f18d7c69e531fd69e424c169ded30f697c4400696b4fd3695f5231692fbdf3692d014e68f0c5b868ec5d5968815f5e6870bd8168591ac468182af86807a2d267f4b85867e9557f67c299eb67a58e56679cf6e46797a9bd67861dd5677d6ab7677cb4fc6764ca14675791036720ef71671e455d6715fe0566fa486766ec05af66a505056692cb0b668c2a28666a9db966633ec66650db2466357d726631b913662a78136614a38b660f545b66080b776601c88565d358d565d1d42365a5c3d165933f436591993e658166e0657c5ac765750c786551f0df6551a0a7653c8d2565372d7e65240599651f9f43651315a96505f6066505f1b264f5dc3264f5c7da64eeedf064e1829264de36ba64cde20764c783b564c38b4f64be41c464bcebc764b5465c64a93da364a1b4fe6476760a63b81e346373a69c636f0faa636f06f6636a620b633e2135631de0ea631ca7d6630eef3e63016b5362edf0f362c9242262c5fc0962b7c96762b2ad5c62b179756297e169624793b6624450c36229550c6217eff561f2a48f61f0c69961d94c796198cc9b617abd49616aad1e6161f529614e87926141ab816132966960da9e3360c1d73a605fe8466059cab75ff35d3c5fcabd5e5fbb11b05fa602065f97e9085f825d2e5f748c9f5f73b9de5f59e1e15f4315865f2bee675f22bd485f1e108d5f016df25f0058905ef8b3255ef456685edb889a5edab4165ed2aa8c5ec7bee65eb69c775e75bc095e65377a5e550ed35e5252ba5e3f2db65e381d9c5e2708de5e22473a5e067fdb5def7f415ddd8a775da9c9105d90017f5d877e0f5d84f9455d686aca5d5db09c5d59926c5d4120025d0e58695d07faf75cd82a765cd625ba5c937b515c901b6a5c7ff5f35c73bfea5c322d535c12135b5bfee5fc5be42daf5bcfb91b5bcde6505bbfd89d5bb6cd235ba1f6605b4f7b595b1e12e05b110c205b1067125af98e035af32a205af105d85ad7d3495acd8cd25acb1d485ac5d5235ac37a595aa81b025aa156d25a8dac1a5a731a895a71d0935a5ec6995a546ce55a4324035a0e8d1a59e9e2f959e4200559db357759cea79d59c3fe3a59b1450259a25184597461ec596b5c0459698399595f45d759419a53590beee359028b4358f6b0d858d4e3ca58cb2c0258b7b1d858a7b4be588895b758790cb0586ffca2586a75a75858ef17584ed1a258389769582e70025823595e581c53dd58105f515807129e57c459c257afb47657935a16575a6d1a5726c29f571e518d56e4dc7d56d5d0cd569d2ae556901804566d11775664ce28565544cf5651ee2a563f4c815638b86d56308c8c5623c06f561cfd2356027953560168dc55c3713855bde48b55b1efad558c3a4c55857dfc55839ca9557643b35571bf785563c01d55622a36555d03bd554ef9f25548f94955348f8f552b5db055180f1854e675b254dca52454d48a3354b8e2d254adaf7854ad0331549e6d3a5497e48f548c3a9c546f12ce54617e6554575830544e3bd9544c3bf9542fd80f542c18ff542904d75424996653e46edb53de1e1153da64a253d6868053a96a0f538d7e4e53653723536405665347d4435342e985532e81de532b320c5306bb7752f003e252ea921952e7422452e7296852dd67ce52ca42ab52bdcf7a52ab16eb529ef57d5293704e526ca49a5259c00e5257da92522fbba652238fb2521bba99521029525205c0795204c04751de27c251cbc42051ae14125194a935517ace035164bcbf515e9f9a514968565148631f51411334511e607a5104337250f0d17650e4de1350dd37a450b2167a50ab8d4a505aea1d50505a21502144105012b1145001cfb15000a2aa4ff788b54fd26e574f65cec94f3e64b44f3307304f0b10f54f0824794ece87514eb453064e7e5aa64e505c9d4e4a49544e472a734e34b16c4e115b3f4dff4f984de39c694dd66a6f4dbed16a4db5da774da4198c4d9956784d80c5644d520bda4d4f401b4d2413604d1b03c64cffced64cf526934ce861264cd229824cb225de4cb1aace4c7fd4fb4c7324bd4c72a2954c6f5b804c6baa334c5d6f144c0e6a004c0b7cc34bfd36134ba210764b7281934b343e954b1f1b514b1ae86d4b11d6b84b09e3494b0957f74afcb8574af92c3a4af477ea4ad8f1824ad19ee64acd983f4abf8bff4aa2c36b4a9749c64a82d4db4a607fab4a52055a4a4215054a34db294a2e2c304a13560949fb2d0949ea28c849e8c96749e59eb849e08c5749c94c0b49a5d7fb4987da12497368bd49676171496436c2495014a8492963e448cf1bc148c74ccb48c3829b48ab39ed48a20f9c48a1510b488db61d486b2408484db3cb483a05b5480135b047d4a82b47d0206c47ceb82247cac85e47b6333947a56054478cf2704785e9e8478030d04777c0e847500c77474c0b8347362f17471fbafb4707141046e3f34c46cea48146c3b7a446c1793d46b6918646ac6fd24695c557469599074690911a4684c1a8465838344633bc9646293cf3461a9f3e460117bf45e5abfc45cfefdd45cec6dc45c8a6a545a8905945a73acf45a5280a45a29baa4588ec3345792e6f456a492b455c8387454bd01b4549a3c74535b5274530958f44f1532944e080d844ca84ac44c6abab44a3a0d844948f87448ffb3d44899ede447b44dd4477a3a04475fcf3446f32f2446bf0774462da2c4459fbad445565534439314f442afa8d4427e3634424de6044229dba43cab29b43b9e64743b1933743adf38a438959e943653f5643594b14434316e5433490994321d5f6431ad8c34315803d430b962b42c1825442bd83a142af35da4235c775421ed6d742130137420a5d1c4203bcd541f7552441ee2ada41ed436541ec104641e5591741ddeb6d41c8af4941ad06e041a67a59419a41af418af14941871a1c4147cc0741455f3a411cd206411487fd410aaaa54104616b40ab207340694f3a406800eb403131d6401abd90400399a73ffee0f33fe86a663fda2aba3f70a6413efdcaba3efa52303ee634193eb4373c3ea6f3cf3e6e67563e5fa6513e57fd7a3e53c2083e524db53e4c61b03e21ce233e012a023dec5b283de97f063dc96b2e3d98238a3d945f893d8ea70c3d6f679a3d64aab03d3f50a03d3d1ac23d3c64b03d2eca163d2e09243d21645e3d1dd3583d0ddf523cefd1313ce6e6443ccc59f93cc34c1b3cbf20053cb2ee2a3cab54643c8dda623c76f6463c4bfdd63c3fa3013c25e9983c18c5a13c1222053c1028673c0a85853be8c29a3bc650c03bc033323bbe3b0b3badde2c3b8b52e53b8b23403b5867d03b5672f03b4a114c3b3a99ab3b28ae933ae879213ad9e32a3ac007783abf247d3ab57bf73aaa0d653a99366a3a964f613a9454bb3a8f5cf43a847c4b3a75ded83a7206653a5fb9003a5ac4193a5a06e43a5782953a40c0c23a0de5963a0d679d3a09ad5e39ff90e139e5ea4739df50bf39bf0bd439ad4f84399eaeeb3996480c398c443b397a5db3395f9ced3957eccd3953ae1a394d6a943948cba13941213c393dbef9392c39673927afec392394d6390dec1439089a9f38fda5bc38d11e8e38c41c10388b7c77388256ed3860ab6338508e633835d51e382f8552382e0e8c380516c737ce6e6537c73213379b53913795a362378c417437859da5374eff983742d3473732be9536eaa61b36d311c036ace3d4369ebe933694d97a36932a913692c589368f8ad5367cfb05367b0e90366d96b1366c6db0366c44443667ac583662b57b36545338364bd1123640c7873638bdb835e1176535dbdcc535d8a77835b3a8dc35a9152c35a656953592390b35726649356ba6a935597766355683c6353240e6352a6102351e6c2d34f5e27c34e0516234be792034b61354349a2ed134984f2f348a919d3480d63134645a68345ee96c343cd620341f2853341b17b033ff731c33fbf87333f1506733e1f3ab33d2376d337163ee32f3318b32da959a32d55eab32bdc6d6329e53b9328477fc327b8fe23271b88432709c2a323e41af3223a757321c94ab320b7a163202fb5131eb601e31a94982319f723f318bc82a31791ca2316f95e6314298be31407d393127e18c3118d1673116094f3110c5c930ff71de30ccf05830b2c0ce30b19d6330abbd51307b3bb330399de3302c1a64302b6847301535952fe479392fb491ab2fb161512f9468422f8f73252f89917d2f8478a82f5a94342f5227c52f4f6b072f4a02a62f3a2b022f328e192f248ecf2ec669ee2ebd25b62ea1acdc2e7089d72e6c859d2e40efd02e3e38f42e3126852e29c7322dedbe2f2dea99a02dc61a732dc399f42dbeba742dbe4df92dbce65b2dadf6f12dab444c2d848f622d6ebd482d671fd32d64a09e2d5388542d4f65d72d4a3e0e2d44b27d2d3509ac2d32c0c52d0c1be52cc3e0972cbcd5aa2cae70702c9a86ef2c97557b2c95bc022c7d21a42c5450c12c28ca142c162ad22bd5714f2bcf05152bc8fd252ba768de2ba402b12b7944f82b7789fe2b765d5a2b40eb7c2adcf4dd2ad347942ab3d0dc2ab172e32aa3cbc12a80983a2a7a5a672a717ade2a3cb3bc2a287f5d29ff681929f1ae7429f003e929e8a7e829b6757a29afbeab29a717672999c8e32990afae298b8e392934f34829337d5e2923aecc290617ff290351d228e5047f28d1339f28ca9765289f5f62287e7bf2287be0572874c5cb28695567283d6e062838fa652811ad05280085c427ed007227d3eeef27d2416227bccca327ad5d60279ae51527976827278e70d42788055a2785b1bc2772e34a2749817a273400ce272fcbb0271aa1d926fee9e826f47c4e26e977e626d4539826cf030726bc808726b56eef2657bdfa26563380265571e426548abe26442a082633e78e2624f6612606a27225f71e3a25edf32325ea391525e4635b25b2161525ac262425a543a8259f74a52599ddbc25841829257f31e92557de31254a2f55254815f8253d70f62535fae62531071f252b6aa525101ee5250c37542502a1fa24c43ab524c1574424829a77247759dc246ab5632469eaef245d4413242224a32420885b23e68f9123d5a7582374e2f8234955422345c1f1232df58e22fba4ab22f328e122ce471f22cde2b722cafac322b9f014229c3a5a22924073227ed7b9226f965a226dfbb522509e6722342c38222e0b3c2228ef312224dcfe221f15bb221447e82201313c21f5a1b521e1f70521c6ee9b218e05d1217aed5c214592a2213dcb422121633b211eb47a2118e28720f3972120d592ab20d1c55120c74ae82095389e208fdb8a2086cb0a206410bc2062e7bb20616e68204e0bc1203b138c202cc0e5200ac5a92004eca520005bee1fe006721fbc6fa11fb5f2e21f7c972c1f6f8e141f5f0ac61f47c0c21f381faa1f10fc1c1eec6d1d1ede15fd1edcd84f1ec69c5f1ec658cc1ebc04421eb9c57b1eb0ca9e1ea9a9721ea32b3a1ea256ab1e9f00611e84ee681e81d8c91e6a49581e5a8d2f1e41fba81e1f59b01e1957361e1547c01e10bbb71e0260841dcf09011dceff311dcdb1ab1dc8e97e1dc4a6641dc3dd5f1dc093b21dba27bc1d962a7e1d9476141d72d8471d261c0b1d1c8c9b1d1703e11d09e7251cd5ad3c1c7b4d291c7064471c547fbb1c3e07931c1dc2eb1c1c69561bddf7051bd3d2091bcd56ef1bbc15a61bbabd751bac76501b9f90481b6e4dc91b31c9aa1b1faf071b1d8b021b1436c01b13a73a1b1230791b056a451af357591ada68641a541c4e1a43065f1a2890ad1a200a671a1b78691a076f6e1a05032519fc2b6819eea06519da416519bbd8cc19a8af81198e0533198bcb2419693f8719394bbc1933d4d21918cc6518c71d20189bab6618423b7018227fe0180f30e1180a7d7f1806c0f91805e0db17c8647917bd4fd2179295b217783b4a17432bae17404744173fad98170a243116fda21816f149af16c853ab16b9e2431689e15a165e47f7162f0440162c5873162acc4b15f8c58515f1276615a89c15159639bc1585f38d156e0409156cbe6c155d803315527e451547eaf9153333b214f4b3c314f0b6ae14ebdc6014c8316014be4e4e14b6fd8514b1465914aa8cdb149898111474d9a3146a3ed7145b0b67141fd1701412731b140993fc14054912140119ac13e048c813bc3c7613b7f2f113ab9acc13a9d8d413a79a2913a65a2213a0ae511396e75d13946b11139166f51366bd851341d3291341a1621339d6631329f76913284b34130e0aeb12fe6c1b12f001b412d8a8a912cba48212b8480212b59db612a0190f129ed810129abfc212865535127efd921264872f125f9a5d125d733b12345247122f7470122958b61225e792120bb269120b00ff11f6229111ee08fd11d8de131178d1bf116ca78f1157761d1133186411111be410e23a5f10e1f62d10dff1f110b5d05710b5bff0109d11bb109c79e510951d86108395f6107d5753107b60671076000e10738e3c105fdf7d102f11a310262be10fee293a0fed98450fa2bffd0f9133190f66824f0f6278f80f2aeaf50f2406a70f1256020f069d5f0ef8d5030ebdd8100eab61780e8b94190e640f920e5fc0260e59297c0e55799b0e257d890e13bd260df32ca60dd31cd50dcee17e0dccd3300d9e51d90d6ca4d50d3b7b950d37df050d32cdaa0d2e6d950d2a979a0d1fa0a70cf97bb60ccedbe10ca3d8e60c7cb06e0c711ffe0c3d371c0c2f78620c2c4ddd0c2962df0c21fcde0bc7ee780bbf4ded0ba178a10b7720010b5bf4f20b58f6630b49e2690b4191630b3654890aee75a90ae9c42a0ae8a9c90ae28aac0ac726b40ac0b7a00abc24c60ab18b000a8c074a0a8875370a6f87f60a6e39e90a5d9a930a5b7b990a575a070a4185c60a3a66b00a3a59f20a1b07a309d0168409c8127309afb60709a0bb77098fe2530970335e093eb2a9093acaaa093737080935cdbb092bc4c00915414d08df155808c952a508b3758508ae805008891e09088593b2085786840851073a083cfc970803040507dc371507c899ca07c491b407bf66a407b4418507b1d02907ad6a95078ef083077ffbd0077150b1076ce6d80769a51d075130d0074f16bc0745539207380224071f0afa0718cdd5070c2437070b469a0707f98e06fcaf0f06fa73ab06e3534906de78af06d8f5b706cc2f8806be1f9006ae1d8f068a6d760673fd97067324a4064da87406247d4a060190730600b26e05cc1a7b05c9a5a305b8fc7b05b67ae70584a8e005625e730548429a0532123e0522f131051011ed04e5a50104d0e26f04c9f4c204bcbb9f04b28dfa04843c4e04786e8004716cf6044a965904472453043ebf74042ed02a041c1db3040f026004012dc503dbfc9603d1a06e03c79e3d03c6b4e003bd4ed203aa95220392ac9e038fa95c038222210372da7c036dab840364e4cd035cd50603468342033b5aa10330281c0312dc44030ea50f030370d902fe48f402fc06a602c72d400288e512028628e902751f21024197b50227ec8b0226b9ad0224087301d7c21501c02fbf01950c8d019477280190a7f601749eca01514b4b014f87ab0123161d00eb31dd00ba878d00a1245e009bf6c2009310d50042444a0017d24d00029a66
  | 8 => 0xfffe92fcfffb48c0fff35a28ffe9ea79ffe1ac80ffdbfa97ffd4033bffcb2ee3ffbc0a72ffb4f6adff867bbeff5d1987ff543fe8ff4d884bff441679ff42751dff41ab84ff3f9633ff3d9babff37645fff30fc33ff2f09f0ff29e103ff1da355ff100d88ff0cb785ff07f7e8fef6e685feeb5c9afed03cd3fecfdd2afecdbdaffeb6866efeb5249dfea7a400fea6ea52fe992274fe8bf188fe7be84cfe65525afe61cfc8fe557767fe50c3affe4edd1dfe34db71fe2fd105fe2d094ffe1db6b9fe07ac8ffe070b76fe01bf29fdf50ccdfde27b8afdd55bacfdcf5471fdccccd2fdc0f462fdb8c9f7fd9eb82ffd9148a0fd900760fd882677fd8825dcfd83cd23fd6e7cfefd6e4ba6fd67ddfafd512d89fd4e2f45fd409dbffd3e5635fd1089defcf492d1fcf11372fcea89c7fcdadb6bfcd67899fcd654b6fccaafb2fcb58192fcaa682bfc9ea76ffc899666fc81b336fc80ce54fc7a6471fc70d57efc6edf36fc637424fc605e94fc4b269dfc41bc22fc2e7833fbf81953fbc42e27fbb5df15fba4c4bafb71e6d5fb6a58eafb63de54fb5e7c75fb43a64efb3b2569fb3a6faefb2ee31afb00ff99fae7180dfae03f08facd5cb9fac19bbdfa8580a7fa79ac47fa6d83fbfa4f0686fa3acf15fa24926df9f81cb5f9ee5b0af9e1387ff9c57854f9c22780f9c08eddf9c0679bf9b77cb2f99cfcaaf98dc744f98bc2d3f983c1a5f97bbca9f96dd351f96d3371f9616d19f95fd4f7f95797c2f94f85c4f9424c09f93efa94f9324ceef927d2a1f91cc656f90abee3f9002e2ff8fbe322f8f26245f8ee21f0f8e93b08f8c3ac64f89f3d44f89b3847f89a92f2f88cff80f87c6bfff8761fe4f86cdeb7f867996af8624f06f85223f3f849a466f838f56af8377d11f8369342f81e5e1df81c1b2df8192afcf814c43bf7f5dc33f7f3f8a6f7e68e87f7c0e15ff7b01791f797cfc5f78e742af78038e5f778b5d7f75d6d73f75c4544f734f151f7281445f720d43bf7007a62f6d04cfef6c1a628f6c11c1cf6b80b62f6abba69f6a1e15cf69c0319f69a690ef6965a59f66ac349f667e77ff66392c0f65decb1f63c79c9f637fbb0f637bdfdf6224b29f61a0eb3f611c3edf60a92c5f5f61640f5ee05fff5eac283f5db9c62f5c63c7bf5bb1508f5b0b6fbf5960827f58ca168f566fa2df55944f0f554cf92f54ba55ef54557bef53c037ff535613bf532fc25f52fca29f51e2d19f513cf8ff50cc289f50b4891f4fd76d0f4f4fdedf4b3bdc2f4b32899f4ad26e6f4aba465f49cb7daf494cff7f48cde50f48bd9a4f48b4508f480d7b6f4800709f47f91ecf4706208f451a007f4264e1df424c712f4188e7bf412f288f4115296f40fbeb7f4081a42f404579ff3f7c93af3f0dc42f3e4c9f6f3d02f80f3befc22f3b1a683f38b2966f38a794ef387a31af3726620f35c6c03f358286bf352d687f3448826f3420327f33ef590f32471c0f3074d53f2f8a5bcf2f0f243f2e95975f2e077faf2dd896bf2d9f43df2d5440af2cc800cf2c6133df2c3fac9f2b786a7f2ae32b9f2aa4440f2a880e7f293c25af289db53f2717bc0f26fbfc1f259b946f240c413f22c4de0f225f64af221b681f216d662f1f41142f1e6a173f1dadb3ff1d53ff6f1c9e2c1f1c1f7eef1bde13bf1b144f2f1aacc8bf1aa4d23f1992e1bf197111bf1910b3bf18e3df9f1373f22f1296495f116aaf1f11422b4f1131154f10d4970f1070404f0fb96a5f0f26c76f0ecdee1f0d4c668f0bf01d1f0bdf228f0b6e76af0affeaaf094b70ef0791ee2f075aa7cf066a9adf04d2a79f04452d9f0416ee0f03c56f4f0347e5cf0333b23f0309ff1f02a83f0f01efb8df00e6ee9effd8797eff98c17eff60c0befefe805efeeccc3efeabd9aefe541b7efb8ada9efa1e861ef9363cbef8ba102ef79d2ffef70fb5fef404f59ef3b176fef374a13ef310e56ef1b747cef151287ef12f698ef0d09c3eee96f5beee92399eed92922eec9f7f2eebee58deeb9ba7aeeb7167ceea0cf1dee9ab6d1ee87bf80ee838fd5ee809807ee567acdee5500f7ee542b1fee4e26edee3e9eb3ee207373edff3011edf9d06aedd39901edd07f52edceed75edcdb477edc8e7a2edc38633edc295faedaa5cbfeda49baded9db7b9ed8fce61ed8ce04ced8513e2ed704051ed62b07fed600c36ed546b3ced424020ed3312dced29fcdbed1e1133ed017646ece5d846ece3c810ece022c4ecdffb36ecdbc9d4ecb5aed8ec9bea8bec889c62ec7810d3ec753a51ec726b1dec6e9b75ec4eed56ec4ea556ec39f37fec382154ec38091cec37732bec2c1d73ec28ec6fec2488c6ec245c1dec17f0fcec112ad6ec0e6e1eec040f8febfb74d7ebda5daaebd18e00ebc21c2eebb4c9eeeba172a0eb984ecbeb6fb178eb6b038deb60f5a5eb4a87e7eb3d892beb2d80fdeb2cbf64eb2412efeb156557eb15505beb0e0d5aeb0243d4eae17274ead73cbeeacb87a4eac213fdeabd1ac1eaa4ec72ea7edf53ea6282fbea61c94aea5edb46ea59159eea57e3baea5392cdea47ddebea460bcdea430ce4ea2fdd44ea2eec5aea2e31f6ea23e18cea213cdeea1c5d9fea1a74bdea1214daea093c6ce9f68a25e9f2d516e9dff2dde9dcaf8de9d22bc3e9c02236e9b8c838e9ae9904e9ae754ee9a8a06de9a78f11e99b9fefe99b0034e98cea01e98c7229e98bf404e98921c9e984e86ae96faa5fe96b42c5e9694f0ce9468841e93dbea4e9277268e919dbc2e90ffd3fe8f4932be8ebb1fde8db9941e8d91971e8d705e9e8d7015ee8bc88d4e8b1b383e8ade732e89dcc47e8938307e885466de88344cbe88323d5e87fd33de8703c1ae86344b9e858e1bce856c470e85446c1e848bcb4e8420571e824edefe820e080e80e9ad4e8076869e8013beae7f8350ce7f6d2c0e7cd6bece7c26b93e7aa6a94e7a33a53e79edea8e7984443e7898ddde7746e72e772a367e7543acee74eca54e74d333be743861ae7421d8fe740a4e6e7334f07e70f5e3de6f7e47ae6f411ebe6d0ebece6cf18c9e6cd59bde6c77e8fe6b42a76e6a0e5a3e69cb084e6803be0e65ad448e6546a53e64d646be625e688e615f802e60533d3e5fed0e3e5fc4fd7e5f33f39e5ee9089e5e20300e5c37b2be5babd00e5b763a4e5acd3a8e59b3a16e588d96be576e37ce56ffcffe56bfd66e539f860e539550ae53158f7e52f0bdfe52b6bb2e52af7b4e524b520e5198b9de4fd8999e4d2a890e4b9295ae4b3cee2e4ad04aee4abe142e4aa963fe4a7e74ce4a123a2e493d7aae483456ae460b5ade4604f0fe450c3dbe450bda2e438e922e438603ae41d4258e41a0b43e40b8840e4065c94e3f43fe7e3f061dfe3ea2b85e3e3d926e3c910cde3c76642e3c73b85e3bfade5e3a42b93e36dd8bbe3649968e3582e4de341f683e33cced1e331f1d7e32cce78e314b56be30df255e3036409e2f40a48e2e7825de2e2d8f5e2db36abe2d931e5e2d7d312e2c5acf2e2bff775e2bbaed0e294b420e278f0b9e2743734e2552be1e254a18fe250aa97e24f066ee24a4c03e22b744ee21e72e4e20860dee1fcd913e1fb7db3e1ed3366e1dfb7e9e1dbc967e1bec93ee1bd0a4ae1bb7da2e1b5e733e1b1be21e1a97884e1a69026e19beb37e18030c6e1793d1ce177af3ee17639aee172476ee14d6cf4e1397264e1309e5de11e8e50e1029d61e0fdecf4e0f82dabe0eed8efe0e73624e0e41c4de0da5227e0bd8988e0b5b04ee0a8c021e09677a9e0654e4be02d96b1e029a06fe0292863e0236c12e010220ee00f2474e00c7805e0048efae00352bfe002950bdfe65e05dfd8aa53dfc2bc1fdfbe3865dfb18f13dfa4146bdf9757c2df900796df771a55df714015df7010bbdf675b59df5608dbdf528455df4587e6df32a36edf277e4fdf2484c8df122fdadf111933df0f4241defdcab0deee0aa7deeb10e6dec4aa00deb33796de9118e9de8f1b96de83ec81de82f49fde82b161de7fbac2de77c5bdde746b5ade73d423de5e58fede502d06de4a6368de3ef7d2de12a0cbde1062edde09f22bde06e962de00713adde5000bddcb9d90ddc3fa74ddb71b85ddae0963ddac629cdda918eedd8d2611dd884864dd83bd67dd70b072dd42927edd3b21ffdd1886eadcfadafadce71140dcbd36bcdca7e81adc989035dc981c72dc9463d2dc80dfefdc73d4f5dc6f9b8adc6ef735dc4d39dddc3467bedc2cf32adc1f66e0dc1e9c0cdc03d0a9dbfd1ba7dbfc7194dbf1eecddbf18b7edbde5086dbd5fca9dbd4640cdbc74b98dbb052d5dbad4736dbabec6ddbab88eddba9eae2db94ebaddb94e5f8db8b2f14db66a85adb4f0c5cdb4ba981db497df9db4647eadb3bf6d8db364c06db35dbc1db31cb43db258137db17503bdb144650db122f0fdafd8487dae57884dad8bc77dabb0ec9daa25e12da9e1f9ada8494a8da81e1d9da3d3983da3a8c2dda330e2eda222741da178335da11d48bd9fea361d9ee5266d9eda20cd9db6578d9d397b1d9c2bb56d9af05eed99cbd0cd996fb3bd98d4e2dd97ece6cd9781a44d9546b9fd9524c42d9494b2ed933e3d8d923b012d91f84a9d91b0923d9154e5dd90eaa44d9081207d9040d67d8f496bad8f3ff96d8ed9100d8d2a5a5d8d0ae31d8b94e7bd8a6a949d89cc1b5d88dabcbd88772b4d882e20dd8810bcbd8688654d8639ce1d85ae432d856f1bdd855c6b7d8492b4fd830e08fd8308e15d81e066dd80e6918d801fcf8d8018becd7fa3a88d7f9d65fd7f051b8d7dc3008d7d351cfd7cd0545d7c02232d7bc0999d7b17545d7a5cff1d794a5e6d79418bbd792fb95d77306e0d76f45d6d7687a72d75978a3d73fd709d736f04ed73692f3d722fe82d70e164ed70624eed6fb9ec2d6e8f582d6e2ef2ed6e08ce2d6dfadadd6d74318d6ccce19d6bbc35ed6b7f40fd6b494d2d6854035d67b70f8d66f29d8d66d36c2d66d324dd66319a9d652919bd6378299d636ec23d6356515d634f979d61de2b4d5f62670d5f468a8d5edb146d5ebca57d5d97cadd5c78965d5c3ec28d5c219ecd5b7b41fd5961442d59020bbd58b2d23d58871f5d56425a2d5617d98d5557c32d53fdd3ed531e157d522ba02d51b2530d510b4e8d4e77c44d4c446c4d4ae4093d4a1259dd49c49efd495c185d4853965d475595ed46ea3f8d4632845d4600a36d45371aed4431cbad438c84cd431656fd42cfbffd41a68b8d4090c5cd3f5d521d3d66ce8d3cadf5cd3caa06dd3c88e34d3a8345bd3a62518d39b48dfd39096a0d3760539d35f21ddd3553416d34a7b6bd347263ed33a7bdbd32fbe06d3293afdd31eb9f5d3154a6cd3090a42d2ffd64ad2e6ba2fd2d3ede2d2d0d237d2cdb743d2c11f8dd29a7fe7d28f8781d289fd12d257acadd24f3bf2d2484149d232a613d2313b24d2312088d227cc7ed220dc2fd204e4d9d1f66846d1d468ccd1d320fcd1d15175d1bdd55fd1b3dc4cd1b329cad1afd519d1ad30bcd190f48ed18894ded184dcf8d15fd5d3d15e2c4fd1576e8bd147782fd13c89f0d134290ed128775fd1282c26d125e6ffd11a8e07d0fcec5ed0f487bdd0ef2911d0e23182d0dca862d0bec5ddd0bb21fad0b91ae0d0a85d5ed089ca4dd089ba8ad077e979d072caafd067b5b7d0616286d059dec2d053bf04d04f8444d033c05ed0318366d02d20e2cffb5aa9cffa8693cff68183cfe69399cfddfbc1cfdb8680cfd9f9b7cfd68053cfd28115cfcae480cfb38788cfa38837cf91aba7cf8e01facf705b3ccf6c2f51cf5f3adacf494256cf32f733cf303d0ecf20fe00cf1d3fa8cf0dc13ccef5e139ceeb33f9cee6ff90ced52b12cec7a0a0cebe6dc1cea9d1cacea99402ce9a7613ce8db32cce7cdf2fce75e69cce6e3cc0ce5fa6c9ce4264b5ce41fbf0ce152b78ce0f9d1ccdf9f057cdeff5dbcde65866cde072a6cdbeea62cdbb7d6ccda92e48cd9d3ea2cd96cb53cd93b2facd91bbedcd8fe65ccd8f554acd82d7e0cd7666afcd58f060cd50fdaacd4a2d76cd41d3fecd372e02cd1b7fcacd157c72cd0b96f2cd0ab84acd03e0a0cd033108cd01fdb6cceb8531ccdbb081ccdb8f36ccd68327ccc79810cc9c6b2ccc6ecad7cc698810cc575d97cc3d5d3fcc36e9e7cc33a420cc21ec7fcc1e6615cc11c6c2cc012291cbf5bf23cbf1d943cbeccf81cbec5cf4cbe9a487cbca61ebcbc7a065cbc56b56cbc46503cbbf4502cba3d396cb9a9c48cb885872cb8039fccb793177cb6b4903cb6b0d64cb425174cb3db82bcb2cd6b2cb2bf2c4cb29cc2dcb234490cb0af092cb0a7abdcaf44c48caeff8b2caebe49dcad1ab95cad0b502cad07c1ccac45f4bcabda7cfcab0626fcaaa6b5aca7aac54ca6c4b2bca6a970dca5e606cca5c4c5dca5a3d15ca598684ca51a122ca511422ca4c302bca237e72ca19f28fca15c118ca0acc1eca0a9de7ca0a28cec9c23132c9c106a8c9bd182fc9ad7efdc9abd5d4c9979803c98885c0c986e59bc9866239c980a29ec97a05acc97984f1c971acb1c964efe8c963a9cec960f37bc956a83cc955d012c94fa9fdc94ee609c928f1d7c919d661c916c456c90d3fedc902baf1c8fca1c8c8f1e254c8edaf2ec8d17168c8cdabefc8cc98a8c8cc24e4c8c60372c8baa48bc8b38223c8b30abfc8a998d3c8a29a65c89f3cfdc8990caac892e17ec88fc0e0c88f6600c88d0bd6c872ecedc86c89f3c86c2044c8648bc6c8642814c85d8364c8398257c82dadf3c823718cc8187968c806de03c7fc4a9fc7fae24fc7f934d5c7f12940c7e45ba7c7e1a247c7e0e4abc7d9ff25c7d74a3cc7d57d86c7d2a178c7c5c42ec7ba447dc79e7539c79bc35bc79a2d1ec7949c4cc793734bc78af781c7846982c77e86d7c779939cc7771406c767dc3bc746ae17c7401486c727790bc725dd5bc718d44bc70b3baec6f84241c6f32951c6edc6c8c6df4eaec6db8479c6ced129c6ccc95dc6cbe2fac69f8d15c67d33a4c672fbbfc66b189dc66a9c73c6644ba4c65c0e6bc6480c62c62e1d58c62ca263c6279d0fc627238cc6269fe9c5ec8fd2c5e4a030c5d25bfbc5c0f8c2c5b90fd4c5b6d5e6c5ab3a6dc5a91ad0c5a26bd4c5936bf6c5912722c58b6003c589ea26c57f14d5c57a9fe3c57a8731c57953c6c56fa7b3c550eecdc5436fd6c5400713c53c14e0c5120400c5092660c50836b2c4fd3cb5c4f93d08c4d26e07c4cda5f8c4b9ed05c495db37c48bfb38c48a100bc477d512c474a249c47152fbc46fe0e6c46369a3c44c3e02c443d1eac42ebc60c425f001c421dea0c3fbf4c7c3f31376c3f03592c3dacd0fc3d1df83c3c519fdc3b66f17c3b4c047c39f3cacc39b9d06c39977afc391c484c383248ac36522e5c35b2276c34d2dd7c349f078c33a554ac32f8ea7c327f5d9c32617f4c315becfc2fde27fc2fb7b2dc2f1c283c2e46e0ac2d8f5c3c2d7141cc2b2cccbc2a68de3c2a3088fc2a28046c29923e5c28a01f9c2778978c2775875c26776afc261878dc2524cf0c240de54c23a094dc231439ec22525edc217b6f8c2059e49c2043e4fc202c188c1f71a0ec1f2986cc1f21629c1efa149c1e78c5cc1e4dd54c1daecacc1d0d408c1a6a08cc1a0594bc1982957c1786b65c16e3953c166b1d3c15cfd19c158dfbcc15344e7c134fc15c10ec391c0ed9977c0e9cadbc0dff9bec0c459dbc0b07ac3c0aa8feac0a88245c09e761ac08c4bedc0850c1cc07389d2c062b08bc042a647c03744c1c03554acc01a41fdc01411dbc007671abfd5ef0dbfc8c41dbfbabaa3bf9e9cf6bf6b5e76bf6971cfbf603fafbf4f4541bf40effcbf3a1878bf364893bf29b6e2bf0fa958bf098cdfbeffe927befd4d9dbef1ffcfbeed699fbeec8fbfbed5c230bece9669becd9844bec5d330bebfaeecbe910246be8ef8f4be84a13fbe830634be6ac8cebe5fabadbe52d19ebe4fb3efbe472d58be43a530be373682be2fa9f3be1ace46be1413f3be12a097be10093cbdf5f657bdf22a21bdec4f2cbdd99de8bdbc8bf5bda93e5dbda25bffbd84828abd7c433bbd67bbf6bd667ea6bd4fcfafbd3e66a3bd26b4cbbd1e6384bd18cb73bd12e6fbbd078a75bd06f8a1bcfa664dbce33a1dbcd241b2bcc97ad6bcc0154ebcbe710cbcaa444fbca6ff81bc9e8f99bc9c5dc2bc90f9f2bc8a3484bc7773a7bc72f889bc4c817abc4b25e3bc42b070bc336201bc30d079bc2578a9bc1f7b6fbc1b0e8dbc18fa0ebc11b155bc0514c5bbe5a3d8bbdedb2abbdbee08bbd78b94bbc64a56bbc44f18bbab0fd6bb9e662cbb979218bb8fd035bb88f59fbb7b5703bb7b3e12bb7b2f1cbb6bdbf8bb551275bb4611a6bb2e1951bb2d9c6fbb1a7519bb14147ebaf0f79ebaeb675abae78d03babf8df0baa236c8ba989f50ba8cbdb9ba5d9721ba4c7ae4ba485859ba40d0caba2eeb9fba27b91aba269558ba1dfd2ab9ff4bf3b9c8d754b9b77d35b988f47cb98484ddb9707243b9600000b95dfe06b9575ee5b94ab6f6b93e483db939b9b8b93468f0b91f0b92b90fd765b90906b0b908b83fb905bc20b904357bb9041013b90190d5b9000b0eb8fd0fa9b8f1661ab8cdd997b8cbd8d3b8c65605b8c1760db8bf130bb8b4f29db89f5a8ab89e3722b89e1476b88ab9ceb88a232ab85bd1c0b85a7604b85a6b1bb84c5d58b84b3ae9b842b8c7b841a774b839f07eb82c4e01b8161064b8107d81b7f5a802b7e307b2b7de6dd4b7a66631b79032adb78937a0b77a41f0b775652bb76fd658b7630ca2b75febfdb74edf46b74dcc44b72183d0b71e23d5b71a523ab71739f6b703a4ccb6fbff61b6f923c1b6f28cc5b6cf18e1b6b43ae6b6b0ff1ab6aedfceb6a4f813b6a37e44b6a2ef5cb68ce1cfb67f2169b6463e57b642e70cb63a2982b629a089b62906d7b6109e9fb6081c9bb5f6646db5ea455cb5e93791b5d52452b5cfdfc9b5bfea4cb5be3c73b5bb0acdb5a8d948b58b4a6db5836599b575fb8ab5626ff8b560a05bb55b1d5fb5468f38b53c7e50b523c848b51aa307b519893eb509e277b505ed6fb4f5230cb4e35258b4ddb793b4d250dfb4cbde80b4c72f0db4c4fee9b4abecccb4a73d72b48b09c8b47a1fc5b476ff5cb468e191b45f05b6b45788f0b43c9f75b418fd36b418dc6cb413cf05b40c3b23b3d8b492b3d85e53b3cb30c4b3cacb3ab3c0d7d7b3b9a405b38e9540b37adcbfb37a90b9b3689e7eb359bcf8b350e2ecb34f68f4b349647db34658dcb32d48c6b3066059b3025acbb301eb94b2efc24eb2e08e4cb2df287eb2dbe5b6b2daa177b2d2c865b2ce5139b2cafaf4b2b1eda4b2b14ffdb2abc74eb29d374ab2993bf5b27f242fb23fe822b2357be8b2252ae2b224b86cb20d7b9db1f001cbb1d4afd5b1cf094cb1b5a45fb1b43205b19a5cc2b1967f56b1894879b183a782b180907cb17fb369b167a470b162246eb15dddb3b150eaf5b149a0feb142eb30b13839c3b127045bb125bd86b1253c60b1012655b0f43cc2b0f1206bb0e3897cb0cafb8fb0be58d2b0b4d30cb0b36ffab0ab6854b09a24f9b08c3ba1b08bd743b079a500b0748151b06dc1e3b06aed8db03c43cab03a6052b02f0ce4b00f8a78b00ab69aaff4ddf3aff3c09eaff31febaff0d4a4afe535c2afda2408afc8d04eafb25e74afa6442bafa4ca33af9bb1b7af8aae1daf84a66faf8192caaf800d91af7bcc6daf6de315af55fbbaaf4b2467af383239af2e7f74af2c9fc8af1b5032af1498c2af1205c0af0740d7aefe09a2aef562afaed680faaeb6f057aeaf7f32aea5566daea21acfae95b038ae7e927aae6688adae5fcf60ae5848ceae5347a7ae4a5f76ae2b1c8eae0f2405adfe7af5ade8c4efaddbaa36add92a18adbee3d1adbc8a63ad868bccad75ed98ad61338fad5ca3cfad565f55ad27461ead0dba5bad0ae900ad067e3eacee4970ace5d74eace00c26acdd0a1bacdb6978acc4805eacb6158dacb28834aca9a6f0aca49912ac977b70ac942e9dac74642eac64b3d7ac63f12aac536cc9ac4feb91ac3546a1ac2d7709ac16a3a8ac016dffabebe39aabe4f556abe3f7b4abe239adabdf9d26abda481eabd68aefabb22dbdabac21a4aba085a6ab9dda0fab909c90ab8c8498ab84d788ab7c9417ab7b21e9ab78d2eeab77f410ab675feeab67488fab5f5a4fab4f8ad9ab3fdd9cab3c4afcab3485ffab1acaefab0a777baaf49657aaeecb9daae9aee6aad326a9aacc9273aac85c19aab3d109aa96f87caa8c3f48aa82aa10aa81b617aa79c681aa72d6f2aa4f6534aa4a3e1faa47ed7faa413335aa3e7183aa3b925baa3a60afaa302b43aa2e14c9aa24f5a6aa213eddaa1b7423aa067b58a9e4dbaba9e1a184a9def368a9d8c4d0a9d41e17a9c28302a9bd15a0a9b6c597a9b1604ea9aee218a9abffdda98f9fffa98f12e5a98ac4bda97d6de3a97bec43a96edc90a945f9fea93bddf6a930845ca9214122a9114209a90b9beea900c69da8fbd1ada8f3c7a8a8db5e19a8da24faa8d64d90a8b26e75a8b01585a8a8dc8aa8a881bba8935be6a88fda13a88e3bd8a875c6dba85a7697a859f623a85054f9a8458c37a8370121a814cbcfa81259dda80c49f8a7fdc429a7ef6037a7ebaf74a7e3e144a7d566caa7c7fd01a7c6f468a7bfb6cfa7b52ef1a7a4a7cda79e037aa7922c52a786b46da75f2675a754f9dfa72a3d86a72875f2a70e7620a70d7ba1a6fe6b0ca6f2f9dba6f08e7aa6ea36fda6ca7277a6bbb7c3a6b85e67a6adce6ba6ac655fa6aa5269a6aa2ca2a69d4f99a685a012a6745925a655dd2aa6472dc1a646b430a620b119a613723fa5e7ff01a5e3de98a5d4940ea5cf3a71a5c6b544a59e4b8aa56d7e2ba563a70ba5624403a55cf0c7a549ab3fa5438086a5349822a5312b8ea530179aa52d068aa51e7e76a51b7cb4a513311ea5117a20a5086e66a507a7dda4fee9dba4f392e7a4e3385ea4db5d4ea4d6b5cfa4ce515ba4ca49d4a4c5c55fa4a0d1dfa49ad217a4988ab6a48b29dfa481b91ea481113ba467b9cca4625d28a45a1865a44a01f1a446c0c5a4427e2da44110b3a4374d1ca435bc6ea4325a3ca42597b1a40ef2a1a40bb60ca40588f3a4005128a3ff424da3fb7bb0a3f97f9ca3f4cd17a3cf3304a3c97a49a3c5ddaba3b24c88a3adf740a378342da3648456a34dcb0ea34a2c65a33ab13da331acf6a32acb72a311a8e0a30707eea2fdd3f9a2fc7876a2ef3b09a2ea7daea2e93932a2e70ea3a2e51caaa2b70f3ca2b546e2a2a75d8aa2a3104da29e5db7a293ed00a28dd856a26fd788a2651f1ea25fdbbfa25c5329a25773f8a23e2925a221980ba2200338a21eb985a1fe57d1a1f164ffa1e685c6a1de8bd4a1c4bf5ca19f6e17a19c800ea187b25ca186cadaa17ea2b3a171e2f1a1555de3a14c9a46a1498687a14698f3a141dd8fa12ad541a11d32fda10da93aa0efcbd6a0edebf5a0cbf452a0c4c212a0c29bdba0af79a4a0ad7f13a098f7dca0910259a08e713ba068fe58a06045dda05d9220a05a5e22a055f368a0472ce4a0438c56a038ba5da0383524a0328437a0319ba6a02e41baa02152dba005f2c49ff1f82a9feaf38b9fea4f349fe7e4d89f94a6ca9f918d579f7d8b129f71ce8a9f696cd89f6321599f6145a59f5a81829f4a4e5d9f44eaca9f3f7da79f3c8b449f3885999f31aed79f2adf7c9f207b539f206c189f16febb9f0abe1b9f07ffcc9eff6b169efe2afa9ef8e29f9ee58f4a9ed8981d9ed19fa19ec13c269eb9ddc29ea7f62d9ea7703b9ea6473a9ea1b2619e9dcb709e95e10b9e76346c9e7405fe9e6d48c69e65782e9e60da919e5f3e849e5635269e53c9e99e4898cb9e45ccb79e41ca8c9e2bc4929e2af3a49e1e8d519e06e5dc9dfcc0689def85059de35e329dd0890f9db671969d989a2e9d899da19d6be93a9d68e6639d67ebfd9d660fc19d643cb79d5563e69d4ee16b9d41df659d40eb249d38a5a79d2dee109d12ceae9d0f08409d0d55d29d099abb9cff63c19cf59b3a9ce4e3b39cd238819cbc1e509ca547649c9f14d39c9a0aa99c93b2e69c6d22009c683a0b9c661a029c45d30b9c3ad11d9c2efa269c1bf1e99c1541369c0c10f79be6ee969bbc64d39bbbd6c39bba8aea9bad4cdc9ba2a0b69b9052d79b6e17689b6867739b5751729b4215d89b3d3d099b2fa5179b28da7e9b1c43ee9b1a3c2c9b0a9ec49afd995d9af9f69f9aee561e9ad2eb999acf90099ac3ceb49ac2aa059aa31a519aa2291d9a9b930f9a93eda49a8f90689a8383929a82491f9a6e46b09a3a46ec9a38f8e69a32bdd59a25cd569a1b14b79a142dd69a10b66e9a036a9799da15be99d1e65099bddefa99a9500399a09ada999fa7fc99895acb99743599996bdf45995693329946e5eb9929b07d9928724f992319d3991f32e4991df8f299157547990ce9f39908739a98fa1aea98f3282598f14c7b98e3959998e3549898d7df0898d0868b98bcae0498b5f61e98a9187f989d8dca989a06339891b06a9880a0b8987d473f986fb85e983ec09d982ac9b09822f80b980df6b09804b8f597dba79a97d97a7f97cf149797c8325b97be58f097bc3aa797b64a2097a33c8c97a3005e97a19015979fa1f397886006976f0a3a976e2d10975bc96e9757640d9701659e96e4ae0996df03e196da617896c31e4196b9c7e096b566f196b1962796b1191396840c939678fafa967831da96671a09965a6b35965927db96573236964dec94964cf0df96421bc89631f6029623f11496229a6496227a499616643c95eb01f895e4745f95ced26295cb14f19598b492957e57f9956bde7a956adefa955e263595577a21955770c99542ee499542d578953657a7952bd5529521720e950e8abd9508bb4794f430a194eea3d894ee770894de3e5d94c988f794c64f6d94c30c7e94bae87794b1674b949e61b0949bde979496b1fe94907858947efc689467deaa944c4eaa944a99f59449187894412088943fe88c942efa3a942031dd9412238f94119be69405b02693fd1c1793e86bd193d96a1a93c6725d93b1638893ae40e0939ecccc939b7acd9384f1d99382e92393705974936fce8f9367bc2f934d04b3934a26b793445a8e933258019323c20a931ba3fb930ff576930867279305705092ead75c92d563b292c0bd4092bded8092b0bacf92ab1121929d01fa9296efea92919f0f9290e954927993e29272db44926d4634926854d0926270e3925daabd9252bcb1924d0ba2923e0202923d84b392374725922fd8fb921193a592103719920444a4920037b091ec54be91e8b60491d6ee3891bb5f9291ae567391980df59186c24391803ae49178e43c9173987991706b10914e5d5391489e119145ed6b913e3c2b910db3b2910c0a5c9104c5b690f3c3ab90f2308390ec133d90d92ea690d3a7e490d3450190cbf7cb90c9cbf290c3181690bddfbb90b700be90ac1e8e909416aa907e6475907d81269074cef99072d3ef90704955906bece1906bacea906385f5905308d6904f3b41904eec819030ff19902f4cce901a260a90088c768ff93b128ff5b6ea8ff3f57c8fef737d8fee8efa8fedb1d08fc18ac18fb05ed28f9855708f96d3288f80aa538f69d5a48f66e49c8f547b638f3ffd228f3ced638f377b818f322f2b8ef7dcfa8ee018328edee4d18edae48f8eca2e318ec7f8268ec515618eb9de528eb48c778eaa56998ea743818e9228ba8e91c7598e8a1ba08e8403248e82e4578e5ab11f8e4822618e4628fc8e41b5fd8e371c088e3713d28e30f7c48e2edf928e12b05d8e075dd28e07344b8e0597ac8e04de6c8e00f3fd8ddae3268dd8ac678dcf42a58dc884ee8dc5372b8dc1f6848dac73e28da09da68d96c1b18d9589348d85bc008d82fef08d7b88508d72735b8d55db708d494e918d3fa5228d390c3f8d2909238d1b08ec8d1282ff8d0357378cf950278ce905468ce386b48cca397c8cc64d678cb6100b8cac0e9c8c8134e28c7d53b98c6a95dc8c643ac08c6097aa8c604e438c4956bb8c44864e8c3095728c03ef6e8bf419ea8be44c048bd60b928bd5dc508bcc3a8e8bc581a78bb91e3e8bb1b4a68bb0b00b8ba515a98b9662fd8b9616e38b8518fb8b794e698b6d46118b6988b38b594c998b520ee58b4a01bf8b2c92218b2bd1258b1ce4918b1ab71a8b13879e8b07caa68b0200428afe2a548ae831b68abdf4268ab626418a9c33858a9b69118a8d6bec8a8087468a6a790c8a62d1388a46f6d78a444bb68a36f1a08a352b8b8a25ee318a24053c89fbbcd489f8792c89ec7e2f89d3df9089bb1cdb89b2a3088980dfbc897f2a52897e9d118961805d893c3c1e891e478c8906ceea88ec4a6788e085a388c1e17088bdf98488adf3ab88a69556887c8cdb887520c88874b7978859e17b88583071884f19e5883eeaaf88310157882c4db7882382d58821ee8b8801d81287ffcc3087fd795f87c7d80487abf22f87a9349687a087fb8793ca608791f414878cbb5a8786b638877509dc876a7cd587672d2987544b03874ee348874661ab874523f8874099c7872d9d268719cb8e8707b1e286f8620786e21aa886d1f0d186d1415586b35ebe86a7e2a4869aaff386958ede869466b986866a268660b2b28647f3f4863746de8631e9a98630e6fe8629f9968604289f85efefae85dd7b3185da097b85d4fb1185aeaf4285a7a6cb85a51c478590ed3b85820319856a3008855cbb708550e2b78550d6fd8539856b852f1fe284d9bc6284be079a84bc0c5584b685dc84af42ba84aa444684a7cb7f8492bf4784878d79847503e68470c2c6844ad558844943be8448c12c8436f91d8428f09c842117ae841f3e4884118ec283fdfea483eab02083e92b9f83e671f883c168de83bba74583b435ff83a7eb7483a626d68399f40c8390b26a8388dfac837c56de8355356a83516812834296448340500e83384f19832cb0ec83272c458326a8e3831cbacf831b844e831441ee82ead50482e9f33682dee76a82dcebac82d7a43e82c69c9282ac32e482a78e6e829baa22829ad5f9828df5d88285c8ff828356d982741a65825e095d82566e30825351698251cc058226a26882241d4d82208a408218c21b82069c94820401a181fd8bce81ee395d81d5092f81d04af981c77e7f81b15f3d81adfdf981a7427c819d83608195f4668184ec7e8183bf73815066b681445bb7813f9b9081383f84812225e0811b2074811a93a781020ae880f012d080e4408f80ddf13280c6240580c29cec80b8ccd280b3a84080a8cbd180a7931e80a0c4aa8084caee807d39d4807d2e1f805811d9804952fe804755e480408439802f5ce8802bacbf802ab1c88029974480227fbb80202ea0801594e9800579ad7fe95e0e7fe94e867fe5b6d97fe4459c7fd84a297fc54c6d7fab234a7f9927cf7f8f94b27f89e70a7f893ede7f7b55867f7b20e47f6854777f5e03357f5b8e297f54031a7f5000a97f2f6e2d7f2f5cd97f1c49897f1b65247f13f4557f1104227efe89017ef61b8d7ef576017ed1720b7ec7b0ff7ec36ac17eaf47397e950cbf7e92f21a7e87e66a7e7fceb47e6957127e6946a07e58be207e5164fc7e4c04057e132f507e0f75fb7e0951c77dfea3b37df018a67dca24f67dc6e5457d9bd6b47d94fccf7d9494627d93bf5d7d91f4d87d8b950c7d79a2077d643bf47d4933397d48d6fc7d43117a7d3985ff7d30b0227d270b167d2354ba7d19f4d17d16bd8d7d145f2b7d083cb07d03a5087cf7b2cb7cedd1737ceb60657ce20e487ce152d87cd0bb557cd079317ccb69507cc2702b7cbfc9557cb3a7ca7ca854847c9ae2577c99ff107c92092d7c8f75d27c83fdda7c810dfe7c8020b07c752f0d7c70426a7c6e6cd77c5eeea97c4225957c34faa67c1ea7a47c1ad2b27c19301c7c1362327c10a1377c0f8a5f7bfb8cb97bedb0e97be2d00b7bde98627bac65a37bab3cc07ba5e4f37b9e470c7b8c8e087b87e0697b84fa517b7e4d4d7b7a06bc7b7710f97b64b1d47b5640f17b3fdafc7b3bae457b3b2acf7b3a7fe97b391a7a7b314e007b247cfd7b1e44537b1a7d707b06f87d7afa5e1f7af505d67ae1bf267ade21677ad985667ad8b2ec7ad8b19a7abecc6e7a9fe6717a9ec7b57a91876b7a8590877a5d33a07a47d8057a45fe777a1980a87a09a1d57a097e0d79f0b49479decf9679dace5879bb466079ba88a779b4790479a865fd79a6c0ef79a4ec1979a2a6fd79983ba7797fcc717974b465796d2331796ca4977959c95679561a1b7942a237793920b17932de1b7930a2d5792e3246791ea3d1791730ce791383f07901693c78fc63fa78f15ffc78eba70e78e0b1b878ddda6a78bfdf4778b44fe8789c2ae9789912fb788ef15d7883a3b7786a7e377865fce3785fcc5f785a429b78577cf378308704781528427814032e780eca8d7806c05077fca7ac77fb683f77c251be77bd291677bb72cc77b5784777ac26cd77a4d875779b7f6477828530776f97a5776b58b977487473772f399b7701397176fb961b76f955ab76f15a7d76d98e0676d62dd276cc6c4376b6f60b76a9808a76972e3b76907dbb7682a59976774fee766ce241764cbbe3764c5616760acae77609e6ae75f8252475edf6c575ed80b075e5f49375be0dc175bc802c75ad7e8775a18852759729a87592d7c2757ffc6d7572f1717564141575621c3775530b5d754b0f2f75402c03752cd466752790557524048c75104713750d7cc274e9187674da07f474d8f97874c8536674b4e2f77493d0e174913e48747dc3da747710a6746b380e7467210e7465a738745b96ba743e6bad743d70e274346c357425855e74179c06740c3c1673f0aa0273e0d9dd73cf6ad073c0b79f73bac61273b1e8c2739d4a517399d43d737c9944737846b4736cf9b7736212417352b64e734162a7733f27a073347b5b732a2f5973182d6a7314c197730902bd73016d8972fc172872eb91c172e565d172df6b2572d617f372d31d8772d2517672bffab172bd526872bce11a72b8c9a972b41c0a729fb0b0729c6d86728b673972818b627269ebf772505b86724fd5077239a86c7230e5fc722eb37e7211777c720b9a8971ed2a9671c2f2b471aecdd77178e9e77168243271649daa7144f7e8713e79b57135d34f7127b8ad7118f7ab710d49de70f8a63870eddd2070d657f870d260a070ceab5170c477487093ee4f708604f7705eb838705551ba70547afa703dbac6703bb42b702a2e747024cc0f701509046ffcbe836ff6d00b6fe6201c6fc8ca0d6fbb5bb16fb8ba4b6fb542b36f8eefd66f8384e26f8240966f6a634c6f6121176f4ef6a76f4162e96f31a7e56f3145776f2fff766f28e34d6f0b2f836f099ed16efdc6616edefafa6ecf00686ecd2b286ec49c4a6eae9afd6ea5bcc56ea1fd3e6e9b9d0c6e7e04816e6ca1f46e675ca76e42c88b6e4004686e39303f6e37d8096e36c8dc6e28e8d26e119e986df4bc956ddfd7ad6dd46e6f6db7e2e96da8017d6da33dbf6d97ae3b6d9710126d9042716d7e8e216d6c30e76d5591586d4c5a666d3e34446d39439a6d329d136d30b5fc6d1f44ec6d15e0456d0fd7f96cffd57a6cdd2e8e6cd7d29d6ccae2906cbbeb986c9d391c6c92ba836c9054886c9031ec6c8c64fa6c7db2e96c7873e66c6fd79f6c6cbed26c376f9e6c338b306c2846d86c0a70726bf5913d6bea9fef6bea7a9d6bd747d96bcb63416bbea5286bbd79e96bb4fbaf6bad4ec16ba480406ba42bea6b9045cd6b8b126b6b74a4d36b58d8cc6b3c6e896b378ac46b31207f6b2239c36b18a12b6b17c7426b1723236b0c85c66b0b0bce6b06f7f16b026b186b00d0296afc9ebe6ad9bf936ac1a4ea6ab8c4a06aa71eb06aa4f7826a9935586a8edd516a879cbe6a8673bd6a8103226a7eb7646a7d45ba6a7ce72c6a602dd86a47e54f6a466b576a2c14ed6a2447326a1e89786a19aee96a163a336a123ccc6a0ea1206a0b450a69f5f01169dc58dc69a9d74d699773ab6992cb8569905d2e69698020692d076c6925e83869141052690a441068fd8d5968f4fad268e5ba4868e01ab168df904468d2175568b0d01268aa286868a9ae6c68972fbe6886f370687e6075687dc605687c020e686dd02f6863860c685cbc0a6854d22b684aa03068497ea068435559682956076826879b6825ec866825c1e7681799a568045821680091e267ffc38c67f8980c67ec3d7a67eb31e367e618f067e1e0c367d36a9867c6306667b96a7b678da4ec677849de674c43ff674b50d067469492673ff210672d828c672cf9f9671f7e7c671da11a67139f526706c7416702caf366feb6bb66ec05af66d3925066c833cc66c7dede66c06e9f66bd4be6668911f66674b2dc665b1a16664f749166471f6e6642f84e664226ca6640ef9d663b5a69662a1271661cb8c0661a18ba6614a38b660bcbeb65d5e7fb65d358d565d1afad65ac238865a7c1c56598b0a365933f436582b3e1657aa2d365750c786556baf7654c3e9865304fd9652f857b65284306651cdac16517434565166e106504936864f5dc3264e05fbd64dc93c664d7faab64d02dc764c183dc649b72cb648782bd647eaf0564792ef064748acf64739d556467c810645bf5c7645b39a6644078a86428f9d26410c203640d7cf4640802d463ff226c63fecea063f6bd3063f6109163eddb6c63ec792363e8273963e552e663e367f563dab55b63c96b5863c8804863c1858763b05bd363abeb6f6395534f63886695638006046374dfbb635cba676357751a6352890a63401d91631fc171631f7db1631859fb6302600462e97a1f62e6de3a62e520fa62db65b162d4d09762c383fa62be9b5462abe29862a10d47629dbf53628705df625acd7362335692622a7aa26212fa5561e4077861d94c7961cdb5cd61cc3aa861bc549061b07e6161af077461abdd8b61a9d05461a1134a619d151c619d0a496184d5ed617c4300617b5d9f61785dfc6171974e616611b06146639c60f0fdb760eb451360e33cd160e24e8760de507d60d850b460d5edf160c9bce660c083d960b3f7eb60acc2b060a506826083c6f0607b2ad3607558ca60703dfd606a67be60580ddd6047d6886042d021602746cf5ffb24415ffa31d25ff4f5ec5fe0a0715fbf29435fbdafd55fa9107c5fa82a705fa7524e5fa4d3605f9a06045f91900b5f8fd9a15f86f94d5f74def05f7377705f61edd45f531ab05f4bde1a5f4315865f417bb75f3fa4125f3cf5ec5f343a255f1101045efffb4b5efe56355ef8de815eeab56c5ee76f915ee2b1d75ee031d45ec4efd15ea1bf835e9f827e5e9d411e5e9d27bd5e97d7eb5e96aded5e8f7dac5e798cf75e71565e5e5210c55e5176105e4e12735e4d39ec5e3f2db65e381d9c5e2937ea5e262aa85e1841505e157ec25e11b5cf5e067fdb5decf7a65dbb299d5db288115da862cd5d9fa3505d9b056c5d90017f5d6dfea25d5abfa95d59926c5d4d836b5d2dfb5c5d0e58695d0d7dce5d09592a5cff94765cf677b75cbbb7255ca998915ca6aea15c93f6a55c937b515c8e50555c7dd88e5c67e4415c61986e5c60e2255c542d905c5300725c495b7e5c3f8c305c3601b05c1e31015c15bb3f5bfee5fc5bfc07f95bf7baa25bf6dfb45bee4d455be8c6765be171545bd417d25bcde6505bca81045b8f8d195b7652ac5b5da9475b5993fd5b511ac85b489f285b41b8a45b3cc6b85b34a7e65b1658e45b08ab895b06256f5b037df35af4c4855ae4ac3c5ac391c55abb5ec25ab37ede5ab0df005aabb2645aa3a77d5aa16d9c5aa156d25aa0f2ba5a763b215a5c7aee5a43ba125a3a97355a1ed7c45a15c3925a1124475a0f566459f3088759d9347559bd8e7859bc8e66599118c0598acf935983031959779b305969810559491212594368145927347c5923f2ce591c074959028b4358fef9d058f8bcd658f3790758f2332a58cef4f958c6698258c2d5ba58bbdc8058ba5f3058b4efe45895834658711ea25864a234585ba9d058559234583a158f5835674458345ef658255e275823c4095808514558074df657fe250657f4e6b957e6c62b57dcadbd57db793357d687c757c615c357bf02c957bd2e6857ade37e5799824f5789849d576bba2357655e3557576fcb574d3031572f18135726c29f571bea4f5715e3c857116f56570e12ee5704ed9957023a7e56f1dac056ee78f856d8010e56d1ad3f56caf55356bf8ac256bb9aae56b73b9e56b62d235689c03856888fba5672ed075670257756616dcc5655a83a563f4c815628eba05613b57155ed347d55e77bec55d7355455c8824855a60d7255a4e4715583023e558036a35564593d55644b29556253205545c73a5541d71f5532e894552b5db0552a45715528ce6c5520220e551d81ed551bcac15500123a54ffc6a054f5b68a54eb111a54e5e9a054df429d54d2f9b954c430d754b8c03754ad033154a885de54976ac15493b765548efba65488d41e5485ce0d5483e409546e09ba545fae90544c24a4542df0e5542d58b4542499665419d3c15414a5115402c45253fe345453fe00f853d6868053cda04a53c398cc53bfb6f253bf6c8e53b57da9537f2543537e76c7536ee7fa53655dce535959bd535796f7534f293e5344b1405334c6715313a2215311dcbe530aae2e530a95f352ffb4ce52f4452752ee782d52ea921952e4ecba52dd67ce52cd63eb52c17d8e52b2d7b4529ab4585293704e5289bf6d5284fd3b527785c35274933c5272f048526452405254df58522df7c052260152521e89f45203e1c55203916951fc8ce251e3375f51e3157f51cb3eef51ca400751c78ec551c182a151a5faac5192be37517f9d7e517ee7c3517e2fab515e9f9a5157f3c6514bf67351444603514113345134eff45133088a512680725115caa951157c525105d3b250ab8d4a50ab0f9650a32a15508a95205085dc4b50756f7a506c9d45505576265049fd66503350a250332da8502f3e3b5027e2e55024533d500662bf5003aed04fc9ae154fb497bc4fa2eb474f9bf6344f891cf84f88d73a4f7fa6764f7a29b94f77dd814f64778f4f5b9dc54f4660004f32acd74f2f3fe64f2b3f754f0f7b9b4f0824794ef7c0cb4ef6569b4ef46e714ee51ed24ee3b5594edaa22a4ed89ff54ed1ca8a4ebdff434eb33d0a4ea8f4b34ea524a14e6e225b4e61b0754e5782114e565a074e3f99794e23e33f4e1bb8364e199cf74e0127284deb2a3f4dea4bb04de786884dbff31b4dba4e704db5da774d80c5644d79717a4d74c4b74d6b88224d68e25d4d5b5f3e4d38c48e4d364f2f4d2b01894d1612334d12fdeb4d00b67e4cff5c634ce6f0e84ce370154cb13a2d4caf3bbb4c72a2954c72972c4c6582a94c5d59914c58b2a34c5799514c3d48a44c33fbdc4c1f1cb74c15866e4c13a2034bfe5b1e4bf950454bf246694be9c7034bddeab74bd93ed24bcedb0d4bbf4ebb4bb8d1044ba412374ba407294b9e2f094b9c32194b956fb84b8db4614b7a0b824b5f8bc84b5f294f4b3064ba4b2f60134b290d784b1b4f024b1904134b18494d4afcb8574ade82d54adc2fe14ac40a014ab52d674ab000bf4aaad00c4a99450e4a8e643a4a83c26c4a7fcda64a7ab7d74a7a40fb4a74ec1c4a691d5c4a5d1adf4a4e1e094a4b62f04a41085e4a196abc4a13fd574a06b0c849fe65b049fb2d0949e8c96749e59eb849e0096049d729a149d4ddfa49c3dc8549bd325749ba07a849b9011349a7f798496c84da496761714966768e4954644549424ab7493bca6149389c1a49361e1d4924f00f48fb6bda48e3572148d962d948cf1bc148a384b148a0d24a4898c4934898c415488f4abe488adb3b487a212d48733190486d4ed5486967ba484db3cb4842c2a14836a02148348d5848221cbb481ac6744815896a48145789480129004801107847e3156b47dc1fac47d8803947caaa4747b893f147a026454795f6034795617c479301cf4792ef93477171264765750147500c77474cdb0b47309dae4725a896472475674722590b47218156471effc647111cbe47069cbb4705e6cd46f22b5d46eaf7df46dfebcc46dc02f946d2216e46c32bac46b8de1d46ac6fd246aa811746a93d3746a3f69b46854cec467f1c674677acb6466b2acb4667b0c44660775b4654606b4653e517465360b34653189a46415a0d4634601a462bc7fc4621eea7461c05be461b472146131693460b761d460630d045ff5b2b45fa04a845f254ce45eefaf845e6607645d0191745c93c9845a0b91c4597abf6458432c645792e6f456df183456a3efb4568c1074566f46045462cb2453f10be45377762452f94fb44faf2af44ef5e5a44e2161844cad75944ca84ac44c807ea44ae848c44ad892b449b14514499f0a04482883944801597447ca58e4475a9d94467f5f44462b983444f6feb4449ddf54447973f444370c144403070443e8496441e70c9441cbb744415465c44095a6543faeffe43e93caa43dca48a43da3c4443d692cc43d370bc43cebf8743c164f143b1933743aabe0943a4844b439684f94396074c43827e70438204f2437b981443763a6043744532436f67e4435de9bf43339ed1432c9d86431f485a42fc761c42effbc942e08e1142dfc3e742d0293d42c32d7f42c278a942b7123c42a9dff742a188994297e98e428ea14d428b8ec64278a5e842781b8242719538426e62e3426a5cff425cde14425814754245de4f4233504b4229a04f41db717e41d7997541d4cb8b41b1d12241958cdd418c01df4184c791417b1019416b4ca84163496a416278934145168b412f534f412b9150412aecbf412a922a4122ee60411aebd54115050841055bbe40ff4b0840eea32640baf96b40b8578740b2cb41409d549c409771cc407804e840573d294053a5684049b29b403e9de94017d76940158455400940ba4008e81b3ffb57623fe86a663fd23d723fb422743fa6e7e43f9215453f887fba3f88242d3f7e55483f69d7853f69530f3f5614a93f50e3de3f4f6d3a3f4ddb4b3f21b6b23f0379c03ef805bb3ef47d203edb7f5a3ecd9bf53ec6427e3ea59b6a3e98100b3e8accc33e8a31703e7c48183e700afd3e6206e83e503afc3e48cd433e2fb6053e2e2c913e2be6c73e25b4a73e0a246d3e07b71a3e07115c3dfed99e3df0a5ec3decdd013dec5b283dd067893dc7c7d23dc0ade73dbed31e3db2b3b63dab9cd63d9db4e23d9d93333d9303f03d8af6ca3d887b593d865f193d7f63313d547ca93d27777a3d2116d43d17f7f63d098ed43d06b1ae3cf019503cefd1313cecd30b3ce62cc43ce33a9d3cdb56573cd92d223cd460cb3cd314b33cc3ef173cb2ee2a3ca6dfb63ca613323ca07a923c88d28c3c87a72a3c6cc5e73c66e33c3c639fa33c574fb33c3fa3013c3253b03c2656e63c2270343c19192e3c140bf13c12bc153c07f3403bf398133bf10ebf3be57b463bbebddc3bbac1f43bb03b473ba8f6903ba096323b991e5c3b957fc23b9363813b920d9c3b8742ae3b83cf513b7cf6f33b72301d3b67c5293b62c7dc3b5a05af3b52d64f3b2d7d523b22e9fd3affc42c3af77e333ae991fd3ae879213ad2d9fb3abb836a3ab6d7ab3aae509d3aa725ba3a966b023a950f6b3a911db93a82e9523a7e7efe3a7ab6a73a77ac1d3a7353dd3a633c673a62e3963a544d9f3a52fa043a4d3d843a4bf66f3a48fac03a48b9ca3a3a2a883a1a5e6c3a17da633a0263ff39ff352339f35cb339f03a3c39eb2bf839e17ba039c4146639bc860e39a65991399d3a04399970553992b1d8398c930f3965c24c3962a0c23957c3c939506a90394de844394b39e0393b70c9392e8e61392dc1bf392932153927afec39248799392062aa3919f06f391824e6391632fc38fe845238fb3e6a38dddd6038b5e6ec38a06ed538838016387ff902385800e138438d2e38369df3382c57023812737e380a85e6380a3a183806d4df3801825f37e74f9937e1a44a37d60e3437c2d17437b90bd937a9fb8b379d3ef53799ba82377c0a67376f6cfe375a202d3746267737413ff63725c1493722af22371d63493713a4e83702019d36f599fd36c6630836b5128936b4bb0136ae697c36ad5ee936a695c7367b0e90364c3d34364a05f53638dba93628575c35f4bed535e8f8d835e1d31135da077835d13ca635c5bf5835b3a8dc35898ba2358811cc356d5faa355611283553100f354f6237354af18b353ce6c9352def32351d4e5c350a95e635059cc834ec52fc34e0516234ddfe2334d37e0634cdbf4434c37a8534be792034b4ba5234a24cab3498a171348467b63481f2df346c665b344fa1fc34449c29343f85ad342c3ef93428e5a9341bb4c2341a918333f7c62833f301b933f1506733ea735833e065e833b48f6833b4011c33aedae233aeb9d433a64f40339ff6e6338f5b28337e7f9f3379c7fa3376b37633734902336bdea2336bbadc3363b26d3355f10c333ad253330d267c32ec817c32d55eab32c1047732a8be83328e8aac32705fa3326430fa324c44b7323e5a173239fb623228161c321c94ab3214b4c2320b7a163200f03e31f4648731f179e931ef1ac531e5c3c431e2fc8b31df7d1931d563ad31cbdf6d31bd07d431b5b63b31b56bb931a94982318f44ed318bc82a31878857317db27231773465316f95e631684544315691f4314c25d5313f5adb313ad9233135529c3131c3ad312c573f311c4c7e30f86d8330f04ef730ccf05830cb27e930caaf3f30c9da2a30bbb60730b8ed0e30abbd5130894339307544223040a0883018495e3015dcce30155f322fffb5822ffc42ba2fede1052febf0c52fe7b8f32fc7a19b2fc5a78b2fbb196c2fac2c192f995cbe2f98eee42f793f612f5aea6d2f5227c52f3ca6bd2f30bf942f2efc202f2e947e2f21e84a2f1c617b2f0b9a542f013cfc2eec045a2ee7a8582ee6d6a42eddea2e2edae9382ed8d2bb2ec46e6e2ea864532ea3b07d2ea0ed802e9cb8ce2e9012742e797a462e1711ee2e0dbfdd2e064cd52dfda3b92ded355c2deb56dd2dd80af72dc7bfc92dc61a732dbe4df92dba668f2dab444c2d9a83632d8f8c1f2d8b4a912d8294f42d778f062d629e2b2d563ad92d52b3e12d5220702d4b28032d434e4e2d41e6c42d3aee052d1895b02cedcdd52cdfe47d2cd842bf2cd7680c2cbe858a2cac0bb62ca57b262ca4bb502c9802a42c84193f2c70cabc2c6cf2052c5f11552c3e319f2c38c08d2c1a765b2c15f3962c0e91032c0c8d032c0a7f932c0365db2beee34c2be01ad92bd5714f2bc15fc72b8b0daa2b857bce2b82210b2b7cf2372b75addd2b496e662b43944f2b421a572b3cdc082b376d552b33f1e92b1d8c082afba5252af46fe62af1f4732ae6aa532ac9d6102ac66d332abcef562a97540d2a925f5f2a90c6f92a8e67c12a8be5842a8989a32a55ef6e2a3871ec2a2e3d202a2bdd582a287f5d2a271b1d2a15b2342a0cd0f32a0bfe602a00e48829fce84d29ea9d2d29dfd94529dc6b6f29d2bb8229974803299518d029888f5029833395296e1ace29697f6429664857295abe4a2953c3a329475de92946b95029372e81292db514290aa9f62907e60428f8b12928e36e7b28e0151f28d5852328c27ca128c2370828bb94b428a8b37e289e2d57287ba8ab2871738928578aea28557fab2839b8d92836270a283520582828fd0b2821650527fcf4fa27d81eb327d49d9b27d2f3a12797682727904b08278c746d27811d68276152722756b6bd274e22e7274c959a2749817a27455b0c273dd5ca273c5d2a273ace202719c5d22716b1aa26fba77826fb7e8b26f5d80226f47c4e26d7229b26bc808726b37ad8269cf83e269aed4a268dc0692674700c261dd584261c2eb1261af8682605fd6c25e8710625e4f8ff25d09df525b8ca0f25b010f325af5cb225ac262425ab0a7f259ee367258b94132571214e256d786c256d735a256d216f254815f82536fe4b2512d65225101ee525092bda25003f6c24feaf0224fdd62524f607d924f2561424e5803324ccac3224c2806d24c2804a24c1574424bf24a624ba5fa824ac0649249f22b7249ea4bb24954670249399532486af1224833e5c247e55b7244964de24411877242c3d472423aefc24177376241232ac240be0252407ed2223f15e1923e09b0523da528623d7ae8823d619b523acdd5b239d9279239539592387cb3c238576842383bec9237a01222350f730233a9bab23090d7e22fc295a22e257ee22d3515522c3bfb722bd0caf22bb4bc822b3e50722952a792262de2a225b0f7e224a7aa0224565382229e36f2228ef31222847e5221c6989221764a3220a869521f041f921d412e721ba3db22196a96d2194d3c32187992e217cafb1217aed5c216c302c2163e1d42162a456215727d62154bafe2146cbc121440b5d21278021211eb47a21144a322114050b2113b28d210e00f82107c98920fb9d5620f872a720e8654e20e52daa20ced6f420c2a48320bc0f6920b39a5c20b09c8620a1f0fb20a0b9e22087f433207b261d2075c9d520744655206402d720616e68204c2fc62035d758203205fa202e1ee720280d4e2027f84e201e8f341ff7eee21ff0510c1fee05551fe3ca471fe1efb01fe164c11fde60d71fc08e9f1fa66c7a1f9b97291f50a7221f47c0c21f1c29b21f1abdcf1f1636dc1f11ace31f0a3b631f02b79f1efc16d31efb94ea1ef701a11edcd84f1edc17dc1ed3da771eb337c11eb0ca9e1eb0935c1e9f331c1e9027391e8f6c761e7652641e62e0661e57b2461e42703f1e424acf1e41fba81e36f4731e339e4c1e2f9ec91e2b97301e2a1d8c1e2a12a21e1680df1e1664981e0ebf431df8190c1dec0aac1de16b111db943131dabb4cc1da043221d9cbb4a1d8b4c331d8b262c1d7679931d4e868c1d4669541d3f72f61d3e47d41d3ae2a81d3a8ee91d3534631d2287fc1d0f59bb1d09e7251d0600df1d054f781cf8b5651cf5119d1cef48081ced26c61cded0db1cd39e0f1ccceba81cb24af61cac57f91ca086801c9b8cc61c8b3c191c804eaa1c7451991c66a4be1c596c331c589bf71c579cee1c4cc9c81c482b1e1c418cc51c3eb6561c3dc17b1c3aa0ac1c147e021c0b12a41bf76a491bee048a1bed92e51bdd589b1bd479ec1bac283b1b762d8f1b6dfc771b627aa71b5abfb71b5416aa1b40b8eb1b4091ad1b21f3d21b1d79371b19276b1b1903331b0d5a8a1b056a451b03bb361afb9f091aec94811ae784561ad511721ac5e40a1ab321ea1aaa2e0e1a999d491a67cbd51a66f6331a65e5851a454d2c1a3b05be1a28478f1a2661a81a208c411a1ffed71a16801419f8145c19e60fc819e562aa19ddbdc019da416519cf9e0019cc741b19c3e53619c2213119bbd8cc19a58cd81998d18f1995e3c81994ffa31991b30e1991a5ec198598391980e71b197feaff19758937196680ac19608034195928f2195099f21928ff4e191979911918cc651903bb9a18ff7f2518fc7a6718f2448418e9ef3118da7c0118d5fcf718c1df0b18b356f3186f9ac5186d5cb4186c361f1864e9481858f10918396e861837509a183710811825222a181dd6eb181bbc4b18101f1c17ea3c6e17d8a3ac17d0832f17bf9d3317bd4fd217b4587e17aafa4e179c434b1794e9e3179295b2178d437817843eba1783da1a17812b6e178007de177e00bf1766491317550a0a17472abc1733703d1724255316f3a2aa16f13faf16ee416316eaa0ab16d7e7d916d7a2d416d3313b16d022f116cc4a6916c853ab16c37bda16c1787b169dd20e1699a8d01696f31716918d031685753a1675e01d166fa1d416677dc8166757ed16608b0b165ffa29165e4b9c164504a216369a3b162f044016123d09160c9cc7160ac0f215f8c88d15d6485a15bdeace15b2b4b915ac0f631593a41015832707157c20a11579be80157466d1157142b6156e37491554e064154ce30615465ae11538c43a151bf5ea15117545150c83aa150673571503129714ff2f1714f6ee9514e86e7e14d57a5b14d17d3414cfef7814c878a914c0747414b37176149f9242148fc838148bd457146ef1df14653b6b14502bb014039bcb14007f7113ebad5d13e5ef7813e45e4613d4f86613d2db0713cd21aa13beefb913a80fbd13a09af4139269ab13890a851382cda5137c0ea3137b037b1375beda136bac77135f8fde135ab383135276f01345d912132a2470130e10a012df883d12c441ca12c1544412bbbd7f12a82d6912a52a3712a1c17b129abfc212949c68126c3d1412639261125fe605125ded16125c467e1258ee89124d89dd123fec4e1234524712215778121519a3120d5b47120bb269120b25851207116811f9be4811ecc94311e5486a11e22e6c11e2164e11d8de1311cedb6111ca5cec11bb4bf711b76ca111ad4703119bbc20118f87481184fb3611702244115e99be113d3fec11257e6611254e0010f37bcd10eed6d510e700d310db889710dad2dc10d873ca10d135ce10cff68310ac5f9710a88d2310a277e9109a1293108e65b31087324d10820c5c107e4d96107d5753107997fe105c60a2105673cd1048456e10303acc102cb63c101c644a100efcf40ffe803e0fdbada40fd9ce270fd52ea90fd50bd70fbd6be50fbc07b20fbaa0550faeec0a0fa2bffd0f9b96400f8623c20f84c5f80f75b8d90f70758a0f69b4ab0f6278f80f53a2330f501bb10f43d4140f2d340a0f1881da0f1251ac0f0bf1ed0ed859a40ebdd8100ea28d790ea24b6e0e7994b70e719cfa0e640f920e59297c0e4a5b1e0e3fa0720e2f42500e12de4d0e00eb280de5921b0de204dd0ddabdf40dcd20c90dc905490dc4ebc80db0367e0dadda5a0d8698c70d7b3c1b0d79c59d0d5fb3380d5f8eee0d5905640d3e9e790d2e6d950d1edd1f0cf2c0e90ce7df030ce5ab4d0ce4cabb0ce471460cdf24320ccedbe10ccebb6f0ccaae820cc67ccb0cb159640ca56c4e0ca5020f0c9bf91b0c8c5bbe0c8b27250c8963610c84ea8b0c817c8d0c7797840c75d7660c4de82b0c406d980c2f78620c2cfc700c1fd0cf0c1be7930bf325510bf24aad0bef499c0be565f90be096960bdf7d980bce7c580bc9441f0bc647fc0bb965ac0bb89b570bb7be010bb5c2880ba8ee5c0b8de77e0b72743b0b6acdbf0b69fd020b657dad0b5bf4f20b3455a40b330d610b2c7ec70afcd18b0ae8a9c90ae722550adb5f520ad7c5720ac27fd50abd12b90a8d4ab60a84dace0a8169070a79f8ad0a5b06ae0a40e3c50a2c43d80a206b680a1ff51a0a14b4d50a118fa50a10ad5109f4b61609eb18e009e3aa2209df062109d8050809cea75009bc75b30987af340971c0db095c4501095553de0937d28609339858091e4e050913030c090519b408f1313608ec609f08ebb33008e26abb08c952a508c687fc08c6594708bc1d7108b3092c08a2045d08a13328089e9c19089df71808969d450880db28086f2566086a5ec30863f7aa0833e4a20832831c08305137082cd47f082bb64f08285d07082551050815354f07e6a6df07e20b4b07ded3f507d90cb707cf36f507a9accd07a1087007862240077cbc7d07735bb6076ce6d8076b3a7c075fc0b1075130d0074c063707464b35073326c50730cced07158c1606fbf27006dbb6d606d6ca4606d3e86c06d3000c06bd889306b668c406ad3a9706a5b2a306a091a4068eb4ae068d6da5068a6d76068a0612067f16420650a7540645b3360635db55063325fc062e95ee062882980627f2a9061e9c1d060cb72a0600b26e05f2087705e5df2e05e029cc05b4a78005b3078b05ac6dfd05904b3305829c5a058164d5057224cf056bcc39055b138a0551466405424b8f05301047052cecc8052c043005240c2f051d6e39050aca2805046f0a04eea17a04d8ee6204d22c4704d1363004d0ecf604bcc9960493b9f6049123e104797369046c49560465713a045c110b0445ec390445709b04438f790427a95b0423f3030413709703da75ae03cf7ee703ad2c4503ac0680039c06e30389f1d50381c2f703791668035fc5c303507e19034e6b5c034c0ae30329e1d30312dc4403006f6402f13adc02d08d5a02c9862102c1fa0f02bf056a02a2af6e0278b369026d7845026519b0024cf2c5024197b50227cece0222cec20219220e021600a50214e56a0212d6a601f5e29901e39a7c01e0b67901e0ae2401dbe19d01d489b901b68b3401aad28901a87312017e6add01796d6e01749eca016368bd015d01c30154a02b014b6c1c014a3383014402b9013b534c011d4ada011a7a5701179ebe0108249c00fded9100f19d8b00eaf9f700d0f18700cca869009b69340098771c009246a3008f7861008dba7d00746c4c004c92de004b2d2000437e4e003b042900394d1a002e995c0008b346
  | 9 => 0xfffe92fcffd0c239ffc2d8e1ff8d4354ff84290aff441679ff41ab84feeaf29dfeeabb0ffec8dd43fea1e259fe5e92bafe2fc725fe29ee5bfe08abecfdc2e29bfd7e5d5dfd70f94dfd654de4fd013f10fccaafb2fc92114ffc7f7c80fc6e8ac4fc637424fc3cd8fffc3c9e99fc230823fbd55457fb9d35cffb783888fb1e3e82fb0d6534fae44f65fac19bbdfaae6b75f9c6b33cf9c57854f983c1a5f969de3af95fd4f7f913dc39f90abee3f8923a3ef8740bb8f867996af8430e0ef83d1429f827b7fff81ba0c7f7e5bcd7f7e526a6f7cd99c7f7af42b6f7ab790cf788cb89f6f78d39f6c1a949f6c1a628f6a30bf8f69c0319f6965a59f6844210f66392c0f654c67af64e5e20f63c79c9f63c5bb3f631402ff61bdc91f61a0eb3f5a24060f59e69f5f57080b5f53b450ff50cc289f4f38d93f4e76c3bf4d5010ff4bda9a3f48e3a04f480e2d4f480d7b6f4706208f4593d3ef4188e7bf3e4c9f6f39e4954f38c17dcf3773878f366d04ff3559dbbf32e4be2f31a06cef31753aaf31265b1f2d991c2f2b786a7f2a64278f2a317a1f2917e7df280d061f268044ef25ae26ff24dc53af24227a8f23283f9f1f4b925f1f15783f1d2f6a8f1b57e34f1aacc8bf1a33b32f17f357bf1582116f142330bf12cf172f1070404f0eb3434f0e6d26ef0c19d4ef0bd53b9f093bb05f0833786f075aa7cf07051d4f066a9adf06404a8f056cb5cf04e5e96f047e5f8f03b129df02693bdf0155a44efd12f7fefb17e8eef962a46ef8ba102ef404f59ef324309eefb7622eeecaaf9ee87bf80ee855bd7ee809807ee5500f7ee2969e7ee2844e8edff3011ede5d333edde936dedd39901edd18342ed8252b1ece91c44ebd06a96eb528f29eb4ad429eb110597ea8deeb2ea7da627ea460bcdea430ce4ea2fdd44ea092bc3e9ffbe66e9f60567e99b0034e94e37d9e927ed8de91d0789e9065e79e8e4f184e8d7082ce885d5d9e87e1b13e862139fe8027e24e7ddaf2ee7ceff99e7c32729e7a0cea6e792e54ee7843e24e76947b7e73fe43ce731ab3de72d56c9e719491de6f6dca8e6f3d270e6cd59bde6a7c56be676b753e664f2f8e609433be5db4ca7e5cc967ee5babd00e5acd3a8e595f812e58f25f0e5813c98e542163ae539f860e4fdd19ae45649d7e4054395e3c910cde3a231c8e36eaa5ce346a5d5e3400571e2d6a01de293e1b1e2743734e268c8b0e232e4c0e19eadcde1875b85e18681ffe184fb77e1509e0fe07df737e0477d16e0435893e042a79cdfbe3865dfa9712fdf900796df714015df59e3a9df532a6adf2db5a4df1d467adf122fdadee69880de502d06de35c45ede1062edde06e962ddeed5cfddd93fc5dd55e403dd49a024dd3dfb12dd26b9abdcf6f914dcf4e1f9dce6f8a1dcd9e0e9dcd90f49dcaab3aedc73d4f5dc4472fadc3e5a20dbc7a452dbb91d76db5e43d8dad8bc77dac3a17fda60958fda5dc83cda43479ada25d346da111b65d9ee5266d99766d1d948254dd9027302d8eff3f6d8e4f8aed8cfc0b7d8b52804d8798daed86a6ab7d85343f3d833cb3bd803cfbcd8018becd7f051b8d7ecd013d7be99c4d794a5e6d79418bbd764e346d6fb9ec2d6f2c2b8d6d72d24d6b7f40fd66d324dd66319a9d652919bd6419b3dd62eff47d6187370d5fea674d5ec7966d5e12930d5c8c284d5b5ff45d5ae9fdad52e63d8d4ef6c74d4d5f729d4c865d8d4c446c4d4a01339d466be74d4551aafd4431cbad41a68b8d4119118d3dbad28d3c88e34d3a8345bd3a21dfdd39cf724d3913b50d2f59345d2c46632d293fd57d28ce2ccd2590860d1d9096dd1afd519d190f48ed17a7eb2d16f1d89d15fd5d3d13c89f0d138a81dd11a8e07d110f2e0d0bc976fd0b91ae0d0983801d07db433d077e979d066f257d04c5269d0466e3ed0310e67d023052ecfe69399cf9d3252cf93e824cf822afbcf82082dcf681144cf303d0ecf26d61dcecf8213cececadfce9a7613ce8db32cce7f07e7ce75e69cce6e3cc0ce651689ce64e06cce4f734ace41fbf0cda75746cd996deecd91bbedcd8f554acd78f24fcd372e02ccda05d9cca62649cc8400c5cbd7696ccb9c67ebcb8d9603cb65edcacb24e352cb0a7abdcb02b32dcaf4c9d5cae71dcacacb1f20cab139dacab043b1ca79c990ca78545dca511422ca11573bca0a9de7ca0a28ceca050934c9e8d86fc9dadd1ac99c9beac98c3023c9894ba6c9876f14c96edd38c956d6e7c94ee609c918e4fac8ed43adc8c4e765c8bfec4dc8bda07ac8b3e94ec88e6d44c88a085dc879f884c876aee9c87454b7c86c3849c868c591c8685b3bc812b409c7f8f564c7c5c42ec7b580dac7b20e72c7a4251ac7a0d3d7c793734bc788307dc76055e1c75dda5bc72d88aec716ee05c6f84241c6e94407c6ccc95dc6c095f2c6bb68f2c67f5e2bc65794dfc6522a5dc62ca263c6010b53c5ec8fd2c5a50ec5c59cd431c59c70a1c5936bf6c59048e2c57a9fe3c567d4e6c56540b8c5105c76c4f93d08c4cda5f8c4c28bdcc49a4329c495db37c44f9dc9c43f6c4ac436ad58c4306362c3e7ad2bc3dec8a9c3b270bac37ddd48c327f5d9c3274742c323471ac2fc5ec9c2f16352c2b2cccbc2a68de3c27af6d3c2074947c17ac58ac15c9f7bc08b2d71c062b08bc039a14fc03744c1c020b2a4c01f7050bf78a859bf575a9ebf432e92bf09cd61beec8fbfbe97be57be830634be60fce4be59cc93be074675bde5383dbd9b75d3bd66c75cbd58de04bd384d99bd240309bce081e9bcd57874bccd90efbcbfa797bc9e8f99bc73e788bc4c817abc4b25e3bc4762aebc18fa0ebbed62febbb55c91bbb5287abb9e662cbb94cea1bb7b2f1cbb49cbe0ba7dec25ba621ad2ba54317aba0cc9d6b9f8d3ccb9d64fb5b9600000b9538b78b9292436b9108461b90e8384b8e8b648b8cdd997b8c948c7b8c65605b88ab9ceb8756b1fb86483bfb855a56bb84c5d58b841a774b7db6eebb7d1a24fb79ab181b7908d52b7376aa9b71e23d5b6efe81db6e4b6a2b6e0fe78b684801db67f2169b5e98fd4b5bfdfa6b59492e3b58b4a6db55fb35db5074923b4fd6b9ab47eeff4b45e7f24b4356a9bb427397fb41b24e9b3f87bd9b3f0bf5eb3d5a959b3cf7f13b3cacb3ab3ba9b09b37c3873b3531f07b349743ab34535afb333db62b3120f4eb30325f1b2e4a6a0b2d3f18eb2cbe445b2a6cfc8b2956a24b28fdac8b26f3aebb238fd44b22fc89db1e7cd54b1e269b7b1c80e6eb1b64156b1a7d0b7b17fc735b169d167b148e0deb134858eb12242bdb0ff264bb0922dc8b079a500b01ee29faffc7108aff30d8dafe535c2afc4e254afb68ca6afa3d111af8aae1daf8192caae95b038ae8e2e22ae7e927aae37caf6ae193ca9adcac7fead80063cad0fd414ac823e06ac75c8dcac6f2851ac3b768dac05929dab899db2ab7b21e9ab78d2eeab749890ab14901fab021960aadb6223aacc9273aacb9f3faa472576aa2e14c9aa10ab55a9ed285ca9e1a184a9de05d2a9d8c4d0a9befd05a9b4342aa97f6d98a96abaa9a92311e8a9114209a8e8944ca8e5aaf9a8db5e19a8b7f669a8afc709a8afc6bfa8a8dc8aa893495ea86fec06a856be4da84f5ddfa823f3d5a7f45ce8a7ef6037a7da062ca7cbeecfa7abeda2a792583ca78abd68a76a9a13a754f9dfa751cd20a73c6d9ea71f1242a6f96788a6cbad9da6a7ed12a6a63402a690c4eca64310fda607478ca5e3e7c2a5cf3a71a5c1ebd9a57f3dc7a530179aa51f474ba51e7e76a4db5d4ea4c08746a4bad7b6a4b7f86fa49ad217a481b91ea459f1bfa456220ea4427e2da4059454a3e7b97ba3cf3304a3a39bf4a378342da377ab0ea36acd46a2fb9541a2a3104da28dd856a25ca8cba1f76099a1aca34ca160f03ba1445379a11038f5a10b73f4a0f81fe1a0961dbea04b6702a03d7daaa0158312a00799ba9f2eb1fb9f2e6c9a9ef837da9ed4ebf79e7461689e67e4ee9e104b809e0a9e6d9dd8acbf9d9753449d921ab79d7bc0b49d6be93a9d643cb79d3f76529d190c2e9cf59b3a9cdcd43e9cd238819cb190319ca63fe59c9a0aa99c40b3719c36c57d9c069ec79c03693f9bec78189bbbde179badf4bf9b9064689b5ec3229b548f379b4d2c8f9b21228e9b1f81119b0957fd9b084f419afb6ea59aee561e9ad400359ad2eb999ab5a2c19a3ac9c89a036de899e8e19399b26772996932eb98edcaf998c4ce0598b2f928985182dc9822f80b97f760fb97efcf8397cf53ab97bedb2697a2ffee975bc96e9730325e96c7203896c0ce5f96b1962796a80e6696a6cbd99678fafa9602ba2795c1246e95bbea2c954f4149951cfdb694dea293949dccfd94944d5f946cfa9894529a5e94412088942feb70942031dd93d08de093c5046a93b206ae9359aa1f932bcdfd9296efea92919f0f9290e954926e6a70926607ff92581b669239a3039226b2c4920a3f2c91e13b2e91dbf57791803ae4917eaf199173987991480169911a67c99104c5b690fddc4f90e18fe190c7f85f90c057e090aee9f29075e3ec901d29d0901a260a900e2a5d8ff5b6ea8fb9365a8f9947038f96d3288f938c1f8f863aa78f80aa538f5e04268f5d1d048f4f33ac8f278a058ec7f8268ec1d4968e7097b88e5938368e4628fc8e39f0988e2354468dc6a56f8db31ff38db0e2c58dac31a78d1b08ec8cd846d98cb6100b8c9555888c728b0f8c6e53648c5edb678c35f0f28c2861468bd60b928bcd33f28bbbcd4a8bb0b00b8b9750028b7141fa8b6988b38b3ac7d98b1ab71a8b1735d58b08937b8afe2a548afdf6d18ad2af8b8ac77cb08ab1155c8a4d2e6c8a0c4f2c8a0192e689d9e34389c9af4b89b15c15897bd9e4896d42548966981a8936c833891729318906909e88e51f0d88adbd72889fd41a889f39bc88999333884f19e588492ec6882f04fa882a2b238804a05287ec81ff87d5e39d87bc6fc287b2c2f18789cb89874661ab873dab0787017bd886f809b186f2b68286e21aa886b68398869466b9868b24ed86790a9086663b9e86452f20863d15c785f5139485c6847685a51c4785976148856a3008856540cf852f1fe28518705184cb850584a398d68481be598470c2c6844ad5588448c12c8436f91d8436097c83ab7b4b83702fcb8361c6b58353c2cb834d6af083272c4582927706828df5d8825a8cdc8253516981a3ebf0812225e081206b3680c6240580bd4c6580876875804952fe802415f8800f92517fee32087fbc3db17fab234a7f32dffa7ef576017ed019777e871ba27e7fceb47e65e2c97e312d017e1c3fa17e132f507e0e56497dd78ac07dcd96637dca24f67db89fdb7d82bbeb7d79a2077d6aee387d12a2797d11b7a87ced0a237ceb60657ce4bd2b7cc1e7d17c92092d7c66721d7c2dc37a7c2b9dc07c22f46e7c19301c7be9085d7ba664e67ba5e4f37ba09a4d7b948d0d7b7b3d607b7a4de37b3bae457b24a24c7b0ca52a7b06f87d7aeb70fc7ae206f37adee9f47adb616d7a1a497d79e4763479ba88a779ab2c0f79983ba7798ef197796032bf7959c9567930a2d5792916f07901693c78c8e55e78aba608789912fb787690d6786a7e37785bae4d7814032e77cbe74077c6aff2777a038b76e27d7176cc6c4376bb8ea676ac035076a9a41076a337f576958dc97673c020760dbfdb7609e6ae760036c075f8252475ded1e475c9bc9f75be69e37552cbf1754b1eba74dc233274913e487468d809742f8a6273ccdf2b73cc2e2673be44ce73ba6a3d7396650a736cf9b7736ae9eb734162a773182d6a72e009ec72df6b2572ddca1572d8238c72d2209472a8cb9d72411d767239a86c72358074723433237233341e721a1b2571fa2efe719f89377167950b70f4ada070e6c44870a4cbf770630e8d6fd2fd816fcf02676fa2a86a6f35cbfa6eceb4ee6e2c9f9c6d88d7156d60da256d5de8e26d4109d36d3845d36ce87cbe6cca55dd6cbbeb986cb45e966c7873e66c2a10d56c185a886c0a70726b53f4776b17c7426b026b186ad6d4086aa27e626a8d2d196a785b356a41e1146a3a5876699e0c91695447a7694fabea691fa2d5691931c968e5ba4868e0fc7e68d96c1a68aa286868972fbe688b45d968866c686863860c6854cbb8684aa03068470f4568435559682b985c67b84d3367a955b6677849de6767324b67504801672cf9f9671f7e7c6702ec6766f3e72266ec05af66ebba0b664b3478662798b6661af64b661a18ba65d6171c65d358d565bb5a1265ac238865a7972d656332a5654c3e98651d8f20651cdac164f4880e64f143b164e0a71864aa2cf76491f43e647ea3736410c20363f6bd3063c1858763bc938a63a1ec0b6395ee7763927f396379509d6374dfbb636c081b63494861633755946336242b6319775262f392c362abe29862a10d4762804b88623c9011622f6dfe622ea6b96229812961eebd5c61d9ff5a61b893e461a722ed612fa55a60f0fdb760eddb2060d850b460c76deb60580ddd604eeeaa604d5ea960024fac5fe44d615f73b5585f6b17f85f60d28b5f4dfb165f3623605f2a586a5f21ef265f1263205f0bfa805f027ed45edc7f305e8f7dac5e8e25045e895a9f5e66fb3c5e61d6dc5e5fdd065e59359a5e3cbefd5e29f9165e2937ea5e1a07145df4ee975dc973d45dc2ea665db3a3f25d9d36655d59926c5d39a10e5d37c0635d33ba4f5d2f352f5d0326ed5cff94765cfe49ef5c937b515c767a905c6556f35c56ffba5c4916625c38bf575c158d805bf7baa25bee4d455bcc23925bb1da195ba242575b89787a5b489f285b3cc6b85b112fa85b0468ce5afbaa805af4c4855aedc1285aa3a77d5a82da355a69aaa15a3a00345a118dda59ff5bc559e6079159d81e3959d0541b59c7a3cc59bd8e7859bced1d591dce01590a825958e3a12e588ef96d585e51ea583b3d1458205f8d57e6c62b57a0fc03576a81e256d8010e56d1ad3f56bf8ac2567ce875563f4c8156099d4c55d7355455635ce3552b5db054c5831e54909e53547a7caf5478e8cf545fae90543e138953e33c6d53a4dd1c539cd3d3536ee7fa5351ef4f534e87c15331df9b5323f64352ef055e52d86dc252c033ab52ba8d2252b8b8e252b3a20d52b302d9527dbe1d5276ebb1526902595219cc6c51f6271151afe4d851669303515e9f9a5157f3c6513966ff50cd5c965087358d504d42c5504a61455024533d4ff8bc2d4fc2cf7c4fae564f4fac55584f2dcf014ed89ff54e61e6794e61b0754e565a074e4b88504e2419224e08b7594decbd6b4dd3b92b4dbf92e54dbe5d014d7193084d5b5f3e4d0f18b44d0975074cf9bc8a4ce6f0e84cc4947b4cb716854c3d48a44c1830bb4c04427b4bce5e8b4bae1fcd4ade82d54ab2ebc54a987cde4a8e81304a7fcda64a7ab7d74a64d0ee4a5436964a41f1a24a2a6b344a196abc49e8c96749bd325749adfa74497072cf493e46fa49389c1a49097bb448cf1bc148cbb3c348a384b148a07c08489f5a8448920a6b485b60e247f3d8c547d8ccaa47abb2ee4786c8f74775cefe4774b990476a0cda475e78364752eaae47508ede47500c774732b19747309dae47142c3346dfebcc46c2337646a4824646985c2e467d77704677acb6466e4b86460a024c45d0191745b8d6f945b3de6f4567d48145459c3b452f94fb44ad892b44ac806944a3340a4481362a44712ab14447973f4417214c44095a6543faeffe43e454e8437dd9ec432960fe42c3acc542b7312242ae7574425cde144218a7ce42153f07420abe7641ee23ec41c5580f419afd7a4184c7914172c4aa4163496a414b6f95413fb0cf413ce0ba410bdd3b40ff4b6b40d6976940b52b4e4084bce5407eb12d4053a56840280e584008e81b3fa9c8ea3fa6e7e43f9117c03f7108703f1dcc973ef805bb3ef47d203ed885a63ecd9bf53ec7a31f3eb3ac8b3e48cd433df8b8a13def0c143dc7c7d23d8d181a3d8af6ca3d5f5fba3d547ca93d43d8383d34182a3d2bf8a83d28e5993d17f7f63ce33bbf3cc8e51d3c66e33c3c3fa3013c3b4c2c3c30b5a53c2faeb03c1ff73b3c1b28ed3bf398133bc801033ba096323b7cebf23b6d8fe33b67c5293b56c2dc3b1ca6bb3b15f87d3ad459763a62e3963a57ecf43a4d3d843a4d17a33a48b9ca3a374c8639f3f77039c4389339beb687392f915f391824e638b5e6ec389acd1f3868e3593810ed8337b90bd937ac241b37a54bb6379d3ef5378dca61377fe1093753406a372346f73722b32f36eccf3f364a741536368ef53600ab0535b3a8dc35a13e5f3597a27f3588d2793584f29e358401b0356c496a3561be8f350be8b734e0516234c51bc334b7326b348ea1a23480b84a346698eb345b5265344b32a934154eb933a3c4fe33a108353396ec5433931edd332dbd0c331fd3b43317da50330a8e9132e8d11432e0452632cb1d1b32b53cc832932a44324f9aa7322c4f8e321ba4af31ef1ac531e0a42a31a9498231a7060a319d088f318f1f37317ffede3159e78e3108199430f47ff030caaf3f309f187430847aac3055937a3044449f3026790230051e112fec4d932fe4248a2fbba9be2f52b0b02f2efc202f0923a42e9a34122e7f3dd22e46e2562dddec942dd85e622dc61a732d9a74be2d3aee052d1895b02cd5d4472c38c08d2ba083f42b421a572b0253372af8728b2a6c79062a2bdd582a287f5d2a200c8629f7856d29ea9d2d29d51b1a29d2bb8229be305929901ca9295abe4a290aa9f628d528bf2857398b2845478928403fae27f8388527ecb4f127d81eb327d05d9927ac87a32737272c26fb7e8b26f5d80226d5708e26ca40f226346931261c2eb1259b9b952593151a25779110255d312a254844f7254116ef24fdd62524cbb10f24c2806d24ac064924a958812496e95d24833e5c24537d8223e0325923d7ae8823d619b5235ce8ab2350f730230f975122d2ecf722aca27e229c72d622952a79228a8d31224f7ddc224af6da221c69892208f3e021f156c421c70ee321aed969213b8e4021038c2f20e4a67620a0b9e22086f9eb2074decc2071c5aa20606f3620510615204c2fc62046e8b320106e921fad84c31faad9c31f85e0a71f85099f1f82483c1f77a0d31f4bce1b1f439d491f22d5251f1243ac1f11ace31f10b7991f045a541ef701a11ef055cd1eb337c11eaf89fc1e98e5651e9830fb1e8f6c761e5e34ae1e522f891e41fba81e2ffcfb1e2213a31e1c4b991e1680df1df9f8ef1deee1191deae9851dbcb5441d8b262c1d6f81b01d4669541d3e47d41d3c8c9a1d304db71d2287fc1d1ed57f1d06a8aa1cad89191cab1b9f1c5a35081bfca5661beebc0e1b6dfc771b4265671b1dfbd81b1027f11b0255561ae9772f1a7f3e8e1a6b75be1a6a113b1a454d2c1a19b61c19c2a69e198598391980e71b195928f21955500b1910208419007cde18ea43be18ad03af1876e4dc1864e94817ffafc417fa7d951766795717550a0a168864a416608b0b165280b4161ad3ea15d6485a15cd70ba15aab14a15978cca15370126153131981500870514fb033a14f38bce14e86e7e14a4cb1c149dcab9146ef1df14675098145cacf51412ed981407679413e5ef78139fa26f1380a8511379b72b13687b1e135f8fde13066c0212dd0c3712c200b112a82170129a3818123c85731232549c121c0b48121519a3120eedf211fbda7b11f8dbb911d8de1311bf55c8117f72251175b785117188cd115976d41146559f113de7cf112c7351110e410e10eed6d510bb0c1410ad22bc109af5e5108b61b5105d9b46105c60a2105673cd10561395102adcbd101553f60fc4b8f90faeec0a0f1251ac0f0bf1ed0f0acb1a0f0a41680ee272480ebf3ac50ea28d790e2f42500e230a100e03ab400df56b8a0dec076f0db322070d63e58b0d5fb3380d3e9e790d2014e00d106d530d0283fb0cdf24320caf1ab30c8c5bbe0c84ea8b0c4e429c0c44fc1a0c3dce2f0be096960bc0d1c90b3d91760b2358d10b1f0a850aecdeb00ae8a9c90ab4fd3f0aa37a530a94109c0a935dbb0a7f194f0a7caeeb0a206b680a0a769a09ff454309cf702509b7561909b1c9eb098bfa1a091869a308ed297408cb31df08969d45086b06350832831c082c4569080fdb3307fb459d07cbf9cd079098c6078d58f30782af6e077e725607779aea07735bb606dfd59306b9d1df06b485f90640e91d06257454061b6f6005be5fe7059eec93059ee30a059a1aa60572ee3a056f2cd705696749055b7df1053948e7052c043004f4794704df26bc04d8ee6204d57de90483e4560459a3100431938c03d3a4530363edb9035cabcb035a96bd02f13adc02e811ff024197b50231e772016d8161013b534c00eaf9f700dfa3ec00cca86900b5f2a4004c92de002e995c002d1dd2001a8bd3
  | 10 => 0xf1aacc8bee809807ee5500f7e5babd00e5acd3a8d66d324dd3c88e34d13c89f0d077e979c62ca263c5936bf6c327f5d9bc18fa0ea9114209a8db5e19a481b91ea3cf33049822f80b9173987986e21aa87c92092d7ba5e4f37b06f87d79ba88a76b026b18651cdac163c1858762abe2985bf7baa25b3cc6b85024533d4ade82d54053a5683d8af6ca3d547ca93c66e33c3bf398133a62e39627d81eb326f5d80224c2806d1b6dfc771a454d2c1980e71b15d6485a105673cd0e2f425008969d45
  | 11 => 0xee809807
  | _ => 0

def LT : Nat → Nat
  | 5 => 0x55555555555555555555555555555555555555555555555555
  | 6 => 0x66666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666666676666666666666666666666666666666666666666666666666666666666666666666666666666676666666666666666666666
  | 7 => 0x777776777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777776777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776777777777777777777777777777777777777777677777777777777777787777777777777777777677777777777777777777777777777777777777777777777777777776777777777777777777777777777777777777777777777777777777777777777677777777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776777777777767777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776777777777777777767777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777777676777777777777777777777777777777777777777777777777777777777776777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777877777777777777777777777777777777767777777777777777777777777777778777777777777777777777777777777777777777767677777777777777777777667777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777777777777777767777777777777777777777777777777777777777777777777777777777777777777777777777777777677777777777777776777777777777777777777777777777777777777777777767777777777777777777777777777777777777677777777677777777777777777777777777777777777777777777777776767777777777777777777777777767777777767777777777777777777767777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777767777777777777777777777777777777777777677787777777777777777777777777777777777777777777777767777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776777777777777777777777777777777777777777777777677777777777777777777777677777777777776777777777777777777777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777767777777777777777777777767767777777777777777777777677777777777777777777777777777777777777777777777677777777777777777777777777777777777777777777677777776777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777776777677777777777777777777777777677777777777777777777776777777777777677777777777777777777777777777777777776777777777777777777777777777777776777777777777777777777777
  | 8 => 0x888888788888888888888888888888888888888888878878878888888888888888888788888888888888788888888888887888888888888888888788888888888888888878888888887888888888888888888888888888888788888889887887888788888878888888888888888888888888888888888877888888788878888888888778888888878887788888888888887888888888788888888888888887888788888888888888888888788888888888888888888788888878888888888888888888888888888888888888888888888888888888888888888888888878888888888788888888888888888888888888788788888878887888888888888888888888888888888888888888888888888888888888889888888888888888888788888788888888888788888888888888888888888888888878788788878888888888888888888888878878888888888889888788888888888888888888878788888888888888888887888888889888888888888888888888888888888888888987888888888888888888888888888887888888888888888888888888888888878888888888888888888888888887888888888888888888888887888888887888888888888888878888888888888888888888888888888888888888888888888888888888888878888788888888888888888888888888888888888887888888888888888888887788888788888888888878878888888888788878788887888888888888888878888888888888888888888888888878888888888888888888888888788888888888888878888888888887888888888888888888888888888787887778888888887888888888888888888888878788888888788888888888888788888878888888888888888888888888888888788888888888888888888888888888887888888888888888888888888888788888888888888888888888888888888888888888888888877887888888788888887788888888888888888888878888888888888887888878788888888888787888888888888888888888878888888888878887888887888888887898888888888888888978888888888888888888888888888888888887888788888888888788888888888888888888887878888888888888888888888887888888888888888888888788888888888878888888888888888888888888888888888888788888888888888888888888887888888888888888788888888888878888888888888888888888788888888878888888888888888887888888888887888878888888888888888888888888888888888888888888888788888888888888888888788888788888887888888888878878888888888888888878888878888788888888888888888887888878888888888888888888788888888888888888888888888878888888888888888888888888788888888888887888888888888788878788888788888888888888888788888888888888888888788888888888888878888888888888887888788888888888878888888888888888888888888888788888888888887888888888887888888888888888888888888887888888888888888888888888888887888888888888888888888888889888878888877888888888888888887878888888888888888888888888888888878888888888888888888888888888888788888888878888888788888888888887888888888888888888888778888878888888888888888888888888888788888888888888788888888888888888887888888888888888888888888888888888887888888888888888888888888888888888888888888888888888888878888878888888888888888888888888888888888888888888888888887888888888888888888888888788888888888888888888888888888878878888888888888887888878788887888887788887988888888888878888888888888888888878888788887878888888888888888877888888888878888888888888888888888888888888888878888788788888898888888878888888888888888888888788888788888788888888888888888888888888888888888888888888788888888878888888888888888878888888888878888888888888888888888888888788888888888888878888888888878888887888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888887888888888888888887887888878878888888887888888888888888888888888888888888888888888888888888888888888887898888888888888888888888888888898888888888888888888888888788888888888888888888888888778888878888887887887888888887888888888888788888887888888888888888888888887888888888888888888888887888888888888888888888888888888888888888788888888888888888888878888888888888888788888888888888788888888888878888878888888888888888888887878888788888888888888888888888878887888888788888888888888888888888888888887888888898888888888888888887788888888888888887888888888888888888888888888888888878888888888888888888888777888888888788888888887888888888878888888888888888888887888888888888888887888888888898888888888888888888887888888888888788888888888888888888888888888788888888888888888888888888888888888888888888888888888888888888888888888888788888888888888888888888888888888888888878888888888888888888878888888878888888887888888888888888888888888888888887888888888888888888888888888888888888888888888887888888888888888888888888888888888888888888888878888888888788888888888887888878888888888888887888888888888888888887888888888787888888888888787888788888888888788888788888888888888888887888888888888888888888888888887787888889888888888888888888888888888888878888888888888888888888888888887888888888888888888888888888888888888888888888887888888878888888887878888888888888887888888878878888888888788888888888888888888888888888888888888888888887888888888887888888887888888888888888888888788888888888888888878888888887888788888888878888888888888888888888888888788888888888888888888888888888888888888888888887888888888888888888888887888878888888888888888788888888888888888888888887888878888888888888888888878888888888888888788888888888888888888888888888888888888888888888888888888888888888888887888888888788878888888788888888888888888888888888888788888888888888888788888878889888878888778888888888888888888878888888788888888888888887888888888888888888888878888788888888888888888888888888888888888887888888888888888888888888888888878878888888888888888878888888888878888888888888888888888888888888888888888888888888888788888888888788888888888888888788888888888888888888888888888
  | 9 => 0x8999988999999999999989998999999999899889898998999999999999898797998999899998999999889889999999999899999999999998999998999999898999999999988999897899799899999999978899989999999999999999999999989999998899998999899999989999999999989889999898988999999999999899999899999979999999999998899889899887899999999999998999889988999999999889988989989989999989999989998898899989988979999999989999999989889999999998999999999999999979999799999898999998979998989997899899999999899998899999898999999898999999999999979889899989899999997999998988999879999979999899989999999999998999999999999999999999999999998999899987898999999999997899998998998989999989989998999999899999989999999999989989889998899899898999889999999999999999999999999879989899899999999999999998989999999999899999899989989999999999898999998889999999989899799999997989989989999899989999998989999998997998989989999999999999999999997999999999899998989999999898989999878899999989898989899899998989989998999899899997998999989989999899899999989799789899898989999899999998989999997999999979889899999899999999999999999999999979899898899999999999899889989898999899889979999897989989899999988899999899999988999999999989898999999999999999899999999899999979999989799999988999988999898999999999899999999899888979897999989999899999999999999999978999998999998988999999998999899899998999889999878999897989999999999999979898999989989999889999898899999989999998989999999998989899988989989989898999989987999998989989999898989999988999899899999999979999999979999999999999999999999998979999999899999999998999999798898989998799898998899999989998899989999998988998998898999989998999999989999989999999999998998989998997999899998988998999999989999999989988899999989998989989999999989989999899998999999998999799999999989999988999988899998899999988999898899989999979999998999999999898999999999899999999999999989989999999989799889898899
  | 10 => 0x878888888888888888888888888888888888888888888888
  | 11 => 0x7
  | _ => 0

def DT : Nat → Nat
  | 5 => 0x2063dd60c8b460000000000003d47528b4bc118000000000007ccf51169782300000000000106e0b2dd230300000000000021939b6aa4606000000000000432818c808c093000000000007a8d551691818000000000001031fd92923024c000000000016b2624b046060000000000003dd736c811697800000000000640c5116a052f0000000000010ca0630623030000000000001903064928b48c0000000000040c7368b494918000000000007b88b4bc0c0126000000000010f5ea22d23030000000000001eeba945a5e085000000000003e67ba8b4bc09300000000000864e6d9017823000000000000c516ea624b030000000000002063d445a46060000000000003fb7365e094918000000000007cce6d1697823000000000000f519022d2f046000000000001ec22d2f04d849800000000003735baa79310c0000000000007f6f50bc11818000000000000f75cda2d2f04a400000000002063fb230428600000000000043d60c8b48c0c0000000000006e6b754d17829800000000000f75ea22d2f0300000000000020630645a460600000000000036b45a5e0a613600000000000640c5124a2d12600000000000f75d4b0645a5e00000000000219306492460600000000000039b6408b4bc11800000000000628c1924a2d180000000000010b52c11818024c000000000021935540a460600000000000037366aca91697800000000000864f50bc118180000000000010f61911818024c0000000000218978230300498000000000040c7bac8116893000000000007a8c511697818000000000000dcd6ea2d3be53000000000001fdb732f05309b000000000003735ba9fd31118
  | 6 => 0x6e6b75169d732a30000000000ed916978252460498000000021940e6ac46060093000000003735ba9c8bc12e1c2000000006e6d2d1699523036c00000000dcd90ac345a6208c000000001d4b6b45a5e08c10a000000003fb6e671094918126000000007bec4d1697818024c000000010d1b9a932f053060000000001b9b4b45a75cca8c0000000003735ba8b4dc99523000000000864dad9017823024c00000001035aa25023030049800000001b9b1f45a6208c093000000004346e68b4bc14c26c000000007baee124a2d18024c00000000fd16ea2d35e6548c000000001fdb3e5ba8148c0c0000000003fb6d65e094918126000000006e6b75281af32a46000000000f99b5a2d2f046049800000001cdb3e5ba8b48c0c00000000039c628c1d16978180000000006e6c5161a2d2f04a400000000f55d4b9b45a5e08c000000001b9add45a6d4ca91800000000373650c511697812600000000864f58bc11818024c000000010396eac345a4606d80000000206add4a06548c0c0000000003dd6e6c191697818000000000818fedd4add23024c00000000f75d4b0745a5e049800000001eeba95ba8b4bc0930000000040e5ac8b48c0db126000000007b4b7549a742f024c00000000dcd6ea2d3c25e0a60000000020735560c8b48c0c0000000003aa5ba9c8bc1181c2000000006e6d512819523030000000000dcd8fa2d36046070800000001db24945a46060093000000003925ba8b4ca9181b6000000006e6b75481782984d800000000ea96ea2d2f04b870800000002193b62f046060093000000003dd7368b4bc0ec18000000000752e6d83a2d2f046000000000ea5cdadd45a5e08c000000001d12dd4e45e08c0e10000000039c67cc1d16918180000000006e6cf961a2d25246000000000b593122d2f046060000000001b9afb45a6548c0db000000003736aac818a22d126000000007e8b75169a428224c000000010ca062d623030049800000001d12dd45a5e0970e10000000036b45a7108c10a18000000000744c351697825c24c00000000dcda5a2d3ae30049800000001ed2dd45a5e0a6136000000003dd736c8516978180000000006e6cf98a30645a30000000000f816ea934d65e049800000002193be2f04a48c093000000002d64928b502918180000000006e6c8561a402f046000000000c816b24945a46049800000001fa2dd45a6bc8c093000000004325ac814bc11818000000000704c858a22d2f024c00000000dcd6ea2a23036c49800000001fdb732f04a48c10a000000003735baa8131118180000000006e6b75169cd32a36c000000010b9fa25823030049800000002073fb2f0460850c0000000003825ba8b4bc12e1c20000000081ab752811818024c00000000ea5ce30745a5e08c000000001c130d45a5e0970930000000037363e900bc1181260000000077cd558322d23030000000000dcd6ea2d31045449800000001b9add4d86208c0e1000000004326e6d5583118180000000006e6b753122d282300000000010c9b9b202f046049800000001b9b0d4d86208c0930000000035560c8b4f3918180000000007bae6d6b22d2f030000000000fd16ea5028230049800000001b9add4d69892c1180000000036b45a5e099918126000000007f6dccbc12923024c00000000b7566ac34928b48c000000001b9add45a5e0a68e9000000003735ba9c8bc14c23000000000864dad8317823030000000000b5924a2d41e46049800000001b9b0d45a5e0a6136000000003f45ba96c8c0c0126000000006e6c7d3917825c24c00000000dcd6ea5032a46060000000001b9add48c5e088093000000003216288b502978180000000006e6b75169782984b800000000fe96e978230300498000000016b24945a86c60093000000003b66288b4bc0c012600000000864f20bc11818024c00000000f75b5a2d2f04a449800000001b9add45a5e0a40e10000000037361a8b4bc148126000000006e6d2d2819523030000000000dcd77a2d2f04b870800000001fdadd5869248c0c0000000003fb77c5e08c10a1800000000081cfed6e94118024c00000000dcd6ea2d360460708000000018a2dd4ae8b4600930000000040c7baea56ea2d12600000000628c1d24a2d18024c00000000dcd86a2d360460498000000018a2dd4928b4600930000000039b6d68b4bc129230000000007e8b751694818024c00000000dcd6ea814c446060000000002073145f68b460093000000003b86e6960ca918180000000006d6c851697825c24c00000000a9124a2d25246049800000001b9add4c493c8c0c00000000042e6e6a4cec8c012600000000628b5916a052f030000000000e71aab0745a46060000000001b9b1345a6208c093000000003f45ba9892c118180000000006e6b75169e232a30000000001031d4b9b5ba8b48c000000001b9b4b45a7346d893000000004336e6a48bc0c0126000000007baee1d4a2d2f024c000000010357da502303004980000000219c022f0460600930000000040e664b75168c01260000000081cb7561a5023030000000000dcd6ea7235446070800000001b9b55628c19168c0000000003aa63e9c8bc118126000000006e6b753125723030000000000dcd9031445a5e0498000000021737351e96060093000000003735ba8b4d512e1c2000000006d68b4bc11821430000000000dcd6ea402f045449800000001fa2dd45a6c48c0e1000000003735ba8b4bc14c25a000000006e6c35169aa25c24c000000010396b25023030049800000001fa30d45a6c48c093000000003aa63e8b4bc12e12600000000864e719017823024c00000000dcd6ea462f046070800000001dc3a97368b4bc118000000003b650a5e08c0c01260000000078c8b4bc11818024c00000000dcd86a462f046049800000001eebd545a5e0600930000000036b45a5e08a8c012600000000724b752819523030000000000fedcdb145ba5e060000000001832d64928b48c0c000000000373628b3516978214000000007f6e70bc12923024c00000000ed9d4a2d2f046049800000001f33b645a5e08c0930000000039c628c1d66a2d2f0000000006e6b75391b025c24c00000000dcd7da5032a46060000000001b9b216288b4c4093000000003735ba8b4ca9181be000000006e6b751698825c384000000010c9df3142f0300498000000021937360c5e08c0c00000000037361a8b4c412e126000000006e6b75169d829830000000001031fdb0723030049800000002063fb5ba460600930000000038263e8b4bc12e126000000007f6dcd8a17821430000000000fedcdb3e5ba46060000000001fdb9c628c1cbc0c0000000003735baa3d3a1b11260000000081ab751694118024c00000000e0977a2d2f046070800000001b9add526988ec8c0000000003735ba940e699518000000000738cf983acd45a460000000010398a2dd45a36c49800000001ea36b45a5e08c0c0000000003fb7baea56e978126000000006e6c4d2017823024c00000000dcd6ea8f4c496060000000001d52dd4e46c08c0930000000040d5ba9408c0db126000000006e6b75169d734865400000000c516ea6245a5e060000000001b9add4a075cd7893000000003fb6e6cf88c10a180000000007f6ea5cdadd2f046000000000f75e722d2f030049800000001b9add4d86c4ca918000000003fb738cf98391818000000000738c818a22d2f024c00000000dcd6ea2d32a50460000000001b9b1f45a5e0a40930000000040d5ba940eb8c0126000000006e6c353917823038400000000ed9aaa2d23030049800000001db22d38846060093000000003d845a5e08c0c0126000000006e6c351697825c384000000010c9eb3062f046060000000002073fb6426c48c093000000003735ba948ca91818000000000628b7524a2d40a30000000000dcd6ea2d32a52c60000000001d52dd4e45e08c0930000000037363e8b4d811812600000000744b751698823038400000000dcda5a2d32a50460000000001b9ad645a5e09b0e1000000003a261a8b4c411812600000000770c5124a2d18024c00000000dcdaa2503ae30049800000001fa2dd45a6548c0db000000003735ba8b4de1b1230000000006e6b752819523036c00000000dcd6ea2d3bc65460000000001b9b21628900bc0930000000040e640c191697823000000000744b753917823024c00000001031b5a2d230428600000000021939b5ac5e08c0c000000000373628c1916978180000000007e8b75169d732a30000000000dcd6ea402f04b8708000000021940e6aa46060093000000003555ac8b502918180000000006e6b75281d732a30000000000dcd86a402f04b8498000000021939c60c5e08c0c0000000003825ba8b4c41181c200000000704c351698823024c00000000dcd6ea6133a46060000000002072dd5868b4a08c0000000003735ba978bc1181c2000000006e6d2d281cd18024c00000000dcd86a5e2f046049800000002063d57368b48c0c0000000003735ba8b4eb9a412600000000804b75169181b624c00000000f516b22d2f046060000000002072d645a50460093000000003145ba92516a0f12600000000868f694997818024c00000000c516eacd4928b449800000001b9b3e60c8b48c0c0000000002d64545e08c0c0126000000007e8b752f11818024c00000001031eeb0745a30049800000001c92dd45a654a08c00000000040c7bab75168c01260000000087ab591691818024c00000000dcd6ea2d3105308c000000001b5b2045a5e08c093000000003735f68b4ca9411800000000077cc818322d2f046000000000dcd8fa2d3104b8498000000020a40e5ba46060093000000004326e6c818317823000000000818e6d83a2d23030000000000f756ea2d40a5e060000000001fa2dd45a4606d8930000000032060c8b4f397823000000000818e6d6ea2d23030000000000f598a30645a5e060000000002193be6aa460600930000000040c7f6ee08c0c012600000000864ef8e211818024c00000000dcd77a2d31046070800000001fdb145ba92460093000000003dd7708b4bc0c0126000000006e6b7549a743ac24c00000000dcd6ea2d2f05309b000000001b9add44a52c60093000000003b645a5e08c10a18000000000864d54f391818024c000000010b9f02932f030049800000001b9add4fc5e08c0e1000000003f45ba8b4eb8c012600000000744b752017823038400000000e8986a402f046049800000001b9add4d86c08c0e1000000003f46968b48c0db126000000007f6dcce211821430000000000dad1697826c44049800000001b5b2145a6208c093000000003735ba8a8a08c0126000000007baea5169781d824c00000000f696ea902f04d849800000001eeba9736b75169780000000039c628c19169781800000000081cc516ea5018024c00000000dcd6ea6245a6bc8c000000001db22d2f046060093000000003fb6e6c818a17812600000000818b7561a2d23030000000000f75d4b2145a5e049800000001b9add45a758a6136000000003825ba900bc1181c200000000818e7183a2d23030000000000fedb597823042860000000001d4b9b45a5e08c0ec0000000038261a900bc118126000000006e6b752791818024c00000000dcd6ea503486548c000000002173734c49608c0c00000000033e628b7516a05180000000006e6c7d3917823038400000000dcd6ea782f046070800000001df2dd45a5e09b0e1000000003dd5ba8b507978126000000006e6b751699d2903a4000000010316b22d23030049800000002063fb5bab348c0930000000037363e8b4bc12e1c200000000752e6d90a2d2f046000000000dcd6ea7235446049800000001b9add5249ccbc093000000003fb6e65e099918126000000007c0b753125823030000000000e719030745a5e08c000000002193732f04a48c093000000002d645a814bc118180000000007f6f55cd97823030000000000dcd6ea2d2f04d070800000001ea3b645a5e08c0c00000000037361a8b4bc13412600000000736b7566a2d2f046000000000f75d4ad645a5e049800000001c0b2145a5e08c093000000003735ba900bc14c230000000006e6b754897829830000000000dcd9031460c8b4bc000000001b9b2a6188b4bc093000000003735ba8b4ca9411b6000000006e6c7d2017825c24c00000000fd17da2d23036c498000000021ebb645a46060093000000003736aac1916918180000000007e8b752819523030000000000f816ea934c45e06000000000206b5445a6bc8c093000000004326e6d558a0c01260000000087ed558322d23030000000000dad1697829846060000000001b9add4d8734d8893000000003735de900bc1181c2000000006e6b75169952303800000000103990ac345a6c48c000000001b9b1245a5e060093000000003735ba9d1311b123000000000864ef8bc11821430000000000fedcdb072f0460600000000020b3f25ba46060093000000003fb736b74bc118180000000005baa9131258230300000000010356ea2d35e6548c000000001ed30d45a5e09b0930000000036b642900bc11812600000000864b592491818024c00000000fedb9b212f04b849800000001b5b0645a5e08c0c0000000003aa63e8b4bc1181c200000000738c1d66a2d2f046000000000dad4297825246049800000001fa2dd45a7346d8930000000040c7baee1168c012600000000804b752811818024c00000000dcdaa22d35e6548c000000002193be2f04606009300000000373628c1966a2d2f0000000007beb754897818024c00000000dcd6ea723604607080000000206b5445a6548c0c0000000003735ba900d51181c2000000005ac9611291818024c00000000dcd86a4035446049800000001b9add45a6c0970e1000000003fb6e65e08c10a180000000006e6b75169d936253000000000f75dc22d40a5e060000000001fdb9c60e5e08c0c0000000003fb6e6b0cbc12923000000000818ee1cda2d23030000000000dcd86a2d31046070800000001eb35560c8b48c0c0000000003fb6e65e08a8c012600000000818ed91691818024c00000000dcd9ab1445a5e060000000001b9add4e45e08c0e1000000003f45ba9408c0c012600000000642c5124a2d18024c00000000dcd86a722f046049800000001fdb73628c18bc0c0000000003dd6d68b4bc10a180000000006e6b751697825c38400000000dcd5222d2f05309b000000001b9b0d45a5e097093000000003736a68b48c0c0126000000006e6b752018823038400000000fd1a5a5023030049800000001db22d40a5e08c0c00000000037361a900c411812600000000836fed6e97823030000000000dcd6ea913b03004980000000206add45a6bc8c0930000000039c6aac191691818000000000744b753617825c24c00000000ed99022d2f0460498000000021940c5ba46060093000000003735ba8948c0e012600000000628b7561a4945a300000000010c9ed17823030049800000001b9add45a6d88c0e1000000002a44928b48c10a180000000007baf55cda2d2f030000000000c516ea2a2f030049800000001eebb845a83cbc093000000003735ba8b4d219528200000000754b75169b023038400000000c516b24945a30049800000001b5a2d3884a48c0930000000040c7f6f756e8c01260000000081ab752814118024c00000001035aa22d23030049800000001fdbd62f0460850c0000000003a25ba8b4d81181c2000000007f6e099097823024c0000000105d6ea50230300498000000021940e6405e08c093000000003205ac8b502978230000000006e6b75169af32a46000000000dcd903145868b4bc000000002063fb2303b060093000000003735baa4d3a1782980000000081cbe91691818024c00000001031fdb9b5ba4606000000000206add4b646060093000000003dd736c1d169781800000000076c8b50797823024c00000001039fd97825246049800000001eeb9b5ba8b4bc0c0000000003fb7baee0bc0c0126000000006e6d2d169af32a46000000000dcdaab2060c8b48c000000001b9add4a0734d2093000000003fb7385e08c10a1800000000076c8b50d97818024c00000001031fdb2123030049800000001b9b0d4805e08c0e1000000003f45ba8b4ca94118000000000750b751697823024c00000000dcd92a2d2f04b8498000000020735660c8b48c0c0000000003735ba940ca941180000000007e8bed2811818024c00000000dcd6ea5e33a46074800000001fdbb87365e08c0c0000000003d56288b502978180000000007e8b75169181be24c00000000dcd8622d2f04d84980000000205add45a46060093000000002d645a83d02978230000000007f6ed8bc11818024c00000001031fdadd58646060000000001b9add4b66548c0c0000000002a445a868bc118180000000007bae7183a2d2f0300000000010c9b5b55230300498000000016b22d436814bc0c0000000003735ba9b0d811812600000000818c516ea2d18024c00000000f9deeba945a5e049800000002193be6405e08c0930000000037363e9c8d811812600000000804b751694118024c00000000fd16ea5039a30049800000001b9add45a6c0a6118000000003aa5ba9c8bc12e126000000006e6c7d169b025c24c00000000feddf178252460498000000018a30745a814bc0c00000000040e7f6bec8c0c012600000000628b7516a052f030000000000dcd6ea2d32a52060000000001f3ba97368b4bc11800000000373642b0d1697825c000000006d68b4bc12923042800000000e6d6b22d2f046060000000001fdb9b5bab34bc118000000002a445a814bc1292300000000085a8b4bc11818024c000000010399031445a5e0498000000020abfb5ba460600930000000037363e9c8bc1181260000000076cc191697823030000000000dcd6ea6c3544b849800000001fa2dd4d86c48c093000000003f45ba8b4a08c0126000000006e6c7d1697825c24c000000010d1b9a933ac30049800000001fdb736405e08c0930000000039c67cc5183a2d180000000006e6b751697827c38400000000dcd6ea2d2f0530998000000016b22d43683cbc0930000000037361a8b4bc13e126000000007e8b752911818024c00000000fd16ea2d29630049800000001fa34b45a504600930000000036b45a5e0949181260000000081cc858a22d36224c00000000dcd86a2d3626548c000000001b9add4c48b48c0db000000003fb6e6b34bc118214000000006e6b75169cd35e65400000000f75b5b2045a5e049800000001fa2dd4a04606d893000000003fb738c1d66978230000000006e6b75169ae23024c000000010ca073062f046060000000001b9add4c48b4eb8c0000000003aa63e8b4d8118126000000007f6dccbc13622024c00000000fedb9b2131046049800000002063dd736b75168c0000000003145ba961128c01260000000077cc818a22d2f024c00000000dcd9030645a5e08c000000002063dd6428b460093000000003cd45a5e08c0c012600000000818e6d169181d8300000000010c9b9b206285e0498000000019031445a79cbc093000000003aa63e8b4bc1181260000000081ab75169d735e24c000000010c9b9b5523030049800000001b9add5207589b093000000004326e67108c0c01260000000087f0c9aa91818024c00000000f75dc39b45a5e06000000000204b736425e08c093000000003735ba9892c118180000000007f6dcd8a17825224c00000001039fdadd23036c49800000dcd6ea9345a6c4bc14c0000000040d5f68b48c0c012600000000818e6d90a2d23030000000000dcd9332145a5e049800000001eebb645a5e060093000000003735ba9c8d8118126000000006e6d51169d735e24c00000000e0990ac345a5e08c000000001b9add5269acec8930000000040d6a88b4eb8c0126000000007e8bed1694118024c00000001031eead645a30049800000001b9add45a6208c0e10000000043277cc18bc118180000000006e6c351698823024c00000000f756ea4945a30049800000001db39b45a5e08c0c0000000003735ba8b4eb9af32a000000006e6b75169cd35e24c000000010c9831e72f046060000000001b9add4d85e0970e10000000037360cb3516978230000000006e6c353617825c24c00000000e098fa2d2f04604980000000206add45a75cca8c0000000003735ba8b4c6110126000000007f6dcd9f12923024c00000000e896ea6c31046049800000001b9add51e9ad2c0930000000036b50a7108c0c0126000000007f6dccbc14c23030000000000dcd8f22d2f046049800000001eb32060c8b4bc1180000000040e628c1916978180000000006e6b7539a622f046000000000f75d5b2145a5e0498000000021939b5ba5e08c0c0000000003736a88b4eb99518000000000770c5116a052f030000000000f75b9b2045a5e049800000001b9b0d45a6c08c0e1000000003fb6e6c18bc118180000000007e4b752c11818024c000000010b9eea2d2f0300498000000020636b45a4a48c093000000003f45ba940d211812600000000756e6d90a2d2f0460000000010356ea5e23030049800000001fdbdd736b74bc0c00000000039c640c1916978230000000006e6b75169ba23038400000000dad6ea5832a46060000000001b9add45a6508c0e1000000003dd6d6c191697818000000000864e71aa91818024c00000000dcd86a2d32846049800000001b9b1f45a5e09f093000000004326e65e08c10a1800000000081cbed61a2d23030000000000fedcd9782303b0600000000021939c60e5e08c0c0000000002d64ae8b48c0c01260000000081ab75169181b624c00000000dcd6ea903b26c449800000001b9add5388b4bc14c000000002d64928b48c0c0126000000007cef751697818024c00000000dcd6ea2d3ae6bc49800000001b9b1345a5e097093000000003145ba8b507a052f0000000006e6b751698c23038400000000dcd6ea2d2f04b449800000001b9b0d45a6308c093000000003145bab3516a052f00000000081ab75169d718024c00000000dcd6ea924c45e060000000001df31460c8b4bc0c00000000037367cc818a22d126000003735baa4d311b123030000000000fedcdb212f046060000000001b9add4bc6548c0c0000000003f45ba8b4a08db12600000000864dcd8a3062f030000000000dcd6ea624a046060000000001b9add4805e08c0e1000000003925f68b4ca91818000000000628c19169e72f030000000000dcd86a402f046049800000002063fb628b746009300000000373640b0d169782300000000087f0c8bc11818024c00000000fd16ea2d23038049800000001b9b5445a75c60093000000003735ba8b4ca9181b6000000007f6c516ea052f0300000000010c9b9b5564046049800000001b9add45a734d88e10000000040d5ba940d7918126000000006d6a14bc11821430000000000e6d8a2dd45a5e060000000001b9b0d45a734d8893
  | 7 => 0x3f45de8b4bc11818024c000006e6b75169782302ec49800000f696ea2d2f05308c0c0000001b9b3e5ba8b48c0db1260000037361a8b50797823024c00000000dcd6ea2d3ae65460000000e896ea2d31c46060093000001b9add4c496116918180000003735bab351697823038400000744b591697823030049800000fedb9b213625e08c093000001b9add50298cce918180000003735ba8b4bc12e1c22e0000006e6d411697823030049800000ea9b9b1f45a5e08c0930000016eaa44b08948c0c0126000003f45ba8b4b811818024c000006e6bbd2817823030049800000f39b5a2d2f046060093000002173734d68b4bc1181260000040e736b7516978230300000006e6c8583a2d2f04b849800000ee1d4b7345a5e08c093000001b9b0d59a8b4bc118126000003735ba8f0c711818024c000007e8b75169b132a46060000000dcd7a22d2f0460850c0000001b9add45a748bc118126000003735ba8b50d9781c2300000006e6c856ea2d2f04b849800000fd16ea2d23036c60093000001b9ad64785e08c0c0126000003735ba940b811818024c000006e6d2d169952f046060000000dcd6ea503485588c093000001b9add45a5e0910e1180000003fb6e6c518397818024c000006e6c996ea2d2f030049800000e716c22d2f046060093000001b9add45a854bc1181260000037361a8b50d97818024c000006e6b75169b023038449800000e496ea2d38846060093000001fdb73628b74bc0c0126000003735ba8b4bc0ff1c2300000006e6c858ca2d31046049800000dcd86a2d2f048860093000001b9add45a734bc0b8126000003735ba8b4bc14c26c300000006dab7561a2d2f046060000000dcd90add4806208c093000001b9b3e5ba8b5079181260000038f5ba8b4bc11818024c0000080cdcd6e97823030049800000dcd6ea7245a6c08c093000001b9add4a05cc8c0c01260000036b5be8b4bc11818024c000006e6b752017823036c49800000dcd9f30759a8b48c093000001cab0045a5e08c0c0126000003736a28b4bc11818024c000006e6b751697828234849800000dcd6ea4035446051093000002064035ba8b48c0c01260000037367cb7566a2d23024c00000864dad6b17823030049800000e096eac345a5e08c0c00000021a4036e65e094918126000003735f28b4bc11818024c00000714b751697827234849800000dcd6ea2d2f0454850c0000001c52ef45a5e08c0c0126000003735ba9892c225230300000006e6cf96ea2d43630049800000dcd6ea4945a83d02918000001fdb735485e094918126000003735ba9b0ec9b123024c000006e6b751699523036c37800000dcd6ea2d2f052060093000002073925ba9408c0c01260000038a5ba8b4b811818024c000006e6bed169c423030049800000e096ea402f046074893000001b9ade45a5e094918126000003a25ba8f0bc11818024c000007c0b7535a2d2f046049800000dcd6ea2d310460708a2000002133fb6e6c84bc118126000003c476e8b4bc11818024c0000070eb751697823030049800000dcd8a2dd4d85e060093000001b9add45a6c08c0bf126000003735d28b4d217823024c000006e6b752819d23030049800000fd16ea4945a460600930000021a3be50a5e08c0c0126000003735ba9010797823024c000006e6c351698823028849800000ee1b9a4945a83c8c093000001b9add50a5e08c0db126000003735ba8f0bc1181ac24c00000738d556ea2d23030049800000dcd6ea4945a86d028c0000001b9add4a09248c0c0126000004326e6d54bc11818024c00000704b751698e23030049800000e096b22d2f046060093000001b9b3e5b48b48c0c0126000003735bab352017823024c000006e6b75169782722e049800000dcd6ea402f04b85c093000001b9add45a814bc1181700000037363e8b4bc11817224c000006e6bbd1697823030c49800000dcd77a2d2f04b860093000001b9b2d45a5e08c0c0126000003735ba8b4d691819224c00000628b75169f02f030049800000ef96ea502f046060093000001fdb735ba5e08c0e11800000040e67cc516ea2d18024c000006e6bd11697823030049800000e9d6ea2d2f046064893000001b9add48086cbc0c0126000003735ba8b4bc118214300000006e6b751697025c30049800000ee1b9a4945a86c60093000002073735f69408c0c0126000003736008b4bc11818024c000006e6b75169a431046049800000f81dc22d40a5e08c0c0000001bf2f445a5e08c0c0126000003735ba9892c178230300000006e6b75151952f046060000000dcd6ea2d36046060093000001bf2dd45a5e08c10a180000003fb6e6c34bc11818024c00000738dcd6ea634285e08c000000001ce31460e8b4bc0c0000001dc37345a5e08c0b8126000003735ba9c8bc11814424c000006e6c0d2817823030049800000dcd77a4031046060093000001b9add5868b4bc1292300000037363eb75169b023024c000006e6b7549a2d3b269049800000dcd6ea2d2f0460708d0000001b9add50a83cbc118126000003735ba8b4ea9b118024c000006e6b75169822302e0498000010d1b9a9338846060093000001c52dd4ae8b48c0c01260000040e738b752811818024c000006e6aa51697825246049800000dcd80a2d2f052060093000001b9add5868b4bc1411800000040e5bab0d16978230300000006fab751697823030049800000e556ea2d2f046060093000001b9add4e88b4bc1181c2000003735bab354297823024c00000804b75169b123030049800000fd16ea2d3544606009300000219b7345a5e08c0c01260000040e6e6b75169181be24c000007f6dccbc1181dc30049800000dcd6ea2d2f04f869093000001b9add45a6a0bc118126000003875ba918bc11818024c00000714b7524a2d23030049800000dcd6ea2d2f04b851093000001b9b0d4e88b4bc118126000003735de8b4bc1181a424c000006e6b751699327230049800000fedb9b3e60e46060093000001b9add4a06a88c0c0126000003735ba9c8d817823024c000006e6b751695628236c49800000e496ea502f050460093000001b9add45a5e08a8c01260000036b5f68b4bc11818024c000006e6b7542a1b2f030049800000dcd6ea6c2f0460708c0000001fdb7367cb748c0c0126000003736968b4e68c01261bc000006e6c7d3917829c46049800000dcd6ea2d3b26c4a70e9000001b9add45a5c08c0d21260000036b45a5e08c10a18024c000006e6b751698023030049800000fd16ea634b046060093000001b9b4b45a5e08c10a1800000039c60ead91697823030000000868dcd169c425246049800000dcd6ea2d31c4a48c093000001d12dd45a5e08c0e1080000003dd5ba8b4f397818024c000007c0dcd9031445a5e049800000dcd86a6c2f0460600930000016b22d3fc5e08c0c0126000003735ac8b4bc12923024c00000704b751e17823030049800000dcd6ea2d2f04605f893000001fa2dd4a05588c0c01260000040e7f6b752c11818024c000006e6b752018823028849800000dcd6ea2d390460850c0000000003dd752b75169781260000037361a8b4bc136230384000006e6b752815b23030049800000e8986a2d2f046049840000001eebab5ba8b4bc0c0126000003736c6b751691818024c0000077cb75169c425246049800000dcd6ea2d31c50460093000001b9add45a5e0971181c2000003735ba8b4bc11817c24c000006e6b591697828230049800000dcd8a3065ba8b4bc0c0000002072d645a5e08c0c0126000003735ba8b4e69c418024c0000081cfed6eacd2f046049800000dcd972dd45a5e060093000001b9add45a6c4bc1181c20000037363e8b4bc14e25c24c000006e6b7524a2d25c30049800000e296ea2d31c4e460093000001b9b0d45a5e097118126000003a25ba9d13617823024c000006e6b752017823030849800000dcd6ea2d2ac46070093000001d52dd45a5e08c0e1170000003735baa24bc14e18024c000006e6c35169b12f046049800000dcd6ea2d3105e08c0e1000001b9afb4a05e0a08c01260000037361a8b4bc14c230300000006e6c816c22d2f046049800000c516eaa44928b460093000001df2dd45a5e0970c01260000037367cb753611818024c00000864dccbc1181d830049800000e296ea2d35446060093000001d53215ba8b4bc1181260000037361a8b4c417823024c000006e6b751697823030049800000df96ea2d2f046060093000001c92dd45a654bc118180000003735ba98d2b91818024c0000085cfd11697823030049800000dcd6ea2d32a46060073000001d12dd45a5e094918126000004215ba8b4bc11818024c000006e6b751698e29630049800000dcd6ea2d2f05046f893000001fa2e945a5e08c0c0126000003a25ba9b0d897823024c000006e6b7524a2d23034849800000dcd5222d388460850c0000001ce3145bab3516978126000003a25ba8b4bc14118024c000006e6b751e17825246049800000dcd77ac345a5e08c0c0000000003a9736b7516978230000003a25ba8b4bc1181c22e0000006e6ba52817823030049800000eadcdadd45a5e08c0c0000001fa2dd45a5e08c0c9126000003735ba8b4b494118024c00000868dad1697825246049800000dcd6ea2d3544b860093000001b9b145ba8b4d2178126000003735ba8b4e213918024c00000000e719f30745a46060000000dcd6eac345a5c08c0c0000001df2dd45a5e08c0d2126000003735ba8b5029c4230300000007e8b75169b123030049800000dcd6ea3c2f050460093000001b9b55628b59168c0126000003f45ba8bcbc11818024c000006e6b752817823032449800000dcda5a2d2f046060093000001b9aef4805e08c0e9126000003825ba8b4bc1181c2100000006e6bed169952f046060000000ee15222d40a5e08c0c00000020636b60e8b48c0c0126000003f45ba8b4c411818024c000006fcd2d1697823030049800000dcd6ea4945a86d07893000001b5add45a734bc0c0126000003925ba940b811818024c000007c0b7516a0f40a5e08c000000dcd6ea2d39046060093000002193736425e08c0c01260000040c6d6b751691818024c000006e6d55902dd45a46049800000e0986a2d2f046049840000001dc37345a7108c0c0126000004146e6b74bc11818024c0000086900ddf17823030049800000dcd6ea462f046060093000001b9add4a06208c0c0126000003736028b4bc11818024c000007e8b7549a2d3b230049800000dcd6ea2d31c4e469093000001b9add4d698916978230000003735de8b4c711818024c000007f6ea5b9add2f0460498000010c9b9b062f046060093000001f03b845a83cbc118126000003be5ac8b4bc1182143000000077cb7916978230300498000010cdb9a2a2f0460600930000016eaae4928b48c0c0126000003735ac8b4b811818024c000007c0b7516a1b40a5e060000000dcd6ea2d35446069093000001c52e945a5e08c0c0126000003735ba8b50d97817024c00000864f81b9b062f046060000000dcd6ea2d31046057893000001fa34b45a6c48c0c0126000003735ba8b4bc12217024c000006e6bed2817023030049800000dcd6ea934c6764ce8c0000001c52dd45a5e08c0c912600000373640c515222d2f024c000006e6b75169781fe2e049800000f81dc22d4365e060093000002072dd5848b48c0c0126000003735baa24bc13323024c000006e6b753a22d39a6c449800000e096ea2d2f04a48c093000001b9add45a7588c0c0126000003735e48b4bc11819224c000006e6b7516a222f030049800000dcd6eac34928b48c0c0000001b9add45a6a88c0c1126000003735ba8b4d217823038400000714b751698823030049800001039b9add4d86c48c093000001b9add4a05788c0c0126000003735ba8b4bb1181b624c00000724b752819d23030049800000dad6ea2d2f04e460093000001b92dd4928b48c0c01260000040e6e6b751694118024c0000067cc516ea2d3ce30049800000e096ea2d2f050460093000001b5add45a814bc118180000003f45ba8b48c0c01261f8000006e6b75169ad23038460000000dcd86a2d3485e08c093000001b9ae945a5e0970c0126000003be5bab0d16978230300000006e6b75169ca23030049800000dcd90b194805e08c093000001d12ef45a5e08c0c0126000003a75ba8b4bc1181c2300000006e6c4d1697822a30049800000e0990b0745a5e08c093000001fdb9c628b74bc0c012600000382642b751697823024c00000744b751697023030049800000dcd6ea2d2f04b864893000001b9b1960c8b4bc118180000003fb7e4b74bc11818024c000007baea5b5add45a5e049800000f39b9a2d2f046060093000001f02dd5268b502978180000003b86d68b4bc11818024c000006e6bbd1e17823030049800000dcd6ea2a2f046060093000001c92f445a5e08c0c0126000003925ba8b4bc118214300000006e6ba51697824030049800000dcd6ea3c2e046060093000001b9add45a6bcca9562300000036b5ba8b4c111818024c000006e6b5d61a2d2f046060000000e719f2dd59a8b48c093000001b9acd5868b4bc1181d8000003735ba8b4c411818624c000006e6b751698825c30049800000dcd6b24945a46060093000001b5a852f0460760c0126000003735ba8b4e69952f0300000000010356ea5023030049800000f81dc29345a5e060093000001b9add45a5e0900c9126000003735f6940ce91818024c000006e6cf96ea2d34846049800000e596ea2d2f052060093000001d531f45a5e0a71181260000043477c8b4e211818024c0000077cb751698e23030049800001039b9add45a52c60093000001d92dd45a5e08c0c0126000003be5ac8b4bc11818024c000006e6b75169c423036c49800000dcd6ea402f0460708a2000001b9add5868b4d5118180000003dd736b7516978230300000006e6c517422d2f030049800000dcd74a2d2f046069093000001b9b215788b4bc118126000003735ba90116978230384000007f6dcd6e9782302e049800000dcd86a402f046051093000001b9b1345a5e08c0c0126000003735ba8b4bc14c2301000000085cdcd169d9230300498000010c9b9ad62f046060093000001b9b0d45a6a88c0e1180000003736068b4c711818024c0000081adcd6ea2d3ae30049800000fd18a2dd45a5e060093000001ce2dd59a98d16978230000003e0736b7516978230300000006e6c352022d2f046049800000e7183acd45a5e08c0c0000001b9aa445a5e099918126000003735f68b4bc118214300000006e6b75169782824a449800000dcd6ea2d33a4606f893000001d4b6b45a5e08c0ec126000002d645a79cbc11818024c000000010c9b9b202f046049800000e396ea2d32646060093000001d5b73642b0d1697823000000373628b752817818024c000006e6b75169af2e446049800000f75dc2dd45a5e060093000001b9add51e925168c0126000002dd5488b507a052f0460000006e6c7d1697825c24c20000000dcd6ea2d31046069093000002073145ba8b4600930de0000036f5ba8b4bc11818024c000006e6b7549a742f053874800000ea5cdb6b5ba8b4bc118000001b9b4b45a734ca978180000003735ba8b5079c423024c000006e6b75201a42f046049800000dcd6ea7a45a46060093000002073735ba9408c0db126001b9add526988bc11818024c000005bab355222d40a5e08c000000dcd7ba2d2f04e460093000001d12dd4928b48c0c0126000003735baa30bc11818024c000006dab751697023030049800000dcd6b22d35446060093000001fdb732f0460798c012600000373642b3561a2d2f0460000006e6b7566a2d38846049800000e0977a2d2f046060093000001b9add45a654bc139180000003735ba9c8d814e23024c000006e6b75361782302e049800000b755222d436814bc0c0000001b9add4928f08c0c0126000003735f08b4bc13e18024c00000704b751697023030049800000dcd77a2d2f046070840000001b9add45a690ca9180de000000007f6dccbc12923024c000006e6b7516a1b38830049800000f216ea2d2f04cc8c093000001df2dd4785e08c0c01260000039c60eac916978230300000005ac9251697823030049800000c516ea2d3dc5e060093000001c92dd45a5e08c0c01260000036b5ba8b4b911818024c000006e6b7517178272300498000010d2064035ba46060093000001b9add45a75cd7978126000003b86e68b4ca97823030000000770a9116a1b2f030049800000e298a2dd45a5e060093000001f02dd45a86d07978126000003735baa14d217823024c00000818fed6eaa423030049800000dcd8fa722f04605c093000001b5add45a5e08c0db126000004346e6a4cbc11821430000000752dad90a2d2f046049800000dcd6ea2d32a50460093000001d5b7363e8b4bc118126000003fb6e6b60bc11818024c000006e6b751699530446060000000dcd6ea2d32a46060077000001e737345a888bc0c0126000003735ba8b4bc14c2302e0000007f6e719f2dd23030049800000dcd6ea2d2f04605c893000001fdb735865e08c0ec180000003735d2b0d16978230300000006e6b75391782303a449800000fd16ea2d2f0460708c000000206add4a0460600930de000003736aab691691818024c000006e6b752d982230300498000010356ea2d3ae5e060093000001b9ada45a7108c0c01260000040d5ba9611691818024c000006e6b751696323036c49800000e896ea2d35446060093000001fa30d45a5e08c0c0126000003735ba940bc1181c2300000007e8b753122d2f046060000000dd58a2dd45a5e060093000001b9add5868b4bc1181920000041f6e6b7531a58230300000006e6c7d1697825c2e0498000010d1b9a2d2f04a48c10a000001b9b0d4a05e08c0c01260000036b6428b4bc118126100000006e6bed1697823030049800000dcdaa22d2e446060093000001b9add4786a88c0c0126000000006e6b7528195230300000006e6b751699523030045000000fedce2dd4c65e08c0c0000001fdb885ba5e08c0c0126000003735ba8b4bc12e1d224c000006fcbed1697823030049800000dcd6ea2d39a6c4d2093000001b9b2c45a5e08c0c01260000036b5ba8b50797823024c000006e6bbd1697825246049800000dcd6eac345a6208c0c0000001c934b45a5e08c0c0126000003735ba940bc1411b624c0000077cb751697825246085000000dcd7a22d39a5e060093000001cb2dd45a5e08c0c0126000003735ba8b4e6978214300000006e6ba51698e23030049800000dcd6ea2d2e04a48c093000001b9aef45a5e0a08c01260000036b5bab351697823024c0000076cb751697823030049800000e096ea4945a46060093000001b9add45a6c08c0bd126000003e05baa4d16a0f2f024c000006e6b75169b134446049800000dcd6ea4031046074893000001fa33e5ba8b48c0c012600000373642b751697827c24c000006e6b751697823038423000000fd16ea2d3b26908c093000001b9add45a6388c0c9126000003735ba8b4b814118024c000006e6b591697823032449800000dcd6ea2d348558a0893000001fdadd548814bc1181800000036b5ba8b50d97818024c000006e6cf96ea5023030049800000fedb9b215865e08c0c0000001b9b0d45a5e08c09308c0000038a5ba8b4bc1181c2300000006e6b751697829c4d870800000fedb9add38846060093000001f039c632c1d16978180000003735ba7f8b811818024c00000736b755222d2f046060000000dcdaa22d3ae5e060093000001b9add4a05e08c0e01260000042e6e6a3d1697818024c000006e6b591698823030049800001039b9b0345a46060093000001fdb736725e08c0c01260000038a61a8b4bc11818024c000006e6c351697829c4d849800000dcd8a2dd45a5e069093000001b9b215ba8b4d8995230000003735ba8b4b994118024c000006e6b751697825c2cc49800000dcd6ea722f0460708c0000001b9add45a850bc11812600000373642c511697818024c000006e6b75169952e446060000000dcd90aa445a5e097093000001b9b215869d116978230000000006e6b75169b0230384000006e6b75169952f04606d800000f696b22d2f046060093000001fa2dd4805e08c0c012600000373628c191697818024c00000744ba51697823030049800000dcd7a22d2f04e460093000001b9af445a814bc118180000003735ba8b4bc13921430000000704b75169aa23030049800001039c92dd45a50460093000001b9add45a5e0970e1180000003735baa3d169b118024c0000072cc051697823030049800000dcd6ea892f0460850c0000000003145ba925168c0126000003e06e6c518322d2f0300000006e6b752818d23030049800000e896ea2d2f046064893000001c533e5ba8b48c0c0126000003735d28f0bc11818024c000006e6b75361c423030049800000dcd9cadd45a5e0a7136000001b9add45a6a88c0e1080000004346e68b4bc12923024c000006e6b75361b133a46049800000c516ea2d40a5e08c0c0000001b9b0d45a5e0970c0126000003735ba9251692923024c000006e6b751699d28230049800000dcd6ea5e2f052060093000001fa2dd45a6548c0c00de0000037e5d28f0bc11818024c000006e6c35169aa23024c20000000ee1b9a2d2f0460850c0000001b9add4785e08c0c9126000003735ba8b4d795623024c0000077cb751697825246049800000dcd6ea4945a504600930000020637360e8b48c0c0126000003735ba940ca9181801bc00000744b751698823030049800000b7556a4945a46060093000001b9add4805e08c0af126000003735ba8b4eb9952f0300000006fcb751e17823032449800000dcd6ea2d39a5e060093000001b9add4785e0880c0126000003735ba8b5079952f0460000006e6bd11698223030049800000dcd6ea5845a6548c0c00000016eaa445a86d079781260000040c6e6b751691818024c0000081ab7531a2d35e46049800000dcd7922d31846060093000001b9add45a6088c10a180000003735ba8b4bc11817a24c000006e6d5983a2d3b253860000000dcd90ac345a6c4bc118000001bf2dd45a734bc0c0126000003736008b4c111818024c000007e8b754297823030049800000dd59f2dd45a46060093000001b9add4e89b0d5118126000003735ba8b4d814e2303a400000628b75169f62f030049800000ef96ea2d2f050460093000001fdb6b60e5e08c0c0126000003735ba940b81181b624c000006e6b751699423034849800000dcd6ea3c3104606009300000206add45a6bc8c0c0126000003735bab35169952f04600000081cdcd7da2d28230049800000fedb5add2f0460600930000016eab64928b48c0c0126000003735ba8b4bc1181c2348000006e6cf96ea2d25c30049800000dcd8fa7445a5e08c093000001b9aef45a5c08c0c01260000043281cb74bc11818024c000005bab5916a052f046060000000e416ea2d2f046060093000001b9b1460eb0d169781800000038a5ba900bc11818024c000006e6b7516a1b32a5e060000000dcd86a2d2f046069093000001b9b145bab0d16978180000003955ba8b4c111818024c000006e6b75169782303846c800000dcd6ea2d3184b860093000001b9add45a674a58c01260000039c6e6c5183a2d2f03000000081cb5d16978230300498000010d1eebc445a5e0600930000020739c5ba8b4a08c0126000003735ba8b4bc12e14e24c000006e6b751697823030049000000dcd6ea2d3544a48c093000001b9add45a790ec995180000003735baa3d3a17818024c000005488b50c17823030049800000dcd6e22d2f046060093000001fa2dd45a734d88c0126000003dd7708b4f397818024c00000744b753a2632f046049800000dcd6ea503ae5c060093000001b9add45a5e08c0e1182000003736968b4e697818024c000006e6b751697827c28849800000dcd6ea6c3626a88c093000001fa2dd45a5048c0c01260000037369696116995230300000006e6b753122d3b246060000000dad169c42303b060093000001b9add45a6a8a08c0126000003735488b4bc118214300000006e6b75169aa2303845c000000dcd8fa2d2f04b88c093000001b9b0d45a5e08c0c1126000003825d28b4bc11818024c000006e6b751697829036c49800000dcd6ea2d39246060093000002073205ac8b4bc1181260000036b5ba9b0bc11818024c000006e6b7516a224285e049800000dcd8fa2d3625e08c093000001b9add45a5e09c8c01260000039c60ea9116978230300000006e6b752017823030c49800000dcd6ea402f04b860093000001b9add45a814bc11818000000373586a9116978252460000006e6b754497823030049800000dcd9f2dd45a46069093000001c52dd50a5e08c0c012600000373628b751698e18024c000007e8b751695628230049800000df96ea2d2f04e460093000001b9b0345a5e0a58c01260000038e5ee8b4bc11818024c000006e6c516b22d2f030049800000df96ea2d40a5e08c0c0000001c12dd45a5e08c0c9126000003fb6e6c516eacd2f024c00000754c7d169782302e049800000dcd6ea2d2b650460093000001b9add45a6c4ca918144000003735ba940ce9181b624c000006e6d55832dd45a46060000000dcd6ea502ac50460093000001b9b2060e8b4bc118126000000006e6c818a22d2f024c000007baea5b9add45a5e049800000ee1b9a2d2f046060093000001b9add50a7109491812600000373640b751697823024c000006e6c5183a2d2f0538600000010b9b9a932f046060093000001e737345a850bc118126000003825ba8b4c411818024c0000081ad5131a2d23030049800000ee1bf22d2f0460600930000000036b45a5e08c10a180000003735de9251691818024c000006e6b75169a42f246049800000dcd6ea2d3485d88c093000001b9aa445a5e08a8c0126000003735ba8b4c111818024c00000868ef916978230428600000010c9ce2d62f046060093000001b9add5205e094918126000003735ba8b4c41181c2100000006e6bd11697823036c49800000dcd6ea2d37c6c48c0e1000001b9b475ba8b4bc118126000003c85ba8b4bc118214300000006e6b75169782304286d800000df96ea2d30446060093000001df2ef45a5e08c0c0126000003735baa14bc12e18024c000006e6c351698823024c200000010096ea2d2303004986f000001b9add4805e08c0d2126000003736968b4bc13918024c000006e6d2d16a052f046060000000dcd86ac345a5e08c0c0000001fdb735ba654bc118180000003be5ba8b4b811818024c000006e6c5171a2d2f030049800000dcd6ea5e2f046060093000001b9b1460ca9116978180000003735ba894bc13918024c000006e6b75449c823030049800000ef9db22d2f046060093000001fdb732f04a48c0ec126000003735ba8b4c411822024c000006e6b7531a2d35e6548c000000dcd74a2d2f04a48c093000001d13145ba8b4bc0c0126000003925f68b4bc11818024c000006e6b75391b02302e049800000dcd6ea2d35e6548c0c0000001b9af445a83cbc118126000003735ba8b507978230428000006e6ba51697828230049800001039fd9782303b060093000001b9b145ba8f0bc0c0126000003735ba8b5129181b624c00000818ee1b5a2d23030049800000dcd6ea2d31c460708c0000001fa2dd45a5e08c0b8126000003736968b4c111818024c000006e6b75169c434846049800000dcd6b22d2f0460708c0000001b9b3e60eb0d16918180000003b645a79cbc11818024c000006e6b752d95623030049800000dcd7a2cd45a5e08c093000001d4b9b6e6b7516978230000003735de8b4d511818024c000006e6b7566a2d2f046085000000dcd6ea2d2f050464893000001b9b3e5bab0d169181800000037361a8b4c711818024c000006e6b754297823034849800000dcd6ea712f046064893000001b9add4a05e08c0b8126000003aa5ba8b4bc1181c230000000738dcd9f30745a46060000000dcd6ea2d3104a48c093000001b933e5ba8b48c0c0126000003735ba8b4d812e17024c000006e6b75361952f046060000000dcd7a22d4365e060093000001ce3075bab3516978230000003735ba8b50d9782143000000081cb7561a5845a46060000000dcd6ea2d310504600930000020639b5ba8b48c0c0126000003735ba8b4ec99529c3000000081cb7566ac345a5e08c000000f696ea2d2f04a48c093000001b9b2160e8b4c4118126000003735ba8b5112052f0300000007e8b751697723030049800000dcd6ea2d2e446060093000001b9add45a5e09b11012600000373602978bc11818024c000006e6c856ea2d31046049800000f496ea2d2f046060093000001b9add44a460600931140000043477c8b4bc11818024c000006e8b7516a052f046060000000dcd6ea2d2f05309b093000001df2dd4928b48c0c0126000003c85ba8b4bc11818024c000006e6b752817723030049800000dcd6ea2d2f04606d893000001b9b3e5ac8b48c0c01260000039a5ba8b4bc11818024c000007f6dcd9f2dd59a46049800000dcd6eac34805e08c0c0000001bf2dd45a5e08c0db1260000040e7f6c84bc11818024c000006e6b7547a6245a5e060000000e896ea2d2f0460708c0000001b9add45a6388c0e0126000003ce6e68b50297823030000000714b75169782302e049800000ee1b5a2d40a5e08c0c0000002072d64b08b48c0c0126000003b86e88b4bc11818024c000006e6b75152052f046060000000dcd9f30745a5388c0c0000000004326e6c18bc118180000003a261a8b4bc11818024c000007f6de56e978230300498000010c9df2dd2f046060093000002073fb5ba7648c0c0126000003735ba8f0bc1181c2300000007e8b751691818024c37800000e098a2dd45a5e060093000001b9add4e45e08c0b8126000003735ba8b4af14118024c000007f6dcd9097826c46049800000e496ea2d33a50460093000001b9b0d4785e08c0c01260000036b5ba8b4d217823024c0000077cb5d1697823030049800000dcd6ea2d3ae5e060093000001b9add45a83cbc11812600000000818fed6e91818024c000007f2b751697823030049800000dcda5a2d2e446060093000001b9ad945a5e08c0c0126000003735ba8b4bc11817424c000006fcb7516a0f2f046049800000dcd6ea4031c46060093000001b9add45a558a40c01260000037360eb351697823024c000007e8b751697923030049800000e719f30745a5e08c0c0000001c92dd45a734bc0c0126000003735ac900bc11818024c000006e6b7561a852f046060000000dcda5a2d2f04606d893000001b9add45a5e0a68c0126000003735bab351697823024c000006e6b751697825c2e049800000ef96ea2d35446060093000001b730745a5e08c0c0126000003735d28b4b811818024c000006e6b7531a2d35e6748c0000010356ea5045a46060093000001b9add4a05d88c0c0126000003735ba8b4de178230300000006fcb7566a2d2f046049800000e899f2dd45a46060093000001e42dd45a7208c0c0126000003735de8b4bc11819224c000007f6dcd7a17823030049800000db96ea2d2f046060093000001fdb732f04607f8c01260000039c642c511697818024c000007f6dcd6e97823042860000000ef9902d645a5e08c093000001b9add45a86cbc0c0126000002d645a814f3978230300000006e6c051697823036c49800000dcd6ea2d2e046064893000001eb2a445a5e08c10a1800000037e5ba8b50d97818024c000006e6cf96ea3c23030049800000fedce3075ba5e08c0c0000001b9afb45a674a08c0126000003f46968b48c0c01261bc00000864dcd902d62f046049800000dcd77a2d31046060093000001b9add45e5c08c0c012600000403736b75169782303000000081adcd6ea50230300498000010d1b9a8538846060093000001902d645a79cbc118126000003735baa14c711818024c000006e6b751697826c42851000001039fdadd5865e08c0c0000001b9b4b45a83cbc118126000003735f68b4e697818024c00000864dcd9022d2f046049800000dcd6b2852f046060093000001c13215488b4bc118126000003145ba8b4ff17818024c000006e6c516ea2d2f04a449800000dcd6d22d2f046060093000001fa2dd45a7108c0c0126000003735ba9d1169b023024c0000077cb75429c423030049800000dcd6ea2d42c5e08c0c0000001b9add4b08948c0c0126000003735ba8b4eb13622024c000006e6d2d66a2d2f046049800000e096ea2d2f0460708c00000020731460e8b4bc0c0126000003a25ba900bc11818024c000005baac924a2d23030049800000dcd7a26c2f046060093000002073145ba8b4bc0c0126000003735ba940e211818024c000006e6b753617823042860000000dcd7c22d32846060093000001c92dd45a5e09c8c01260000038261a8b4bc11818024c00000724b7516a052f046060000000f81db22d2f0460600930000020639c5ba8b48c0c0126000003736968b50d97818024c0000085cdcd24a2d23030049800000dcd6ea2d2f04b856893000001c72dd45a5e08c0c0126000003736948b4bc11818024c000006e6c351697823038420000000dcd6ead245a5e08c093000001b9add45a6208c0a21260000040e6e6b75169411b624c000006e6ba524a2d23030049800000dcd6ea2d4465e060093000001fdb7345a5e094918126000003b87248b4bc11818024c000007a2dcd1697823030049800000dcd6ea4d45a46060093000001b9add45a690ca978230000003735ba9d11697822a24c00000762b751697823030049800000dcd6ea744d85e08c0e1000001b9b146188b4bc0c0126000003fb77c5e08c0ec18024c00000738c516eac345a5e060000000ef974a2d2f046060093000001b9add4928b48c0c9126000003925ba8b4c111818024c0000081ca911697825246049800000dcd6ea5035e5e08c093000002193c46e65e08c0c0126000003735ba9b0bc12e14424c00000744b754297823030049800000dcd86a744d85e08c093000001fdb7360e5e08c0c01260000038267cb751691818024c00000754b75169b02302e049800000dcd7da2d2f04e460093000001fdb735ba5e08c0c0126000003735baa4d311782303000000077cb751697823032449800000dcd7da2d40a5e08c0c0000001ce2dc45a5e08c0c01260000037361ab751697825c24c000006e6b75169b12ac46070800000dcd5322d2f04a48c093000001c52dd45a7108c0c0126000003fb6fcb74bc11818024c0000081cdcd6ea2d23038049800000dcd6ea2d3aa654bc0c0000001c8add45a5e08c0c0126000003745ba8b50797823024c00000738a9116978230428600000010356ea502f046060093000001b9b0d45a6c4ab118126000003e05ba95d1691818024c000006e6b751697825246070800000ef96ea2d31046060093000001b9b215768b4bc118126000004025ba8b4ca978230300000006e6b751697823034049800000f55cdb6b45a5e08c0c0000001d12dd5269d0bc118126000003735ba8b4d897822a24c000007c0b7524a2d23030049800000dcd6ea5045a6548c0c00000021a3da45a5e08c0c01260000037361a8b4bc12923024c000006e6b75361b12f046070800000dad16978230428760c0000001dc36b45a83cbc118126000003735ba8b4bc14c22a300000005488b5029782303b060000000dcd6ea2d2f0504708c0000001ce3145ac8b4bc0c0126000003735ba9611511818024c000006e6d2d169a432a5e08c000000dcd7da2d30446060093000001b9ae945a6a88c0c0126000003735ba9c4bc1181c2300000006e6b7561a2d2f04605c000000e296ea2d31c46069093000001b5add4a05e08c0c012600000373642b751699423024c000006e6c35361b12f046049800000f818cadd4928b460093000001b9b0d45a5e0a08c0126000003b876c8b4bc11818024c00000704b752017823030049800000001b9add45a654a08c0000001b9b0d45a5e08c0e11700000040e7c0bed1691818024c000006e6b752c22d39a65460000000e71902dd45a5e08c093000001b9add45a6a88c0c9126000003735ba8b4e212e18024c000006e6b751697827c3a449800000dcd6ea6c2f046060093000001b5a2d2f0460778c0126000002dd59ab0d169e72f0460000007f6dcda5978230300498000010d1b9add4b06548c0c0000001b9add4805e08c0e108000000373628bbd1697818024c000006e6b752816323030049800000df96ea6c2f046060093000001dc36b45a86cbc0c0126000003735ba8b4bc136230384000006e6b7539a2d2f046049800000dcd6ea2d428814bc1180000016b22d40a5e08c0c0126000003735f0900bc11818024c000006e6b754297825246085000001031fdb6b5ba46060093000001cc2dd4a05e08c0c01260000037361a900bc118126100000006e6c7d1697829c4d849800000dcd8a2dd45a5c060093000001eeb6b60e8b4bc0c01260000037361a8b4bc13623024c000006e6cf96ea2d25246049800000f75b5add45a5e060093000001b9add45a6c4ca9181d2000003965ba978bc11818024c000007c0b5916a052f046060000000dcd6facd45a5e08c093000001b9add45a6388c0b81260000037363e9c8bc11818024c000006e6b59169782302e049800000fd16ea7445a6c48c093000001b9b3e5ba8b4a08c0126000003735f48b4bc11818024c000006e6b751697823038425000000dcdaa2502f0460600930000016b22d41e79cbc11812600000373684b751691818024c000006e6b752017823044049800000dcd6ea9345a75860093000001b9add45a5e0a6118180000003825baa14bc11818024c00000754b75169782302e049800000dcd6ea2d33a46060089000001b9b0d45a5e08c093094000003735ba8b4d81181c228800000724b751697823036c49800001039fdb565ba46060093000000003aa5ba9c8bc118126000003215488b50297823030000000000dcd8fa2d36046049800000dcd6ea2d38846069093000001b9b4b4d85e08c0c01260000037363e8b4bc12e18024c000006e6c856ea2d31846049800000e896ea6c2f04d88c0930000021a3dd752b7516978126000002d645a86cf397818024c000006e6c091697823030049800000dcd6ea2d40a734bc0c0000001b9b4b45a764a70c0126000003735ba9d1319b133a460000006e6b752017825246049800000dcd6ea744c66a88c093000001b9add45a6509f0c01260000039c67cb7561a2d230300000006e6d558322d230300498000010d201b7338846060093000001f03ab642c6516978126000003735ba8b4e69a41261bc0000081ad516ea2d23030049800000dcd7a22d3485e08c093000001b9afb45a5c88c0c01260000036b45a5e08c0ec18024c000006e6ba51e18223030049800000dad1697823044060093000001b9add45a690bc118214000003735ba900bc14118024c0000081cc196b22d2f0460600000010bd6ea2d2f046060093000001c92dd45a83cbc118126000003f45ba8b4ca978230300000007c0dcdaab0645a46060000000dad6ea2d2f04b860093000001dc37345a734bc0c0126000003735de8b4bc1181c2300000006e6bed1697823036c49800000dcd6f22d38846060093000002063b86e68b48c0c01260000039b6d6c1d1697823030000000744b75169782302e049800000dcdab30645a5e08c0c0000001b9b2160e900bc118126000003735d28b4bc11819224c000006e6b751e18223032449800000dcd6ea2d2f052c70093000001b9b145ba925168c01260000037354e8b4bc12923024c00000736dad6ea2d2f046060000000dcd6ea5032a5e08c0c0000001b9add45a5c08c0e118000000373642b752017823024c000006fcba51697823032449800000dcd6ea2d39a60860093000001c92dd59a8b4bc118126000003da5baa40bc11818024c000006e6b753a22d3ac46049800000feddc36b2f046060093000001cb2dd45a5e08c0db126000003e06e6c818ca2d2f024c00000000dcd8a30645a5e060000000dcd6ea3c2f04605c0930000020fb735ba8b48c0db126000003735ba8b4ca9411801bc000006e6c351697023030049800000ef98a2dd45a5e060093000001b9b065ba8b4bc118180000003735ba98916970230300000006e6b75169d935e46049800000dcd74a2d31046060093000001b8add45a5e08c0c01260000036b45a5e09491818024c000007f6b75619e72f046060000000dcd6ea852f04a48c093000001b9add45a5e0880c9126000003925ba8b50d97818024c000007c0f79dc22d2f030049800000fd17da2d2303004986f000001b9add4d68b4bc118126000002dd54895d1691818024c0000085cf8116978230300498000010c9b9b145ba5e06009300000183aa44928b48c0c0126000003735ac8b4bc0c016624c000006e6b751698823032449800000dcd6ea852f050460093000001b9add45a6508c0a21260000031460e8b4f397818024c000005baa9124a2d23030049800000dcd7da2d41e5e08c0930000021a3a9736b7516978230000003145ba8b4f397818024c0000081ab75169d923030049800000dcd6ea2d40a5e09c8c0000001fdb9b5ba5e08c0c012600000373640b711697823024c000006e6b751699523030040000000dad6ea2d2f046069093000001b9b145ae8b4bc0c0126000003fb6e6b7cbc11818024c000007e8d2d169952f046060000000dcd9f2ef45a46060093000001b9b1459a8b4bc0ec126000003735ba8b4ea9a82f024c000006e6b7561a2d38846060000000dad90a2d2f046060093000001b9afb59a8b4bc118126000003f45ba8b48c0c01261ec0000077ca911697825246049800000e716b26345a5e08c0c0000002072fb5488b48c0c0126000003735ba8b4eb14c23030000000714b75169952f0460600000010096ea2d3505e08c093000001efadd45a5e08a8c0126000003b86e68b4bc13918024c000006e6c516ea2d35430049800000dcd7da2d4365e060093000001dc37345a814bc118180000003735ba8b4bc11718024c000006e6b751e19323030049800000e7183acd45a5e08c093000001b9add45a64c8c0d6126000003735ba9cd1517823024c000006e6c818a2d645a5e049800000dcd6ea2d3044e460093000001ce2dd59a8b4bc118126000003735ba8b502982230300000006e6b75169b02f046070800000a91169e72f04a48c093000001b9add45a5e0970c81260000038a5ba8b8bc11818024c000006e6b7524a2d23038460000000dcd6ea2d3485e08c093000001b9b134e88b4bc118126000003735ba900bc13e18024c000006e6b752c24823030049800000eadb9b216288b4bc093000001b9b215ba8b4e69b1126000003145ba9251697818024c000006e6d556b22d23030049800000dcd55a2d2f0460850c0000001bf2dd45a690bc118126000003735ba9f0bc11818024c000006e6b59169c423030049800000dcd77a402f046060093000001b9b0d4928b48c0c0126000003735ba8b4ce9411b624c000006e6b75169ad23030049800000e096ea2d2f04605c093000001b9add4c492516918180000003b86e68b4c111818024c0000077cb751697823038460000000e9d6ea2d2f046060093000001b9add45a654bc12e1800000039c60eaad16978230300000006e6b7520170230300498000010fdaaad645a46060093000001b9add45a6308c0a2126000003be61a8b4bc11818024c000006e6d51169d923030049800000f816b22d41e5e08c093000001b9add45a734bc0db12600000373642c5166a2d2f024c0000081ab75169af2e046049800000dcd6ea2d3aa5e060093000001efadd45a5e08c0c0126000003fb724b74bc11818024c000006e6b751699b23030049800000dcd6ea9245a5e060093000001ce2da45a5e08c0c0126000003735ba8b4eb9af23024c00000804b751697823030049800000dcdb5a2d2f0460850c00000021a37350a5e08c10a180000003736268b4d897823024c000007e8b75169b134846049800000dcd6ea2d2f04b85d893000dcd6ea9345a5e0a60c012600000373640c1916978230300000006e6b751697823038462800000dcd6ea2d33a46070093000001b5add5868b4bc118180000003f45ba8b4e68c01261bc000006e6b751697826c4a049800000dcda5a2d3485e08c093000002193e077c5e08c0c0126000003f45e88b4bc11818024c000006e6bbd4297823030049800000e71b5b0745a5e08c0c0000001fa2dd45a5e08c10a180000003be5baa14bc118214300000006e6b752017823028849800000dcd6ea2d354460708c0000001b9b0d45a5e08c0c5126000003be67cb751691818024c0000081ab75169d723030049800000dcd6ea852e046060093000001b9af44a05e08c0c0126000003735ba8b51017818024c000006e6b7516a0f39a5e049800000dcd902a445a5e08c093000001b9add45a654bc1181a4000003735ba940bc11821430000000744b75169c423030049800000dcd7da2d2fc46060093000001b9b0d45a6a88c0c0126000003fb6e6c50bc0ec18024c000006e6c5174a2d2f030049800000f9dd4b6b45a5e08c093000001fdb735f65e08c0c0126000003aa63e8b4bc11818024c00000001031eeadd45a30049800000dcd6eacd45a734bc093000001c92dd4d85e08c0c0126000003735ba8b4ec9b122024c000007f6dccbc11821430049800000dcd6ea3c38846060093000001b9add45a5e08c0e110800000373628b751697819224c000006e6b75169d932a46060000000dcd6ea2e2f0460690930000021a36b45a7108c0c01260000040c6dcb751691818024c000006e6c0d1697823038049800000dad6ea2d31c46060093000001b9add5388b4bc14e1d20000037361a8b4bc118126210000006e6b751697827236c49800000fedce3072f046060093000001b5ad645a5e08c0c0126000003a25ba9d1169aa23024c000006e6b7516a052f04606d800000f216ea892f046060093000001fdb6b5bab34bc118126000003736a88b4d797023024c000006e6b75169782822e049800000dcd6ea4948046060093000001b9add4d85e08c0b9126000003fb738b74bc11818024c0000070ebc91697823030049800000dcd8a2dd45a62060093000001b9add45a6208c0e9126001b9add526894d891818024c0000077cb752017823030049800000dad83a2d2f05388c0c0000001b9b145bab3561a2d2f0000003a25ba9b0d511818024c0000077cc196b22d2f046060000000dcd6ea5044a460600930000021a403736b74bc118180000003b86e68b4bc1181b624c00000730b751698e23030049800000e297a22d2f046060093000001b9b4b4b08b4e68c01260000040d6a88b4b811818024c000007f6e6d6eaa42f046060000000e296ea2d2f0460850c0000001b9add45a6c4d0118126000004326e6c196b178230300000006e6bed3617823030049800000dcd6e2cd45a5e08c093000001b9add45a6088c0db126000003875ba8b4bc12e18024c000006e6c354817823030049800000dcdaa22d3ae4606009300000207365628b75168c0126000003735ba8b50797827224c000007f6dcd90b142f030049800000dcd6ea2d41e814bc118000001832d645a79cbc1181800000037359aa91169782304280000071eb7516978230348498000010c9b9b0645a5e08c0c0000001b9add45a71094918214000003736968b4ec995230300000006e6b75169d822a30049800000dcd6ea7236046060093000002073e05ba8b48c0db126000003735ba9c8bc1181c224c000006e6ba11697823030049800000dcd6ea8549246060093000001b9add45a734d88a21260000036b5c68b4bc11818024c00000000fd16ea2d23036c49800000dcd6eacd45a5e09c8930000000040c736b75169181800000039c60eb355222d2f0460000006e6b7566a2d40a5e08c0000010b9b9a6245a5e08c0c0000001fa2dd45a46060093108000003735d28b4bc1181c2300000006e6b752f17823036c49800000dcd6ea2d2f045449846000001fa2dd45a5e08c0c0126000003735ba8b4c411816624c000006e6c516b2cd45a5e049800000ef96ea852f046060093000001dc37345a83cbc118126000003735ba900d511818024c000006e6b75169af32a5c08c000001031fdadd45a46060093000001b9af445a5e0970c0126000003735ba8b4bc12e214300000006e6b7516a1b40a5e060000000dcd6ea502f046060093000001c12dd45a7108c0c0126000000007baee11697818024c00000000dcd6ea2d2f05309b000000dcd6ea2d2f0460708c9000001c92fb45a5e08c0db126000003735ba8b4e69a432a5e0000006e6b7516a0f30446049800000dad6ea3c2f046060093000001b9b216289d116978126000003735ba8b4d812e18024c000006e6a911697826c44049800000dcd6ea2d2f04b870893000001dc37359a8b4bc118126000003736a48b4ca978230300000006fcb752817823030049800000dcd9eadd45a46060093000001b9b215488b4c4118126000003735ba8b4ca95623036c000006e6c35169782303244980000107dfdadd2f046060093000002072d845a5e08c0c0126000003b86dc8b4bc11818024c000006e6b7566a2d304460498000010356ea2d32a5c08c0c0000001dc37345a86cbc0c0126000003735ba8b4c41181c2300000006e6b753122d36246060000000dcd6ea924545e060093000001fdb735ba734bc0c0126000003735ba97d1691818024c0000081ad596ea2d23030049800001031fdb735ba46060093000002012dd4545e08c0c0126000003735ba8b4bc13e17024c000006e6b75169d823030049800000dcd6ea2d3ae6548c0c0000001eeb7360e8b4bc0c01260000037361a8b4c411818024c000006e6b7516a1b30430049800000dcd6ea2d32a6388c0c0000001eeb735ba8b4bc0c0126000003736268b4d691818024c000007f6dcd9f1181d830049800000dcd77a2d2f04605c093000001b9ad645a654bc1181800000037367cba51691818024c0000081cdcd6ea2d35e46049800000dcd6ea8535446060093000001fa34b45a5e08c0c0126000003a76268b4bc11818024c000006e6bd11697823034849800000dcd6ea2d2e04605c093000001b9add45a75cca956180000003735ba8b4bc118214348000006e6c858a22d3625e049800000dcd9f2dd45a46064893000001b9b4b4a05e08c0c01260000038e5ba8b4bc13918024c000007c0b753122d2f046060000000f6986a2d2f046060093000001b9b205b48b4bc1181260000038a5ba8b4bc11818024c000007f6dcd8a2dd5865e060000000dcd9cadd45a5e097093000001b9add45c6388c0c0126000003735ba8b4bc12e17e24c00000752dc16ea2d2f046049800000dad6ea582ac46060093000001b9add45a6308c0c9126000003735ba8b4bc12723024c000006e6b753917823030049800000dcd7922d2f046060093000001b9add5269d0d5118126000003735ba8b4b991817024c000006e6b753a2632f0460708000010d201b732f0460850c0000001b9add45a71094918126000003735ba9b0e697818024c000006e6c7d6ea722f046049800000dcd9f2dd59ab0d16918000001fdb735485e08c10a1800000037361a9d13197823024c0000081cc8561a2d2f0460600000010d201b9c60e5e08c0c0000001b9ae94805e08c0c0126000003735ba8b4e214118024c000006e6d51169952e046060000000dcd6f22d2f0460850c0000001b9add45a6208c0a7126000003925ba8b4d217823024c000007f6dcd6e97827230049800000fd16ea2d23036c4986f000001b9add4e8988bc118180000003fb738c1d52178230300000007f6dcd6ea052f046060000000dcd6ea5b2f04606f893000001b9af345a5e08c0c0126000003a25ba8b4ca978230300000006f2b7561a2d2f046060000000dcd6ea2d2f04b860093000002063dd6d6b75168c01260000040e5bab0d169d9230300000007f6dcd8a2d62f030049800000dcd6ea402f046064893000001b9af74785e08c0c0126000003fb6e6cf99091818024c000006fcb751697825c30049800000dcd6ea2d3b26a08c093000001b9af745a5e08c0d61260000036b45a5e08c0f118024c000006e6c7d6ea2d2f04b849800000e6db9add45a5e08c0c0000001c534b45a5e08c0c012600000373642b0d1697826c460000006e6b751e1952f046060000000001db22d2f046060093000001b9add45a838bc1181260000040c7f6b74bc11818024c000007f6ee1b997823030049800000dcd8a2a445a5e094893000001b5add2f05a48c0c0126000003735ba900c411818024c00000724b751697a23030049800000f816ea4945a8148c0c0000001b9add45a6c0a71181c2000003735baa8116995230300000006e6b7524a2d2302e049800000fedb9add30446060093000002072dd5488b48c0db1260000040e6e6b752814118024c0000081cdcdaa22d23030049800000dcd74a852f046060093000001b9afb45a690bc118126000003735ba8b50d9781b624c000006e6b75169952f646060000000dcd792462f046060093000001b9af45868b4bc118180000003be5ba8b4bc11817024c000007c0ee124a2d23030049800000dcd6ea6c2f04e460093000001bcad645a5e08c0c0126000003f45ba8a8bc11818024c0000081cb59169d923030049800000dcd6ea6c40a5e08c0c0000001b9add50a5e08c0c9126000003735ba8b4ec9b1230384000006e6b751697823034849800000dcd8fa2d2f0460708b8000001b9add45a6508c0e9126000003736968b4bc12e18024c00000818dad169181d830049800000df96ea2d2f046069093000001ce31460e8b4bc118180000003735528b4bc118214300000006e6b75361aa26c46049800000dcd86a2d3b26c48c093000001fa2dd45a734ca97818000000373628b75169781c2300000006e6b751697823036449800000dad6ea2d2f04a48c093000002074035f68b48c0c0126000003735ba8b4ba11818024c000006e6b754298823030049800000dcd6ea2d34e5e08c093000001dc3734d85e08c0c01260000039c6aab591691818024c000006e6b752317825c30049800000e7183aa945a5e08c0c0000001b9ad745a5e08c0b812600000373628c351697818024c000007f0b751697823030049800001031cdb6b5ba8b48c0c0000001b9b1f45a5e09b1181260000036b5ba8b4bc14118024c000006e6b7516a1b41e5e049800000dcd6ea6c30446060093000001b9add4bc5588c0c01260000038a5ba8b51117818024c000006e6b75169af32a46049800000dcd7a22d31c460600930000021a37345a7108c10a180000003735ba8b4c7118214300000006e6b7549a742f044049800000dcd6b22d2f0460850c0000001b9b5245a6a0bc118126000003735ba8b4d511817024c000007baee1b5a2d2f030049800000fedb9b3e5bab0c8c0c0000001b9add59a8b50d978126000003925f68b4ab11818024c000006e6b751696328230049800000dcd77a2d38846060093000001c12dd45a654bc1181800000040e7f6b74d891818024c0000077cb75169c423042860000000f81b9b1960c8b4bc0c0000001ce3075ac8b4bc1181800000036e5ba8b50d97818024c000006e6d2d1697823034849800000dcd6ea2d2ea46060093000001d52dd45a6c08c0c01260000037367cc5183a2d18024c000005baa913122d2f046060000001039b9add4b646060093000001e738a45a5e08c0c0126000003dd752b751697823024c000006e6cf98a2dd45a30049800000e296ea2a2f046060093000001b9add44a5e08c0d2126000003aa5ba9c91697823024c000006e6b75169a831c46049800001031b5b2145a46060093000001eeb9b5ba8b4bc0c0126000003735ba8b4d491818024c000006e6b751698c2303a449800000ef96c22d2f046060093000001f03a95ba8b4bc118126000003736968b4ec91818024c0000081cc516ea5845a30049800000dcd6ea2d2fc4606d893000000002d645a814bc118180000003fb6e6b74bc1181b624c0000077cb75169781802cc498000010c9b9ad82f046060093000001b9b0045a5e08c0df1260000040e628b7566a2d2f024c00000844dcd6ea2d2f046049800000dcd6ea2d2f04fc8c093000001b9add5868b4bc1181800000037260e8b4bc11818024c000006e6b75169af2e046049800000f81b9b1345a5e060093000001d12f445a5e08c0c0126000003aa6e6b753917823024c00000704c856ea2d2f04b849800000e896ea2d2f0460850c0000001b92dd45a5e08c0c0126000003735ba8b4ec978298300000006fcb7561a2d2f046060000000dcd9f2a445a4a48c093000001fa2dd45a460600930e6000003985ba8b4bc14b18024c000006e6b75169cd3485e049800000dcd86a2d2f0460708c0000001b9add4b08b4d2195230000003736a48b4bc11818024c000006e6b751695623036c49800000e496ea502f046060093000001b9b145ba900bc0c0126000003735e88f0bc11818024c000006e6c51832d645a5e060000000dcd6ea402f046074893000001dc39b6d68b4bc118180000003735ba8f0bc1182143000000072ab751697823037c49800000e71b9add4c695c8c0c0000001b9aa445a5e0a6118180000003735ba98d1117818024c000007f6dcd9097823024c200000010d2074036ac4606009300000206add45a5c08c0c0126000003735d28b4c111819224c000006e6b75169952f04a48c0000010d1b5a2d2f0460850c0000001fdb735ba83cbc118126000002dd54892516a05230300000006e6c81832dd45a5e08c000000e896ea7445a5e08c0e10000018a2dd45a814f3978180000004346e6d551691818024c000006d6bbd1697823030049800000fedb9b0759a5e08c0930000021a37345a7108c0c0126000003735d28b4bc11817024c000006e6b7531a2d3ae6bc49800000dcd6ea6c2f04606d893000001b9add45a6388c0c0126000003af5ba8b4bc11818024c000006e6b75169952f050460000000dcd6ea2d3c25e0a70e9000001b9ad645a5e08c0c01260000038f5f08b4bc11818024c00000868dcd6e9d52f030049800000e896ea2d2f04b851093000001fdb735bab34bc118126000003a261a9d11697823024c000006fcb751698e23030049800000001b9b5560c8b48c0c0000001b5add45a5c08c0c0126000003735ba8b4b09181b624c0000081ab751697323030049800000fd17da2d2f046060093000001b9add45a75cd78c01260000037367cb75169181c2300000006fcb591697823030049800000dcd6ea5b2f050460093000001d12dd4d85e08c0e1180000003be6aab751691818024c00000770a9124a2d23030049800000dcda5ac345a5e08c0c0000001ccadd45a5e08c0c0126000003aa5ba8b4bc11818024c000007f6db96e97823030049800000ef96ea2d38846060093000001b9add45a75cab0c012600000434804b74bc11818024c00000770c51169e72f030049800000dcd6e9fe32a5e08c0c00000021fad645a5e08c0c0126000003e05ba92516a0f23024c0000081cdcd6ea2d29030049800000ed9b5a2d2f046060093000001fdb735ba86cbc0c01260000037367cc351691818024c000006e6bed2817823030049800000ea98fadd45a5e08c093000001d130d4d85e08c0c012600000373628b754297818024c000006e6d2d169cd3485e049800000dcd6ea2d2f05309b11000000206add4c68b4eb8c0126000004326e6d556e91818024c000006e6b7523a2d23030049800000dcd6ea2d35e6748c093000001b9add4805e08c0b3126000003736968b4ab1181b624c000006e6b75169882302e049800000dcd6ea2d3c26548c0c0000001b9b2a642c5116978126000003735ba8b4d217827224c0000083edcd6ea5023030049800000b5916a252f046060093000001b9add45a814d2178230000003a25ba8b4d8978230384000006e6b753620f2f046049800000dcd6ea2a3b246060093000001b9b21548900bc118126000003e05ba92516a1b18024c000006e6b752019423030049800000dcd6ea8f45a5e060093000001b9add45a5e08c0df126000003a261a8b4d897823024c000006e6b752817028230049800000dcd8fa2d3605e08c093000001b9b5445a5c08c0c0126000003825de8b4bc12e18024c0000081cd596eac345a46060000000dcda5a2d31c46060093000001b9add59a9b0bc1181260000037360ca91169782303000000081ce71ab30745a46060000000dcd6ea2d3b2734ca8c0000001b9add4805e08c0e1180000003825e88b4bc11818024c00000770dcd169a42f046049800000dcd522852f04a48c093000001b9b5a45a5e08c0c0126000003825ba8b4bc118214300000006e6b75391782302e449800000dcd6ea2d39a6c474893000001d12dd45a5e08c0c01260000040e6e6c011691818024c0000081cfed8a2dd2f030049800000dcd6ea2531c46060093000002073735ba9892c118180000003736aac816b22d23024c000006e6c352017823030049800000dcd6ea6c4365e0600930000021a37345a5e099918126000003735ba8b4bc12e14a24c00000000fedcdadd2f046060000000dcd6ea2d3486088c093000001c92dd45a5e0970c0126000003735ba9b0bc12218024c00000714bed1697823030049800000dcd6ea3c2f046060093000001b9add5028b4ca918180000003dd738b751697818024c000006e6b751697823035849800000df96ea3c2f046060093000001b9b215ba8b4bc14c26c0000036b5ba9251691818024c0000071ec856ea2d2f046049800000dcd6ea2d2f04b85c893000001b9b544c68b4eb8c01260000040e6acb591691818024c000006e6b75169882302b449800000001ce30759a8b4bc118000001c12dd45a5e0970a2126000003735baa14bc1181c2300000007c0b7549a4945a30049800000dcd77a2d32a5e08c0c0000001b9b3e5ba9008c0c0126000004326d6b74bc11818024c000006e6c354297823030049800000e89a5a2d2f046060093000001b9add45a654b8118180000003735f68b4bc12e18024c000006e6b752819d28230049800000dcd90add45a5e0a4093000001fa2dd45a734bc0c0126000003925ba8b4bc1181a424c000007e8b752c22d32a46060000000dcd6ea5b2e046060093000001b9add45a6548c0db180000003735ba900bc11814e24c0000070ec856ea2d2f046049800000dcd6ea6c31046051093000001b9b4b4785e08c0c0126000003b645a5e08c0ec18024c000006e6bd11697825246049800000e296ea2d4285e08c093000001b9add4a0734bc0c0126000003735ba8b4bc129230428000006e6b756a22d2f046060000000dcd6ea934e85e08c0e1000001b9aef45a5e08c0bb12600000434818fed6e91818024c0000081cdcd6ea2d36246070800000dcd6ea5c45a46060093000001b9add4565e08c0c01260000037361ab751698823024c000006e6b75169952e646060000000db56ea2d2f046060093000001cc30345a5e08c0c01260000040d5ba98d2c11818024c000006e6bd11697828230049800000dcd86a934e85e08c093000001b5add45a6a88c0c01260000040e6e6c35169b123024c000006e6b751697828242860000000c516ea2d40a5e060093000001b9add5a68b4bc118126000003736008b4bc14118024c000000010c9df17823030049800000fedb99c42303b060093000001b9b3e5baa148c0c0126000003735ba8a8c711818024c000006e6ba5169c423030049800000dcd6eaa044a46060093000001b9b215de8b4bc12e126000003735ba98d169d732a30000000714bd11697827230049800000dcd6ea2d360460708b8000001c12dd45a5e08c0c0126000003a15ba8b4bc11818024c000006e6b7549a2d2f053060000000dcd7da2d2f046069093000001b9add45a7108c0c9126000002dd54892516a0f23024c000006e6d2d169952e046060000000e3d6ea2d2f04f860093000001b9b145ba8b4bc0b8126000003ab6d6c851697823024c000006e6c856ea2d36046049800000dcd6ea2d2f0460708400000018a2dd45a83cf39781260000040c7badcd6ea2d18024c000007e8d2d169cd2f030049800000e556ea2d2f050460093000001b9af845a5e08c0c0126000003735ba8b4bc12922a24c000006e6c351697823024c20000000b7566aa44928b48c093000001fdbdd6d6b74bc0c0126000003145bab35169e72f024c00000714b75169cd2f030049800000fd16ea2d2f04e460093000001b9add4b66748c0c0126000003735ba8b51294118024c000007e8b7516a052f046060000000dcd6ea4945a6548c0c0000000003fb6e65e08c10a1800000040e7f6cf96e91818024c000005baa9124a2d43630049800000ee1b9a2d41e814bc118000001fa2dd45a6908c0930de0000040e806b75169181b624c000006e6b752817827230049800000dcd6ea2d2f44606d893000001b9add4a0814bc118180000000007f6e71839782303000000077cb75169952f046060000000e09a5a2d2f046060093000001fa3b845a5e08c0c0126000003925bab0d16978230300000006e6b7531a142f046049800000dcd6ea2d2f04d88a893000001b9add4d696112918126000003735ba9b0bc13623038400000744b753617823024c20000000dcd6ea2d43e5e08c093000001dc37345a86d02978180000003735d28b4bc13323024c00000770dcd2817823030049800000fd16ea2d30446060093000001fa2dd45a460600930ee0000042e6d68b4bc11818024c000007acb591697823030049800001039b9b0145a46060093000001b9add4e88b4bc14c2300000037361a9b0bc13623024c00000724b751695623036c49800000dcd6ea2d2f04a48c093000001b9add45a5e0970bd126000003735ba940c111818024c0000081ab75169b123030049800000df96ea2d2f04a48c093000001fdb6b2f0460760c01260000036b5d28b4bc11818024c000006e6cc51697823030049800000fd1b9add45a4606d8930000021a3736428b4bc12e126000003735ba9b0d897823024c00000818e6db9add45a46060000000dcd6ea2c2f046060093000001b9add45a86cd2178126000003735ba8b4bc14118024c000006e6b7531a2d33a4606d800000dcd7a22d2f04e469093000001b9add4e25e08c0c0126000003735ba8b4bc1181c21300000081cf816ea5023030049800000dcd8a2d845a5e060093000001b9add45a5e08c0e11700000037e5ba8b4bc14118024c00000738cf98a2dd45a30049800000dcd77a2d2f0460850c0000001b5add45a5e08c0c912600000373628b0d169781d8300000006e6b75169aa32a46060000000001b9add4e45e08c0e1000001c92dd45a6388c0c0126000000007e8b752811818024c00000714b751697827230049800000fedcdb6b5ba5e08c0c0000002012dd4b08b48c0c0126000003f45ba8b48c0c0126228000006e6b751697829028849800000dcd7dac345a5e08c0c0000001c92d645a5e08c0c01260000038a5ba8b502978230300000006e6c351697823024c26000001031eeadd45a5e060093000001eebb86e68b4bc0c0126000003735e88b4b811818024c000006e6c35169782302e049800000dcd6ea2d2e0460850c0000001b5add45a6208c0c0126000003735ba8b4d8978298460000006e6bed1695623036c49800000dcd6ea634b06548c0c0000001c92fb4a05e08c0c0126000003735ba984bc11818024c000006e6c9d90a2d2f04b849800000ee1c522d2f046060093000001df2a450a5e08c0c0126000003735ba8b4e69781a424c000006e6c311697823030049800000dcd6ea5032a5588c0c0000000003735ba8b4bc12e1c2000003735ba98d169d733a30000000738c516ea6345a5e060000000dcda5a2d2f04a48c093000001b9add45a674a40c0126000003fb5baa912491818024c000007baf116ea2d2f030049800000e296ea2d30446060093000001b9aef45a5e0970a2126000000006e6c351697825c24c000007f6c516e9e72f030049800000dcd6ea2d2f052c60093000001b9b4b45a5e0a08c0126000003735f68b4c711818024c000006e6cf96ea2d2302e049800000dcd6ea2d40a5e0970c0000001b9add4e45e0a71181d2000004075ba8b4bc11818024c000007f6dad9097823030049800000dcd6ea2d36046051093000001fa3215ba8b4d8918126000002d645a7c8bc11818024c00000628b755222d40a5e060000000dcd90b145868b4bc0c0000001b9b55628b75168c0126000003b86e68b4bc12e18024c000006e6b751697823038421800000dcd8a2dd45a710600930000021e373642900bc118126000003b65ac8b4bc11818024c000000010356ea2d35e46049800000e096ea2d3104b860093000001ce2d645a5e08c0c0126000003fb738b756697823024c000007e8b751697823036c49800000dcd6ea502e446060093000001b9add45a5e0a712e1d20000040c736b751697823030000000770e6db9a2d2f046060000000dcd90add48c5e08c093000001b9b396288b4bc0c0126000003925ba8f0bc11818024c000006e6c351697823024c21800000dcd6ea2d3044b860093000001f3b6b45a5e08c0c01260000036b6429d11697823024c000007f6dcd6e9a42f046049800000dcd7a24945a46060093000001b9add4c48b48c0c00de000004346e68b4bc118214300000006e6b752817823036c49800000f75d4add45a5e060093000001b9add4928b48c10a180000003735ba8b4bc13e18024c00000754b753917829c46049800000dcd8fa2d3605388c093000001b9ae945a654bc118180000003735ba8b4bc1391a424c000006e6b75201782302e049800000dcd6ea2d3ac4a48c0930000018a2dd4928b48c0c0126000003735ba8b502978230348000006e6bbd1697823030049800000ef97a22d2f046060093000001df2dd45a5e08c10a180000003736968b4ec9cd18024c000006fcbbd1697823030049800000dcd6ea2d30448060093000001b9add45a5c08c0c0126000003735ba8b4ca978230324000006e6a91169c425246049800000e897da2d2f046060093000001fa2dd4a0460600930de0000037e5ba8b4b811818024c000006e6b75169b132a46060000000fd16ea2d41e5e08c093000001db37345a5e08c0c0126000003f45ba9611691818024c000006e6b75179952f046060000000ee1b9a2d2f046069093000001b9add5868b4e6978180000003735f68f0bc11818024c000006e6b75281d72f030049800000dcd6ea2d32a6208c0c0000001b9add45a86d07a052f0000003735ba9410797823024c000006e6bd11698e27230049800001031b92dd45a46060093000001b9add4e88b4d6918126000003735ae8b4bc118214300000006d6c85169b12f046049800000fd16eacd45a5e08c093000001b9add45a6088c0d2126000004346e68b4bc11518024c000006e6b751697323030049800000dcd9f2c345a460760c0000001d3add4e88b4bc118126000003735baa051291818024c000006e6b75361a42f046049800000fedb5add5865e08c0c0000001b9add45a734ab0db126000003735baa4d169d932a300000006e6b75429782302e049800000b756b24945a46060093000001b9add59a940bc1181260000038a5ba8b4bc1181b624c000006e6b7545a2d23030049800000dcd9030645a5e08c093000001fa2dd45a86cbc0c0126000003735e88b4d511818024c0000081cb755225023030049800000ee1b9a2d43683cbc093000001b9add45a764d214e126000003735ba8b4d5118214300000006e6b75169c423038460000000dcd6ea634b06748c0c0000001b9add45a6c4ce9181c20000041f5ac8b4bc11818024c000005baab916a052f046060000000dcd6ea504365e060093000001b5b145ba8b4bc0c0126000003e06e6c818322d2f04600000081cb756022d23030049800000ef96b22d2f04a48c093000001d4b9b5ba8b4bc118180000003736968b4b811818024c000006e6b75169cd31c30049800000dcd86a2d38846060093000001b9add4805e08c0ad1260000037361a8b4d899d23024c00000738cf96ea6345a46060000000dcd6b22d39a5e0600930000000040d6a88b48c0c0126000003736968b4d8995230300000006e6b59169782302f449800000fd1a5a5845a46060093000001fdb3e5ba79c8c0c0126000003735ba95d1691818024c000006e6c856ea2d3104b849800000ea96ea2d2f04605e893000001b9add4e88b4d51181c2000003f45ba9611291818024c00000714b7516a0f2f046049800000dcd6ea2d2f04b86d893000001d5b9c642c1d16978230000003ab6e6b753917823024c000007badb96ea2d2f030049800000dcd6ea4945a460600930000021940e5ac5e08c0c0126000003735bab0d16978272300000006e6c4d3897823030049800000dcd6ea2d3544b851093000001b9b0d4e88b4d5118126000004327c0dcdaa91818024c0000067cb755222d40a46060000000df96ea4945a46060093000001fa2dd45a6c48c0a2126000003735ba9b0d51181c230000000864dcdab17823030049800000dcd8a2d65868b4bc0c0000001b9add45a74cbc0c01260000038a5bab351697823024c000006e6b75429c423042860000000dcd6ea624b046060093000001b9b3e642b0d16918180000003735ba8b4bc11012614400000864ef8bc1181d830049800000dcd6ea2d32a4606007e000001df2dd45a5e08c0c01260000037360eb751697829c4cc00000000dcd6ea2d35e6548c000000dcd86add4805e08c093000001b9add5269d0ec9b11260000037361a9b0d511818024c003735baa4d169b12f044049800001039b9afb45a46060093000001c12fb45a5e08c0c0126000004326e6c1cbc11818024c0000081ce716ea634b046060000000dcd6ea2d3544605f893000001b9b1f45a5e08c0e1180000003b86e6b0d1697823030000000714b7516a1b2f030049800000dcd89a2d2f04d88c093000001b9b206288b4bc118126000003735ba9c8bc12e17024c00000704b751697825c3a4498000010c9b9add2f046060093000001b9add48c5e08c0a21260000041881cb752811818024c00000770dc91697823030049800000dcd81a2d2f046060093000001fa2dd45a690ca978230000003875ba8b4bc11819224c000006e6b614297823030049800000dcd6eac345a6088c0c0000001d12dd45a734bc0c0126000003755bab351697823024c000006e6b7516a0f2f04b849800000dcd6ea2d3626a88c0e1000001b830745a5e08c0c0126000003815ba8b4bc11818024c000006e6b5d1697823030049800000dcd8222d2f046060093000001d12dd45a5e08c0bd126000003735ba8b4c713918024c000006e6b754897822a30049800000dcd6ea2d31052060093000001b9add45a814c7118180000003735ac8b4bc13918024c000006e0b751697823030049800000dcd6b22d40a5e08c0c0000001c92dd45a5e0949181260000037361a8b4d89aa23024c000006e6d516ea2d3ae30049800000dcd6ea3c39a5e060093000001b5add45a5e08c0e1180000003735bab351697825c24c000007f6fd16e97823030049800000dcda5a4945a46060093000001fdb732f0460850ec180000003735d28b4bc11821430000000000f75cdadd45a5e060000000e0990aef45a5e08c093000001b9add4a05f88c0c0126000004346e68b4e411818024c000006e6b75169aa23030049800000dcdaab065ac8b48c0c0000001b5b0d45a5e08c0c0126000003925ba8b4bc14118024c000006e6b75201c423030049800000ee1b9a2d31c46060093000001df34b45a5e08c0c0126000003735e88b4bc11819224c000006fcb75169aa23030049800000dcd6ea2d2f0460850c9000001b9b205ac8b4bc1181260000041681cfed6e91818024c0000081cfed6e91818024c37800000dcdafa2d2f046060093000001b9add45a734bd8c0126000003fb6e65e08c0ef18024c000006e6c516ea2d32a5e060000000dcd77a2d3104b860093000001b9ad645a6088c0c0126000003735e88b4c411818024c000006d68b4bc1181dc30049800000dcd6ea2d310460850c0000001b9add45a734ca970180000003735ba940ab11818024c000006e6bed1697825246049800000dcd6ea2d31046070893000001b9add5225e08c0c0126000003735ba8b4ca986230300000007f6f75b9add2f0300498000010356ea634a046060093000001b9ae945a5e08a8c01260000036b67cb751691818024c000007e8b7536178230300498000010396eac345a6c48c0c0000001d12dd45a5e09c8c0126000003cf5ba8b4bc11818024c000006e6bed1697828230049800000e896ea2d40a5e08c0c0000001b9add45a5e09e918126000003735baa14e211818024c000006e6b752ba2d44430049800000dcd6ea2d38646060093000001b9b4b45a6a88c0c0126000003735ba8b4bc11519224c000007e8b75169d929c300498000010d1b9a2d3ac46060093000001b9add45a86cbc0d21260000036e6428b4bc11818024c000006e6b751e17827230049800000fedc52dd2f046060093000001b9add478814bc11818000000434818f756ea2d18024c000006e6b754817823030049800000dcd6ea2d2f04e46b093000001b9add4a05848c0c01260000041f6e6b751694118024c000006e6b751698825c28849800000dcd6ea2d3044606f893000001dc3a245a5e08c0c0126000003745ba9251691818024c00000704b75169cd2f030049800000dcd6ea2d2f0460708c8000001e73734ae8b48c0c012600000396642b751697823024c00000704b75169782302f449800000e896ea2d30446060093000001b9add5868b4bc1181b60000042e6e68b4bc11818024c000007f6e6d6ea2d2f046060000000e616ea2d2f046070093000001dc3734785e08c0c0126000003735ba95d1511818024c000006e6d2d28156230300498000010c9b9b202f046060093000001b9b395ba8b4c411812600000434704c851697823024c000007f6dd56e97823030049800000dcd6ea2d3104605f893000002072d645a6c48c0c0126000003a75ba8b4d691818024c000006e6b751697825c30849800000dad6ea402f046060093000001dc36b4928b48c0c0126000003fb6e65e08c0ec18024c000006e6b7524a2a23030049800000dcd74a2d2f046060093000001b9add4786088c0c0126000003fb6e65e08c11018024c000006e6b7516a1a2f046060000000e496ea502f04606d8930000021a3735265e094918126000003c76e68b4bc11818024c000006fcba51697823030049800000df96ea3c30446060093000001fdb735ba5e0970c01260000037367cc516eacd45a24c000006e6b751697823032449800000e4977a2d2f046060093000002073216288b4bc0c01260000038a5ba9b0bc11818024c000007c0dcd6ea2d2f04d870800000dcd86a2d32a5e08c0c0000001fdb9b6e6b74bc11818000000373642b0d16978230100000006fcb751697823032449800000e5d6ea2d2f046060093000001c92dd45a5c08c0c0126000003735ba8b4eb9af2e024c000006e6b752c2052ac46060000000f81b9b0d45a5e09b093000001b9add5868b507978230000003735ba8b4c71181b624c000006f2c516ea2d2f030049800000dcd6ea2d2f052074893000002073145ba8b4ec8c0126000003c85ac8b4bc11818024c000006e6b591697823036c49800000dcd6ea2d31046060093000001b6add45a814bc118180000003fb6e65e09491818024c000006e6c1d66ac345a5e08c000000dcd6ea2d2f0460708bb000001b9add4b08b4e69a41260000037e5ba8b4c411818024c000006e6c858a22d2f04d8498000010096ea2d3aa5e0600930000021a40c736b7516918180000003735bab3561a2d2f0460000006e6b75169702302e449800000dcdaab0645a5e08c0c0000001b5add50a5e08c0c0126000003825de8b4bc11814424c00000738dcd83acd45a5e08c000000dcd86a2d2f04605d893000001dc3734b05588c0c0126000003735f6940bc1181b624c00000704b7516978272300498000010356ea2d3ae5c060093000001c12dd4805e0970c0126000003825ba8b502978230300000005ac925169e7230300498000010c9df2d62f046060093000001b9add45a6748c0e9108000003b86da8b4bc11818024c000006e6b75169cd2f04a449800000dcd6eac345a86cbc0c0000001ed2dd45a5e08c0c01260000037367cb751699523030000000868f75dc22d2f030049800000fedb9add2f046069093000001b9add4d85e0970c0126000003735ba9c8d897823024c000006e6b75169d93486548c000000dcd74a2d39046060093000001fa2dd4d68b4bc118126000003fb6e6c84bc11818024c000006e6bbd1697825c3a449800000dcd6ea2d2e64605c893000001b9b4b45a5e08c0c9126000003735ba9b0d5118126100000008730d1df17823030049800000e3d6ea2d32846060093000001b9add45a83cc7118126000003735f68b4b811818024c00000864ef91697823030049800000ea96ea722f04605c093000001b9b445ba8b48c0c01260000037363e8b4d811817024c000006e6c517a22d2f030049800000dcd6b22d41e5e08c093000001eeb6b45a5e0760c0126000003b87048b4bc11818024c00000752dad83a2d2f046049800000dcd8a2dd45a5e0850c00000021a3e0788a4cbc0c0126000003735ba98d2819523030000000752dad6ea2d2f0460498000010c96b1e72f046060093000001b9add45a6c08c0e91260000037363e8b4bc118126100000006e6b7566a2d31c46049800000dcd6ea462f046064893000001c12dd45a6088c0c01260000039c628c1d6ea2d2f0300000006e6b5966a2d2f046049800000dcda5a2d31046060093000001b9add5207588c0c0126000003735ba8b4bc1181c2144000007bae6db5add45a5e060000000e896ea2d2f04606d893000001b9add45a86cc70c0126000003aa5ba8b4bc12e17024c000006e6d2d49a2d3b230049800000dcd6ea2d2d24606d893000002193be6e65e08c0c0126000003735ac8b50d97818024c000006e6c351697823024c28800000dcd90b0745a5e0a7136000001b9adc45a5e0949181260000040e628b7561a2d2f030000000770dccbc16923030049800000dcd83acd45a5e0a7118000001c92dd4928b48c0c0126000003736028b4c411818024c000006e6b75169c42302e049800000dcd6ea3c2f04606d893000001b9add480654bc1181800000040e6e6b752f11818024c000006e6b753617823034849800000dcd6ea9344a76460093000001b9add45a654c6918180000003735488b4bc129230428000007f6dcd16978230428600000000018a2dd45a814bc0c0000001fdb7367cc516e8c0126000003736a88b4eb97018024c000006e6b75169782724a449800001039c92fb45a46060093000001fdb9c60e8b4bc118180000003735ba8b502978252460000007e8b75169a42f0460498000010395222d2f0460850c0000001d12dd45a83cbc118126000003735ba940d217823024c000007badad90a2d2f030049800000dcd6ea2d40a5e0a08c00000016eaad45a814bc1181800000037354c8b4bc11821430000000736dad169782303b060000000fedb9b075865e08c0c0000001dc37345a5e0949181260000040e628b591697818024c00000744b7566a2d2f046049800000dcd6ea3c41e5e08c093000001b9afb4928b48c0c012600000373642c651697825c24c000007f6dcd6eac32f046060000000dcd6ea8532a5e08c0c0000001b9af445a5e08c0e1180000003fb738dcd83978230300000006e6c856ea402f04b849800001071fdb9c5ba5e08c0c0000001fdb725ba5e08c0c0126000003735ba8b4c112923024c00000770dcd1697828230049800000db56ea2d2e446060093000001b9b435ba8b48c0c0126000003a25ba8b50d97818024c000006e6b7566a3c2f046049800000b755b22d40a5e08c0c0000001b9add45a6c08c0e1180000003be5f68b4bc11818024c000006e6c7d169782302e04980000103a01add4a046060093000001c92dd45a6a88c0c01260000037361a8b4bc118214300000006e6b753917823038451000000dcd8a30745a5e060093000001b9add4a05e88c0c0126000000006e6c7d3917823024c00000868ed91697823030049800000dcd6ea2d30450460093000001b9b145ba8b4bc0c0126000003735ba9c916978230384000007e8b752822d23030049800000f696ea2d3ac46060093000001b9aef45a734bc0c0126000003735ba8f10d97818024c000006e6b75151b123030049800000e3d6ea402f0460600930000015224945a460760c01260000037e628b751697818024c000007e8d2d169a42f046049800000e1d6ea2d31846060093000001c13215ba8b4c4118126000003735ba8b4eb9952e0300000006e6b7547a5844a30049800000dcd6ea2d39a5c060093000002073e05ba8b4a08c0126000003cb5ba8b4bc11818024c0000081cdcd6ea2d23036c49800000e096ea2d2f04606d893000001b9b565ba8b4eb8c0126000000007e8b751694118024c000006e6b75169cd36265460000000dad6ea2d2f04605c093000001fdb735ba6388c0c01260000040e738bed1691818024c00000714b75169a42f046049800000dcd6ea2d30c46060093000001fa2dd4b08b4e68c0126000003925ba940ab11818024c000006e6b751697825c38451000000dcd6ea9c45a5e088093000001fdb735ac5e08c0c0126000003735ba95d16a1423024c000006e6c353a22d2f046070800000001b9b1f45a5e0970930000021939c5ba5e08c0c0126000003735ba8b4ca94123030000000868fd16ea5823030049800000dcd6ea2d2f0454708c0000001b9add5869b0bc118180000003735ba8b4dc11818024c000006e6cf97a22d23030049800000fd1b9add4a046060093000001b9b0d45a5e0970a2126000003e079c8b4bc11818024c000006e6cf96ea2d23042860000000c516ea2d44a5e060093000001b9b1345a5e08c0c9126000003735ba8b4e697318024c0000081ab751697723030049800000dcd6ea634a06748c0c0000001f02dd4545e08c0c0126000003735f68b4d511818024c00000736dad90a2d2f046060000000dcd86a2d2f045460093000001b9aa445a5e094918126000003925f68b4bc14118024c000006e6c353617823038460000000fedb9b072f05388c0c0000001b9b215ba978bc118126000003f45ba8b4ec995230300000006e6b75169782303845f800000e719f3075ba8b48c0c0000001b9add45a654ab141180000003f45ba8b4d89181d224c00000744b751698823028849800000f816b24945a46060093000001b9ad645a5e09b0a212600000373642c1916978230300000006e6d2d8a22d2f030049800001039b9add45a75c600930000021a3be5265e08c0c0126000003825ba8b50797823024c000006e6b6d1697823030049800000dad169782303cc60093000001c72dd4785e08c0c01260000040e67cb7561a2d2303000000071cb751697823035849800000dcd6ea2d3485e097093000001b9afb4a05588c0c0126000003aa5ba9d11697823024c000006e6c35169b12f046070800000dcd77a2d2f04e460093000001ce3205ac8b4bc118126000003735ba918bc1181d224c000006e6b753618e23030049800000c855224945a46060093000001c12dd59a8b4bc118126000003735ba8b4ca11818024c000006e6bbd2017825c30049800000dcd77a2d40a5e08c0c0000001b9add45a6bcbb118126000003735ba9ad169d923024c0000081ab751691818024c37800000dcd6b26c2f046060093000001c12dd45a5e0970b8126000003fb6e6b8cbc11818024c00000642c51169e72f030049800000001b5a2d2f04a48c093000001b9af44805e08c0c0126000003735ba8b4b813918024c000006e6b751697823038460000000dcd6ea402f0460850c0000001b9add45a814b8118180000003fb744b74bc11818024c00000868ef91697825246049800000dcd6ea2d2f04607086a000001c12dd45a86cbc0c0126000003925d28b4bc11818024c000006fcb751697823038460000000dcd6ea402f046070893000001b9add454460600930fc000003735ba925169cd18024c000006e6c351697823030049800000dcd6ea6245a5e08c0c000000207356628b75168c0126000003ab738b753a2632f0460000006e6c351697823024c35000000f75b5ad645a5e060093000001b9add45a5588c0df126000003825de8b4c411818024c000006fcc351697823030049800000e496ea2d2f046064893000001b9add45a5e0a71331260000040d6e6b75169af23024c00000770dcd1697023030049800000b59169f02f046060093000001b9add45a5e0a08db126000003be5ba8b4e697818024c000006e6bbd1698223030049800000dcd53a2d2f0460850c0000001b9add45a6208c0a512600000373640c511697818024c00000744b753a22d2f046049800000e496ea2d31046060093000001fa2dd4a05e08c0c0126000003735ba900bc12e14424c000006e6b75169782303a448800000dcd83add45a720a70c0000001ce30754e8b4bc118180000003735e8a14bc11818024c000006e6c151697823030049800000dcd9f30745a46060093000001b9add50a5e08c10a180000003735ba8b4ca9782302e0000007e8b751694118024c37800000dcd9f2dd45a46060093000001b9add5a28b4bc118126000003a25ba9b0bc11818024c000006e6d2d1697823038460000000dcd6ea2d3b26908c093000001b9b1460c8b4bc118180000003735ae8b4bc11817a24c000006fccf96ea2d23030049800000dcd9cadd4805e08c093000002063705ba8b48c0c0126000003735ba978b811818024c00000744b751697826c46070800000dcd6ea2d31846060093000001b9add45a83cbc141126000003735f68b4bc11819224c000006e6b751697823038049800000e096ea2d31046051093000001b9add4ae8b502918180000003a261a8b4bc13623024c0000077cb711697823030049800000dcd6ea2d39a6a860093000001fdb9c2f0460760c0126000003735ba8b4ca9181b624c000005bab0d5224945a46060000000dcd6eacd45a5e0a0893000001fa2dd45a46060093100000003735ba8b50d97825224c000006e6b7524a2d27230049800000c516eac345a79cbc0c0000001b9add4928b502918180000003735ba960f39952303000000077ca911697823042860000000fedb6add2f046060093000001b9afb45a6208c0c01260000040e5baa911694118024c000006e6b75169952ee46060000000dcd6ea2d3104b874893000001c12dd45a5e08c0c2126000003be5ba8b4bc13918024c000006e6bdd1699323030049800000dad6ea2d38846060093000001df2dd45a814bc118180000004025ba8b4ec91818024c000006e6b756622d2f046049800000dcd6ea5e2f046051093000001cb2dd45a6208c0c0126000003735ba900bc11818024c0000077cc516b22d2f030049800000dcd6ea5039a55860093000001b9b065ac8b4bc118180000003fb704b74bc11818024c00000868dcd9022d2f046049800000ee1b9a4945a46060093000001b5b3945a5e08c0c012600000373696cf91691818024c000007c0e716ea934c65e060000000dcd8a2df45a5e060093000001b9add45a6348c0c0126000002a445a79cbc11821430000000714b752817823030049800000df96ea402f046060093000001b9b4b45a764d2118126000002dd5488a8bc11818024c0000081ab75169af2f046049800000001b9b2060c8b4bc11800000219373628b58bc0c01260000040d6e6d511691818024c000006e6b75169d732a30049800000ef9dc22d2f046060093000001ce2dd59ab0d16978230000003be640b751697823024c000007f6dccbc1181e230049800000dcd90aef45a6208c093000001b9aee45a5e08c0c0126000003735ba8b4ca9181801bc000006e6b7561a2d3485e08c000000c516b22d3ce5e060093000001b9add4bc6748c0c0126000003be5ba8b4c111818024c000006e6c35169d623030049800000dcd77a2d2f04606d89300000219373640b74bc118126000003735ba918c611818024c00000868dcd4997822030049800000fd16ea2d2f04b860093000001fdb9c6425e08c0c0126000003735ba8b4b81181b624c000006e6b75169aa27230049800000001d531f45a5e08c093000001c92fb45a6748c0c0126000003735ba8b5029aa230300000000010c9b9b5523030049800000dcd6ea852f046060093000001dc37045a5e08c0c0126000003735ba8b4ca979230300000006e6b75169952ec46060000000dcd6ea502f04b860093000001c12dd4d85e08c0c0126000003735ba8b4bc14817024c000006fcb754297823030049800000dcd6ea8f4d68b4bc093000001c52f445a5e08c0d212600000373696900bc11818024c00000868fedcdadd2f046060000000e0977a2d2f046074893000001b9ae94785e08c0c9126000003e0756b7549a742f024c000006e6b751697822a24c20000000dcd6ea6c2f046070840000001f02dd45a850bc118126000003b86e68b4d511818024c000006e6ba5169cd2f030049800000dcda922d3aa5e060093000001b9add45a690c7118126000000006e6b7531258230300000006e6b753122a2f046060000000dcd6b22d3485e08c093000001b9aef45a83cbc1181260000037361a9b0bc118126100000006e6b75169a32f046049800000fedb9add2f04a48c093000001b9add45a5e0970af126000003735baa711697823038400000752dcd83a2d2f046049800000e498a2dd45a5e060093000001b9b4b45a6548c0c00de000003735ba8b4eb97018024c000006e6d51169af2f046049800001009a922d2f046060093000001b9add45a734bc0c9126000003735ba8b50797023024c00000752dcd6ea2d2f046049800000dcd6ea2d2fc50460093000002073fb60e5e08c0c0126000003735deb351697823024c000006e6c354e22d2f046049800000dcd6ea2d39a6c460093000001b9aef45a5e0970b8126000003fb6e6b74bc14118024c000007e8b751697823034849800001039fdadd2f046060093000001b9add45e734bc0c0126000003735e88b4bc11817024c0000081ce496ea2d23036c49800000f75cdb735ba8b4bc0c0000001b9add59a8b4b8118126000003736268b4bc1181c2300000006e6b75169d531c30049800000dcd6ea2d2f0460850b8000001b9add45a734c40c0126000003735de8b50d97818024c000006e6d2d42978230300498000010d1b9b5652676460093000001b9add4a05e08c0d21260000040e7dcb751694118024c000006e6b75169b02302e049800000dcd6ea2d3ae5cc6009300000206b5445a5e08c0c0126000003735ba8b4e2195230300000006e6b751697822c30049800000e296ea2d2f04b8600930000021a37345a5e09b110126000000006e6b75391b023024c000006e6b751699d23036c498000010096ea2d31c46060093000002063dd5ba8b48c0c0126000003735ba8b50d97018024c00000868dcd90a2d31046049800000fd16ea2d3b2460600930000016eab245a814bc118180000003735ba9b0d895623024c0000067cb7561a2d3ce46060000000dcd6ea2d2ac504600930000021a3c845a5e08c0c0126000003735ba8b4bc12e24e24c000006e6b753917825c30049800000dcd7922d2f04b860093000001b9add4928b48c0db12600000373628bed1697818024c00000818f816ea2d23030049800000dcd6ea6c2f04a48c093000001fdb9c5bab0cbc118180000003a25ba8b4d217823024c0000077cb751697823036c49800000c516ea2d3e45e060093000001b9ae945a5e09c8c0126000003735d28b502978230300000006e6ba54497823030049800000dcd9f2df45a46060093000001b9add4d85e0a08c01260000040e6e6bed169181b624c000006e6d2d169cd36230049800000e718a30745a5e060093000001eeb736428b4bc0c0126000003735ba8b4d79952f0460000006e6b75361782303845c000000e0990b1945a5e08c093000001b9add478690bc1181260000040c752dad6ea2d23024c000006e6b75169d733a30049800000e718a2dd45a5e060093000001b9add45a584a08c0126000003735ba8b4bc12e18624c000006e6b751697827232449800000e0990add4805e08c093000001b9add45a5e0a4918126000003735ba8b50297823032400000000dcd6ea2d31046070800000fc96ea2d2f046060093000001c52dd45a5e08c0d2126000003735ba8b4bc14c252460000006e6b752915623030049800000e496ea2d2f0460708c0000001b9add4928b507918126000003735de8b4c411814424c00000000dcd86a2d31046049800000fd1a5a2d3b2460600930000020739c5ba8b48c0db126000003735ba8b4ab14b18024c000006e6b7516988272300498000010356ea2d32a5e08c0c0000001b9b4b45a558a08c0126000003735ba900c412e18024c000006e6b7516a0531046060000000dcd74a2d30446060093000001c930d45a5e08c0c0126000003b86e68b4bc11819224c000006e6b75389b12f046049800000ef96ea2d41e5e08c093000001b9add520764bc0c0126000003735bab3524a2d23024c000006fcba51698223030049800000dcd5228538846060093000001b9add45a5e08c0e1172000003735ba8b4d51181b624c000007e8b7561a2d2f046060000000e496ea2d2f05046d893000001b9add45a6088c0c9126000003735ba8b4d21952e046000000738a911697825246049800000ef96eacd45a5e08c093000001c52f445a6388c0c0126000003735ba92516a1b18024c00000744b752017823028849800000df96ea2d30446064893000001dc37345a6208c0c0126000003735ba8b4c111018024c000007c0b7516a052f046060000000dad6ea2d32a5e08c0c0000001b9b325ba8b4bc0c0126000003a25ba8b4d51181c2300000007e8b75169cd3485e049800000dcd6eac34a05e08c0c0000001b9b1f45a5e08c0bb126000003735ba940d797023024c000007f6dcd7797823030049800000dcd6ea2d2f04605c093000001eebb845a5e08c0c0126000003735ba8b4bc12e1a424c000006e6b75169782984d88c000000fd16ea2d2ac4606d893000001b9add45a620a71181d2000003735ba8b4f097822024c00000744c35169aa23030049800000dad1697825246076093000001df2dd45a86cbc0c0126000003e0632b7516a052f0300000006e6b751695b23036c49800000df96ea2d2f04605c093000002072dd5868b48c0c00de000003735f68b4bc1181c2300000007f6dcd6e97023030049800000dc16ea2d41e5e08c093000001b9add4a05588c0db126000003735baa4d3597823024c00000724cf96ea2d23030049800000f81dc22d2f046060093000001cdb736428b4bc1181800000040d5ba940b811818024c000007aaa9116a052f046060000000dc16eacd45a5e08c093000001b9add45a83cd5118126000003e0770c651697818024c000007e8b751698e23030049800000fd16b22d2f046060093000001b9afb45a5e0a08db126000003735ba978c411818024c000007acc196b22d2f04606000000107d8a2dd45a5e060093000001df2d650a5e08c0c0126000003825ba8b4d217823024c000006e6b754817826c44049800000dcd6ea5031c46060093000001b9add59a8b4d5118126000003b8752dad1697823024c000006e6b753917829c46070800000ef96d22d2f046060093000001b9b5445a654bc118180000003735ba8b4bb91818024c000006e6b592817823030049800000e0977a402f046060093000001b9aef4d85e08c0c0126000003735ba9d1169b132a4600000081cb591691818024c37800001039832dd45a5e08c0c0000001c52dd5868b4bc118180000003736968b4bc11817024c00000868dcd83a932f053860000000dcd6ea2d4366a860093000001b9af445a7108c0c0126000003735ba8b4c991818024c000006e6b75169c423042860000000fedb5b145ba5e060093000001b9add4d85c08c0c01260000037367cbed1691818024c000006e6b752017823029449800000dcd6ea5048e46060093000001c92dd4805e08c0c0126000003735ba8b4bc14e26c3a4000006e6b751697829c4b870800000ea5cdadd45a5e08c093000001fa2dd51e8b4bc0c0126000003dd6e6b591697818024c00000790ba516978230300498000010316eaa445a46060093000001b9ae945a5e08c0db1260000039c67cc1d1691818024c000006e6b75201782302e449800000dcd6c22d2f046060093000001ce33e5ba8b48c0c0126000003735e88b4c71181a424c00000724b751699523030037800000fedb9add49246060093000001b9b145b88b4bc0c0126000002d645a7b8bc11818024c000006e6d512817023030049800000e096ea402f046051093000001c52dd45a6388c0c0126000003735bab0d1697825c30000000714b591697823030049800000dcd8a2a445a5e0850c0000001b9add45a5d88c0c0126000003fb77cb74bc11818024c00000744b752817823030049800000dcd6ea2d2f046073093000001fa2dd4785e08c0c0126000003735f6900bc11818024c00000724b754297823030049800000dcd6ea502d246060093000001b9add45a6208c0db1260000036b6428b4bc13623024c00000738c5183aa445a5e060000000dcd8a2dd45a814bc0c0000001b9b1345a5e08c093080000003735ba900bc12e1d224c000007e8b755022d23030049800000e216ea2d2f046060093000001b9add45a72cbc118180000003735d28b50797823024c000007aadad1697823030049800000dcd6ea2d3485e0a0893000001b9b3e642c51168c0126000003aa5ba9c8bc11818024c000006e6c7d169b023030049800000f696ea2d2f04d888093000001b9add45a734bc0e1180000003755ac8b4bc11818024c0000081cd556b22d23030049800000dcd6ea2d2f04cc8c10a000001b9add45a5e08c0e117a000003d96e68b4bc11818024c0000077cb751697826c28849800000fd16ea2d2f646060093000001fdb7359a5e08c0ec126000003735f68b4ca9181801bc00000770dcd8a22d2f030049800000dcd74acd45a5e08c093000001ce3065ac8b4bc118180000003735ba9c4d691818024c000006e6c7d3922d2f046049800000dcd86a2d39a5e060093000001fdb705ba5e08c0c012600000373640c516ea2d2f024c000006e6b751698e25c30049800000dcd6ea2d3ae6c460093000001d3add4e25e08c0c0126000003735ba9b12491818024c00000704b75169882303a449800000dcd6b22d2f04b86009300000183aa445a814bc1181800000036b5e88b4bc11818024c000006d68b4bc1181fe30049800000fd16ea2d32a5c08c0c0000001b5add45a5e08c10a18000000373628b751698218024c000006e6b7561a2d2f04606900000103a01add45a50460093000001b9b215de900bc118126000002dd5488b502978230300000006e6ba516a1b2f030049800000dcdaab0745a46060093000001b9add45a5e8a08c0126000003fb6e6b74d511818024c00000754b751697825c30049800000dcd90ac345a5e08c0c0000001b9add45a83cc4118126000003735baa813199d2303000000077cb753617823030049800000dcdaaadd45a46060093000001b9afb50a5e08c0c0126000003736968b4bc91818024c000006e6b75281952e046060000000dcd6ea2d38846060093000001b9add45a720a70c0126000003735ba8b50d97819224c000006fcb75169c423030049800000dcd6ea2d32a4606007b000001b9add59a8b4c4118126000003ca6e68b4bc11818024c000006e6b751695e23036c49800000dcd6ea2d3104b85c093000001c92dd45a6748c0db126000004346e68b4bc14c23030000000714b751e17823030049800000dcd6ea5e2f046074893000002173734b08948c0c0126000003fb756dcd9097823024c000007c0b7516a0f2f046049800000dcd6ea2d2f04cc8a893000001b9b37628c1d169781800000037360eb754497829c300000006e6cf96ea2d39a30049800000e496ea2d2ac50460093000001b9add45a764e69a4126000003736a48b4ec91818024c000006e6b7516a1b31030049800000dcd6ea7445a6a88c093000001f03195ba8b507978126000003f46e6b751694118024c000006e6b751698e23034849800000dcd6ea6c2f046062893000001b9ad645a5e08c0d2126000003fb6d6cf96e91818024c000006e6b7531a2d33a50460000000dcd6ea2d2f04e4708c0000001b9add45a6bcbc11812600000373690b751691818024c000007f6dcd90acd2f046049800001039b9add4a046060093000001d12dd45a5e0970c0126000003735ba9b0d511818024c00000704b752817823030049800000dcd86a2d2f04e460093000001b9add45a5e09a0a21260000037361a8b502978230300000006e6cf98a2dd5868b460000000e7183aae45a5e08c0c0000001b9add45a6a89b1181c2000003736968b4e211818024c000006e6aad1697825246049800000dcd6ea3c2f04b860093000002073145ba8b4d88c0126000003a9738b751697823024c000006e6c7d1697823030049800000dcd7da2d33a4606d893000001dc37345a5e08c0e11800000037361a8b4d513623024c0000081ab751697823030049800000dcd7da2d2ac50460093000001b9add480734bc0c0126000000005ac9251691818024c000006e6bbd169a42f046049800000dcd6ea2d2f04cc8c093000001b9add45a6088c0e1180000000006e6b75169d735e24c000006e6b7516a132f046049800000dcd9f2a445a460850c0000001b9add454460600930de000004346e6c852017823024c000006e6b75169a42e046049800000dad83a2d2f046060093000001b9b0d45a6088c0c0126000003735ba8f0bc12018024c000006e6b75169e12f046070800000f816ea5844a46060093000001b9b3e5ba8b49c8c0126000003fb6e6ba4bc11818024c000006d6b751697823030049800000dcd6ea2d362690ca918000001ce33e60ea9116918180000004346e6c1916978230300000006e6cf96ea2d40a46060000000fd16ea5845a6908c093000001b9add45a734ca8c00de000003736d68b4bc12923024c00000868dcd4297825246049800000dcd86a2d3c25e08c093000001b9b145ba8b4bc0db126000003a25ba8b4bc1181a424c000006e6bd1169952f046060000000dcd9f3145ac8b4600930000000040d5ba8b4eb8c0126000003735baa093a178230384000006e6b7535a4945a46049800000fedb9add2f046064893000002193e06e6c80bc118126000003925ba8b4bc11817024c000005ac8b4fb17823030049800000ef9832dd45a5e08c0c0000001fa2dd45a5e094918126000003be5baa14bc12923024c000007b4b7549a2d2f030049800000dcd6ea3c2f046069093000001b9add45a6208c0c21260000037360096cbc11818024c00000770dcd9f22d23030049800000dcd6ea8539a5e060093000001cc2dd45a5e08c0c01260000039c6e6b7531a222f030000000628b7524a2d3ce300498000010c9b9b065ba5e08c0c0000001b9add4a05e094918126000003f45ba8b4bc14118024c000007f6dcd6e98823030049800000001b9add4805e08c0e1000001b9add5868b4c7118180000003a25ba8b4bc11818224c00000848dcd6e97823030049800000dcd6b2c345a5e08c0c0000001b9b216288b4bc0930800000040e642a91169b123024c000006e6b7540a2d2f046070800000fedb9add59ab0cbc118000001b9aef4805e08c0a2126000003735ba8b4d41952f046000000864f81e217823030049800000dcd6ea502f0504600930000000037361a900bc118126000003736a88b4bc11818024c000006e6c196ba2d2f046060000000e6db6add45a5e08c0c0000001b9add45a7209991812600000373628b7516a0f2f024c0000072ab752d97823030049800000dcd6ea903625e08c093000001b9add4805e09c8c0126000003735ba9391691818024c00000868f75cdadd45a5e060000000dcda922d31c46060093000001b9ae94d85e08c0c01260000037361aa051697823024c000006e6b75202052f046060000000dcd6ea902f05308c0c0000001dc3734928b5029181800000036b6968b4bc11818024c00000704b751697825c30049800000dcd8a30759a8b4bc093000001c92dd45a5dc8c0c0126000003735ba8b4bc14723024c000006e6bed169782302e049800000dcd6ea2d32a6008c0c0000001b9b145bab35169781260000040c752dcd6ea2d23024c000006e6b753617823032449800000dcd6ea2d2f04b870840000001fa2dd45a7848c0c012600000373640c651697823024c000006e6b754517823030049800000db98a2dd45a5e060093000001dc3734805e08c0c0126000003735ba925169a423024c000006e6c81832d645a5e08c000000dcd86a2d2f04b849840000001c12dd4806208c0c0126000003735ba8b4bc1361d838400000000dcdaa22d3ae30049800000fedd4b6b5ba5e08c093000002073dd5ba8b4bc0c0126000003735ba900bc14e2303a4000006e6b591698e23030049800000dcd6ea6c31046060093000001b9aa450a5e08c10a180000003735ba900c111818024c000007c0b7549a252f030049800000e296ea2d2f04a48c093000001df2dd45a690bc118126000003735ba8b4bc11819024c000006e6c351697826c44049800000dcd6ea2d2f0460708db000001b9aef45a6208c0e9126000003f45ba8b4ec9cd18024c000007b4b753a22d2f046049800000dcd71ac345a5e08c0c0000001b9add45a6f4d8995230000003be6aab591691818024c000006dac851697823030049800000dcd6ea502f052c60093000001b9add50a5e09c8c0126000003735ba8b4bc12e22024c0000077cb59169c423030049800000f81b9add4e25e060093000001b9add50a814bc118180000003735ba940ca91818024c000006e6bdd1697823030049800000fedb9b214e85e08c093000001c52dd45a5e0a08c01260000037361a8b4bc1181b624c00000744b7561a2d2f046060000000001b9add45a6548c0db000002193736aab588c0c0126000003825ba8b4bc1181a424c000006e6b751699523030042000000dcd6ea2d32a5e08c0c0000001b9b145b48b4bc0c0126000003f45baa051691818024c00000744c351697823038460000000dcd6eac34785e08c0c0000001bf2dd45a654bc118180000003555ac8b4f391818024c00000770dcd4297823030049800000dcd6ea722f0460708b8000001b9add4b65e08c0c0126000003735ba9d1129b123024c00000864dcdaaa2d23030049800000dcd7c22d2f046069093000001b9b605ba8b4bc0c0126000003735ba8b4bc12e25224c000006e6b754298223030049800000dcd90add4e45e08c093000001b9add45a83cbc1181c2000003735ba8b4d51a423024c00000812dcd6e97823030049800000dcda2add45a5e08c0c0
  | 8 => 0x21a3c46e68b4bc11818024c0040e6e6b752c225230300498006e6b751e1782ac46060093000dcd74a2d2f05388c0c0126001e23735ba9251691818024c0038a5ba8b4bc11818024c09800000dcd6ea2d2f04605d893000e896ea2d2f04606009303e00222b735ba8b4bc11818024c0037367cc1d16978230300498006e6b751697023030049840000dcd6ea2d2f04606009311e001b9adf5488b4bc11818024c003735ba9611697825246049800770dcd169e72f046060093000f81ce3195ba8b4bc0c0126001b9b3e5ba8b4bc11818024c003735bab2916978230300498008a4dcd6ea2d2f0460600930010d1b9ae945a5e08c0c0126001b9add5269d0bc11814424c003735ba8b507a052f0460600006e6b751697823032459893000dcd6ea2d2f05388c0c0130002073735ba8b4d891814424c003e06f6b7516978230300498006e6b75169d93485e08c093000dcd6eaa045a5588c0c0126001b9add45a5e0970c0126098003735ba8b4bc14e230324498006e6dcd6ea852f046060093000f11df2dd45a5e08c0c0126001b9add45a5e0760c016624c003736acb751697e230300498006e6b7549a632f053860093000dcd6ea3c2f04606009303e001b9add4a05e0a08c01261bc003fb6e6b74bc11818024c068007e8b7531a2d2f046060093000dcd6ea2d3185e08c0c0126001dc3ab6e68b4bc11818024c003fb6e6d596e978230300498006e6b75169e730446060093000001b9b215ba8b4bc12e126001b9add4b08b4bc14118024c003735e88b4c711818024c2b800000dcd6ea502e0460600930010d1b9add45a5e08c0c9126001b9add45a674bc13918024c000006e6d2d169952f0460600006e6b755fa2d2f046060093001039b9add45a460600930e2001b9add45a5ecab11818024c003735ba8b50299d2f04606000081cfed6ea2d2f046060093000fd16ea2d39a5e08c0c0126001fa2dd45a5e08c0c018024c003735f68b4d8978230300498006e6b751697823030049855000dcd6ea634a05e08c0c0126001b9add45a5e0970c0126028003b86e68b50797823030049800714e296ea2d2f046060093000dcd6ea744c65e08c0e9126001d5b735ba8b4c111818024c003735baa3916978230300498007f6dcd83add2f046060093000dcd6ea2d3105388c0c0126001b9add5269b0bc11818024c000007f6dcd8a2dd2f030049800834e716ea2d2f04606009300100dbcadd45a5e08c0c0126001fdb735bab74bc11818024c0040e806b75169d9230300498006e6b7524a2d40a5e08c0c0000dcd6ea2d32a5c0ab118180001b9b395ba8b4bc118126118003735ba940bc118180300498006e6b751697824846060093000dcd6ea2d3b25e88c0c01260022c3735ba8b4bc11818024c004346e6b751698823030049800782dcd6ea2d2f046060093000dcd6ea4545a5e08c0c01260000038f5ba8b4bc11818024c003735ba8b4bc12e18024c0980072cb75169b12f046060093000dcd6ea2d3b25648c0c0126001b9add45a5e08c0a21261000041f6e6b75169b1230300498006e6b75169e536246060093000fd16ea2d39a5e0ab0c0126001dc37345a674bc11818024c0036b6d6b751697823030049800724b751697823030049801000dcd6ea2d2f0460600930f8001b9b0b5ba8b4bc11818024c0040e5baa991697823030049800000dcd9f2dd59a8b48c093001039fdb735ba5e08c0c0126001b9add4805e0bc11818024c003b86e692516978230300498006e6b751699d30446060093000dcd6ea2d33a460600930ee001b9b215ba8b4bc11812610c003c46e6b75169aa230300498006e6b751697823034849826000dcd6ea2d2f04d88c0ad126001c12dd45a5e08c11818024c003735ba8b4bc1181802bc498006e6b75361782303004980d000e496ea2d2f0460600930fc001b9af55ba8b4bc11818024c003736acb7536178230300498006e6b752c22d2f052c60093000dcd6ea2d39a5e060093126001b9add4b08b4ca91818024c000006e6b751697829030049800704c656ea2d2f046060093000dcd6ea2d388460760c0126001b9add45a690bc11812606c004036e6bd1169782303004980083ef816ea2d2f046060093000fd1b9add45a7648c0c0126001c92dd5488b4bc11818024c004036e6b7516978230428600006e6b75169782303484980a000dcd6ea2d2f04606009308c001b9add45a654bc118180008003735ba8b4ca978230300378006e6b7561a2d2f046060057000dcd83add4d85e08c0c0126001b9add45a5e08c0c0126030003735ba98d169d933a460600006e6d596ea2d3b253860093000e096ea2d2f05588c0c0126000003875ba8b4bc11818024c003735ba9251691818024c20000714b7531a2d2f046060093000dcd7a22d2f0460690c0126001b9add45a5e08c0c015424c00434752dad6ea2d2f0460498007c0dcd6ea2d39a5e060093000f41b9add45a5e08c0c0126001b9add5ba9b0bc11818024c004446dab751697823030049800000dcd6ea5033a46060093000dcd6ea2d33a46060093114001f03735ba8b4bc11817a24c003c96e6b751697823030049800806e7183add45a5e08c0c0000dcd7a22d2f046060093000001b9add45a5e08c0d212604c0038a5ba8b4bc118180300498006e6b751697829c4d860093000dcd6ea6c2f04d88c0a2126001b9add45a5e09d91818024c003735ba8b4bc118214300000006e6bed1697823030049801000dcd6ea7445a734bc0c0126001b9b185ba8b4bc11818024c003be5ba8b4bc11818024c20000880dcd6ea2d3b246060093000f25bf2dd45a5e08c0c01260020cb8a5ba8b4bc11818024c003825ba8b4bc11818024c0f8006e6b75169fb2f046060093000fa1b9add45a5e094918126001b9add50a5e0bc11818024c0043c6e6b7516978230300498006e6c516eac345a5e060093000dcd86add45a5e09b118126001b9add45a764d89181d224c003735ba8b4bc1181b636c4980081cdcd6ea6c2f0460600930010d1b9b214e88b4bc118126001b9b075cc8b4bc11818024c000006e6bbd1697825c300498006e6b75169c423030049807000dcd6ea2d3884a48c0c0126001ce373628b751697818024c003735ccb7516978230300498006e6b75169db2f046060093000dcd6ea6845a5e08c0c0126001b9add45a5e08c0d418024db9b215baa4d169d92f0300498006e6b751697823030050093000dcd8a2dd45a5e0748c0126000003735e88b4bc11818024c003735e88b4bc11818024c180006e6c515222d2f03b060093000001b9add45a5e08c10a180002073735ba8b4ec94e18024c003735ba8b4bc11818024c028006e6b751697823042860030000001b9b0045a5e08c0c0126001c53735ba8b4bc1181a424c003735ba8b4c711818024c2b8006e6bed5222d2f046060093000dcd6ea2d2f046051093098001b9add45a79cbc1181b624c003735ba8b4bc11817028849800000dcd6ea2d36046060093000dcd6b22d2f0460600930ae001b9add4c68b4bc12e18024c003735de96116978230300498006e6b7549a2d2f0538748c000107db9add45a460600930fc001b9aa445a5e08c10a18024c003736c8c3516978230300498006e6b75281702303004986f000dcd6ea2d45a5e08c0b8126001b9b0345a5e08c0c0126228003e06e6b7116978230300498006e6c1d6ea2d2f05388c0b8000b755222d3e45e08c0c0126001b9add5aab0d16978230300003735ba8b4eb9782e0300498006e6b751697829c4606009c000eadb9add45a5e08c0db126001b9add45a5e08c0c318024c003735ba8b4bc12e180300498006e6b75169782524608c093000dcd6ea5845a5c08c0c0126001b9add4b08b4d215623024c003735ba8b4bc13918024c498006e6b751697823030049869000dcd6ea2d36255c8c0c0126002153735ba8b4bc11818024c00373642b75169c4230300498006e6b75169cd3625e060093000e7183aa445a5e08c0c0126001f03735ba8b4bc11c18024c003735ba8b50297823030049800772dcd6ea2d2f046060093000dcd90add45a6c4ce918126001b9add45a5e08c0ed18024c003735ba8b4d511818024c200000010396eac345a5e08c0c0000001caadd45a5e08c0c0126001ce2dd5488b4bc11818024c003e0756c856ea2d2f0460498006e6c656ea2d2f04a48c093001061c92dd45a5e08c0c0126001b9aef45a5e08c0c012610c003925ba8b4bc11818024c02000000dcd6ea7445a5e08c0e1001111b9add5265e08c0c0126001b9add45a5e0a091818024c003735ba8b4e213623030049800000dcd6ea2d3505e08c0930010d1b9b2145a6c4bc118126001e23735d28b4bc11818024c003e06e6b7516978272300498006e6b7561a2d2f046060026000dcd6ea2d2f055894918126001b9add45a6f8d511818024c003e06e6b7516a052f046060000850dcd6ea2d35446060093000dcd6ea2d3605e08c0b8126001b9add45a5c08c0c012610c000006e6b751697825c28849800000dcd86a7445a5e08c093000e296ea2d2f04e48c0c0126001b9b195ba8b4bc14118024c0037363e8b4bc14e2302e0498006e6dcd6ea2d2f04605c093000dcd6ea2d33a5e08c0db126001f0373628b591697818024c003b86e68b4bc11818024c498006d6b75169782303b060093000001b9add45a5e08a8c0126001b9add4e88b4bc13918024c003735d2ba516978230300498006e6b7516a0f3ce5e08c093000001b9add4d85e08c0e1180000003fb6e6cf96e91818024c003f45ba8b4ec978230300498006e6b753a22d40a5e08c0c0000dcd83add45a5e08c0c0128001e23735ba8b4bc11819224c00413704b7516978230300498006e6b75169782ac50460093000dcd8a2dd45a5e0a70c0126001b9add5868b4bc118180028003735ba8b4bc12923024c0f800868dcd6ea933b25e060093000dcd6ea4445a5e08c0c0126001b9afb5ba8b4bc1181b624c003735ba8b4c111818024c49800000dcd86a6c2f046060093000eadb9add45a83cbc11812600225b9c5ba8b4bc11818024c003735ba98d16978230348498006e6b75281d92f046060093000f81dc37345a5e08c0c012600201b735ba8b4bc11818024c003735d2b7516978230324498006e6b7566a2d3ce5e08c093000f81b9b205ba8b4bc118126000003735ba8b4bc11817e24c004346e6c516ea2d2f0300498006e6c858a2a445a5e06009300100dbf2dd45a5e08c0c0126001b9add5868b4bc11818004c003735ba7f8bc15623030049800744b751697823030049857000dcd6ea2d2f05046009303e001b9add45a5e08c0d218024c003735ba8b507a0f2f046049800788dcd6ea2d31046060093000ee1b9a7445a5e08c0c0126001f6b735ba8b4bc11818024c003735ba8b4bc1181a424c350007c0dcd6ea2d30446060093000eadb9add59a8b4bc118126001b9add4ce8b4bc11818024c0000081cb5916978230300498006e6bed1697823030049804000dcd6ea2d43679cbc0c0126001b9add45a5e08c0c0126000000006e6b75169b12f046070800738dcd6ea2d2f0460708c0000fa9b9add45a5e0970c0126002072dd54e8b4bc11818024c003735ba8b4c711818024c130006e6b753a22d2f05388c0e9000dad6ea2d2f04606009300e001f73925ba8b4bc11818024c003735ba8b4bc11814424c218006e6b75169782303a4708c0000dcd6ea2d2f05748c0c0126001b9add4e88b4c111818024c003735ac8b4bc11818024c130006e6b752819d2303004986f000dcd6ea3c2f0460600930ae001b9add45a5e0a591818024c0037e5ba8b4bc11818024c000006e6b75169e12ac46060093000dcd6ea2d41e674bc118126001d5b735ba8b50d97818024c003735ba9611699d23030049800000dcd86a2d3625e08c093000e71b9b0d45a5e08c0c0126001f03c45ba8b4bc11818024c0037361a8b4bc1181d2300498006e6b7549a2d3485e08c093000dcd9badd45a5e08c0c0126001b9add45a6c4bc13918024c00373666b7516978282300498006e6b75169cd2f057860093000dcd6ea2d39a5e060093002001b9add45a85cbc11818024c003735ba8b5029b12f0460600006e6b751698e2303004980a000dcd6ea9f45a5e08c0c0126001b9add59ab351697823024c003735ba8b50da0f2f0300498006e6b7524a2d41e5e08c093000dcd6ea584928b48c0c0126001b9ad645a5e08c0c0126028003735ba8b4bc118182300498006e6b7566a2d33a5e08c093000001b9add45a5e08c0c0126001da3735ba8b4bc11818024c003735ba8b4bc11818024c180007c0f118cadd45a5e060093000dcd9d2dd45a5e08c0c0126002073735ba9ad1697823024c003735ba8b4ea9782d230049800000df96ea2d2f046060093000dcd74a2d3045e08c0c0126001bf2dd45a5e08c0c01260c0003735e88b4bc11818024c01000852f816ea2d2f046060093000dcd6ea2d2f04606c0c0126001b9add45a764e695618024c003735ba8b4c711818024c098006e6bd1169782303004986f00107d6eaa445a5e08c0c0126001b5b215ba8b4bc11818024c003735ba8b4bc118214300010006e6b75169782304286006f000ef96ea5845a5e08c0c0126001b9ad645a5e08c0c012604c004036e6d2d16978230300498007e8b75169782303004981b000dcd6ea2d436674bc0c0126001c52dd45a764bc11818024c003b86e68b4d89782303004980081cdd96ea2d2f0460600930010096ea2d2f05a48c0c012600215b735ba8b4bc11818024c0037367cb7561a2d230300498006e6b755222d39a5e060093001145b9ada45a5e08c0c0126001b9add45a608bc11819224c0036b5ba8b4bc136230300498006e6ba51697823030049840000dcd6ea2d34c5e08c0c0126001b9add45a5e08c0d2126168003735ba8b4d897829c460748006e6b75281782303004981b000dcd6ea4945a86cbc0c0126001dc3735ba8b502978230300003735ba8b4d217823024c068006e6b75169b1304460600930010d201b6b5ba5e08c0c0126001ce37367cb751691818024c003736acb75169a42f0460498006e6c0d2c22d2f046060093000dcd6ea2d2f04606009303a001b9b4b45a5e08c0c0126000003735baa0516956230300498006e6c716ea2d2f0460600930010d1b9ae045a5e08c0c0126001b9add45a5e09f11818024c003735ba9d916978230300498006e6b7516978230384600b3000dcd9f2dd45a460748c0126001e9b925ba8b4bc11818024c003735ba8b4bc1782302e0498006e6cf95222d2303b060093000dcd6ea2d2f046064893080001b9add45a5e0a71181c2300003735ba8b4bc139230348498007f6dad6eaa42f046060093000e29b9add45a6388c0c0126001b9aef45a5e08c11818024c003735ba8b4bc11818024c458006e6c1d6ea2d3485e08c093001039f02dd45a6c48c0c0126001d12dd45a5e08c0c0126098003735baa0116978230300498006e6b75169782303004986c000fc5b9add45a5e08c0c01260020739c5ba9611691818024c003735ba8fd1697823030049800868dcd6ea2d2f0460708c0000dcd86a2d2f05388c0c0126001b9add5ba8b4d217823024c003b8770dcd1697823030049800000fd16ea2d36246060093001145b9add5268b4bc0c0126001b9add45a5c08c11818024c00373632bbd16978230300498006e6b7561a6345a5e08c0c0000dcd6eacd5648b4bc118126001b9add45a5e09b11918024c00373628b7561aa445a5e0600006e6d556ead645a46060093000dcd6ea5e3625e08c0c0126001b9add4c68b4d797023024c000006e6d2d16978230300498006e6b751698823030049840000dcd6ea2d2f0460600930720021a37361a8b4bc11818024c003735ba8b4ca9782303b0600006e6c296ea2d2f04606009300103a01b565ba8b48c0c012600225c346e6b74bc11818024c003736968b4bc11818024c180006e6bbd6ea402f046060093000dcd6ea3c2f04606009304c001b9add45a8948c0c01261bc003735ba8b4ec97825c300498006e6bbd169782ac46060093000dcd6ea2d326460600930ce001d12dd45a5e08c0c0126028003735ba961169aa230300498006e6c656ea2d2e046060093001169b9add45a5e08c0c0126001bf2dd45a5e08c0c01260e400373642ab916978230300498006e6b7561a2d2f0460600c0000dcd6ea2d2f04e460093002001ce3735ba98d16978230300003735ba8b4d7970230300498006e6b7540a2d2c246060093000dcd6ea2d2f04606d893126000003735ba8b4e411818024c003735ba8b4e2118180288498006e6b75169b133a460510930000020636b5ba8b48c0c0126001b9add45a814bc1181800040040e6e6b75169a42f046049800704b751697823030049857000dcdb2b145ba8b4bc0c0126001b9add45a5c0ab11818024c0040a6e6b751697823030049800000dcd6ea462f046060093000dcd6ea2d45a7108c0c0126001d5b735ba8b4bc11818424c003fb6e6b74f397823030049800000dcd80a2d2f046060093000dcd6ea2d39a690bc0c0126001d12dd45a5e08c0c012604c003a25ba8b4bc1181c2300498006e6b751e1782303004980a000dcd6ea2d2f05dc8c0c0126001b9aef45a5e08c0c012607c003735ba8b4d89952ac460600006e6b751697823646060093000dcd6ea2d354460600ad126001b9add4c08b4c411818024c003d36e6bed16978230300498007c0dcd6ea2d2f04606d8930010356ea6345a5c08c0c0126001ce3735ba900bc11818024c003f45ba96116956230300498006e6b751695623036c60093000dcd6ea3845a5e08c0c01260021a37345a5e08c0ee18024c003735ba900bc1181d230049800714b75169782303004981b000dcd6ea5845a56c8c0c0126001b9add45a764bc12018024c00373660b7516978230348498007f6eadb9add2f046060093000dcd6ea2d2e04606009303e001dc37345a5e08c0c01260040037367cb751694e230300498006e6ce56ea2d2f05388c0c0000dcd6ea7445a5e08c0db126001b9add4785e08c0c012604c003735ba8b4ca978230300038006e6b755222d2f04e460093000dcd6ea2d3265e08c0c0126001b9add45a710bc118214300003735ba9d1169aa230288498006e6b75169cd2f030049804001111b9add45a5c08c0c0126001b9add5488b502978230300003736cec1d16978230300498006e6b75169a22f046060093000dcd6ea6345a6388c0c01260021a37367cb751691818024c0040e6e6b751697a230300498006e6b5931a2d2f046060093000dcd6ea2d30446060093002001b9b675ba8b4bc11818024c00373628b595222d2f0300498007c0b7524a2d3ce46060093000dcd9f3215488b48c0c0126001b9b4b5ba8b4d217823024c003736e6b75169c4230300498006e6b751697823030049865000dcd6ea2d31c460600c0126001b9add45a83cbc11812624c003e877cb7516978230300498006e6b591697823030060093000dcd6ea6c354460600a2126001fdb735bab34bc11818024c004196e6b751698e23030049c0e6e6b7549a2d36246060093000dcd6ea2d3b25e08c0d2126001e2373628b751697818024c003fb6e6b74ce978230300498006e6b751697823030049802001059b9add45a5e08c0c0126001b9add45a5e08c0c01261bc003b86e6a9116978230300498006e6b7524a2d3e046060093001039b9add4a08b48c0c01260021fb735ba8b4e211818024c003735ba9b1169aa23030049800756dcd6ea7445a5e08c093000df96ea2d2f046060093004001b9b0d5ba8b4d511818024c003735bab351697823024c498006fcb75169782303004986f000e719f2dd45a5e08c0c0126001f03735ba8b50797823024c000006e6b75169d6230300498006e6c856ea2d32a5e08c0c0000dcd6ea6c3ce5e08c0c0126001ce3735baa14bc11818024c004596e6b7516978230300498006e6b751697825c3004981b000001b9add45a888bc0c0126001dc37345a7a8bc11818024c003735baa9116982230300498006e6b751697823033860093000ecdb9add45a5e08c0db126001b9add50a5e08c0e918024c0038a5ba8b4c7178230300498006e6b753a22d41e5e08c093000dcd522852f0460760c0126001b9add4928b48c11818024c003735ba8b4ca97826c460600007c0ed56ea2d2f046060093000002073735ba8b4a08c0126001b9add45a65cbc11818024c003735ba8b50d97818024c498007c0dcd6eacd45a5e08c093000dcd6ea2d3625e08c0db126001d5b735ba9b0bc11818024c003735ba8b4c411818024c260006e6b752c2312f046060093000dcd6ea2d2f25e08c0c0126001b9add45a5e0bb11818024c003735ba900bc14e230300498006e6b754e2632f046060093000dcd6ea2d3626a88c0a2126001b9add45a5e09491812615c00373632b7524a2d23030049800704b751697823030049826000dcd6eacd4e88b4bc118126001df2dd45a5e08c11818024c0037361a8b4bc11818029c4980083edcd6ea6345a5e08c0c00010d1b9add4805e08c0c0126001b9add45a5e08c0c01261b4003735ba8e916978230300498006e6cd96ea2d2f046060093000dcd83aab45a5e08c0c0126001f03735ba8b50d97818024c003736a898d16970230300498006e6b7534a4945a46060093000fd16ea9345a5e08c0c0126001b9add4928b4ab11818024c003735ac8b4bc11818024c1b800000e0990add45a5e08c093000dad6ea2d2f0460600a2126000003ce6e68b4bc11818024c003735baaad16978230300498006e6b751697828230049857000001dc36b45a5e08c0c0126001df3195ba8b4bc11818024c003735ba8b4bc1181be300498006e6ba52c22d2f046060093000001b9add4545e08c0c0126001b9add4e88b50d97818024c003a25ba98d1697823030049800704b75169782303004980a000dad6ea2d45a5e08c0c0126001b9add526940bc11818024c003735baa4d3a1782303a4498006e6b751697827230049804001039b9add45a6c48c0e9126001b9add4d8674bc11818024c003735baacd16978230300498006e6b751697823037c49880000ef96ea2d2f05588c0c0126001b9add45a814bc118180010003735ba9b0bc11818028c498006e6b75169cc38846060093000dcda5a2d2f046060093004001b9add4928b48c0c012607c0038a5ba8b4bc13918024c2b80081adcd6ea2d2f046060093000dcda5a2d2f0460600930de001d12dd45a5e08c0c018024c0038a5e8b7516978230300498006e6b752c22d2f046064893000001b9add45a620970c0126001b9add45a5e0949181e624c0044d6d6b751697823030049800000dcd6ea2d39a654bc0c0000dcd6ea2d31c4e48c0c0126001c12dd45a5e08c0c012604c003735ba98d1e178230300498006e6b7549a832f046060093000dcd6ea2d3b2674a70c0126001b9add45a83cd897823024c003735ba8b4bc1181a424c0d8006e6b753ca2d2f046064893000ef96ea2d2f04606009303e001f03735b48b4bc11818024c003735baa14bc14e230300498006e6b751e1782303006009381cdcd6ea934e85e08c0c0126002253e06e6b751697818024c003f45ba8b4bc11818024c068006e6b7549a6333a5e08c0c0000001df2d645a5e08c0c0126001b9b6b60e8b4bc11818024c003b86e68b4bc11818024c020006e6b751697823035860093000fd1ab2dd45a5e08c0c0126001b9b3e5bab0d5222d230300003735ba8b4bc11818024c3a8006e6b752c22d31046060093000dcdaaadd45a5e08c0c0126001b9add59a8b4d897823024c003736d6b751697823030049800868dcd6ea852f046060093000dcd6ea2d3885e08c0c0126001b9add45a6a88c11818024c003735ba8b4bc16223030049800788dcd6ea2d2f0460708c0000e496ea2d2f05048c0c0126001b9add45a6c4bc11814624c00373628b751697818024c2000081cb755222d36246060093000dcd6ea502f04606009301a001b9add45a5e08c0e9126100000006e6c4d16978230300498006e6b751698223030049804000002193735ac5e08c0c0126001b9b565ba940bc11818024c003f460eb7516978230300498006e6b75169782303004b09300107a072dd45a5e08c0c0126001b9b6567cb751691818024c003735bab0d169d92f0460600006e6c656ea2d35446060093000dcd7a22d2f0460760c0126001e237361a8b4bc11818024c003735ba94116978282300498007e8b756ea2d2f046060093000dcd6ea2d2f04606d893002001b9add45a86cd897818024c003735ba8b4bc11818024c410006e6b7516978230428760c0000dcd90add45a5e08c0930a2001dc3735ba8b50797823024c003735ba8b4d21952f0460498006e6b75169782303004980f0000016b22d3ce5e08c0c0126001f03735baa4d1697818024c0037360eb7528178230300498006e6b75169aa2ac46060093000dcd6ea6345a654b8118180002093735ba8b4bc11818024c003735ba8b4bc11818024c14000760dcd6ea2d2f046060093000dcd6ea2d2f046060093020dcd90add5268b4d897823024c003735bab7528178230300498006e6b751697825246049826000e296ea9345a5e08c0c0126001cc3735ba8b4bc11818024c004126fcb7516978230300498006e6b753a22d3545e08c09300100dc92dd45a5e08c0c0126001b9add45a638bc1181a424c0040e7e8b751697823030049800712dcd6ea2d2f046060093000eadb9b216328b4bc118126001b9add45a6a88c0c012607c00434752dcd6ea2d2f0460498006e6b754da402f046060093000f81b9add45a5e08d0c0126001b9add45a5e08c0ef18024c003735ba8b4bc14118024c130007f6dcd6e97823030049893000dcd6eaa445a5e08c0db126001b9add4c6960ab11818024c003735ba8b4bc12923024c050006e6b75169782303004982c000dcd6ea2d388460788c0126001b9add47c8b4bc11818024c003b86e6b7516a1b2f03004980081cdcd6ea502f0460600930010edb9add45a5e08c0c0126001b9add4d86a8bc11818024c003735e88b4bc11818024c038006e6b754122d2f046060093000e496ea2d2f046060093000001b9afb45a5e0a091818024c0036d5ba98d16978230300498006e6b75169b029c4605c093000dcd6ea3c2f046060093062001b9add45a5e08c10a18001df03735ba9d131978230300498006e6b751697827046060093000001c12ef45a5e08c0c0126001b9add45a5e094918214300003735ba9d116978230308498006e6b7516a0b2f046060093000f11b9b3e5ba8b48c0c0126002073735ba8b4a08c01261bc003fb7c0dcd6e978230300498006e6b75169d931c46060093000e1d6ea2d2f04d88c0c0126001b9add45a83cbc118126004003826e6b751697825c300498006e6b752c22d2bc46060093000dcd6ea2d2f04a48c093026001b9add45a5e0a08c0126028003735ba8b4bc11816624c200006e6b59169d92f046060093000dcd6ea2d33a5e08c0c0128001b9add45a5e08c0c012e24c0038a5ba8b4bc11818024c06800716dcd6ea2d2f046060093000b755224945a79c8c0c0126001c53565ba8b4bc11818024c003fb6e6b753a178230300498007e8d2d6ea2d2f046060093000dcd6ea2d2f04606009309c001c12dd4c68b4bc11818024c003735baa4d1697825c300498006e6b7566a2d2f046049801000dcd6ea2d2f04e4690930ae001b9add45a5e0a08c012604c00000724b7516978230300498006e6b75169952f0460600a2000dcd77a2d2f0460600930ae001b9af45ba8b4bc1181a424c003925ba8b4bc11818024c180006e6c855222d2f046049840001099b9add59a8b4bc118126001c53075ba8b4bc11818024c004036e6bed16978230300498007bcee1b9a2d2f046060093000e096ea2d2f0460600c0126001b9add45a8b4ca97823030000373642bd116978230300498006e6b7561a2d2f04606001b000dcd6ea2d2f04607d0c0126001c52dd5ba8b4bc11818024c00373642b7516978230428600007c0dcd6ea2d2f04d851093000dcd6ea2d2e0460600930ae001b9add5488b50797823024c003736d2b7516978230300498006e6d196eac345a5e08c0c0000dcd6ea2d2f0460818c0126001b9add45a86cbc0c01260040040e6e6b751691818024c40000738dcd6ea2d2f04605c093000e296ea2d3fc5e08c0c0126001b9add45a5e08c0e9126130003735ba8b4bc1181c2300200006e6b75169782303a45c093000dcd7a22d2f04d88c0c0126001b9add4b68b4bc11818024c000006e6b75169782302e4498006d6b75169782f046060093000dcd6ea6c2f046060093126001b9b0759aa911697823024c003735ba8b4bc13623042860000770dcd16a053ce5e08c0c0000dcd6ea2d2f046060093066001b9afb45a5e08c0c0126000003736bab75169952f0460600006e6b7549a2d2f048060093000dcd6ea2d41e7a8bc118126001b9af25ba8b4bc11818024c003735ba8b4da178230300498006e6b751697823030049822000dcd74a2d2f04608c0c0126001b9add45a6ccbc11818024c003735bab355222d2f0460498006e6b751697826c46070893000dcd86a2d2f046060093080001b9af845a5e08c0c01261a8003ef6e6b5916978230300498006e6b75169b12f046061093000dcd6ea2d37c5e08c0e1180002253736428b4bc11818024c003735ba8b91697823030049800806e716ea2d2f046060093001039c52dd45a5e08c0c0126001b9ae15ba8b4bc11818024c00000744b75169aa23030049800788dcd6ea402f046060093000dcd6ea2d2f04b86009301a001f03735ba9b0bc11818024c003735ba8b4d897e230300498006e6b75169d92f04606f893000dcdab2dd45a5e0970c0126001b9b195d28b4bc11818024c003735ba8b4bc11818024c3b0006e6b75169782c646060093000dcdb9add45a654bc118180001b9b105ba8b4bc11818024c003735ba8b4bc118230324498006e6b75169782be46060093000fedb9add3625e08c0c0126001b9add5488b50d97818024c003735ba8b4f39a42f0460498006e6b7549a632f046060093000dcd6ea2d2f04606d893008001b9add45a5e08c0c014c24c003735ba9d136178230300498006e6ba5169782ac46060093000dcd6eaa04c65e08c0c0126001b9add45a5e08c0ec18024c000006e6bed16978230300498006e6b751697823044060093000dcd7da2d2f046060093060001b9b175ba8b4bc11818024c0037360eb751697825c30049800744b75169d92f046060093000dcd6ea9345a5e08c0d2126001b9add45a6388c0c012606c00373632b751697823032449800000dcd6ea2d2f04b874893000df96ea2d2f0460760c0126001d5b735ba8b4d217823024c003735ba8b4bc14c230300498006e6b754222d2f046060093000dcd6eadd45a5e0970c0126001b9ad645a5e08c0c012606c0039c6e6b7516977230300498006e6b75169d92d246060093001079b9add45a5c08c0c0126001b9b215ba8b4bc11518024c0040e6eab7516978230300498006e6b751698823046060093000dcd6ea2d2f05588c0c9126001b9add4a08b4b811818024c0037a6e6b7516978230300498006e6ba5169782303004981f000001cb2dd45a5e08c0c0126001b9add478764bc11818024c003e05ba8b4f8178230300498006e6b75169b12ac46060093000fa9c12dd45a5e08c0c0126001b9b145ba9611697818024c0037367cb751691818024c200006e6b75169782d046060093000dcd6ea2f2f05588c0c0126001b9b195ba8b4c411818024c003735ba8b4bc16c230300498006e6b7531a2d2f04a48c093000dcd922dd45a5e08c0c0126001fdb73628b751697818024c003735ba8b4bc14e2302e04980086edcd6ea2d2f046060093001039b9add45a5e0970c0126001b9add5068b4b811818024c003735ba9d1169b12f0460498006e6b75169782303244981f000dcd77a2d2f04606009304c001b9add45a620ab11818024c003c46e6b7542978230300498006e6ce56ea2d2f04d88c093000dcd6ea2d2f04606009300e001b9add45a5e09491818024c003735ba8b4d219d2f0460498006e6d316ea2d2f0460600930010d1b9add45a5e08c0b8126001b9add45a83cbc118126010003735ba98d1699d2e0460600006e6b75169782303484980d000dcd6ea6345a5e0a08c0126001bf2dd45a5e08c0c012601c003735ba8b4bc11814424c288006e6b7516970230300498260010398a2dd5488b4bc0c0126001b9b565ba8b4bc1181a424c003735ee8b4bc11818024c338006e6b751697823029c49840000dcd6ea2d3b25ec8c0c0126001bc3735ba8b4bc11818024c003735baa4d169d92ac300498006e6b75361b12f046060093000dcd6ea2d2f046074893086001b9add4928b48c0c012615c003735de8b4bc11818024c050006e6b751697828230060093000dcd6ea2d3104606009303e001b9add59a8b4bc118126010003735ba8b4f29782302e0498006e6b751698e31c46060093000dcda5a2d2f0460760c0126001b9add45a5e08c0e11802e00037360eb7516978230348498006e6b75169b12c246060093000dcd6ea2d2f046070093114001b9add4c67f8bc11818024c003735ba8b4bc14118024c400006e6b75169702303004980a000dcdab30745a7648c0c0126001b9add45a764d894e18024c003735bab751697823034849800000dcd6ea2d4285e08c093000fd16ea2d32a5e08c0c0126001b9b2160e8b4bc11818024c003be5ba8b4bc11818024c2b8006e6b75169782303004a093000001b9b216288b4bc0c0126001b9aef45a5e08c0c012604c003736acb75169d9230300498006e6b75169d533a5e060093000fedb9add2f0460600930020021a4036e6d58bc11818024c00373642b7516978230300498006e6b7516a1b2f030049804000e496ea2d2f046060093004001c7b735ba8b4bc11818024c0041f806b751697823030049800724b75169782303004986f000dcd6ea2d3f85e08c0c0126001b9b215ba8b4bc1181261a8003a25ba8b4bc11818024c0d800736dad6ea2d2f046060093001099fdb735ba5e08c0c0126001b9add45a5c08c0c012604c0037e642b7516978230300498006e6b752017823030049840000dcdacae945a5e08c0c0126001b9add45a5d88c0e918024c003736968b4d8956230300498006e6b751697826c460600930010d1b9a2d2f0460798c0126002012dd45a674bc11818024c004036e6b75169cd2f03004980086900db9b072f0460600930010f9b9add45a5e08c0c0126001b9add45a784bc11815e24c003735ba97516978230300498006e6b75169782a44a48c093001039b9add45a5e08c0d2126001b9b565bc8b4bc11818024c003735ba8b4bc1181f6300498006fcb751697826c460600930010d201b735ba5e08c0c0126001b9add45a7bcbc11818024c000006e6bd116978272300498006e6b75169952f05e08c0c0000dcd6ea5045a6748c0c0126001b9b065ba8b4bc11818024c003735ba8f0bc11818024c0d8006e6b75169782303004987a000fedb9b075485e08c0c0126001b9b2155a8b4bc11818024c003736968b4bc11818024c038006e6b75169dd2f04a48c093000dcd6ea3c4785e08c0c0126001b9add45a6389c8c012615c003a2744b7516978230300498006e6c858ca7445a5e08c093000fedb9add5485e08c0c0126001b9af45ba8b4c711818024c003735ba8b4e697818024c000006e6c1d6f22d2f046060093000dcd6ea604805e08c0c0126001b9add45a7b8b811818024c003736a48b4bc16923030049800000dcd74a3c2f0460600930000021a37345a5e094918126001b9add586a4d16978230300003e06e6c196ea2d2f0460600006e6ba51e17823030049830000dcd6f2dd45a5e08c0c0126001bcb735ba8b4bc11818024c000006e6b751699d282300498006e6b75169782303004984a001039b9add45a7648c0c0126001c12dd45a764bc11818024c003735e88b4bc118180288498006e6b75169782303004982e000dcd6ea5845a5e08c0e1180001b9add45a5e08c10a180288003735ba8b4ab11818024c3f0006e6b75169782a246060093000e1db9add45a5e08c0c0126001b9add45a6a88c0c012615c003735ba8b4bc14e23c30049800000dcd6ea3c2f046064893000dcd7a22d45a5e08c0c0126001b9afb45a5e08c0c01260080000077cb7516978252460498006e6b7516a0540a5e08c0c0000dcd6ea2d37e5e08c0c0126001b9add4785e08c0c91260c0003735f68b4bc11818024c378006e6b75169fa2f046060093000dcd6ea2d45a5e08c10a180001b9add45a5e08c0c01260fc003735ba9b0bc11818024c00800738dcd6ea2d2f046060095000dcd86a5845a5e08c0c0126000003735ba8b4e697818024c003735baa14bc11818024c200007c0dd96ea2d2f046060093000dcd6ea2d39a5e060093060000003735ba96116995230300004136e6b751698823030049800001031b9add45a46060093000dcda5b2145a5e08c0c0126001b9add45a7588c11018024c003735ba8b4f0188230300498006e6b7524a2d23030049826000001b9add45a5e08c0bd126001b9b625ba8b4bc11818024c003735ba8b4c7169230300498007e8b75169a42f05588c093000e71b9add45a7108c0c0126001b9add45a5e08c0c0126230003736968b4bc1362303004980083edcd6ea2d2303004986f000dcd6ea2d388460748c0126001b9add45a690bc15b23024c003735ba8b4d899d2303a4498006e6b7516a182f046060093000dcd5222d388460760c0126001b9add5868b4bc118180034004556e6b751697823030049800770dcd16a052f0460600930011021a37345a5e08c0c0126000003fb6d6b74bc11818024c003735ba8b507a053ce5e08c00077cb751697823030049826000dcd6ea502f05c08c0c0126001b9b4b5ba8b4ec91818024c003736acb7561a2d2f0460600006e6b753a22d2f0460708a20010396eaae45a5e08c0c0126001b9b216328b4d897823024c003735ba9251691818024c050006e6b751697823030049866000dcd6ea9345a6388c0c0126001ce3736acc1d16978230300003726acb7516978230300498006e6dcd7a22d2f046060093000dcd6b29345a5e08c0c0126001c92dd45a5e08c0c01261d4003735baa913617823030049800756e716ea7445a5e08c093000dcdb9add45a5e08c10a180001b9add45a5e08c0c01261ec003735ba940bc1181b630049800806dcd6ea2d2f04e460093000dcd6ea462f04d88c0c0126001b9b075bab0d16978230300003735de98d16978230300498006e6c353a22d2f046051093000dcd8a30745a5e08c0c012600201b735ba8b502978230300003de6e6b7516a1b2f030049800000dcd8a2dd5868b4bc0c0000dcd6ea2d2f04f8600930d4001df2dd45a5e08c0c0126028003735ba9251691818024c098006e6b756eac345a5e08c0c0000fd16ea2d3ce5e08c0c0126001b9add4d85e08c0e118028800373654b7566a2d2f0460498006e6b75169a42f046049893000dcd8a2dd45a5e08c0c0126001b9add45a5e09c8d218024c003b86e68b5079e72f0460498007dadcd6ea2d2f04e460093000dcd77a2d2f0460600c0126001b9b3e5ba9611691818024c003735ba98d1697023030049800738dcd83add45a5e08c0c0000dcd83aa945a5e08c0c0126001b9add4d88b4bc1181c2300003fb6e6cf96ea2d230300498006e6b7546a852f046060093000dcd6ea2d2f04e460093000001fdb735ba5e08c0c0126010003735ba8b50da053ce5e0600006e6c353617823030051093000dcd86add45a5e08c0e1180000003735b88b4bc11818024c003f4756b7516978230300498006e6b7516a052f046060000000dcd6ea503ce5e08c0c0126001b9b19628b751697818024c003735ba8b4bc11818026c498006e6b75169ec2f046060093000ef96ea2d2f046060093026001b9b525ba8b4bc11818024c003735ba8b4b8118180300498006e6b7554a2d2f046060093000f81b9add45a690bc118126001c12dd45a5e08c0c012606c00403770dcd16978230300498006e6b752c22d2f046070093000dcd9f2dd59a8b4bc118126000003736968b4e697818024c003735ba8b4bc118202300498006e6c353622d2f046060093000b755222d3e05e08c0c0126002073735bab0d16978230300004346e68b4bc1181ee3004980072adcd6ea2d2f046060093000dcd8a2dd45a5e0ab0c0126001b9add45a5e0a7118180254003735bab0d56a2d2f0460600006e6c3586a2d2f046060093000f81b9b555ac8b48c0c0126001b9add45a6388c0c0126034000006e6a9116978230428600006e6b7532a2d2f0460600930010399f2dd5488b48c0c0126001b9add45a764bc12923024c003ab6e6b7528178230300498006e6d89a5a2d2f046060093000dcd6ea2d3085e08c0c0126001b9add45a660bc11818024c003736acb751698e230300498006e6b753a22d3485e08c093000dcd6b22d2f04606009301a001ce2dd5568b4bc11818024c003946e6b7516978230300498006e6d596b22d2f04606009300100db9add45a6088c0c0126001b9add4c68b4b991818024c003735ba8b4bc118212300498006e6b7516a1740a5e08c0c0000dcd6ea2d3544606009304c001b9add45a6c4bc1181c2288003be5ac8b4bc1181d830049800788dcd6ea2d2f04605c093000ee1b9a2d43679cbc0c0126001b5add45a5e08c0c0126164003735ba8b4e214e230300498006e6b751698f2f046060093000dcd90add45a7588c0c0126001dc37345a5e08c0c0126000000006e6b7516978272300498006e6b751697829030049884000001ce3075488b4bc118180001df2dd45a5e08c0f718024c003735ba8b4bc13918024c18000000dcd6ea402f04b860093000001b9add45a814bc118180000003735baa24bc11818024c003736b8b751698e230300498006e6c1d6ea2d31c46060093000dcd8a2dd45a5e06009303e001b9add45a764bc14118024c003735ba8b502978230300180007e8b751699d2f046060093000dcd83ad645a5e08c0c01260021a3735ba8b4e211818024c0037361a8b4d897823028849800000dcd8a2d645a5e060093000dcd6eadd45a6388c0c0126001b9add45a5e08c0c01261080037367eb7516978230300498006e6b75169f52f046060093000dcd6ea2d30446060093000001b9b5660e8b4bc14e230300003735ba8d516978230300498006e6b756b22d2f046060093000dcd6ea7d45a6a88c0c0126001b9add45a6a88c0c01260280045b6e6b7516978230300498006e6b7564a2d2f0460600930010d1b9b3945a5e08c0c0126001b9ae945a5e08c0c012615c003a25baa4d16978230300498006e6b752819d2f046060093001095b9add45a5e08c0c0126001f0b735ba8b4bc11818024c003735ba8b4bc118180288498006e6b752c2402f046060093000dcd6ea744665e08c0c0126001b9add45a730bc11821430000000770dcd16978230300498006e6b75169782302884986a000001b9b205ba8b4bc118126001dc37345a5e08c0c01260c0003735ba8b4bc16d23030049800846dcd6ea2d3485e08c093000df96ea2d2f0460600a2126001b9add45a674a08c01261bc003735ba8b4bc1181e0300498006e6b7516a2d2f046060093000dcd6ea6c2f046060093008000003825ba8b4c411818024c003735ba8b4d511818024c098006e6b75169aa23038460093000dcd83add45a5e0a7118180002073735ba8b4c711818024c0039c6d6b7516978230300498006e6bed6ea502f046060093000dcd6ea2d2f0460648930ae001b5add45a5e08c0e918024c003735baa4d1e1782303004980081cdcd6b22d2f046060093000df96ea2d45a5e08c0c012600226b7360e8b4bc11818024c0038a5ba8b4f3978230300498006e6b7549a2d2f04606b093000001b9add45a6088c0c0126001b9add45a5c08c0c01260c4003735ba8b4c111818024c180006e6b75169b13485e08c093001135b9add45a5e08c0c01260020eb735ba8b4ca978230300003735ba8b4bc16523030049800000df96ea2d30446060093000dcd6ea402f046060093086001b9add45a734bc0c0126008003736bab7516978230300498006e6b75169cd2f03004986f000df96ea2d30446060093060001b9b4967cb751691818024c003735e88b4bc17823030049800756e296ea2d2f046060093001039f7add45a5e08c0c0126001b9add45a5e0bc118214300003735ba8b4bc143230300498007c0e716ea9345a5e060093000ff5b9add45a5e08c0c0126001b9add45a6208c0c012615c003735ba8b4bc118230384600006e6b7531a4945a46060093000dcd6ea2d3c8654bc118180001b9add50298cbc11818024c003a25ba8b4bc11818024c0680086cdcd6ea2d2f046060093001071b9add45a5e08c0c0126001b9add45a6c0bc11818024c003a26acb7516978230300498006e6c856ea9c45a5e08c093000dcd6ea2d33a46060093100001b9add45a5e09491812606c003735ba8b4ec995230300498006e6c7d1697829c46060093000dcdb9add45a5e08c0c0126001b9b075c68b4bc11818024c003735ba9991697823030049800000dcd6ea5e2f046060093000dcd6ea4945a460600c0126001b9b0d45a5e08c11818024c003fe6e6b7516978230300498006e6c656ea2d2f0460708c0000dcdaa2dd45a5c08c0c0126001b9ae35ba8b4bc11818024c0037e6e6b75169782303004980081d00d6ea2d36246060093000ef96ea6345a5e08c0c0126001b9add45a5e08c0c9126144003735baa152c17823030049800744c1d6ea2d2f046060093000dcd6ea3c2f04606009301a001b9add45a6c4bd11818024c00373642b7d16978230300498006e6b75169782302e049877000dcdab2dd4785e08c0c0126001b9add45a5e0ab1181c2300003735ba8b4bc14118024c0d8006fcdf96ea2d2f0460600930010fdb9add45a5e08c0c0126001b9b1961a8b4bc11818024c003a25bab7516978230300498006e6b75169782824606d893000eadbaadd45a5e08c0c0126001c52dd45a674bc11818024c003736968b4bc11818028849800810dcd6ea2d2f046060093000ef96ea2d2f0460600c0126001b9add45a67cbc11818024c003925ba8b4bc1181d830049800000e497da2d2f046060093000dcd6ea2d3ce5e0970c0126002073735baa3d1697818024c004346d6d591697823030049800744b751697826c46051093001021bf2dd45a5e08c0c0126001b9b0d45a5e0ab11818024c003735ba8b4bc11818024c3c8006e6d2d16a2d2f046060093000dcd83add4785e08c0c0126001b9add45a5e08c0b8126100003735ba8b4bc11818024c040006e6b75169782303846001f000dad6ea2d2f05388c0c0126001b9add5ba8f0bc11818024c003ab6e6b751697825c300498006e6b7516a272f0460600930010d1b5b0745a5e08c0c0126001b9add45a6088c0c01260e4003145baa91169e72f0300498006e6b7549a2d2f049060093000dcd74a2d2f04606009304c002073a25ba8b4bc11818024c003735ba8b512978230300498007f6dcd9f2dd2f0460600930010d1b5add45a5e08c0c0126001b9b5d6968b4bc11818024c0037361a8b4bc11818024c0f800000dcd9f2dd5868b48c0c0000dcd6ea4645a5e08c0c0126001b9add58e8b4bc11818024c004036e6b751697823036c498006e6cf96ea2d23046060093000e09c12dd45a5e08c0c0126001b9add45a5e08c0c9126098003f46e6b75169b1230300498006e6b7516a0f40a5e08c093001039b9add4785e08c0c0126001b9add45a744bc11818024c003735ba8b4d217823024c00800724b751697823030049807000dcd74a2d2f0460600930140021a3735265e08c0ef18024c003735ba98d169b133a460600006e6b751697827230049802000dcd77a2d3b25e08c0c0126001b9add45a5e09c8c01261bc003736e6d2d16978230300498006e6b751697823031460093000dcd6ea6345a6a88c0c0126001b9b3e632b751691818024c003735ba8b502978230300010006e6b75169782303004985b000dcd6ea2d40a5e08c0c00de001b9add45a674bc12e18024c003825baa4d16978230300498006e6b751697823036c49800000dcd6ea2d2f0460600930ce001b9add5328b4bc12923024c003ff6e6b75169782303004980081cdcd6eaa045a46060093000dcd7da2d2f0460760c0126001b9add47a8b4bc11818024c003735ba8b4e6178230300498006e6b75169d92e046060093000dcd9f2dd45a5588c0c0126001b9add45a6a88c0c018024c003735d28b4bc11818024c09800818dcdb5add45a46060093000dcd6ea2d2f046064893014001b9add45a764d215623024c003f45ba8b4bc11818024c498006e6b751698823030049826000e716eacd5488b4bc118126001b9add45a5e08c0c01261c8003735ba8b4bc14f230300498006e6b75169e72f046069093000001b9add45a5c88c0c0126000003735ba8b4bc13622024c00373640b5916978230300498006e6b75169782c846060093000001b9b215ba8b4c4118126002073735ba8b4bd91818024c003b86e68b4bc11818024c010006e6b7516a1b40a5e060093000ee1b9a2d2f0460600930de001b9add5488b4d217823024c003735ba940bc11818024c498000010d1df22d2f046060093000dcd6ea2d2f046064893026001b9b3e5ba8b48c0c012607c0039c6e6b75169952f0460600007e8f816ea2d2f046060093000eadb9add45a5e08c0d2126001b9b6660e8b4bc11818024c00392642b751697823030049800000f216ea2d2f046060093000001b9add45a5e08c0db126001b9add45a654bc1181d2300003735ba8b4c411818024c05000806dcd6ea2d41e5e08c093000dcd6ea2d2f04605c093034001b9add45a5e08c0db1260c0003735ba8b4bc11818024c420006e6d996ea2d2f0460600930010d1f03735baa4cbc0c0126001b9add45a6088c0c0126008003735baa4d3a17829c300498006e6b75169822303004986f000db583add45a5e08c0c0126001b9add45a5e09b11814a24c003735ba8b4bc1782303004980081cdcdab30745a46060093000fd16ea7445a5e08c0c0126001c92dd45a5e09b11818024c003e06e6b7528178230300498006e6b75169782302b449840000dcd6ea402f04608c0c0126001c12dd45a5e08c0c012603400000744b7516978230384600006e6bed1697823030049807001039b9b565ba8b48c0c0126001bf2dd45a5e0bc11818024c003826acb7516978230300498006e6bb16ea2d2f046060093000dcd6ea2d31046060093026001e23735ba8b4e211818024c003e56e6b751697823030049800806dcd6eacd45a5e08c093000dcd6ea2d43683cf3978126001b9add45a83cbc118126000004407c0b7516978230300498006e6b7524a2d3ec46060093000dcd6ea744a05e08c0c0126002073e05ba8b48c0c01261bc00000744c3516978230300498006e6c656ea402f046060093000dcd6ea634725e08c0c0126001b9add45a5e08c0b817024c0038260eb751697823030049800000fd16ea2d2303004986f000dcd6ea2d33a5e08c0d2126000003735ba9c8bc11817024c003735ba900bc15623030049800806dcd6ea2d4365e060093000eadb9add45a5e08c0c1126001c12dd5ba8b4bc11818024c003735bab351697823024c00000884dc96ea2d2f046060093000dcd722dd45a5e08c0c0126001b9add45a78cc711818024c003735ba8b50ba0f2f0460498006e6bbd169782303004981b000dcd6ea9d4928b48c0c0126000003735ba8b4eb97818024c003735ba8b50897823030049800000dcd6ea2d41e5e08c093000dcd6ea6c2f04605109308000211bf45ba8b4bc11818024c003735baa011697823036c498006e6b7516a2a2f046060093000dcd6ea744c6674bc118180001b9add45a83cbc1181260c000373642bed16978230300498005baab9169e72f0460600930010d1b9a932f0460760c0126001eb3735ba8b4bc118214300003735ba9d1169782302bc498006e6b7516a1b2f030049800000dcd6ea2d348690bc118126001b9add45a668bc11818024c003735ba900bc11818024c0f800724bed169782303004986f000dcd6ea2d2e046060093036001b9add45a764ce91818024c003735f0b7516978230300498006e6b75169782303c460093000dcd8a2dd45a5e0600930ae001b9add5268b4bc12923024c000006e6c1d66a2d2f0460498006e6b755422d2f046060093001039c12dd45a5e08c0c0126001c52dd45a5e08c0c012624c003746e6b7516978230300498006e6c356ea2d2f046049840000dcd6ea2d32a5588c0c00de001fa2dd45a6c4bc11818024c003735f68b4bc136230300498007d2dcd6ea2d2f046060093000dcd6ea9c45a5e08c0a2126001b9add45a654bc14e230300000006e6b7566a2d2f0460498006e6b754297823046060093000dcd6eaa145a5c08c0c0126001b9add59a8b4bc1181260c0000006e6b751697825c2e0498007c0b75169ee2f046060093000dcd6ea4945a7648c0c0126001b9b4b45a5e0bc11818024c003735baa4d1697828230049800868dcd6ea2d32a5e08c0c0000001b72dd45a5e08c0c0126001b9add45a690bc118126010003e0714b7516978230300498006e6b75281b12f046060093000e09b9b215ba8b4bc118126001b9ae94c68b4bc11818024c003735ba9d1169782302a8498006e6c656ea852f046060093000dcd6ea2d3905e08c0c0126000003735ba8b50d97818024c003735ba9ed24a2d23030049b736acb7549a2d2f053860093001031b5add45a5e08c0c0126001dc3736d68b4bc11818024c003735baaf116978230300498006e6b7516a1b2f030049830000ef96ea2d3b25e08c0c01260021a37345a5e0949181d824c0038a5ba9d116978230300498006e6b75429782ac46060093000dcd74a2d2f0460600c0126001b9add4b08b4bc11817024c003736028b4bc11818024c420006e6b75169bb2f046069093000dcd6ea3645a5e08c0c0126001b9add4c68b4bc11819224c003735bab0d169e72f0460600006e6b7550a2d2e6460600936e6c1d6ea9345a5e0a70c0126000003735de8b4c411818024c004326e6b59169782303004980067cb755222d3ce46060093000dcd6ea2d2f04a48c09301a001b9add45a5e08c0c0126120003735ba8b4bc1181d224c288006e6b751697829c4605d8930010d201b9c5ba5e08c0c0126001b9b565ba8b4bc12923024c004436e6b7516978230300498006e6b751697823030049878000dcd6ea2d3ae5c08c0c0126001b9add45a5e08c0c918024c003be5ba8b4bc1292303b0498006e6b7531a2f2f046060093000dcd6ea852f04606009303e001d5b735bab0d16978230300003735ba8b4d89782302bc498007c0dd56ea2d2f046060093000dcd6ea2d2f04b860093126001b9add45a734bc0ec18024c003735baac516978230300498007f6e716eaa42f046060093000df96ea2d2f0460648c0126001b9add45a734d891818024c003735ba8b4bc171230300498006e6b75169c12f046060093000dcd6ea2d2f05046009301a001b9b075ba8b4bc12923024c003735ba8b4e211818024c200006e6b7531a2d31046060093000e95b9add45a5e08c0c0126001df3735ac8b4bc11818024c003736acb751697828230049800788dad6ea2d2f046060093000e6db9add45a5e08c0c0126001ce3795ba8b4bc11818024c000006e6b6916978230300498006e6b756ea2d2f04a48c093001039ce2dd45a7648c0c0126002093735ba8b4c111818024c000006e6b752c225230300498006f8dcd6ea2d2f046060093000f81b9add45a5e0970c0126001b9add45a6208c0c018024c003735ba8b4bc1181b624c01000868dcd90a932f046060093000dcd7eadd45a5e08c0c0126001b9add45a5e08c0db1261bc0043977cb7516978230300498006e6c1d6ea2d2f050460093000dcd7a22d2f0460600930b2001b9add45a734d895618024c0000081cc516ea2d2f0300498006e6b7566ac345a5e08c0c0000dcd6ea2d3645e08c0c0126001b9add4e88b4bc11818624c003735ba9d11697825c300498006e6b754b22d2f046060093000dcd6eadd45a5e0a08c0126001b9add5868b4ce9782303000038a5ba8b4d8978230300498006e6b75169d935446060093000f81e22dd5268b4bc0c0126001b9add45a79cc711818024c003f45ba8b4bc15e230300498006e6b75169782b046060093000dcd8a2dd45a5e06009304c001fa2dd45a5e08c0c0126004003735ba8b4ab1412303004980081cdcd6ea2d2f04a48c093000dcd6ea2d2f05148c0c0126001b9add45a758bc11818024c003735ac8b4f397823030049800806fedb9add2f046060093000dcd6ea4945a460600930360000038e5ba8b4bc11818024c003735ba8b4e697818024c03800000dcd6ea2d31046051093000dcd6ea2d2f0460708c00ae001b9add45a5e09411818024c003736a48b4ce97823030049800756dcd6ea2d31c46060093000dcd6ea502f04606009300200228b735ac8b4bc11818024c003ab6e6b59169782303004980081cdcd6ea2d2f050460093000dcd6ea2d37a690bc118126001c92dd45a5e08c0c014424c003f45ba8b4ec9562303004980077cb75169782303004981b0010396eaad45a5e08c0c0126001b9b145ba8b4bc0c0126028003735ba8b514978230300498007f6dcd6e97823030049800000dcd86a2d2f0460600930ae001b9add51a8b4e211818024c003ef6e6b5d16978230300498006e6b75169d92b646060093000dcd6ea2d2f04606b8c0126001b9add45a5e08c0d212624c0039c6e6bd116978230300498007acdcd6ea2d2f046060093000001b9add45a690ca978230001c92dd45a8b4bc11818024c0039c6e6b7516978230428600006e6bd1169782303a460093000dcd6ea2d2f05548c0b81260020eb735ba8b4bc11818024c003735ba8b4bc1182143a4600007deead6ea2d2f046060093000fd16eaa445a5e08c0c0126001dd3735ba8b4bc11818024c003735ba8b50797823024c010006e6b7516a0f2f04604986f000dcd5222d2f0460850ec180001b9add45a7a0bc11818024c003735ba8b4e797823030049800752dad6ea2d2f046060093000dcd8a2dd45a5e060093026001c13735de8b4bc11818024c0039c628b7516978230300498006e6b751697825c4b860093000f81b9add45a5e08c0d2126001b9add45a5e08c0ee17024c000007f6dcd83978230300498006e6b75169e42f046060093000dcd90add45a734bc0c0126002072dd56c8b4bc11818024c003735ba9d131978230300498006e6b751699d31c46060093000dcd6eaa44a05e08c0c0126001b9add45a5e09c8ec18024c003735ba8b4d897823030c498006e6b75169b12f04b860093000dcd6b22d33a5e08c0c0126001b9b5e5ba8b4bc11818024c003806e6b751697823030049800000fedb9add2f046060093000dcd6ea2d40a5e08c0ec180001b9add59a8b4bc118126008003735bab351697823024c378007f6dcd6e97823030049830000dcd6ea7445a5e08c0d2126001ce2dd5528b4bc11818024c003735ba8b4e697826c300498006e6bbd49a2d2f046060093000e896ea2d354460600a2126002073735ba8b4f091818024c003846e6b7516978230300498006e6d916ea2d2f0460600930010396eaa445a460600930de00202b735ba8b4bc11818024c003735bab0116978230300498006e6b75169882f04b860093000dcd5222d2f0460778c012600201b735ba9b0bc11818024c003e06e6c858ca2d2f030049800724dcd6ea2d2f046060093000fadb9add45a5e08c0c0126001b9add5268b4b811818024c003735ba8b50e178230300498006e6b7516a1b2f0300498020010d1b9b2145a5e09b118126001b9add45a86cbc0c01261bc0037367cb751691818024c2b8006e6bed1697823030051093000dcd6ea2d2f0460600930d6001d12dd45a79cbc11818024c0036b5ba8b4bc11818024c20000770dcd169782303b060093000dcd6ea2d2f04606009d126001b9add45a6a88c0c012606c0038a5ba8b4bc11818024c008006e6bed16a2d2f046060093000dcd6ea6c2f046060093000000003e05ba9251691818024c003735ba8b4bc11821e300498006e6b751697822a3a460093000dcd6ea2d2f04e46009300e001b9add45a5c08c0c0126018003ab744b7516978230300498006e6b7524a2d43646060093000dcd6ea2d304460760c0126001b9b2f5e88b4bc11818024c003735ba8b4bc11818024c3e8006e6b7516a052f046060007000dcd6ea3c3ce5e08c0c0126001ce2dd5ac8b4bc11818024c003735ba8b4bc11819a300498006e6b7528a2d2f046060093000fd16ea2d3485e08c0c0126001b9af445a5e0a711818024c003735ba98d169782303004e0006e6b7549a2d2e646060093000dcd6ea2d2f05388c10a180001b9aef45a5e08c0c0126034003735ba8b4bc1182302e0498006e6b751697823038460026000dcd6eacd5568b4bc118126001b9b565de8b4bc11818024c003a26e6b75169aa23030049800000e096ea402f046060093000dcd6ea2d3605388c0c01260021a3735e88b4bc11818024c003c46e6b75169952f046060000756dcd6ea3c2f046060093000b755222d3dc5e08c0c0126001b9add45a6ecc711818024c004346e68b4bc1181fe30049800868dcd6ea2d2f0460850c0000dcd6ea2d2f0460600a8126001b9add45a6c4bc1181a424c003735ba8b4b811818024c068006e6b75169c52f046060093000dcd74a2d3b25e08c0c0126002073735baa051691818024c0037361a8b4bc11818024c13000000dcd6ea6c2f046060093000dcd6ea2d2f0460600930b2001b9adc45a5e09b11818024c003736acb7516970230300498006e6c656ea2d2f04605c093000e296eaa445a5e08c0c0126001b9add4d85e08c0c01260c00037360ebbd16978230300498006e6b751697823044860093000ee1b9a2d2f04606009300e001fa2dd45a5e08c0c0126010003736e6bed16978230300498006e6b75169782303846000a000001b9add45a5e09b1181c2001ce3735ba98d2c178230300003a25ba8b4ce978230300498006e6bbd6ea2d2f046060093000dcd6ea2d2f05588c0b8126001b9add45a640bc11818024c003735ba8b4c611818024c288007c0b75169f62f04606009300110a073735ba8b48c0c0126001b9b215ba8b4bc13918024c0037360eb7516970230300498006e6b75169d92f046064893000dcd90add45a814bc118180001b9add52698cec97818024c003735ba900bc11818024c2b8006e6b751698223030049807000e616ea2d2f0460600931140020c3735ba940bc11818024c003735ba961169c4230300498006e6b752817823030049804000dcd6ea2d3e45e08c0c0126001b9add45a5e0970c01260040037361a8b4bc11818024c05000000dcd86a2d2f04d88c093000dcd6eadd45a5c08c0c0126001b9add45a764bc11018024c003735ba8b4ec9b1230300498006e6b751697823038460013000dcd6eac345a5e08c0c0126001b9add45a5e08c0e11c2300003966e6b7516978230300498006e6b75169782724d860093000dcd8a2dd4c68b4bc0c0126000003dd6d6b751697818024c003735ba8f0ce978230300498006e6c7d169782303005c093000dcd6ea2d2f0460600930c2001b9add4908b4bc11818024c003735ba8b50297826c46060000704b751697825c30049840000dcd6ea2d2f04605c09303e001b9b4f5ba8b4bc11818024c003735ba8b4bc11818024c3a00081cdcd77a2d2f046060093000dd56eaa445a5e08c0c0126001b9add45a6c4bc11818224c0039c6e6b7516978230300498006e6c351697823030049813000dcd86a2d2f0460708c0126001b9b145ba8b4bc0c018024c003735ba8b4ec988230300498006e6b75169782303a460093000001b9add45a5e0a6118180001b9add45a5e08c0c016024c003735baa811699d230300498007c0dcd6eac345a5e08c0c0000dcd5222d2f0460760c0126001dc3736428b4bc11818024c003735ba8b4bc1181d224c35000738df96ea2d2f046060093000dcd5222d2f0460880c0126002073735ba8b4b811818024c00373670b75169782302e0498006fcb75169782303a460093000001d52dd45a5e08c0b8126001b9b3e5ba8b48c0c0126098004516e6d596ea2d230300498006e6b752c1e72ac46060093000dcd6ea934928b48c0c0126000003925ba8b4bc1181b624c003735baa911697825c300498006f6dcd6ea2d2f046060093000dcd6eac34e88b4bc118180001dc37345a5e09b11818024c003735ba8b4ec97829c2e0498006e6b751697829446060093000dcd6ea2d2f05388c0c013c0021f3b86e68b4bc11818024c00373642b75169822303004980081cdcd6ea2d23036c60093000dcd6ea2d33a5ec8c0c0126001b9add45a5e0a711817e24c003925ba8b4bc178230300498006e6b751697823030049834000dcd6ea2d2f0460600930e6001b9add45a5e0a71362303a4003735ba92916978230300498006e6b75169782ce46060093000dcd6ea2d2fc460600930de001df2dd5268b4bc11818024c003735ba8b4bc1181d23004c8006e6b751698226c46060093000dcd9f2dd45a46060093014001b9b215ba8b4f097823024c003fb6e6b74bc11818024c0100082cfedb9add2f046060093000fedb9add2f0460600930de001b9add4ba8b4c111818024c003735baa14bc11818024c2b800798dcd6ea2d2f046060093000e8db9add45a5e08c0c0126001b9add45a6388c0c012624c003735ba8b4d0178230300498006e6b956ea2d2f046060093000dcd6b22d2f046060093126001b9ae945a5e08c0c012606c003735ba8b4bc1181a424c00800704b75169e72f046060093000dcd74a3c45a5e08c0c0126001b9aa445a5e09491818024c0037367cb751691818024c098006e6b751697823c46060093000e296ea2d2f046060093008001b9add45a794bc11817e24c0038d6e6b7516978230300498006e6b751697823031c60093000001b5a2d2f0460760c0126001f03735ba8b4c711818024c003735ba9251691818024c068006e6c3d6ea2d2f046060093000dcd6ea2d32a5e08c0c0080001d5b825ba8b4bc11818024c004346e6d5916978230300498006e6b75169782303244981b000f81b9ad645a5e08c0c0126001b9add45a5e08c0c0126104003736acb7524a2d230300498006e6d9d6ea7445a5e08c093000dcd6ea2d41a5e08c0c0126001d12dd45a6a8bc11818024c003735ba8b4bc1181d030049800868ef9169782303b060093000dcd6ea2d39a5e0600a2126001b9add45a5e08c0c016624c0039c6e6d2d16978230300498006e6b751e22d2f046064893000dcd97add45a5e08c0c0126000003f45ba8b4ca978230300003736968b4bc1181d2300498006e6b75169562303004986f000dcd6ea7445a6388c0c0126001b9add45a5e08c0ec1b624c003735ba8b4bc14e23030049800000dcd7da2d2f04606d893000dcd6ea2d3b25788c0c0126001b9add4805e08c0c0126098003735ac9d116978230300498006e6b7516a2d39a5e060093000dcd6ea5745a7f88c0c01260021a37360e8b4bc11818024c003735bab0d169b12f046060000000dcd74a2d2f046064893000ef96ea2d2f04606009301a001f0373632b591697818024c0037360eb7524a2d230300498006e6b75169782303ac60093000dcd74a2d2f046064893060001b9add45a7e4bc11818024c0037e5ba8b4bc14e2303004980077cd596ea2d2f046060093000dcd7da2d2f05e08c0c0126001b9add5488b4bc1181a424c00000736dad6ea2d2f046060000868dcd6ea2d2f046060093000dcd6e9e72f05a48c0c012600000373642b752017823024c003735bab7524a2d230300498006e6b75169882303004981b000dcd90aa445a5e08c0c0126001f1b735ba8b4bc11818024c004346fcb7516978230300498006d6b752c22d2f046060093000dcd90add5028b4bc118126001b9add5268b4d511818024c003735ba98d169782303846000077cc1d6ea2d2f046060093000dcd6ea402f046060093014001c12dd45a674bc11818024c003fb6d6b7516978230300498006e6b75169942303004986a000dcdabadd45a5e08c0c0126001b9add4c68dcbc11818024c003965ba8b4bc11818024c42000000dcd832dd45a5e08c0c0000dcd6ea2d2f25588c0c0126001b9add4d85e08c0c0126008003735ba9b0bc11818024c3780083edcd6ea2d2f046060093000ef96eadd45a5e08c0c0126000003735baa14bc12923024c003735ba8b4f2978230300498006e6b7516978230384600c0000dcd6ea2d2f04b860093008001b9add5608b4bc11818024c000006e6b7535a2d2f0460498006e6c3531a2d2f046060093000ef9b9add45a5e094918126002073735ba9251691818024c0040e6e6bed6ea2d230300498006e6c516eaae45a5e060093000dcd6ea2d2c2460600930de001b9add4805e08c0c012604c003735ba8b4bc1181b624c038006e6dcd6ea2d39a5e060093000dcd6ea5845a58c8c0c0126001b9add45a5e08c0c015c24c0037361a8b4bc1181803004980081ce71ab2dd45a46060093000dcda6add45a5e08c0c0126001d12dd45a5e08c0c012624c003735ba8b4bc118216300498006e6b75169992f046060093000dcd6ea2d41e5e08c0ec126001b9b035ba8b4bc11818024c000005baa9124a2d230300498006e6c856ea2d2f04b849840000e616ea5845a5e08c0c0126001b9af15ba8b4bc11818024c0040e77cb751697823030049800000c516ea2d3ce5e060093000dcd6ea2d3626388c0c0126001b9add45a890bc11818024c003735baa14bc11818024c130006e6c9d6ea2d2f046060093000dcd6b22d3625e08c0c0126001b9add45a5e0a08db18024c003866e6b7516978230300498007f6dcdb5add2f04606009300100db9add45a690bc118126001b9add45a6a88c0c0126034003736968b4ab11818024c378006e6b756ba2d2f046060093000dcd6ea3c2f046060093126001f03a25ba8b4bc11818024c003736968b4bc14e230300498006e6b75169e72f04a48c093000f11b9af445a5e08c0c0126001b9b215ba8b4bc13622024c003736acb75169aa23030049800000dad90a2d2f046060093000dcd6eacd45a5e08c0ec126001c52dd45a5e08c0c012617c003c46e6b7516978230428600006e6c216ea2d2f046060093000dcd6ea2d2f0460600ac126001b9add45a7108c11818024c003735ba8b4c597823030049800868dcda5a2d2f046060093000e896ea7445a5e08c0c0126001b9add52e8b4bc11818024c003735ba8b4bc139180288498006e6b75429782303004980a000dcd74a2d2f04607f8c0126001d5b735ba8b4bc12923024c00373642b751697823036c498006e6b75169a42f046049800000dcd83add45a6a88c0c0126001b9add45a814bc1181802880039c6e6b7516a222f030049800724b751697823036c4986f000f81b9add4785e08c0c0126001b9add45a79cbc14118024c003735ba9d516978230300498006e6cf96ea6345a46060093000dcd9f3145baa91168c0126001b9add45a86cbc0ec18024c003735ba8b4e317823030049800000ee1b9a2d40a5e08c0c0000dcd8cadd45a7108c0c01260016eaad45a79cbc11818024c003e26e6b7516978230300498006e6b7516a2d2f04e460093000dcd6eadd45a6a88c0c0126001b9add5868b4bc11818000400434818dad6ea2d230300498006e6b7516a0f2f046049807000dcd6ea4045a5e0970c0126001b9add45a8b502978230300003735baad516978230300498006e6b7544a2d2f046060093000dcd6ea2d2f04d88c0db1260016eaa445a7d8bc11818024c0039c6e8b7516978230300498006e6b753a23c2f046060093000dcd9f2dd45a460600c0126001b9add45a5e08c0d2126010003735ba8b4e21562303004980073adcd6ea2d2f046060093000dcd6ea852f046060093026001d5b735ba8b4bc14118024c003735ba8b4d5136230288498006e6ce58ca2d2f046060093000dcd6ea2d3b26908c0c01260000039c5bab351697823024c00373640b756b22d2f0460498006e6b7550a742f046060093000e296ea2d2f0460690930ae001b9add45a5e09e11818024c00373628b75169d92f0300498006e6b75169912f046060093000dcd6ea2d2f046060093048001dc37345a5e08c0c014424c003735bab351697823024c0380084edcd6ea2d2f046060093000eadb9b2160e8b4bc118126001b9add45a5e08c0e018024c002dd56c8b4f397823030049800000dcd6ea2d3485e08c093000dcd6ea934625e08c0c0126001b9add5368b4bc11818024c003735ba8b4ca9702303004980081cdcd6ea2d35446060093000dcd6ea2d3485e08c093060001b9add45a674bc12923024c003735ba8b4e211818024c0f8006e6b75169782303f860093000dcd83ac35488b4bc118180001e739c6e68b4bc11818024c003b86e68b51697823030049800756dcd90add45a5e08c093000001b9b555ac8b48c0c0126001b9add45a5e08c0c014e24c0039c6e6b7515178230300498006e6b751698223030051093000001b9aef4805e08c0c0126001b9add586a9116978230300000006e6b75169ad230300498006e6dcd6ea2d2f04e460093000dcd6ea2d43c5e08c0c0126001b9add45a86cbc0c012601c0039c6e6c1d5222d2f0460600006e6dcd6ea2d40a5e08c0c0000001d3add45a5e08c0c0126001b9b215ba8b50797823024c003735ba8b4ce978282300498006e6b7516a2d30446060093000e896ea2d3625e08c0c0126001b9add45a5e09491821424c003735d2a4d16978230300498006e6b75169e12f046051093000dcd7da2d2f04606d8930de002003735ba8b4bc11818024c0040e6e6b7531a58230300498006e6b751698e23030049801000dcdb2add45a5e08c0c0126001b9add45a83cbc13623024c003735ba8b4d8969230300498006e6b7531a402f046060093000dcd6b22d2f046060093002001b9afb5ba8b4bc14118024c000006e6b75169d52f0300498006e6b75169e62f046060093000dcd6ea2d2f046060093110001b9b215bab351697823024c003735baa71169782303a4498006e6b75169782ae46060093000dcd6ea2d2f04606009302e001b9add45a734bc17818024c003735ba8b4bc11817024c2b8006e6b751e1b12f046060093000dcd6ea5845a654bc118180001b9add5268b4bc11819224c0040c6e6b751697823030049800770dcdb9a2d2f046060093000f09b9add45a5e08c0c0126001b9add45a5e08c0ca18024c003735ba900bc11818030049800892dcd8a2dd45a5e060093000dcd6ea402f0460600930d4001b9add59a8b4bc13623024c003826e6b7516988230300498000010096ea2d2f046060093000dcd77a2d2f04b860093080001b9add5268b4bc11018024c003735ba9791697823030049800724e496ea2d2f046060093000dcd90add45a86cbc0c0126001b9add5268bcbc11818024c003735ba8b4bc1181802d849800704b751697823030049893000dcdb9add45a6088c0c0126001b9add5828b4bc11818024c003735e88b4bc11818024c200006e6b75169e133a46060093000dcd89a2d2f0460748c0126001b9add45a5e08c10a180100003735baa911698e23030049800000dcda5a2d3485e08c093000dcd6ea2d2f04606d8930f6001b9add5268b4c411818024c0037e6e6b7516982230300498006e6b751697824a46060093000dcd6ea2d4365e09b0c0126001b9b075ba8b4ec97829c300003735aca9116978230300498006d6b751697823046060093000dcd74a2d2f04606009301a001fdb735bab355217823024c003735baa6116978230300498006e6b752c22e2f046060093000dcd6ea2d2f046070893080001b9add5049b0bc11818024c003736acba51697823030049800000dcd6ea402f046051093000f816ea9345a7c0bc0c0126001b9b145ba8b4bc0c012606c003735ba8b4bc11818024c15000000dcd6ea2d354460708c0000f81c12dd45a5e08c0c0126001b9add45a830bc11818024c0042e6e6b7516978230300498006e6b75169702e046060093000dcd6ea8145a5e08c0a2126001e23735ba8b4bc11818024c0036b632b7516978230300498006e6b7549a2d2f05385c0930010396eab245a5e08c0c0126001b9add45a5e08c0c91260340037360eba516978230300498006e6b751697827230049867000001b9b0d45a6a88c0c0126001c12dd4e88b4bc11818024c0037360ea911697829c46060000868ee1b5a2d2f046060093000dcdab2dd45a5e08c0c9126001e237e5ba8b4bc11818024c003735baa1531978230300498006e6cf96eaae45a46060093000dad6ea2d2f05588c0c0126001fdb735ba5e08c0ec18024c003735d2b7516978230300498006e6b75169d92f0460708c0000dcd6eac345a5e08c0c0008001b9add50a5e08c0c018024c0042e81cdcd16978230300498006fcba56ea2d2f046060093000dcd6ea2d2f0460688c012600225b735ac8b4bc11818024c0037360eb751697823032449800852dcd6ea2d2f046060093000dcd77a2d3ce5e08c0c0126001b9b0d45a764bc11818024c003735ba8b4bc11923030049800724dcd7da2d2f046060093000e896ea2d2f046060093002001b9add45a6208c0c0126034003735f09d116978230300498006e6b755522d2f04606009300107db9add4545e08c0c0126000003735ba8b4ec995230300003735bab7516978230324498006e6b751697825c28849840000dcdab2dd45a6208c0c0126001b5add45a5e08c0c012607c003d0714b7516978230300498006e6b751697823030049886000dcd6ea2d3ce5c08c0c0126001b9add5028b4ce91818024c003ab6e6bbd169782303004980081cdcd74a2d2f046060093001111b5add45a5e08c0c0126001b9add4a05e0a091818024c003736268b4bc1181802cc49800000fedce2dd2f046060093000dcd6ea2d2f05e09c8c01260022437361a8b4bc11818024c003735ba8b4bc1181a6300498006e6b751697826c3b051093000dcd6ea3c2f046060093002001b9b075ba8b4c411818024c003735ba8b5029782f0460600006e6d596ea9345a76460093000dcd6ea6345a75cb80c0126001d5b735ba8b4b811818024c004346e6b7d1697823030049800000dcd6ea2d31046074893000dcd71aa445a5e08c0c0126001b9add45a5e08c0b8126098003fb6e6b74bc11818024c038006e6ce56ea2d2f046049840000dcd6eadd45a6208c0c01260021a3735ba8d8bc11818024c0040e6e6b7516978230324498006e6b75169a42f046049802000e096ea2d2f04b88c0c0126001b9add4e88b4bc11822024c003735ba8b4d217823024c37800738e496ea2d2f046060093000fadce2dd45a5e08c0c0126001b9add5408b4af11818024c003735ba8b4bc1181b628849800724b75169782303a460093000dcd6ea934e85e08c0c0126001d12dd5488b4bc11818024c004037e8b75169782303004980081cdcd6ea2d36246060093000dcd8a2dd59a8b4bc118126001c12dd45a6c4bc11818024c003a96e6b75169782303004980083cdcd6ea2d2ee46060093000f11b9b4b45a5e08c0c0126001b9add45a5e09491812624c00000714bd116978230300498006e6b7516a2d2f04606d893000dcd6ea2d31c46060093008001b9add57a8b4bc11818024c003735de8b4ce97823030049800770dcd169782f046060093000dcd6ea2d2f04605c093014001d12dd45a5e08c0e1180288003735ac8b4bc11818024c020006e6b75361782303b060093000dcd9f2dd45a7648c0c0126001c52dd45a6388c0c012615c004036e6b75281782303004980081cdcd6ea2d31046060093000e096ea2d3105e08c0c0126001b9add5488f0bc11818024c003735bab3554a2d2f0460498006e6b753a22d3625588c093000dcd74a2d2f046060093064001fa2dd45a5e08c0c0126000003735ba8b4ce970230300498006e6b751697828230049893000f816ea2d3fc5e08c0c0126001f03735ba8b4bc12923024c0037362cb751697823030049800744c351697823030051093000dcd6ea2d2f046060093028001b9add45a608bc11818024c003735ba8b4bc11818024c3b80081d00d6ea2d2303004986f000001b9add45a83d02978230001b9add45a5e08c0b812604c003735ba8b4d81181802e0498006e6b75169782303845c093000dcd6ea2d2f04d88c0c2126001d33735ba8b4bc11818024c003c56e6b7516978230300498006e6b751697a2303004986f000fedb9b215ba5e08c0c0126001b9add45a750bc11818024c0040e6e6b7549a2d3b2300498006e6b75169782303846001b000df96ea2d3045e08c0c0126001b9add45a6748c0db18024c003735ba940bc11818024c000006e6b753a22d2f04a48c093000dcd6ea2d2f0460838c0126001edba25ba8b4bc11818024c003735ba8b4bc16a23030049800868ef9b9a2d2f046060093000f81b9add45a5e0a08c0126001b9add4688b4bc11818024c0040e7c0b7516978230300498007f6dcd6e97826c46060093000dcd6ea2d2f046060093080001b9add4e48b4bc11817024c003c86e6b751697823030049b9c6e6b7549a632f046060093000dcdb9add45a5e08c0db126001b9b0d45a5e08c0c012606c003e46e6b7516978230300498006e6b7516a0f2f046051093000001fa2dd45a5e08c0c0126001ce3735f68b4bc11818024c0037e5ba8b4bc11818024c200006e6b75169b12f046088093000fd16ea2d2f046060093060001b9add4e88b4bc14118024c0000077cb754297823030049800000ee1b9a2d41e5e08c093000dcd6ea5e2f046060093108001b9add4d85e08c0c012601c003735f68b4bc1181d2300498006e6b75169d02f046060093000dcd6ea2d2f05308c110180002073e0632b751697818024c003735ba8b4df1782303004980077cef96ea2d2f0460600930010a1b9add45a5e08c0c0126001b9add45a8b50797823024c003735ba8b4bc11818024c0c8006e6b753a22d3625848c093000e89b9add45a5e08c0e1180001b9add53e940bc11818024c003735ba8b4ca978230460600006fedcd6ea2d2f046060093001135d5b735ba8b4bc118126000003735ba8b50da052f0300003735ba9a91697023030049800000dcd6ea502f046060093000e496ea2d2ac460600930de001b9add45a5e08c0e518024c003735ba8b4bc11818024c450006e6c8583a7445a5e08c093000e496ea2d2f05388c0c0126001b9add4a05e08c0c01260c0003735bab3516978230288498007cedcd6ea2d2f046060093000dcd6ea6045a5e08c0c0126001d137361a8b4bc11818024c003735ba925169e7230300498006e6c856ea7445a5e08c093000dcd6ea403b25e08c0c0126001b9b195ba8b4ca978230300003735bab3516a2d2f0460498007e8dcd6ea2d2303004986f0010d1c92dd45a5e08c0c0126001b9afb45a5e08c0c01261cc003735ba8b4bc160230300498006e6bd12c22d2f046060093000dcd6ea6345a6748c0c00de001b9b295d28b4bc11818024c00403714b7516978230300498006e6b7516a1b2f030051093000dcd6ea2d32a5e0ab118180001b9add4b08b4bc118214300003735ba8b4bc1181802c849800756dcd6ea4945a46060093000dcd6ea2d3c8734bc0c0126001d12dd45a5e08c0c01260100039c5488b4bc1181d830049800704b751697823030049801000001dc37345a86cbc0c0126001b9add45a5e0a711817224c003be5ba8b4f3978230300498006e6b75169c423030049857000dcd6ea2d2f0488600a2126001b9add45a5e08c0c012611c003735ba8b4d897825246049800714b751697823034860093000dcd90add4d85e08c0c0126001b9add45a8b50d97818024c003735ba8b4bc1181802d4498006e6c516ea9345a5e060093000dcdb9add45a83cbc118126001b9b3e5ba8b48c0c012606c003735baa3516978230300498007dae296ea2d2f046060093000ef5b9add45a5e08c0c0126001b9add4928b50791818024c0039c6f6b7516978230300498006e6b754422d2f046060093000dcd6ea8345a5d88c0c0126001b9b295ba8b4bc11819224c0037368ccf96ea2d230300498006e6cf96eac345a5e08c0c0000ef9d5add45a5e08c0c0126001c52dd45a5e08c0c0126000003735ba8b4bc0ff18028849800788dd16ea2d2f046060093000dcd6ea3c2f046060093008001b9add45a654bc11818007c003735ba9b0bc1362303004980081cdcd6ea2d2303004987e000001eeb735ba8b4bc0c0126001b9b0d45a5e08c0c014a24c003736968b4bc11818024c200006e6b75169b12f050460093000ed5b9add45a5e08c0c0126001b9add4b48b4bc11818024c0037360eb75169782303004e0006e6c656ea2d2f04605d893000dcdb9add59a8b4bc118126001b9b075ba8b4bc14e1fe300000007e8d2d16978230300498006e6b75402502f046060093000dcd6ea2d2f04606009303400201b755ba8b4bc11818024c003735ba9251699d230300498006e6bed169562303004986f000e096eaa445a5e08c0c0126001b9afb45a5e0a711818024c000006e6bd116978230348498006e6c856ea2d2f04b88c093000dcd90b0745a6c4bc118126001ce3735ba8b50a17823024c003736dcb7516978230300498006e6b751698223032460093000dcd6ea2d2f0460600930a4001b9add45a6388c0d212615c00373642b75169b12f0460498006e6b753a22d37e5e08c093000dcd6ea853b25e08c0c0126001b9b735ba8b50d97818024c003735ba98d169782302e049800868dcd7da2d2f046060093000001c52dd45a5e08c0c0126001b9add45a6dcbc11819224c003735ba92524a2d230300498006e6c856ea2d2f05308c0c0000e296ea2d2f04606009306000201b735ba8b4bc12e18024c003be5ba8b4ce978230300498006e6b75169782303004982b000dcd6ea634b05c08c0c0126001fdb73628b74bc11818024c00373628b751697818024c06800868dcd1697823042860093000dcd6ea5845a8948c0c0126001b9add45a5e0b911818024c003735ba8b4bc11818024c260006e6d598a2dd45a5e060093000f81ce2d645a5e08c0c0126001b9aa445a5e08c0f118024c003735ba8b4bc1181802e0498006e6c856ea2d3105e08c093000dcd6ea2d3e25e08c0c0126001b9add45a79cd511818024c000006e6b753917823030049800000dcd7922d2f046060093000dcda5a2d32a5e0ab118180001b9add50a5e0949181d824c003735ba8b4bc1181b624c420006e6c7d6ea2d2f04605c093000dcd77a2d2f046060093126000003735ba8b4e212923024c003735ba8b4bc17823036c498006e6b751697825c30049800000dcd8a3075ba8b4bc0c0126001b9add4805e08c0c012606c003be5ba8b4bc118214300498006e6b75169562303004987b000dcd9c2dd45a5e08c0bb126001d5b735ba8b4d511818024c003735ba8b503978230300498006e6c516eadd45a5e060093000dcd6ea2d2e046060093126001b9add45a5e08c0c0126048003eb6e6b711697823030049800738c855222d2f046060093000dcd83add5268b4bc14e180001f03735de8b4bc11818024c003735ba9d11697827c300498006e6b75169b132a460600930010e9b5add45a5e08c0c0126001b9add45a5e094918126004004396e6b7542978230300498006e6b751697823030049829000dcd6ea2d2f046060093120001b9add4c68b4bb91818024c003735ba8b4e211818024c130006e6b753722d2f046060093000dcd77a7445a5e08c0c0126001f03735ba8b4b811818024c000006e6b751697825c300498007e8b751697823030049802000fd16ea2d2f0460600930de001b9add45a5e08c10a1dc300003735ba8b4bc12e18024c1800081cdcd8a2dd45a5e060093000dcd8d2dd45a5e08c0c0126001b9add45a5e0a411818024c003735ba8b4bc11821c30049800738dcd6ea2d39a5e060093000dcd6ea2d2f0460828c0126001b9add45a5e0a08c0126004003735ba8b4d519d230300498006e6b753a22d2e046060093000dcd6ea2d39a5e0748c01260000039b6e6b7516978230300003735baa4d1697823038460000806dcd6ea2d2f046069093000dad6ea2d2f0460600930ae001ce3735ba8b4bc11817a24c003735ba940bc11818024c010006e6b751697823030049868000dcd6ea502f0460600930de001b9add5268dcbc11818024c0038e6e6b7516978230300498007f6dcd6e97823030051093000dcd6ea2d38846060093014001fdb7360e8b4bc11818024c003735ba8b5079782f0460498006e6b752c22d2f046060093000e096ea2d2f046060093008001b9add45a5e08c0d21a424c0037361aa4d16978230300498005baa91169fe2f046060093000dcd6eaa445a5e094918126000003735ba900c411818024c003fb6e6b7516978230300498006e6b75429782303004981b000df96ea5845a5e08c0c0126001b9add4f28b4bc11818024c003735ba8b4bc11818024c1c0006e6b751697824030049830000dcd6ea2d2f046069093000001b9b216328b4bc13623024c003735ba8b4e211818024c098006e6b7531a5833a4606009300103983aa445a5e08c0c0126001b9add59a8b4bc17823024c003735ba8b4bc14e26c3a460000704c856ea2d2f046049840000dcd6ea2d2f04c08c0c0126001b9add45a5e08c0c015a24c003735ba8b4bc118198300498006e6b755222d2f0504600930010396eaa445a5e08c0c0126001b9add5768b4bc11818024c002dd5648b4f3978230300498006e6b75169a42f046076093000dcd77a2d2f04b88c0c0126001b9add45a5e08c0c012610c003735ba8b4bc121230300498006e6b75169782303846000d000dcd83ae045a5e08c0c0126001b9add45a86cbc17818024c003735de8b4d8978230300498006e6c1d5322d2f046060093000dcd7a22d2f04608c0c01260020e3fb6e6b74bc11818024c003736acb7516978230384600006e6b7516978230460850c0000dcd6ea7445a5e08c0a2126000003735ba8b4bc1181a424c003735ba8b4e21181ee300498006e6b816ea2d2f046060093000dcd6eaa645a5e08c0c0126001fdb736e6b74bc11818024c003735ba8b513178230300498006e6b751697823034849830000dcd6ea2d3104b860093080001b9add45a5e08c0c01261c00037361a8b4bc11818024c068006e6b75169b12e046060093000dcd6eabe45a5e08c0c0126001b9aef45a620bc11818024c00373632bd116978230300498006e6d5986a2d2f046060093000dcd6ea2d362690ab118126001b9add4c68b4bb11818024c0037360eb751697823038460000788e496ea2d2f046060093000dcd8cadd45a5e08c10a180001b9b3e5baa4d1691818024c00427738b7516978230300498006e6b75169cd2ac3004986f001095b9add4d85e08c0c0126001b9ae945a79cbc11818024c003735ba8b4e697829c300498006e6b7524a2d23030049893000dcd6ea6c2f0460600a2126001b9add5ba8b4bc1181c2300003735e88b4bc156230300498008970396ea2d2f046060093000e096ea4045a5e08c0c0126001c52dd45a5e08c0c0126008003735ba8b4bc15623042860000756e7190add45a5e08c093000e296ea2d2f0460600930de001b9add45a5e0a711817a24c0037361ac1d16978230300498006e6b75169a42f046049807000dcda5a5845a5e08c0c0126001c72dd45a5e08c0c012619c003735ba8b4bc136230384510006e6b753622d2f0460600930010d1b9add45a734bc0c0126001ce2dd586a9116978230300003a25ba8b4bc11814424c20000756dcd74a2d2f046060093000e71b9add45a5e09c8c0126001b9b0d5ba8b4bc11818024c00434818dcd6ea2d230300498006e6b75169e72f046064893000e71b9add45a814bc118180001b9add45a5e09c8e918024c003be5ba8b4bc11818024c49800706dcd6ea2d2f046060093000f81b9add4928b48c0c0126000003735ba8b50da0f2f024c003735ba8b5029782303a4600006e6b75169aa35446060093000dcd7a22d2f04606009303e001b9b0d45a5e09b11814424c003735ba9611297823030049800000dcd7a22d31c46060093000dcd6ea9950a5e08c0c0126001b9add45a5e08c10a18007c0040e6e6b7516978230384600006d6b7516978230300498260010c1b9add45a5e08c0c0126001b9add45a5e09711814424c003ab6e6b7516978230324498006e6b753a24945a460600930010d1fdb6b5ba5e08c0c0126001b9add45a5e0aa91818024c00373692b7516978230300498006e6c896ea2d2f046060093000dcd6ea2d2f04a48c093008001f03be5ba8b4bc11818024c003735ecb7516978230300498006e6b751697823045460093000dcd6ea2d3625e08c0a21260020737361a8b4bc11818024c004516e6b75169b1230300498006e6cf96ea2d2303004980d000e09b9add4805e08c0c0126001b9add45a79cc411818024c0040e6e6b753122d2f0460600006e6b896ea2d2f046060093000ee1ce37345a5e08c0c0126001b9b5667cb751691818024c003735ba8b4bc1181bc300498006e6b75169782303b860093000ee1b9a2d2f0460748c01260021a3d76e68b4bc11818024c003735ba8b4bc1182003004980077cb753a22d2f046060093000dcd74a2d33a5e08c0c0126001b5add45a5e08c0c0126028003736e6b7536178230300498006e6c856ea2d3485e08c09300100db9add5868b4bc118180001e23735f68b4bc11818024c003735ba8b4bc14118024c02000864f81b9add2f046060093000dcd6ea2d3b25e08c0b8126001b9add5269d0bc11814a24c003735ba8b4c417823028849800756dcd6ea2d31046060093000dcd6ea2d2f0460600930e2001b9add526900bc11818024c0037367cc1d6ea2d23030049800738dcd6ea2d30446060093000dcd6ea2d2f04b860093004001b9add45a5e0970c01261bc003e86e6b751697823030049800000dcd9f3145ba8b460093000dcd8eadd45a5e08c0c0126001b9add45a690bc13623024c003735ba8b4c11181d2300498006e6b7531a2d38846060093000dcd77a2d2f04606009300200226b735ba8b4d897823024c0037367cb756ea2d23030049800744b751697823030055093000dad6ea2d2f046060093026001b9add45a674bc11819224c004536e6b7516978230300498006e6b755a22d2f046060093000f816ea2d3ce5e08c0c0126001b9add5868b4bc118180000003735ba8b4bc14e238300498006e6b75169952f046060057000f81b9ad745a5e08c0c0126001b9add45a7108c0c018024c003735ba90d1697823030049800704bbd1697823030049840000dcd6ea2d3626748c0c0126001b9add45a5c08c0c0126004003735ba8b4f09782303a4498007badcdb5add45a5e060093000001b9b4b45a7648c0c0126001b9add45a6a88c0c012624c003e0756b7516978230300498006e6cbd6ea2d2f04e460093000f818cadd45a79cbc0c0126001c92dd45a5e08c0c01261dc004476e6b7516978230300498006e6b75169f02f046060093000dcd6ea2d2f05389c8c0126001b9b375bab0d16978230300003735ba925169b1230300498006e6b7516a052f05388c0c0000dc16ea7445a5e08c0c0126001b9add45a674c411818024c0040e6e6cf96ea2d230300498006e6b751697e2f046060093000dcd6ea2d2f04606009310e002183736968b4bc11818024c003735ba8b4bc1181fa300498006e6b751922d2f046060093000f816ea2d41e5e08c0c0126001b9add4e88b4bc11818a24c003e0756c656ea2d2f0300498007c0dcd6ea2d35446060093000fedb9add2f05e08c0c0126001b9add45a5e08c0a5126100004346e6b7516978272300498006e6bbd5222d2f046060093000dcd6ea2e2f0460600930ae001d53735ba8b4bc11817024c003735568b4bc1181d830049800000dcd6eac345a5e08c0c00010d1b9add45a814bc118180001c92dd45a5e08c0c0126100000006e6b75169af2e0460498006e6b75201782303004980d000dcd88add45a5e08c0c012600201b735ba8b4c711818024c003735bab0d1697823030018000724dcd6ea2d2f04606d893000fbdb9add45a5e08c0b812600214b9c5ba8b4bc11818024c003736acb7520178230300498006e6b751697823046060093000dcd6ea9345a764ce8c012600201b735ac8b4bc11818024c003be5ba8b4d8978230300498006e6b7516a192f046060093000dcd6ea2d2f0460600930c0001f0373640b591697823024c000006e4b7516978230300498006e6b753a22d35446060093000dcd6eaa445a5c08c0c0126001b9add4c68b4d797823024c003735ba8b4c71181a430049800000dcd6ea2d39a690bc093000dcd8cb0745a5e08c0c01260000037361a8b4bc1181c23000037e5ba8b4bc118230300498007dcdcd6ea2d2f050460093000dcd6ea9350a5e08c0c0126001dc37345a5e0a711818024c000006e6d4916978230300498006e6cf96eab645a46060093000dcd83add4805e08c0c0126001b9b625ba8b4d217823024c00373632b751697823030049800756dcd6ea744c65e08c093000001b9add45a5588c0db126000003925ba940bc11818024c003735ba8b4bc1181a424c010006e6b751698e23030049800000dcd6ea2d35e5e08c0c0126001b9add45a5e08c0d21261bc000006e6b75201782303a449b735baa4d1697823043060093000dcd6b22d2f046060093000001b9add45a5e08c0c012607800434770dcd16978230300498006e6b751695623030049884000dcd6eadd4805e08c0c0126001b9b065bab59169782303000037e632b751697823030049800770dcd6ea4945a46060093000dcd6ea6945a5e08c0c0126001b9add45a5e0ab11818024c003735ba8b4c114e230300498007c0b7524a2d2f04606009300000206add45a5c08c0c0126001d838a5ba8b4bc11818024c003735baa05169782303a4498006e6d9d6ea2d3b246060093000dcd90add4808b4bc1181260021a3c46e6a4cbc11818024c003735ba8b4bc11817024c0d800704b751697823028849840001111b9b5645a5e08c0c0126001bf2dd45a5e0ab11818024c003735ba8b4ee9c423030049800868dcd6ea2d304460600930010356ea6345a5e08c0c0126001f03c45ac8b4bc11818024c003736d68b4bc1181d83004980081ce716ea2d362460600930010d1b9a852f0460760c0126001b9add45a89102978230300003735baa85169782302e04980089cdcd6ea2d2f046060093000dcd6ea2d2f04606009303e000004346e68b4e211818024c0040e6e6b7520178230300498006e6b7542a2d2f04a48c093000dcd6ea2d39a5e0ab8c0126001b9add45a5e08c0d518024c000006e6b751698e230300498007e8b75169782c646060093000dcd83aa745a5e08c0c0126001fa3735ba8b4ca978230300003735ba8b4c711818024c18000000dcd6b22d2f046060093000dcd7da2d2f046060093080000003fb6e6b756697823024c0037e5ba8b4bc11818024c0f8006e6b75429782303004980d001111b9add45a5e08c0c0126001b9ad645a5e08c0c01260c0003735ba8b4cb178230300498006e6b7516a1b3d05e060093000dcd6ea6c2f05e08c0c0126001b9add54e8b4bc11818024c003736acb7542978230300498007e8b75169782303b060093000dcd6ea2d2f04cc8c0c0126001b9add45a5e0970e9126100003735ba8b4ca9782303001300077cb75429782303b060093000dcd6ea2d3626a88c0c0126001cdb736d6b751697823030000373670b751697823030049800000ea96ea2d2f046060093000001df2dd45a7108c0c0126001b9add45a5e0b091818024c003735ba8b4bc11818024c128006d6b7531a2d2f046060093001041b9add45a5e08c0c0126001b9b4b45a5e08c11818024c003735ba8b4bc11818024c3f8006e6b7524a2d23030049801000dcd6ea2d3b25e0a70c0126001b9b075baa14bc11818024c003735ba940bc1181d830049800000dcd7da502f046060093000dcd6eab845a5e08c0c0126001b9b335ba8b4bc11818024c00373642aad1697823030049800806e896ea2d2f046060093000dcd6ea2d33a460600930fc001b9add45a884bc11818024c0036b5ba8b4bc118180300498006e6b756ea852f046060093000dcd6ea2d32a5e08c0c0014001b9aef45a5e08c0c012601000373696c6516978230300498007e8b75169b12ac46060093000e71b9add45a5e08c0db126001df2dd45a5e08c0c0126004003735ba8b4d895b230300498006e6b75169782303a46d893000dcd6ea2d2f04e88c0c0126001e23735ba8b4e697818024c003735d28b4bc11818024c498006e6d2d169782ac46060093000dcd6ea2d2f046060093022001b9add45a5c08c0c0126010004036e6b751e178230300498007d2dcd6ea7445a5e08c093000dcd6ea744625e08c0c0126001d12dd45a5e08c0c0126000003735ba8b4ca978230300098007e8b751697823030049807000dcd90aef45a5e08c093080002073735baa14bc11818024c003735ba8b4bc118180260498006ecdcd6ea2d2f046060093000dcd6eaa44928b48c0c0126001b9add45a5e0a011818024c003735ba8b4bc14a23036c49800000dcd6ea8f45a5e060093000dcd6ea2d2f046064893126001f03735d28b4bc11818024c003735ba8b4ee178230300498006e6c516ea2d3ce5e060093000001b9add45a5e08c0df126001b9b4b45a5e08c0c012607c003735ba8b4bc1181b624c39800000dcdaa22d2e046060093000dcd6ea502f04606009300e001b9add4785e08c0c0126000003735baa711697829c300498006e6d656ea2d2f046060093001011b9add45a5e08c0c0126001d6b735ba8b4bc11818024db9add5268b4bc118214300498006e6b75169a42f046051093000dcd6ea2d41e7c8bc118126001b9ae94e88b4bc11818024c003be5baa9116978230300498006e6dad90a2d2f046060093000dcdaa26345a5e08c0c0126001d5b73628b751697818024c003e06e6b751697823032449800000e896ea2d2f046060093000dcd6ea2d4505e08c0c0126001b9add45a8b4d217823024c003e06e6b7549a632f030049800768e896ea2d2f046060093000e896ea2d2f046060093060001b9b5b5de8b4bc11818024c003735ba9ad16a252f0460498006e6b75169882303004989300104db9add45a5e08c0c0126001b9add5868b4bc118180008003735bab0d16978230300378006e6b75169e02f046060093000e71b9add45a83cbc118126001b9add5288b4bc11818024c003735ba9d116978230324498007e8c856ea2d2f046060093000dcd6ea2d41e5e08c0e9126001b9aef4808b4bc11818024c0038a5ba8b4bc1181d8300498006e6b7566ac345a5e08c093000dcd6ea2d3b27108c0c0126001d83735ba8b4bc1181a424c000006e6b751e178230300498006e6b751698a2f046060093000c1d5222d3ce5e08c0c0126001b9add4785e08c0c01260c00040e738b751691818024c3f0006e6b75169aa23030049801000001b9add45a5e08c0d6126001b9af445a5e08c0c012615c003e06e6b75169882303004980070eb751697823030049851001159b9add45a5e08c0c0126001fa2dd45a5e09b11818024c000006fcb751e178230300498006e6b751697823042860057000b755222d3ce5e08c0c0126001b9b215ba940bc11818024c004346e6b751697223030049800738dcd6eacd45a5e08c093000df96ea3c2f046060093060001b9add45a888bc11818024c00373628b7566a2d2f0300498006e6b751695623036c4986f000e496ea502f0460600930de001b9add45a5e0a71181b624c003735bab35169782303a44980086adcd6ea2d2f046060093000dcd8a2dd45a674bc0c0126001b9acd5488b4bc1181d824c003735ba9d11698823030049800724b752c22d2f046060093000dcd6ea3345a5e08c0c0126001b9add45a710949181d824c0040e6e6b7516941230300498006e6b752817826c46060093000dcdb9add45a690bc1181260021a3735ba8b4bc1181b624c003b76e6b751697823030049800738dcd6ea2d4365e060093000dcd6ea2d4365e0748c0126001e23735ba8b4bc13918024c003735ba8b4bc123230300498006e6b751697823030049835000dcd74a2d3625e08c0c0126001e23735ba8b502978230300003735ba8b4bc1181ec300498006e6b751697823038860093000dcd6eaa445a6a88c0c0126001c52dd45a5e08c0c012601c003735ba8b4ea1cd2f03004980074edcd6ea2d2f046060093000dcd6ea2d31c46060093004001b9add45a5fcbc11818024c003735ba8b4c711818024c378006e6b591697823030049802000dcd6b22d2f0460600930de001b9add4e45e0a711817024c003735ba9251691818024c02000000dcd6ea2d32a5c08c0c0000dcd6ea2d354460708c0144001b9add45a5e0970ec18024c003735ba8b4e697818024c200006e6b75169b12f046064893000dcd6ea9345a5e08c0b8126001b9add45a5e09b11815e24c00373642c1d1697823024c23000806e096ea2d2f046060093000dcd6ea4045a5e08c0a2126000003f45ba8b4e697818024c003735ba98d169952f0460600006e6b751697823030049863000f11dc37345a5e08c0c0126001b9b215ba8b4bc118126118003e07aeb7516978230300498006e6c35169aa23030051093000dcd6ea2d41e5e0a71181260021a3736428b4bc118126100003be5ba8b4bc11818024c020006e6b751697823043460093000eadb9b215488b4bc118126001b9add45a6209711818024c003735f6940bc11818024c378006e6b75169e72f0460708c0000dcd6ea2d39a654bc118180001b9add45a654bc118180300002dd5489251697823030049800000dcd6ea2d2f04a48c10a001009b9add45a5e08c0c0126001b9afb4b08b4bc11818024c004346e6b7516a0f2f0460498006e6b75169b131046060093000e096ea2d2f046060093000001e23735ba8b4c111818024c003735bab391697823030049800714c856ea2d2f046060093000dcd90add45a5e0a7136126001b9add59a8b4bc14e23024c003735fcb751697823030049800000db56ea2d2f046060093000dcd86a2d3ce5e08c0c0126001b9add45a7108c0c012606c003ab6e6b7516978230384600006e6b751697829c4b85c093000e81b9add45a5e08c0c0126001f7b7360eb7516978230300003735d2b7516982230300498006e6b751698831046060093000e296ea2d2f04d88c0c0126001b9add5268b4ec9b118024c003735ba96cbc11818024c400006e6b751697825c300498070010d1b9add59a8b4bc118126001b9add45a734ca9782ac3000041f6e6b752c22d23030049800756dcd86a2d2f046060093000dcd6ea2d2f04605c09301a001b9add45a5e08c0f518024c00373642b355222d2f0460498006e6bd11697823030049826000dcd6ea2d2f05108c0c0126001b9add45a86cbc14e18024c003736acb75169782302e04980075cdcd6ea2d2f046064893000dcd6ea2d2f0460850c004c001b9add45a5e09b91818024c004346dcb7516978230300498006e6c656fa2d2f046060093000001c12dd45a5e08c0c0126001b9add45a5e0a712218024c003735e48b4bc13623030049800704b751697823030049830000dcd6ea2d2f0460600bb126001b5add45a764bc11818024c003fb738b751697823030049800874dcd6ea2d2f046060093000dcd6ea2d2f0460600931120021a3735ba8b50d97818024c003735ba8b4bc1181d8348498006e6c256ea2d2f046060093000dcd83add45a5e08c0b8126001b9add45a5e08c0c013824c003735ba8b4ce978230384600006e6b751697829c3fc60093000001b9add45a5e08c0e1080001b9af445a5e08c0c0126028003a25ba8b4bc11818024c010006e6ba51697823030049801000e896ea2d2f0460600930de001b9add5ba8b4bc11817024c003735baa4d16993230300498006e6b75169782304286000a000dcd6ea634a05c08c0c0126001b9add5748b4bc11818024c00373656c1d16978230300498006e6b75169aa23030049804000001b9af845a5e08c0c0126001b9aef45a5e08c0a2126100003735ba8b4bc14128230049800882dcd6ea2d2f046060093000dcd86a2d33a5e08c0c0126001b9add45a5a48c0c01261bc00373656b751697823030049800000dcd86a2d2f046049840000dcd90add45a5e08c0c3126001b9b215ba8b4bc12e18024c003735ba8b4ec963230300498006e6b751697823030049857000dcd9f2dd45a79c8c0c0126001b9add45a690bc17823024c003fb6e6b7561978230300498006e6bd11697823030049813000dcd6ea2d2f04e460093080001b9add4785e08c0c0126008003735ba8b4bc11819224c008006e6b751e1782303004986f000dcd6ea2d2f0460850c0026001b9add4805e0970c0126100003735ba8b502978230300200006fcb751697823030049857000dcd6ea744c66c4bc118126001b9b555ac8b4bc11818024c003e0770b75169782303004980086900db99782303b060093000dcd6ea2d2f04d88c0c3126001b9add45a5e09b12e18024c003735ba8b4d69782303004980081cdcd6ea2d2f04605c093000eadb9b3e5ba8b48c0c0126001b9add45a6c4af11818024c004036e6b7516978252460498007f6e71b9add2f046060093000dcd6ea2d2f04605c0930b0001b9add45a764bc11918024c003735baa1d16978230300498007f6dcd6e9782303a460093000fedb9aa42f0460760c0126001b9ae95488b4bc11818024c003735ba8b4bc1181a424c038006e6b6149a2d2f046060093000dcd6ea2d44886cbc0c0126001b9b145ba8b4bc0c012624c003735ba8b4c411818024c008006e6b79169782303b060093000dcd6ea2d3046088c0c012600201b735ba8b4bc14118024c0038f5ba8b4bc11818024c3500081d00d6ea2d2f046060093000f81b9ad65268b4bc0c0126001dc37345a5e08c0c0126100003735ba8b4bc12923024c000007e8b751697823030051093000dcd6ea2d2f45e08c0c0126001b9add4928b5029e7230300003735ba8b4bc1181e6300498006e6b7557a2d2f046060093000e096ea2d31046060093080001b9add5488b4bc11819224c0039c6e6b75169782303004b800714dcd7a22d2f046060093000dcd6ea2d2f05648c0c0126001b9aef45a5e08c0c0126118003735ba8b4bc136240300498006e6b751697823030049851000dcd6eac445a5e08c0c0126001b9add5268b4bc14e18024c003735baa4d169d92bc300498006e6cf96eacd45a46060093000dcd6ea2d2f05388c0e9080001b9add4e88b4ec9b123024c003f45ba8b516978230300498007c0dcd8a2dd45a5e060093000dcd6ea2d2f04606009310a001c92dd45a5e08c11818024c003735baa811697829c300498006e6b751698223030049840000dcd9f2dd45a6748c0c0126001df2dd50a8b4bc11818024c003735ba8b4bc1181802f0498006e6b7549a743b25e060093000dcd6ea502f0460600a2126001b9add45a5e0a08c0126000003735f68b4bc11818024c3880083cdcd6ea2d2f046060093000dcd6ea2d2f05508c0c0126002053825ba8b4bc11818024c0036b5ba8b4bc11818024c0d8006e6c516ea7445a5e060093000f9ddc37345a5e08c0c0126001b9add4a08b4bc11818024c003735ba9d1169782303a4498006e6b75201e72f046060093000e498cadd45a5e08c0c0126001b9b215ba8b4bc1181a424c003b86e6925169e7230300498006e6b755222d31046060093000001b9add45a5e094918126001e03735ba8b4bc11818024c003735bab5516978230300498006e6d2d1697823030049857000dcd6ea2d2f04a48c093060001b9add45a5e0a711a18024c0043c6e6bbd1697823030049800724b75169782ac46060093000dcd6eacd586a9116978230001b9add5268b4f297818024c003f76e6b7516978230300498006e6b751695623030049873000dcd6ea2d2f04d88c0d2126001e23735ba8b4bc1181b624c003ab6e6b7520178230300498006e6b75169aa2f0460708c0000dcd6ea9f45a5e0a08c0126001b9add5068b4bc11818024c000006e6b75361b12f046049800738dcd6ea6c2f046060093000dcd6ea6c2f0460748c0126000003735ba8b4bc14118024c003735ba894bc11818024c2b8007e8dcd6ea2d2f046060093000dcd6ea2d2f050460093060001b9add4b08b4e697818024c000006e6b7538978230300498007f6dcd6e97829c46060093000ef9b9add50a5e08c0c0126000003735ba8b4bc1181c22e00037361a8b4d5178230300498006e6b7531a2d33a5e08c0c0000dcd6ead845a5e08c0c01260021a4036e6c84bc11818024c003925ba8b4bc11818024c0f8006e6b751697823030049826001039b9b675ba8b48c0c0126001b9add45a5e08f91818024c003736acb751697923030049800000e296ea2d2f04e460093000dcd6ea2d2f04bc8c0c0126001b9add45a7acbc11818024c003735bab0d169782303b060000868fedb9add2f046060093000dcdb9add4a05e08c0c0126001bf2dd45a5e08c0c012609800373642b751697823030449800778dcd6ea2d2f046060093000fedb9b215485e08c0c0126001b9afb45a5e08c11818024c003735ba8b4bc11814424c230006e6b751822d2f046060093000f816ea2d3d45e08c0c0126001ce3735baa4d31978230300003736b0b7516978230300498006e6d2d169782b246060093001101b9add45a5e08c0c0126001b9af44c68b4bc11818024c003735ba900ce978230300498006e6b751697825c46074893000dcd74a2d2f046060093008002073735ba8b48c0c01261bc003825ba8b4bc11818024c010006e6b753ea2d2f046060093000dcd6ea2d2f05388c0c012e001c12dd45a5e08c0c01261bc003735ba8b4ec9952f0460600006e6c856f22d2f046060093000dcd6ea6345a5e08c10a180001b9b3e5baac91691818024c003735528b4bc1181d8300498006e6b75169782303004980a000dcd6eac845a5e08c0c0126001b9add5268b4e211818024c00373628b75169b12f0300498006e6c657da2d2f046060093000dcd6ea853ce5e08c0c0126001b9add45a6c4bc1181d224c0038a5ba8b4bc118180288498006e6b751697829c4d851093000dcd7a22d2f0460600c0126001bf2dd45a5e08c0c0126028003735ba8b4bc118214300600006e6b753a22d2f046059893000dcd6ea5b3b25e08c0c0126001e23735ba8b50797823024c003735f68b4bc156230300498007e8b7516a252f046060093000dcd6ea2d2f046064893008001b9b395ba8b4bc11518024c003735ba8b4bc15323030049800714b7516a2d2f046060093000dcd6ea462f0460600930a2001b9add45a5e08c0c012604c003735ba8b4bc1181c230049800756dcd6ea852f046060093000dcd6ea2d3105e08c0e9126001b9b0045a5e08c0c0126200003735bab0d16978230300038006fcb751697823030049813001039b9add45a5e48c0c0126001e23735bab351697823024c000006e6b7516978296300498006e6c3516978230300498936e6c1d6ea9345a764bc0c0126001b9b215489d11697823024c003735ba8b4bc14e2303a45c0006e6b753922d2f046060093000dcd6ea6245a5e08c0c0126001b9add45a5e0999181fe24c004346e68b4e21181d8300498006e6b75169d937e46060093000dcd7da2d2f04606009303e001b9add45a6388c0ec18024c003735ba9b0bc14e230300498006e6b753a22d32846060093000f81b9add45a5e08c0e1180001fa3736968b4bc11818024c003735ba8b4c411818024c020006e6b59169782303b060093000dcd6ea2d2f04607b8c0126001b9add45a5e08c0c015224c003735ba8b4e211818024c068006e6d2d16978230300498260010edb9add4785e08c0c0126001b9add45a7b8bc11818024c0040e738b7531a2d2f046060000868dcd6ea6c2f046060093000f11b9add45a86cbc0c0126001b9add4e88b4bc1181c2300003736acb75169c4230300498007c0dcd86a2d2f04606009300100db9aef45a5e08c0c0126001b9add45a6a0bc11818024db9add5268b5041782303004980077cb75169c42303b060093000dcd6ea8533a5e08c0c0126001c53735ba8b4bc11818024c003955ba8b4bc11818024c400006e6c856ea2d31046049840000dcd6ea5845a5e09c8c0126001b9add45a5e0970c014424c003ab6e6b7549a742f0460498006e6b752c22d40a5e08c0c0000dcd86a7445a5e08c0c0126001b9b075ba8b4e211818024c004036e6b7516970230300498006e6b75169782a4460850c0000e71b9add4c67f8bc118180001b9b215bab0d1697823030000373666bed16978230300498006e6c858a22d2f046060093000dcd6ea2d2f04606d893080001b9add45a738bc11818024c003736968b4bc11818024c050006e6b75169b12f046059893000dcd6ea2d2f046060093088001b9add45a8b4bc12e18024c0039c6e6c8583a2d2f0460600006e6b756ea2d38846060093000001ce2d645a5e08c0c0126001b9add45a6a88c0a2126100003735de8b4bc11818024c000006e6b7531a2d2f04606009e000e71b9add45a5e08c0c0128001b9add45a5e09611818024c004347badad6ea2d2f0300498006e6b75169782303a460094000dcd6ea852f0460850c0126001ce2dd54e8b4bc11818024c003735e88b4bc11818024c2d0006e6b7561a2d2f04d88c0c0000dcd6ea2d31c4606009300e0022536b5ba8b4bc11818024c003735ac8b4bc11818024c038006e6b75169952f04606001b0010d1b9ae645a5e08c0c0126001fa2dd45a5e0bc11818024c00373642aa516978230300498006e6cf96ea2d23030049893000dcd9cadd45a5e08c0c0126001b9add45a5c08c0c0126000003736968b4bc11818024c098006e6d6d6ea2d31046060093000ea96ea2d2f05388c0b8126001dc3734b08b4bc11818024c003735ba8b4bc1181802fc498000010d1b9a2d2f0460850c0000001b9add4a05e08c0db126001bab735ba8b4bc11818024c003735ba8b4bc12923024c010006e6b75169782524604986f000dcd8a2dd45a5e060093002001b9b215488b4d897823024c000006e6b751697827c300498006e6bd11697827246060093001039b9add45a7108c0c0126001b9add4a05e0bc11818024c003735ba90116988230300498006e6b75169aa23030057893000fedb9add586a90bc118180000003735ba8b4bc1391a424c003e06e6cf96ea2d230300498006e6b752c22d30446060093000001b9aef45a5e08c0c0126001c12dd45a5e08c0e9126100003735de8b4bc11818024c18000000ef96ea2d2f0460850c0000dcd6ea2d2f050460093004001b9add45a6c4bc1181c2300003735ba8b4bc14118024c378006e6dcd6ea2d2f04b860093000dad6ea9345a5e08c0c0126001b9b3e5ba9d11691818024c004476e6b75169cd2f0300498006e6d056ea2d2f046060093000001b9add45a5c08c0c0126001b9add45a674a091818024c003a25ba8b4bc1181d8300498006e6b751697023030049830000dcd8a3075488b4bc0c0126001b9add4c88b4bc11818024c00373642b751698e230300498006e6b7516a0f2f046049840001039f02dd4b08b48c0c0126001b9add4928b50291818024c0037361a8b4d8978230300498006e6b75169782303f060093000dcd90ad645a5e08c0c0126000003735ba8b4d8995230300003735ba8b504978230300498006e6b7531a2d2f046060093000dcd6ea2d2f0460690a2126001b9b145baa911697818024c003735ba8b4d51181802a849800738dd96ea2d2f046060093000dcd6ea2d2f04c88c0c0126000003f45ba9611691818024c003856e6b7516978230300498006e6b751698e26c46060093000df96ea6345a5e08c0c0126001b9add45a8b4bc1181a424c003735ba8f0bc1181d8300498006e6b591697826c46060093000dcd6ea2d39a5e08c0c0126001b9add4e08b4bc11818024c003735ba8b4bc118180300498006e6b7566a2d2f046049840000dcd6ea7445a5e08c0a7126001b9add45a840bc11818024c003735ba8b500178230300498006e6b751697825c2e049840000dcd6ea2d2f0460600930d40020cb735ba8b4bc11818024c00373642c1d1697829c460600006fcb751697823030060093000dcd6ea402f0460600931260021a36b45a5e08c0ec18024c0037360cb5916978230300498006e6b751697823030049880000dcd8fadd45a5e08c0c0126000003735ba8b4b991818024c003e76e6b7516a0f2f0460498006e6b7524a2d41e79c8c093000dcd8cadd45a734bc0c0126001b9b305e88b4bc11818024c003735baa4d16978232300498006e6bf16ea2d2f046060093000dcd83add45a5e099918126001b9add45a86cbc0c0126100003735ba98d169782303004c8006d6b75169782303004980d000e896ea2d2f04606009300e001b9add45a734bc15618024c0036b6acb7516978230300498006e6b752c22d32a5588c0c0000f81b9add4805e08c0c0126001f037360cb5916978230300003735ba8b4bc11818228849800806dcd6ea4945a46060093000e296ea2d2f05e08c0c01260021a39b6d6b7516978230300003735ceb7516978230300498007f6f11b9add2f046060093000dcd77a2d31046060093080000003735ba98d2c19d2303000037367cb75169b1230300498006e6b75169782303004983e000dcd6ea2d2f046060093038001b9b735ba8b4bc1181a424c0036b60eb7516978230300498006e6b753a2402f046060093000dcd6ea2d32a460600930de001b9b145bab0d16978230300003735ba8b4f097829c300498006e6b751e17823030049807000dcd9a2dd45a5e08c0c0126001b9add45a734bc0c012607c003735ba8b4d5978230300498006d6b756ea2d2f04606009300100ddf2dd45a5e08c0c0126001b9af445a764bc11818024c003735ba8b4f6978230300498006e6b7524a2d43679c60093000dcd6ea4945a46060093000001b9add45a5e0b711818024c003e05ba8b5029e72f0460600006e6b75169d92f0460850c0000dcdb0add45a5e08c0c0126001ce3735ba8b4d217823024c003735ba8b4bc11818024c1b8006e6b75169c42f04a48c093000dcd8022d3b25e08c0c0126001fe3735ba8b4bc11818024c003735ba8b4bc152230300498006e6b75169a42f046074893000dcda5a6345a5e08c0c0126001ce3735ba98d16970230300003735ba8b4f39782302e0498006e6b751697823038460001000dcd6ea2d3625e08c0a7126001bf2dd45a5e08c0c01260dc003735ba8b4bc14223030049800744c856ea2d2f046060093000dcd6ea4245a5e08c0c0126000003735ba95d1691818024c004347c0f1116978230300498006e6b754297823030049893000ef96ea2d2f046060093000001b9b4b45a734bc11818024c003735ba8b4ee978230300498006e6d2d1697823030060093000dcd6ea2d2f04606009311c001b9add45a6b48c0e918024c003735ba8b4bc11c230300498006e6b75169782303004985a001039b5add45a5e08c0c0126001b9add45a5e08c0c01260c4003735ba8b4bc12923042876000756dcd6ea2d2f04605c093000dcd86a2d2f046060093002001d3add45a5e08c0e918024c003a25ba8b4bc136230300498007d4dcd6ea2d2f046060093000e496ea2d2f0460600930ae001f03b845a79cbc11818024c00373628b751697818024c02000000dcd6ea4945a46060093000dcd90add4785e08c0c0126001b9add4928b48c0c01260c0003e06e6b7542978230300498006e6b75169782f04b860093000dcd6ea2d2f04e48c0c0126001caadd45a764bc11818024c003735ba900bc12e230300498006e6b7516a052f04608c0c0000dcda5a2d39a5e0ab0c01260021a36b6428b4bc11818024c003735ba940bc1181b624c378006e6b751e17826c46060093000dcd6eaa445a5e08c0e1180001b9add45a654bc1692303000040e7c0b7549a2d2f0300498006e6b751698823028849840000001df2dd45a5e08c0c0126001b9b145ac8b4bc11818024c003735baa153a178230300498006e6b752ea3c2f046060093000f11b9add4d85e08c0c0126001b9add4806c4bc11818024c003735ba9611697823036c4980077cb7516978230300498300010a5b9add4e88b4bc118126001b9b195ba8b4bc13918024c003735eea4d16978230300498006e6b751697825246077893000dcd83aae45a5e08c0c0126001b9b545ba8b4bc11818024c00373632b7516a052f046060000001039b9afb45a46060093000e096ea2d2f0460760c0126001b9add5868b4bc118180288003735de8b4bc11818024c010006e6c355222d2f04606009300100db9add45a6a88c0c0126001b9aef45a5e08c0c01261bc003735ba8b4ce9782302e0498006e6b7516a253b246060093000dcd6eaae45a5e08c0c0126001b9add45a5e0ab13918024c003735ba900c4178230300498006e6b7534a2d40a5e08c0c0000002193735ba5e08c0c0126001b9add45a814bc156230300003735baa4d169952f046060000792dcd74a2d2f046060093000dcd6eac345a8b4bc118180001dc37345a5e08c11818024c000006e6c0d16978230300498006e6b751697023030049802000dcdb0b4b45a5e08c0c0126001b9add45a5c08c0c01261bc0037361a8b4bc1181c230051000858dcd6ea2d2f046060093000dcd9f2dd45a46060093002001b9add45a690ab1181261bc003735ba8b4fb178230300498006e6b75169a42f05388c093000dcd6ea2d2f046061093080001b9add5468b4bc11818024c0041d7e8b7516978230300498006e6b75169aa23030049800000dcd6ea2d3b25e08c0bf12600220b735f68b4bc11818024c003b86e6c6516978230300498006e6b751698223046060093000dcd6eaac45a5e08c0c0126001b9add45a5e09c8c012607c003735e88b4bc11818024c0d8006e6b75169ad23030059893000001b9ad745a5e08c0c0126001b9afb45a5e08c0c012615c000006e6b751698e272300498006e6b7516a052f04606001f000dcd6ea2d2f0460850c00360021a3735ba8b4d217823024c003925ba9411697823030049800000dc16ea2d2f046060093000e9d6ea2d2f0460600b3126001b9aa445a5e08c0ee18024c003735ba901169782303a4498007f6dcd6e97823030049840000ee1b9a2d2f05588c0c0126002073735ba9d1169b123024c003735baa4d17178230300498006e6cc16ea2d2f046060093000f6db9b0d45a5e08c0c0126001b9b195ba8b4c111818024c003825ba8b4bc11818024c038006e6b7529a2d2f046060093001071b9add5868b4bc118180001b9add45a5e0bc1181a424c003735ba8b509178230300498006e6cf983aa445a46060093000dcd6ea9d45a5e08c0c0126001b9add45a7f4bc11818024c003735ba96116a0f2f0460498006e6b596b22d2f046060093000dcdb9add5868b4bc118180001b9add45a608ab11818024c003735ba8b4ab11818024c3b8006e6b75429b12f046060093000001b9add45a6a88c0c0126001b9b3e5baa911691818024c003735ba8b4ca978230300068006e6b751698e23030051093000001c92dd45a5e0a08c0126001b9add45a5e08c10418024c003735ba8b4d511818024c18000770dcd169782303004981f000dcdb92dd45a5e08c0c0126001b9b565ba8b4ca978230300003735ac8b4bc11818028849800000dcd902d645a5e08c093000dcd6ea2d45a6388c0c0126001b9add59a9611697823024c003925ba8b4bc11818024c130006e6bdd6ea2d2f0460600930010d1b9add4665e08c0c0126001b9ad645a8b4bc11818024c003fb6e6b7566a2d2f0460498006e6b75169782303004982d0010396eaa44b08b48c0c0126001b9add45a6088c0c012607c003926e6b7528178230300498006e6c1d6ea2d32a5e08c0c0000dcd6ea2d3b25e08c0c0126001b9add45a5e0ae11818024c003735ba8b4bc11818024c100006e6b751697823038460004000dcd6eadd45a654bc118180001bf2dd45a764bc11818024c003735ba900bc11818024c0080081adcd6ea2d2e046060093000dcd6ea2d2f0460898c0126001b9add4b08b50d97818024c003735ba8b4bc11818024c2e000704c856ea2d2f046060093001039c92dd45a460600930de001b9add4f68b4bc11818024c003735e88b4c7178230300498006e6b75169782804e460093000e496ea2d2f046060093014002072dd59aa911697823024c003735f69411697823030049800000dcd6ea502ac46060093001121b9add45a5e08c0c0126001b9b0d45a5e08c0c0126010003825ba900bc11818024c200006e6b751697828c46060093000dcd6ea2d2ac46060093114001b9add5269d0d897823024c003735ba8b4bc1292303b049b9c6e6b7549a742f046060093000dcd6ea2d2f04a48c110126001c12dd45a5e09b11818024c004346e6d9d16978230300498006e6b751697823030049818000dcd6ea6c2f046060093080001b9add45a5e08c0c012602400373654c516ea2d2f0300498006e6b751699d2303004986f000dcdb9add45a6388c0c0126002073735ba8b4ca9782303000037362ab751697823030049800724b751697823030049813000dcdb9ad645a5e08c0c0126001b9aef45a5e08c0e9126100004206e6b7516978230300498006e6b7516a1d2f046060093000dcd6ea2d2f0504760c0126001b9b075ba8b4bc11817624c000006e6bed1697828230049800000dcd6ea8538846060093000dcd6ea4945a46060093004001b9add548900bc11818024c003735ba9251691818024c37800756e716ea6345a5e08c0c0000dcd6ea9c45a5e08c0c0126001b9add4de8b4bc11818024c003aa6e6b75169782303004980077cdcd6ea2d388460600930010e5b9add45a5e08c0c012600201b735d28b4bc11818024c0037367cc516ea2d2f0300498006e6bed1697823030049826000fbdb9add45a5e08c0c0126001b9add4c68d8bc11818024c003825ba8b4bc11818024c25000892dcd6ea2d2f046060093000001b9add5205e08c0c0126001b9add45a674bc91818024c003be5ba8b4bc11818024c010006e6bd11697827230049857001095d12dd45a5e08c0c0126001df2dd45a5e08c0c01261bc003a25ba8b4bc118180288498006e6b751697825246049807000dcd7a2f445a5e08c0c0126001b9af05ba8b4bc11818024c003735ba8b4bc129252460498006e6b75429782303004980100100db9add45a5e08c0c91260016eaa445a814f3978230300003736968b4ec978230300498006e6b75169782304287f8c0001039b9afb45a460600930de001b9ae945a5e08c0c01260000037367cb751691818024c020006e6d656ea2d30446060093000e896ea2d45a5e08c0c0126001b9afb45a5e08c0c0126028003e05ba8b502978230300498006e6b7565a2d2f046060093000fd1ce2dd45a5e08c0c0126001b9add45a5e09b11822024c00373696b75169952f0460600007e8b75169782303a460093000ed5b9add4e88b4bc118126001b9add45a79ce211818024c003735ba8b4bc11817024c49800806dcd6ea2f2f046060093000dcd6ea2d2f05046009300e001b9add4785e08c0c014424c003735ba8b4c3978230300498000010b9b9a2d2f046060093000dcd6ea2d2f046060093036001b9b495bab351697823024c00373642b75169b12ac460498006e6b751697823032449800000dcd6ea2d2f04608c0db126001ce3735ba940bc11818024c0037368cb7516978230300498006e6bed1697823030049813000dcd6eac345a5e0bc118180001b9add4788b4bc11818024c003735ba8b4bc11818024c11800806dcd6ea2d31046060093000dcd6ea502f0460748c0126001b9add45a6bcbc17023024c0037e5ba8b4bc11818024c0d800756dcd6ea2d38846060093000ee15222d3ce5e08c0c0126001b9add45a768bc11818024c003735baa8516978230300498006e6b751697823030049883000f81b9add45a5e08c0b8126001bf2dd4788b4bc11818024c000007f6dccbc1181d830049800000dcd74a2d2f046060093000001b9add4786088c0c01260020739c5ba8b48c0c01261bc003735baa9142978230300498007c0b7516a0f3ce5e08c093000dcd8cadd45a5e08c0db126001b9ae945a5e08c0c01260c0003735ba8f0c111818024c180006e6b75169cd2f030049857000dcd90add45a5e094918126001b9b4e5ba8b4bc11818024c000006fcba516978230300498006e6b75169d936246057893001039b9add45a460600930f6001b9add4e88b4bc11817024c0037e5d28b4bc11818024c18000744dcd6ea2d2f046060093000dcd6ea2d31046060093000001b9add45a5e0ab1181b624c003735ba8b4ce9782303004a8006e6b751697826c4a48c093000dcd6ea2d4085e08c0c0126000003735ba8b4bc11819224c003735ba8b4bc11819224c18000884dad6ea2d2f046060093000dcd6ea2d35446060093004001b9add4aa8b4bc11818024c00373642b7516978282300498006e6b75169aa2303004986f0010356ea2d2f05c08c0c0126001b9add45a5e08c0c013424c003925ba8b4bc14118024c378006e6bd149a2d2f046060093000001bf2dd45a5e08c0c9126001b9add4b08b4bf11818024c003735baa4d1697823042860000888dcd6ea2d2e446060093000df96ea2d2f046064893060001b9add45a710ce91818024c003735ba8b4bc11018024c180006e6dcd6ea3c2f046060093000dcd6ea2d2f04606009309e002233735ba8b4bc11818024c003fb6e6b752c178230300498006e6b752017823030049804000dcd6ea2d2f04606d89303e001b9add45a5e0a093618024c003735ba8b4bc11818024c408006e6b7547a2d44a5e060093000dcd6ea2d3ae5e08c0c0126001fdbfb6e6b74bc11818024c003e05ba8b50d9e72f0300498006fcdcd6ea3c2f046060093000dcd6ea2d41e5e08c118126001c92dd4c68b4bc11818024c000006e6b751698823030049800868dcd169c42f046060093000dcd6ea2d31c5e08c0c0126001b9b216328b4bc118126100003735ba8b4c411818024c180006e6b75169782303a4498460010d2074035ba5e08c0c0126001fa2dd45a5588c0c01261bc003735ba8b4bc11818024c22800788dcd6ea2d3485e08c093000fd16ea2d2f05388c0c0126001b9ad645a5e0bc11818024c00373642c1d1697826c460498006e6b751697823030052893001021b9add4785e08c0c0126001b9add45a56c8c0c01261bc003735ba8b4d41782d2460498006e6c856ea402f046049840000001b9add59ab0d16978230001c92dd45a5e08c0c018024c003735ba8b4e2118214300498006e6d2d169782303004981b000dcd8cadd45a83cbc1181260021a3735baa4cbc14e18024c00373642b751697826c4604980081cfed6eaa42f046060093000dcd6ea2d4367c0bc0c0126001cfb735ba8b4bc11818024c003e56e6b591697823030049b735baa4d16a052f0460600930010d1fa2dd45a5e08c0c0126001b9add59a8b4bc11823024c0039c714b7516978230300498006e6b75281562303004986f0010d1b9a2d2f0460850ec180001b9add45a5e09711817024c003be5ba8b4e2178230300498006e6b752817829c46060093000dcd6ea5945a5e08c0c0126001c52dd45a5e08c0e918024c003735ba8b4bc14e26c3a4498006e6b754ca2d2f046060093000dcd6ea6345a5e08c0b9126001b9add4988b4bc11818024c003735ba90516978230300498006e6b7516a0f2f05588c093000dcd6ea5845a5588c0c0126001eab735ba8b4bc11818024c003735e88b4bc11818024c068006e6b75169b12f04605c093000dcd6ea2d2f0460658c0126000003da5ba8b4bc11818024c003735ba8b4bc118214300068006e6d597a22d2f0460600930010d1b9add4a05e08c0c0126001b9b195bab351697823024c003735de8b4bc1181d8300498006e6b75169782303005c893000dcdab2dd45a5e08c10a180001b9add45a86cbc11818024c003be5ba8b4bc1182143b0600006e6b751697823045060093000dcd7da2d2f0504600930de001b9add52698cb811818024c000007f6dcd90978230300498006e6b7566a2d2f05588c093000db98cadd45a5e08c0c0126001b9add45a5e09111818024c003735deb751697825c300498006e6b7516a0f2f04604981f000dcdae2f445a5e08c0c0126001b9add45a5c08c0ec18024c0037360ebd116978230300498006e6c856ea2d2f04604984a000e096ea2d2f0460600a2126001fa3735ba8b4e697818024c004346e68b4bc1181de300498006e6c1d6ea2d2f0460850c0000dcd6ea2d2f04e4600930ae001b9b195ba8b50d97818024c0036b5ba8b4f3978230300498006e6b754297823030049804000dcd6ea404805e08c0c0126001b9add4768b4bc11818024c003735ba8b5029782303002b8006e6bd16ea2d2f046060093000dcd6ea2d2f04607f8c0126001b9add4e88b4bc11815a24c003735ba9b12c178230300498006e6bed31a2d2f046060093000dcd6eadd45a5e08c10a180001b9add45a734bc0c0126098003825ba8b516978230300498006e6c656ea2d2f048860093000001d4b6b5ba8b4bc118126001b9b005ba8b4bc11818024c003735ba8b50d9782ac300498006e6b751697823038451040000dcdaf2dd45a7648c0c0126001f03735ba8b4bc11e18024c003e06e6b6116978230300498006e6b7566a2d2f04604981f000eadb9b215568b4bc118126001b9add45a5e08c0f418024c003735ba8f0bc11818024c33800756dad6ea2d2f046060093000dcd6ea5845a5848c0c0126001b9add45a5e08c0d612619c003735f68b4bc118180300498006e6d51169782e046060093000dcd6ea2d32a654bc118180001b9b6d5ba8b4bc11818024c0039c6e6b751697825c30049800894dcd83a2d2f046060093000dcd86a2d2f046051093080001b9add59aa9d1697823024c003e05baa4d169e72f0300498006e6b751697825c3a460093000dcd77a2d2f04606009300e0021a3dd6e6b751697818024c003e06e6b75169781802cc498006e6b7516a2141e5e08c093001039b9af445a5e08c0c0126001b9add45a734bc0c0126028003735ba8b4bc11818024c2a000770dcd1697823030049857000dcd9f33e5ba8b48c0c0126002253735ba8b4bc11818024c003735ba8b50d97818024c0f80081cdcd6ea2d2f0460850c0000dcd6ea2d2f0460600930c4001d12dd45a5e0bc11818024c003735ba8b4b811818024c03800738c516eaa445a5e060093000f81d5add5268b4bc0c0126001c52dd45a5e0a711818024c00373696961169562303004980081cc516ea2d2f046060093000dcd6ea2d2f05a48c0c0126001b9add45a6088c0c012615c003735ba9d13617823028849800704dcd6ea2d2f046060093000dcd6ea2d39a5e0600930260020739c60eb7516978230300003735ba9d116976230300498006e6b75169c72f046060093000e7183add55a8b4bc118180001b5add45a674bc11818024c003735d28b4bc11818024c010006e6b75169d43485e08c093000dcd74a2d2f0460600930de001b9add4785e0bc11818024c00434714b7516978230300498006e6b75169782303004985d000dcd6ea2d2f04606009302a001f039c5ba98d169782303000037360eb751697822a300498006e6b753917829c46060093000dcd86add4e88b4bc118126001b9b345f68b4bc11818024c003735ba8b4d217823024c200006e6b7549a2d2f046060093000dcd6ea2d44286cbc0c0126001b9add45a6c4bc11815a24c003735ba8b4bc11817024c008006e6c8577a2d2f046060093000dcd6ea2d2f046064893004001b9add5408b4bc11818024c003735ba8b4bc11819224c37800000fd16ea2d3485e08c093000df96ea9345a5e08c0c0126001b9add45a6c4ab11814424c003735ba8b4bc118180254498006e6bbd2017823030049840000dcd6ea6c4d85e08c0c01260016eaa445a814bc11818024c0044f6e6b751697823030049800806dcd8a2dd45a5e060093001141b9add45a5e08c0c012600226b735baa4cbc11818024c003735de8b4bc136230300498006e6c856ea2d2e046060093000dcd86add4d85e08c0c0126001b9b215868b4bc11818024c003735ba8b4e41181fe300498006e6b751697823030049806000dcd6ea2d2f65e08c0c0126001ce3735ba8b4bc1181a424c003735ba8b4bc11a230300498006e6b75169c423030049893000dcd6ea2d2f0460748d2126001b9add45a5e09491814424c003735ba8b4b8136230300498006e6b751698823030049802000dcd6ea2d310460600930de001b9add45a850bc11818024c003735ba8b4bc13918024c130006e6b751697829c4b8600930010d1b9a2d2f0460760c0126001b9add45a814bc118180098004346e68b4bc118220300498006e6b7524a2d2303b060093000dcd8a2dd45a5e060093000001b9aff5ba8b4bc11818024c0040e5bab5916978230300498006e6b751697823030049850000dcd6ea2d45a5e094918126001b9add5488b4bc11817024c003735ba8b4ca9782e046060000000fedb9add5865e08c0c0000f81b9b555ba8b48c0c0126001b9b5660e8b4bc11818024c003735ba9b0d8978230288498005baa9116a0f3ce5e08c093000dcd76add45a5e08c0c0126001b9add45a690ca9782ac460004346e6b751697825c300498007c0dcd6ea2d38846060093000fedb9add2f04608c0c0126001b9add45a5e08c0c01260340039c6e6b753a2632f0460600006e6b75169b12f246060093000dcd6ea2d2f0504600a2126001b9b565ba8b4bc11818024c003735ba9b1169b12f0460498006e6b75169782303845c0a2000ef96ea2d2f0460760c0126001bf2dd45a5e08c0c0126034003735ba8b4bc13918024c050006e6cdd8a2dd45a5e060093000001b9b1f45a5e08c0b8126001b9b0d5ba8b4d897823024c003735ba8b516978282300498006e6b7542a852f0460600930010d1cdb735ba8b4bc118180001b9add4e88b4e211818024c003735ba8b502978230300050006fcd596ea2d2f046060093000dcd6ea7445a6c4ce91812600000373628c1d1697818024c003fb6e6c656e978230300498006e6b7538a2d2f046060093000b7566aa445a79cbc118126001dc37345a5e08c0c0126098003735ba8b4bc11818024c298006e6d716ea2d2f046060093000dcd83add45a5e08c0c0126001b9add45a5e08c0c014224c003e0756b753a22d2f046049800000dcd8a2dd45a5e060093000eedb9add45a5e08c0c0126001b9add45a5e08c0e918224c0039e6e6b7516978230300498006e6d2d49a2d2f046060093000dcd8a2dd45a5e060093060001b9add52a8b4bc11818024c003fb6e6b74bc156230300498006e6b756ea2d2f046060093000dcd6ea2d2f04e460093026001bf3075ba8b4bc11818024c003735ba8b502978230300098006e6b751697825646060093000dcd6eac245a5e08c0c0126001b9add4805e08c0a2126100003735ba8b4ff178230300498006e6b75169e732a5e08c0c0000dcd6ea2d3044606009304c001b9b735ba8b4bc12923024c003925ba8b4ec978230300498006e6b7524a2d230300498070010d1b9a2d2f04a48c0c01260016eaa445a86cf397818024c0037e5bab7516978230300498006e6b751697826c46051093000dcd91add45a5e08c0c0126001f9b735ba8b4bc11818024c003735ac8b4f417823030049800770dcd169782303004980a000dcd6ea9344a5e08c0c0126001b9add45a818bc11818024c004346d6b7549978230300498006e6b75169782303e460093000002073735ba8b48c0db126001b9aa445a5e08c0f318024c003fb6e6b74bc11818024c0f800756dcd6ea2d32a5e08c0c0000dcd6ea6345a734bc0c0126001fa3c45ba8b4bc11818024c0040e6e6b751691818024c4200081cdcdb32dd45a46060093000dcd93add45a5e0970c0126001b9add45a5e08c0f218024c0037360eb75169782303004c8006e6dcd6ea2d2f050460093000dcd6ea3c2f0460648c0126001df2dd45a5e08c0c012601c003735ba8b4bc11818024c0180081cdcd6ea2d2f046060093000e096ea2d2f05e08c0c0126001df2dd45a5e09491818024c003735ba8b4bc11818024c2c0006e6b751697829c46069093000e716eaae45a5e08c0c0126001b9add55a8b4bc11818024c003735ba8b4c111818024c050006e6b751699c2f046060093000ee1b9a2d2f046060093026001fdb735baa9cbc11818024c003735ba8b4e69cd2f0300498006e6b75169cd2f030060093000dcd6ea2d2bc460600930de001b9add45a814f71782303000040e6fcb751697823030049800724b751699d2303004986f000f11b9add4a05e08c0c0126001b5add45a5e0ad91818024c0038a6e6b751697827230049800868dcd6ea2d2f046069093000dcd6ea2d2f0460600bd126001b9add4d85e08c11818024c003735ba8b4bc11814424c250006e6b752922d2f046060093000fadb9ad645a5e08c0c0126001b9b4b45a5e08c0c0126034003735ba8b4bc11818024c138006e6b75169aa2303b0600930010d1b9b5645a7648c0c0126001b9add45a710d891818024c004546e6b7516978230300498006e6c1d5b22d2f046060093000001b9aa445a5e094918126001b9add45a6088c0c012604c003735ba8b4bc1181b624c2b8006e6d59a5a2d2f0460600930010d1b9b2145a5e08c0c0126001b9add51ca14bc11818024c003735baa7116978230294498006e6c856ea4945a4606009300100db9add45a5e08c0e1180001b9add56c8b4bc11818024c00373632b7536178230300498006e6b751699d32a5e08c0c0000dcd6ea2d2f0460600930dc001b9add45a5e08c0b8126010003735bab0d61a2d2f0460600006e6b7524a2d26c46060093000dcda5b0745a5e08c0c01260021f3735ba9251691818024c004036e6c3516978230300498006e6b7525a2d2f046060093000dcd7da2d3b25e08c0c0126001b9add4d85e0ab11818024c003be642b7516978230300498006e6b75169882303a449840000dad6ea2d2f046060093126001eeb6b5ba8b4bc11818024c00373696b7516978230300498006e6b75169ac2f046060093000dcd6ea2d2f046060093064001b9add45a5e08c0e11800000039c6e6b7561a2d2f0460600006e6c1d6ea2d390460600930010edb9ae945a5e08c0c0126001b9add5868b4bc1181d23000039c67cb755222d230300498006e6b7531a2d2f0460600a0000ef96ea2d2f04d88c0c0126001b9add5368b4bc12e18024c00373586a91169782303b0600006e6b75169d92ac538600930010f1b9add4805e08c0c0126001b9b0d45a5e08c0c0126000003735ba9b0bc11818024c0f8006e6d856ea2d39a5e06009300107db9add45a7648c0c0126001f036b5ba8b4bc11818024c003735ba8b4d511818024c03800000dcd6ea2d32846060093000e496ea2d2f046060093036001b9b015ba8b4bc11818024c003735f68b4ce91818024c3780081cdcda5a2d2f046060093000dcd6ea2d2f05408c0c0126001b5add4e88b4bc11818024c003735ba8b50797823024c2b8006e6b751697823030049816000dcd77a2d2f046060093084001b9add4b08b4d217823024c000006e6b751697823038460000768dcd6ea2d2f0460708c0000dcd6ea2d2f0460708c0060001b9add50a7108c0ec18024c003735ba8b4bc1181802ac49800788e296ea2d2f046060093000dc190add45a5e08c0c0126001b9add4a08b4bc1181b624c003735ba98d16978272300498006e6ba96ea2d2f04606009300112db9ad845a5e08c0c0126001b9add4c68b502978230300003735de8b4bc118180288498006e6c856ea2d2f046062893000001b9b0d45a5e08c0c0126001b9add45a708bc11818024c004036e6cf96ea2d230300498006e6b751697823044460093000dcd6eacd45a5e08c0930ae000003735ba989169782303000037361a8b4bc11818024c18000738b755226345a5e08c0c0000dcd6ea2d2f0460720c0126001b9add45a5e0bc12923024c003735ba8b4bc139180300498006e6bbd16a2d2f046060093000dcd6ea2d40a5e08c0c0180001b9add5205e08c11018024c003735ba8b4b8118180288498007c0dcd6ea2d2f046460093000e71b9add45a6388c0c0126001b9add5428b4bc11817224c00373642b75169aa230300498007e8b751697823030049840000dcd6ea2d31c460748c0126000003735ba8b4bc1411b624c0039c6e6b5916978230300498007f6b75521e72f046060093000dcd6b22d2f0460748c0126001b9add45a6748c0c01261ec0040e806b752c22d230300498006e6b75169c423030049801000dcd6ea2d45a5c08c0c0126001b9add45a86cbc0c012615c0037367cb751691818024c000006e6d2da5a2d2f046060093000dcd8a2dd45a5e060093004001b9b295ba8b4bc11818024c003735ba9611697a230300498006e6c516ea2d2f03004986f000dcd6ea2d2f05e0a08c0126001dc3734c68b4bc11818024c003735ba8b4d5136230300498006e6b751697823036c49826000dcd6ea502f046060093080001b9add5868b4bc14e23030000000744b753a22d2f0460498006e6bed169782303004981b000ee1b9a2d2f0460600c0126001b9b205ba8b4bc11818024c003735ba98d1698223030049800748dcd6ea2d2f046060093000dcd90add45a5e08c093108001b5add45a6c4bc11818024c004346e6b7561a2d2f0460600006e6b75169852f046060093000001b9b3e60e8b48c0c0126002073735ba8b48c0db1261bc000006e6b7542978230428600006e6dcd77a2d2f046060093000f81b9add5269d0bc0c0126001e23735ba8b4bc12e18024c003735ba8b4bc14e2303a460000868e71b9b0745a5e08c0c0000dcd90ac35488b4bc118180001b9add45a5e08c0db126028003735d28b4bc1181d8300498006e6b7516a223fc5e0600930010d1b92dd45a5e08c0c0126001df3735ba8b4bc118214300003735ba8b4c111818030049800000dcd9f2dd45a46060093000dcd6ea502f046060093114000003a25ba9b0bc11818024c003735baa91169c4230300498006e6cf96ea2d23030049830000dcd6ea2d2f0460630c0126000003735ba8b4ec9a423024c003735ba8b4bc118188300498006e6b75169b72f046060093000fd16ea2d32a5e0ab118180001b9add5268d8bc11818024c003736e6b7516970230300498006e6b751697826846060093000dcd6ea2d2f04a48c0f1126002073565baad91691818024c003735ba8b4c111818024c400006e6b75169782302bc4984000100db9add4805e08c0c0126000003735ba8b4c611818024c00373672a9116978230300498006e6b75169e12f046060093000dcd6ea2d2f04606d893026001b9add45a5e08c0ec19224c003735ba8b4d896323030049800000dcd6ea2d2f046070093000dcd6ead559a8b4bc118126001fa3735ba9611691818024c00373680b7516978230300498006e6b75429782303b460093000dcd6ea2d2f04606009305e001b9add4c69611699d230300003735ba8b4d0978230300498006e6b7516a0f2f046049826000dcd7a22d3ce5e08c0c0126001e73735ba8b4bc11818024c004576e6b751697823030049800770dad6ea2d2f046060093001039ba2dd45a5e08c0c0126001b9add45a79cbc118214300003735ba900bc11818024c000006e6b751698e29c46060093000f39b9a2d3fc5e08c0c0126001e1b735ba8b4bc11818024c003735ac8b4bc14e23030049800000dcd6ea4945a8148c0c0000dcd6ea2d310460760c0126001b9ae945a5e08c0c012601c003735ba8b4ca978230300498006e6c856ea902f046060093000e89ce2dd45a5e08c0c0126001b9add45a5e09c93918024c003ab6e6bd11697823030049800628b75169e72f046060093000e896ea2d2f0460748c0126001b9add45a78cbc11818024c004346e6b751698e230300498006e6b7566a2d2f046049826000dcd6ea2d3b2734bc0c0126001d5b735ba8b4bc118214300003ec6e6b751697823030049800868dcd6b22d2f046060093000e296ea2d2f046060093080001b9add45a83cbc118126028003f06e6b751697823030049800754b751697829c46060093000dcdab2df45a5e08c0c0126001b9add45a5e08c0c912601c0040e6e6b7515178230300498007c0dcd6ea2d32a5e08c0c0000e71b9add4785e08c0c0126001e23735ba8b4bc1181a424c003735ba9251691818028849800756e7183add45a5e08c0c0000dcd6ea3c2f0460748c0126000003735ba900bc11818024c000006e6c196b22d2f0460600006e6b7516a1b2f030049826000001dc3734928b48c0c0126001b9add4805e08c0c01260c0003f56e6b7516978230300498006e6b7516a0f2f046049813000dcd6eacd45a5e08c093014001df2dd5ac8b4bc11818024e1a3735ba8b4ec97829c30049800868dcd83a2d2f05388c0c000100db9add50a5e08c0c0126001b9add4928b51691818024c003da5ba8b4bc118220300498006e6b751697826246060093000dcd6ea7445a654bc118180001b9add5028b4bc11818024c003735beb7516978230300498006e6b751697823038460002000dcd6ea2d2f0460708c00de001b9af445a674bc11818024c003be5ba8b4bc118180288498006d6b751697823030049801001109b9b0745a5e08c0c0126001b9add45a674bc11821430000373642ba516978230300498006e6b751698823030049807000dcd89add45a5e08c0c0126002193735bab58bc11818024c003735bab351697823024c098006e6b7516a1b2f03004980a000ef96ea2d45a5e08c0c0126002213735ba8b4bc11818024c0037361a8b4bc11818024c0100086900de23732f046060093000dcd6ea852f046060093000001b9b0d45a5e08c0c01261bc003735ba8b4bc126230300498007f6dcd6e97823030049857000dcd6ea2d38846060093008001b9ae945a5e09b11818024c000006e6b751699523030037800724b7549a2d2f046060093000dcd90add45a5e08c0c9126001d63735ba8b4bc11818024c003735ba9d117178230300498005bab59169e72f046060093000dcd6ea2d3485e08c118126001b9add45a86cbc0c012604c003735ba8b4bc11818624c200006e6b751697825c30049840000fbdb9add45a5e08c0bd126002193735ba8b4bc11818024c003735ba8b4bc118214428600006e6b751697828236c4986f000dcd6ea6345a5c88c0c0126001b9b4b45a654bc11818024c003735de8b4bc178230300498006e6dcd6ea4945a46060093000f11b9ade45a5e08c0c0126001b9add45a5e09b11819224c004296e6b75169d9230300498006d6b755222d2f046060093000e896ea2d2f05388c0c0126001b9add45a5e08c0f818024c004346e6b8d1697823030049800870dcd6ea2d2f046060093000dcd8cadd45a690bc118126001b9add5268b4bc11817224c003735ba8b4bc136220300498006e6b751697823042060093000dcd6ea2d2f05c08c0c0126000003735baa14bc11818024c0037366cb7516978230384600006e6b7531a2d2f04606d893000dcd6ea2d4065e08c0c0126001b9b215ba8b4c411818024c003735ba8b4d419d2f0460498006e6b754297823030049830000dcd6ea2d3485e0ab1181260021a3a25ba8b4bc11818024c003735ba8b4bc11818a2884980077cdcd6ea2d2f046060093000dcd6ea2d362654bc118180001b9add45a734bc0c012606c003735ba900c411818024c200006e6b751697823043060093000dcd6ea3c2f05388c0c0126001b9add45a764bc13918024c003f45ba96116978230300498006e6b751697823036c60093000dcd9b30d45a5e08c0c0126001b9add45a6209b11818024c003735ba8b4bc11818024c2b0006e6b7516a053b25e08c0c0000dcd6ea2d3aa5e08c0c0126001b9add45a6a88c0c014424c003825deb751697823030049800724b75169782303004980d000dcd9f2dd45a460600930040020b37367cb751691818024c0037367cb751691818024c3780087eef96ea2d2f046060093000e49ab2dd45a5e08c0c01260021a3735ba8f0bc11818024c0044d6e0b7516978230300498006e6b75169a42f04604981f000dcd6ea584a05e08c0c0126001b9add45a8b4d511818024c004016e6b751697823030049800814dcd6ea402f046060093000dcd6ea2d2f05cc8c0c0126001b9afb5268b4bc11818024c003da642b7516978230300498006e6b751697829c4d85c093000dcd6ea4945a8948c0c0126001b9add4d85e08c0c012615c003735ba8b4f397823030049800724c1d6ea2d2f046060093000dcd6ea2d33a5e08c0bf126000003735ba8b4eb97018024c003b86e68b4ec978230300498006e6b75169782303004980b000e3d6ea7445a5e08c0c0126001c92dd5ba8b4bc11818024c0037e5ba8b4f3978230300498006e6b75169a42f05848c093000e71c12dd45a5e08c0c0126000003a96e6b751697823024c003735ba8b4c411818024c250006e6b751697823034849840000dcd6ea2d2f046051093108001b9b705ba8b4bc11818024c003735ba9c8bc1181802e049800704b75169782303a460093000dcd6ea6345a75cbc0c012600228b735ba8b4bc11818024c003ab6e6b751697823030049800000dcd6ea2d39a6c460093000dcd6ea6345a83cbc1181260000040e7f6b74bc11818024c00373668b751697823036c498006e6b75169d930446060093000dcd6ea634b0674bc118180001e23735bab0d16978230300003ab6fcb7516978230300498007f6dcd6e97823030049826000dcd6ea2d41e5e08c0c0126001b9add4a08b4ab11818024c003736e6b75169aa23030049800724dcd6ea2d2f050460093000dcd90add4e898cbc118126002073925ba8b4bc11818024c003735bab3531a2d2f0460498006e6d2d169a42f05588c093000dcd8a2dd59aa9116978126000003735ba8b4d811817024c003e06f2b75169782303004980081cdcd6ea2d23030049873001039f02dd45a7648c0c0126001b9b0759a8b4bc11818024c003735f68b4bc11818024c068006e6b756822d2f046060093000dcd75add45a5e08c0c0126000003735ba8b4ce9181b624c003736acbed16978230300498006e6c396ea2d2f046060093000001fa2dd45a7648c0c0126001fb3735ba8b4bc11818024c003735ba900bc11818024c010006d6b751697823030049804000dcd6eacd45a5e08c0c0126001b9add45a6748c0c0126210003735ba900bc11818024c37800798e096ea2d2f046060093000dcd6ea2d2f04b8600b8126001b9add45a674bc11818024c003fb6e6b74bc11818024c05000000dcd6ea2d2ac50460093000dcd6ea5745a5e08c0c0126001b9add45a5e0a712418024c003735ba8b4bc11818028c498006e6b753ba2d2f046060093000dcd6ea2d3e65e08c0c0126001b9add4c68b50d97818024c003735baa15169c4230300498006e6b752c22d39a55860093000dcd6ea3945a5e08c0c0126001f5b73642b751697823024c0037360ebed16978230300498006fcb751699d2f046060093000dcd8a2dd45a5e0760c0126001b9add45a5e09c8c012606c003735ba8b4ca97823030000800714b752c22d2f0460600930010d1b9add4b05588c0c0126002183f45ba8b4bc11818024c003735ba8b5029782303000d8006e6b75169782303004f893000dcd6ea2d4365e0600c0126001b9add4928b4bc11818024c003735f6b7516978230300498007f6dcd6e97823030049813000dcda5a2d3ce5e08c0c0126001b9add45a808bc11818024c004346dab7516978230300498006e6b754822d2f046060093000dcd7a22d2f0460600931260021a40e6e6d591691818024c003735ba8b4bc11821430049800788dcd6ea2d31c46060093000dcd6ea8245a5e08c0e1180001e23735ac8b4bc11818024c003735ba8b4bc11819e300498006e6b75169d932a5588c0c0000ef96ea2d2f05e08c0c0126001c12dd45a5e0a711818024c003ab6e6d2d16978230300498006e6b7567a2d2f046060093000dcd6ea3145a5e08c0c0126001b9add45a6c4ab1181d224c003e06e6bd11697823030049800770dcd169782303004981b001039b9afb45a5e08c0c0126002263735ba8b4bc11818024c00000738c516ea2d2f0300498007c0dcd6ea2d2f0460850c0000dcd6ea6a45a5e08c0c0126001b9add4d85e08c0c012609800434704b7516978230300498006e6b755222d32a5e08c0c0000dcd6ea2d2f05688c0c0126001b9add45a5e08c0dd18024c003735e89d116978230300498006e6ba51697823030051093000dcd8a2dd45a5e06009300e001ce3735ba8b4bc12923024c00000714b751697823034849800806dcd6ea2d2f04605c093000dcd6ea7445a5e08c10a180001b9add50a5e08c0c0126008003735ba8b4c111818024c0d8006e6b75429782303004986f000dcd6ea2d2f04a48c0e9126001b9add45a6c4bc14818024c003e0738c1d6ea2d2f046060000000dcd6ea4945a83c8c093000dcd5222d2f04a48c0ec126001b9b075648b4bc11818024c0040e5bab0d16978230300498007f6dcd169782303b060093000dcd6ea2d2f04606009301c001b9ae945a8b4bc11818024c003735ba8f116982230300498006e6b753ea6c2f046060093000dcd6ea7445a5e08c0e1126001b9add45a7d0bc11818024c003735ba8b4dd978230300498006e6b75361782303004980a000dcd6ea8345a6c4bc118126001b9add4b08b4bc12e18024c004346e68b4bc1181e2300498006e6b755922d2f046060093000dcda5a2d33a5e08c0c0126001b9add45a5e08c0c914424c003735ba8b4c71782723004980088efd16ea2d2f046060093000e71b9add45a5e0a08c0126000003735d28b4c111818024c0040e738b7516978230300498006e6ba51698223030049830000e716eaad45a5e08c0c0126001b9add45a5e0a08e918024c003735ba8b4bc11817024c00000868fa5b9a2d2f046060093000dcd6eab945a5e08c0c0126001b9add45a5f4bc11818024c004346e6d5949978230300498006e6b75389782303a4600930010395222d2f0460760c0126001b9add45a8b4bc11819224c00373642b75169d9362460498006e6b7561a2d2f0460600400010d1b9add2f05a48c0c0126001b9add4d85e08c0c012604c003735ba9b0bc1181c2300498006e6b75169782d646060093000001b9add45a6088c0c9126001b9add45a6088c0c91260c0003735ba8b4bc14a282300498007e8b751697823046060093000dcd6ea2f45a5e08c0c0126001b9add5268b4e697818024c004346e6c1d49978230300498006e6b751698823030051093000dcd90b145ba8b4bc0c0126001b9add45a6a8bc11818024c000006e6b7524a2d436300498007aadcd6ea2d40a5e08c0c0000dcd6ea2d4287f8bc118126001b9add45a5e08c0c013c24c000007c0b7516a052f0460600006e6a99169782303b060093000e716eab645a5e08c0c0126001b9b735d28b4bc11818024c004346e6b7549978230300498006e6b75169f72f046060093000dcd6ea2d45a6208c0c0126001b9add4805e08c0e9126100003735ba8b50da052f0460600006e6b75169d92f04606d893000001b9add45a5e08c0b8126001b9b145ba8b4bc13618024c003c4744b751697823030049800806dcd6ea2d2ee46060093000dcd6ea502f04608c0c0126001b9add45a5e08c0c014824c003f4632b7516978230300498006e6b751697826c46074893000dcd6ea2d2f04605c093060001bf3735d28b4bc11818024c003735ba9d131970230300498006e6bd1169b12f046060093000dcd6ea2d348654bc118180001b9add45a6c4bc118214300003735baa85169d92f0300498006e6b75169782303b0708c0000dcd6ea2d3245e08c0c0126001b9add45a5e0b311818024c003f45ba8b4bc156230300498006e6dcd6ea2d2f046064893000dcd7a2dd45a5e09c8c0126001b9add4c6960bc11818024c00373632b7528178230300498006e6b75169782b646060093000dd16ea2d3ce5e08c0c0126001b9add45a6c4bc1181c224c003d5770dcd16978230300498006e6b751697823030860093000f11b9add4785e08c0c0126000003e07708b4bc11818024c003735ba8b500978230300498006e6b75449782303fc60093000fedb9add4c65e08c0c0126001bf3735ba8b4bc11819224c003fb6e6c516eaa42f0300498006e6b751697829c4a48c0930010b9b9a2d44a5e08c0c0126001b9b395ba9d11697823024c0037361a8b4bc1181d8300498006e6c351697823044060093000dcd6ea5845a5e08c0d2126001b9add4a05e0ab11818024c003b86e68b50d978230300498006e6b751698e23030049840000dcd6ea2d2f046060093076001b9add45a6748c0db1261bc00434788dad169782303004980081cf816b22d2f046060093000eadba2dd45a5e08c0c0126001b9add45a654bc118180010003735ac8b4bc11818024c200006e6ba56ea3c2f046060093000dcd6ea2d39a5e06009301a001fa2dd45a5e08c0c012607c003fb6e6b74bc11818030049800868dcd6ea2d2f04a48c093000dcd6ea2d2f046074893094001b9b565ba8b4e697818024c003736e6b7516988230300498006e6b753897823030059893000dcd6ea2d2ac504600930de001fdb736428b4bc11818024c003735ba8b4bc14e28230049800770dad169e72f046060093000dcd6ea2d2f05388c0e1170001b9add45a5e08c0c012624c003735ba98d169782303004b8007badcd6ea2d2f046060093000dcd6ea502f04606009303e001bbb735ba8b4bc11818024c003735ba8b4bc11820430049800868dcd6ea2d2f050460093000dcd83add45a734bc0c0126001b9add50a710bc11818024c0037367cb7566aa445a460498006e6b751698e2303004988a000001b9add45a5dc8c0c0126001b9add45a83cec97823024c003735ba8b4bc1181c2300038006fcb75169782303004989300100db9ad845a5e08c0c0126001b9add4e898cbc11814424c003735ba951169782303004980081cc855222d2f046060093000dcd6eadd45a734bc0c0126001b9add5268b4bc11c18024c003735baa7516a1b2f030049800726dcd6ea2d2f046060093000dcd6ea2d2f04606009307a001f03735ba8b4bc11818024c003735ba9ed16a0f2f0460498006e6c351697823030049807000dcd6ea2d2f0460738c0126001ed3735ba8b4bc11818024c003735ba8b5129b1230300498006e6b751697826c46059893000dcd6ea852f0460850ec180001b9add45a690bc11812615c003735bab35169d92f0460498006e6b751699e2f046060093000001b9add45a64c8c0c0126001b9add45a5e08c0ea18024c003e06e6c6583a2d2f0300498007c0df96ea2d2f046060093000e296ea2d2f04608c0c0126000003735ba8b4e2118214300003735debbd16978230300498006e6b7549a2d2f04e460093000dcd9f2dd45a460760c0126001bcadd5488b4bc11818024c00373642b8116978230300498006e6b751695623030049880000dcd6ea2d2f046060099126001b9add4e88b4bc11818024c00373642a99169782303004980081cb755222d3b246060093000dcd6ea9345a814bc118180001b9b075ba8b4bc14e26c300003e06e6c656ea2d2f0300498007e8d2d169782ac46060093000dcd9cadd45a6c4bc118126002073735ba8b4e697818024c000006e6b751697829c4d8748006e6d2d169782b646060093000df96ea7445a5e08c0c0126001b9add45a5e08c0db12606c003735ba9b131978230300498006e6b756322d2f046060093000dcd6ea2d2f04a88c0c0126001c53195ba8b4bc11818024c003735ba8b50d9d92f0300498006e6c855222d2f04d88c093000dcd90add45a5e08c0e1180001b9add454674bc11818024c003735e88b4bc11818024c008007aedcd6ea2d2f046060093000ea5b9b6b5ba8b4bc118126001b9add45a5e08c10a180004003735ba9b0bc11818030049800714b75169782ac46060093000dcd6ea2d3d25e08c0c012600201b9c5ba98d16978230300003735baa14bc1181de300498006e6c518a2dd45a5e060093000e71b9aef45a5e08c0c0126001b9add4ac8b4bc11818024c003d677cb751697823030049800770dcd49a2d2f046060093000001b9ad845a5e08c0c0126001b9aef45a5e08c0e918024c003735ba8b4bc136230384600006e6c8586a2d2f046060093000dcd83add45a5e08c0c01400000039c67cb751691818024c003735ba8b50517823030049800744b751697823030049840000dcd6ea2d2f04606e0c0126001b9ae945a5e0bc11818024c003e05ba8b512978230300498006e6b751e1822f0460600930010d1b9b5e45a5e08c0c01260020d3735ba8b4bc11818024c003735ba8b4d21782b2460498006e6d2d1697823030049893000e71b9add45a5c08c0c0126001b9add5b88b4bc11818024c0037367cb751691818024c038006e6b75169702303a460093000e296ea2d2f04606009303e00208b735ba8b4bc11818024c0037361a8b4bc13623030049800846dcd6ea2d2f046060093000dcd6ea2d2f04e46009301a001b9add5268b4c111818024c00000714b751698e230300498006e6b75169832f046060093000dcd6ea2d2f0460600930c8001b9add45a814bc118180034003736acb7516978272300498006e6b7562a2d2f046060093000dcd6ea2d37a654bc118180002143a25ba8b4bc11818024c003b36e6b7516978230300498006e6d2d6ea2d39a5e060093000dcd6ea2d2f05e08c0c9126001b9b565ba8b502978230300003735ba8b4bc12e230300498006e6b751e17823030049840000f11c12dd45a5e08c0c0126001b9af45488b4bc11818024c003735488b4bc1181fe30049800000dcd6ea2d2ec46060093000dcd6eaa445a5e08c10a180001b9ada45a764bc11818024c003e06e6d2d16978230300498006e6b751697823a46060093000dcd6ea2d3625e08c0c0126001b9add45a83cbc11812606c003735ba900bc1181d8300498006e6c1d6ea2d2f04e460093000dcd6ea2d2f04606d0c0126001e63735de8b4bc11818024c003735ba8b4bc11817024c010006e6c1d6ea2d40a5e08c0c0000dcd8cadd45a5e0970c0126001b9b075baa24bc11818024c003735ba8b4bc11817024c378006fcb75169b12f046060093000dcd6eac34b08b4bc118180001b9b4b4e88b4bc11818024c003735bab7516978272300498006e6b751698823030049884000e7183add5488b4bc118180001d52dd45a5e08c0c017024c003735bab7516a052f046060000806dcd6ea2d38846060093000fedb9add5868b4bc118180001dc37345a5e08c0c0126034003735ba8b4c4178230300498006e6b75169782ac4b860093000dcd6ea2d3b26c48c0a2126001b92dd4b08b4bc11818024c003925ba8b4bc1181b630049800770dcdab22d2f046060093000dcd6ea2d40a7f8bc118180001b9add59a8b4bc11812606c003f46e6b75169a42f0460498006e6c516ead645a5e060093000dcd6ea2d2f04808c0c0126001b9b3e642b751691818024c003735ba9d112978230300498006e6b75169822303004980d000dcd6ea2d3485e08c09304c001b9b145ba8b4bc0c014424c003735baa4d169d92f0300498006e6b75169782303004984d0010396eac35488b4bc118180001dc37360e8b4bc11818024c003736acb7516982230300498006e6b75169c423030049800001039b9add45a5e09c8c0126001b9b3e5ba8b49b11818024c003735ba8b4bc13918024c2c0006e6b751697825c3004981f000dcd8cadd45a5e0900c0126001b9add45a86cbc0c012606c0037354e8b4bc1181d83004980081cdcd6ea2d40a5e08c0c000109db9b215ba8b4bc118126001dc3735ba8b4bc11818024c003735de8b4bc14e230300498006e6c516ea2d45a5e060093000e496ea2d3ce5e08c0c0126001b9add50c8b4bc11818024c003735ba900bc11818024c038006e6c1d6ea2d30446060093000dcd6ea2d3184d88c0c0126001d73735ba8b4bc11818024c0040e7c0d596ea2d23030049800868dcd77a2d2f046060093000dcd6ea2d3485e08c093014001b9add586a9916978230300000005baa9116a052f0460600006e6b751697029c46060093000dcd6eadd45a6088c0c0126001d5b925ba8b4bc11818024c003735ba8b4ec978234300498006e6b75169782303004984b000dcd6ea2d2f04608c0d2126001fdb7367cb755211818024c0039c6e6c1d5322d2f04606000075cdf96ea2d2f046060093000001b9b215868b4bc118180001e42dd45a5e08c0ff18024c003735baa14bc1181d8300498006e6b751697826c46053893000001b9b555ba8b48c0c0126001b9b1b5ba8b4bc11818024c003735ba8b4bc11818024c248006e6b752c22d31c46060093000dcd6ea4945a7c88c0c0126001b9b645ba8b4d511818024c003736d8b751697823030049800868dcd6ea2d2e046060093000001b9add45a7108c0c0126002073b86e68b4bc11818024c003735ba8b4bc11818024c488006e6b592c22d2f046060093000e71b9add4ae8b48c0c0126001b9add45a7108c0c01260c0003736968b4d8978230300498006e6b75169a42f046049813000dcd6ea2d3b25f88c0c0126001b9b195ba8b4bc1181a424c0038c6e6b7516978230300498006e6bed1697823036c60093000dcd6ea6d45a5e08c0c0126001fdb735ba764bc11818024c003735d28b4bc118192300498006e6c858ca2d2f046060093000dcdb9b145ba8b4bc0c0126002073735ba8b4c111818024c0040e6e6b751691818024c3b8006d6b75169782303b460093000dcd6ea2d2f05588c0d2126001ce3735ba9251691818024c003735e88b4bc11818024c020007dedcd6ea9345a5e060093000dcd6ea2d2e65388c0c0126001b9add4928b48c0e918024c003c46e6b7516978252460498006e6b75169812f046060093000dcd90add4805e08c0c0126001b9ad645a5e08c0c015a24c000007c0b7516a0f2f0460498006e6b751697823042860004000dcd6ea2d2f05788c0c0126001b9add45a5e08c0c01260040038a5e88b4bc11818024c2b800724b751699d2f046060093000dcd80a2d3625e08c0c0126001b9add56e8b4bc11818024c003735ba8b50da0f2f0460498006e6b751699d23030049873001099b9add45a5e08c0c0126001b9add45a5e08c0c919224c003736d4b7516978230300498006fcb751697823030049801000dcd6ea402f04d88c0c0126001df39c5ba8b4bc11818024c003735f68b4f397823030049800704b751697823030049840000001b9add4e88b4d5118126001b9b275de8b4bc11818024c003be5ba8b4bc1181d2300498006e6b75169782303484981f000f11b9add45a5e0a08c0126001b9add50a5e08c0c012601c003e97c0b751697823030049800000dcd6ea2d31c46069093000ef95222d2f0460760c0126001b9add50a5e09491818024c003925f6b751697823030049bab6e6b7549a632f046060093000dcd6ea6b45a5e08c0c0126001b9add45a764ab11818024c003735ba8b4bc11818024c3f000756dcd7da2d2f046060093000001b9add45a6bcbc118126001b9b075488b4bc11818024c003735ba8b50417823030049800888dcd90a2d2f046060093000dcd6ea9345a5e08c0db1260000040e6e6b752811818024c000006e6b75361aa230300498006e6c8553a2d2f046060093001039b9add45a46060093114001b9add5488b4bc11818024c004036d6b7516978230300498006e6b755122d2f046060093000dcd6ea2d39a654bc0c0126001b9b386428b4bc11818024c003735ba8b4f017825c300498006e6b7516a1b4365e060093000dcd6ea2d2f0460600b7126001b9add45a700bc11818024c004497f6dcd6e978230300498006fcb755222d2f046060093000fd16ea2d2f0460600930ae001ce3735ae8b4bc11818024c0037367cc516ea2d230300498006e6b7516978230384600a2000dcdb42dd45a5e08c0c01260015222d3ce5e08c0ec18024c003735ba8b4f517823030049800000dcd8fa2d2f046060093000dcd6ea6c3b25e08c0c0126001d12dd4b08b4bc11818024c003735ba8b4be178230300498006e6b751697823030049836001145ce2dd45a5e08c0c0126001b9b215baa14bc11818024c003ab738b7516978230300498000010356ea2d2f046060093000dad6ea2d2f04606009300000220b735ba940bc11818024c003735ba8b51697823038460000852dcd90add45a5e08c093000dcd6ea2d2f046060093078001b9afb45a674bc11818024c003735ba940bc11818024c2b8006e6c351697823030051093000dcd6ea2d2f0460748c5126001b9add45a5e08c110126100003735ba8dd1697823030049800704b751697823030049847000dcd9f2dd5528b48c0c0126001b9add45a764b091818024c003735ba96116969230300498006e6b7524a2d29c46060093000001b9add45a5e099918126001b9add54a8b4bc11818024c003735baa14bc136230300498006e6d2d1697823030049801000dcd86a2d45a5e08c0c0126002243735ba9b0bc11818024c0039c6e6b75169aa230300498006e6b75169ff2f04606009300112db9add45a5e08c0c0126001fdb735ba5e08c0c012606c003735ba9611e178230300498007c0ef96b22d2f046060093000f6db9add45a5e08c0c0126001b9add45a6a88c0e918024c003735f6bed16978230300498006e6b751697828046069093000e896ea2d2f0460600ad126001b9add45a5e08c0db126034004346e6b7524a2d230300498006e6d596ea2d2f04606d893000dcd83add45a5c88c0c01260016eaa445a894bc11818024c0044a6dcb751697823030049800000dad83a2d2f046060093000dcd6ea794785e08c0c0126001b9add5268b50797823024c003be5ba8b4bc14e230300498006e6b7561a2d2f04608c0c0000001b5add45a5e08c0c0126001ce2dd59a8b4bc11818024c003735ba98d169a42f0460498006e6d2d169d92ac460600930010c9f03735ac5e08c0c0126001b5add45a5e08c0c01260c0003c860eb7516978230300498006e6c1d6ea2d2f04606d893000e896ea7445a5e08c0a21260021a3be5ba8b4bc11818024c003736e6b7516978230384600006e6c856ea934e85e08c093000dcd6ea2d39a690bc118126001b9add45a690bc11818024c0040e6e6c856ea2d362460498006e6b7566a9345a5e08c093000dcd6eadd45a5e08c0db126001b9b195bab0d1697823030000373696a9116978230300498006e6b75169782303a449884000dcd6ea2d2f0504600930ee001b9add45a5e09491812610000373628b75169782f0300498007c0b59169e72f046060093000e71b9b1960e8b4bc118180001b9b7361a8b4bc11818024c003735bab0d169782ac460600006dcb7549a2d2f046060093000dcd9f2dd45a460600a2126001d12dd4d85e08c0c014424c003735ba8b4bc11818024c108006e6b7542a2d2f0460850c0000dcd6ea2d38846060093004001b9add45a7108c0c01261bc003735baa4d16a1b2f0300498007c0ead6b22d2f046060093000dcd6ba2d2f05388c0c0126001b9af445a5e08c0d212615c00000730b7516978230300498006e6b75282502f046060093000dcd6ea2d2f050460093080001b9b3e5ba8b51691818024c003735ba8b4bc1181802c449800830dcd6ea2d2f046060093000dcd6ea2d39a690bc156126001d12dd4d88b4bc11818024c003735ba98d19978230300498006e6b751697823030049804001039b9add45a5e08c0db126001b9add5268b4bc12218024c003735ba8b50797823024c06800744c356ea2d2f046060093000dcdab2dd45a83cbc118126001c52dd45a5e08c0c012615c003f47e8b7516978230300498006e6b75169e32f04e460093000dcd6ea2d2f04d48c0c012600190aa445a79cbc11818024c003735bab0d169782303000f8006fcb751697823030049804000dcd90b0745a5e08c0930800021a3705ba8b4bc11818024c003735ba8b4bc1181c6300498006e6b75361782303004981b000dcd6ea2d36e6088c0c0126001b9add45a6388c11818024c003f45ba8b4bc11818024c130006e6ced6ea2d2f046060093000e89b9add4e88b4bc118126001b9b215ba8b4bc118126100000006e6b7528178282300498006e6b591697823046060093000dcd6ea2d3545388c0c0126000003736a88b4bc11818024c003735bab351697823024c068006e6c1d6ea2d41e5e08c09300103db9add45a5e08c0c0126001b9add45a7e0bc11818024c003736acb7566a2d2f046049800788dcd77a2d2f046060093000e496ea2d2f046060093126001d12dd45a6c4bc11814424c00444738dcd6ea2d2f0460600006e6b756ea2d41e5e08c093000dcd8cadd45a6388c0c0126001b9add4a05e08c0c0126098004346e6b75169aa2303004980081cd596eaa445a46060093000dcd6ea6245a894bc118180001b9add45a79ce697818024c003bf6e6b751697823030049800000e096ea2d2f04b860093000e716eab245a5e08c0c0126001b9b195ac8b4bc11818024c003736e6cf96ea2d230300498007e8b75169782303004980a000f11b9add45a5c08c0c0126001d13735ba9b0bc11818024c003735ba8b4bc1181d82e0498006e6b7516a1b2f03004980d000dcd83add59a8b4bc118126001b9add45a638ab11818024c003735ba8b4bc11818024c1d000000dcd8a2dd59a8b4bc093000dcdab2dd45a86cbc0c0126001b9b4b45a690bc11818024c003735ac8b4bc156230300498006e6b756eacd45a5e08c093000f81c92dd45a5e08c0c0126001d5b735ba8b4e697818024c0040e6e6b752811818024c378006e6d6d6ea2d2f046060093000dcd6ea2d3b25e0a70e9180001b9add4805e08c0c014424c004036e6b75169952f0460600006e6b75281782303004980a000dcd6ea8e45a5e08c10a180002073735ba8b50797823024c003f45ba8b4bc11818024c098006e6c6583a2d2f05388c0c0001039b9add4b08b48c0c0126001b9add4e88b4bc11814a24c003825ba96116978230300498006e6b75169a52f046060093000dcd83add45a86cbc0c0126001c92dd4e88b4bc11818024c003735ba90116978230300498006e6b751698e2303004981f0010d1d5b736428b4bc118126001b9add45a5e0970c012615c003ee6e6b7516978230300498006e6b59169782303004981f000dcd6eadd45a86cbc0c0126001ce3735d28b4bc11818024c0038e5baa4d16978230300498006e6bc91697823030049851000dcda5a2d2f046060093008001b9b215ba8b4bc11812611c003735ba940bc11818024c098006e6ba5169782303a460093000dcd6ea2d32a5e08c0c0000002073735bab351697823024c003735ba8b4ca178230300498006e6b753617823030052893000dcd6ea8f45a5e08c0c0126001ce3735ba8b4bc118180260004036e6b7517178230300498006e6bbd6ea2d31046060093000dcd6ea2d2f04605c09300e001b9add45a5e08c0c0126234003735ba8b4e699d2f030049800738dcd6ea2d2f046064893000dcd7da2d2f046060093126001b9add45a5e0a58c0126228003735ba8b4bc178230384600006e6b75169782303a464893000001b9af745a5e08c0c0126002073735ba8b50d97818024c003735ba8b4bc11818024c2f8006e6b75169bd2f046060093000dcd6ea2d3887108c0c0126001b9add45a624bc11818024c004346e6b751c97823030049800744b751697823046060093000dcd86a2d2f05e08c0c0126001b9b735ba900bc11818024c00373632b8d1697823030049800714b751697823030049826000001b9add45a654bc118180001f03735f68b4bc11818024c0036b5ba8b4bc11818024c010006e6b751697825c30049851000dcd6ea2d32a5e08c0c0060001b5add45a5e08c0c01261bc003de6e6b751697823030049800756dcd6e22d2f046060093000ecdc92dd45a5e08c0c0126001ce3735ba8b4c411818024c003735ba8b4bc1181802d0498006e6b756d22d2f046060093000dcd6ea852f0460600a2126001d13195ba8b4bc11818024c003735ba8b4c41181d2300498006e6b75169c4230428760c0000dcd6ea3c2f04608c0c0126001b9add45a6c4bc11814a24c000006e6b752d978230300498006e6bed3a22d2f046060093000dcd6ea2d2f0460830c0126001fdb735baa4cbc11818024c003e05ba8b4f9178230300498005bab0d5222d3ce5e08c0c0000e496ea2d3625e08c0c0126001b9add50a8b4bc11818024c003735ba8b4f3978272300498006e6c856ea2d2f04604984c000e896ea2d2f05588c0c0126001e83735e88b4bc11818024c00373642b75169782302e049800714b75169782303004980a000dcd6ea2d40a79cbc1181800021a3735ba8c4bc11818024c003735ba8b4bc1181a424c2b8006e6b75169782303004985e000dcd952dd45a5e08c0c0126001b9b195ba8f0bc11818024c003735ba8b4b191818024c378007a6dcd6ea2d2f046060093000dcd6ea2d2f05bc8c0c0126001b9aef45a5e08c0c01261000040e6e6b6916978230300498006e6cf16ea2d2f046060093000eadb9add45a5e09c8c0126001b9add45a5e09b11817024c003e0738b751697823030049800756dcd6ea2d40a5e08c0c0
  | 9 => 0x21a3c46e68b4bc11818024db9add45a5e08c0c0126010013735ba8b4bc11818024c378047c0dcd6ea2d2f04606009300edcd6ea2d3ce5e08c0c014424c003b86e68b4f3978230300498006e6cf96ea2d2f0460600936e6b7516a2d3ce5e08c0c0126dcd6ea6345a5e08c0c0126101b9add4e88b4bc11818024c03bab6e6b7516978230300510936e6d79ab2dd45a5e08c0c0126dcd6ea2d2f0460600c0126101b9b215ba8b4bc11818024c49bab6e6b7516a2d2f0460600936e6b75169b12f0460760c0126dcd6ea5845a5e08c0c0126099b9b5e60eb751697823030049b735ba8b4bc136230300498937c0dcd90add45a5e08c0c0126001b9add45a5e09211818024db9add45a764bc15723030049b736e6b75169e72f0460600936e6b751699d2f0460600a2126001b9add45a5e08c0a2126101b9b215ba9d11697823030049be06e6b751697826c460600936e6b752c22d2f046060093014dcd6ea2d45a674bc11818024dd5b736e6b751697823030049b735ba9d11697826c460600936e6b75169b12f04606009300edcd6ea5845a5e08c0c012604dce3735baa4d16978230300498006e6b7516978230300578936e6b7549a2d2f0460748c0126f11b9add45a764bc11818024c003735ba8b4e21181d8300498006e6b7516978230300498466e6dcd6ea2d33a5e08c0c0126001b9add45a5e08c0c0126031b9add45a5e08c11818024c2b8006e6b7516978230300550936e6c856ea2d3625e08c0c0126dcd702dd45a5e08c0c012604c003735ba8b4bc14e26c30049b735ba8b4bc1181d8300498016e6cad8cadd45a5e08c0c0126dcd8cadd45a5e08c0c012615dce3735ba8b4bc11818024c06b735ba8b4bc1181d23004980d738dcdab2dd45a5e08c0c0126dcd6ea2d3625e09b11818024db9b565ba8b4bc1181d230049c4a868dcd6ea2d2f0460600936e6b75169782ac460600930aee71b9b075ba8b4bc11818024db9b075ba8b4bc1181d2300498006e6b996ea2d2f0460600936e6b75169aa2f0460600a2126001b9add45a5e08c0c014024c000006e6bd11697823030049b9c6e6b756ea2d2f046060093000001b9add45a5e08c10a180dcd6ea9345a5e0a711818024db9add5ba8b4bc1181d2300498006e6b7516978230300498056e6b75169782303004985703ee71b9add45a7f8bc11818024db9add5488b4bc1181d8300498006e6b751698e23030049857868dcd6ea9345a5e08c0c0126dcd6ea2d2f04606009300e005b9add45a79cbc17823030049b7360eb751697823030049873000dcd6ea2d2f0460618c0127039ce3735ba8b4bc11818024db9add45a6fcd897823030049c03806dcd6ea2d2f04606009381cdcd6ea2d2f0460748c0126eadb9add45a5e0bc11818024de23735ba8b4bc11818024c0d8006e6b7516a052f046060093000dcd6ea2d2f0460768c0126dcd6ea634b08b4bc11818024c0039c5baa9116978230300498006e6b7516978282460600936e6b752c22d2f0460600c0126dcd6ea2d2f05388c0c0126035b9add5488b4bc11818024c03b735ba8b4bc118180250498016e6d596ea2d2f05388c0c0126dcd6ea2d2f04608c0c0126099b9add45a5e08c0c014424c49b735ba8b4ec978230300498406e6c856ea2d2f0460600930030d1b9add45a5e08c0c0126034003735ba8b5079e72f046049b735ba98d1697823030049843868dcdab2dd45a5e08c0c0126f81b9add5ac8b4bc11818024db9add45a8b4bc11818024c49b7360eb751697829c460600936e6b751699d2f05e08c0c0126dcd6ea2d2f04d88c0c0126005b9b195ba8b4bc11818024c133f46e6b75169782ac460600936e6b756ea2d2f05388c0c0126f81b9add45a5e08c0c014424db9add45a5e08c11818024c054346e6c1d6ea2d2f04606009300100db9add45a5e08c0c0126dcd6ea2d2f05588c0c012609a01b735ba8b4bc11818024c183e06e6b7516a2d2f046060093868dcd6eadd45a5e08c0c0126dcd6ea7445a5e08c0c014424c003735ba8b4bc1181a430049b73642b755222d2f0460600936e6c656ea2d2f046060093014fa5d5b735ba8b4bc11818024db9add45a5e08c11818024c09b735ba9d116a2d2f0460600936e6b75169782303b060093008001b9add45a86cf397818024db9ade5ba8b4bc11818024c008006e6b75169782303004980081cdcd6ea2d2f05388c0c0126dcd6ea2d2f04606009304c07db9add45a5e0a711818024c2c3735ba8b4bc1562303004980a6e6b751697823030049830000dcd6eaa445a5e09b11818024db9b735ba8b4bc11818024c49b73632b751697823030049813869039b9add45a5e08c0c0127135b9add4e88b4bc11818024c003735ba9611699d230300498007c0f116ea2d2f0460600936e6b75169782ac46060093026dcd6ea2d2f04606009303e029f03736e6b7516978230300498006e6b75169782303046009383f039b9add45a5e08c0c0126000003735ba8b4bc11818024c003735ba8b4bc11818024c183735ba8b4bc11818024c180306e6dcd6ea7445a5e08c0c01260000037e5ba8b4bc11818024db9add45a5e08c0c012607c09b735ba8b4bc11818024c03804000df96ea2d2f046060093060dcd6ea2d2f04606009308006db9add45a6c4bc11818028849b735ba8b5169b12f0460600936e6b752c22d3ec5e08c0c0126dcd90add45a5e08c0c0126011b9add45a5e08c0c013024c053735ba8b4bc1412303004986f6e6b751697826c46060093008dcdb9add45a6c4bc11818024c000006e6d2d16978230300498006e6b751698823030049840000dcd6ea2d2f046060093072dcd6ea6345a5e08c11818024db9b145baa911697823030049bc46e6b7549a2d2f046060093000e71b9add4c68b4bc118180dcd6ea2d2f04608c0c018024db9add50a8b4bc1181d830049b73632b7531a2d2f0460600936e6b75169782f04606009312700db9add45a5e08c0c012600a01b735ba8b4bc11818024c37b735ba961169d92f0460600936e6b7531a2d2f05588c0c0126dcd8cadd45a5e08c0c018024db9add45a5e08c0c014424c00be06e6b75169782f0460600936e6b75169cd2f05588c0c0126dcd6ea2d2f05588c0c018024db9add45a5e08c0c0126008003735ba8b4bc11818024c378006e6b7516978230300498570aedcd6ea2d45a5e08c0c0126005f2be06e6b751697823030049b735ba98d169782303004981f788dcd6ea2d2f04606009301adcd6ea7445a5e0bc11818024de23736acb751697823030049beb756dcd6ea2d2f046060093000dcdb3add45a5e08c0c0127111b9add4c68b4bc11818024db9add45a5e08c0c018024c0fb735ba8cd1697823030049813788dcd83add45a5e08c0c0126dcd6eaa445a5e08c0c014424db9b5e5ba8b4ce978230300498006e6b751697823030049802000dcd6ea2d2f0460600930def11b9add5ba8b4bc11818024db9add45a5e08c0c01260c0013735ba8b4bc11818024c378306e6b755222d45a5e08c0c0126001d5b735ba9d11697823024db9b735ba8b4bc11818024c00b826e6b75169782303004984081cf11b9add45a5e08c0c0126001b9add45a5e4bc11818024db9add45a6c4bc11818024c423735ba8b4d89782f0460600936e6b7549a2d2f046060093080dcd6ea5845a5e08c0c012606db9b735baa911697823030049c2981cdcd6ea2d2f046060093000dcd6eaab45a5e08c0c0126e71b9add45a79cbc11818024db9add45a79cbc1181d230049b735ba8b4bc11818024c2b8268850d1b9add45a5e08c0c0126eadce3735ba8b4bc11818024db9b195baab91697823030049bab6e6b75169782303a4600936e6b75169782303004984001adcdab2dd45a5e08c0c0126101b9add45a5e08c0c012615c053735ba8b4bc11818028849804000dcd6ea2d2f0460600930eadcd6ea2d45a5e08c0c0126010003736d6b7516978230300498006e6b75169c42f0460600936e6c1d6ea2d2f046060093080e71b9add45a674bc11818024db9add45a5e08c0c012615c09b735ba8b4ce9782303a460093000dcd6ea2d2f046074893080dcd6eadd45a5e08c0c0126100003735ba8b4bc1182143b0603735ba8b4ec97823046060093000dcd6ea2d2f04606009301e001f03735baa4d1697818024db9add45a5e0bc11818024c00b735ba8b4f397829c4606009381cdcd6ea2d2f046060093080dcd8cadd45a764bc11818024db9b735ba8b4bc11818024c024346e6b75169e72f046060093756dcd6ea2d2f05388c0c0126dcd6ea2d2f046060093004009b9add45a5e08c0c01261bc0138a6e6b7516978230300498576e6b75169782303004986f0dedcd6ea2d3b25e0ab11818024c003735ba8b4bc1181de30049c34756dcd6ea2d2f0460600937c0dcd6ea2d3d05e08c0c0126dcd6eaa445a5e0bc11818024db9add45a5e08c0c0126098133735ba8b4ec9782303004981f000dcd6ea2d2f046060097126dcd6ea2d33a5e0a711818024dba3735ba8b4bc11818024c00b735ba8b4bc11818024c1300a7d6f81b9add45a5e08c0c012700db9add45a5e0b191818024e1a3735ba8b4ce97823030049800000e496ea2d2f046060093806dcd6ea2d2f0460760c0126dcd6ea2d2f04606009304c04db9add45a5e08c0c0126028053735ba8b4bc1182303004981b83edcd6ea2d33a5e08c0c0126dcd6ea2d3ca674bc11818024db9add5269611697823030049b735ba98d16978230300498576e6b755025845a5e08c0c0126dcd6ea2d2f0460760c0126001b9add45a5e09b11818024c02b73632b75169782303004981b000dcd6ea2d2f046060093044001b9add59aa911697823024db9add45a5e08c0c012604c053735ba8b4bc11818030049857000dcd6ea2e45a5e08c0c012600201b9c5ba8b4bc11818024db9add45a5e0ab11818024c0d8006e6b75169782c646060093806dcd6ea2d2f04606009300edcd6ea2d2f04606009302604c003735baa4d31978230300498006e6b75169782303b060093000001b9afb45a5e08c0c0126001b9add45a5e08c11018024db9add45a5e08c0ec18024c183735ba8b4bc178230300498046e6b75169782303004981f036e71b9add45a5e08c0c012624db9add4b08b4bc11818024c06c27756dcd6ea2d2f0460600936e6b75169782303a460093126dcdab2dd4b08b4bc11818024db9add45a5e08c0c012601c003735ba9d1169f22f04606009383cdcd6ea6345a5e08c0c0126f81ce3735ba8b4bc11818024db9b075ba96116978230300498006e6b75169b12ac460600937c0dcd6ea2d2f0460748c012700db9b215ba8b4bc11818024db9add5ba96116978230300498006e6b751697829c4605c093000dcd6ea7445a6c4bc118126e71b9add4e88b4bc11818024db9add4e88b4bc1181d2300498006e6b751697823030049807000dcd6ea2d2f04a48c0c012700db9add45a5e09b11818024db9add45a5e08c0c01260c003b735baa0d31a2d2f0460600937aee71b9add45a5e08c0c0127039b9add4b08b4bc11818024db9add4c68b4bc11818024c134346e6b75169782b6460600936e6b7516978272460600930aedcd6ea2d2f0460600c012609800373642c1d16978230300498006e6b75169782303004a093788dcd6ea2d3ce5e08c0c0126dcd6ea2d2f05388c0c012624c003736acb75169d9230300498006e6c856ea2d2f0460600936e6b7531a2d2f046060093014001c92dd45a5e08c0c01261bdb9b215ba8b4bc11818024c184346e6b751697823030049893000dcd6ea402f046060093080f11d5b735ba8b4bc11818024db9add45a5e08c0c018024c050006e6b751697826c46060093738dcd6ea2d3625e08c0c0126dcd6ea2d2f04d88c0c01260c1f03735ba8b4bc14e23030049b735ba8b4d89782303a4600936e6b7531a2d2f0460600930260021a4036e6b74bc11818024db9add5268b4f817823030049c347c0dcd6ea2d2f046060093894dcd8cadd45a5e08c0c0126dcd6ea7445a5e0a711818024db9add45a5e08c0c018024c098007f6dcd6eaa42f046060093852eadb9add45a5e08c0c01270d1b9add4e88b4bc11818024db9add45c8b4bc11818024c010006e6b796ea2d2f046060093000de5b9add45a5e08c0c0126dcdab2dd45a5e08c0c01261c4003735ba8b4bc11818024c2500081cdcd6ea2d3b2460600936e6b7549a2d2f04608c0c0126f11b9add45a674bc11818024db9add4c68b4f7178230300498006e6b75169782303004982e6e6b75169782303b060093004dcd6ea2d2f0460760c01261bc003735ba8b4df978230300498006e6bed169782303004986f6e6c656ea9345a5e08c0c0126000003735ba8b4e697818024db9add5268b4bc15623030049b735ba8b4ec978230300498576e6b751697e2f04606009301adcd6ea2d3625e0a711818024db9add45a5e08c11818024c06b735baa4d169782303004981f6e6d596ea2d2f04608c0c01270d1b9add45a6c4bc11818024c003735ba8b4bc11818024c3db735ba8b4bc11818024c038026e6b75169782303004986f00ee71b9add45a5e08c0c0126005b9add45a79cbc11818024c203735ba8b4bc1181d2300498016e6c656ea2d2f04606009301adcdab3195ba8b4bc11818024db9b075ba8b4bc118230300498006e6c516ea2d2f0460600936e6b75169782ac4606009301a001b9add4c68b4b811818024c0039c6e6c1d6ea2d2f0460603735bab751697823046060093756dcd6ea2d2f046060093080dcdab2dd45a5e0ab11818024dce3735ba8b4bc11818024c3f373632c1d6ea2d2f0460600936e6d9d90add45a5e08c0c0126dcd6eac35488b4bc11818024db9add4c698d1697823030049c036e6b751697823030051093000dcd6eaa945a5e08c0c0126dcd8cadd5ba8b4bc11818024db9b075ba8b4bc15623030049b735ba8b4bc11818024c0f80d738dcd6eaa445a5e08c0c012700db9add45a8b4bc11818024db9add4c68b4bc11818030049b736acb75169782303004981f6e6b755222d2f0460748c0126dcd6eadd45a5e0ab11818024db9b215ba8b4bc11818024c0140e6e6b75169782304606009384edcd6ea7445a5e08c0c0126dcd90add45a5e08c0c01261bdb9add45a5e08c0c013824c0db735ba8b4bc118180288498006e6b7516978230300600c0126000003735ba8b4bc13918024db9add45a674bc11818024c203735ba8b4bc136230300498026e6b751697826c460600930dedcd83add45a5e08c0c012607c000006e6b7516a052f04606040e6e6c656ea2d2f0460600936e6b751697823030049857036dcd6ea2d3885e08c0ec18024db9add5ba8b4bc11818024c0fc446e6c1d6ea2d2f046060093000dcd6ea2d2f046060093085039b9add45a5e0ab11818024c003735bab591697823030049b735ba8b4ec97823030049826756dcd6ea2d2f04606009308edcd9c3075ba8b4bc11818024db9add45a5e0a711818024c00c036e6dcd6ea2d2f046060093000dcd6ea2d2f0460600a2126dcd6ea2d2f0460600a21260c000000770dcd1697823030049c346e6b75169782303004980181cdcd6ea2d2f04606009303edcd6ea814b08b4bc11818024c003735ba8b51697823030049bb5756dcd6ea2d2f046060093000dcd83add45a5e0a7118180dcd6ea2d45a5e08c0c01260c1b9add45a764bc11818024c053c46e6b751697823030049893000001b9add45a6088c0c0126001b9add45a6088c0c01260c1b9b195ba8b4bc11818024c194426e6b752c22d2f046060093001135b9add45a5e08c0c0126dcd6ea2d3b25e08c0c012604db9b4b5ba8b4bc15623030049b735ba98d16978230300498316e6b755222d2f05388c0c0126f81e23735ba8b4bc11818024dd5b735ba8b4bc11818024c15b735ba8b4c717823030049857868dcd6eaa445a5e08c0c0126001b9b735ba8b4bc11818024dce3735ba8b4bc11818024c023c46e6b753a22d2f0460600936e6dcd6ea2d2f046060093060dcd6ea2d2f0460748c0126010003735c6b7516978230300498006fcdcd6ea2d2f0460600936fcdcd6ea2d2f046060093060f5de23735ba8b4bc11818024db9add45a5e08c0c01260980db735ba8b4ce9782303004984c6e6bd16ea2d2f0460600930ae001b9add45a894bc11818024db9add4b08b4f397823030049800868dad6ea2d2f0460600936e6b75169782303004b89300edcd6ea2d2f046060093036029e23735ba8b4d897823030049bab6e6b752c22d2f046060093806dcd6ea2d2f05e08c0c0126dcd6ea2d2f04606009303604c003735ba8b4bc11818a30049b735ba8b4bc14e23030049804000dcd6ea2d2f0460600930cedcd6ea2d2f046060093126101b9add45a5e08c0ec1d830049c296e6b75169b12f046060093868dcd6ea2d2f046060093008dcd6ea6345a764bc11818024db9add45a5e08c0c014424c013735ba8b4bc1181802884986f7c0dcd6ea2d2f046060093080dcd6ea5845a674bc11818024db9add45a764bc11818030049b735baa4d16978230300498576e6b7516a2d2f046060093004dcd6ea2d45a5e08c0c01261bc000006e6b751697823036c49b735ba9d11697823030049840000dcd6ea2d2f046060093108001b9b665ba8b4bc11818024db9add45a764bc11818024c400006e6b75169782f0460600936e6b75169782f046060093060dcd6ea2d32a5e0ab11818024db9add45a5e08c0ec18024c0380081cdcdab2dd45a460600936e6b7516978252460760c0126001f2b735ba8b4bc11818024db9add45a5e09111818024c133735ba9a92c22d2f0460600936e6dcd6ea2d2f046060093004dcdb9add45a5e08c0c01261bdb9add45a5e08c0c012615c06bc46e6b7516978230300498016e6d596ea2d2f0460600930ae000003735ba8b50797823024db9add45a5e09711818024c20373642b75169782303b0600936e6b75169782303004980700edcd90add45a5e08c11018024db9b075ba8b4bc11818024c2b8006e6b75169d933a460600936e6b75169b12f046060093080001b9add45a5e08c0f118024c003746e6b751697823030049b735bab7516978230300498576e6b751697826c460760c0126dcd6ea6345a5e08c0c012606c003e96e6b751697823030049800000dcd6eacd45a5e08c0936e6b75169882f046060093080f11b9add5488b4bc11818024db9add45a5e08c0c018024c0db735baa8531a2d2f0460600936e6d596ea2d2f05648c0c0126000003735ba8b50d97818024db9add5268b4bc11818024c1340e6e6b751697823030049857788dcd6ea2d3d45e08c0c0126dcd90add45a5e08c0c012601c003735ba8d91697823030049b735ba8b4f3978230460600936e6b751697826c4606009300edcd6ea9345a5e08c0c0126028003735ba8b4bc11819230049b735ba8b4bc11819230049830756dcd6ea2d2f04608c0c0126dcd8cadd45a79cbc11818024db9add5268b4bc11818024c09b735ba8b4f39782ac460600936e6b751697b2f046060093014dcd6ea2d2f04606009304c035d5b73632b751697823030049b73642c856ea2d2f0460600936e6d596ea2d2f04606009304cde5b9add45a5e08c0c012601db9add4b08b4bc11818024c498006e6b751697823036c4986f6e6b75169782303a460093018eadb9add45a5e0ab11818024db9add45a5e0bc11818024c013735ba8b4bc11818024c200016e6b75169782f0460600930dedcd90add45a5e09b11818024db9add45a79cbc11818024c0fb7360eb751697823030049826880dcdab2dd45a5e08c0c0126dcd6ea2d33a5e08c11818024db9add45a5e08c0c0126034053e06e6b752c22d2f0460600936e6d596ea2d2f046060093014dcd6eadd45a5e08c0c0126099b9add45a5e09b13623030049bc46e6b751697823030049804756dcd6ea2d2f04606009303edcd8cadd45a674bc11818024db9add4e89611697823030049b735ba8b4ec9d92f0460600936e6b75169782303004981301adcd83add45a5e08c0c0126029b9b565ba8b4bc11818024c09be06e6b7516978230300568936e6b751699d2f05588c0c0126dcd6eadd45a5e08c0c0126029b9add5488b4bc11818024c2040e6e6b7516978230300498266e6c1d6ea2d2f046060093026001b9add45a7a0bc11818024db9add5ba8b4bc11818024c09b735ba8b4ce9782303004981f881039b9add45a5e08c0c0126001b9add4e898cbc11818024db9b565ba8b4bc1181ee30049c1a6e6b752c22d2f04606009381cdcd6ea2d2f046060093014001b9b5e5ba8b4bc11818024c000007f6dcd6e97823030049800724dcd6ea2d2f04606009381cdcd6ea2d2f046060093026001f5b735ba8b4bc11818024db9add4b08b4d897823030049b735ba8b4bc1181d8300510936e6b7549a6345a5e08c0c0126dcd6ea2d45a5e08c0ec18024db9add5268b4bc11818030049b735ba8b4ec9782303004981b6e6ce583add45a5e08c0c0126dcd6ea6345a5e08c0c012601a01b9c6e6b751697823030049c036e6b75169782303a4600936e6b751697823030049840008000003735ba9b0bc11818024c003735ba8b4bc11818024c2cb735ba8b4bc118180288498076e6dcd6ea2d2f0460760c0126dcd6ea6345a5e08c0c0126035b9add45a8b4bc11818024c038006e6bbd6ea2d2f0460600936e6d596ea6345a5e08c0c0126dcd6ea2d2f0460600c0126034003735ba8b4f917823030049b736acb7516978230300600936e6b75169782303004f09303e001b9add45a764d891818024db9b075ba98d16978230300498006e6b7561a2d2f046060093868dcd6ea2d2f0460768c0126dcd90add45a5e08c0c0126109b9add45a5e08c11818024c49b735bab7531a2d2f0460600936e6c1d6ea2d2f0460600c0126001ce3735ba8b4bc11818024db9b215ba8b4bc11818028849b9c6e6b751697823030049830000dcd6ea2d2f0460748c0126dcd6ea5845a5e08c0c0126005b9add45a5e08c0e918024c183735bab751697823030060093000dcd5222d2f0460760c0126dcd8cadd45a5e08c0c012624db9b735ba8b4bc11818024c03be06e6b7516978230460600936e6c856ea2d45a5e08c0c0126dcd6ea2d2f04d88c0c014424db9add45a5e0ab11818024c498006f6dcd6ea2d2f04606009381cdcd6ea6345a5e08c0c0126dcd6ea4045a5e08c0c012610201b735ba8b4bc14e23030049b735ba9d116978230460600936e6b7516a2d2f04d88c0c0126f81b9b195ba8b4bc11818024c003735ba8b4bc11818024c39c4d6e6c856ea2d2f0460600936e6b75169782303004981b037039b9add45a5e08c0c018024e1a4036e6b751697823030049be06e6b75169782ac460600936e6b75169782303004989303edcd8cadd4e88b4bc11818024db9add5489611697823030049bfb6e6b755222d2f0460600936e6b753a22d2f05588c0c0126dcdb9b215ba8b4bc11818024c003735ba8b4bc11e23030049b926e6b75169782303004986f7c0dcd6ea2d2f04606009303e0021a3736ac8b4bc11818024db9b735ba8b4bc136230300498007c0dcd6b22d2f046060093000dcd6ea2d2f0460600b3126e71b9add45a5e08c0c01260e5b9add4e88b4bc11818024c0fb7360eb75169782303004985a000dcd6ea2d2ac460600930de001b9add45a5e0a711818024db9add45a79cbc11818024c2bb735ba8b4bc14e230300498300010d1b9b0745a5e08c0c0126dcd6ea2d2f05e08c0ec18024db9add45a6c4bc11823030049800868dcd6ea2d2f046060093868dcd6ea2d2f046060093060001b9b215488b4bc11818024dd5b735ba8b4bc11818024c2bb735ba9d1169782c2460600936e6c656ea2d3625e08c0c01260020fb735ba8b4bc11818024c003735ba8b4f297823030049b735ba8b4d89782ac460600936e6b7549a2d3b25e08c0c0126dcd6eaa045a764bc11818024db9add45a5e0bc11818024c03b735ba8b4ce978230300498576e6b75169b12f04606009303edcd6ea2d2f04888c0c012606db9add4b08b4bc11818024c02427806dcd6ea2d2f046060093738dcd6ea2d2f046060093004e71b9add45a5e08c0c01261bdb9add45a5e08c0e918024c013735ba8b4bc1181d23004986f6e6b75169d92f04606009301adcd6ea9c5268b4bc11818024db9b565ba8b4ec97823030049b73642b75169782f0460600936e6b75169e72f04606009304cdcd6ea2d2f04608c0c0126005b9add45a5e0bc13623030049b7360eb75169d92f0460600936e6b7516978230300510a2126dcd6eadd45a764bc11818024dd5b735ba8b4bc11818024c13373632b75169782303004980100109db9add45a5e08c0c0126000003735ba8b4d217823024db9add45a8b4bc11818028849b735ba8b4f39782303004980a000eadb9b215ba8b4bc118126dcd6ea2d2f05588c0c0126004003735ba8b4bc11818029c49b735baa4d169782303004981b6e6b7516a2d45a5e08c0c0126001b9add586a9116978230301b9add5488b4bc11823030049bab6e6b75169782303004980a81cdcd6ea2d3b25e08c0c0126dcd6ea2d3ce5e08c0c012604db9add542a4d1697823030049b735ba8b4bc14e230300498026e6b751697829c460600930dedcd6ea2d2f04606009303e005b9add45a674bc11818024c13373632b755222d2f046060093806f11b9add45a5e08c0c0126eadb9add45a5e08c0c012604db9add4728b4bc11818024c134346e6b7516978230300498027d2dcd90add45a5e08c0c01270d1b9add45a5e08c0c01261bc003735ba8b4bc15723030049b736e6b751697823030051093000dcd6ea2d2f04606009302edcd6eaa445a5e0ab11818024db9b735ba8b51697823030049b735ba8b4ce9782303004980a6e6b75169782303004981b01adcdab2dd45a5e08c0c012606db9add5488b4bc11818024c0fb735ba8b4ce978230300498136e6c1d6ea2d2f046060093036dcd6ea9345a5e08c0c014a24db9add5ba8b4bc11818024c0d800788dcd6ea2d2f046060093788dcd6ea2d2f046060093060dcd6ea2d2f04606009312615db9b736e6b751697823030049b735ba8dd169782303004981f6e6b7531a2d2f05c08c0c0126001b9ae95ba8b4bc11818024db9ae95ba8b4bc11818024c183e06e6b75169782303004985781cdcd6ea2d2f04606009303600214b735ba8b4bc11818024db9add45a5e08c11818024c023735ba8b4d21782ac46060093000dcd6ea2d2f04648c0c0126dcd6ea7445a5e08c0c012615e01b735ba8b4bc11818024c0a373632b7516978230300498046e6b7531a2d3ce5e08c0c0126dcd6ea2d2f05588c0c01260121a3736d6b751697823030049c036e6b7516978230300498406e6b75169e72f0460600c0126eadb9add4c68b4bc11818024db9add45e8b4bc11818024c050006e6b7549a742f046060093894dcd6ea9345a5e08c0c0126002073735ba8b4d891818024db9add45a5e08c0c012607c023735ba8b4bc17823030051093756dcd6ea2d2f0460600c0126dcd6ea2d2f046060093080001b9add45a8b4bc178230300498006e6b751697823030049814000dcd6ea2d3045e08c0c0126001b9add45a5e08c0c01261ddb9add45a784ec97823030049b735ba8b4c1178230300498306e6b75169b12f0460600930aedcd6ea6345a674bc11818024db9add526a4d1697823030049b735ba8b4bc11818024c498266e6c1d6ea2d2f04607f8c0126dcd6eaa05268b4bc11818024c0040e7c0b751697823030049b735ba8b4ce97823030060093000dcd6ea2d2f046060093080dcd6ea2d2f0460600930800c1b9add5069d11697823030049800000fd16ea2d2f046060093738dcd6ea2d2f0460760c0126f81b9add45a5e08c0c0126099b9add45a5e08c0ec1d230049b736e6b75169782f0460600936e6b751697823030049893014fadb9add45a5e09b11818024db9add4e88b4bc11818024c13000000dcd6ea502f0460600936ecdcd6ea2d2f046060093008001b9add45a5e08c0c0126229b9add45a6c4bc15923030049b735ba8b4bc11818024c49813000dcd6ea4945a79c8c0c0126dcd6ea6a4c68b4bc11818024df03735ba8b4bc11818024c050006e6c856ea7445a5e08c0936e6b7549a2d2f04606009301af11b9add45a5e08c0c0126009e23735ba8b4bc11818024c37b736acb7549a2d2f046060093000dcd6ea2d32a5e0ab118180dcd6ea7445a5e08c0c0126029f03735ba8b4bc11818024c09b9c6e6b751697823030049807000dcd6ea2d2f04606009308edcd83add5268b4bc11818024db9add45a5e08c0e918024c03b735bab7549a2d2f0460600936e6b751697823246060093004dcd6ea2d2f04606009912604db9add4e88b4bc11818024c0980076adcd6ea2d2f0460600936e6b751697823030049857002001b9add45a5e08c0c0126069b9add45a5e08c0c012603406b735ba8b4d8978230300498266e6b751697829c460760c0126dcdab2dd45a5e08c0c0126036073735baa4d1697823030049b736acd596ea2d2f046060093000dcd90add45a6c4bc118126e71b9b215ba8b4bc11818024e1a3735ba8b4bc1181d830049800000e296ea2d2f0460600936e6c856ea2d2f0460748c0126dcd83add45a5e08c0c0126034003735ba8b4bc11818024c15b736acc1d6ea2d2f046060093000dcd6ea2d2f046060093098dcd6ea2d3625e08c0c0126029ce3735ba8b4bc136230300498006e6b75169782303005c0936e6b756ea2d2f04606009301adcd6ea2d2f04d88c0e918024db9b565bab751697823030049b735baa9116978230300498576e6c1d83add45a5e08c0c012700db9add4b08b4bc11818024db9add45a6c4bc11818024c09b7360eb756ea2d2f0460600936e6b751697829c4606009300edcd6ea2d2f05e0bc11818024db9add45a79cec97823030049c0e6e6b75169782303004980d6e6b756eadd45a5e08c0c0127039b9b565ba8b4bc11818024e1a3735ba8b4bc11818024c03b9c6e6b75169782303004984a6e6b7531a2d2f046060093126dcd6ea2d2f046060093080009b9add45a5e08c0c01261bc204516e6b75169d92f046060093756dcd6ea2d3b25e08c0c0126000003735ba8b4bc12e18024e0737360eb751697823030049b7360eb7556a2d2f0460600936e6b751697823030060093126dcd6ea2d2f04908c0c012607db9add45a6fcbc1181d230049c0e6e6b756ea2d2f0460600937c0dcd6ea6345a5e08c0c0126f11b9add45a5e08c0c012603db9b565baad916978230300498006e6b75281782303004986f6e6c856ea2d2f05388c0c0126f81b9add45a5e08c0c018024db9add4e898d1697823030049b735ba8b4bc11818024c13001000dcd6ea5845a5e08c0c0126dcd6ea5845a5e08c0c01260c0003fb6e6b751697823030049c346e6c856ea2d2f0460600936e6b751697829c4d88c0c0126dcd6ea2d3b2674bc11818024e0740e6e6b751697823030049b735ba9d116978230300600936e6b753a22d2f0460600930d50d1b9add45a5e09b11818024c003735ba8b4bc1181802b449b735ba8b4bc11818024c050010010396eaa445a5e08c0c0126dcd6ea2d2f0460748c01261ec003735ba8b4bc11818024c21b735ba8b4bc11818024c2b8046e6b755222d2f04606009304cdcd6ea2d33a5e08c0c0126025b9add45a5e08c0c012604c008006e6b753a22d2f046051093000001b9add45a5e08c0d2126001b9ae05ba8b4bc11818024c003735baa991697823030049b735ba8b4f39782303004981b7c0dcd6ea2d2f04606009306edcd6eaa445a5e08c0c0126029b9b195ba8b4bc11818024c02bab6e6b75169782303004981b6e6b7531a2d3625e08c0c0126001b9add4d85e08c0c014424db9add45a6c4bc118180300498006e6b753622d2f0460600936e6b755222d2f046060093026001b9b0d5ba8b4bc11818024de23735ba8b4bc11818024c110006e6b75169782aa460600936e6b751699d2f046060093036001b9add45a6c4bc11814424dce3735ba8b4bc11818028849b735ba8b4bc1181d230051093000dcd6ea2d2f0460770c0126e71b9add45a8b4bc11818024de23735ba8b4bc1181d830049b735ba8b5169782303a460093806dcd6ea2d2f04608c0c0126001b9add45a5e08c0c01261c5b9add45a5e08c0c0126098020007c0b75169e72f046060093806dcd8cadd45a5e08c0c0126dcd6ea2d43679cbc11818024c003735ba8b4d899d23030049c036e6b75169782303004981e806dcd6ea2d2f05588c0c0126dcd6ea5845a5e08c0c0126008003e0756b751697823030049b735ba961169782303004986f6e6b75169782303004980a008dcd6ea6345a5e08c0c0126004003735ba8b4f817823030049b9c6e6dcd6ea2d2f0460600936e6dcd6ea2d2f0460748c0126001b9add45a5f8bc11818024de23735ba8b4bc11818024c03b735ba8b4bc118180300498016e6b75169d92f046060093126dcd6ea2d2f05588c0c0126000000006e6b7561a2d2f0460604036e6b75169782303004981f6e6b751697823030049813008001b9add45a5e08c11818024db9add45a5e08c11818024c183735ba8b4bc14e23030051093806dcd6eaa745a5e08c0c0126dcd6fadd45a5e08c0c012603400373632c1d1697823030049be06e6b75169d92f0460600936e6b755226345a5e08c0c0126001b9b195ba8b4bc11818024db9add45a5e08c0c012607c003735ba8b51697829c46060093868dcd6ea2d2f0460600a2126dcd8cadd45a5e08c0c01260c0003735ba8b4bc11818024c0f3735ba9d1169d92f046060093884dcdab2dd45a5e08c0c0126001b9add45a5e0ab11818024db9add5488b4bc11818030049c346e6b7516a2d2f046060093788dcd90add45a5e08c0c0126dcd6ea2d2f05588c0c01260c1e23735ba8b4bc13623030049c4d868dcd6ea2d2f046060093000dcd6ea2d2f04606009303edcd6ea9345a79cbc11818024c000006e6b751698e23030049b735ba8b4bc11818024c1801f6e6b75169782303b060093080000003735ac8b4bc11818024c004446e6b751697823030049b736e6b751697829c46060093000dcd6eaa745a5e08c0c0126eadb9add5268b4bc11818024df7be06e6b7516978230300498006e6ce16ea2d2f046060093868dcdb9add45a5e08c0c0126001b9add45a5e0b091818024db9add5389d116978230300498006e6b75169d92f0538600936e6b751697823030049893036dcd6ea2d33a5e0b491818024db9add45a764d897823030049b735ba8b4f39782303004980d000dcda5a2d2f05588c0c0126dcd6ea2d2f04606009308001db9b565ba8b4f397823030049b9c6e6b75169782f0460600937c0dcd6ea2d2f046060093036dcd6ea9345a674bc11818024db9add45a5e0bc1181d230049b735ba98d1697823030049804000dcd6ea2d2f046060098126eadb9add45a5e08c0c0126034003766e6b751697823030049b735ba9d1169782303004981b756dcdab2dd45a5e08c0c0126dcd83add45a79cbc11818024db9add45a5e08c0c018024c023735bab75169e72f046060093756dcd83add45a5e08c0c0126000003a25ba8b4bc11818024dd5b735bab751697823030049b73642b7516978230300498406e6b751699d2f04606009301adcd6ea2d2f04608c0c0126009b9add45a5e08c11818024c37c0e6e6b75169e72f0460600936e6d596ea2d33a5e08c0c0126000003735ba8f0bc11818024db9add45a5e09b11818024c200006e6b751e17823030049830000dcd7a22d2f0460600930aedcd8cadd45a5e08c0c0126008002dd5488b4f397823030049c5181cdcd6ea2d2f04606009381ceadb9add45a5e08c0c0126dcd8cadd45a5e08c0c01261bdb9b075ba8b4ce97823030049b735ba8b4bc15623030049802000dcd6ea3345a5e08c0c0126dcd6eadd45a674bc11818024db9add45a6c4bc11818024c0db735ba8b4bc1562303004986f6e6b75169782f05388c0c0126dcd6ea2d3b25e08c0c0126005b9add4628b4bc11818024c06c346e6b75169782f0460600936e6b75169782303004981f004dcd6ea2d2f0460600930de07e073735ba8b4ce97823030049b735ba96116978230300498226e6b755222d3b25e08c0c0126f11b9add45a5e08c0c014424e1d4036e6b751697823030049bc46e6b7516a2d2f0460600936e6b752c22d2f0460760c012700db9add45a5e08c0c012615db9add45a5e08c0d218024c2bb735ba8b4bc1362303004982b6e6b996ea2d2f04606009304cdcd6ea9345a5e08c0c012624db9add45a5e08c0c014024c133735ba8b4bc11818024c2b800788dcdb9add45a5e08c0c0126000003825ba8b4bc11818024db9add45a5e08c0c012606c00800874dcd6ea2d2f0460600936e6b752c22d2f04606009300ef81b9add5268b4bc11818024c003735ba8b4bc11818027049b735baa4d3a22d2f046060093000dcd95add45a5e08c0c0126001b9add45a5e08c0c012615db9add45a5e08c0c012615c1841e806dcd6ea2d2f0460600936e6b755222d2f046060093036dcd6ea2d2f046060093126035b9b565ba8b4bc11818024c49b735ba8b4ec978230300498046e6c856ea5845a5e08c0c0126dcd83add45a5e08c0c012624df03735ba8b4bc11818024c06b735ba8b4bc118180288498407c0dcdab2dd45a5e08c0c0126002074035ba8b4bc11818024db9add5ba8b4bc11818024c49b735ba9611697826c46060093000dcd6ea2d2f45e08c0c0126001b9add45a5e08c0f318024db9add4e88b4bc11818024c06b735ba8b51697823030049840000dcd6ea2d2f05648c0c0126dcdab2dd4e88b4bc11818024c003735ba8b4bc11818024c28c036e6b751697823030049826000dcd6ea9345a5e0a70c0126f81b9b075ba8b4bc11818024df03735bab751697823030049b735baa4d169b12f046060093001079b9add45a5e08c0c0126dcd83add4e88b4bc11818024e073735ba8b4bc11818024c498006e6b752822d2f046060093000dcd6ea7445a5e08c0e9126dcd6ea2d2f04606009304c001b9add5ba9d11697823030049800000dcd6ea2d2f04a48c093806dcd6ea2d2f046060093014f5db9b075ba8b4bc11818024e073e06e6b751697823030049b736e6b751697823030049840000dcd6ea8345a5e08c0c012700db9add45a5e08c0c012604c000006e6b751697828230049bc46e6b75169782f046060093000fd1b9add45a5e08c0c0126dcd6ea2d2f046060093014002073735ba9d116978230300498006e6b7531a2d33a5e08c0c07caf11b9add45a5e08c0c0126001b9add45a5e08c0c0126099b9add45a5e08c0c012606c023735ba8b4bc11818024c180266e6b75169b12f04606009301adcdab2dd45a6c4bc11818024db9add45a5e08c0c012604c003735ba8b4bc1182303b060093001101b9add45a5e08c0c0126002073735ba8b48c0c01261bc003735ba8b4bc11818024c0537360eb75169b12f046060093738e71b9add45a5e08c0c0126dcd6ea2d2f046060093060029b9b195ba8b4bc1181d830049b735ba8b4bc1202303004980d000dcd6ea2d3625e08c0e9126e71b9add45a5e08c0e918024db9add5ba8b4d897823030049c1a81cdcd6ea2d2f0460600936e6b75169782303a4748c0126dcd6ea2d2f05549b11818024db9add45a5e0ab1181d8300498006e6b751697823030049813000dcd6ea2d2f0460708c0126dcd6ea2d2f04606009306004db9add45a5e08c0c012615c013735baa4d169782bc460600936e6b75169782303004986f0aedcd6ea9345a5e08c0c0126005f4bc46e6b751697823030049b735ba8b4bc1182303004980781cdcd6ea2d3625e08c0c0126dcd6ea2d2f0460760c012607db9add45a79cf3978230300498006e6b75169782303dc600936e6c656ea2d2f04606009300e001b9add45a7b8bc11818024e1a3735ba8b4bc11818024c2c800714dcd6ea2d2f0460600936e6b75169782ac4606009300eeadb9add45a79cbc11818024db9add548a4d1697823030049b735ba8b4bd178230300498026e6b7516a0f3ce5e08c0c0126eadd5b735ba8b4bc11818024db9add45a5e08c0c012603400b73642b7516978230460600936e6b75169782303a4600b3126dcdab2dd45a5e08c0c012600601b735ba98d1697823030049b9c6e6b751697829c460600936e6b75169782f046060093080dcd6ea2d2f04606009303e01db9add45a5e0a71181d2300498006e6ce56ea2d2f0460600936e6b752c22d2f0460600a2126dcd6ea2d2f04d88c11818024e01b735ba8b4bc11818030049b73642c656ea2d2f046060093868e71b9add45a5e08c0c0126dcd6ea5045a5e08c0c01261bdb9b075ba8b4bc11818024c00c346e6b75169782303a460093000dd5b9add45a5e08c0c0126dcd6ea2d3ce674bc11818024db9add4b08b51697823030049b735bab7516978230300498016e6c856ea2d2f05588c0c012712db9add5268b4bc11818024db9b195ba8b4bc13623030049800000dcd77a2d2f0460600936e6b755222d2f04606009301aeadb9add45a674bc11818024e0fb9c6e6b751697823030049b735ba925169e72f0460600936e6d596eaa445a5e08c0c0126001b9add45a5e0a08c01261bdb9add45a5e0ab13623030049800000dcd6ea2d2e0460600936e6c856ea2d2f04606009303edcd6ea2d3b25e08c0c015e24db9add45a5e08c0c0126098013735ba8b4bc11818024c3782681cdcd6ea2d2f046060093002dcd83add5488b4bc11818024c003735ba98d16978230300498006e6c516eaa445a5e0600936e6b7531a2d2f046060093060dcd6ea2d2f04d88c0c012607db9add5baa911697823030049b736e6b752c22d2f046060093000dcd6ea2d39a5e08c0c0126001b9add45a5e08c0c018024db9add45a5e08c0c018024c183735ba8b4ce99d2f0460600936e6b75169782303004980a004001b9add45a5e08c0c01261a9b9add45a5e08c0c01261bc050006e6b7516978230300498806e6b751697829c5388c0c0126dcd6ea9345a5e08c0c0126011b9add4d88b4bc11818028849c0e6e6b755222d2f0460600936e6c356ea2d2f0460600a2126dcd6ea2d2f046060093026009b9add45a5e08c0c01261bc09c346e6b751697829c460600936f2dcd6ea2d2f04606009303e001b9add45a734bc15618024db9add45a5e08c0c012a24c02434868dcd6ea2d2f0460600936e6b751697b2f046060093008dcd6ea2d2f04688c0c0126011b9add45a794bc14e23030049b735ba9a91699d2f0460600936e6b7540a7445a5e08c0c0126dcd6ea2d3c26c4bc11818024c003735ba8b4bc11818024c1bb735ba8b4bc11818024c068046e6d596ea2d2f046060093008001b9add45a5e08e11818024c003735ba8b4bc11818024c2d0006e6b7516978230300498316e6c1d6ea2d2f046060093008000003735ba9251691818024db9add5ba8b4bc11818024c020006e6b7516978272460600936eadcd6ea2d2f046060093004000003be5ba8b4bc11818024db9add45a79cbc11818024c49b735baa05169b12f0460600936e6b752c22d2f05e08c0c0127039b9add45a5e08c0c0126010003735baab91697823030049b735ba8b4bc11823030051093756dcd6ea2d2f046060093126dcd6ea2d45a5e08c11818024df03735ba8b4f3978230300498006e6b75169f62f0460600936e6c656ea2d2f0460600a212700db9add45a764bc11818024db9add4c68b4bc11818024c013735ba98d169782303004986f6e6b75169782303b0600930aedcd6ea7445a79cbc11818024e28be06e6b751697823030049be0756dcd6ea2d2f0460600936e6c656ea2d45a5e08c0c0126f11ce3735ba8b4bc11818024db9add45a5e0ab11818028849bc46e6b75169782303a4600936e6b751697823030060093004dcd6ea2d2f0460600c01261bdb9add45a8b4bc15623030049bab6e6b753a22d2f0460600936e6b751699d2f046060093126dcd6ea2d2f0460600a212607c000006e6b75169aa230300498006e6cf96eaa445a460600936e6dcd6ea2d2f04608c0c0126dcd6ea2d45a5e08c0c012607df03735ba8b4ce97823030049b736e6c656ea2d2f0460600936e6b75169782303004985700e001b9add45a764bc11818024db9add45a764bc11818024c183735ba9d11699d2f0460600936e6dcd6ea2d2f05588c0c0126dcd6ea7445a5e08c0c014624db9add45a79cd8978230300498006e6b7516978252460760936e6dcd6ea2d2f04606009303e001b9add45a5e08c0c0126024003735ba8b4ce91818024c37bab6e6b75169b12f046060093788dcd6ea2d2f05388c0c012700db9add45a5e08c0c012606db9ae35ba8b4bc11818024c0fb73656c856ea2d2f0460600936e6bbd6ea2d2f046060093080dcd90add45a5e08c0c012615e1a3c46e6b7516978230300498006e6b754e22d2f0460600936e6cad6ea2d2f04d88c0c0126dcd6ea2d2f0460760c0126099b9add45a5e09b11818024c2b8007dedcd6ea2d2f0460600936e6b75169782303004981b000ee1b9add45a79cbc11818024c003a25ba8b4bc11818028849b735ba8b4d899d2f046060093738dcd6ea2d2f046060093080dcd6ea2d2f0460748c0126101b9add45a5e08c0ec18024c050006e6b75169782303004981b6e6b751697823030049830036dcd6ea2d2f0460760c012604db9add45a5e09b1181e6300498006e6b751e22d2f046060093000dcd6ea2d2f046060093046dcd6ea2d2f04606009304c01db9add4788b4bc11818024c183735ba8b4bc136230300498516e6b75169782f04608c0c0126001b9add5428b4bc11818024c000006e6ba516978230300498006e6ba516978230300498306e6b75169e72f046060093002dcdb33195ba8b4bc11818024db9b195ba8b4bc17823030049800744dcd6ea2d2f0460600936e6b75169782303004980a00e000003735ba8b4bc11819224dd5b735ba8b4bc11818024c008006e6b7516978230324498307cadcd8cadd45a5e08c0c0126dcd6ea2d2f05e0ab11818024db9add45a5e0a711818024c3bb735ba8b4bc11818024c498936e6b75169782303004981300edcd90add45a5e08c0c0126099dab9c6e6b751697823030049b735baa91169e72f04606009376adcd6ea2d2f0460748c0126dcd6ea2d2f05388c0c0126101b9b075ba8b4bc11818024c233735ba8b4ec978230300498026e6b75169782f04606009303edcd6ea2d3b25e08c0c01261bc000006e6b751698823030049be06e6b751697823030049893000dcd6ea2d31c5e08c0c0126dcd6ea2d2f04d88c0c0126098003735ba8b4bc11818029449c346e6b751697823030049840756dcd6eaa445a5e08c0c0126dcd6ea2d33a5e08c0c0126005b9b215ba8b4bc11818024c050006e6c856ea2d2f04d88c0936e6b753a22d2f046060093126f81f03735ba8b4bc11818024c003735ba9611695623030049b735ba8b4bc1362303004980a756dcd6ea2d3d45e08c0c0126dcd90add45a5e08c0c012604df03735ba9d116978230300498006e6b7516a1b2f046060093000dcd6ea2d2f04888c0c0126dcd6eacd5488b4bc11818024db9add45a5e09b11818024c09b735ba9d13a22d2f0460600936e6b755222d33a5e08c0c0126001b9add45a5e09c8c012615db9add45a5e08c0c318024c068006e6bd16ea2d2f046060093000dcd6ea2d2f04607f8c0126dcd6ea6345a5e08c0ec18024e01b735baa4d1697823030049b735ba8b4bc1181d8300600936e6b75169b12f046060093126dcd6ea2d2f05388c0c0126069b9add45a5e08c0c014424c2b800894dcd6ea2d2f0460600936e6b75169782303004981b004dcd6ea2d45a5e08c0c012615db9add45a5e08c0c01261bc0db735ba8b4f397823030049804788f11b9add45a5e08c0c0126f81b9add45a6c4bc11818024c003735ba8b4bc16923030049b9c6e6b752c22d2f046060093000e09b9add45a5e08c0c0126dcd9cb215ba8b4bc11818024db9add4c68b4bc11818024c03b735ba961169782303a460093756dcd6ea2d2f046060093008dcd6ea2d2f05388c0c017024db9add4e88b4d897823030049c036e6b75169782303004980d6e6b75169782303006009300f00db9b565ba8b4bc11818024c003735baa4d1697823030049b735baa4d1697823030049830000dcd6eaa045a5e08c0c0126dcdb9add45a5e08c0c012615c003735ba8b4bc11818025449c036e6c1d6ea2d2f0460600936e6b75169782303004980d00100db9add5ba8b4bc11818024c003735ba8b4bc11818024c030006e6b751697b2f0460600936e6b751699d2f046060093008001b9add45a5e08d11818024dce3735baa991697823030049b73642b7531a2d2f0460600930010d1b9a2d2f0460760c0126dcd90add45a5e08c0c018024db9add4c68b4bc136230300498006e6d5983a2d2f04606009381d00db9add45a5e08c0c0126001b9add45a5e08c0c0126035b9add45a5e08c0c01260c0068006e6d596ea2d2f0460600936e6b751697823030049893002dcd6ea2d2f04d88c0c018024db9add45a6c4d897823030049b736acb751697823030049830000ef96ea2d2f0460760c0126dcd6ea5845a5e0a711818024db9add45a5e08c0c014424c130006e6c1d6ea2d2f046060093000001b9b145ba8b4bc0c0126dcd83add45a5e08c0c01260c21a3735ba9611697823030049b735ba8b516978230300498266e6b75169782384606009300ef81b9add45a5e08c0c0126004003735bab751697823030049b735bab751697823030049830000dcd6ea2d3fc5e08c0c0126dcd6ea2d2f05548c0e918024db9add45a5e08c0c014424c050006e6b751697826c460510936e6b753a22d2f046060093002dcd6eaa445a5e08c0c012624de23735ba8b4bc11818024c203735ba8b5169782303004980a001039b9add45a5e08c0c0126dcd6ea2d2f0460600a212604c003735ba8b4bc11818024c2c3735ba8b4bc1181c230051093000dcd6eaad45a5e08c0c0127039b9add45a5e08c0c01260c1f03735baa911697823030049b736e6b7516978230300498266e6b7516a2d2f046060093026dcd6eaa44e88b4bc11818024c004346e6c8516978230300498006e6b755b22d2f0460600936e6b75169782f0460600930aedcdb9add45a5e08c0c0126029b9add45a764bc1181d8300498006e6d2d6ea2d2f0460600936e6b75169b12f04606009300312df03735ba8b4bc11818024c003735ba8b4bc11818024c193735baa4d16978230300498026e6b7549a2d2f0460600930dedcdb9add45a5e08c0c012604db9add45a5e0aa94e23030049b9c6e6b7516978230460600936e6b7516978230460748c0126dcd6ea2d2f05388c0ee18024dce373632b751697823030049b73632b75169782303a460093000001b9add45a5e08c0e1180dcdb3b565ba8b4bc11818024dce3735ba8b4bc15623030049b735ba8b4bc11818a300498266e6b755222d3625e08c0c0126dcd6ea2d2f046060093126011b9add45a764bc11818024c03b735ba8b4bc1562303a460093788dcd6ea2d2f0460600930560000037361a8b4bc11818024db9add45a5e08c0c0126034013735ba8b4bc11818024c3780d6e6d596ea2d2f046060093004dcdab2dd45a5e08c0c01261bdb9add45a5e08c0c0126100203e06e6b751697823030049804738dcd6ea2d2f04606009303edcd6ea2d2f0460748c012607db9add4c68b4bc11818028849b7360eb7516978230300498026e6b753a22d2f046060093008dcd83add45a5e08c0c01261bdb9add5ba8b4bc11818024c013735bab75169782303004986f6e6b751697823031460093026dcd6ea6345a8b4bc11818024db9add45a5e08c0c018028849b73642b75169d92f0460600936e6b75169782303b060093036dcd6ea2d2f05e08c0c0126099b9add45a5e0a711823030049b735ba8b516978230300600936e6b751697823030049801002dcd6ea2d3b25e09b11818024c003735ba8b4bc14e2303a4604346e6b751697823046060093000001b9b3e5ba8b48c0c0126dcd8cadd45a5e0a711818024e073735ba8b4bc11818024c0140e6e6b75169782303004986f756dcd6ea2d2f0460600aa126dcd6ea2d2f05e08c0c0126029b9add45a5e0ab14e23030049c346e6c656ea2d2f046060093000dcd6ea2d3c25e08c0c0126dcdb9add4c68b4bc11818024de23735ba9611697823030049c346e6b75169782ac460600936e6b75169782f046060093026dcd6ea2d2f04606009303601db9add5488b4bc11818024c00b735ba8b4d8978230300498046e6dcd6ea2d2f0460600c0126dcd6ea2d2f05388c0c012607db9add5388b4bc136230300498006e6b75169952f046060093868dcd6ea2d2f04606009303edcd9c2dd45a5e0a711818024e224346e6b751697823030049b735baa4d169782303bc600936e6b75522a445a5e08c0c0126dcd6ea2d40a79cbc11818024c000006e6b752017823030049b73642b75169782303004981b000dcd6ea8145a5e08c0c0126001b9adf5ba8b4bc11818024db9add45a5e09b11818024c0d800884dcd6ea2d2f04606009381cdcd6ea2d2f0460600930ea001b9add45a5e0970c012610201b735ba8b4f397823030049b735ba96116978230300498146e6b751697823030049804002001b9add45a5e0b811818024c000006e6b754297823030049c03756dcd6ea2d2f0460600936e6c656ea2d2f0460600a7126001b9add45a690bc15623024db9add4b08b4bc11818024c2000077cdcd6ea2d2f0460600936e6b75169e72f046060093000dcd6ea6345a5e0bc11818024c003735ba8b4bc1181b6300498006e6b75169aa230300510936e6b75169782f0460600c0126dcd6ea5845a5e08c0c0126229b9add5488b4bc11818024c023735baa4d169782303b0600936e6c656ea2d2f04606009302f00db9add45a674bc11818024c003735ba8b4f397823030049b735ba8b4ec978230300510936e6b75169e72f046060093060dcd6ea2d45a764bc11818024c004516e6b751697823030049800756dcd6ea2d2f0460600936e6d596ea2d2f046060093044eadb9add45a5e08c0c01260c1e23735ba8b4bc118230300498006e6b7516a0f2f0460600936e6b7549a2d2f04606009300ee71b9add45a5e08c0c012615db9add45a5e08c0ec18024c06b735ba8b4bc1181d230049857788dcd8cadd45a5e08c0c0126dcdab2dd45a5e08c0ec18024c003735bab351697823030049b736e6b75169d92f046060093000dcd6ea2d33a5e08c0c0126001b9add45a5e08c0c014624de23735ba8b4bc15623030049b735ba8b4ce97823030049830000dcd6ea3945a5e08c0c0126dcd83add45a5e08c0ec18024db9add5ba8b4bc1181d8300498006e6b7524a2d2f046060093000dcd7dadd45a5e08c0c0126f11b9add45a5e08c0c012607c003735ba8b4bc11821430049b73642b7549a2d2f0460600936e6b75169782303004980d00edcd6ea2d2f046060093008011b9b565ba8b4bc11818024c038006e6b7518a2d2f0460600936e6b751697823030051093037039b9add45a5e08c0ec18024db9add5268b4bc136230300498006e6b753522d2f04606009383ce71b9add45a5e08c0c0126dcd6ea2d45a5e08c0c012606e1d4346e6b751697823030049b7360eb7516978230300498076e6b756ea2d2f04606009300edcd6ea2d2f05388c0c012615dd13735ba8b4bc118180288498006e6b755922d2f0460600936e6b751697823036c600930dedcd6ea8345a5e08c0e918024db9add45a674bc11818024c1cb735ba8b4d897823030055093868dcd6ea2d2f0460600930ae0020739c5ba8b4bc11818024db9b215ba8b4bc11818024c06b736acc856ea2d2f046060093738dcd6ea2d2f04606009304d039b9add45a5e08c0c012601db9b735ba8b4bc11818024c0db735ba8b4bc118230300498406e6b751697826c4606009301adcd6ea2d2f0460748c0126099b9b565ba8b4bc13623030049b735ba9612c22d2f0460600936e6c8583add45a5e08c0c0126dcd6ea2d3ce5e08c0c0126008003735ba8bd1697823030049b735c6b75169782303004981b6e6b75169e72f0460600930de001b9add45a6a8bc11818024db9b3e5baa9116978230300498006e6b75169782303004f0936e6c856eadd45a5e08c0c0126dcd8cadd45a5e08c0c012610201b735ba8b4bc11818024c49800868dcd6ea932f0460600936e6c1d6ea2d2f04d88c0c0126e71b9add45a5e08c0c0126028000006e6b75169782302e049bab6e6b751697823030049802756dcd6ea2d2f0460600930dedcd6ea2d2f0460748c0126028003735ba8b4bc1362303a449b735ba8b4bc156230300498406e6d996ea2d3b25e08c0c0126dcd6eadd45a5e09b11818024db9add45a764bc178230300498007e8b75169782ac46060093806f81b9add45a5e08c0c0126001b9add4c6960bc11818024c003735ba8b4bc15b23030049b9c6e6b7516978230300498136f6dcd6ea2d2f046060093014001b9add45a5e08c0c218024e07373642b751697823030049b735ba8b4bc1181d2300498136e6b75169782303004984003f00db9add4e88b4bc11818024e073735ba8b4bc13623030049b735ba8b4ce978230300498026e6b751699d2f0460600930de001b9add45a5e08c0c012624db9add45a5e08c0c012624c183735ba8b4bc14e230300498266e6b751697823c46060093014dcd7dadd45a5e08c0c01261bdd5b735baaad1697823030049c1a806dcd6ea2d2f046060093868dcd6ea2d2f04606009304cdcd6ea2d3b25e08c0f118024c003e06e6b751697823030049be06e6b7516978230300498306e6b751697829c46060093014001b9add45a5e08c0c013224c003735ba9d116978230300498007c0dcd8cadd45a5e0600936e6b753a22d2f0460600930610d1b9add45a5e08c0c012602a01b735ba8b4d897823030049b73672b75169782303a4600936e6b751697829c46060093026dcd6ea2d2f05e08c0c012606c003d76e6b751697823030049b735baa4d1697823030051093868dcd6ea2d2f046060093026dcd6ea9345a8b4bc11818024c0041a6e6b751697823030049b9c6e6b7531a2d2f046060093000dcd6ea2d2f04b88c0c0126dcd6ea6345a5e08c0e918024e1d3c46e6b7516978230300498006e6b75169b12f046060093738dcd6ea2d2f0460600c0126dcd6ea2d3625e08c0c01260c1b9add45a5e08c0e918030049b735ba8b4bc1181802884980d81cdcd6eaa945a5e08c0c0126dcdab2dd45a5e08c0c014424db9b735baa4d1697823030049b735ba9611697823046060093000dcd6ea2d3105e08c0c0126f11b9add45a5e08c0c012615db9add45a8b4bc11818024c068006e6b7516978240460600936e6d596ea2d45a5e08c0c0126dcd6ea2d2f0460610c0126009b9b075ba8b4bc11818028849b73632b752c22d2f046060093000dcd6ea9345a764bc0c0126dcd6eadd45a5e08c0c014424e01b735ba8b4bc11818024c00b7360eb7516a2d2f0460600936e6b752c22d2f05588c0c0126001dc3735ba8b4bc11818024db9add5ba8b51697823030049b735ba8d9169782303004981b6e6b75169e12f04d88c0c0126dcd6ea2d2f046060093126009b9add45a5e08c0c012624c37b735ba8b4bc11818024c008006e6dcd6ea2d2f04606009301adcd6ea5845a5e08c0c012607c003735baa14bc1181d830049c0e6e6b7516978230300510936e6dcdab2dd45a5e08c0c0126dcd6ea6345a5e0a711818024c000006e6b75169c423030049bbe6e6b75169782303b0600937c0dcd6ea2d2f046060093005039b9add45a8b4bc11818024df03735ba8b4bc11818024c37c036e6b755222d2f046060093868dcd6ea6345a5e08c0c0126dcd6ea2d2f05388c0c018024db9add45a5e08c0e918024c2d3736e6c1d6ea2d2f046060093000dcd90b1945a5e08c0c0126dcd6ea7445a5e08c0c0126009b9add4e88b4bc11818024c37b736e6b756ea2d2f046060093868dcd6ea2d2f0460600c0126dcd6ea2d2f0460608c0126004003735ba8b4bc15e230300498006e6b7516978230300498016e6b7549a2d2f0460600930cedcd6ea2d2f046060093060005b9add5488b4bc11818024c003735ba8b4f39782303b060093000e096ea2d2f046060093080001b9add45a764ab11818024c003735ba8b4bc11818024c3f44b806dcd6ea2d2f04606009381cdcdb9add45a5e08c0c0126eadb9add45a5e08c0ec18024de23735ba8b4bc11818024c130006e6c1d5222d2f046060093000dcd6eaa445a5e08c0c0126dcdb3add45a6c4bc11818024db9add5488b4bc11818024c183735ba8b4bc11818024c2b8406e6b7549a2d2f05e08c0c0127101e23735ba8b4bc11818024de23735ba8b4bc11818024c050006e6b7516978230384600a2000dcd6ea2d3d45e08c0c0126dcd6ea2d3ce5e08c0c012601db9add45a6c4bc11818024c013735ba8b4d89782303004986f000eadce2dd45a5e08c0c0126dcd6ea2d33a5e08c0ec18024c0037361a8b4bc118180288498006e6b751ba2d2f046060093788dcd6ea2d2f046060093027039b9add45a894bc11818024dd5b735ba8b4bc11818024c03800896dcd6ea2d2f046060093806dcd6ea2d2f046060093008dcd6ea2d2f0460850ec18024db9add45a5e0bc11818024c06b736ccd596ea2d2f0460600936e6d596ea2d2f05e08c0c01260000036b5ba8b4bc11818024dce3735ba8b4ec97823030049b735ba8b4bc118230460600936e6c856ea2d3ce5e08c0c0126f11b9add45a5e08c0f718024db9add45a764bc1181d230049b735ba8b4bc11818024c02000000dcd6ea2d3485e08c0c0126dcd6ea2d33a5e08c0c012601db9b075ba8b4bc17823030049b735ba8b4f397826c460600936e6c656ea2d2f04608c0c0126eadb9b215ba8b4bc11818024db9add5ba8b4bc17823030049b735ba8b4bc15623046060093756dcd6ea2d2f04d88c0c0126dcd8cb195ba8b4bc11818024c003735ba8b4bc11818024c023735ba8b4bc11818024c18004000e296ea2d2f0460600930aedcd8cadd45a5e0ab11818024db9add45a5e08c0c01261001340e6e6b75169782f0460600936e6b75169782304606009303edcd6ea2d2f046060093004005b9add45a5e0ab15623030049b735ba8b4bc11818024c378016e6c856ea2d33a5e08c0c0126fbdce3735ba8b4bc11818024c00373642b751697823024c20373632b75169782303004981f6e6b751699d2f04d88c0c0126dcd6ea2d2f046060093080029b9add45a5e0ab11818024c0fb735ba8b4ec97829c46060093806dcd6ea2d2f0460600930bedcd9c3195ba8b4bc11818024db9add45a5e4bc11818024c00b735ba8b4bc11818024c20013788dcd6ea6345a5e08c0c01270d1b9add45a764bc11818024dce3735ba8b4bc11818024c0db735baa9116978230300498026e6b755222d2f0460600930dedcd6ea2d2f0460748c012606c0040e6e6b752c22d23030049b735ba8b4bc11818024c0f81f788dcd6ea2d2f0460600c0126001b9add4808b4bc11818024db9add45a5e08c0e918024c11b735ba8b4ce9782303004982e6e6b7517a2d2f04606009300edcd6ea2d3ca764bc11818024db9add45a6fcce97823030049b735ba96116978230300498576e6c856eab245a5e08c0c0126dcd6ea2d2f0460760c012624c003735ba8b4bc11818024c2fbef6e6b751697829c46060093000001b9add45a654bc118180f81b9add45a5e08c0ec18024db9add4e88b4bc1181d8300498006e6b7542a2d2f046060093000dcd6ea2d40a79cbc118180dcd6ea2d2f05388c0c012606c003735ba8b4bc1181a424c2bb735ba8b4bc11818024c49807000dcd77a2d2f046060093080001f039c5ba8b4bc11818024e1a3735ba8b4bc11818024c0db735baa851697829c46060093
  | 10 => 0x100db9add45a5e08c0c0126000003735ba8b4bc11818024c003735ba8b4bc11818024c180006e6b751697823030049802000dcd6ea2d2f0460600930de001b9add45a5e08c0ec18024c003735ba8b4bc11818024c038006e6c856ea2d2f046060093000dcd6ea2d2f04d88c0c0126001b9add45a5e08c0c014424c003735ba8b516978230300498006e6dcd6ea2d2f046060093000dcd6ea2d2f05e08c0c0126001ce3735ba8b4bc11818024c003735ba8b4bc1181d2300498006e6b751697829c460600930010d1b9add45a5e08c0c0126001e23735ba8b4bc11818024c003735ba8b4bc11818024c200006e6b752c22d2f046060093000dcd6ea2d2f04608c0c0126001b9b195ba8b4bc11818024c003735ba8b4bc156230300498006e6b75169782303004981f000dcd6ea2d2f0460600930ae001b9add45a5e08c0c0126098003735ba8b4bc11818024c050006e6b751697823030049813000dcd6ea6345a5e08c0c0126001b9add45a5e08c0c018024c003735ba8b4ec978230300498006e6b75169782303004981b000dcd6ea9345a5e08c0c0126001b9add45a5e08c0c0126034003736acb7516978230300498006e6c1d6ea2d2f046060093000dcd6eadd45a5e08c0c0126002073735ba8b4bc11818024c003735ba8b4f397823030049800756dcd6ea2d2f046060093000dcd6ea2d33a5e08c0c0126001b9add45a5e08c0c012624c003e06e6b7516978230300498006e6b753a22d2f046060093000dcd6ea2d3625e08c0c0126001b9add45a5e08c0c0126004003735baa9116978230300498006e6b751697823030049804
  | 11 => 0xdcd6ea2d2f046060093
  | _ => 0

def S (s j : Nat) : List Nat :=
  (List.range (fld (LT s) 4 j)).map (fun t => V.getD (fld (DT s) 11 (9 * j + t)) 0)

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 14 0 (N s)

def pool : List Nat := [20276122991265857, 60818386252271687, 60848111714630723, 50675391484984386, 60838225776805952, 50705136278896703, 40552187925955648, 10133118560306239, 40552197593826374, 50695240678444100, 30419127422224453, 60798624035050566, 30399307217699909, 50675430141787204, 10133147553430593, 30409212489172034, 30419098426999877, 40542292324454471, 40532416044008511, 60838177458420802, 60808490646570048, 10133147552382017]

def Z (s : Nat) : Nat → Bool := barScore 63 S N idx pool s

end Shard28


namespace Shard28
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmark_one : span (Z 8) 1 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmark_four : span (Z 8) 4 0 = true := by decide +kernel

end Shard28

end PEqualNP.Outside.L_meta_984.Cert
