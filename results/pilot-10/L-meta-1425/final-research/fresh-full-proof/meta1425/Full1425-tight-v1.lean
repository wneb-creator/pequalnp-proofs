import Mathlib
import PEqualNP.Defs

-- Generic Run normalization adapted from Digger-Rockwell PR801, Apache-2.0.
-- Source commit ea90309308dd46a22d4a469766e46dd63f4484d0.
-- Monotone preservation, directed coverage, and this finite certificate are new.


namespace PEqualNP.Outside.L_meta_1425.Cert

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

section RunFacts
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

end RunFacts

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


def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := a ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {m y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((a ^^^ m) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun m y s ys → f ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
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

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun m y s ys → f ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
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

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun m y s ys → f ys = true) :
    next m (s + 2 - ws.length) ws f = true := by
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

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun m y s ys → f ys = true) →
      next m (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

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

def pairCover (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all fun p => ws.any fun w => decide (w.testBit p.1 ≠ w.testBit p.2)

theorem pairCover_ok {m y s ws} (h : NatRun m y s ws)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, m.testBit p.1 = m.testBit p.2 ∧
      y.testBit p.1 ≠ y.testBit p.2) : pairCover pairs ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply List.any_eq_true.2
  have hex : ∃ w ∈ ws, w.testBit p.1 ≠ w.testBit p.2 := by
    by_contra! hn
    exact (hpairs p hp).2 (run_bits h p.1 p.2 (hpairs p hp).1 hn)
  obtain ⟨w,hw,hd⟩ := hex
  exact ⟨w,hw,decide_eq_true hd⟩

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def bar (m y : Nat) (cover : List Nat → Bool) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next m (s+2-ws.length) ws fun zs => cover zs && !(found S N idx s zs))

theorem bar_sound {m y cover S N idx} {s i : Nat}
    (hb : bar m y cover S N idx s i = true)
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (h : NatRun m y s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun m y q (S q j) := by
  cases s with
  | zero => simp [bar,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover zs && !(found S N idx s zs)
    have hF (zs) (hz : NatRun m y s zs) : F zs = true := by
      simp only [F,hc hz,Bool.true_and,found]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {m y cover S N idx} {cap : Nat}
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, bar m y cover S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun m y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := bar_sound (checked s hs i hi) hc hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_bar {m y cover S N idx cap xs}
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, bar m y cover S N idx s i = true)
    (initial : ∀ s ≤ cap, xs.length ≤ s+1 → found S N idx s xs = true) :
    ∀ s ≤ cap, ¬ NatRun m y s xs := by
  intro s hs hr
  have hi := initial s hs (run_len hr)
  simp only [found,Bool.and_eq_true,decide_eq_true_eq] at hi
  exact bar_all hc checked s hs _ hi.1 (Run.perm (List.isPerm_iff.1 hi.2) hr)

theorem encoded_exclusion {n : Nat} (f : BFn n)
    (hnc : ∃ x x' : Fin n → Bool, f x ≠ f x') (cap : Nat)
    (rows xs : List Nat) (m y : Nat) (cover : List Nat → Bool)
    (hc : ∀ {u ys}, NatRun m y u ys → cover ys = true)
    (hinputs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hmask : m = 2^rows.length-1) (hgoal : encL f rows = y)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → cover zs = false)
    (hno : ∀ s ≤ cap, ¬ NatRun m y s xs) : ¬ HasCircuitSize n f cap := by
  intro h
  obtain ⟨s,hs,ws,hsub,hrun⟩ := exists_run f hnc cap h
  have hr : NatRun m (encL f rows) s (ws.map (fun a => encL a rows)) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hz : (ws.map (fun a => encL a rows)).Sublist xs := by
    rw [← hinputs]
    exact hsub.map _
  by_cases he : ws.map (fun a => encL a rows) = xs
  · rw [he] at hr
    exact hno s hs hr
  · have hp := hproper _ (List.mem_sublists.2 hz) he
    rw [hc hr] at hp
    contradiction


theorem run_tight_bits {m y s ws} (h : NatRun m y s ws) (i j : Nat) :
    ws.length = s+1 →
    (∀ w ∈ ws, w.testBit i = true → w.testBit j = true) →
    y.testBit i = true → y.testBit j = true := by
  induction h using Run.fold with
  | done => intro hl hw; exact hw _ (by simp)
  | perm hp h ih =>
    intro hl hw
    exact ih (by rwa [hp.length_eq]) (fun w hm => hw w (hp.mem_iff.1 hm))
  | one save h ih =>
    intro hl hw
    have hlength := run_len h
    cases save <;> simp [kept] at hlength hl <;> omega
  | two conj ka kb h ih =>
    intro hl hw
    have hlength := run_len h
    have hk : ka = false ∧ kb = false := by
      cases ka <;> cases kb <;> simp [kept] at hlength hl ⊢ <;> omega
    rcases hk with ⟨rfl,rfl⟩
    apply ih
    · simp [kept] at hl ⊢
      omega
    · have ha := hw _ List.mem_cons_self
      have hbitB := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
      intro w hm
      simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at hm
      rcases hm with rfl | hm
      · cases conj <;> simp only [Bool.false_eq_true,ite_false,ite_true,
          Nat.testBit_and,Nat.testBit_or]
        · simp only [Bool.or_eq_true]
          intro ht
          rcases ht with ht | ht
          · exact Or.inl (ha ht)
          · exact Or.inr (hbitB ht)
        · simp only [Bool.and_eq_true]
          intro ht
          exact ⟨ha ht.1,hbitB ht.2⟩
      · exact hw _ (by simp [hm])

def tightPairCover (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then
    pairs.all fun p => ws.any fun w => !w.testBit p.1 && w.testBit p.2
  else pairCover pairs ws

theorem tightPairCover_ok {m y s ws} (h : NatRun m y s ws)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, m.testBit p.1 = m.testBit p.2 ∧
      y.testBit p.1 = false ∧ y.testBit p.2 = true) :
    tightPairCover pairs s ws = true := by
  unfold tightPairCover
  split_ifs with ht
  · apply List.all_eq_true.2
    intro p hp
    apply List.any_eq_true.2
    have hex : ∃ w ∈ ws, w.testBit p.1 = false ∧ w.testBit p.2 = true := by
      by_contra! hn
      have hb := run_tight_bits h p.2 p.1 ht
      have hy := hb (by
        intro w hw hwi
        have := hn w hw
        cases hv : w.testBit p.1
        · exact False.elim (this hv hwi)
        · rfl) (hpairs p hp).2.2
      rw [(hpairs p hp).2.1] at hy
      contradiction
    obtain ⟨w,hw,h0,h1⟩ := hex
    exact ⟨w,hw,by simp [h0,h1]⟩
  · apply pairCover_ok h pairs
    intro p hp
    exact ⟨(hpairs p hp).1,by simp [(hpairs p hp).2.1,(hpairs p hp).2.2]⟩


def collectBits (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => f w ||| collectBits f ws

theorem collectBits_testBit (f : Nat → Nat) (ws : List Nat) (j : Nat) :
    (collectBits f ws).testBit j = true ↔ ∃ w ∈ ws, (f w).testBit j = true := by
  induction ws with
  | nil => simp [collectBits]
  | cons w ws ih => simp [collectBits, Nat.testBit_or, Bool.or_eq_true, ih]

def diffCov (m i : Nat) (ws : List Nat) : Nat :=
  collectBits (fun w => if w.testBit i then w ^^^ m else w) ws

def dirCov (i : Nat) (ws : List Nat) : Nat :=
  collectBits (fun w => if w.testBit i then 0 else w) ws

theorem diffCov_testBit {m i j : Nat} (hm : m.testBit j = true) (ws : List Nat) :
    (diffCov m i ws).testBit j = true ↔
      ∃ w ∈ ws, w.testBit i ≠ w.testBit j := by
  rw [diffCov, collectBits_testBit]
  apply exists_congr
  intro w
  cases hi : w.testBit i <;> cases hj : w.testBit j <;>
    simp [hi, hj, Nat.testBit_xor, hm]

theorem dirCov_testBit (i j : Nat) (ws : List Nat) :
    (dirCov i ws).testBit j = true ↔
      ∃ w ∈ ws, w.testBit i = false ∧ w.testBit j = true := by
  rw [dirCov, collectBits_testBit]
  apply exists_congr
  intro w
  cases hi : w.testBit i <;> cases hj : w.testBit j <;> simp [hi, hj]

theorem maskCovered_of_bits {a mask : Nat}
    (h : ∀ j, mask.testBit j = true → a.testBit j = true) : a &&& mask = mask := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  cases hm : mask.testBit j with
  | false => simp [hm]
  | true => simp [hm, h j hm]

def diffCover (m : Nat) (groups : List (Nat × Nat)) (ws : List Nat) : Bool :=
  groups.all fun p => (diffCov m p.1 ws &&& p.2) == p.2

def dirCover (groups : List (Nat × Nat)) (ws : List Nat) : Bool :=
  groups.all fun p => (dirCov p.1 ws &&& p.2) == p.2

theorem diffCover_ok {m y s ws} (h : NatRun m y s ws)
    (groups : List (Nat × Nat))
    (hpairs : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      m.testBit p.1 = m.testBit j ∧ m.testBit j = true ∧
      y.testBit p.1 ≠ y.testBit j) : diffCover m groups ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply beq_iff_eq.2
  apply maskCovered_of_bits
  intro j hj
  obtain ⟨he, hm, hy⟩ := hpairs p hp j hj
  apply (diffCov_testBit hm ws).2
  by_contra! hn
  exact hy (run_bits h p.1 j he hn)

theorem dirCover_of_witness (groups : List (Nat × Nat)) (ws : List Nat)
    (hw : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      ∃ w ∈ ws, w.testBit p.1 = false ∧ w.testBit j = true) :
    dirCover groups ws = true := by
  apply List.all_eq_true.2
  intro p hp
  apply beq_iff_eq.2
  apply maskCovered_of_bits
  intro j hj
  exact (dirCov_testBit p.1 j ws).2 (hw p hp j hj)

def diffGroupsGood (width m y : Nat) (groups : List (Nat × Nat)) : Bool :=
  groups.all fun p => (p.2 < 2 ^ width) &&
    (List.range width).all fun j => !p.2.testBit j ||
      ((m.testBit p.1 == m.testBit j) && m.testBit j &&
        decide (y.testBit p.1 ≠ y.testBit j))

theorem mask_bit_lt {mask width j : Nat}
    (hm : mask < 2 ^ width) (hj : mask.testBit j = true) : j < width := by
  by_contra hn
  have hle : width ≤ j := by omega
  have hp : 2 ^ width ≤ 2 ^ j := by gcongr
  have he := Nat.testBit_eq_false_of_lt (hm.trans_le hp)
  rw [he] at hj
  contradiction

theorem diffGroupsGood_sound {width m y : Nat} {groups : List (Nat × Nat)}
    (hg : diffGroupsGood width m y groups = true) :
    ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      m.testBit p.1 = m.testBit j ∧ m.testBit j = true ∧
      y.testBit p.1 ≠ y.testBit j := by
  intro p hp j hj
  have hp' := List.all_eq_true.1 hg p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp'
  have hlt := mask_bit_lt hp'.1 hj
  have hc := List.all_eq_true.1 hp'.2 j (List.mem_range.2 hlt)
  simpa only [hj, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, and_assoc] using hc

theorem diffCover_ok_of_good {width m y s ws groups}
    (h : NatRun m y s ws) (hg : diffGroupsGood width m y groups = true) :
    diffCover m groups ws = true :=
  diffCover_ok h groups (diffGroupsGood_sound hg)


def dirGroupsGood (width y : Nat) (groups : List (Nat × Nat)) : Bool :=
  groups.all fun p => (p.2 < 2 ^ width) && (!y.testBit p.1) &&
    (List.range width).all fun j => !p.2.testBit j || y.testBit j

theorem dirGroupsGood_sound {width y : Nat} {groups : List (Nat × Nat)}
    (hg : dirGroupsGood width y groups = true) :
    ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      y.testBit p.1 = false ∧ y.testBit j = true := by
  intro p hp j hj
  have hp' := List.all_eq_true.1 hg p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp'
  have hlt := mask_bit_lt hp'.1.1 hj
  have hc := List.all_eq_true.1 hp'.2 j (List.mem_range.2 hlt)
  exact ⟨hp'.1.2, by simpa only [hj, Bool.not_true, Bool.false_or] using hc⟩

theorem dirCover_tight_ok {m y s ws} (h : NatRun m y s ws)
    (hlen : ws.length = s + 1) (groups : List (Nat × Nat))
    (hpairs : ∀ p ∈ groups, ∀ j, p.2.testBit j = true →
      y.testBit p.1 = false ∧ y.testBit j = true) : dirCover groups ws = true := by
  apply dirCover_of_witness
  intro p hp j hj
  obtain ⟨hneg, hpos⟩ := hpairs p hp j hj
  by_contra hn
  have hle : ∀ w ∈ ws, w.testBit j = true → w.testBit p.1 = true := by
    intro w hw hj'
    cases hi : w.testBit p.1 with
    | false => exact False.elim (hn ⟨w, hw, hi, hj'⟩)
    | true => rfl
  have hf := run_tight_bits h j p.1 hlen hle hpos
  rw [hneg] at hf
  contradiction

theorem dirCover_tight_ok_of_good {width m y s ws groups}
    (h : NatRun m y s ws) (hlen : ws.length = s + 1)
    (hg : dirGroupsGood width y groups = true) : dirCover groups ws = true :=
  dirCover_tight_ok h hlen groups (dirGroupsGood_sound hg)


def barBudget (m y : Nat) (cover : Nat → List Nat → Bool) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (idx : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next m (s+2-ws.length) ws fun zs => cover s zs && !(found S N idx s zs))

theorem barBudget_sound {m y cover S N idx} {s i : Nat}
    (hb : barBudget m y cover S N idx s i = true)
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (h : NatRun m y s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun m y q (S q j) := by
  cases s with
  | zero => simp [barBudget,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover s zs && !(found S N idx s zs)
    have hF (zs) (hz : NatRun m y s zs) : F zs = true := by
      simp only [F,hc hz,Bool.true_and,found]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barBudget_all {m y cover S N idx} {cap : Nat}
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, barBudget m y cover S N idx s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun m y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barBudget_sound (checked s hs i hi) hc hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barBudget {m y cover S N idx cap xs}
    (hc : ∀ {u ys}, NatRun m y u ys → cover u ys = true)
    (checked : ∀ s ≤ cap, ∀ i < N s, barBudget m y cover S N idx s i = true)
    (initial : ∀ s ≤ cap, xs.length ≤ s+1 → found S N idx s xs = true) :
    ∀ s ≤ cap, ¬ NatRun m y s xs := by
  intro s hs hr
  have hi := initial s hs (run_len hr)
  simp only [found,Bool.and_eq_true,decide_eq_true_eq] at hi
  exact barBudget_all hc checked s hs _ hi.1 (Run.perm (List.isPerm_iff.1 hi.2) hr)



def certTotal (N : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => N n + certTotal N n

def certAt (Z : Nat → Nat → Bool) (N : Nat → Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n+1, p => if p < N n then Z n p else certAt Z N n (p-N n)

theorem certAt_sound {Z : Nat → Nat → Bool} {N : Nat → Nat} (n : Nat)
    (h : ∀ p < certTotal N n, certAt Z N n p = true) :
    ∀ s < n, ∀ i < N s, Z s i = true := by
  induction n with
  | zero => intro s hs; omega
  | succ n ih =>
    intro s hs i hi
    by_cases he : s = n
    · subst s
      have hp := h i (by simp only [certTotal]; omega)
      simpa only [certAt,if_pos hi] using hp
    · apply ih ?_ s (by omega) i hi
      intro p hp
      have hh := h (N n+p) (by simp only [certTotal]; omega)
      simpa only [certAt,if_neg (show ¬ N n+p < N n by omega),Nat.add_sub_cancel_left] using hh

theorem certFlat_sound {Z : Nat → Nat → Bool} {N : Nat → Nat} {cap : Nat}
    (h : span (certAt Z N (cap+1)) (certTotal N (cap+1)) 0 = true) :
    ∀ s ≤ cap, ∀ i < N s, Z s i = true := by
  intro s hs i hi
  apply certAt_sound (cap+1) ?_ s (by omega) i hi
  intro p hp
  exact span_ok h p (Nat.zero_le p) (by simpa using hp)




open PEqualNP.CircuitLowerBounds

-- Explicit upper bounds only; no minimality or NOT-elimination claim.
def upperMono (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def upperComputes (C : Circuit) (T : Nat) : Prop :=
  ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) =
    Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)

def upperCircuit0 : Circuit := ⟨[⟨.and, [1,4]⟩, ⟨.and, [2,5]⟩, ⟨.and, [3,6]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,8]⟩, ⟨.or, [7,9]⟩], 10⟩
theorem upperCircuit0_mono : upperMono upperCircuit0 := by
  simp [upperMono, upperCircuit0]
theorem upperCircuit0_computes : upperComputes upperCircuit0 0xe8a8a8a8 := by
  unfold upperComputes
  decide +kernel

def upperCircuit1 : Circuit := ⟨[⟨.or, [3,4]⟩, ⟨.and, [0,5]⟩, ⟨.and, [2,3]⟩, ⟨.and, [2,6]⟩, ⟨.or, [0,7]⟩, ⟨.and, [1,9]⟩, ⟨.or, [8,10]⟩], 11⟩
theorem upperCircuit1_mono : upperMono upperCircuit1 := by
  simp [upperMono, upperCircuit1]
theorem upperCircuit1_computes : upperComputes upperCircuit1 0xe8a8e888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit2 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.or, [3,4]⟩, ⟨.and, [1,6]⟩, ⟨.or, [1,6]⟩, ⟨.and, [0,8]⟩, ⟨.and, [2,9]⟩, ⟨.and, [5,7]⟩, ⟨.or, [10,11]⟩], 12⟩
theorem upperCircuit2_mono : upperMono upperCircuit2 := by
  simp [upperMono, upperCircuit2]
theorem upperCircuit2_computes : upperComputes upperCircuit2 0xe8e8e880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit3 : Circuit := ⟨[⟨.and, [2,4]⟩, ⟨.and, [1,5]⟩, ⟨.or, [2,4]⟩, ⟨.and, [3,7]⟩, ⟨.and, [6,8]⟩, ⟨.or, [0,9]⟩, ⟨.or, [1,8]⟩, ⟨.or, [5,11]⟩, ⟨.and, [10,12]⟩], 13⟩
theorem upperCircuit3_mono : upperMono upperCircuit3 := by
  simp [upperMono, upperCircuit3]
theorem upperCircuit3_computes : upperComputes upperCircuit3 0xeaa8a888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit4 : Circuit := ⟨[⟨.and, [1,3]⟩, ⟨.and, [2,5]⟩, ⟨.or, [0,6]⟩, ⟨.or, [2,3]⟩, ⟨.and, [4,8]⟩, ⟨.or, [1,9]⟩, ⟨.and, [7,10]⟩], 11⟩
theorem upperCircuit4_mono : upperMono upperCircuit4 := by
  simp [upperMono, upperCircuit4]
theorem upperCircuit4_computes : upperComputes upperCircuit4 0xeaa8c888 := by
  unfold upperComputes
  decide +kernel

def upperCircuit5 : Circuit := ⟨[⟨.and, [0,4]⟩, ⟨.or, [1,2]⟩, ⟨.and, [0,6]⟩, ⟨.and, [1,2]⟩, ⟨.or, [5,8]⟩, ⟨.and, [3,9]⟩, ⟨.or, [3,9]⟩, ⟨.and, [7,11]⟩, ⟨.or, [10,12]⟩], 13⟩
theorem upperCircuit5_mono : upperMono upperCircuit5 := by
  simp [upperMono, upperCircuit5]
theorem upperCircuit5_computes : upperComputes upperCircuit5 0xeaa8e880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit6 : Circuit := ⟨[⟨.and, [0,1]⟩, ⟨.and, [1,3]⟩, ⟨.or, [5,6]⟩, ⟨.and, [2,7]⟩, ⟨.or, [4,6]⟩, ⟨.and, [0,9]⟩, ⟨.or, [8,10]⟩], 11⟩
theorem upperCircuit6_mono : upperMono upperCircuit6 := by
  simp [upperMono, upperCircuit6]
theorem upperCircuit6_computes : upperComputes upperCircuit6 0xeaaac880 := by
  unfold upperComputes
  decide +kernel

def upperCircuit7 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.or, [2,4]⟩, ⟨.and, [5,6]⟩, ⟨.or, [2,5]⟩, ⟨.and, [1,8]⟩, ⟨.or, [7,9]⟩], 10⟩
theorem upperCircuit7_mono : upperMono upperCircuit7 := by
  simp [upperMono, upperCircuit7]
theorem upperCircuit7_computes : upperComputes upperCircuit7 0xeac0e8c0 := by
  unfold upperComputes
  decide +kernel

def upperCircuit8 : Circuit := ⟨[⟨.and, [0,3]⟩, ⟨.and, [0,4]⟩, ⟨.or, [1,5]⟩, ⟨.or, [2,6]⟩, ⟨.and, [7,8]⟩], 9⟩
theorem upperCircuit8_mono : upperMono upperCircuit8 := by
  simp [upperMono, upperCircuit8]
theorem upperCircuit8_computes : upperComputes upperCircuit8 0xeac8e0c0 := by
  unfold upperComputes
  decide +kernel

def upperCircuit9 : Circuit := ⟨[⟨.or, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.or, [1,3]⟩, ⟨.or, [3,4]⟩, ⟨.and, [6,8]⟩, ⟨.or, [2,4]⟩, ⟨.and, [7,10]⟩, ⟨.and, [0,11]⟩, ⟨.or, [9,12]⟩], 13⟩
theorem upperCircuit9_mono : upperMono upperCircuit9 := by
  simp [upperMono, upperCircuit9]
theorem upperCircuit9_computes : upperComputes upperCircuit9 0xeac8e880 := by
  unfold upperComputes
  decide +kernel

def upperBudget (T : Nat) : Nat :=
  if T = 0xe8a8a8a8 then 6 else
  if T = 0xe8a8e888 then 7 else
  if T = 0xe8e8e880 then 8 else
  if T = 0xeaa8a888 then 9 else
  if T = 0xeaa8c888 then 7 else
  if T = 0xeaa8e880 then 9 else
  if T = 0xeaaac880 then 7 else
  if T = 0xeac0e8c0 then 6 else
  if T = 0xeac8e0c0 then 5 else
  if T = 0xeac8e880 then 9 else
  0

theorem monotone_upper (T : Nat)
    (hT : T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset Nat)) :
    ∃ C : Circuit, upperMono C ∧ C.gates.length = upperBudget T ∧ upperComputes C T := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨upperCircuit0, upperCircuit0_mono, by decide +kernel, upperCircuit0_computes⟩
  · exact ⟨upperCircuit1, upperCircuit1_mono, by decide +kernel, upperCircuit1_computes⟩
  · exact ⟨upperCircuit2, upperCircuit2_mono, by decide +kernel, upperCircuit2_computes⟩
  · exact ⟨upperCircuit3, upperCircuit3_mono, by decide +kernel, upperCircuit3_computes⟩
  · exact ⟨upperCircuit4, upperCircuit4_mono, by decide +kernel, upperCircuit4_computes⟩
  · exact ⟨upperCircuit5, upperCircuit5_mono, by decide +kernel, upperCircuit5_computes⟩
  · exact ⟨upperCircuit6, upperCircuit6_mono, by decide +kernel, upperCircuit6_computes⟩
  · exact ⟨upperCircuit7, upperCircuit7_mono, by decide +kernel, upperCircuit7_computes⟩
  · exact ⟨upperCircuit8, upperCircuit8_mono, by decide +kernel, upperCircuit8_computes⟩
  · exact ⟨upperCircuit9, upperCircuit9_mono, by decide +kernel, upperCircuit9_computes⟩

theorem monotone_equivalent_of_upperBudget_le (T : Nat)
    (hT : T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset Nat))
    (gates : List Gate) (hsize : upperBudget T ≤ gates.length) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0) := by
  rcases monotone_upper T hT with ⟨C, hmono, hlen, heval⟩
  exact ⟨C.gates, C.output, hmono, hlen.le.trans hsize, heval⟩


def fld (x b j : Nat) : Nat := (x >>> (b*j)) &&& (2^b-1)
def hk (ws : List Nat) : Nat := (ws.map (fun w => (w+317)^3+1)).sum % 4294967291
def qDirectInputs (bits : Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | record, x :: xs => List.replicate (record &&& (2^bits-1)) x ++
      qDirectInputs bits (record >>> bits) xs

def qDirectOther (values valueBits indexBits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, record =>
    let index := record &&& (2^indexBits-1)
    let rest := qDirectOther values valueBits indexBits n (record >>> indexBits)
    if index = 0 then rest else fld values valueBits (index-1) :: rest

def qDirectState (initial : List Nat) (countBits valueBits indexBits slots values record : Nat) : List Nat :=
  qDirectInputs countBits record initial ++
    qDirectOther values valueBits indexBits slots (record >>> (countBits * initial.length))
def qDirectStatePattern (initial : List Nat)
    (countBits patternBits patterns valueBits indexBits slots values record : Nat) : List Nat :=
  let headerBits := if patternBits = 0 then countBits * initial.length else patternBits
  let inputBits := if patternBits = 0 then countBits else 2
  let inputRecord := if patternBits = 0 then record else
    fld patterns (2 * initial.length) (record &&& (2^patternBits-1))
  qDirectInputs inputBits inputRecord initial ++
    qDirectOther values valueBits indexBits slots (record >>> headerBits)

def qGroupOffset (counts : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => qGroupOffset counts n + fld counts 12 n

def qGroupLocate (counts : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, g, j => (g,j)
  | n+1, g, j =>
    let size := fld counts 12 g
    if j < size then (g,j) else qGroupLocate counts n (g+1) (j-size)

def qGroupNoninputs (initial ws : List Nat) : Nat :=
  ws.countP (fun w => !(initial.contains w))

def qGroupedState (initial : List Nat) (groups valueBits indexBits patterns values counts specs : Nat)
    (records : List (List Nat)) (j : Nat) : List Nat :=
  let slot := qGroupLocate counts groups 0 j
  let g := slot.1
  let localIndex := slot.2
  let spec := fld specs 12 g
  let countBits := spec &&& 3
  let patternBits := (spec >>> 2) &&& 31
  let headerBits := if patternBits = 0 then countBits * initial.length else patternBits
  let width := headerBits + indexBits * g
  let record := fld ((records.getD g []).getD (localIndex/256) 0) width (localIndex%256)
  qDirectStatePattern initial countBits patternBits patterns valueBits indexBits g values record

def qGroupedIndex (initial : List Nat) (counts specs : Nat) (seeds : List Nat) (ws : List Nat) : Nat :=
  let g := qGroupNoninputs initial ws
  let n := fld counts 12 g
  let spec := fld specs 12 g
  let seedBits := (spec >>> 7) &&& 31
  let flag := 2^(seedBits-1)
  let h := hk ws
  let code := fld (seeds.getD g 0) seedBits (h % (max 1 ((n+3)/4)))
  qGroupOffset counts g +
    (if code ≥ flag then code-flag else ((h+code+317)^3 % 11400714819323198549) % n)

def tableFn (T : Nat) : BFn 5 := fun x => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)
def allRows : List Nat := List.range 32
def C0_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C0_values : Nat := 0xffffaaaaffaaffaaffaaaaaaffaa0000ff00aa00ff000000f0f0a0a0f0f00000f0a0f0a0f0a0a0a0f000f000f0000000cccc8888cccc0000cc88cc88cc888888cc00cc00cc000000

def C0_patterns : Nat := 0x0

def C0_N : Nat → Nat
  | 2 => 2
  | 3 => 10
  | 4 => 10
  | 5 => 1
  | _ => 0

def C0_counts : Nat → Nat
  | 2 => 0x2000
  | 3 => 0xa000
  | 4 => 0x9001
  | 5 => 1
  | _ => 0

def C0_specs : Nat → Nat
  | 2 => 0x181000
  | 3 => 0x481000
  | 4 => 0x401101
  | 5 => 257
  | _ => 0

def C0_seeds : Nat → List Nat
  | 2 => [0x0, 0x3]
  | 3 => [0x0, 0x196c10]
  | 4 => [0x2, 0xb4312]
  | 5 => [0x2, 0x0]
  | _ => []

def C0_records : Nat → List (List Nat)
  | 2 => [[], [0x48c65]]
  | 3 => [[], [0x81c9554dc769c273358b79ce7]]
  | 4 => [[0x1f], [0x23715d6f69e4f45db76bcaf]]
  | 5 => [[0x1f], []]
  | _ => []

def C0_S (s j : Nat) : List Nat :=
  qGroupedState C0_initial 2 32 5 C0_patterns C0_values (C0_counts s) (C0_specs s) (C0_records s) j

def C0_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C0_initial (C0_counts s) (C0_specs s) (C0_seeds s) ws

def C0_groups : List (Nat × Nat) := [(14,0x40000008), (28,0x40002000), (25,0x20), (26,0x48000000), (1,0x28), (22,0x40000000)]
def C0_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C0_groups ws else diffCover 0xffffffff C0_groups ws
def C0_Z := barBudget 0xffffffff 0xe8a8a8a8 C0_cover C0_S C0_N C0_idx
def C0_flat := certAt C0_Z C0_N 6
def C1_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C1_values : Nat := 0xffffffccffffff00fffff0f0fffff000ffffccccffffcc00ffffc0c0ffffaaaaffffaa00ffff8888ffff5555ffff0f0ffff0fff0fff0ff00fff00000ffccffccffaaffaaffaaff88ffaaff00ffaa0000ffa0ff00ff88ff88ff33ff00ff0fff0fff00f000ff000000fcfcfcfcfcfcccccfcfc0000fc00fc00fafafafafafa0000faaaf000fa00fa00f8f8f8f8f0f0f0c0f0f0f000f0f0c0c0f0f00000f0a0f0a0f0a0f080f0a0f000f030f000f000f000eeeeeeeeeeeecccceeee0000ee00ee00ececcccce0e0e0e0cccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaaaa88aaaaaa00aaaa8888aaaa0000aa00aa00a8a8a8a8a0a0a0a0a0a00000888888885555555533333333333300000f0f0f0f00ff00ff00ff00000000ffff

def C1_patterns : Nat := 0x0

def C1_N : Nat → Nat
  | 2 => 5
  | 3 => 26
  | 4 => 60
  | 5 => 36
  | 6 => 1
  | _ => 0

def C1_counts : Nat → Nat
  | 2 => 0x2003000
  | 3 => 0xd00d000
  | 4 => 0xe02d001
  | 5 => 0x23001
  | 6 => 1
  | _ => 0

def C1_specs : Nat → Nat
  | 2 => 0x201281000
  | 3 => 0x381381000
  | 4 => 0x481501101
  | 5 => 0x601101
  | 6 => 257
  | _ => 0

def C1_seeds : Nat → List Nat
  | 2 => [0x0, 0x8, 0x6]
  | 3 => [0x0, 0x6e41203, 0x1c05c42]
  | 4 => [0x2, 0x34419794070689b0983d0040702c0f, 0x2a6c3902]
  | 5 => [0x2, 0x66382308880301015f008025010, 0x0]
  | 6 => [0x2, 0x0, 0x0]
  | _ => []

def C1_records : Nat → List (List Nat)
  | 2 => [[], [0x3a33e33c3], [0xe170a3281]]
  | 3 => [[], [0x3c36c73d346b6672ed48b20e4e76273cb3c76a7], [0x22383464c6ace0ce091c62858c8068ce0ce0b92c3836a786dd18d09c19e1a3]]
  | 4 => [[0x1f], [0x6a778f61734f29d84f46f6af39756f3178ef32f04f25d1af12f4bb42f1ef4d77af6b741b82f2db46b8cf72f0af5f786f58f50f17e7ef1cf65774f7cf88f44f47b55768f], [0x109c9c62673834e84e2e33739c1536a34eb4e4e3235a13878c70f10e1e19c3a1383]]
  | 5 => [[0x1f], [0x37f8bf0dd6ff87f0fe11f27f71f07f23f2bf1bf5df81f42f53f09f43f02f03f8cf09b0ff1af0df77f39f07715f5bf39786f19f8df], []]
  | 6 => [[0x1f], [], []]
  | _ => []

def C1_S (s j : Nat) : List Nat :=
  qGroupedState C1_initial 3 32 7 C1_patterns C1_values (C1_counts s) (C1_specs s) (C1_records s) j

def C1_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C1_initial (C1_counts s) (C1_specs s) (C1_seeds s) ws

def C1_groups : List (Nat × Nat) := [(22,0x40204008), (25,0x200008), (26,0x8004000), (12,0x6000), (5,0x202088), (17,0x280000), (28,0x40000000), (9,0x2000), (10,0x4008), (2,0x8)]
def C1_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C1_groups ws else diffCover 0xffffffff C1_groups ws
def C1_Z := barBudget 0xffffffff 0xe8a8e888 C1_cover C1_S C1_N C1_idx
def C1_flat := certAt C1_Z C1_N 7
def C2_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C2_values : Nat := 0xfffffffffffffffcfffffffafffffff0ffffffeeffffffccffffffc0ffffffaaffffffa0ffffff88ffffff80ffffff55ffffff33ffffff11ffffff0fffffff05ffffff03ffffff00fffffe00fffffcfcfffffc00fffffafafffffa00fffff800fffff0f0fffff000ffffeeeeffffee00ffffec00ffffea00ffffccccffffcc00ffffc0c0ffffc000ffffaaaaffffaa00ffffa0a0ffffa000ffff8888ffff8800ffff8080ffff5555ffff5500ffff3333ffff3300ffff1111ffff0f0fffff0f00ffff0505ffff0303ffff00fffffeff00fffcfffcfffcff00fffc0000fffafffafffaff00fffa0000fff8ff00fff0fff0fff0ff00fff0f0f0fff00000ffeeffeeffeeff00ffee0000ffecff00ffeaff00ffccffccffccff00ffccccccffcc0000ffc0ffc0ffc0ff00ffaaffaaffaaff00ffaaaaaaffaa0000ffa0ffa0ffa0ff00ff88ff88ff88ff00ff80ff80ff55ff55ff55ff00ff33ff33ff33ff00ff11ff11ff0fff0fff0fff00ff05ff05ff03ff03ff00ffffff00fc00ff00fa00ff00f000ff00ee00ff00cc00ff00aa00ff000000fefefefefefefe00fefe0000fe00fe00fcfcfcfcfcfcfcf0fcfcfcccfcfcfc00fcfcf0f0fcfcccccfcfc0000fcf0fcf0fcccfcccfc00fc00fafafafafafafaf0fafafaaafafafa00fafaf0f0fafaaaaafafa0000faf0faf0faaafaaafa00fa00f8f8f8f8f8f8f8f0f8f8f800f8f8f0f0f8f80000f8f0f8f0f800f800f5f5f5f5f3f3f3f3f1f1f1f1f0fff0fff0ff0000f0f0fffff0f0f0fff0f0f0f5f0f0f0f3f0f0f0e0f0f0f0c0f0f0f0a0f0f0f080f0f0f000f0f0e0e0f0f0c0c0f0f0a0a0f0f00000f0e0f0e0f0c0f0c0f0a0f0a0f000ff00f000f000f0000000eeeeeeeeeeeeeecceeeeeeaaeeeeee00eeeecccceeeeaaaaeeee0000eecceecceeaaeeaaee00ee00ecececececececccececec00ececccccecec0000ecccecccec00ec00eaeaeaeaeaeaeaaaeaeaea00eaeaaaaaeaea0000eaaaeaaaea00ea00e0e0e0e0e0e0e0c0e0e0e0a0ddddddddcfcfcfcfcdcdcdcdccffccffccff0000ccccffffccccccffccccccddcccccccfccccccc8ccccccc0cccccc88cccccc80cccccc00ccccc8c8ccccc0c0cccc8888cccc0000ccc8ccc8ccc0ccc0cc88cc88cc00ff00cc00cc00cc000000c8c8c8c8c8c8c8c0c8c8c888c0c0c0c0c0c0c000c0c00000c000c000bbbbbbbbafafafafababababaaffaaffaaff0000aaaaffffaaaaaaffaaaaaabbaaaaaaafaaaaaaa8aaaaaaa0aaaaaa88aaaaaa80aaaaaa00aaaaa8a8aaaaa0a0aaaa8888aaaa0000aaa8aaa8aaa0aaa0aa88aa88aa00ff00aa00aa00aa000000a8a8a8a8a8a8a8a0a8a8a888a0a0a0a0a0a0a000a0a00000a000a0008888888888888800888800008800880080808080777777775f5f5f5f55ff55ff55ff00005555ffff555555ff5555555555555500555500005500ff005500550050505050444444443f3f3f3f33ff33ff33ff00003333ffff333333ff3333333333333300333300003300ff00330033003030303022222222111111110fff0fff0fff00000f0fffff0f0f0fff0f0f0f0f0f0f0f000f0f00000f00ff000f000f000c0c0c0c0a0a0a0a050505050303030300ffffff00ff00ff00ff000000f000f000cc00cc00aa00aa0055005500330033000f000f0000ffff0000ff000000f0f00000cccc0000aaaa000055550000333300000f0f000000ff000000f0000000cc000000aa00000055000000330000000f00000000

def C2_patterns : Nat := 0x2558559559559559555515151515254550941905815

def C2_N : Nat → Nat
  | 2 => 48
  | 3 => 219
  | 4 => 500
  | 5 => 363
  | 6 => 34
  | 7 => 1
  | _ => 0

def C2_counts : Nat → Nat
  | 2 => 0x1501b000000
  | 3 => 0x404807501a000
  | 4 => 0x37146076001
  | 5 => 0x9e0c7006
  | 6 => 0x21001
  | 7 => 1
  | _ => 0

def C2_specs : Nat → Nat
  | 2 => 0x481481000000
  | 3 => 0x301601681501000
  | 4 => 0x501681616101
  | 5 => 0x601616216
  | 6 => 0x601101
  | 7 => 257
  | _ => 0

def C2_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x283221859fd8809, 0x1d407050400aa6, 0x0]
  | 3 => [0x0, 0x2197fa160140105c49, 0x35806d784002422202b00100060eb029009854c0ce004012020800c00502f800c17600600700f40400020bb001c004004, 0x6630fa00703e00502906010884483900101706b002018002003010, 0x1d]
  | 4 => [0x2, 0x690060080116b803e04600e00100100302301983601500101009439b02701a8352b401102104303000c002803, 0x35a94d01000d809a0060353b7403e00d003800440c00a030000626600107f8230026005891010c00e13900080744b10cc04100e85d0040096c2500a800f030c19800a00101d01c400400700109000b40ec00800200100030170004016023191000400801500100400e000d054004000800100e000401000101e83520140280518130050020, 0x24d671062c3dc7d0340f0062227c2105475, 0x0]
  | 5 => [0x13, 0x6d946000a00209a3a901100b89d00100587f0860330080050bc01900f00c09f02800200287400302e1e385b83e0010fb0f70508c700b83d00107b80500f00f00307d01f05301005200f015, 0x160131a500100472f01e8710c101200500e02200917b05189e0b506425600801c0070018360090144201e100206c03800100505d17d800055002019, 0x0, 0x0]
  | 6 => [0x2, 0x7388217a582101e110001816001, 0x0, 0x0, 0x0]
  | 7 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C2_records : Nat → List (List Nat)
  | 2 => [[], [], [0xaa2b89164912a4b425d9244a92c09364522acae2549e42a9258952770aa4d41429d82ce3405085711d89443b1608aa3b04d2572310922491148bb3404ec5922b0ec1491a02782b91164521dcae4], [0x559e0ae0621ac920549e4b40561d8b20941a0960919ac920942188a0941a0980941ac920671a0980929a0980941a49208f2188a0809ac9207ca188a0942108a04da188a0821a0980941a0940942148a0941a8920], []]
  | 3 => [[], [0x809e387979e4677b1d367949e3a76a1d8877c9e0c77f9e507459d247961e4a75d9e3c77b9e447671e087951e4e7], [0x310d65941a8b28570d3a762be50c33c15e928441a50a419a0998431170ce26198ca91ccd52394160c782bb152791aa4f2554968d28261a504b34a1703671a07284896506b2b109225496852840963c8619e0ae43b1648c4248e68762ca15a394158cac3b1552794ca0ea5999d8b25261a50bc19d8b25942ac7282518ec59326d0c3549e43284519884954a0f05941f0a9b22d2507b2ca1503942e8728420e508c34a126594148d282e9a084c34a11e5682a47283b96605731ac938671a02ab2b8a50b41b14ae6942187283d15385732a4f31671a0b23359650aa1b38d099895ccab2ba958768ca10a35595e4ab2b9936452ab0ec13b1668782b9a026b2ca0c4694170ca92d0d58761b3cec5942bc728560e50692ab0ec95496a4a92d2a60762cc55239416ccab2b8e505a331093294164d283895364524a0f259b2a47322b99364561d8b2c671a229b2299884931e0ae5], [0x941ac92180b1c922943149223b15c8a49a1d8b24941a0981941a0988941a09804aa188b07ca788a4942708a468b38d019433cd01942a4f21942348a4942188a860af892294340d01549d8d01941ac9224c2188a85f1ac930991e0ae4941e4b4494250d01941d8b24941ac924942f4d01941a098494338d01942508a4942188a463b10922941ac920941ac928992acae29b2a4f21942a4b42942acae29431c92282344d019426c8a494344d019b2a4b425495c922942188a294318922942f492265b20d01659a0988942acf0192b44d01942788a4942188b094310922942b0ec1942b0b22942188a1941ac930942748a4941a099091b1c9224c2548a494234922941e0ae4641a09904f26c8a4942188a09a2b0ec18f2788a4941a0982609ac928], [0x94344d04c04a0d049228250c7359241284f2188a0]]
  | 4 => [[0x1f], [0x4811d068610f086711fa680806e67c90dc6559d2a6541d8866f994268010fe4431db260f993648f1a5065b991498091f2665917474490b4982023047a19028940e2846201bc66e1936618924a060920262ca57078f01a4684921e494122248911f209404f287518566781a4668191ce672981e629252282b260864c1010027999c082122c412902e4471a50292914871e919c635a17c62626500841234431251099180e2862111e89191c466d99c66771a3c45911a6490115878510ea8929990643997248691c065a1df044d80c04], [0x8dbd0f28071e69283b44d198b95dcee391e50c43ca00477a9daaf4299e4ac83ca070794064ef94c1e50ab1c80da7940e4f28811e51153bf4a679441cf28209e50103ca1827940c8f28941e50493ca14079b2a57322bda50183b2c98e94498f28079e50013ca1b079414cf283a1e505ab1ac93994438f31941e50c93ca20a7943d0f287f1e504c34a22679442cf28669e50243ca06c746927422040e5078aca0d0794200f280a1e50063a550d395ca0f28399e73283ca1ba7942c4f28089e2eee3cd95339404cf1b3b3650ef3c58da794464ef4529e50fa3ca014794178f2d941e42fd3c809c7943ccf28659e50d63ca0fc791b1cf283cb650865ca14674311711e4f1e504d3b1c93a5e9275284f9e2cef3ca16c79425cf343b36511f3ca0d6d942f8f28151cd649c4a0c2794140e6b24f250543ca0ce7984a0f33941e509b3ca13079400cf284a1e40fe3ca1a27941bce6b24ea50203ca0b27940b0f28169e68762ca12a765b20e9422f250763ca086794458f2154ae50782ca19e794468f286a9e509e3ca0607941c8f287d9e5d283c11967940a0f25689e50ac9ca17a794480e984a9e50e43cd65078d3d4f28049e50553af8d754a1a3328261e65283ca0da7940fcf28511e503a34a13a794320f2855ae50b53ca152794258f343b1e50f13ca2427941acf283c1d3c45e4a00e7341335280a9e50123ca1f875495cf28069e50a73ca03a794328f2835d552763c689c794398f288b9cd04ccca1dc7943c8f281a1e50ab9cd0ed577294f283c366d283ca0d65943b0e682660740834d95279431cf28231c5c082ca09c79405cf28629d3c9b3b057c768b38f28119e503a3cde507940ccefe54ce50863ca1d6794014e8d22f18ec43ca17e794270f282d3a502f3ca1c27940ecefd391e506c3ca0f359402cf28171650633ca008794338f28769e50653cd952394098f282d1e50d73ca09075e9a3301609e50b03ca158794058f282cb8d04ce4a248794298f28562e50221ca08e78f254f28619e50ac1ca0e07, 0x271283ca0fa794132d284d1e50b33b2099694190e8622f250993ca1047942187281e1e50d03ca1b4794198e762b9e50223ca0b3694164d28061e50cc3ca0a2794110f28139e50213ca08a794234f283c9dde57b4a1567940f8f28601e2ca03cc8ae694020f28611e64573ca14a7940b8e8622e6501c3ca0ae7940d4f28149e50fd3ca08479421a728881e50833ca03c794131d01639e505f3c8d7c794318ec135b6645774a0b469446cf280d1e50792ca1ea782344ef94f1e501b3a188ba943a4f28201e34a03a610cb], [0x689a09989446cec5942a4d039a4a1583941248a69a4a0ec59434498663b0492a4f2548b468b20d119a4a0b269415c92694344d034f2608ac9431c926994a156394344d01942788a6943d4ec5943bcae668b2cd09341248b8940e8442994a0ae6941a0923639ac938942788a5942788b4941a08a59b4a15239b4a0b469445cae694344d099448552363af89329431c9239431c9229415c8a69b4a0f25942788ac940b8441942790c394344d11940e85c44f2188b89431cd65941d88a5942788a49431c932994a0f059431c92a94344d05942a4923941d8d05943f9523], []]
  | 5 => [[0x1ca62e0d], [0x100a3b285c84a9868a79a9b4a7e2a0e66090a8a7aa802a9418daa772a20a21a93ca092a3ea041828a9429fa61f2998a8ba880a0ca838a05a986a64aa1ca5ea81aa20a94ca59a8e0a5f2990614a8e8a9a2a505262418a992812a9010aaa192848a771952a4ba8caa0b912aa2128aea7629faa9329baa24aa36a8aaa34a652830a29a97c609aa16a63a898a392a3440400fca6e9034a60a820a0aa996a052a0aa072870a22a928a4c28a0a4b285ca112820423a946a19a9aea8b29e865028d6877a9e8a4ca9e4a7da860a83a96aa602844716283061b29fca322944a10283aa39a836a74aa2c430a8c6a15281ea04116ca412850a65909aa132906a6b299aa28a90ca1d282ea53a93ea431e72a52a984a272a6ca1e287ea943c10a75a86aa6c293048128dea362990a2fa8d0a90a9c2a35a9daa4d297ea8caa26a94008ca13a91aa7d2a40a6aa962a1d2648a68a81e633282ca9411c8a73283ca78a822a], [0x25008bcca517940e9f1b393e5068bca1a27941a0f32941e511778e820e94484f16273cda4eba788be94126f28503e5045bca075794114f2836de50a03b44d1b3914def4395e511bb8b820d94125f36941e69283ca010f94278f2852de509ebca1eb794042e180b9e5053bca0daf7ea96f34945e50c73cda50f941c9f288d9d8e49dca08af63b05f2152be50a93ca0457944a1f281d5a5121bca152f7714eed13466501838e8316501b6f282bbe502e2ca0ae7943faf2852bc5c18aca03174f1178c724ea502eb8e85dc941b4f286b3e50687b44d1d943d4f2854de50d1ba94e4f5294de2e116650493ca0af79431df283b5dde4eba790db94089728529e50c7bca0e579445ce3a116a346d7b1cd7d0803cf28173e50723ca09c7944a0e6822f6502e6b459170c040f28505e40a07ca2517940e8f1729be50223b4499e9413ae6824ee50533a792b7941d8f281d1a50d63ca1de763afaf2877bd3c45eca13cf943f8f28083e503a74a01071106272868be50229ca236f24917c1007de50221ca05c794061f286b5e65287a809d74f261f28081dea6dbca242f940baa22082e50f578602ef943bef36945e50fe7ca044f7f282f34943e504e7b1c93e941d9ed165be5117bca0a6f], [], []]
  | 6 => [[0x1f], [0xa7f941e43f0c5da3f7afcd1f087d4bf083ddff117c5dd397e2ff1d7c75e507d3df6b7c31f63fc9df177cdbf116c93f8dfdfdf947e51722fe50f], [], [], []]
  | 7 => [[0x1f], [], [], [], []]
  | _ => []

def C2_S (s j : Nat) : List Nat :=
  qGroupedState C2_initial 5 32 9 C2_patterns C2_values (C2_counts s) (C2_specs s) (C2_records s) j

def C2_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C2_initial (C2_counts s) (C2_specs s) (C2_seeds s) ws

def C2_groups : List (Nat × Nat) := [(25,0x8282800), (26,0x40484800), (28,0x20606000), (3,0x8080880), (6,0x404080), (5,0x202080), (10,0x4800), (17,0x280000), (20,0x600000), (18,0x480000), (9,0x2800), (12,0x6000)]
def C2_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C2_groups ws else diffCover 0xffffffff C2_groups ws
def C2_Z := barBudget 0xffffffff 0xe8e8e880 C2_cover C2_S C2_N C2_idx
def C2_flat := certAt C2_Z C2_N 8
def C3_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C3_values : Nat := 0xfffffffffffffffcfffffffafffffff0ffffffeeffffffccffffffc0ffffffaaffffffa0ffffff88ffffff55ffffff33ffffff0fffffff00fffffefefffffcfcfffffcf0fffffcccfffffc00fffffafafffffaf0fffffaaafffffa00fffff8f8fffff5f5fffff3f3fffff0fffffff0f0fffff0c0fffff0a0fffff000ffffeeeeffffeeccffffeeaaffffee00ffffececffffeaeaffffe0e0ffffddddffffcfcfffffccffffffccccffffccc0ffffcc88ffffcc00ffffc8c8ffffc0c0ffffc000ffffbbbbffffafafffffaaffffffaaaaffffaaa0ffffaa88ffffaa00ffffa8a8ffffa888ffffa800ffffa0a0ffffa080ffffa000ffff8c8cffff88ccffff8888ffff8880ffff8800ffff8080ffff8000ffff7777ffff5f5fffff55ffffff5555ffff5500ffff5050ffff4444ffff3f3fffff33ffffff3333ffff3300ffff3030ffff3000ffff2222ffff1515ffff1155ffff1111ffff1100ffff1010ffff0fffffff0f0fffff0f00ffff0cccffff0c0cffff0c00ffff0a0affff0808ffff0555ffff050fffff0505ffff0500ffff0404ffff0303ffff0101ffff00ffffff00f0ffff00ccffff00c0ffff00aaffff0088ffff005fffff0055ffff0050ffff0044ffff0033ffff0011ffff000fffff000cffff000affff0005ffff0003fffefffefffe0000fffcfffcfffcfff0fffcffccfffcff00fffcfcfcfffcf0f0fffcccccfffc0000fffafffafffafff0fffaffaafffaff00fffafafafffaf0f0fffaaaaafffa0000fff8fff8fff88888fff80000fff5fff5fff50000fff3fff3fff30000fff0fffffff0fff0fff0ffc0fff0ffa0fff0ff00fff0fcf0fff0faf0fff0f0f0fff0f000fff0ccc0fff0aaa0fff0a000fff08880fff00000ffeeffeeffeeffccffeeffaaffeeff00ffeeeeeeffeeccccffeeaaaaffee0000ffecffecffec0000ffeaffeaffea0000ffe0ffe0ffe00000ffddffddffcfffcfffccffffffccffccffccffc0ffccff88ffccff00ffccfcccffccf0c0ffcceeccffccccccffccaa88ffcc0000ffc8ffc8ffc0ffc0ffc0ff00ffc0c0c0ffc00000ffbbffbbffbb0000ffafffafffaf0000ffaaffffffaaffaaffaaffa0ffaaff88ffaaff00ffaafaaaffaaf0a0ffaaeeaaffaacc88ffaaaaaaffaaaa00ffaa8888ffaa0000ffa8ffa8ffa8ff88ffa8ff00ffa80000ffa0ffa0ffa0ff80ffa0ff00ffa0f000ffa0a0a0ffa0a000ffa00000ff8cff8cff88ffccff88ff88ff88ff80ff88ff00ff88f888ff88f080ff88aa88ff888888ff880000ff80ff80ff80ff00ff77ff77ff770000ff5fff5fff55ffffff55ff55ff55ff00ff555555ff550000ff50ff50ff44ff44ff3fff3fff3f0000ff33ffffff33ff33ff33ff00ff333333ff330000ff30ff30ff30ff00ff300000ff22ff22ff220000ff15ff15ff11ff55ff11ff11ff11ff00ff10ff10ff0fffffff0fff0fff0fff00ff0f0f0fff0f0000ff0cffccff0cff0cff0cff00ff0aff0aff08ff08ff05ff55ff05ff0fff05ff05ff05ff00ff04ff04ff03ff03ff01ff01ff00ffffff00fff0ff00ffccff00ffc0ff00ffaaff00ff88ff00ff5fff00ff55ff00ff50ff00ff44ff00ff33ff00ff11ff00ff0fff00ff0cff00ff0aff00ff05ff00ff03ff00fe00ff00fc00ff00fa00ff00f800ff00f500ff00f300ff00f000ff00ee00ff00ec00ff00ea00ff00e000ff00cc00ff00c000ff00bb00ff00af00ff00aa00ff00a800ff00a000ff008800ff007700ff005500ff003f00ff003300ff003000ff002200ff000f00ff0000ffff000000fefefefefefefcfcfefefafafefef0f0fefeeeeefefeccccfefeaaaafefe0000fefcfefcfefc0000fefafefafefa0000fef0fef0fef00000feeefeeefeee0000feccfeccfeaafeaafeaa0000fe00fe00fe00fc00fe00fa00fe00f000fe00ee00fe00aa00fdfdfdfdfcfffcfffcfcfffffcfcfcfcfcfcfcf0fcfcfcccfcfcfc00fcfcf8f8fcfcf0f0fcfcececfcfcccccfcfca8a8fcfc0000fcf8fcf8fcf0fcf0fcf0f0f0fcf0cc00fcf00000fcecfcecfcccfcccfcccf000fcccccccfccc0000fca8fca8fc00fc00fc00f000fc00cc00fc000000fbfbfbfbfbfb0000fb00fb00fafffafffaff0000fafafffffafafafafafafaf0fafafaaafafafa00fafaf8f8fafaf0f0fafaeaeafafac8c8fafaaaaafafaa0a0fafa8888fafa0000faf8faf8faf8f8f8faf8f0f0faf80000faf0faf0faf0f8f0faf0f0f0faf0f000faf0aa00faf0a000faf00000faeafaeafaea0000fac8fac8faaafaaafaaaf000faaaaaaafaaa0000faa0faa0faa0f000faa00000fa88fa88fa00ff00fa00fa00fa00f800fa00f000fa00ea00fa00aa00fa00a000fa000000f8fcf8fcf8f8fcfcf8f8f8f8f8f8f8f0f8f8f888f8f8f800f8f8f0f0f8f8a8a8f8f88888f8f80000f8f0f8f0f8f0f0f0f8a8f8a8f888f888f800f800f7f7f7f7f7f70000f700f700f5fff5fff5f5fffff5f5f5f5f5f5f0f0f5f55555f5f50000f5f0f5f0f555f555f500f500f4f4f4f4f3fff3fff3ff0000f3f3fffff3f3f3f3f3f3f0f0f3f33333f3f30000f3f0f3f0f3f0f0f0f3f00000f333f333f3330000f300ff00f300f300f300f000f3003300f2f2f2f2f2f20000f200f200f1f5f1f5f1f1f5f5f1f1f1f1f1f1f0f0f1f0f1f0f0fffffff0fff0fff0fff0f0f0ff00fff0ff0000f0fcfcfcf0fcf0fcf0fcf0f0f0faf0faf0f8f0f8f0f5f5f5f0f5f0fff0f5f0f5f0f5f0f0f0f4f0f4f0f3f0f3f0f1f0f1f0f0fffff0f0fff0f0f0fcfcf0f0fcf0f0f0fafaf0f0f8f8f0f0f5fff0f0f5f5f0f0f5f0f0f0f4f4f0f0f3f3f0f0f1f1f0f0f0fff0f0f0fcf0f0f0faf0f0f0f5f0f0f0f3f0f0f0e0f0f0f0c0f0f0f0a0f0f0f080f0f0f050f0f0f030f0f0f000f0f0e0e0f0f0e0c0f0f0e0a0f0f0e000f0f0c0c0f0f0c000f0f0b0b0f0f0a0f0f0f0a0a0f0f0a080f0f0a000f0f08080f0f07070f0f05050f0f030f0f0f03030f0f03000f0f02020f0f00f0ff0f000f0f0f00000f0e0f0e0f0e0f0c0f0e0f0a0f0e0f000f0e0e0e0f0e0a0a0f0c0f0c0f0c0f000f0c0c0c0f0c00000f0b0f0b0f0a0f0f0f0a0f0a0f0a0f080f0a0f000f0a0e0a0f0a0a0a0f0a0a000f0a00000f080f080f070f070f050f050f030f0f0f030f030f030f000f0303030f020f020f00ff00ff000fffff000ff00f000f0f0f000f000f000c000f000a000f0000000efefefefefef0000ef00ef00eeffeeffeeff0000eeeeffffeeeeeeeeeeeeeecceeeeeeaaeeeeee00eeeeececeeeeeaeaeeeee0e0eeeecccceeeeaaaaeeee8888eeee0000eeeceeeceeeccccceeec0000eeeaeeeaeeea0000eee0eee0eee00000eecceecceecceccceecccccceeccaa00eecc0000eeaaeeaaeeaacc00eeaaaaaaeeaa0000ee88ee88ee00ff00ee00ee00ee00ec00ee00ea00ee00e000ee00cc00ee00aa00ee000000ecececececececccececccccececa0a0ecec0000eccceccceccccccceca0eca0ec00ec00eaeaeaeaeaeac0c0eaeaaaaaeaea0000eac0eac0eaaaeaaaeaaaaaaaeaaa0000ea00ea00ea00aa00e8e8e8e8e0f0e0f0e0e0f0f0e0e0e0e0e0e0e0c0e0e0e0a0e0e0e000e0e0c0c0e0e0a0a0e0e00000e0c0e0c0e0a0e0a0e0a0a0a0e000e000dfdfdfdfddffddffddddffffddddddddddddccccdddd5555dddd0000ddccddccdd55dd55dd00dd00dcdcdcdcd5d5d5d5d0d0d0d0cfffcfffcfff0000cfcfffffcfcfcfcfcfcfcccccfcf0f0fcfcf0000cfcccfcccfcccccccf0fcf0fcf00ff00cf00cf00cececececdddcdddcdcdddddcdcdcdcdcdcdcccccdcccdccccffffffccffccffccffccccccff00ffccff0000ccfcccfcccfccccccceecceeccddddddccddccddccddccccccdcccdccccfcccfcccdcccdccccffffccccffccccccfcfcccccfccccccceeeeccccddddccccddccccccdcdccccccfcfcccccdcdccccccffccccccddccccccc8ccccccc0cccccc88cccccc00ccccc8c8ccccc888ccccc0c0ccccc000cccc8c8ccccc88cccccc8888cccc8800cccc8080cccc4444cccc0ccccccc0c0ccccc00cccccc0000ccc8ccc8ccc8cc88ccc8c8c8ccc88888ccc0ccc0ccc0cc00ccc0c0c0ccc00000cc8ccc8ccc88cccccc88cc88cc88cc00cc88c888cc888888cc880000cc80cc80cc44cc44cc0ccccccc0ccc0ccc00ffffcc00ff00cc00cccccc00cc00cc00c000cc008800cc000000c8ccc8ccc8c8ccccc8c8c8c8c8c8c888c8c8c0c0c8c88888c8c80000c8c0c8c0c888c888c8888888c800c800c4c4c4c4c0ffc0ffc0f0f0f0c0f0c0f0c0ccccccc0ccc0ccc0c0ffffc0c0f0f0c0c0ccccc0c0c0c0c0c0c000c0c08080c0c00000c080c080c000c000c0000000bfbfbfbfbbffbbffbbbbffffbbbbbbbbbbbbaaaabbbb3333bbbb0000bbaabbaabb33bb33bb00bb00babababab3b3b3b3b0b0b0b0afffafffafafffffafafafafafafaaaaafaf0f0fafaf0000afaaafaaaf0faf0faf00af00aeaeaeaeababababaaffffffaaffaaffaaffaaaaaaff00ffaaff0000aafaaafaaaeeaaeeaabbaabbaaafaaafaaabaaabaaaaffffaaaaffaaaaaafafaaaaaeeeeaaaabbbbaaaaafafaaaaababaaaaaaffaaaaaabbaaaaaaa8aaaaaaa0aaaaaa88aaaaaa00aaaaa8a8aaaaa888aaaaa0a0aaaaa000aaaa8888aaaa8800aaaa8080aaaa2222aaaa0a0aaaaa00aaaaaa0000aaa8aaa8aaa8aa88aaa8a8a8aaa0aaa0aaa0aa00aaa0a0a0aaa00000aa88aa88aa88aa00aa888888aa880000aa80aa80aa22aa22aa0aaa0aaa00ffffaa00ff00aa00aaaaaa00aa00aa00a000aa008800aa000000a8a8a8a8a8a8a0a0a8a88888a8a80000a8a0a8a0a888a888a800a800a2a2a2a2a0ffa0ffa0f0a0f0a0aaa0aaa0a0ffffa0a0f0f0a0a0aaaaa0a0a0a0a0a0a000a0a08080a0a00000a080a080a000a000a00000008f8f8f8f8c8c8c8c8a8a8a8a88ff88ff88cc88cc88aa88aa8888ffff8888cccc8888aaaa888888888888880088888080888800008880888088008800880000008080808080800000800080007f7f7f7f7f7f00007f007f0077ff77ff77ff00007777ffff77777777777700007700ff007700770070f070f07070f0f0707070705fff5fff5fff00005f5fffff5f5f5f5f5f5f00005f00ff005f005f005757575755ffffff55ff55ff55ff000055775577555f555f5555ffff5555777755555f5f555555ff555555555555550055555050555544445555000055505550554455445500ff0055005500550000005454545450f0f0f050f050f05050f0f05050505050500000500050004ccc4ccc4c4ccccc4c4c4c4c44cccccc44cc44cc4444cccc444444444444000044004400404040403fff3fff3f3fffff3f3f3f3f3f3f00003f003f003737373733ffffff33ff33ff33ff000033773377333f333f3333ffff3333777733333f3f333333ff333333333333330033333030333322223333000033303330332233223300ff0033003300330000003232323230f030f03030f0f03030303030300000300030002a2a2a2a22aa22aa2222aaaa222222222222000022002200202020201f1f1f1f151515151313131311ff11ff11551155113311331111ffff1111555511113333111111111111000011001100101010100fffffff0fff0fff0fff00000ff00ff00f5f0f5f0f3f0f3f0f0fffff0f0ff0f00f0f5f5f0f0f3f3f0f0f0fff0f0f0f0f0f0f0f000f0f0c0c0f0f0a0a0f0f00000f0c0f0c0f0a0f0a0f00ff000f000f000f0000000e0e0e0e0ccc0ccc0c0ccccc0c0c0c0c0c0c00000c000c000aaa0aaa0a0aaaaa0a0a0a0a0a0a00000a000a00080808080707070705ff05ff05550555050f050f0505ffff0505555505050f0f0505050505050000050005000404040403ff03ff03330333030f030f0303ffff0303333303030f0f030303030303000003000300020202020101010100ffffff00ffff0000ff55ff00ff33ff00ff0fff00ff00ff00ff00f000ff00cc00ff00aa00ff000000fc00fc00fa00fa00f0f0f000f000f000f0000000ee00ee00cccccc00cc00cc00cc000000c000c000aaaaaa00aa00aa00aa000000a000a00088008800770077005f005f0055ffff00555555005500ff00550055005500000050005000440044003f003f0033ffff00333333003300ff0033003300330000003000300022002200110011000fffff000f0f0f000f00ff000f000f000f0000000c000c000a000a00050005000300030000ffff0000fff00000ffcc0000ffaa0000ff000000fcfc0000fafa0000f0f00000f0000000eeee0000cccc0000cc000000c0c00000aaaa0000aa000000a0a0000088880000777700005f5f000055ff0000555500005500000050500000444400003f3f000033ff000033330000330000003030000022220000111100000fff00000f0f00000f0000000c0c00000a0a0000050500000303000000ff000000f0000000cc000000aa00000055000000330000000f00000000

def C3_patterns : Nat := 0x25594645855956458559561565565555454951525465152546516454951945915855

def C3_N : Nat → Nat
  | 3 => 196
  | 4 => 0x60c
  | 5 => 0xb05
  | 6 => 0x3ee
  | 7 => 31
  | 8 => 1
  | _ => 0

def C3_counts : Nat → Nat
  | 3 => 0x3308e003000
  | 4 => 0x14735a16a001
  | 5 => 0x1085e7410006
  | 6 => 0x2fd0eb006
  | 7 => 0x1e001
  | 8 => 1
  | _ => 0

def C3_specs : Nat → Nat
  | 3 => 0x481701181000
  | 4 => 0x681681681101
  | 5 => 0x601701696216
  | 6 => 0x681696216
  | 7 => 0x501101
  | 8 => 257
  | _ => 0

def C3_seeds : Nat → List Nat
  | 3 => [0x0, 0x1, 0x8003000593b032208e000c0050018001047030d0028032003888a0b100030be4074021c0d80068006039a02501040190074014005a01f0014006005c001, 0x287c008062026cc4045f1904e6679]
  | 4 => [0x2, 0x10ecc1531a515fa2a62a709181945dea9287e06f400201800600e21e60015a702300023c62a8800400602c8670020ae401404882280cc00601c80080060e800400822d516a01800a801c03701c800401c00113d8038014001157806c6f805a014c29802708f0be003610c00a000812c0e0004003000801602400c02a807a0b782c012401400c0010008018004001013000207f, 0x640c40b39ad0ca813c9ea04a8648016f842cd86a800c60a04800046643cf0094d6828000111c0e441ac09699a81900120053aca94406a0fb996805c0c000301680986520aa03002b00d00071b69108024013028038a5f0001003052814234f00d047402200800e80141e80350bd82d402800d9ad000801e00f09700040f200100bcb3c11c022014879c03c034000815000200200680300060060078070272029068028405e1ae02a81824dc00c006009001400203406a800803c039474c08400100c0224004040051001809a006001800c00c10f00b014c05601d01d0004004023019805c06601600182e00100219ad00f637c01204e81a400d35a0f0800403603106780102d6001006c6d400a00100b800c18e0750034d6a30c0340e801122f404500100e0004052006845c0a112200580140cc01c044000402c01a00100200690df011008003801600e801001c01900580080050dd0008004057099, 0x887b142b800c00a00401d800c72d14786f01953f8042000891800202f00082a800705522e8ed430c095031c51d35c00304cc05c00200d0c0039c07806912806f803e009004000418800109500343d404f8a380045fe01c00301b81180020010008242048059812c01e02c002021c046006038813c006002006823001c0010010004024010]
  | 5 => [0x13, 0x8f0b040121a600a010c03a05b2c5800424a002060cf206f09319df80244166652a983bc00202402380780980fc09c002e6a000d01a82787160db98d000866605e04980843a60021cd0104f9017808180225722a205186540be006000868e46a00104489ec07200515f000a8204300b400541bb2268f700c003006601182d80560a204980aa2ea03c00204a00ae01602f801008a33f006c53c00201e01003401bc02a069805028e003001802229c055060800400202a0af80182a000188c800c022102000801800601e00680ec228082000802c04201a88a004e1b006500dc2e829c0ea00080f0004130002804802000e000801c03c0090c2000c0c2024003806403908303881b005004c01a41a001000100d001012005e00b029802603a00c0038002004018c18000800f010805282002b001000c37a03f005801412201207800680661ba003800807007a00b019002001b09482bc018002000800e0b20f3002023002a00c000800801e0050240168118114000d040004134001015801a0350090074034030013000418001700080081e8019019803c00200103f80042620018200006022009, 0x115544d001428595f84af004c1700a6c003000e5e70068a3402a000100903d3012c05400a021f004c01b0aa64bf012401600041c40464010047c0010078023000e5e700b80030db414f000401700500482dd47c3002c016082649401a81850084013002002a015800702b00080342448000414d00380ff979c005019642d0dbc001026402b180c020116c75102f40931ab0009032c0030010056121e402979c05f01142d001a801500e0248008c1cc1930020000400f06841cb001c00900ec01500882af124803e07080c2000404f0d54025979c05f02d800500223d7024408e055000404025e70018005000400e000400200680028f0000e005000f01023700008168001a32c021000700083390094056000800401603458c98149000402a000401d8c24003003019d00380490d6001c00dc00302bc182009403d02c41c500080200050002007000200b22ec0f8c0f38b8a2d2000c18a03e013106f800201a811100bc004078807b89f400c0028120001c0fd040401e894400e00800160870027000400201e4006002c001005c04604d4002001c02f040800d02b81080b7000400f00018914004001a2240418014000800604c00be03f40c6886406a002003f882002200061bb0248063001405a002c001000c0170008003013e177011000401fa1300058029011c0f700200c6061800e000407083b409d000609c0020002004815300dc050011c00c82380070128036025000700180050048011000400400dc05b013800381fc051004c041001c037000400302480b8979c02700380010020166005c0e1005004b005c04600240070004003000c002000400781ec001017c010008800d0138005002804b0018047816400b0010002015800700080010014009000e0270004009000c02f0044022017406b012403c, 0x8fa0c01e900e10102400500325a4ad0b586f85c1a51020038480260470d900705414008482223e90821e04100101901100500304082000305881000c0b700680f22101002002b01908800b80d05402500d01002801600300100603300300a0290b8056]
  | 6 => [0x13, 0x4027095008091c16200100b032a09a25b035837030e0080ed00240029b04db001402a0fc02600740160790018038008002028001c0d60210d0800852c018033805802e0a6001800c00d00808280140060df005001c02600202d00bc0b8006, 0x4f38d544500860bc88380052c423a4a5811409c01421ac176005006112801c0b493580a853205a08e003c01603a03800a40da3e8097800400875202a83240140210b1842647808521485740a2005020c8705f20c104601d04280b3025010019e00503202181a11e7008008c08200309b8264004001046812c054002007c66804a02102102080a80028c0022401c00f000801627402905380a00cc00201f00040aa2b100080d40240ae02543b001200a0008014122005017432c1140810258014004001048806400801501a0018022025003811c05e06e049802c188012001001000e0ec006002c0290a683a823021000e049800c00a001014cbf400600500c00f003600200380080de00e00880dc0110440340008008004007007c002001000802400402b001826000200681c801000401100d0004004024, 0x0]
  | 7 => [0x2, 0x199f108401004018340a, 0x0, 0x0]
  | 8 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C3_records : Nat → List (List Nat)
  | 3 => [[], [0x5e2b75075cf3], [0x19c24b1b4c4f634965024e85358dce94f33f54ae36569ac6d09410daba6b1ae14d638828292cb5358da12591ba749636849f86cd0fe8d35a231b424b834ce8786fcd258da5a801ba74c836849486d2d418d3594053a850034045254f8d2e0d25a341be33fa37eab386d31358dad2d319ff27727c69246e9d0c1595a011a1f292673aa006d4d008da12041be35c2344e4eccd5d008da126f1a5c45b1698a006f212e0deaa4b1b4d4d6369886cab75400d25a358b4228264d688469d516a53e21e1b554d6380092c6d090e15a594f334250035e092c6d09428dabaf11bf649637c6b3c6eb9258dcf2801a6b29aa68499c6d5d3a0df42481af749635e08612d4d358da12d71a6b298a66892c684496a9ae26b1b575a637549ac6d09030da114f33a7500349650a4d08a6196d2384b464d636aeb506f8d738d70a1b8ab749635008786d5d780d6f26b1b424ba34184b64e911c15d3a5c1b9d5063684bcc6f8d258d6714293105e036b49d06d493a8d7324b1b424ec36849d46f91258daba751b5a4d636849a46e1d258d6d2268b574b037ca92c6b4ca6a9f1a571bd949637c6b386d093e0da62751bd53fa3684b606e81358d8e2e11bf549634968c07105131535a2e4ba441516b29ac695ca1495926b1af05c23684a0c69d0a6a92594192e24d63], [0x1aba6b29a2684a00d385f1a4b31e17c6c54bf05ae26b29a2684c8cc185f1a4b34e1684a00ca050611f21f06ae9acd385aba6b37214d692d1685f1a4b28426ae9acca850f94321e4684a010e05a132330417c692cca85aba6b4361684a00ca85abb1e300179a9accd850114321e86ae9acd285a12803821684a00d205a128045a1882e910385a128037216849ad0c05f1a4b46a16ae9acc905d22da46e16ae9acdf850891f21e844e4c487920024b28427c692cd70620ada44816ae9ad1705e6a6b33413fe4c487c1f1a4b4301794a00cc0600a4b364168492d0d8600a4b35417c692cd885a128029e2684a14a789f1a4b3721]]
  | 4 => [[0x1f], [0x34bd6eb74d5b65ef73f75677517b4e1b44ef29be4b9b2a3e88af848f7ecf800f6e976b9770775b9b4f1b37fd505b363d7b2f2077714f830f3bfd670f6e773c1d41af5f6f6cd74e7b5b3b6e571f974ebb40bb4ffb88ef6bf7655781cf503b664f782f70ef749738dd74773c5d523b68b769977437375d7aaf285e5a3b4dfb4bbb535b890f393d85cf5cb7844f519b840f5bf7888f468f854f6f573bdd208f422f70174d1b4edb69d75b5b5c3781af5eef69176bd774b755bb7c8f4fdb391d826f5e9b525b6cb7543b431d810f4b5b329d399d56577c6f71ef46bd82af32dd65d7464f66cf553b6c376f171a7d349d311d68d75b7b7e6f571b51db7577610f860f6b17415b1add4adb460f674f34fd4c1b5ebb449773975f8f351d1e776b57705731dd4e3b4fbb856f6a976a7750db395d74176af7439d51fb4ddb3abd383d57ef4cdb882f84af202f6df76e37413b3a9d4a7b361d529b3afd6b771fb75697377d40db56af69b7824f87af4efb6bb7470f29fe6c1735fd1fcf45dd5c77884f574f2a9e6d77653765971abd46ef83af5f1b41de513b3a5d5f3b341d389d537b3cfd6d375637555b822f70371f7b48b75c976a176ab785af53db6cf770af71175afb69f71eef32fd886f409b828f31fd1b9b1f3b50bb3a7d501b5c1781ef437d5a5b836f4bdb37dd299e75cf53fb73773fdb353d2b7e6b373cb77aef6f374197616f, 0x547b4bfb5c575adb4a5b816f842f56ef52bb7e2f36bd4a1b521b373d387d283e5977557b77ef44d74cfb55ef4a9b405b764f50fb48cf6c57880f7f0f6d9753bb6d174d3b814f509b818f42fd87cf6957559b7b6f87ef55d76ed775973c3d65b75e0f281e74ef61576577545b539b4f3b6c77745784cf5dcf5b1b3dcf858f486f4f9b4457598f3ffb2a5e83cf668f325d68f743f776175d2f515b35dd766f44b775f7732f709782ef4a3b443745bd7eaf6ad740fb507b411b44774cbb1f5b4b7b74d7511b32bd83ef5a1b5abb3a1d531b315b4177], [0x7488eaaee97a4dd22809bd649734d652d63f87e1d352375a0a32b98ae691a874cae5d22fb3c1f3c0d748706a92c1b8e3326b5a2434f534e4eeaf8d25adb3a909c654d6b6b4b6a6f8d3badd925a5afa497353869f3104d2353b9b9cc6a5ba77483f8f1047e1e2234e3bb26ae77a2972669c5ad5121b9aa70286b6aeb6a6b8ccad6209956bf834ed63c8ddae907cce20ae33b4229c76989ac69fd124d1b9a76bca44958b69ad6f8d53ad7b24b9ba434f549650a4c8171cd16a24abf84bcb69ca126acc8fcddc26b5ba436356b89ac6e90dcd5f7ace9c286ae780092e6d1d384e2522d6c2c7047748876b1bd35ad92aba5be3774767c8056e896b4d1d1b96be3372d448656afb524cd25a2dab4e3735744b6a6bc08fad03995ca7525cb4d68ed6fa1a11d1b9b96b9c5b534d652971cda19cff90fcc415acb764691ab8d0ecdaba6b3b8c6847888d5ce89103cd3594dd3ee68477c6eacec050de52593d9a273feb7a2ec8eec9d21d2d1a4cb574d635b48dd6bec582e20ba23c3f372d8ca9d571053bad011b9ca5e16b37648bced38a49d402249bf8362d75292e6f452d4d2e1319c5b402b46e7e5ad09791e1f3a43c00496b50087331493badd92805ae337f54bc7072bf535adad995ab4229f6882875ad0942ada114f726b45ad8729dd6fbd75cdc4a4b9b42436d756a026b8d2f4d062079afb23eb882a0d7000a139c12ab9bad431567c9ad6c94c7e54e1d4cbc8500b69c72aad09429da72909bbb68478eed08ed3903ce193423a1f21f58726e5a8dd16b58aa376b564ef36ae69eabd116e57d9e0698f23f932a47f304d4e2e24a6b5b8240f342243daf44cfd5d913b3ae336358a86e5a92d18cd7824b3b1544958e29ad6d09428d258b89a77292b5b46e72f6d121d92ae39be332ad87eb696f8d6d2df7ae19c654b0b8e6e74e84503ad7191f9ada1f93858890ebed7a2da727f9a5e36395789ad6bed121dc51313b4e4eb3764b696fbd27cdf4995cc4b684774469eabed3badad9bfabd134f549650b4f44ce560024b3b4223c782669daf45749d7da075af6431975a9926acc584da108f1c02497382697970f8dcb62b9b36bef59f38d4d08ebed6f9de8a273b23307974e92d718d35ade725e9b4e5b5380292e6becdcb6009aa6c57404b7de7f66d48a7d9eb1fd9b5c4d6b5f66c5b105692daba2eac4144875be47e6d3135cde89a4ac1a500b, 0x74e4c4ebd125cda12801a5e26334964f271b9a11dfa24b9c5d4d6b1fc3e56ec85a9d0611f9b255bf35006572f8d121dfe2dd399525b9882d5cef39d91de43ba39b9286d40e7e72f7d0f1dab27f9b2e40f38cabc96ae88fada62779aeb4d6b4964fe6a00e0e62ba705b35497357292e689087d6162075b2530996568dce86d03e5421b9cc3f5a4b7c69796d09911df1a075be346ad8cabc16eada11e209926c4145ed8ca9d16ead0dd52f1b9cae923eb4bc4ee6dccf055f1ba43a2726274544eecb48cae620b5a3a3744875e492e6b68dfe5eda5e5b42500b80a92e6f6d03adda3423b5734b56842f0f104a6b92f18fcb4e50138e6d2cee913bcda725a998f26358c8d08ee9d25ce0024b1c414bcb8049ad6c94c3e57dae33bb149735b47b328dc87b56d195cc446847756c0671cda11dd934e3c7343c779481f2ee916d5a12809c655a6b7bed08e968a1ae023423c3e73877c66c5abed0ead0f9433afb590b8dc9ad71193dad9d2243b34448774863eab687f2d9d1956b8a16a780692e71cdcf1df1a4b9b3a40eb4d62ed68e0dcb574ae33b2e32b57649796d090c55299319ba446e7422830e9f1124d6d14dd26b260b50870729fcdce639b4c399223f9800c40ed093a9df824b9bdb34ed764890ed6d7d9da125c5b5250b33484c6abd170cd0610fab4e474742247d7105a71e253423bcd4d6b3722e5a92c9f4dd21a4ac624eeb5b48eb2f9d25cdd6a4b9b5640f36b89aced5d35add3a5e5ba74967748b5a6f45d39daba809a3821ed79c69eabecdfb53b9c1cb4c286776481d7151a71d40194cb424ea373897a6d49404d92ae95c0749737d692e6d5d8e1d6f992aa0737398bc878edcccad592afb5af049637de92e6d1ca19e209cf6b575f675e8b8e687cdcd58e3015a2f34f544c43eae912f4d12218aaab46eb6ce72aacb91b9dd21dcaba45b534f65374c9570ce2094f724b28538d29d16a00d3e5c52535c62372d88ca016ff1a11e12b793be168475c663ea92d0de5cb1a7ab5c4f735d29796b68c7e5f52499c7668474ee8e96f9925cda626b5c4a5e8b8a4d38ed31359da611c3be3620774850acb8c584e303423b105ed346e81d63f07ccd8f224ab3a5c6740450d6f8c4c0cd21436c411f2b7b492e6fb0d3d59d32e3c44430d8c4d08ed08309d7498f6bc6764746e87ce9ac492d380b95bec49735c69de707ccab5d925c5a77286b, 0x7f0b8ced392f4dab94db3e349678ae9d56f8dab9d70a6b5b4e5f677948dda89cd3b570a6b1b1a5c737de95e669c98d52f2375a6a449365cbecec8cc165ae14db2e33c156dca0269ad0c65a125c9ae337355ac6572d6d3bcd7da5e5c314d6b764655af8d80ad8f207cb4229e650a53f4f8dbf1dcb25e9a5e45f369c6feb11135adabaf49c5768e78a89dd6f192f4e0c2a25b254193764751aec94e2dd22839bc829ee49650ac979124e2badf3b4247c78c69617111d69d7091f9b574bd35be9de6c5503e57dad65a1840f96849d56d5cdcd639ba93a8046eb5c681e67fcd3e5d91a76a7732b98889d56ead25cd70a6b3be35c67748b4a707d719d3fa375bec4bd3634bed69dcdfe5d92775c7a684788281d6b8d644d351a7cc7b6847756e9ce8dccab5481b9cb205f6b8ae9696d38a19e2bb4c3bfa4b0b4d68f56f8ca13a209a76b674ef37ee95e71190db6222805c4137ed472525d0e5a71df6a4b9b5746e78ca8056f452f4dae26b9c644d6b5f6b696ea535add91b16c445ecb4ee72b2d58dcd4dc9496afb324d5e092e6b20cae5a114f3be335cd4487e6b1956a2d401b9cbf55b4b6ae656ac70a6b9a71c1ac735ba78ae87ceb68d3e634ad35b574d7387ed38efbd2e4df4a4b9b014d6b4bc69f2bec96ad089956af45e0b40e69f3111a61dad9b9abc634f569c9de6d092e1da7195ac6f68474a62d66ae8582ddd3423b424b836d8a567105ce1e2b9926bb2382d5b489269dcc965e898faa6b29aa5c6b4a692d1b4df63423c01364d4d64f571a135ad88142b2e123937eae90ebc1719dd93a23be94d6b80ad08e89c87b571ada9c654dab46e86db1d1a11cca8b0cba749635d092e6fe0cab5d391a3c5769c76049ad7179a11d3594d7237404b40443f2d5d03cd749313af0496b5c68dcf11935ae20a805bef49337dc92e6fad35ad7d9a76c3f7487764b8cefe935ad55a249bad5013418656b1ddce9da38b93bb275675b48bf2d0135add91313be3500b4c850b4fb1d91d400621b4e34958ae6e5af34cd55f1a4b1a6746eb748656ad5d3dcdae31c3bb2372d64a64b30b155ae3bb4b3bc850ab882b696cd4fecde89ff9bab4bd364a8457148dcb53ba375a5a2633826751b105d21de699baa2744878ae6d1a890ffce253523a7734f98c49ad7104dcb5f1a645c3e4eeb6ae9de6d09401dd5a5c9b2032b964a65729d4a1ad2e12e9ae14d73, 0x17a26b5be35e8b41443f2e70d3d5a72373ada363932450dad09759de8a539aba566750053f4c95782da13233b4229477d2b8e6b68a169fbace9adf286743e80a6978ea652f195cbb272c7882705a92c4b4dd92845b5340f36ac8dce81c87e5ab8931bb24d4b6ae6feb0f96d2da13033b25567369c2e4ea40e5657d9956c7374e774881e6d0942cdf524b9c694d6b8c4d38efdd25cdaba979c034d6b80892e6e90a7d9719a7abe95f6b69c69eadcd7d9df19a769ff26334ee2e56c68cae5c12373b4227c74ee892685096e9a12403bdb4d4b8889dd6bed402deaa075af0234b6ce6e6af45c51e3826b5be849737d09ad707db99de626b5be369c780c92e715d3bad7dae13b575ed35c6a026a10d3e6253573c4675674d65357001322d7192d9b3949734d61786b68c965131a7ab424eb3], [0x882e90c195aba6b0ba34d65248faa32b1e30097c6bb1258da128038038e6d09400da12804d637def8d258e2bb2530096ae9accd0e20ba45b437de92cd3c5a126b4c835c29aca18da128033036ae9ac470e39b574d637c692c73891c94321ec684a008f8da11492626748c94c1c639b425b434964ec8fca20a2421e546e81c87a5f1a4b21e3882e90dc95f1a4b0ba37dec54bf457dada32a9882d38dc95abb254d6364abed718d92afb32a98e6d092f0da134250035e092c988de426b49637a2ec92f0df63425003684a002e8df1a4b23e38cad89358df1a4b35437a2d09400df7a4b28527deec9258e32bec4903684a00c10df7a4b32b1882f44cd9620a0721e9748b68cdc5e8b4229e68ca9ad120df1a4b05c3684a01258e39b4245a5764978d3a632bab4d636ae9acc00df1a4b27837949ad258e38b5c4d63684c95400ddd3424b834bc69c98c51220721f18ae9dcdca6313574d637c692d208dabb1e4d63684c19400d3b9b928696849d4988df1a4b13037c6c55258da124b2383684c41358da1280490388cd31358df43574d63684a01400df7afb496369c9dcdcc632a6b43697c692c988e03a4b28526ae9ac8f8e20ada336989ad09400ddab4250035b489087c632b5c4d635c6b68cac5abb424d6380ef8d258e2bb4229e68e2d5d358daba6b3363748b68d3c5aba6b48234d652c87a9f1a4b35a36ae9ac5e863eb574d637c692d258df434250038aed393b8e2bb574d637c692c738ddcb574d637ded09400e32b5b4d638faf8d258e253424ea3882c94c1a639b4234e56ae9ad358dabb574d63684a005e862bb4e37257a2d09428daba6b49636ae9ac498da12800103888fbd258e39b425e836849ad258e3db4250038e6d09420d92a6b47496989ac8f8dd93a434e56ae9ac7389f1a4b3063882b68caa5aba6b21e34964c496c9aba6b3063802f8d258e20ba44825684c11400de8a4b28527c6c19258df1a4b2fc38e6d093b8df1a4b28635c66548fc51513121f4748b68cac51ba2421e564a9aca6a9f43e34963882b68dca632ba44d637c692c1a0e39be349637d2d5d358df7a4b31f1684c79258e39b4237258ca9acdca632a6b29aa7fef8d258e26b574d63882e90d3962bbd13305684a00c18e2bb4250037c692c8d0e20ba433657c6f8d258dd925e26236ae9acde8df4b4250038e6d08d215f7a4b46e38e6d08e095f1bd14963684a00a70da131c4963882b68c1a603c004963684a007389d91a726256ae9acd90daba6b17a38e6fa5240df7b574d6374e92c8f8df1a4b33638cad09400df63574d63800fbd258da128023c37c692c5e8df1b254963684a00310e26be349635ecbc1258da128011e37c69ad258ddeb425003684a00470dd223721e56ae9ac980e32a6b32a9882e90d915a926b49634964fc87c9f1a4b06e381cfbd258d3594325aa8dad5d358daba6b490342847c87e16d23721e9684c8d400e20a7737298f2d09400d92a4b28528cad5d358df7a4b43118aee90d915a71b9286574881c87c5a128048238f6d09428e003d149638e6d09428e2bb5c4d637a2d091d15a128025c37c6d09258e2bb4250a38e6d08a799e8ada3371684a00d90de6b574d63602b85358e39b4232a564a92d17c5a727728638ae9aca6a9e53425003748b68c1c5f1a4b17a17c6ef5258e3134250036ae9ac170d1ba2440e36ae9ac2f0e32a6b34e9, 0x17d99523e96849ac8d0e20ada36496849ed258df7a4b36317f2f8d258df1a4b49038c4f8d258e20bef49637a2c94bf45d22da36518e6d09458e32a6b32496845388799abafe4d63684a00a18da128005c37a2978d3c5d6ba749637f0fbd258d35a4b25c36ae9ac988da125c28638ae9ad0ea5a128017a37a2d5d358e20ada48298f6d08a799f4be349638fad09400ddeb574d635f6b8c8f8da12801ce38aeb68d925f1a4b36437a292d0ec5abb064d637deba5258df7a4b37318cab7d358e32be34963684c55358daba6b23837c692c9f8df63e349635f6b8cca95e8bb234e5684a00988daba6b2963684a00878da128033638e29aca6aa32a6b37e97c692c470e39bca33058aef8d258e39b4240e3748978d3c5aba6b1ce3748b6920c5aba6b01c364ab8ccac632ae34d636b8c95358e00325496368450c9d99aba6b28638c4fbd240e39b424b438cad39358e2bb4245e5]]
  | 5 => [[0x2cf8c353], [0x2d4f850f0f4f7b60024f378f212f010f08e0770f516940ef8aef7faf384f1c4f060f176f108f6f6f236f220f7c645d8f892f3d4f89af500f7641110f5e8f1caf47cf4b0f8b8f16cf8b6f18ec44857eef21cf8eef440f73854c4f46e16f2519ef65cf34ef2acf052f3acf3f2f6f8f8ccf28ef034f594f326f4eef260f6c8f28af52cf1ccf1a2f2e4f10cf4aaf32ad324c004f84af13cf3fe97e0f89ef75af09cf1d0f05af8f0f7acf6ae5604f296f3c0c062f130f1a4f1def174c25cf88206a2f872f11a9050f640f0d0f3e2f7c6f802f5a491d8f2a6f112f382c35af87e011af048f6b8f1a8f8c6f806f882f434f65c52aef580f300f0a2f7bef496f31af36cf3c6f5c650aef4eea03cf0b85418f1aef67af620f490f62af2c8f3baf5f6026cf0ee58def1c8f3b8f43e50b455a6f5d4f5be512a91baf3f6f27af8a6f186f15cf11cf480f64ef8f6f11ef538f858054cf21af094f52a96faf3f8f21ef2d8f5c251ecf764f13af292f46ef45af3f0f4b89638f26ef078f8d8f7d4f170f0c0f804f602f8fef3f4f3daf0faf0e8f074f56658cef17ac354f064f666f0a4f0baf43cf7a4f1e0f80af618f10af8c8f072f59cf7c4f864f5f6f32af626f19af1d2f1fc0232f334f8aaf37ef6b857c2f4a697486776f30cf2ccf79cf3d2f5daf51af30ef4a6f3fef7fef1d6f5fef34ec0a0f04af2eaf720f714f258f4f4f8d0f22ef180f, 0x80f0a8f044f550f424f370f306f8bcf2c2f876f2caf7a0f556f8ecf166c4e0913ef79ef3faf070f630f68e51e4f584f7bcf7e8f44e0402f426f62ef674f1cee7a6f0cef472f278f41854487086f8eaf8e0f28cf24cf2b4f4c6f718f432f4bca092507cf8acf1bef6c451b6f1169436f158f104f380f01cf1e2f5f4f49cf866f18af8a4f5f61358f796f4f6f1f2f11c9054f676f8f8f764081cf06af0a6516ef724f642f450f834f5089660f578f3eaf1bcf5f6360ef084f8d2f7e4f29af38af6b6536ef0daf02af018f8e8f2b2f032f45ac0560312f7def646f7f6f60cf4e8f10ef4b4917ef6eef2e2f484f454f7fcf520934ed224088cf136f8daf4d49058f622f006f500960af7045348f79af608f8822458f2faf878f192f302f7f00462f76cf4bcf4fef862f726f2aaf1fcf574f3b6f238f612f1b2f0e8000cf252f204f030f448f0d8f394c404f58af242f0bef156f2fcf74855c6846cf8baf478f284e54af74e07ccf49af0ccf14ef188f27cf2cef166f2f6f2e8f194f59ef23af430f3a8c29cf274f05c05b49268f5ecf318f09ef7c0f03a0430c2ecf3def04ef632f734f83e040eb8b0f4aef84a069d768ef7b4f448654ef794f7c600e2f24af076f0dcf036f20cf576f304f03af69c50bc576af5b4b1f0f644f038f0eaf2309182f0e4f114f648f858f08af17af016f2f4f2f8f364f5449786f00ef046f46e20d6f, 0x784f7b6f59af650f77cf730f10897dcf366f0eef09af508f33ef2bef1109234f852f07ef728f7daf5baf066f14af8fcf092f25ef168f6f2f0f8f8f4f8a8f34cf096f436c8e6f7a2f600f33cf5389406f2b0f8a2f71400acf57408c0f50a94049308f2dcf8faf874f344f120f4fe925af0ecf43af0b0f214f792f6af763ef5014246f2c4f476f3c0f150f22af1fef0ae532ac19cf2baf738f3d0f154f87c0896f03ef8caf362f790f8a0f48ef64cf520f05cf688f712f040f69cf2e6f42af870f102f100f588f14650b2f7445744f174f142f70cf57cf7d2f5c6f71af02cf4e0f39cf4220222f466f4e4f3e0f1f8f6ac55d205b4a266f210f3a8f256f64af12af762f5e4f7f8f7d8f5a8f3739002f22a5140f31ef288f696f8b2f24ef144f8e2f5d2f230f2f0f02ef4d8f89cf38ef7565184f32b20b4f1f291cef0b8f16ec6c4f08ef39ef572f1c0f722f61ef3eef636f7a8f026f80cf320f5ac9812f838f6e6504cf152f336f778f72af888f544f342f284f29ae05a082cf0fcf748f41ef77af2daf098f43ef12ef1b0f422f6d4f18cf83003d6f128f1dcf6d8f7b8f6cef0fef7f2f88215e894eaf40ea088f800f2e0f178f0b6f4d4f26af7baf5acf5c6673cf2c0f116f492f14c945ef86cf0f0f47ef6acf0a6f106f44ef1d4f780f2d0f30af06ef14cf662f3b2f276f29ee586f18ef3e6f46e04c8f63cf6fef540f4b4f20af, 0x1daf8d4f290f8f2f134f330f7c6301ef14005bef55697d6f396f526f798f8dcf0bcf3c8f832f0d4f23ef0f6f198f5c2f1c6f5018560f900f788f532f00af704f0c0572cf1e8f244f368f34f56e6f5e0011e9482f516f86af0ba537ec248f62cf756f29ef4b8f146f148f5fcf23cf160f362c126f888076ef020f39af122f240f87cf08cf57af286f0c8f322f164f488f628f47af2f2f0caf15ef186c2eef474f226f6dcf272f52ef06cf132f372c356f78ef224f5b4f2def58ef8d6f33af548f73af022f7f4f2b8f772f830f698f8c2f2fef4ee96a4f494f090f06e0270f3b4f17cf4ea95e0f6daf254f3d8f56cf012f78cf566f01af4c2f6e0f0c6f082f332f324f1c2f1eaf678f2a0f31ec050081c03a2f84ef3b0f118f12290f2f008f6fcf6ce52c6f672f4bc9592f16af218f0aaf7b0f826f372d042f2d6f172f868f52af8b4f3ecf67ef680f0f0905ef316f63af87ef200f452f3e8f6ae8162f808f582f8e4f262f4d6f72ef5a4f748766ef6aef61af4ef8028f7644346f3ccf894f1b4f61cf5d6f78af624f1f850def692f86ef774f348c6d8550af682f826074ef22cf80ef382f40e9264f196f180c846f0c4f67cf394f250f898f80007f0f498f6b6f674066af0e0f634f37af5def42cf85ef190f20ef7cef0e6f420f04a0456f068f228f58cf8c4f372f1a0f400f15af3e4f69c6338f294f71cf2d2f606f07af428f, 0x69850d2f014f056f820f138f2bcf83ef216f590f752f4bd4716f27ef684f8bef], [0x60c657aaac4eed6d26bda8021fb7484c6eed5a75e369bfeb2e483760c6e7a86ca1f626a84da6b46ef8eee92e77028f5e8995ea2a34fd8c4d0ae89073dd359497b4246ef32a47f2fbd03ed4ba4bdb2554fb866d1eec19646d12224bafb364f8ae53fc69cbff6269437bb24bcb77aa036a2c046e3126b7c464d6f796d3aea54126d12207dafe325d8cac71f1952f6d1202e3c46286f8cad3aedb0175df185d7a7f483b64abdb7105e8bd1ca377a6b296f4d697b6b688fecd385dea5e2637640c1b665417358d183dae34837764174ec7125ed40182dc410ba77142f5f104853d2090febe349738ae8e5ed6d835d3ba49da7705cb77ab6b66e4a1f5a705dbb4245f779492eef44d3d61f99b7b42292f5a466f6b6887ed209a7ebd1497776469daef4ea74d38c3eaf623fb80e50bcb2135ee03a64dbd15c7743647fafbd326e32a6b7c07800f77a657a9dd20ede8a377b1e483d8a4d09e85087f5ab943bbd11bf77c6d09ef8c1a3d4014edc7934fd7ded3ae9dcdcf540143dbad23578ae9aded3935dd2f143d9a7089d684bedeef49dddf188e7a11306f78cd0aea0125ed0a195ebe360cf52a0b96e908fddd20e7b9a7347d4bc47f718935add205dbc4174875e84c76e91a15da0a07db064efb7c49ab68e487f62ba07db0640fb5ec92f70f8c1be2211a7ae128778dab8eefa9a75e2ba775afb496f5f61d1f1957dbd0ea07dc656c578af105eeac8e5da702e3bd168577c66c9e89103ccd3931bb4e493789a69faed4a1bdf19437a07287b7480bae9dc5ee583280dc4103af882c19efbddd5ca1821f441286f5c650eef18bf5e209317c57501b89ad5ee92098ddf4a6bda2f449746e43fab69676e2082e7c2511cf32a23b2ffd2f6deebb27bbd40fb5662f6a6e4cdf57625edc57372d4d66e7a92d0c75a0afb7ba4497769c6e6b104dcbd298bdca3717ad40e43fa92c9fcde8a85db2557bb764175e8dd121e2bb5cbc41749730050de9dc2ecdf63427a37448f33050def45dd5da12807c2c482f44887aec8125eddea377a071cfb7c64f1eee9a15d2591fdba221f78cb105eb68cae62bb4e7b4e1cf75b44b76d393bce2bafb7b4249775c6656ae909ddd35a07da80381b83450ded1c5ed5e8bb2bbff5c7777a8bef1957b6cd91a7eb57263789aec9efb53becd91437a5e34fb8e6188e81ccded92afbdbd15b5b5b439f51cd406d7199bbc4423ef, 0x4480baf0a0453d3b88edae332b77de92e6ffd7dbc738bde2da05db4964ff6978c1ed7d8bd6b1a497b684a00669c98f58a99beba421977dee92f1cd71dd1b91f7c7350bb7909adf1cd6d6dd5943ba7017bb4ee6077195d93d2f131dbd176b7674c95eb6969ee20a417c65126b6aed0af150d93d8f183eb4e26375ecb8eeb8c175d8b25edc6537fd40e39f4a00172dd21b2bc414d6f68481f6c69836e3db427c616ad75d847f6ec8989d0385d9afb5c6f40e29b6d5c475d5105d9b42235763c66fab68caeda71433b4e33777c4f6dec0535ad121b2ba0705db89ad5aed38a1dd832dadb25285e8f2707a6f487f5d6a4bdbe317ad4ee0bb69ad25ee26be37bb24bdb69c50deef5125d6d08eda371cee678beded38474de79b9ea0717bb7c639dee916d6df19837bb205cf87c421ec6cd3f5f4a4bda6b437d5b4b6b6a0120ee26adada0705cb5b41e371cdabdd8fa77dbef6fd740e43f3194d3f51d10feb4e36578e29af71042ebd6d183dc33172f77a9df67fccded4011edb966857336147a978172dd21a7aafb21ef64a9936d08caf53ba77dc736a578a46c9efe5f1be251437b315c778829d1ee9087dd3b9b9cc79764f63c6cbae88865dd22da9a2423f777a69fa4c426f9f1b257ae332bd6d80b8f1853feda12803a37262f4bc66f669c2ed555a41daec5c7740e23b6c84dcf5a711fbbc732bd57a2c369dca1ad92ae39b4e17b55001766904bcf971983bbbd16b757aacef039f7bdc109dbbff764f44843ead38ccdd5105ddc334e1b6fc4c6ed5d358e313427bd1475d6ae2f6ef6d20be26b4eba413f3d8ae69fa81c98ed92a97dbb24bcf5f647f6d5c985dda9a4ec735f6f69c906ed088e3e2a44d7c3f262f800c95f1953bed830b0db2546ef7fefe1e92d17dd92a14dc7d501b6848b7b09440bdd391f7b1a2fdb79460fa39c173a26a5edbd169d764abb371cde43df125edb5737b789aa03718503ee2ba7fdb4165d75ac6cb6d1c5edcb184df35711d38aee92eba525be03a4b9be3336f79c66ee654c1f52592eba3713af8ae601ee9024dde89a7ba24263743046bac94dcf4ca8bde9dc21fd6ae906f105d23d1b99b7a2a21fd682b8eeb8c8fcda926b7b3a60cf44881eebed71ddf6248bba421576ae60ef105a5bcf6081e90f1f3b764c95f01d25ededbbd7c41292f43a43fb15ddabe2bb4e3995287d34e66fad092d6d1692eec417def, 0x7a2c42ef45d25d35a24bb8d26378f297b6b8c73d9a11437c1a4d6f8cae92ebed719e2bc4d7ba405c77a2eb6f196143ddd131bc73509b4726e7b1cd3bee26ba4bba236577a2dfaf1956d6d2f0bdc9b9263d882431efbd6d6df624bda6b325d336657ab5887edefa377aba17af77a58fd1cdd6de3ca84d8ff1fcf64a8ebad09405d16943eb9c21171ce23b466c87f5e89b9ebe305cf4bc17668e8d93d82280da6b43bb73860ef1ccdcf4dc85debe246ef38043faf4503ed6d24bda5e4bdb7c6905eaf55d3cea044e9b9373d5c639ee69c73f18091cd90f1a1d4d64b9ed09404dd2183bc65373d7a25faf01d25dd5391fda4b27f775a92e6ed498dd90180dbe9491b40e60f71ce20bdab99bbb4205575e84bb6174171e38b1c7b4146ef7c692d6db0125cca991eada05cb4826e7aa70226d120e7b32560db5f62f5f104d93da0995ebca483d4ee2f7692c96ee26afb7c4d395d83e1c5eb68d96cfc8d0e97e23fb7f0ef5e81c5ee620adadafb4d6f4962d6eb8cc6ddf7a80db424f6f72c92ef150cc3cd382eec626af77de657affcd3f6209b9eba448378aeb6b71351d3de7342bb420b2f49681f6bd0a1ee269c1eb3e46ef79050dee90cddd9026bd943277e8822f5abec98be269b9eb424efb3f26cbaf8c9fbd3b9b9dafb32af7a250bc65473f22ba77dbe306ef5f6657ac95406d7f1437bff32bd5009af69dca1bdf78989bb96af7428845edcd835d2f1b2d9b9333d372303a6b487f5aba6b9af0262f794663b128973cca995ec4d521b684a016e90d3dd7b2f07c7b6a576f223a7104c1bdf4b06da771cfa72c37ef1047fbe2944d79b9303d40e47f6bec2ebda924bb97e21fd5903676e90475e2534ebc4d6b774bc69f2e88a1ddb381abbb2306f748c96e9accaf5de9b9eafb336f448176e86098f62da07dbcd6af78cb129effcd8f5f7a4bbae35bb746e6c9e8905ede221317c6532bd64abed70e471bcf610feb4e1cf64d646b6b6873ed2598fec4d46ef6844c6efe1833de8b52ba243fb76c403aed5d25dd6d10cdbca4d6f8c4a036d5920dda71b9bb254efb4ee43f69aca5eda708ebbb21cef17a176ac057dbd71a4bbbb2088f3064b76b8d35dcd390feb255f6f37239f8c80c1ee3eb57bb9c21f7482892e81c4eedd908e7c4d172f5f639deec8cdbd4801adab317b78f6a176c0535ed152277a77497b43a60f69dc0d6e36995ea80501b, 0x5ec92e686c8e74dc983ec634bdb4bc39f71eda11d3580e5ae323f77d2d5ef15e0d3d92980dc79501b8da9df719535ecd91497be30ba77744baf134caf592995dbb260cf37250daec8a1bd7b24bbb23501b69c182e66c5addd91a7ec73834f6b8c96f001e8bd9297edae30e378f2d3ae4c496fa2bbb27c4d4ffb7644c5e8905ed4ca88eeba428774bc9076d39a15d92ae3bc6144977a2922ea0073ed2f05ddc4111cb34e23ba66098dd1ba075bd13377764d09eb68caf6313423c656af777ae5aefbcd8f62326bdbef5c7787e429ebf96fdcd910fea27336f71a2d6e8e4a1bdd2257bc5788cf4bc0bb6dcc38de2bae3bbef34fd7142f5a56810fa30a77dbce77b769c0baef38cc5d7188e9c576af760cbedf13571dd7f11fdc65501b60c6c7aec9d93d1ba1e7a2a3ffb858275ed5d35bcdc9437a77287b64a69fa6e417352f17fdad2215b8d3105ede440dde324bba1423fb48281f6ec8472d25931bbe377af76447df0cca1bd2e143dbef54fb8d4b8eed3992ddd21a7ea77307b4d647f66e487f4878fcba77337b7c639dced5d93e39995ea6b286f64a81f70602e9de8bb27bb54b5b748c1ae920a1bde8b6ebc574bdb7d8a036a005ee5d90bd69b2049d88243de53887f91ba017b0123fb8e29ef692c8e6c5e88ecc41210f6ae6cae43c557969131dafe5f6f8f26e7a8a9125dd6ba77ae30bb76dc4c6ef45765e2bb427bbd539b46e0b9ef2125ddd926b7a770bbb34e69faf8d25bcdc8e7eafb322f7c66a9f184dcf58d26bdbf87def8dad6eec0535bdf624b9a37286f32a47fb1b5abdd1ba24badf4d7746e43debec8fbcbf131bc7b6857684c71f1cca7f90a20cbada287b4d609f6b8c5ede0d0597c4a684744860ef094472de51b2eb4263cf50023f6e905edd64183dae3263779c92eed5c175d6910fdc4d292f6ae66aed4898dd3211fdbf774978aec71f195f1bd400bddbef764f40e6cb715135be36afb7ba45b578ae921efbd125dd92417b424c978da6e7a65487f632a07db574d777c6f45e8dc73be39ba4b9431c6f64ac076f45155cdc82eec7334fd3726cbaef57dbd25a24bada17bb6ae9aced5dabdddea6adb104d7b23e3676fb1dedde319bbafb32ad46e81f6ef571dd6b10cdb0623fb64a92f6b8c171d1799bba3a46ef80ef8def452f5d2f0e7d3e9307b3062c36a00046e25275db570bd78e6892e9dc48ed1210febef285e, 0x8bc892ed5d35edf19317a5e21fb4bc9636ee92e6d2f044d99b26378ca9ad6af48fed7d91f5a07403b4046cb6b68cdee1ca6b7c415b4f8e2d5ef15d125d35a3a7a3717af6846e7b1cd1bbce7824eafb286f7dec42f1954becca85de9a711d97b6f45f105debe2326b5b4e497744823ae890474de8a1dec5332bd7a2ec8e2382ecde33bdbbb217af5001776b8d71dd2f24bdb25307b8cad72ec19125e39b42399821fd8ae73fb10473ba39bb27be321ef7a2662ebecc1bdf4a4bbbd1501b60c6ffaf8d25ed4011fda0721fb684bd36d38c1de3da80dbd640fb62a907a60c40f53b8e7dbec7c6f684c42f1193bee25342ba80365b77a707aec8d1bdab8e7bc794efb8a8d09ec18d3f59294df35764b78dad3af15cdcbda70bdbbb21cee7644c6f14935be39b42bbec68578e6a2f710620bdc6a53dc4123ef5f6239f19571de208bd7aba17ad44828ef15ca6fa1cb427979155e5c66caed38dcf5e519bebef5f6f7c69adec18b6f97d8717bd177b75b4423669c5ef592995ca4b373d34e47faffdf1be2ba1deb4229cf46e8dde69c73f639c467c577c6f6ae2f6ac5535ecca931ebef497b87c47df15d3bbcdc81aea4b32bd6842e5e81cfeedbc88ebada483b7c481f65b43e793594b5b0643bb2924c7cfa535be38a6b5c57373d89a892ee35c53e0c05d7bef603b5f6bedeee9a11d7191fdb5723f74d669fa50c96f935a64db42349d88266df1361cbd25855db2e64b7748e92e238172df1be37c736dd747280b652c87f9bf086bbbd74976ae03ae69ca1f6291807a2421f746e281eef4d8f62ba2fea3711cf7489aee97898cda7277bc4d2b5e77a4c6ef44d3f53b91fda774d7b54e1576a0073ea26b67ba80263b4f647f68dcc1be26a07dbd13b9d49621ae654c6f5a1224bc6529be7c4892e81c2eec878fe7a5e12bb4962c36d3887dda0a24bc716b974ea4c76ce920be2bafe7bb221ef88c471f1a56d6e1f10f7c77882f5f6b75f10525bd718bdabef373d50023b710473be20b257a4132bd7d8d08eb58a1ed0a207da6b25bb5b42f72f8d259d97306ba6b114f882d09e978476da123a7c44496f8e6d3aed5d35ae269bfeb9633778c49af71c535be312487b57297780ec42e92c9ddc5e82e6bec497781c0d1ebec472da10b5b9950e3d6aec1aef88d3f58e1437ada215b7c66b5ec192f6d928d9db255fdb77aec9f06028bd8a9b2ea9505db, 0x1005f1bcfc983ebe2764f8aea176e907fdcdc8bdec7b29fe3c01c7ad08a75d7da417b1e301d7a253fca5c13ec8f87cf341674f4e02f731cd2f6e2334cb9951cfd44866eef8d25ddd6a5edbab23f78ae8ddef453bed1ba077a6b161b6844eeeec925be1c9b27b4e60d7684538ec9535ee2b995eb255c7b5c623aedf9a15cdc85dac737c6f7a29ab6fbdf1bd92a5edc57850f29247fcc4098ddab82e3c57894f7c62f5eef5abdda1280dc5534fd4d62e5ee9073da2b9987b82483749047f6fbdabddd91a77c656b777de97b71353bedab85dbb6e055760c8dde830c1de3144d7afb05cf39e43fae90474c9f90ff1f9337d6ae43eef452f4e2bc337be323ef43e6caeb8c87dd92adada5e17bb63c92f669cc1f57b11adb152fdd43047fb0a0a1bd40183d9a7263527647fd1c4a6fa003ef7c4d882f8c2d3ae9ed25ed6d05dd8e70bb65000bb6fb0cddda1315ba2413b77a2e36efa535ae209b96c6544978c28ddf129a13d3b9b2dc576ad74960d268b498f4ca91fdafb1cee7a2d5eeff17dbddea84d99505dd7482f6afa5f1bd12143bc28684f8ae38ded308fdd6d05d9bb24b0f39406ba9a920ed6d131db424d6f748422efbd3becd9195eb6e497737223b2f452f6e32a3779311bf746e43dac1971dcc010feb2532bd7569aef1f5f1bd25a377c7b790f77ad3aee91cedd8312ddb4234fd69c9df68e50fdda125edc1377af62a60fab8c3bdd92a24bc654f7b37223baee9d93df4a4b9c73383d4968776d5c73da311b27b425b5b49669faef52f6d7d85d398321fd40e81f6c0570dd831e0eaec5d2f30047f6fdd6d6d20a3778ff1f977c62396bf93beda10083a2f21fd4a62f76c9517f592a7bda370ba7826111e978d3f60fb067b9c23f7882b696b2125ecca8c7e9b2172f30647f6f8d258d76131ba3711cb37247fad39a75de8a24bb425c771fe3e76ec8d93dfd3b27b4e035776411dea5c8feccd93bbc73684f34e0b9b15de43d53a6bdbd15f6f87e43decd5125e39a07daa20a3b75a4c6eb687fed1b85d7b253d9d882239e6542ed592a48da80337b4544c6eeb525de2b9b27bba684f7de8ddf15da75d3b931daec31fd], [0x8ca9ac73ae2098321ed8cb13535ae39bbd68475ec92c98cdf7be349678cb15d35ade8bbd4bd38cac9535adf7a4b05d38e719535ae2bbd168478ae6c887b5f7a4b06937a2ef4d3d6209b921ed36450c87b62b9b205cd8e6d09404de8b2530798e6d09259e2bbd1337589ad38dcd62bbd1364d60c6548fe638c654d6b1ce2f4173232c654d6b8e6ed5a11ddea5e34f98e2c9535ae32a6b238b7de92c8d4df7a6b49738cabf935ae39b4236478ca9ac8fae32a6b336b8af1353bade899b21f58e6d08c19e39b4205c71ce2f42ed1de9310bb68af134dcb639b4211c77d2d0935ae32b574d6b4828dc87b632a6b05cb89b104dcb592b065c737dec9525ce39c4d68478ca9acc1ae39b4250078ca9ac072e39b4268478e6d087399832da32b96849ad259c4705d05c37dec5525ce39b4249077dec1925cde8a6b49738e7195a11df7a4b27f38e6d08989e32b574d678ca9ad35ad2593123f38fb19535adf7a4b48338e6d085e95f7a4b05c38f715da11e32bef49738c49ad25ae32a6b262b7a2c94cdd58311f11da8f71cda11e32b574d7380efbd25ce39b42380774860c87d592b0632b98ca9ac49ae32a6b11cb8e6d08a19da124b23f37a2d09359d20a3744875b460c87e636c654d6b5b466c87e639bd16847684c9535ae32a6b482b894d08989de899b0bb58cad5d358d832fb32ad7deef525cde8bbd76477de92c8fce26b4e286777aec8d3b620ada21eb7d8d09359e32a6b490b4d650c8fae2bb25307977aec8989e39b4264a78e6fbda11de8a4b23f38e6d088f9d92b065f6b7de92c98cd80a6b286b7def8d258e26a77286b60cb8c8fce3ec7368477defbd25cddebb24bcb7d89ad25ce32b424d6b8e6d08470e20ba421e764a9aca1adf7a4b35b37de92cd94df7a4b21f37de92d25ce39b4229c777a97898cddd342286768492ca19df7b42497374869c87d5ffbef49737de92d244d6d24121f977ae90d3d47388e0bb28ca9aca5ae32a6b364b8ae9ac8fae39b420c477de92c4c4d20a0721f98e6d09209da126b23eb6849ad25cdf7a4b1cf38fafbd25cd20a2421f58e6fbd25ce32bbd4d6b7de92c5ecdd6a4b23f37de92c2ece39b4217a789afbd25ce2bb4249676849ad25ae32a6b300b8ca9acdeae03bd1497360cb8ccad632a6b0ba37de92ccdce3dbd168478c4fbd25ce3cc7368477de92c5ec6269b9286d1ce1741719f7aec497389ad393bce39b4221e71ce2f44760cd93121f58cac7935ad6d19521f98e6d08041e2694305ce7a2c9525cd9298311d97a2d08a19e32a6b17a98e6d09402e2bb25364d30647c87e639be968478e6d08739e209b221ed74890487d638c574d6b89a9dcdce632a6b286b8e715da11dd219b21f58e6d09831c5e88e05c97de92c474dd22da21f364a60c87e620a4121ed7de92cc1cdf4b42497364a92c98ce32bd14d6b8af135a71d35a4b286b8c4d09259d2090f17bc60cbec8fada126b49638e6d08cd9df7bd149738e6d082e9d35a4b26337de92c73ca2bb4226277def8d25cda126b26277de92ca1ce32a6b1cea77a69c98d5a132549738ae9ad25ae2099b21ed1ce2381729f7be3496b7de92cbf4c5e88e0bb15b46c887e62bb254d6b8ca9ad25ae32bec4d6b8e6d08971e39bca684760cbed719e03b2549738ca9ac2eae39b4233078ca9ac5ead20a2440f317a1741715a114326278cafbd35ae32b064d6b, 0x8e71cda11e39b424d677486c887d639b4250038ca9ac87ae2326b23eb8aefbd25cd20a3740eb]]
  | 6 => [[0x2cf8c353], [0xbb65ecf6ae5330f49735b498af1238f8a8f76af8caf8cb33d8f64b30cef09af042f472f210f36515fcf0aaf5c65234f602f1b2f21f1194f0baf307340e9894f5f6f474f4ee9482f7a363b8f454f7d8f21ef1cee29cf11cf002f640f05da32ac5b4f497672cf10cf8c4f25cf8f2f4d7a0c4f45ef790f2b4f496f4831172f028f262f25af0ba5490f3371154f39ef60d38cba64b168567c6f448f2870774f2f2f88208daf7d2f6aef23f3300f0e2f7a2f69cf26302daf77af8faf292f01cf17ac4c8f364f18af126f682f17af1def1fef306f372c748f7fef2fcf380f8e2f79cf1a0f50091bef7df6620f850f130f685a17b1500f05c0276f365a75af872f6a4f60cf27ef4485114f46ef05cf71af11d334ec8e7a882f634f214f8afa068f63cf76402636088f6dcf3f2f7def8aef52ef34ef287a286f8e76748523ef428f0b2f0f8f7df389af078f5c6f218f77b07c4f4d6f048f89b035af21f023f00a2f80ef638f43af372f1cef336f60d033765d8f4d7313af900f4f6f4830684f77b654ef04ef102f7c608f6f794f307132af590f866f4eef034f57af37af46e04bcf16af4bc988cf8e6f2c6f40ef78cf62af1cf06fcf834f11c969c51d6f182f764f7a318c2f1c6f1eaf160f010f8a4f5f60296f89ba054f64af], [0x7de92e6d08a1fc2e851fc4d4eff336663f19473f8a191cf88e05df17a0b9efbdf1bd2090ff99b11db77a43fe43c73f9a105dfb424d6f4d69aff15c5ef4738dffbd117bd49647f658c2edc7388efc5721ff4d60bbed0592fc8f91afc4d64bf7a2907e23840ec4705d9bd17a3f0ba176e7702efe32a6bdc738cbf8e6d08ef89defcc191fdbbd23ff23e39ff19473fe26983fc3317bd286433eef4d97c5e8b0e93121ff3642f7af38d97e1408efc4d05cf89aef7e6c8c07cd902efa4b0bb70ba0bae5e45ef4c185dbbef287f7de907e2f417762bbd1fc5789af8cb197e92cd97e32a4bfc73307f4d692ff15cd93e3291ff9cf05df05c085f13535fd258e7f02e05cf7a20bbed0925fe26beffc4623ff21e2f7afbc5ef5358e7f11f1cfe36439fcc1873fa32b57b85d09b777a113f10487fd8f26bfa6b0bb760c1c7ed0873fe39b427c4d17bf80efbfed0520fd208bdfbd117bf33643ff15df7fd83306fc7b8aff2622f7aed5a17d9288edb7e11db17a2d7b134cdfe2bb52fbd177bf64a4b7ec9525fde888efc6d89bf8a866fe50c2efe32beff8e705de05c0abec945ef5640e7fc6189bf4960bbeef5a17de89b2fb4260df3362f7a6c8477cd90c1fc73263f33643fafbddefe329bdf9b2219f17a23ba39c73fd25a41fa410bbf7a2c1bf1cc8ffcc18e7fb25365f9002f7e90503eddd143fb2505df89a06bed08cc7d1d143f99b307f7de39fc9042ede39c57fc5717bf496263e90520fe2b88ef82e049f7a239fd1342edda102e7b4217bf30623b692c87fc5e85de9b2337f89ad3ae4c498fd7f26bfbd1497f33623bf15c73fe30a41fc391cff1ce176cd08317d20a24b99b17bf6844c7e905127dc68bdebef27ff496923e47c477c738e7f44d497f8ca66feb2073f9a112efc6505df64ac43e92c98dd208bde9b2286f8e6d0be50c476d8311ffc570bb760c4c7efbc1a7c9888edb064d7f36443fec18cafd928e7f1b205cf87239fd15c98fe3280efc8011df48243fd194c1fe4005df99b18bf42860fe39c17389892efc801cff2862f7e2f42efdde943fa4b17bf8e6c1bf15e26fda1241f91f11db7a2993e904476d83183fbad23ff1ce2f7e60c87f63290ff88e11df60c66fe92c8ffe2ba6bfc52307f8e6907f15d25fc4708af8bd16bf8e639fe2382edc5e8b9ebca685f8ca6cbe8748ffdb702e782e054f64a60fac18d97ccd99bfbd111db, 0x4d62f7a90473fd92a41fc718aff7a2ef6efbc2efd2597efbef4d7f17a176f195837e2ba7bf8e71c7e0ba166e6c8a1fdf7b25fc654d6f8ae9ade17428dc47086fb0611df8e6f47f15c2efca192efc8017bd3065fbf1962bfe3cc73fc6564bf77a60ff0a0476e3282e7c4d11df1ce23b64c4173c4707cdc7d8e7f8ca176e60c73f992b06dbd1079f17a2e7ec94c1fe268e7fb4211df7de6cbe92c8d7df7a4bf931215f05c09fe43c73fc17001fa4b0bbf89a6cbe5b4476df7b06fbd1337d8e66cbf15d92fd6d10ffb42307f17a23b266c2efca182efc4d287f36439ff01d92fc5e82efb42365f8caef7f15c73f93599bfa411cfe8ae053e9ac477e2090f785d0abf6844c6e238176cd9198fbbd337f77aef7e2f400f55e8bde85d0ab74726cbedb8177cad02e7b0621ff11c21b692c173e32c4df98321ff36460fe0b813bde8bc8fb06483f8c492fe47c8ffd7b131f9630bbf8c315fe43c857df7be3fb2564bf60cb8ee5b4477d4b82e788e115b60c2f7a904173d35980f9dc0bb78ca177f1cd25fe399c0f85d0bbf8e71cfe568177d92943f8e71b3e05c087e4c45efe2688ed8e71bfe21e0bbe92c477da105db9310bbf6fc23be9051bfe4005dbc654d7f74843ee92ccdfc2e801f93123ff3062f7ec9535ede885df91f239f7a266fed08a1bd5385dbbd1337762a92fe39c687da119bfb0632bd8ca52fe174171d80943fc7989bf834176eef473f873801f26b17bf3d823b6d0873f925983fc5760df2862f7a9ad25eda110ff88e05cb64ac73f195abfcd910feb2511df7ded0be174173c738bdebef263f1ce2f791945ef52088efc4d287e8aed0bec942efc738bdf18305cf4820bbe66c8ffda108edc65483f64a60f6ef4d3f5e882e7bd1307f77aec9e43c5efca18ebfbbd11db23e176e60c477d20943f9b211db05c005e9aca1bdf626bfada21fb7a24eff1cca1fdffbbdf90f0bbf8f71cff135837d8305dfbd1685f89a39fc0b8123d901b2f90f21ff77a23bf13498fe38b25fbbd497f4d650fe2f45efcd905db8e7003f11c1f3ec945efd2089dfbd1685777a4c7c9ac173df7bd1f8e71c7f7c4907e7e473f9832e3fc7d7dff57a2f7ebb125fdf4b42f983195f8e6a03f1cc73fa2bb4279431cfe60c50fed0992fcc1931f85d05df8f2ef7e50c173e4008edc4d21ff684923ec182edddebb2fbef35bf8ca23b673c173e2b91ff91f211f, 0x47317bf4826cbf15c476df7983fc657a3f77a0bbec95837e32943fa6b365f684d0bf13520fde8943fc4d4efb8e60b9e4c48d7e3288ef85d09bf17a2aba39c177cd9131fbbd483f8e6177f1cca77ca18e7fc4d373d48266fec9535fdc68bdfb961cfe8fb197e66c177c87908fa6b23ff26239fd15cd9752091ff88e11db28647fec94cdfdde8bde8bd0bb51ce177ec68cdfd2090febe27a3f7a24c7e8a8cdfc4705dfa9705df7de39fec197dfe39a80d9310bb78aeef7ec9473fd9290ffb4223ff77a97be50c2edd35893fa4140ff8dac1bed085ef4c185dfa6b0bbf17a007ef448ffccd931fbbd4bdb77a2f7e60c177e4002efa6b21ff4d623b692c98fe398bdea6b23fb2620bbe60ca1fc878fffc4d23ff60c47f64c473fd35983fc4d05df7a292ee9051bbe328bdfb0605df72c39fefbccdfccd90afb065f6f8af15ff1cdf7fe3982efb25497b1ce0b9e50c477c8f82e7bef23ff7a29aff12898fde88e7fc4d7a3f8e69afefbc476e0d05dfc57483f1ce23bc2f41734a190ff8bd17bd336176e43c2edd9285dbc73337f77a4c6e92d25fd35931fa6b1cff64a0b9ed05837d20931fbbd64bf8ca4c7efbdf7fe38c65fc57287f17a23befbc5efdde9a7fc5705cf1ce176e23800ec5e8aafc4d89bf60c47fc43c477dde85dbbef21ff9000b9f134dcfd8324bfc57337f30660ff195a17d92931fc7311db60c0b9e60cc07e39808fc7389bf8ca9ad69ac8e7cf608ef82e05df2623bfefbc177dffbeffbbd263f306423effd837cd905df9b217bf23e0bbf01de8fc9888efc57365f21e433e17400ddd210ff99b1cfe8e6d0af15ca4fc738d0f34249778e623be92c476ccd931bb4205df64a19fe66c73fd35a48fb0611db0ba167e50c98fc8782e7bef11df8f6f47e238173e39bbdf98323ff78c60fe50ca1fd258bdec4d0bbf60c2f7ec948ffddeb06fbbd1cff89ad3be904c1fe269437bef0bb77a2c97e43c476ccd943f9f91cff23e43fe6c8d97d830e7fc7321ff49639fe92ca1fcbc8bdfbd10bb77de92ef20073fa2b983fbd121ff77a177e9ad20fe39b25f91f1ebf8ae0bbe2f4587c7388ed2a70bbf23e2f7a8bc98fc47081fbbd05cf3365fbe2f4476e268bdebef497b23e177e47c5efc47001f99b05cf1ce177d1b632fcc18bdec4d685f8e6176ed0935fddea6bf9b223ff7de0b9f0cc5efc4705dd8e71b3f], []]
  | 7 => [[0x1f], [0x4d7f17bf1cff11db7dff287f89bf365f05df60df21ff8e7f337f685f307f8aff497f1cfe64bf77bf0bbf263f17bd23ff11df0bb705cf483f7a3f8cbf], [], []]
  | 8 => [[0x1f], [], [], []]
  | _ => []

def C3_S (s j : Nat) : List Nat :=
  qGroupedState C3_initial 4 32 11 C3_patterns C3_values (C3_counts s) (C3_specs s) (C3_records s) j

def C3_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C3_initial (C3_counts s) (C3_specs s) (C3_seeds s) ws

def C3_groups : List (Nat × Nat) := [(14,0x4000a008), (28,0x62202000), (1,0x2282888), (18,0x80000), (5,0x2202088), (17,0x2282008), (26,0x4a080808), (9,0x2202808), (22,0x40a80088), (2,0x80888), (12,0x2000), (20,0x200000), (24,0x2000000), (0,0x8), (6,0x8), (10,0x8)]
def C3_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C3_groups ws else diffCover 0xffffffff C3_groups ws
def C3_Z := barBudget 0xffffffff 0xeaa8a888 C3_cover C3_S C3_N C3_idx
def C3_flat := certAt C3_Z C3_N 9
def C4_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C4_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff8888ffff5555fff0fff0fff00000ffccffccffaaffaaffaa0000ffa0ffa0ff88ff88ff00f000ff00cc00ff000000fcfcfcfcfafafafafafa0000faf0faf0fa00fa00f8f8f8f8f0f0f000f0f0c0c0f0f00000f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000ee00ee00e0e0e0e0cccc0000cc88cc88cc00cc00c8c8c8c8c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a0888888885555555533333333333300000f0f0f0f00ff00ff0000ffff

def C4_patterns : Nat := 0x0

def C4_N : Nat → Nat
  | 3 => 5
  | 4 => 35
  | 5 => 33
  | 6 => 1
  | _ => 0

def C4_counts : Nat → Nat
  | 3 => 0x4001000
  | 4 => 0x501d001
  | 5 => 0x20001
  | 6 => 1
  | _ => 0

def C4_specs : Nat → Nat
  | 3 => 0x381101000
  | 4 => 0x201601101
  | 5 => 0x501101
  | 6 => 257
  | _ => 0

def C4_seeds : Nat → List Nat
  | 3 => [0x0, 0x2, 0x21]
  | 4 => [0x2, 0xf0171060110090025c80bc, 0x13]
  | 5 => [0x2, 0xd8837941a030028400a, 0x0]
  | 6 => [0x2, 0x0, 0x0]
  | _ => []

def C4_records : Nat → List (List Nat)
  | 3 => [[], [0x16e], [0x8991c459a9586c96a]]
  | 4 => [[0x1f], [0x33b47783c4794f3fad6e4b97e2dca3ee7ccf4debee5ba5772ef3ef7d2f6f65bdddc7737b15ec7d6f], [0x152d3c223e05b8a1dd832b]]
  | 5 => [[0x1f], [0x5e379ff91fc7f57cefe5f27e1fcaf83f9fe2ff0fadf29f47ccfabf63e15edf85fc1f0fc6fa1f17a1ec7fc1f], []]
  | 6 => [[0x1f], [], []]
  | _ => []

def C4_S (s j : Nat) : List Nat :=
  qGroupedState C4_initial 3 32 6 C4_patterns C4_values (C4_counts s) (C4_specs s) (C4_records s) j

def C4_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C4_initial (C4_counts s) (C4_specs s) (C4_seeds s) ws

def C4_groups : List (Nat × Nat) := [(22,0x204008), (12,0x4000), (9,0x2000000), (26,0x40000000), (17,0x2280000), (28,0x20004000), (6,0x4000), (10,0x4808), (13,0x2200008), (5,0x200000), (2,0x8), (24,0x2000000)]
def C4_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C4_groups ws else diffCover 0xffffffff C4_groups ws
def C4_Z := barBudget 0xffffffff 0xeaa8c888 C4_cover C4_S C4_N C4_idx
def C4_flat := certAt C4_Z C4_N 7
def C5_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C5_values : Nat := 0xfffffffffffffffcfffffffafffffff0ffffffeeffffffccffffffc0ffffffaaffffffa0ffffff88ffffff55ffffff33ffffff0fffffff00fffffefefffffcfcfffffcf0fffffcccfffffc00fffffafafffffaf0fffffaaafffffa00fffff8f8fffff800fffff5f5fffff555fffff500fffff3f3fffff0fffffff0f0fffff0c0fffff0a0fffff080fffff050fffff000ffffeeeeffffeeccffffeeaaffffee00ffffececffffec00ffffeaeaffffe0e0ffffe0c0ffffe000ffffddddffffdd55ffffdd00ffffd5d5ffffd0d0ffffcfcfffffccffffffccccffffccc0ffffcc88ffffcc80ffffcc44ffffcc00ffffc8c8ffffc8c0ffffc800ffffc4c4ffffc0c0ffffc080ffffc000ffffbbbbffffafafffffaaffffffaaaaffffaaa0ffffaa88ffffaa00ffffa8a8ffffa800ffffa0a0ffffa080ffffa000ffff8888ffff8880ffff8800ffff8080ffff8000ffff7777ffff5f5fffff55ffffff5555ffff5550ffff5544ffff5500ffff5454ffff5050ffff5000ffff4444ffff4400ffff4040ffff3f3fffff33ffffff3333ffff3300ffff3030ffff3000ffff2222ffff1515ffff1155ffff1111ffff1100ffff1010ffff0fffffff0f0fffff0f00ffff0c0cffff0c00ffff0a0affff0555ffff0505ffff0500ffff0404ffff0303ffff0101ffff00ffffff00f0ffff00ccffff00c0ffff00aaffff0055ffff0050ffff0044ffff0033ffff0011ffff000fffff0005ffff0003fffefffefffe0000fffcfffcfffcfff0fffcffccfffcff00fffcfcfcfffcf0f0fffcccccfffc0000fffafffafffafff0fffaffaafffaff00fffafafafffaf0f0fffaaaaafffa0000fff8fff8fff80000fff5fff5fff3fff3fff0fffffff0fff0fff0ffc0fff0ffa0fff0ff00fff0fcf0fff0faf0fff0f0f0fff0ccc0fff0aaa0fff00000ffeeffeeffeeffccffeeffaaffeeff00ffeeeeeeffeeccccffeeaaaaffee0000ffecffecffec0000ffeaffeaffeac0c0ffea0000ffe0ffe0ffddffddffcfffcfffccffffffccffccffccffc0ffccff88ffccff00ffccfcccffccf0c0ffcceeccffccccccffccaa88ffcc0000ffc8ffc8ffc0ffc0ffc0ff00ffc0c0c0ffc00000ffbbffbbffbb0000ffafffafffaf0000ffaaffffffaaffaaffaaffa0ffaaff88ffaaff00ffaafaaaffaaf0a0ffaaf000ffaaeeaaffaacc88ffaacc00ffaac080ffaaaaaaffaa5500ffaa0000ffa8ffa8ffa8ff00ffa80000ffa0ffa0ffa0ff80ffa0ff00ffa0a0a0ffa00000ff88ff88ff88ff80ff88ff00ff888888ff880000ff80ff80ff80ff00ff77ff77ff5fff5fff55ffffff55ff55ff55ff00ff555555ff550000ff50ff50ff44ff44ff3fff3fff3f0000ff33ffffff33ff33ff33ff00ff333333ff330000ff30ff30ff30ff00ff22ff22ff15ff15ff11ff11ff11ff00ff10ff10ff0fffffff0fff0fff0fff00ff0f0f0fff0f0000ff0cff0cff0cff00ff0aff0aff05ff05ff05ff00ff04ff04ff03ff03ff01ff01ff00ffffff00fff0ff00ffccff00ffaaff00ff55ff00ff33ff00ff11ff00ff0fff00ff05ff00ff03ff00fe00ff00fc00ff00fa00ff00f800ff00f000ff00ee00ff00ec00ff00ea00ff00cc00ff00c000ff00aa00ff00a000ff008800ff005500ff003300ff000f00ff000000fefefefefefefcfcfefefafafefef0f0fefeeeeefefeccccfefeaaaafefe0000fefcfefcfefc0000fefafefafefacc00fefa0000fef0fef0feeefeeefeeef000feee0000feccfeccfeaafeaafeaafc00feaa0000fe00fe00fe00fc00fe00fa00fe00ee00fdfdfdfdfcfffcfffcfcfffffcfcfcfcfcfcfcf0fcfcfcccfcfcfc00fcfcf8f8fcfcf0f0fcfcececfcfcccccfcfca8a8fcfc0000fcf8fcf8fcf0fcf0fcf0f0f0fcf0cc00fcf00000fcecfcecfcccfcccfcccf000fcccccccfccc0000fca8fca8fc00fc00fc00f000fc00cc00fc000000fbfbfbfbfbfb0000fb00fb00fafffafffaff0000fafafffffafafafafafafaf0fafafaaafafafa00fafaf8f8fafaf0f0fafaf000fafaeaeafafac8c8fafac800fafac0c0fafaaaaafafa5050fafa0000faf8faf8faf8f0f0faf80000faf0faf0faf0f8f0faf0f0f0faf0aa00faf00000faeafaeafaeaf0c0faea0000fac8fac8faaafaaafaaaf000faaaaaaafaaa0000faa0faa0fa00ff00fa00fa00fa00f800fa00f000fa00ea00fa00aa00fa000000f8f8f8f8f8f8f8f0f8f8f0f0f8f88888f8f80000f8f0f8f0f8f0f0f0f888f888f800f800f7f7f7f7f5fff5fff5f5fffff5f5f5f5f5f5f0f0f5f55555f5f50000f5f0f5f0f555f555f500f500f4f4f4f4f3fff3fff3ff0000f3f3fffff3f3f3f3f3f3f0f0f3f33333f3f30000f3f0f3f0f3f0f0f0f333f333f300ff00f300f300f2f2f2f2f1f5f1f5f1f1f1f1f1f1f0f0f1f0f1f0f0fffffff0fff0fff0fff0f0f0ff00fff0ff0000f0fcf0fcf0fcf0f0f0faf0faf0f5f0f5f0f5f0f0f0f4f0f4f0f3f0f3f0f1f0f1f0f0fffff0f0fff0f0f0fcfcf0f0fafaf0f0f5f5f0f0f3f3f0f0f1f1f0f0f0fff0f0f0f5f0f0f0f3f0f0f0e0f0f0f0c0f0f0f0a0f0f0f080f0f0f000f0f0e0e0f0f0e0c0f0f0e0a0f0f0c0c0f0f0c000f0f0a0a0f0f0a000f0f08080f0f05050f0f03030f0f000f0f0f00000f0e0f0e0f0e0f0c0f0e0f0a0f0e0e0e0f0c0f0c0f0c0f000f0c0c0c0f0c00000f0b0f0b0f0a0f0f0f0a0f0a0f0a0f080f0a0f000f0a0e0a0f0a0a0a0f0a00000f080f080f050f050f030f0f0f030f030f00ff00ff000fffff000ff00f000f0f0f000f000f000c000f000a000f0000000efefefefefef0000ef00ef00eeffeeffeeff0000eeeeffffeeeeeeeeeeeeeecceeeeeeaaeeeeee00eeeeececeeeeeaeaeeeee0e0eeeee000eeeecccceeeecc00eeeec0c0eeeeaaaaeeee4444eeee0000eeeceeeceeeccccceeec0000eeeaeeeaeeeaccc0eeea0000eee0eee0eecceecceecceccceecccccceeccaa00eecc0000eeaaeeaaeeaacc00eeaaaaaaeeaa0000ee88ee88ee00ff00ee00ee00ee00ec00ee00ea00ee00cc00ee00aa00ee000000ecececececececccececccccececa0a0ecec0000eccceccceccccccceca0eca0ec00ec00eaeaeaeaeaeac0c0eaeaaaaaeaea0000eac0eac0eaaaeaaaeaaac000eaaaaaaaeaaa0000ea00ea00e8e8e8e8e0f0e0f0e0e0f0f0e0e0e0e0e0e0e0c0e0e0e0a0e0e0c0c0e0e0a0a0e0e00000e0c0e0c0e0a0e0a0e000e000dfdfdfdfddffddffddddffffddddddddddddccccdddd5555dddd0000ddccddccdd55dd55dd00dd00dcdcdcdcd5d5d5d5d0d0d0d0cfffcfffcfff0000cfcfffffcfcfcfcfcfcfcccccfcf0f0fcfcf0000cfcccfcccfcccccccf0fcf0fcf00ff00cf00cf00cececececdddcdddcdcdcdcdcdcdcccccdcccdccccffffffccffccffccffccccccff00ffccff0000ccfcccfcccfccccccceecceeccddccddccddccccccdcccdccccfcccfcccdcccdccccffffccccffccccccfcfccccceeeeccccddddcccccfcfcccccdcdccccccffccccccddcccccccfccccccc8ccccccc0cccccc88cccccc80cccccc00ccccc8c8ccccc8c0ccccc888ccccc0c0ccccc000cccc8888cccc8800cccc8080cccc4444cccc0c0ccccc00cccccc0000ccc8ccc8ccc8ccc0ccc8cc88ccc8c8c8ccc0ccc0ccc0cc00ccc0c0c0ccc00000cc8ccc8ccc88cccccc88cc88cc88cc80cc88cc00cc88c888cc888888cc880000cc80cc80cc44cc44cc33cc33cc0ccccccc0ccc0ccc00ffffcc00ff00cc00cccccc00cc00cc00c000cc008800cc000000c8ccc8ccc8c8ccccc8c8c8c8c8c8c8c0c8c8c888c8c8c0c0c8c88888c8c80000c8c0c8c0c888c888c800c800c4c4c4c4c3c3c3c3c0ffc0ffc0f0f0f0c0f0c0f0c0ccccccc0ccc0ccc0c0ffffc0c0f0f0c0c0ccccc0c0c0c0c0c0c000c0c08080c0c00000c080c080c000c000c0000000bfbfbfbfbfbf0000bbffbbffbbff0000bbbbffffbbbbbbbbbbbbaaaabbbb3333bbbb1111bbbb0000bbaabbaabbaa0000bb33bb33bb00bb00babababababa0000b3b3b3b3b0b0b0b0afffafffafff0000afafffffafafafafafafaaaaafaf0f0fafaf0505afaf0000afaaafaaafaa0000af0faf0faf00af00aeaeaeaeaeae0000abababababab0000aaffffffaaffaaffaaffaaaaaaff00ffaaff0055aaff0000aafaaafaaafa0000aaeeaaeeaaee0000aabbaabbaabb0000aaafaaafaaaf0000aaabaaabaaaaffffaaaaffaaaaaafafaaaaaeeeeaaaabbbbaaaaafafaaaaababaaaaaaffaaaaaabbaaaaaaafaaaaaaa8aaaaaaa0aaaaaa88aaaaaa80aaaaaa00aaaaa8a8aaaaa8a0aaaaa888aaaaa800aaaaa0a0aaaaa080aaaaa000aaaa8888aaaa8880aaaa8800aaaa8080aaaa8000aaaa5555aaaa2222aaaa0a0aaaaa00aaaaaa0000aaa8aaa8aaa8aaa0aaa8aa88aaa8a8a8aaa80000aaa0aaa0aaa0aa00aaa0a0a0aaa00000aa88aa88aa88aa00aa888888aa880000aa80aa80aa22aa22aa0aaa0aaa00ffffaa00ff00aa00aaaaaa00aa00aa00a000aa008800aa000000a8a8a8a8a8a8a0a0a8a88888a8a80000a8a0a8a0a888a888a800a800a2a2a2a2a0ffa0ffa0f0a0f0a0aaa0aaa0a0ffffa0a0f0f0a0a0aaaaa0a0a0a0a0a0a000a0a08080a0a00000a080a080a000a000a00000008f8f8f8f8c8c8c8c8a8a8a8a88ff88ff88cc88cc88aa88aa8888ffff8888cccc8888aaaa888888888888880088888080888800008880888088008800880000008080808080800000800080007f7f7f7f7f7f00007f007f0077ff77ff77ff00007777ffff77777777777700007700ff007700770070f070f07070f0f0707070705fff5fff5fff00005f5fffff5f5f5f5f5f5f00005f00ff005f005f005757575755ffffff55ff55ff55ff000055775577555f555f5555ffff5555777755555f5f555555ff555555555555550055555050555544445555000055505550554455445500ff0055005500550000005454545450f0f0f050f050f05050f0f05050505050500000500050004ccc4ccc4c4ccccc4c4c4c4c44cccccc44cc44cc4444cccc444444444444000044004400404040403fff3fff3fff00003f3fffff3f3f3f3f3f3f00003f003f003c3c3c3c3737373733ffffff33ff33ff33ff000033cc33cc33773377333f333f333f00003333ffff3333777733333f3f333333ff333333333333330033333030333322223333000033303330332233223300ff0033003300330000003232323230f030f03030f0f03030303030300000300030002aaa2aaa2a2a2a2a2a2a000022aa22aa22aa00002222aaaa222222222222000022002200202020201f1f1f1f151515151313131311ff11ff11551155113311331111ffff1111555511113333111111111111000011001100101010100fffffff0fff0fff0fff00000ff00ff00f5f0f5f0f3f0f3f0f3f00000f0fffff0f0f5f5f0f0f3f3f0f0f0fff0f0f0f0f0f0f0f000f0f0c0c0f0f0a0a0f0f00000f0c0f0c0f0a0f0a0f00ff000f000f000f0000000e0e0e0e0ccc0ccc0c0ccccc0c0c0c0c0c0c00000c000c000aaa0aaa0aaa00000a0aaaaa0a0a0a0a0a0a00000a000a00080808080707070705ff05ff05550555050f050f0505ffff0505555505050f0f0505050505050000050005000404040403ff03ff03ff000003330333030f030f0303ffff0303333303030f0f030303030303000003000300020202020101010100ffffff00ff55ff00ff33ff00ff0fff00ff00ff00ff00f000ff00cc00ff00aa00ff000000fc00fc00fa00fa00f0f0f000f000f000f0000000ee00ee00cccccc00cc00cc00cc000000c000c000aaaaaa00aa00aa00aa000000a000a00088008800770077005f005f0055ffff00555555005500ff00550055005500000050005000440044003f003f0033ffff00333333003300ff0033003300330000003000300022002200110011000fffff000f0f0f000f00ff000f000f000f0000000c000c000a000a00050005000300030000ffff0000fff00000ffcc0000ffaa0000ff000000fcfc0000fafa0000f0f00000f0000000eeee0000cccc0000cc000000c0c00000aaaa0000aa000000a0a0000088880000777700005f5f000055ff0000555500005500000050500000444400003f3f000033ff000033330000330000003030000022220000111100000fff00000f0f00000f0000000c0c00000a0a0000050500000303000000ff000000f0000000cc000000aa00000055000000330000000f00000000

def C5_patterns : Nat := 0x955956458559561565565555454951525465152546516454951945915855

def C5_N : Nat → Nat
  | 2 => 12
  | 3 => 132
  | 4 => 0x4a7
  | 5 => 0xa71
  | 6 => 0x3fc
  | 7 => 32
  | 8 => 1
  | _ => 0

def C5_counts : Nat → Nat
  | 2 => 0x6006000000
  | 3 => 0x3051030000000
  | 4 => 0xc0ed27113c001
  | 5 => 0x10f56c3f0006
  | 6 => 0x30c0ea006
  | 7 => 0x1f001
  | 8 => 1
  | _ => 0

def C5_specs : Nat → Nat
  | 2 => 0x281301000000
  | 3 => 0x181581601000000
  | 4 => 0x581781681801101
  | 5 => 0x681701696216
  | 6 => 0x701696216
  | 7 => 0x501101
  | 8 => 257
  | _ => 0

def C5_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x5c2, 0x161, 0x0]
  | 3 => [0x0, 0x0, 0x11a80e02012802049a00200280783000701f, 0x401a0c0089d004a1f05a9b48240c43b0060020080a00602203800ad0, 0x2]
  | 4 => [0x2, 0x495e01020001000106de105a004004040094001602310082810f0a5f000180ca002901b80047002c813c00240501000600030019003f000206900270000d001b042a004f00b60002005b001500a8002e80a80105000c00180031002000150130003b0016000400060001000100010028001a0013000200250012000100f40001001a000500020001001a001d00090009000100030002000100b4000d809b, 0x2d4565499003000123a81b45dc4f4039826000402a05083c03600ed002853007e19007e803e49a00b001830c09e027000831804a00291d0010144153076c84c6d000202c01841d6008007804c00226b00a474c46803d01600280bd17d027811c252006019801810803a00100bc02804e01545d000c00988d00a8002059026803807800a87b015403c0c203201b000200200080b400801a00649c400200201082ec04e00486542f009a004001007216a0520074298020058009090e0d4004031803044a0018180014002001001808c01e04a93881502e6042006000c00a027000820007302500281164e203817a013002c01e00180d80080020008254030007, 0x68562a8404981bb09c404b600a803f00800008026800f000c0a180ca8371005e0160069801600a40078001000100560014000800d00900068005806a00b6003004b8029008a05c401880300004000c010808a000200480170005000c01e800380770056000c018800401b400040078007, 0x86003007]
  | 5 => [0x13, 0x19806403a043001000c43a0d10068b6182204e00f80f400405d9f30d9a77e42e9d34e5148e0d70064c702c8002382890a62c07c9f8005c10004400bb23c2e411b01e87f0002a8e09c89325333f0006800403a0191fc800800a336144c8181d80ab00648083501830a580223f434b037466c06e024013800420a002007005c0ba005085809c0e200800600301d600501746681c2015001800827200212c01882f51698ae0c6c0840d017d00803ce0fd006001018a006143800414f154083800804202f14680040c804900e82ba7e01160008006274007001001c0a60011150054086001007c39c06208a015800803400b002800400600904785a403e07b022010406410100082ec05200e03d432c0ce03b0058060061086002009c0021b4038000819a1f983b00d008201002a002c05e0050010008094008004805c1a003f009020c002008004001408c02c00381280160169f800100ba00c00100c403803d003801c10e05c002801a02200f02180380b810500300f005200a00f8010025001017009c01e002005803801a00700080f0022004006800400a026, 0x1003113d08fc0241eac04b00040311a0000c00480060008215004cca700bc00300440b105900d100040050004063242a56c94440ef045c08a000425c008899b01d8167006000603dc0090036502000401505d03df001003600040af02fce3600040d7017e4fb005c1580a8804d000c03a026c16307c026c01224e003e0002001002a00184bc00bc1b3055c00192842db00800c608bc00d00e009301cc001002800a063002c00a002000d403391ca56c075000395b003f000403404900080084028000c00490d80040ce81a200c430811b4067047a37502941da8d400a100082c300c400707a001495b00540010132001c12a036000f01c400800340140c6003a005c04f00040af0054018018400404e256c01c805005a4002001633800105330004042000800a004801200382720b0c0b000183a500800f204ac18d008400b01bc0ce064c0fe001c0140050005014c00605cc002040802f8c780e1011810705100d2000c00800a40200118015003230300122b302ac00f000400a000808c021806700c22aa0094012004800a001401700540b008c001e002800104f000201700010568001012800c006400102c804b00840020044214002004f95b0001005805600b22a60028004000e56c02b0005000805a00dc0330040006893c00200f400102b00c3003001b00f80ae050c00101dc005001401801262470018080000401800080d0011c00900080850430003004000e000c0140090015000c00801bc00e007000595b000c008400b01b400a0038014006e1eb003400b0034043003c00200121c1095406183dc09400060a303a00080288029006c02c0004059026209d, 0x59d96c8086042004800488c00119782b81a625e000852411a04d01c04cc0e0010001002c00a00d01f846402600e0d20014004012051801c025059000820003a003005870033005e829004822600200b804c22c0128198012048001003800c0aa00b032805400c001000802800d020, 0x0]
  | 6 => [0x13, 0x83d90d00170e4e14400100900a60281f602780481ba0161560560004a8706e803000600700a802c06c030006804000205201e002400a01a05d00080e80190650068020033001001401814a047804000207701b815804400a0090008008002, 0x28001c02200fe2cc8a60208027e1b00004e90000444302347e10080017001230c42c805700349d1002813c0af40021e280f800645e700044b1016c00c39e80b3008e30c0fc8086094c067009000a000c00200b8031868400100040db003619d000c00d866808b8c300ab010c0f4000c039005014201bc04403c80038c30009860c00800041311844001117c0df02f400403780cf001802500c40cf012016a000400c0040090058617200941a0038c019001400209280e785c408900180870094001001000300940130090001007e30c00200230194002047c001004404c01841d88448008002c0320010022001804084140a70038015840a0f60098005001000b827000305580018c30023002000302b83ac005c0020034002014000a0010002000815512c40018134008000c02400100a401b802600c8003012000900300048124087002403d00cc00881100020004001000c016, 0x0, 0x0]
  | 7 => [0x2, 0x3b0224100b01c0382c0e, 0x0, 0x0, 0x0]
  | 8 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C5_records : Nat → List (List Nat)
  | 2 => [[], [], [0x12294322d72ae25b451c4908aa111813542272a68], [0x7766c0ab818a2282a608686c0a381d021d2a808308a09a820ea1d2860], []]
  | 3 => [[], [], [0x4604d528c09ab1229432a3026aa59a9612b68a399d02452a4528745b451c4ded6d0d22943223026b8712b88707521158a2304ada28e3868b5c6de5780cd815762e64b095c8b686b3d18256d147523a460937a52a8e252495ddada1b744b0548a50d892d2294d2149c37648a55145714ce0af99782384af04a2943a5514914a198ee95b637d5e035b451e48c09aa20c2274b7d4b054d452e4e25730d1415333894a25], [0x1cb9bd2c0448a6f4a191201d62ac4776b68a3893515728e24fc6f4a6421a3bb45826f2bc11c051414d22e44425349aa0da14d26a8392534a191181a426a87649a8b088d814d272472ea48de860eba04584868b6ca3890e9bd28704605349aa0d215326a85b49a8a389d0245286445c6909aa12293922e437a550a1920c23126a866272caf11c4ae249215e09609aa1d0309459072ac5116417f9a429904f05349c88db94d24e85a6534a38a1a3bb3601740918aa120ea4628644d4744a6418a2312a6847a534a191419b72b287929f8de851214d22e848a534a191e4a6a3a215aa534938998a782bc243a5348ba1d926a3ca1450534938a0c31445884ec534a3896aa832b2236053493a16c26a28e283ae810e851812722e84866f4a1912014d22e46288c09aa0d214d26a8680c2cd2056d14d28e2792bfcd205c4af028e2616690aea1141a426b03965349c913514d28e2776c111641351b028f06e8b352c05ddadb2ae2712960a1916d13924e2830c5114050e94d272237a534a191121d62ac8], [0x2404485348b816a9b729a49c09e0e594d2720]]
  | 4 => [[0x1f], [0x7acf4b2f3fdd2e0f83af5caf6857486f71cf6caf7f2f3d1d82cf36fd5a976b573ebd36bd63af49af505b15ef314f856f3e7d48174f5b2c3e2fcf401d304f46bd1c9b5ad76f8f3abd297e2aaf324f3a7d7f4f2c7e495d69f7638f52bb194f754f7fef55bb4a0f706f67f740dd385d299e802f391d87ef130f635753db593b541b395d4efb338f68176bd73efd51db397d834f7c8f86af4f3b456f523b4caf217782ef2dbe4c97832f6fef5cdb293e6eb73c9d2b7e5def5a57595b1f7780ef4a8f47d749cf5b4f501b6b77163e84cf6b372eef32af7b8f473d452f51bb7f8f39bd80af5d0f4c4f2b4f18cf45172b9e373d68b7445b295e81af290f3ffd2a8f521b74cf525b1a6f2bbe559b455e2aef3e9d4ffb3c7d2c1e218f36dd3cdd2c5e642f7e4f460f637744bb7a8f41af77ef7b0f59bb842f2a4f2a2f0fcf5c5b3cfd70cf4097503b459e80cf29af7a6f55db83cf7b2f567b1fef7c0f5f4f7fcf493d5baf2ecf6337830f31cf7a2f3a9d527b84ef816f205b7c6f212f67d748371b7d574f88af7f6f5ab75bcf750f7d8f43bb7faf782f2a6f2e4f5d2f519b2f8f85cf3a5d308f207b52fb7def353d6f3769974e1b5b0f64ef6fb7128f836f6a57549b850f56376e376b9769d7814f7caf7b4f7daf6317357b44db652f2c9e45cf1bdd7c4f74af3c1d7e0f15af545b2e8f87af83ef471d68774a6f86cf5f376757810f469d, 0x1bbd854f3c3d640f7dcf68374a3d870f557b67777f0f3bfd704f334f64af5d6f6e977cef3e3d361d2dcf720f403d47f7371d3d5d6a174ebb20b76e17792f2b0f1a0f5d8f447b328f700f543b59db529b3cbd2bfe48af800f4aef648f4acf449b6f57868f5c7b4f1b6797878f30af84af0d8f399d2cde5eef], [0x4a66ddaf257f9e00a785bc136ed868900f088f13628b383aad4813652b54eea9201cf214d6a4948155fe92eaed1354e0d1b769b729ad7406f6b1299c9d8d94d394d158e63e6bead40a69d350979b8967a75feb926a48b069dc2f05b3c4a6766e72ea8b0a6b98a221cbb2712772a72eae5d492db8a3aaa82397943a5356eed6d1dbb15eb43951eb50494d6a88fae5e09d56c346f6772e581cdfd201d889a4ca8b2bba43a45f2ba166ad9c95e3a53448b29a414f0d0adb921a1d5a4b37b56d89e26c8d0e4e0b9cb6a2c397c3c4559b061492d712d59af04719844765ac50d265782215a913c9989acd0e9149c9ddba6a9b39525373a961b031bc9d8b9a4cc463bad80cb3d6c1120561f2865c293b2d7306f6ac3d6acd861a4cb1436394b0789ab911ae5b894d3ad52b3660069328d4a6b584ad59a783c99764bc16b55654e0eb3d3b1f37b529a085d0756a9ca684e715722ee6fea896e25989ddc1cbaba048b57929f96b689c9dbb1bdac34458e6fe791a960eb34d8139ab895c4736e49f307525b56aa249b7029a772c6beac50d6e5c4a492b9948157769ca7005201d741b769b029ad6288c170e510adf735b3c2a480766e9e26e25712d161b0e39e37b55c45356d0145cda015db14d28ee6246932e24a21d6aa533b5b29a76fe755ab3cace9d226a9ad84f0b75472da5347d9dce1bdaac929ab29a4d5cdb0e5d5d52785b3f29a75e08e16c511825b89cba94d27ee5aa6deae811955479e5c95d29ae48055ac9e0af69bfa245c39514b5e09d96944a6b60c1e56b0f36f96e8b3670d0e5b4ea94d6a8e4a6b764585d025ba1d7226a9c1d594b83a571c9e0fae566a585aca36f983a9e16b352c660b22c721d3979814decf0d1722de494c729229ab7548916744a671142249c1d3cad3c45838bc0922dbc94d3c18396d4808b2cca5122d201dcaa43396d5aa534eba1122dbda8f9ba048ad45045eb12924b4f2961e3b571278308a0eeed0e4d8a2306bbb5b534f072f28b9122e0ea403b3c29a78309e17084f2b4af15972c336f972ee24e960e4b566a584a2c24fa4a672daed56acd3524c9be46a073bc5778f9100361a1b76af0516b7dcab57004dbb6111e56a4044934b0451adc567cd412409a8b475983057dcf90dbb5c49363a78481344845f2c35126584a2cd3b84f1334833b30e1492dbcaf01c06474d81ece4ec38d265121dccc0c516b, 0x80e92daee5354d781445a2824f35e04c96960da361a2925c0f67a777c9aa69e0eae5742403a4237b58028916a39204d6e1bdaaf051eb5aa786a92cab718a22dc9cb2735844779adf4a69e0c33a3a3a2adc754a096cfcf0d60c2cf5b3f5d074f094d6cf4f2d4be94d738967272bc559d0d16a9dbcaf05c39516b830b54ee25699dddad39af0470d6286832eed63cd8595d7434680788ea296c68a69cdb959e4223bad5aa49e6ca4dbb60c23a6a3022ed450534ee81229d8a21ecad5587352272f2ca5201de49d1694c290e7829e16ba13c2e1a28b5c093bcd7346f6ae58ded5bda6a9b795e07872a196c6cdbd54714d59cb29ad776b6969a8a3ce0d2d53bce37b5868cfce8b09cda1a2915a2c22fc45c8a0eba1712d679d1cc22368d712b8a6e25249da014d3b0a3419470535a890e5e5ed1cb6c174f0b5aa6c2a94d1c35bfad53c186e27712925ae651266033713b9971275b06c1a9e0dbe4a694373da3ead29a4c5d08966ad20117abee48076fede4eb34a6ae0c2245c4a5c4b740726adecaf59139a4cb7f3ead5e0a0d70d0efb5a8200aa312a6e8948f4ec14d2658a230c95424ee59a961ad6d124ddb26a9ae8400d29a3916e2524d52c1de6bb536f96fea096794a6b611161737429a76fea4566909ae4d8127cae629ab5aa802ae251e9dd0233abbb5b4380eb296a24dbe5679decc01396d60a6832ded1ad5ce9cba96029ae6ecb2a6ec8f2b60c1e26b3d2bc781e925acfcdbd5c4ae21a4929ad59e6932ab529ae25340394d204b5d0b54eeed3b4d9e961b3cf4d5337a326aba0eab6111c96aca29ab740914abfca6596524bcb794f1379869328e8d26572159d30f4b0d5445356bc11c25a82e83b234d5378272da778ab3529a496a2429ab6088932e6cded5cea789c396f2729a531ce553c4dba2586b7f6e87680c2cea48f1653f14cd3c15aa7486900f115a01d4894d5a2c36fc29a4c1c96099356aa789c1d396d7488726c2d2c358dae83a2c43ba83add8f0056a9e2515d730d5e0b4b0501ac4cd2650014d6c4a66876ec746ad6d56cdf22d53b7b4fd36126df2a3cacad94b1b3c1d36ed83a779b03d712d0e9399a2836f57408f6ad40dbd59e28e9c0a46ad6fe6ddae5d2c35511cbcb403bd5894ce0ee80d7d586a40a9d429ad5ae9aa69010c553c1b0cb394975712500f061472dbca38aa2c45167466f6a5c4a6b91c224cbb34d53, 0x33d5c934808766b616a9d3c14d5a8b2b2b8188e1b0611639dda6e9c34448b6e8960aa08a6ad181275c1d458e83acf0f089ba1e1a1b06b7439756088b38c2d782cb094d72d545966e8962b06147ad8da249c1d518b63694ce7d4a6b60eb403c1836ed45889351299e9e1a2356b3c44938728e1a918aa39bfa785ae24939776b226b34dbe5cf9bdab5b4a672a64e5ca04a6adf722459bd2875872581ce80e1d4f094d6bbb4d5329a1f5cdd8f15512218ca5348075d072db0e53b2e252d33bda544b83a791ac50da64a6928722c452e830900f0750ead881a4cbda4f0b868ce4e900e5d60628f5ba038b52de535cb5544cd3c22cd1592ace4806deace4b05947961d2d53ab548a45da8d51265dd26a9b795e1372a8b2d060f0b52014d3a78273361469325346db603b763adb2aee8548917075122db8a789c0959ab29a461d029722dba2583b7f396d468535a890ab68e595ee4093c4d5d0785a8b8dbb61a2785a4046b529a4e9cb54e5d56d1275a7e4759872a496ab4a6ad121b7c94d1bad], [0x1bcaf029a3636c50d2453c14d272a48c5348bb0de94d28647406f4aa160b3a037a54f05349c992014d22ec4485348bb1ddb895e03712b889b0d2014d22e55aa6dca695d01bd29944d4534a399bda6a29a37408f4a6957226a29a38308e8d225c4ae229a34d451c8bc92014d22f45aa53493893014d22ec6fec50d2253c14d2723872b55418cdb94d24ea868e80de95dda7629a3740a08dec62a3b24d436f65349c9a0ebbb4d436e2c50d2451d14d22ec7769a8f2c52c14d26ac3965349cd1d022437b14808908bc52014d22e66ec5349c9a03ba037a5844890eb262533139653965349c99d03894b05844900eb158a22129a937a534a1d1dda6a4592628bc12c25301d62acc6288b0d2618a2403491868eed350ddda6a2ae3712924a6960c3a037a54966f4a695cab1433f17769a8a6497823824894d4534a38d8a22834915aa53493c9e4bbb4d4383ae80de957814d26aa6fe72c9c960c3bb4d433485349ab11214d22ea3965349c920b3143489782eed350dd037f37a588ac50d2261a2e44d434485348ba5dda6a3ab148c5349c99bb1bd29a57769a91ac56a9b724f1628ba0d2260b3bb4d435eaa0caca8db94d24e8776b69350ce594d272c7769a8e5c5e4ba037a5628690a6a61a3bb5b63776ba1350e0c2cf34895d06dc93a51214d22e8844c3cd2251894d24ea740724a6960eba048c57769a8a68d742d524e38306909aa594b1434896f2bc0920dd01bd2c14740ba0de95d030933f1712534a3997124929a97769a9298d8a1a42a694626909ae21a3143489830c5118a57a94d24ea802c50d2258a22e3489718cc4af19c494d28667769a8d8456d94d27267a09f8dec529a4022e5754e80de95679a429a95b69a8a3c96a94d24e66f28e0a6961ca8336e97129249b15231bd28746e89608a15ba2cd29a359e53493a98a1a429987185349c98d214d26b874090cde95ba25829a57409e0dec5e4b1434894d4534a3892c14d286c83add8de95dda6a2c32740914de960e9bd286559a960a6a62939737a5776c10cfc600bbb4d43890c2cd2261c3a037a5830c50cfa61a37b4d435d0b54db953514d28f280cc50d225d01bd29a5894e64de95d029237b1776b68a68d8a23029a94f072ca6a4db94d24e983ac50d225bfa7827237a0bfcd245dda6a36f1776b61350d6d94d24ea740874dec51894d22ec4f05349c88de94d2865740914a6961cb0d3489844e74de958a25334897408b0ded12594d22ec7406f465158a1a42bb83485349aa5dda6a1303474690a6a53c1cb27316288c0d224d214d26aa83ae80cf95bfa7839694f05349cca00ba037a54d4534a3a97823829a9814eed350cdb94d24f874094cde96253b54d43776dfd350d1214d22f85e0534a3aa10bbb4d433485349aa129a2422e9680c50d245ddad329a35aa534938d2022429a38689a8a38e253314f0337a534a19929a40448362869068256a94d24ea3484e49ae20ea4b37a5830c50d2258a1b429a95c853493a9e826a3a3136e53493b0e594d272559a9608a261a3bb33e34805348b90de94d286c872ee1350cde94324f4740b28dec58a2d53491], [0x7189e0a6939138c3965349c913022429a45d0bd56a94d24e237a5349c91723bb4d4534a3898a1a429a4d509a8a693924e27406f4a694322604805348b90d214d24e45d0bd4db94d24e8]]
  | 5 => [[0x2cf8c2f3], [0x1f4f600f42ef4a6f0c0f238f202f83a279af1c2f39cf376f0e801f0f086f29a2868411e92d4f0d0f11af3bcf56cf824f584f694f47af7b6f830f248f4a4f176f4e8f838f232f17ef4f14466f754f362f7aaf2d8f4daf59a932cf13ef62af4f6f4da017cf60af568f524f22cf26af0e6f82cf6a0f54af5fef6e8536ec650f306f54ef80200fef722f29a17bef46af530f522f4ecf2c2e83022acf57cf4c6f71ef5e4f21af88af3f0f712f2eaf070f6fe10b4f148f5d0f7d6f4faf56af614f48061aaf544f5b0f24ef346f3ecf5aaf5449770f07cf4a62538f826f7f401eaf04af0eaf846f814f07af5b8f1e8f762f050f0a8f6cef50af03ef5249298f062f21cf42af400f45057f800e8f04a0636545c01a00760f02af844f2aef658f594f060f0ccf1940730f81ef14cf802f52290baf41ef6b6f5aa54c2f300f64cf33af06cf852f6c2f2faf242f666f680580c01d6f3f6f178f7c2f10a92bae1caf22ef240f19ac5c2f5ecf458f32ef646f1a8f6d0f0ee579ef150f6a6f080f79cf5cef154f180f2e6f0a4f3aef55a95e0f4d0f106f3800358f2c0e1dcf7c80042f0e2f58af6ccf19af85ef66ef462f2c0f6d8f43ef12cf012f62ef400c79205d4f210f098f11cf2ecf7eef278f61cf06af196f226f1fcf3faf6c8f094f4b4f392f252f4d6f0ecf310f8a6f890f78af5fcf8a8f892f5949018f65cf3080714f654f10cf3eaf, 0x5a6f2b2f7dc03def264f6dcf70ef618f5b4f00ef884f492f0aef3dcf740f0c6f536f590f24cf4a61190f784f01ef796f488f3b6f25af7b4040af156f448f01cf088f224f1f2f5c4f508f4f8f164f14af17af864f42cf4ccf8683894f026f1daf66af36f205c03d8f89cf53ef2d2f774f8140696f866f840f2a0f260f6eef23cf1e2f104f118f05001aef1e0f7d2f4b0f1e6f450f280f7ecf670f57af20ef85af888f76af2cef756f73ef1c6f072f7a4f134f374f340f420f074f48a07dcf250f6aef120f044f66cf090f628f560f38ef54cf432f6d4f396d286f5e2f806f50ef0b6f076f5eaf38cf842f434f1c0f1dee152f77cf710f804f69af11ef01e0378f532f778f896f054f5d0088a0754065ef14e95d015f8f1cef332f61ef5049738f040f716f718f16ef34af73af3c2c776f7d4f490f758f8300364f0a2f76cf422f1b0f1d2f586f792f470c0def7aef72cf690f0a6f05cf31ef7e6f308f43a93e4f29ef7ccf2a6048ef5a0f22af0c2f514f082f882f480f5aa8512f136f27cf572f3b0f3cac30cf6d6f67af6f6f066f12af480788ef30ef132f3f4f07ef348f4860316f860f6a2f0b2f5daf396c16cf3baf8a2f636f0560752f3b8f5f0f032f76ef130033cf830309ef75ef04ef2ae061af78cf330f04cf246f5c8f6fef780f014f06ef4e6f3d2f08e0608f24af3a2f6f2f142f0e0f5b00276f020f13cf70af49ef, 0x6e2f336f59ef496f858f448a0bef874f18ef626f870f6d2f732f67ef342f397510af498f298e4b6f4f0a4489096f83a4476f02ef46cf764f25cf1a4f692f26cf208f322f3c8c72af5bef4d8f0dcf57ef596f2caf0a657d0f662f5f6f00af396f1f8f14ef89ef6ecf77af6bef3d6f766f0d6f3aac112f016f82af3c4f7f4f660f598f40ef03cf788f3e0f1def37af7e2f084f182f5b40326f734f0daf200f38af08cf03af2f6f55ef822f0f8f37cf360c510f39ef656f60cf382f868f6fe4554f122f0aaf3eac45cf270f1a2f416f80ef828f4fcf410f034f5dcf1acf0bcf726f256f05af142043cf172f2d0f8aaf68ef28af18af6fe0130f486f6c6f1e4f578f664f59af27ef5e8f0cef33ef3c8f73cf0d4f3a0f23af1eef3daf2a6f624f620f138f08ef0faf268f320f7bcf29a0672f412f2c2f354f02cf0c8f65af29a41e6062cf2f4f736f428f702f388f28cf728f81cf6e6f190c4d2f01af4f0f616f8021426f83a0820f0eef31af808f6f0f078f3acf80e063cf43af51cf436f1bef2f0f3b4f102f010f00cf7fcf724f6785110f2fef6aaf48af058f0b8f63ef87cf274f708f4d4f34e01485030f350f5c0f282f52cf6c4f460034ef786f448b2e2f198f1b4f6b6575cf602f552f244f328f60ef876f258f7b4f50cf742f220f458e19ef6520746f460f6acf89af02a0176c6b0f6a05144f234f312f20cf550f51c9108f, 0x380f576f8680478f068f84207baf46ac35ef21ef71af254f23ef0acf588f5e6f126f1d8f170f678f3f8f1b2f1d4f652f668f4c0f404f09af160f6a8f024f898f12c9036f158f2baf188f038f4b8f360f182c848f880f818f0f2f534f6e25100f564f55af5d03288f51ef116f114f772f0d2f45ef744f194f45af7f8f0a0f546f166f5faf02c0886f406f214f092f1faf430f442f2d6f7eaf680f470f504f3b2f6baf1ccf6c0f284f0f4f7c8f74ef006f604f67e52def5a2f046f612f5c490f6f790f782f7fc029cf0ba53280580f228f022f302f0c4f262f0f0f186f6def58cf768f3caf36ed10ef0caf35cf72ef414f688f516f8aef146f872f41cf622f1d0f6f252f2f492c2a8f008f13af68cf418f4aaf34cf812f862f506f870036ef4f094baf09cf3f2f3c2f168f368f27af222f582f610f474f16ec25ef236f8acf424f272f6e8f048f53af748f644f064f86ef004f4a6029af184f4e2f112978ef480583af1a0f7e8f266f124f5b6f0b0f37ef5aa688cf798f8a4f6daf344f4bef606f366f440f3aaf174f80cf2a800e4f0ae5794f230f26ef140f782005ef48cf2bcf8a0f4bcf002f1b8f464f56ef052f438f4def056f6fcf042082c015cf08af2ec04e4f58ef5b2f46ef4cef75af318f16af7a0f28ef570f6e4f1ecf1c4f29a3028f], [0x36e0b9a788d27541a38eba02c1e712535f0e604bde827edae45ab784472fa534553c8b8d8ebda718f1e6305b0e5743d742d5b94324fe39671babd50075651bddc3433ef7184e6f0d1d03dddb76b9cb183d46a4e7b0e4af3dd8baa7aff29af845031f048f0f5e81d1e9b735fd830441e53430bd2008f9c06348f39623f2dfd41bd201a4b9ba29af29a23d66dc2ed51c14d6a7837bb628b56ecad743e1c95df26a28f7872dfde9a893eddda24dc342aef7124e6e98129bd29a24d9a426bd7769fb700541bc7988f5bbb71378144e5ebd53c6d669d6dc4a4f1b776bc364e426f9c61e4ec213a2f4628b9e53470be1130b7aa929af5702d36960eb761a0ef794d26cf66294df0e586bc478215b71221761e535e94cdebe1133cbc39397d790dfdf089bfbe0085d3c12397d818491e8c5145e2814d785d05c729a087cb54175dd02ffba18349d36e535b0e5f53ca69117c48616f516535eea9d03de1b7f794d29af1e6085ceed6add2985d794d264f6f69aae9e09ccc8b8abf329628f83049df049126d298c16c1805cf8729e3700561bc7785db4180ba783ae31e53465bdc61cbec50523b36e3bfa6dca6be051277ae229ab37a45fa53483bd782e878c111f961e6936eed3c6e2837f7a3124fb3ac093ab6ca6bd54855da1d37bb7769aa70d1c63ce5939ba5322ef4f023f712a1a3d7a988f2c329af740ba1ecc4155d6d927d9b429af37a551f061d03e0c19f79880f9e844b56eba060bca68517c395ab7396693ac34a6be00af57a2405cb29a421ee3118f965139dbc1718f86803deb10a6be1a3147c54844f894a4b6534893d2982e7c54764f6fe305a8c5126ce58efe9cb0bbd48075ae5d82ebce582eec4429af2ec174ee81126d6a927da3829bd6960aae55893f97a9cbead529b75c8535e30417360c3bb7ba06f77802691eb5460d5bda6a994d1def888cfee72c22756a939ba4529af830535e758ab3e0e8ef7b14349b59444b6c353076114017a3829af66272fa9a81a4d2014d3c12523b5d04e5f129126d740c16c22228f50609f6e55c65e1c9567b9d7197872a776a0d29bd41a78daf0506b83a23d6a2c93ed7405d7c445ab7894ba1e5342e9e039397bb16fef894dfde914debdbb139ba3a221d802db1e57893f982a78dc4d802f6fe535e8902eedbb14d796c043e894ddae53477b9679b7ec1822ef890d02f0882cbe1a1277b305d0f, 0x628893672cdef53522cf4224a6f48c902e5343dbd8db14ba53448b8020b9e69041757a959f2781839712cc4e6dc60f584a6ada83397d4b0759a3bc10b920240b94d0e4f6fe9e3630410b56694ddc334a6f616535ee819cde1a434794d078f872491ee81416dc4b317b315d0f492535eb0c70ed3c02eda5529af8246dfaba03a3e0ea6a7c39517b86823df0742ebca687179cb0bb53b8535eab5306e2508b79b736fd5aa49eedec915d1894d7a60481737a4e6ebc141ed5c127da0b29af831061e53479bd6da60f3bb4d57740a4b6c513f6e2a14d7ba04a6f872961f1158a3dbd94d7a2413db448873706077b994af579cb24fd48c535eeed47ee254017ad50e37868759ea3c93ed869a4ea2422f949645fa91921bdfd0ef7c1d348f5c4535ede4a6dd7a94d7b7f22ef5aab42e924a6f5bf8c17b7924f75d0b55f060d0bce5939aa0b105d8709f9f129783ca68877c344c0f48049ee53410b93514d7a2429ab83a055ee64def60c3317c1837af882b56e53475bd20117ec33449b872902e884a6bd741d67b0933fb59e693712a0c3dd91d67bc9776f5d06ddb029353dba1d6bba06fef29a279ea88226d5689eda3a349b4d44e6e7888bf598b0b7b0d37bd4b0451eec5126d2023bbc1c36fd86845decc129bca68fe7c223c5d5d06ddeeed205e008c16a40183729a3e1eeb929bd3c1a0db9d37b75ea94df075453e094017b9929af7189e370e5126cde943eadb4f1b894797aba0debcd214d7c344d4f776bfeee80a6bd7405d3bb1505b480892f0e567ed6d14d7c124f1b66e535e8f4a6bd29a247b6329af628902ea25356e0c28b7a9d04fb5169ab6a24d26cd21537c1d374f84503df089496cde8b9ba603b9d830c51ee80e8f5c4b31ba0b22fd868265eb6cd87600b8c7ad537b7802a19e9e09ced821a4ec0f26cf844779ee5d41bca68fd7bc829af132261f07541bd87a6adc183acf506902ee80dede111deec34776f82c9a9e7c01275742d53b143bdd29a51dcfb9303dc62d5bb14417d869049f12929bdbfaf57c4a67af8684e5f1519edd200c1aa30348f480292e6dca6f6111e26a2422fb392535e72ca6f5d023ae94d126f844577cb5460ddc61d5e94d182f4800b8f089cebe214347a534a6f45c691e7c0a6bd65117dc1d83af4966f7adfc223e009d97b143499762902e788a6bd120efd452525b3ac747b004debd67910dc184c0f, 0x8023adf08987bd30198f41d824f4a6691ee30bd791d14d7b31493d196329eed4a6bdc49363bd029af802305e5e8bb3d0c0d8ec011dee770e32eba047bd120c1cbbb29af5aa535e534153caf117f2d524f37187d7b120a6bdbf88f794d1b0f2b24e7ce5ca6bdd538c79cb29ad7b4111edfc9cbd7114dd98411ef67a4e6eff877bd2005dbaf0506f830175eeed9edd3b14d7c225e0f824793a891126ccc14d7ba05ab76f2534f061353e009397b305ab7328305f060ef3d8a1b7ec0f29af2b2535e7d42275bb112bc4a72ef4f072f3048b67a0928edc4a397d4d46c3a9189cdd9794d7b144f1b83a759e23c2ecd41a24da783adb802535ec6d305d2aa5379391cf74b0535e89053edc4af07ba0397d59e693294c77bd1214dda3136fd818a0df149cbbe111b7e9bd194f866a3b6b90916d71139dc50397d6fe6f5e9e0a6ae0c2837bfe1cef3a2535efb84f3d61a6adb76397d868174e9e1306d299397b1b5eb76c62e6f088a6bcdb88fca8e4c1b76272fadc493dca688f79a4169b4ce535ee30a6be00b147c4a67b7844565e67ca6bd1d1a4cc22116f6e2692e5342cbd6694d5b6c29af348341e860def5e83c979cb22fd83a305eed57aee0e8cb7b7929af1e63bdcae0a6bd7aac3dc222bcf29a069eba038bdc6240bbbb6fef6fe981ed2ca6bd2985d3c4a890f844583c53413bd2009eb9a426b972c6dfaea9303e0c0c17b14349d24e387711a1a3e2534bbbbb6af74806f6e72c647600c017c1633ef7769ab70e545be051227b7637b729a22decc0dbf60614d7c1d776f776aa770c60ebce59a0ea24273b2f4535e94ceb3d20224dc2272ef894b56f12a063def85979bd0a3d740e26f089c4bcd094d7a78183b628bc369008bdca690f7b294c0f844779ae05bfbd96a537c4a29af86899df0dd3c6e009177bd0299e29a111eec8a6bcd2117eaf55d0f87294df0d1823d2c117ebc55d0f29a4d7d07477b97411779b7273d740d8eee55355d6a9a4b9b719bd4d451f70e60c3e00b347a7805cb36e49fab3c93ee0e9397c1802cf662b8b6174109d30156f422481776294df049bfbd1619ff2d329af83a67df0d0173ca68c57a583acf662902eb5541dddc14d7c2251db4a6285eeed67edc62a2dc4a83af5e0535e770d27628c18788f05cb845075f06077be251e4ebc9740f792c51e6dc1776253df794722fe868a3df0042ebe25161f43411eb, 0x662165f140f275fe0ef7a53480f29a021e9a84c3d121d6dc34506f860902e7585ebd25912eb144a6f80c441e558a6bd7aa40ba584a6f37a0f2a620a6be049d67af5513b872a3de5341a3d3c1a4daf024fb59e693a90077d9bf9cbeb374d578023bdf0757abd479a4dc18824f474893694ca6bdd0258ea5311eb5aa75aef20eaf4b614d7ad511f7732983afe877b9ce94d7b7f4f0b5aa6deaa74a6be25422794d13ef4a649deba077b91a927eb0433fd812535e89077ed8a258ec181a2f5aa6beedfd39bd7aa46f3a4449b5ea757a758a6bca69227a7e29af5d0a0deec4a6bca68e77c2c449b6d839ef0040d3ca68147bc836fd824cfeeb556adceb1cbec18718f7fc3bdcb6c9cdd298c17a6a10f736e45faa0cdbf53c26adb234817612535ec51743db1939bc4a67a783a6f5e53490bdfd0d87c482bbe4486f7694c4f3ddc26abc18462f480536e9249b74ee1bdec3929af29a3ddeded3c6d3c1cbdc3983af5e0493694d0fbe092d5bb7429b78449e365342ebe039127c20397d802eede890a6be1c9e5ec39506f5c849f6b3ca6bccc0abf2d54d574a63bdc9e02ecd6a82e3a4b37b75d0691f0891d757226a9b315ab78029a9e7f08bf62914d7bc729af8a50e5f0e547eddda537a4029af7406f7a758dbf61ca8f5b8926d75d0ba1e94d205dfe0e17c1d224f87d005f058d23d6a877bb8c66f785b061e5342abd8a14cf22405db5ea6dfb1292c3e0c2f57a240bb3844ba1e9810c76251367a6036fd6fe72def213c6ccb14d78d11a0f29a345e9e08bee008017ad536f74f072fb0d16dbdd014cf4345eaf396535e901124d24939ec34662f830ce1f0e42cbe008217b0a397d66e6f6eb5447ce0094d723a349d51e535e534a03dba14d3c0624ef36e23fa8d49174e5939ebbb397d29a305abd56addbfa6a794d002f4d41576db4a6be0e9177a60397d660902f048a6bd752e87c4a6f7773a9aae6dcd974778c1e35b13d783a551e8e88bf4a68b97b315ff75d09a9e8b0def8e588febbb3cbd740902e72ce5f625339bc3936fd492535a5343e3d7a9e1ec39844f83ac51f061cabe0e8c16b7f396d36e3bf8f21743d740ef79b724fb72a67eee54a6bd30224dc09228f844759f089126d6a917b9b724f937a6dfa3cc2e9e29339bacd29af67a535e6f4a6bdbfb31794d168f63eb56e534a23d3c127da4005d76e8535f089fabd4494d7c18182d, 0x29a51fcc5125f61cb0b7c3967f7672535f07598bdd01b7eb7422975d0535ecc4dbf56c26a7c34182d3484d76fd45ebd351577b8c6fef888787ac1130753c14dd94d272f4d48936e04a6bdd814d799f2737496535efd4a6bcfe051eb7950776629e3706047bcdb85deb7422f7868535eb5477da0ea607bc8397d74078bae813c6e2a28fdc543cbd5d4535f11e0ebe25240b99f22fd4d494ded6d305dca9bdbad536fd6283472620c23e111f0ec34348f8a478bb07584bd3c0efd4445d0f6fe3bde9608a749c935f40111eb8946dfae3129bd781245c336797802361e89060edd01bda94d156f6fe49df049205d4188b7b7924976f69ab708925f61c961f24337af872ec9e65060b59ca6ab9bd2877872787a9e04b6d141a4b9de37bd29a4d5cd4038dca69177b7f0ba74d472fadec9cde0eb397ae44d5b8a09e36ec53c6cdb871e9cb1dfc776587d1299c9e1cae4db3129af29a2f5ee30dbf60b1bd7c4a2c1e628a2f68c48bf600b317a3824fd83023d68e0927541260dc455fef24e1f3c618a6be2a161f448517b29a389f129d93d3f127da8329af4804e6eb348a6e2bc017bb5349b873005edfd8a3d782587bdf29af7f83bdcc50e8f6221b7ea3029af29a039f0d0debd849a4dc4a662f776757b0e5a05d00071e9d122fd894a476dfdbfbd7226abc1d29af3bc535e94d1dbdbf8477bc85ab736e693ab0cd26dbfa787a834fdb608535f0742e9ca68217a6a36fd802981ee31126db61bdbc12679767a6f6f0d060bd983297a6a4817868489e860a6bdd00cbaa6a28f329a265eb6d6c3cc208f599f24fb8730d1e5589cfa0c1537c3917af718a0b6e64d27525a40bbea116f894559e9188bf53c139b9fc29af4f0177694c47be00a187bea29af458693d0cd205ca69107bbb5d0f6ae535edd8def5bf9c67c1d48cf718ba1ee249b3e092537b4062975d0981e69093edd637f7c39712f29a135e89047ed3c0efdba03f9d29a4d5eb6d6add7a927dacd22fb718db2e9808bf53c273dae8364f4f0535e534743d6a85dba4043975aa534e534173d200efbb7122f729a50fcc257aeddd8999a24349b782eedecc0a6bd98224daf5449b29a50dd0d2113ca69277c3981ef55249f692cded611418794d248f61ebd76ba093bd9e260ba2424fb790f05f0188bbca68457b312bcf718a4770a600bd2321ddc4a2b2f802759e980a6be1a05d7a1929af, 0x29a131f00447be009277b31449b29a51df07447be07b317a46397d776533d12a04bcbd04df1a40cd95d0b41ed5c43dd821bdea4011f71de23f500473bdbf9d67c4a76af6fe691ef917abdbf88f5c4a732f330651e7788bf57408f5be40e2f2bc535f060d23e0c139794d1b2f80e45de3042ed4a69147b3063776fe175f0e1d03ddd9b7ea78089b4f09e36b5477dd2c1146c3329af83a49de94d201e1ca8b5b57273783ae81f15ca6be092e87a2422fd628ae37074f13dc4b7f7b1429af62872faa0cacbe241deec343baf6a0bd6ec51726e0e82e7af0248f844d02e534413d1221fdb3f5eb76ec6f6aee0deddc4a587c341dee6fe3bdcc50aef971136db7f05cf2f0535f005d03c7782e744a672f76a9ab69008bd4a68247b8c2bde3960b9b12a1cbe039bd7c21776f5aa982e534a1be1a33d794d0ccf5d06dfaf417fdd9c939b95922fe4d48d7aba0173db626abbc15eaf37a50eb1285ebe29160f2da4d4f844789f0e5dc3d7f939bc011c2f], [0x4c0900a69d30253448b6286908be5c494d26c771872ca6b5dda6a05d347469093e6113bb4d534925349b35d038c37b56286902ec58a3143499844e80ded62543951eb830c50d2258a1a429b95ea53493aa008ef182c8689a89c9d9831434991de30447e1d01d637b56286909ae5c627839795eaba16a9e2533105c7740918ded5d01bd225547053492353014d22ed18217417160eba037a5740e24a69dddb144d537769a8170dddb044d53844758deb6253bb4d535ea6dc93e58a1a43499830c50d265e83bb4d537769a8914dd033137b57769a860cdc631434997769a8a69d7aad536f56f69a893cddda6a4cf318223c17262533137a7868eed354dd01bd2875628bd4d265dda6a1df27406f4d255dd94d28ee6285349ab9dda6a27337769a877cd8a1a40cd97406f447d61ca83348b776e80ded5d01bd05d58245341739259bd273529a3cc10ba1a3bb4d4b71872c9cd5c494d2727740c50ded4de94d22ed5ea6dca6b58a1a427397406f4ded47788f05ca7769a8a6cdd01bd11f1628690a6add01bd29a529a3bc47a93014d22ee29a30447a5c637f396d4c0901124dbc94d24877769a88bce1cc22516b8447581735d01bd1df57185349c9d3024022f5762e80ded60e9bd27277185349cb9d0314349962869077e0a682e042e712cc4a69dddaf029ab6288c4d2652c14d22ed37a5349c9d3513924f34d45349c9e0e9bd22ed7184e42ed97a92711fa7769a82ecd7226a2733628c2cd265d01bd24f529a4e493b9dda6a33f3628690a6b57aae824eb776e24a69d8a26a3499628bc0a6adddaf54d537189e0a6ae093a037b518223c2ec5e83143499740980ded52c14d228d790eed354d7aad524f34c0890a6addda6a24f37769a860c4a688f0ba3776a0d354ddda6a3ad37406f4a6d57aae836ed7769a9354d7a94d24ee8689a893add01bd079583ae80deb60eba037a77406f42ed61a3bb4d437185349cd8a68ef0ba67406f4dd553014d22fc1de23c2ec98a2ff34995e0a0ca6ad6694d228b6e85348a1d98b143499776c50d266253143499776e31354d7814d248b8a8eed354dd02f537b5740e5cded6111d6348d776ec9354ca68ef182c8023bc47a9dda6a37b37769a81a4d8a1a41839628980d265dda6a29a3872eed354d7a94d24fa5eab54a69d7114d26cb628960a6b58a1d63499872e80ded60c1a424eb4c05348bb20931434997406f4a69dcab14349929a3042e96112603acd7406f41715c637f2727824eed354ddda6a28f3895088f1358a1a424f934849c8be5c614d272662869068e5dda6a4c137406f48bd57a94d24eb7769a847ce253314d4734853493add030937b55e053493ac778c10bb459e6908be47785d05c66286f4d265d01bd29ad4d453493ae008ef0ba68950899c9e0c314348d740e80ded60c314348b7406f4cfd5ddbbb4d537189e09cce2538c66278a4e80ded58a1a405c9844c50d265d027e37b5740a0cded44785d05c3872c50d2661caf5506b62869017661ca834d4b868eed351d8a1a433f93485348bb53022422f97769a84ccdbb1bd22f5718dfd3c2dd01bd1975872a0c172d8a1a41df962869088660c1a422ed29a4e48bb9d025829ad890c50d265dda6a34937406f49cd5d026a37b57a0e80ded58a1a43439628690a6a62543967a7776cc5354d302534807776e81354dddadb4d534c045c60f0a692722ee, 0x1d014d286e6286902ee60eba037b54b0758a6b5d01bd18351de3041730de93922f5628a0cd265d01bd1df47769a8e8ce1cc223bcd894e80ded53025322ed7769a8a6ad8a1a411f9], []]
  | 6 => [[0x2cf8c2f3], [0x552f04ef7bef2acf868f2f4f1e60054f349348cf5b6f7eaf4c111d6f11ef24f35fef168f182f3bcf4c0f5e0f1df0182c616f342f286f83001def5eaf430f48050ccf7411662f72af1eef1a2f890f53af0f8f6fef5d00156f2bcf5c8f71905d0f374f8451672f516f20ef4fcf29a050730aaf3b8f86804f0967af396f330f66ef2b2f8a4f1831612f894f22f1088f05c0272f116f4d4f1c2f0c2f6ecf696f506f712f5eb3496f220f29a151ef36ec01cf028f068f3f8f5077790f04206c6f740f844f812f4489660f36ef416f1e6f77731faf24f04c10586f66378250126f1cef37b1010f6f6f172f608f628f1b0f104f4cef81ef474f764f18af26af26cf702f76af2d8f762f28ef4a60718f4b0f09af8a0f448f776f3a2f4d5310ef732f6aef8aef132f05cf61af22ef7776034f11e98733512f72ef3c4f228f74160baf5aa56fe083af33ef37af002f3ad7830f8a8f818f61ef27363e0f5eb0872f37b60bb63ad173af4a6f570f042f396c462f1dee310f349117af6291770f87375d4f22f005d7663627308956248f866f6d8f802f078f629383a029b07a0f348f4d5611f30b2f29af7d4f4aaf825724ef888f84570ba53acf196f719629b713cf8020824f59ef0a2f480f048f0e2f224f244f4f0f5aaf8957], [0x628307f0e4defe24439faf53adf81849fe45c8a7d8a1a4c9d60bb71de387c86077f89385df88f003f8a912be758defe2502ef8ef1cff894e33ec50d27d30253f8ef1d7f7760bbe174175c47887daf50e3f37a44be9802efe0905df92711ff1de307e98077f8778c1f35711fb7a0e83ee302edc778eff9170bbf29a0b9ee80a6fe253bbfc39349f628307a75847ed7a94dfc121dff74023fe3042ed5c626afc5711ff1de0b9ee3060f5dda6ad8c105cd84423f6e802efe0c1a47c0922ff6624e7e4e4917e1ca60fc1211ff4c023ff15c60f4938c1eb8c11fb11e0bbf12941fe25314f88f0bb3348307acc5357ca685d7a6a4d5f27223fe5349cbd3505dbba0287f18223facc57afdef85dbb14349d37a3bfe30460fe09331fa6a29bf4d499ff0e42efc8b88fdb8c37bf7406f7ec50173cd20effb305ebf7be177e6f49cdd988c1eb31183f24e3bfe174173d7814d7ba04d5f506a0fee3198fe1c917f9bd29bf330307edb077f99885db9f005df7760b9f12998fddda6afa6a37bf86704be98060f4d2110f85d003f3f8176e49c77f8eb0c1fa834cff894537ee8093fd98260f9391dff8950e5e5349b7c1702a79a411ff29a307aae060f61108ffb8c507f77651febd460fd4194d7bc8719f7ea307b088eb74d20d1f94d1e7f182007a5348a7d7a927db8c5ebf872567e53477f89385dbb8c4f1b18223fe690d27ca688f7a60349f3483bfc49c47ed618eff4391dfe82406be3bc60f14e82e7a601dff6620b9e53477be22412fc33845f11e1f369808bfc7782efb8c349f7ea307ec50a6bddda6a98ef003f1de176cae060fde42f5fb8c397f2724dbea0c47eca68eff88f117b34823f712a1cfdc638cfbbb273f29a535ee309cf9d8b8cfa4b273f5ea49fd1282efe1cb31fb0d507f3ac0b9f128af7e1105db8ef1cfe5b69abe53477ba1c94dfb31349f740983e954eb7de83bbfc12719f05c0abecc48bfd3008fdbbb1dff844a0feeed41fc7785dfc39507f11e23ff0489cfd98a83fc3967bf844307e86077fceb114f91705df8689a9e5349b3c8b912fc344d5f0ba177ecc447fc93924f94d1e6f894307add88bfc9c917faf536fd4c04e7eeedc67cde8cbfb140bbf11e0b96cc4defd35139fa6024ff7766f7ea0d307ca688ff9a433ff3ac49fe9a84cfe09127fc011dff22e45ff1289cfc93910fbbb765f6280bbeeeceb7dd01bdac121dfe, 0x37a6ebedec93fceb1d6fa6a349f11e177f074defc170277acf22ff7d423f6c5093fe2a3bbfc22183d1de0b9d14a257ca68c1fc2229bf4c0176e9a88bfd3014dfbbb663f718dfff128a6be091a4f9a405cf66249fe69093ed7a85dfaf54d5f6c6307e17428dd30117f3bb069f662535eec5307cd205dbbbb4c1f05c093e980a6bd30224db143adf776c53ea0c8bfe2838cfba072ff4c027be6f42edca68c1794d0bb7506307e534177d9894df8ef1b1f50649ff0e541ee2b82efb8c397d37a49fe3045efd7a8c1ebbb29bf8240bbe23c00ecde85df94d11fb62845feeec93fe1102efc52845f824537f12847fceb139fc393adf844693ee818a7ddd88fdc12777f894307e4e4177e251e2fc445ebf776177e534923e1c8c1e9d61dfe2724e7ebd56add3519ffa6005df776307f1218a7e24422f92705cf894176f0e5ddfdd02f5fc4a844f348307e0b8177dc6139bbbb1dfe8943bfe8e893fc4787cfc3911fb628176e4e47bfd8226af9d6183d4d4177e0b810bca6927f92705df11e20b6690d0fd35127fc571dfe5d4a0fe6f4177e251d6fc393bdf4d40bbea0c2efcb602efaf505df824a0ff089307d72139f939183f272307b0897afcde9a4fc2229af84455be5342efca6939fa83349f8a104be4e4897d41924faf511ff628c53e9a877fe091d6fc39719f732cc7ee808bfe2528ffb8c6fef182177a3bc70fd0588ffc50895f1820bbb074debd9885dfc22719f4d448be30460f4a685d3c570bbf71823fe0b8123c2e84df9a424ff7a0c53ee802ede1cc39f88f05db8720bbed2c177c9c85dfc22777f844a2fe17428fe1caf5f9391dfe5ea49fe23c173d418c1eb6c1dff24e48be9a9307d419d6fbbb777f05c087e3045a7c93927f93905cf894023ebd541fd8a066fa83273f3ac23ff048a6fa1c939f9bd33ff4c0307e4e493fc7785dbbbb5ebf22e307ee30a6bd849bdfa83343f712537f0e5d07e008ef72604a6f74023f71288bfc77801f381663f3ac177f0889cfe11314fc12825f4c00b9ecc18a7dc605df85d0ab75ea45fe758177ddd85db9bd183d1822afa0b813fc938c1fa8311ff4d423feeec47fe25260fc3924ff4c06f7eaa42edc9c85db88f0bb71822e7b00477bdab88ffaf55d0f11e22fe690a6fe1ca6af8c105df11e1776bd57afd8a08fdc18349f22e23fe758d27d98861fc39506f718983e9a847ecd202efc220bbf, 0x6284e7ec50defcfe05df94d24ef89423f712998bdca9a4fc223acf66223f71521cfe11422fa4637bf824cdfed8c60f55485df8ef11ff4d475bf0899cfd8a30bfb8c273f37a23fee30173ceb14df9d629af824307ae80173e091bdf8ef11fa6284d7f00477f98a1a4d9bd29af824e83f149d07dd003cfb145ebf71875be45c77f930117eb31663f24e3f7f1121cfd7a9bdfa6048176283bff129d07d7a88fda6a2737718113ea0c49fc6082e7c2205cf3484e7e1742ede2b85db85d0b3f4d449f662047fe2526af93911fb87308beeece8fd30260fc12513f66275bf0e6113dd038cfb8c1dfe5060b9f0cd307d989bafa6a183d662983e45c77fe07939fc4a825f872176e17400dd3502e788f10ff4d43bfd0482edcde82e7c4a5ebf7404e7e960a6fc17001fba029af3ac687eeeca6be110effba0349f5066f7f15c173d8a283fc22663f29a23d653460b609314fc1205cf4c075bee3093fca691779bd11fb5ea4e7ee8198fdd002ef8c1169d770a0fec517ffe251bdfbb1741f7769aaf12a257d418effc39629f1822f7b08a097d4194dfaf51dfe7406f6f0880a7cb602e78ef1d7e8940b9ee8077fa1c80ef8ef11fe872307e3042edc8b82e7c3905cf5eab57ec5077fa0908fda6a29af0ba157f0e477fccc0c1ea5829af1de177c174177cde917ea8305df740307ebd5307e113a0fc57183f3ac317ea0d357cd2117eaf50bb722e443f0e6097c6088fcba0741f1de307a174171d418eff38c29bf6289abeeecd27e110eff0ef1b1e7403bfe5348a3e0926af9bd1dfe7180bbec51307e11117fac31dff3ac3bfe534927c2e84dbc1229af824773ebd4dbfc8b8c1ebea11ff4c0893f15c77fc7782ef1bd22ff82445ff04860fe09260fba0507f3ac45fee24a6bc608b9fc4a845f22e176ea0c2edd879d6fbbb741f8446f7ec50a6fd8a08ffb8c629f8ae23f6e3060fdc6278fb311dfe7406f7a30455fcde8c1f8c111fb71845fe82c47ee111d6fc4a24ff462693ebd4a6bd98a67f9a40bbf22e41fee80eb7e25331b94d22ff3ac6ebe5e82edc778eff39d3adf1de23f6e813f7d350c1fc4a349f740307abc0a6fcd214d7bbb183d8943bfc30400fd98b14f9f005cf182177f0e447fdc60effb311dff11e20be534a6fcbd05dfa60481f34845ff089357da582e785d0b3705c0b9e23c47ed7a9a4fb3105df872535ebd477fddd917fb3126df, 0x37a4e7e0b800bd7a82e7bb5663f84449fef21ddfcde9bdfc125ebf5eaba3e49c8bfd4e82ef98811fb], [], []]
  | 7 => [[0x1f], [0xbbf777f11fb37bf719f29bf11ff05cf507f1dfe29af349f0bb705df183d4c1f741f825f22ff4d5f5ebf663f895f273f183f3adf1dff845f629f24ff873f], [], [], []]
  | 8 => [[0x1f], [], [], [], []]
  | _ => []

def C5_S (s j : Nat) : List Nat :=
  qGroupedState C5_initial 5 32 11 C5_patterns C5_values (C5_counts s) (C5_specs s) (C5_records s) j

def C5_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C5_initial (C5_counts s) (C5_specs s) (C5_seeds s) ws

def C5_groups : List (Nat × Nat) := [(22,0x40a84080), (12,0x6000), (26,0x4a084800), (9,0x2006800), (17,0x2280000), (5,0x206080), (6,0x4080), (28,0x62206000), (3,0x84880), (20,0x200000), (10,0x40004800), (18,0x80000), (24,0x2000000), (1,0x2082880), (2,0x80880), (4,0x80)]
def C5_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C5_groups ws else diffCover 0xffffffff C5_groups ws
def C5_Z := barBudget 0xffffffff 0xeaa8e880 C5_cover C5_S C5_N C5_idx
def C5_flat := certAt C5_Z C5_N 9
def C6_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C6_values : Nat := 0xffffff00fffff0f0ffffccccffffcc00ffffc0c0ffffaaaaffff5555fff0fff0ffccffccffaaffaaffaaff00ffaa0000ffa0ffa0ff33ff33ff00cc00ff000000fcfcfcfcfc00fc00fafafafafafaf0f0fafa0000faf0faf0fa00fa00f3f3f3f3f0f0c0c0f0f00000f0c0f0c0f0a0f0a0f000f000eeeeeeeeeeeecccceeee0000eeaacc00ee00ee00eaeac0c0e0e0e0e0cccc0000ccc0ccc0cc88cc88cc80cc80cc00cc00c8c8c8c8c8c0c8c0c0c0c0c0aaaa8888aaaa0000aa00aa00a0a0a0a08888888855555555333333330f0f0f0f00ff00ff0000ffff

def C6_patterns : Nat := 0x0

def C6_N : Nat → Nat
  | 2 => 2
  | 3 => 19
  | 4 => 46
  | 5 => 34
  | 6 => 1
  | _ => 0

def C6_counts : Nat → Nat
  | 2 => 0x2000000
  | 3 => 0x500a004000
  | 4 => 0x1101c001
  | 5 => 0x21001
  | 6 => 1
  | _ => 0

def C6_specs : Nat → Nat
  | 2 => 0x201000000
  | 3 => 0x201381201000
  | 4 => 0x481481101
  | 5 => 0x401101
  | 6 => 257
  | _ => 0

def C6_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x4, 0x0]
  | 3 => [0x0, 0x4, 0x84201, 0x38]
  | 4 => [0x2, 0x22c04010084c18c0, 0x7448081a02, 0x0]
  | 5 => [0x2, 0x10a1058e4850018b0b, 0x0, 0x0]
  | 6 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C6_records : Nat → List (List Nat)
  | 2 => [[], [], [0x162c2a1c1], []]
  | 3 => [[], [0x58e664faa8b], [0x23613630538aa16561a463996978e89c5c682e391c5], [0x1648c8cce2c391c584e24621c5921]]
  | 4 => [[0x1f], [0x2bc5ee8b9d789f9be0bab77b765dbda7bc1e8f4dee4fa6ebbc97c7b73755eb7b1d7f70ed0ecb7], [0x70d5c8b5b04b4e2e2717538b9c64af338f6127bda9964acb1b248ced0ea9c49ce2f3a179], []]
  | 5 => [[0x1f], [0x13f6bfafeef89d3be75cbfbbf0ae3fc97edf23e97c3dcdf93e5ec3f85fb7e2fc4fb3f05f3ff4fdffc7e0fc6f8be], [], []]
  | 6 => [[0x1f], [], [], []]
  | _ => []

def C6_S (s j : Nat) : List Nat :=
  qGroupedState C6_initial 4 32 6 C6_patterns C6_values (C6_counts s) (C6_specs s) (C6_records s) j

def C6_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C6_initial (C6_counts s) (C6_specs s) (C6_seeds s) ws

def C6_groups : List (Nat × Nat) := [(22,0x40020080), (13,0x20020880), (28,0x60004000), (3,0x80880), (10,0x4800), (6,0x4080), (5,0x80), (9,0x800), (26,0x40020000)]
def C6_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C6_groups ws else diffCover 0xffffffff C6_groups ws
def C6_Z := barBudget 0xffffffff 0xeaaac880 C6_cover C6_S C6_N C6_idx
def C6_flat := certAt C6_Z C6_N 7
def C7_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C7_values : Nat := 0xfffff0f0ffffccccff000000faf0f0f0eeccccccaaaa0000aa00aa00aa000000

def C7_patterns : Nat := 0x0

def C7_N : Nat → Nat
  | 2 => 2
  | 3 => 6
  | 4 => 8
  | 5 => 1
  | _ => 0

def C7_counts : Nat → Nat
  | 2 => 0x2000000
  | 3 => 0x5001000
  | 4 => 0x7001
  | 5 => 1
  | _ => 0

def C7_specs : Nat → Nat
  | 2 => 0x181000000
  | 3 => 0x201101000
  | 4 => 0x301101
  | 5 => 257
  | _ => 0

def C7_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x1]
  | 3 => [0x0, 0x2, 0x21]
  | 4 => [0x2, 0xd7, 0x0]
  | 5 => [0x2, 0x0, 0x0]
  | _ => []

def C7_records : Nat → List (List Nat)
  | 2 => [[], [], [0x1484844]]
  | 3 => [[], [0x56], [0x426723411988c646]]
  | 4 => [[0x1f], [0x178de562bb3ddf0f], []]
  | 5 => [[0x1f], [], []]
  | _ => []

def C7_S (s j : Nat) : List Nat :=
  qGroupedState C7_initial 3 32 4 C7_patterns C7_values (C7_counts s) (C7_specs s) (C7_records s) j

def C7_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C7_initial (C7_counts s) (C7_specs s) (C7_seeds s) ws

def C7_groups : List (Nat × Nat) := [(18,0x400000), (5,0x2000), (9,0x2002800), (28,0x6000), (21,0x400000), (19,0x840), (10,0x800), (26,0x40)]
def C7_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C7_groups ws else diffCover 0xffffffff C7_groups ws
def C7_Z := barBudget 0xffffffff 0xeac0e8c0 C7_cover C7_S C7_N C7_idx
def C7_flat := certAt C7_Z C7_N 6
def C8_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C8_values : Nat := 0x0

def C8_patterns : Nat := 0x0

def C8_N : Nat → Nat
  | 4 => 1
  | _ => 0

def C8_counts : Nat → Nat
  | 4 => 1
  | _ => 0

def C8_specs : Nat → Nat
  | 4 => 257
  | _ => 0

def C8_seeds : Nat → List Nat
  | 4 => [0x2]
  | _ => []

def C8_records : Nat → List (List Nat)
  | 4 => [[0x1f]]
  | _ => []

def C8_S (s j : Nat) : List Nat :=
  qGroupedState C8_initial 1 32 1 C8_patterns C8_values (C8_counts s) (C8_specs s) (C8_records s) j

def C8_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C8_initial (C8_counts s) (C8_specs s) (C8_seeds s) ws

def C8_groups : List (Nat × Nat) := [(2,0x40), (5,0x2000), (9,0x2000000), (12,0x2040), (17,0x80000), (18,0x80040)]
def C8_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C8_groups ws else diffCover 0xffffffff C8_groups ws
def C8_Z := barBudget 0xffffffff 0xeac8e0c0 C8_cover C8_S C8_N C8_idx
def C8_flat := certAt C8_Z C8_N 5
def C9_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C9_values : Nat := 0xfffffffffffffffcfffffffafffffff0ffffffeeffffffccffffffc0ffffffaaffffffa0ffffff88ffffff55ffffff33ffffff0fffffff00fffffefefffffcfcfffffcf0fffffcccfffffc00fffffafafffffaf0fffffaaafffffa00fffff8f8fffff800fffff5f5fffff500fffff3f3fffff0fffffff0f0fffff0c0fffff0a0fffff080fffff030fffff000ffffeeeeffffeeccffffeeaaffffee00ffffececffffeca0ffffec00ffffeaeaffffe0e0ffffe0a0ffffe000ffffddddffffdd00ffffcfcfffffccffffffccccffffccc0ffffcc88ffffcc80ffffcc00ffffc8c8ffffc800ffffc0c0ffffc080ffffc000ffffbbbbffffb0b0ffffafafffffaaffffffaaaaffffaaa0ffffaa88ffffaa00ffffa8a8ffffa8a0ffffa800ffffa0a0ffffa080ffffa000ffff8888ffff8880ffff8800ffff8080ffff8000ffff7777ffff5f5fffff55ffffff5555ffff5500ffff5050ffff5000ffff4444ffff4400ffff3f3fffff33ffffff3333ffff3300ffff3030ffff3000ffff2222ffff2020ffff1515ffff1133ffff1111ffff1100ffff1010ffff0fffffff0f0fffff0f00ffff0c0cffff0c00ffff0a0affff0505ffff0500ffff0404ffff0303ffff0101ffff00ffffff00f0ffff00ccffff00aaffff00a0ffff0055ffff0033ffff0030ffff0022ffff0011ffff000fffff0005ffff0003fffefffefffe0000fffcfffcfffcfff0fffcffccfffcff00fffcfcfcfffcf0f0fffcccccfffc0000fffafffafffafff0fffaffaafffaff00fffafafafffaf0f0fffaaaaafffa0000fff8fff8fff80000fff5fff5fff3fff3fff0fffffff0fff0fff0ffc0fff0ffa0fff0ff00fff0fcf0fff0faf0fff0f0f0fff0ccc0fff0aaa0fff00000ffeeffeeffeeffccffeeffaaffeeff00ffeeeeeeffeeccccffeeaaaaffee0000ffecffecffeca0a0ffec0000ffeaffeaffea0000ffe0ffe0ffddffddffddff00ffdd0000ffcfffcfffcf0000ffccffffffccffccffccffc0ffccff88ffccff80ffccff00ffccfcccffccfc00ffccf0c0ffccf000ffcceeccffccccccffcccc00ffccaa88ffcca080ffcc0000ffc8ffc8ffc8ff00ffc80000ffc0ffc0ffc0ff80ffc0ff00ffc0c0c0ffc00000ffbbffbbffafffafffaaffffffaaffaaffaaffa0ffaaff88ffaaff00ffaafaaaffaaf0a0ffaaeeaaffaacc88ffaaaaaaffaa0000ffa8ffa8ffa0ffa0ffa0ff00ffa0a0a0ffa00000ff88ff88ff88ff80ff88ff00ff888888ff880000ff80ff80ff80ff00ff77ff77ff5fff5fff5f0000ff55ffffff55ff55ff55ff00ff555555ff550000ff50ff50ff50ff00ff44ff44ff44ff00ff3fff3fff33ffffff33ff33ff33ff00ff333333ff330000ff30ff30ff22ff22ff15ff15ff11ff11ff11ff00ff10ff10ff0fffffff0fff0fff0fff00ff0f0f0fff0f0000ff0cff0cff0cff00ff0aff0aff05ff05ff05ff00ff04ff04ff03ff03ff01ff01ff00ffffff00fff0ff00ffccff00ffaaff00ff55ff00ff33ff00ff11ff00ff0fff00ff05ff00ff03ff00fe00ff00fc00ff00fa00ff00f800ff00f000ff00ee00ff00ec00ff00ea00ff00cc00ff00c000ff00aa00ff00a000ff008800ff005500ff003300ff000f00ff000000fefefefefefefcfcfefefafafefef0f0fefeeeeefefeccccfefeaaaafefe0000fefcfefcfefc0000fefafefafefacc00fefa0000fef0fef0feeefeeefeeef000feee0000feccfeccfeccfa00fecc0000feaafeaafe00fe00fe00fc00fe00fa00fe00ee00fdfdfdfdfcfffcfffcfcfffffcfcfcfcfcfcfcf0fcfcfcccfcfcfc00fcfcf8f8fcfcf0f0fcfcececfcfcccccfcfca8a8fcfc0000fcf8fcf8fcf0fcf0fcf0f0f0fcf0cc00fcf00000fcecfcecfcccfcccfcccf000fcccccccfccc0000fca8fca8fc00fc00fc00f000fc00cc00fc000000fbfbfbfbfbfbf0f0fbfb0000fb00fb00fafffafffaff0000fafafffffafafafafafafaf0fafafaaafafafa00fafaf8f8fafaf8f0fafaf0f0fafaf0a0fafaf000fafaeaeafafac8c8fafac800fafaaaaafafaa0a0fafa0000faf8faf8faf8f0f0faf80000faf0faf0faf0f8f0faf0f0f0faf0aa00faf00000faeafaeafaeaf0c0faea0000fac8fac8fac8fa00fac8f0c0fac80000faaafaaafaaaf000faaaaaaafaaa0000fa00ff00fa00fa00fa00f800fa00f000fa00ea00fa00aa00fa000000f8f8f8f8f8f8f8f0f8f8f0f0f8f88888f8f80000f8f0f8f0f8f0f0f0f888f888f800f800f7f7f7f7f5fff5fff5f5fffff5f5f5f5f5f5f0f0f5f55555f5f50000f5f0f5f0f555f555f500f500f4f4f4f4f3fff3fff3ff0000f3f3fffff3f3f3f3f3f3f0f0f3f33333f3f30000f3f0f3f0f3f0f0f0f333f333f300ff00f300f300f2f2f2f2f2f2f0f0f1f3f1f3f1f1f1f1f1f1f0f0f1f0f1f0f0fffffff0fff0fff0fff0f0f0ff00fff0ff0000f0fcf0fcf0faf0faf0faf0f0f0f5f0f5f0f3f0f3f0f3f0f0f0f2f0f2f0f1f0f1f0f0fffff0f0fff0f0f0fcfcf0f0fafaf0f0f5f5f0f0f3f3f0f0f1f1f0f0f0fff0f0f0f5f0f0f0f3f0f0f0e0f0f0f0c0f0f0f0a0f0f0f080f0f0f000f0f0e0e0f0f0e0c0f0f0e0a0f0f0c0c0f0f0c000f0f0a0a0f0f0a000f0f08080f0f05050f0f03030f0f000f0f0f00000f0e0f0e0f0e0f0c0f0e0f0a0f0e0e0e0f0d0f0d0f0c0f0f0f0c0f0c0f0c0f080f0c0f000f0c0e0c0f0c0c0c0f0c00000f0a0f0a0f0a0f000f0a0a0a0f0a00000f080f080f050f0f0f050f050f030f030f000fffff000ff00f000f0f0f000f000f000c000f000a000f0000000efefefefefef0000ef00ef00eeffeeffeeff0000eeeeffffeeeeeeeeeeeeeecceeeeeeaaeeeeee00eeeeececeeeeeaeaeeeee0e0eeeee000eeeecccceeeecc00eeeeaaaaeeeea0a0eeee0000eeeceeeceeec0000eeeaeeeaeeea0000eee0eee0eecceecceeccee00eecceccceecccccceecccc00eeccaa00eecc0000eeaaeeaaeeaacc00eeaaaaaaeeaa0000ee00ff00ee00ee00ee00ec00ee00ea00ee00cc00ee00aa00ee000000ececececececccccececa0a0ecec0000eccceccceccccccceca0eca0ec00ec00eaeaeaeaeaeaeaaaeaeae0e0eaeac0c0eaeaaaaaeaeaa0a0eaea0000eac0eac0eaaaeaaaeaaaaaaaea00ea00e0f0e0f0e0e0f0f0e0e0e0e0e0e0e0c0e0e0e0a0e0e0c0c0e0e0a0a0e0e00000e0c0e0c0e0a0e0a0e000e000dfdfdfdfdfdf0000ddffddffddddffffddddddddddddccccdddd5555dddd0000ddccddccdd55dd55dd00dd00dcdcdcdcd5d5d5d5d0d0f0f0d0d0d0d0cfffcfffcfff0000cfcfffffcfcfcfcfcfcfcccccfcf0f0fcfcf0000cfcccfcccfcccccccfcc0000cf0fcf0fcf00cf00cececececece0000cdcdcdcdcdcdcccccdcccdccccffffffccffccffccffccccccff00ffccff0000ccfcccfccceecceeccddccddcccfcccfcccdcccdccccffffccccffccccccfcfccccceeeeccccddddcccccfcfcccccdcdccccccffccccccddcccccccfccccccc8ccccccc0cccccc88cccccc80cccccc00ccccc8c8ccccc8c0ccccc888ccccc0c0ccccc000cccc8888cccc8800cccc8080cccc4444cccc0c0ccccc00cccccc0000ccc8ccc8ccc8ccc0ccc8cc88ccc8c8c8ccc0ccc0ccc0cc00ccc0c0c0ccc00000cc88cc88cc88cc00cc888888cc880000cc80cc80cc44cc44cc0ccc0ccc00ffffcc00ff00cc00cccccc00cc00cc00c000cc008800cc000000c8ccc8ccc8c8ccccc8c8c8c8c8c8c8c0c8c8c888c8c8c0c0c8c88888c8c80000c8c0c8c0c888c888c800c800c4c4c4c4c0ffc0ffc0f0f0f0c0f0c0f0c0ccccccc0ccc0ccc0c0ffffc0c0f0f0c0c0f0c0c0c0e0e0c0c0ccccc0c0c0c0c0c0c000c0c08080c0c00000c080c080c000c000c0000000bfbfbfbfbbffbbffbbff0000bbbbffffbbbbbbbbbbbbaaaabbbb3333bbbb0000bbaabbaabb33bb33bb00ff00bb00bb00babababab3b3b3b3b0b0b0b0afffafffafff0000afafffffafafafafafafaaaaafaf0f0fafaf0000afaaafaaaf0faf0faf00ff00af00af00aeaeaeaeababababaaffffffaaffaaffaaffaaaaaaff00ffaaff0000aafaaafaaafaaaaaaafa0000aaeeaaeeaaee0000aabbaabbaabbaaaaaabaaabaaaafaaafaaabaaabaaaaffffaaaaffaaaaaafafaaaaaeeeeaaaabbbbaaaaafafaaaaababaaaaaaffaaaaaabbaaaaaaafaaaaaaa8aaaaaaa0aaaaaa88aaaaaa80aaaaaa00aaaaa8a8aaaaa8a0aaaaa888aaaaa0a0aaaaa000aaaa8888aaaa8800aaaa8080aaaa2222aaaa0a0aaaaa00aaaaaa0000aaa8aaa8aaa8aaa0aaa8aa88aaa8a8a8aaa0aaa0aaa0aa00aaa0a0a0aaa00000aa8aaa8aaa88aaaaaa88aa88aa88aa80aa88aa00aa88a888aa888888aa880000aa80aa80aa22aa22aa0aaaaaaa0aaa0aaa00ffffaa00ff00aa00fa00aa00ee00aa00aaaaaa00aa00aa00a000aa008800aa000000a8a8a8a8a8a8a0a0a8a88888a8a80000a8a0a8a0a888a888a800a800a2a2a2a2a0ffa0ffa0f0a0f0a0aaa0aaa0a0ffffa0a0f0f0a0a0aaaaa0a0a0a0a0a0a000a0a08080a0a00000a080a080a000a000a00000008f8f8f8f8c8c8c8c8a8a8a8a88ff88ff88cc88cc88aa88aa8888ffff8888cccc8888aaaa888888888888880088888080888800008880888088008800880000008080808080800000800080007f7f7f7f7f7f00007f007f0077ff77ff77ff00007777ffff77777777777700007700ff007700770070f070f07070f0f0707070705fff5fff5fff00005f5fffff5f5f5f5f5f5f00005f005f005757575755ffffff55ff55ff55ff000055775577555f555f5555ffff5555777755555f5f555555ff555555555555550055555050555544445555000055505550554455445500ff0055005500550000005454545450f0f0f050f050f05050f0f05050505050500000500050004ccc4ccc4c4c4c4c44cccccc44cc44cc4444cccc444444444444000044004400404040403fff3fff3fff00003f3fffff3f3f3f3f3f3f00003f00ff003f003f003737373733ffffff33ff33ff33ff000033773377333f333f3333ffff3333777733333f3f333333ff333333333333330033333030333322223333000033303330332233223300ff0033003300330000003232323230f030f03030f0f03030303030300000300030002aaa2aaa2a2aaaaa2a2a2a2a22aa22aa2222aaaa222222222222000022002200202020201f1f1f1f151515151313131311ff11ff11551155113311331111ffff1111555511113333111111111111000011001100101010100fffffff0fff0fff0fff00000f5f0f5f0f5f00000f3f0f3f0f0fffff0f0f5f5f0f0f3f3f0f0f0fff0f0f0f0f0f0f0f000f0f0c0c0f0f0a0a0f0f00000f0c0f0c0f0a0f0a0f00ff000f000f000f0000000e0e0e0e0ccc0ccc0c0ccccc0c0c0c0c0c0c00000c000c000aaa0aaa0a0aaaaa0a0a0a0a0a0a00000a000a00080808080707070705ff05ff05550555050f050f0505ffff0505555505050f0f0505050505050000050005000404040403ff03ff03ff000003330333030f030f0303ffff0303333303030f0f030303030303000003000300020202020101010100ffffff00ff55ff00ff33ff00ff0fff00ff00ff00ff00f000ff00cc00ff00aa00ff000000fc00fc00fa00fa00f0f0f000f000f000f0000000ee00ee00cccccc00cc00cc00cc000000c000c000aaaaaa00aa00aa00aa000000a000a00088008800770077005f005f0055ffff00555555005500ff00550055005500000050005000440044003f003f0033ffff00333333003300ff0033003300330000003000300022002200110011000fffff000f0f0f000f00ff000f000f000f0000000c000c000a000a00050005000300030000ffff0000fff00000ffcc0000ffaa0000ff000000fcfc0000fafa0000f0f00000f0000000eeee0000cccc0000cc000000c0c00000aaaa0000aa000000a0a0000088880000777700005f5f000055ff0000555500005500000050500000444400003f3f000033ff000033330000330000003030000022220000111100000fff00000f0f00000f0000000c0c00000a0a0000050500000303000000ff000000f0000000cc000000aa00000055000000330000000f00000000

def C9_patterns : Nat := 0x25591615655946156558559561565555454951525465152546516454951945915855

def C9_N : Nat → Nat
  | 2 => 21
  | 3 => 114
  | 4 => 957
  | 5 => 0x914
  | 6 => 989
  | 7 => 31
  | 8 => 1
  | _ => 0

def C9_counts : Nat → Nat
  | 2 => 0xd008000000
  | 3 => 0x103d032002000
  | 4 => 0x107a21b126001
  | 5 => 0x714b13ec006
  | 6 => 0x2f00e7006
  | 7 => 0x1e001
  | 8 => 1
  | _ => 0

def C9_specs : Nat → Nat
  | 2 => 0x381481000000
  | 3 => 0x101501581181000
  | 4 => 0x101581681701101
  | 5 => 0x601701716216
  | 6 => 0x681796216
  | 7 => 0x501101
  | 8 => 257
  | _ => 0

def C9_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x11003, 0x20c820, 0x0]
  | 3 => [0x0, 0x2, 0x122004a2401c320620d00503036a9d216802, 0xb635068218b8038b0083e4010ac296140700801, 0x2]
  | 4 => [0x2, 0x845535901dc0013a1e0d9001001e82bc09f82b400318ac1540508386003212606041600268067002401e21c2126003004b050400305bc001001a0918158004000800201680270004007001a04400340020592126004c00308fc00f0fda00e006801800141c900040210014063028005400d00528498041007001e00540440c44046, 0x80123350278b74370316001003441521b16f80d00a615502c80e801c03f056805806e00f0f8015c3b402a0132fae43321b000c6ac040001006002009600e001c63c20816900886a00843688af00040100f102b001c02f13a022801423000f001001800600404e825411814f88907ac078112005802802e01b017803c0470aa00e8018002012000c26801e00c026000400a00200b85380020af00c017438e01201602f801c036000808800207400204641e4025004008000800200d001c01200484880f000506b002037800206700100d800f01f00100ea000079, 0x19c9e8360f2028038060150cd518690384781103e85e0040308303c0440a8010380c41381b00200802034, 0x2]
  | 5 => [0x13, 0x23ec00500b3000487e000832a24123d714497758f4805e01dc0370024002057c8c101d04e300042c98e0c22703e400401580078da4180100c07901385720d3008e04f800303a80220008007002c0010d623620014028023817200d010c007c00201880080094001001c0070004001000c0208fb009d134a361015824b07b80ed00080698bd802a00062e100463ec00140b6001801c0430012008c15b00e001b080000100a801800040028b280018aac0150008194022c4e800280b5000a286898807b046c02d00a001000040060064062016c0ab05f80df002c05d002000204bc009001002e002c028000a1e6000401b01a806900180d58fb001b006c00f004c005000c078012012a0020058000811800121de00a003400380010170002000400102f402802b4018000400b024408300e000100ec05d003c0050018040023c05f00c4045029800c000403b00a8127865802f000421000c403c859000500160d60950004000411a00a0015001801700bc031000c003009e0ac01f800200081d382a005c00200100014048001003a000c0010050068004c004000400100080030590002015802f004c0d28008027001800200040250018003, 0x1b5e000807700140b309e027c001015b019c020058440b92a24b1003855c2fe400b020018e1c40e9100e8079079004404e030c001e4b1929c02c0064027000c054002c01b92740d40f0006f01d40520006391020c13f000c09107284dd00224b1000802e055c10805d0002002400b0476389001803e01fc600000416301ac1f80b6c01e001a3748dc80020086365098c01d000404a0ae4016034834b000c02f007004900ac00e0040002033400e00780cb0f562ff005c04d92c401d005000200b405700d000405ec39f002001c06bc194000400f00140b800a0087000811001800040078095004406b002a2e603180028b0000e001a237887c008047001f00480330190001006c12287b61ea002800d01a4062085001900403bf0054007000404e001c01c009c04192c414d05c400501904c4875e1b084a40080440008000408d00040030250002017c0210008054843c00d001000c000409a84180a5004e0e800dc05e0038256822802a00100cf037803a0024035023000792c401c000c005000c04d92c40280ac4026000c05b001403802bc01602140070150001003801292c40808204009002401a006c00e00200040004001001802800040090008015001401281c4006067000100100010004001007800f8134011005001a01c800102ac01f002400701b800d000801780f409100040aa005c00502e801192c4001009a00900a8062077c0b9802002200e8048, 0x5d502a02508e66822d00205008700b02100924b04400700200b86601702a08903700900500481b0020010b7, 0x0]
  | 6 => [0x13, 0x20738048000e010814b82d181ce000c01a80cf018800c001e807c003e00040f904fb0020000400082ce0012005802c808b4da400f400300500009008858a8001094c043c0058011000400300fb800300080f3c020000100020010002816200fc03f00358003000201840788001, 0x23b88c8b7800d022025c8eb26a0f849a00420bb009a68c01039092b80c52b2409002893c00218801a800400a02202780890342c940a800401e00297800103700e100e02bc1180019780174e8a0040028c7c3240af001008000e1fb00c00b400203c9248004002005002487c05600406c0ba804a04c00b12d8342839000818827000614180a80e611f026001415f2f0023009c00402304e80800a604f01d80146a520d08f001c4a834f0ec840800812007a800c01803a978481c00200890081546d200d005044400204300c45bc014068010806c4ee1b187c00d81e000d003851800620085f0028158008002c2265e000100280e4002083035800404e00f01b00dc2b707d0008134004017002cbc20b800c81b803009602b81a814401e19201f800401800105980180fa0038088020014001, 0x0, 0x0]
  | 7 => [0x2, 0x199f108401004018340a, 0x0, 0x0, 0x0]
  | 8 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C9_records : Nat → List (List Nat)
  | 2 => [[], [], [0x43485448d506051a94122c82a825b84c84b1ce8850d1ac43893301], [0x1699d12820716660ab820fa1822006fe6b0aa021a19827c07166b0aa016e9d128207f4854d6021799828205ba74c990205a0c28208486a89902111ac2640], []]
  | 3 => [[], [0x5b8b7127], [0xcc13ec38b46c5716b3c66b0aa61c5aa21bfa35896feb746e2cab996b1ac4a3946a58446b12b59600d849a98b8428268486a930d1638d929d22a6a27f23544ca90910f28df941a43427c65ba5cd502d1c94e8941a4245903710744b02ca0993a156542f4725716b746fe90faa1121f541f43033a64fe8d696e8d6ea1b538b5a635c055146a4abe1bdadd1ae3480a5ba74d2e11330d0fa1a51ac28b87167d8b0d11b95c7a422c2f2826], [0x1fd1ac264865e714cc05c0a663a21816744a0921a2392a4485ee3ccc056a9ac2a884c06b09941369ac2a8835869caa221221f396884886cd62205a394181702744a0920599828244666c8a0912aa1822103a2530a092121d128244f653099090a9ac2410848b849909fd2c035814cc744a0c0e89412784658744cc05601ac2a90874b749909902663a214328549009c0aee33015aab00aa0a1238b3581816e3d0905901d128247f487d0a893c95426425aa9809909771982830868e28cc050c9ac2408848dfcd605fd1ac2a8838a660aba1fd21f358838a6b0aa21fd2e345a2868b74a08a1a2d32822844b8c9909c5ae32a828688d8a091c7add3a21466830d90605a392824864e2ccc04e994c26444186c8a0c21a1ac2a88816998a0896026d2a82], [0x107ccc1322200]]
  | 4 => [[0x1f], [0x53db4f7b57b74fdb3add128f7c2f4577732f26b7385d792f57f72dcf82af618f427b812f35bd2b9e6c97488f1f0f18af12cf52bb6637569b3d9d43bb5a7b19cf67d742b726d74d3b808f2bbe7f0f466f7a4f2dfe67f7738f335b3afd796f693745d7832f2b7e2e2f46dd7acf3abd2ade5cf747172cfe61ef273e691784ef5bbb2bde6657628f545b4f1b3e5d571b517b3a1d204f410f42fe2abe7e6f6c17734f630f35dd790f72ef6a97776f7b0f66973e8f719752db7aaf83ef533b708f2b5e5d0f293e1f9b2d8f786f7dcf7bcf476f3d7d49f7816f3b3d68377baf4a0f61172c1e573b47af830f2d7e2afe4c7b6baf3d5d43de511b4d5b47ef283e70ef4f5b794f4b7b61577eaf6b5767b7729779af78af56bb3a9d4cfb80ef824f1fd7626f6c37762f1add269720af484f51bb4d7b339b295e423b7177842f65b7818f49af80cf54af337b291e20974cdb7bef45b716f766175d3b6fcf65d75caf597b437e15be5a1b513b59fb33fd3a7d722f2f374efb389d58cf383d4d1b2d3e539739dd4d9b6557429b359d7c8f2b3e1b1d5a4f531b3e2f6f975b6f195765f7297e766f844f357d67777c0f1eaf4edb852f7caf31ef7ecf52fb620f59177d8f6137425b7e8f287e355d1f7b65777f8f3f9b419b58373daf421b6f7739fd6957302f594f4cbb60f727de6977726f7f4f5bdb5817653762cf78cf5b0f5acf281e1b9b1bdb, 0x30f761b77f2f45977a8f387d480f828f704f4fbb343b7d4f432f515b3a5d2d5e15de7f6f447d6cb742de85ef503b840f0d8f3c1d6ff7445d5aaf3f2f702f285e6ad746fd4ffb58fb4f9b7c4f], [0x76eb7570e5929dc5b6c3b8b295683e85dce2d6eadc5a1bb40b2ace8446616e2d6a9dc094b722d35954cc52f4fe5332d6e9accc2f71e742e856cd98e8d5c59d4ab8146cd7f488dae2d901cee998cb8b702743e55350d1929e05a392c345bab7f4ca8ed915c4dfd157730a47e75a4505cad51ce605941b318358d4f64ca6fe93c2d961d4aaae35998169d96e2d6e8e0f9ce6c066fa781684970190bb9c0ad359c0283c2ca4cace90adb9dd94b722d2a5674e6b33091702e05a1773df45a77965adcfdcac39b9141b3814ccb35809f2cb0e89da8941b1982539816505cf2d45ad6e957d27c2b5a630849703dc59e05b7d3bef6b47716550efe9b09d3d958d3fa546b7f487d4ded0dd90d9ace43465e765ebe8eb5d16da059413b7e358d4cc8fd6b750cad7d15774243a6d868af8f02c5b1e1235a3b2b425383ea8d6e05b21e0fb5b3add283a8688d9ab7472adb2141b3fa574b6f6530f07d092d6b954729745b369484a6e150965eb33f3ac04cd37e887dcb7516cd931d3ac244f2b81086dcb7536adf3aa25c0958075808fcee05092dc5a333add5aeb738e2ce8cd169d77141b23f436e7fcb3d6e71362e059d36b9c282e6c2aea7091bd9dbda669a393655848e2cee2cd655b0a669c084f2b8684c4ee2dc29d60141b2792b7a46c8cdab8d6b2e121acca1535957028b4eb7539adfd0db5ac02a965aa9816e04ad396e9d15b8b114765099a68b511d5c58ba3bfa35993a2506ae05362d77239a9ac2a9946c5078e05771d62a2db3f5472d7f4b8d6e0545ad97957b41f45a76cc702aeeca0b9dda665c06264745a72eb07caaba05a393c2f264742a84a707d931db3158b2e1265642454b49cd0fe9e8b8b3b7527f6816e2cee71092dc29d16ad504eb7424fecb3d604d16a17b3f46c2746c8b6b02d959d59932b38b2a475bab02707c991d0ca125bee26475807b2ab756dae05b2c3b264f737f4b4570bd979e059cd6add28fa7f487dc88d06650b9ace3f4574b8169996f2ca0b9faab55a3f282e5c65534ea8a0d8e994c6a1b425a71ee10e714abb96a9d06b81380d5aa505c99911e5fd1d26bfa45a743e72f8fe93dad8c22d3b5a298783e88db07d3dae05b263bf7716765c6b2ab54f6358c30a3a8b283a650506c9550c4d862c03bbb716745a506cb74d3ad68954d43459eb5ba6556f7d4bad59998cacf46d9816e3ceb751fadc79d1a9ac283c, 0x7388b4edb0e9b60f9ac6bfa424b5ba9057088991d3c22d9b81358d8489916fe8d6350d94c742432eb71674ea5041558d2932b33f35954cc56b488ca0f1d9ac03bfe65874cc5074e3cdfd579a12cbf75bab5fc6b330913a2cd6154c3cb4ccb7ac7b1ab74e5ae0438b3b7f35955ba8db2e2d354d0f920d2dd4f2b3a2506c9e4aa2dfc2236ac04e735806b2a5cca639f735b39d32b1c5706b328650a9e059413424436e5e666330913dad68a23ca2d4193702b00ead4d66595a3f3b8b283639a55f8fe90fe9652665b812d6e694a5e702cea360437b3c015bab5aa6b1afe4a0b93d9d3cba43a8d446663307ccc2dc5ab89ac056b34184432864d63594239abaa5bab8164c8eb55601e1938b3c1f4f8b5bab556c296a9dc5add3b8a33197f487d6998d665d22dd5b815bab580742af6d6ead9f9ecabdf69475a65074a88e2ad8c2c03bf8330b5ba56f48fcd635bea799bfa358b47254b907dc59e1a141b27c283a7acb00e6b09065eb1ac6c225c6b83eb4568fd092e0fa665b645bb346683168b5094cea15be43465878168e5ab555c2e1a38a3bf85a2b5ba70f302d6eadbfad53a2d31b6848b85702d169ce8941a32e3a154c087f4fe9c59d06141d1f638ad8168e6ae04151db627b5a1240b983ecbceff96eadc5b283a3638ad42a442c660abe9c5a3f3b8b25e777ae2ce6b0a3f1c594c3c0b6cc74c06b3285c995a0f94172fa5bab574553502d6f2d601c4abf76c875aa51dce2d961d399accaf835997ee735a9e4ea660fac03ac042f68288496e2d219d9615bb1ac2a9c466505cf9d6eae05b2f3ad5388d7f49996c616eadb0941b3fa4eab716e1ceb01094dfab663a17425a5aa8496e2ce0551fa366b6a2836748e2ce9b116ce0fa755b6656b365e714ef7d092dc5a669b81282e6fa85ecc29094d1c9d1aadd38ab4cc8b66cb168cd8f1a9cc1445a7612b766848d6661a2a25b8b4253436865d07dbe9d5d1cdcb2f331342472f2998b5e8e8941e4224f6b83ecb8f0bccc2e18a7459ac2a9a5bab596ecd6eadfd1985bfa2b6e4ea55f502cd635d3b8b3b2f4eb3874b756fbdc59dfd2795b033539364506ce05bd9d62932b30a359565cb54efdd5c2e1a3883aba28fa7f4505ce71332dfd2dd5b3f5aa73a64caab5567adc0a7c5b8b5bb365e736aa5d1fae05ab55add0b2b5aa8b4ed291f9e05ac03ad5436e7ca6616b55332d3623f5a663a39, 0xdf4e8d6049ac6ae328ba716e10ecad3c4d679c55a18221c4f65316fe9601dd99ac6a3f45a74245074fe8ac394596bd38b2787816d6ced850fd9ff2366a7847eb766711afe8d625f2aa35c1f5bab44684b29b0a0e9fd38c3c342aee], [0x848e2ccc0e1a2cf26438685509919c79d12985816e3d330dba9ac26548489e4990e122e3482a5806b090460f9322206868c81330e05a392645849004d625819982838716e05330e05b8f2826848b01368e059b22826716b74e28ce29b2283471ee04e8950a99822147f4b8cd6261a38f4865716c0ccc4605b8f3a2571e998e8c61a2e32a8a7f46b09026121c5358947e8b5090ccc1542218848e2d320e07b8b3305472830d9450fa19240a5c6b54aa2a121d1330986903d1c9571a2d24123584c890620fac5264671e744a0d0d614c24183a24c888520fb7d3303702998d90dc7aee3311848b00d6461a38128266eab749949c7b203a256eab54991971ac02a92868530a09a191c5330943e854904a1a3814cc37f466088261a14127865aab00d615c09b22826868b755f0e1a32c33035bab55600e1a23626457f4b8d600e121ac2a987f4b8d25a96aac024034728ccd9160f9982643868744a0d21a26628328489b4d6250f9ac24185c69b4aa2a122d558037f4b8c992a1a3202826816e3d2596121cb3309816e3ccc16122d5358984886ccc2a1a38f5ba38685489918d91982834848deccc0e00add264a71e8fcd916059322206702998a0a971a6026525c66b0aa621238f3a25869090a09a1a4243589716e04a09a121ac34e95aa6b090260f99822095c68fc9029719c52a8a716b74a60e1a2dd264383eb44990e05a3936457f487c902a1a40f282683ebcccc261240143ea71e848d9450613222184726c8a0d1fd21f330a7f4b8caa2a1238b5c634cc6c8a0c96ead53589702c0ccc261d14c2646], [0x954cc1322210]]
  | 5 => [[0x2ef94354], [0x84f060f182f492f31cf206f1daf82ef0e2f2460004f598f694f332f28ef74cf260f316f074f1bef67e5670f7eef06ef1b8f304f352f192f244f318f104f306f118f6a2f74af0f0f0dcf376f08ef430f058f3caf20ef3eaf630f1d0f13e0536f6145048f31af570f142f2c4f068f6def174f6c2f008f0def462f86af1def882f4a8f580f03cf2a4f6bcf224f656f38cf2c8f50af020f4a2f714f388f49cf210f0bcf550f064f29af36af3c2f40cf2f6f59ef5806400f2e8f64cf7fcf1a4f516f258f4b0f63ef32cf846f5b4f5c4f860f050004a04f8f83e33a6c25ef12ef3b6f358f760f29cf168f5a8f3a2f468f24ef81621dcf42af28cf4bef7f4183e4518f2f8f780f4cc9146f13af616f0a2f446c3cef424a150f7aef7eaf65ef60af0a8f6b6f738f394f776f5daf800f60cf2b6e4e2f21ef18a011af28af46cf3d0f296e4e6f10cf756f014f088f7178300f59cf25cf460f264f330f090f42ee6c8505801dee0fef12cf156f54ef1b891f4f0bef220f2f0f6eef24cf5c2f11ef23af534f114f1c2f16af252f68cf226f14a90c0f844043202d0f4f6f1eef112f876f0baf310f08cf454f1ea0540f7a6f36cf85cf730f498f822f1ccf4f0f0e8f36ef648f688f2fcf0e8023cf766f72af184f46cc116f10ef26ef2aef836f516969ef84af164f6565200f052f450f1445880f58087faf700f472f236f784f0c2f030f43ef, 0x6b8f0d0f4b2f016f7caf788f17cf870f4a6f53af7c6f570986cf248f80cf45a56d0f40ef68af4e8f7b8f7ac0266f2e6f6e4f646f2eef298f55ef810f2a2f7b4f378f160f374f586f0cef5fcf2b6f03ef59af13cf854f658f05ef404f7bef6c2516cf440f56a94e4f856f1d8f06cf072f102f106f47cf24af0b8f3e805ecf528f18cf5baa7d6f0faf6d8f5fef176f77ef45a732af0f6f33cf5aa344ef65c523ef57cf64ef752f878f604f5c6f796f50ef042f034f758f7fef2c6f080f694585af12691caf07a50ecf754f3e8f338f3e6f4eaf4c0f288f42a57660520f746f424b28311a8f7e2f09af500f66af370f6ccf75cf848f130f7f43858f636f446f62af684f166f408f0f4f7f0f702f01e0566f1a2f07ef6e8f778f56ef412f044f87ef526f37ef542f3b8f5f6f3d2f772f2ecf632f328f4aaf362f4f2f862f122f2fef2aee3a6f028f3a8f26c56aaf168c2faf350f27ef73cf2daf79cf552f51cf7f4f1d2f1e2f276f5f8f5e0f0c6f82cf7d2f05c0544f254f4b4f02a03389562f398f02ef04ef18ef3e0f2bef1cef05af214f152f640f622f75af158f6e2f35ef710f1b4f7f005d6f7e0f4ccb600f6faf312f012f1a6f0f8f190f01cf340f32ef308f046f14ef50cf12c078ef2caf554f45af864f2e207f405faf76ef5aef06af83ef30af4aef576f188f5e8f7960802f81643f6f17cc5b2f866f63cf4f0955af19ef, 0x748f560f4c8f250f2eaf0eaf0d6f07e0634f036f402f61cf7cef3c4f4acf11c9320f432f00ef040f406f30cf816f52ef4bcf6ecf082f42ef324f7165278f108973af86ef85e06eaf138f262f368f41ef36a011cf6d2f7e801ecf702208af47e26b2f7b2f466f344f698f81cf0e0f10af770f448f5aa1740f010f47e1826f7ea04dcf6a0f154f240f5f4f0380486f44af01ef0ba56a4f5dcf062f64af3def04cf5eef482f120f83af148f614f6f4f358c2e0f096f322f650f504f14af1baf77cf314f850f05cf804f70af222f4baf7acf844f608f5449506f196f508f702039af742f21cf868f872f642f25af63af190c4b8f2a0f5bb96daf6b0f04af0b2f71ef7a0f724f11290daf126f4def720f360f6c8f45ef4f8963003a8c84cf076f494f52e90ae5388c16ef00cf19af0ccf44cf442f22ef134f256f4d89478f392f12af0aaf026f6cef33af0b6f3bef558f834f0ee5136f5f0f678f7e8f098f474f48af548f37af7ca0372f0f2f6f2f7dcf056f418f7a2f2d6f744f2836806f216f092f34af71af16e5380f87af38ef6a6f776081ef3c6f1b6f496f4d8f588f466074ef58af4c4f5c8f1fef638f81af2c2f416f1d4f674f1c0f5c0f666f76af70245aa0874f2f4f364f53ef6e0f358d56cf7b6f4ccf296f2d6e21af1c6f0b4f1b2f238f3fcf5a2f3f4f070f6b4f464f3d8f2b4f348f4c2f6d4f3faf09ef390f578f87cf, 0x2a6f162f178f3b0f5e6f366f242f624f83cf58057dc03fef1a0f490f2ccf3a0f750f0caf09cf592f6c6f038f77af132f41cf5bef232f522f5e4f54cf3ecf3f0f546f29ef38af424f22af1aef424948cf22cf76cf68ef452f230f6dcf274f1e8f228f03af0d2f34ef1d2e820f556f56af65e5602f17ef716f15ef798f172f70cf100f02af4daf65cf1e0f67ef5e2f37cf62ef71671e6f41af0aef524f7be041896f0f66cf814f07af1c8f40af4f691f2f202f14cf180f79ef2e2f26cf80af0e6f45a648ef0a4f359317af6f6f564f584f13ef5d8f436f66ef3eef094f1eaf3ccf212f59e9198f6c4f2fa9686f18af054f144f018f282e0d4f5ba95eaf75ef1c6e736f0b0f1aaf69af022f4b007d0f672f8160282f438f71cf6d6f270f838f346f680f01af5def002f3a0c0e4f436e73ef6aef078f07cf3baf0c8f0acf2b4e246f2a8f72cf606f0e49396f7def326f414f006f110f6b457ccf218f1d6f7daf5ccf050f47ef774f124f4a4f782f574f73804e0f5baf0fcf69cf20cf0a6f108f7e4f186f0c4f032f34cf1e4f6e6f4cd5066f1c4f83e0024f3cc53dcf80c0706f6f6527af5f2f00af6bef02cf3d8c0eef51ef5d4f85ef2b0f086f0a65140f234f3b4f170f3bcf5aaf644f47e0764f768f3c8f55cf2e4f1faf0a0f], [0x4244836e3da8dca082ef26605db80c64de87c8879e0b8bbb814aaf7f446de9b5336d1f88e5bb95bbb8146b3b07c2ebe1226d7c0f3a2f44e84b69542aee0fa527bc2297e817005e72cd9751922dbc1f265787c753afdca63d518b1da39365747e174eee9d9bdd1b9c7c0b364f8489cde848996e07a12dbf84aaf868fe9ec8116dd77198dc3a26577f4425f07205be17b037a41298f86856fd0d05d3e031b27c342a4f49684b6f945f35c7b72bc34283e47e661efdc86bdfd13279ac241d848f6dee3ce8dd6a8be6a66241b7f4239e998cc6cca94c7b7b38b742a662eb756eed49855dc0b0ba74cc5074c0ccc6d09198d93209be63eb55e5c42e9ca0910f3034cdb71623aee71c7bcc68a9f3ad5aaf5ba9b76e0571bd3694c7a66239b606a8f707c883e1a22dbb756b778486636e2dc09dd6b66bbad425b11c176707916dd3c998dc0b05cf17c176a9cca63dfd11d7c1f496f4cc99b702cc9be171d0eb81330f71e99b70d0d674e594c7a12299b7f46616fb874bdc08e9742445b77544caf07ccc2e0fc01794105ce47242fa8e488761a3287ba75c7b869091f0c8cc6dd6b46bc347eef81f02decfd71de1841f7ac036574cc2fb6dd5336d6014cba1b38be7020f1f09171edc7aeeb9ac05dd52e92f6f6ca63d902c0bb6636577fc531e6b0647560110ba3f1d2f7f4955e7a028f5d1941f23f47ef6fa99b70c8e2bd7c198dc2b58177de395f0e93ded8fac0bc0b2a2f7020fde8b42edd67932dad51d2f81ef9deb00d65e0da2dbc012b1e7ce2e9eb0038ddc5998bb4a13972e85c5e9d52aedc082e7c34265745a2faf07d903cba110f3fa364f71e56bcb0074d9168e9b434816f4644caee045f35c5910ba2d36574968b6eb54cc3d1fa2d3b1c47ef33046f69b4aa3e07bfe7c243a2f570533702d25bd168beabfa298f6cc42ef0f13e6c7488ed1ac241b5aa4c9e66058ed1ca2dbbfa5c6f7f4e3dec811b75819f7e9411d3e580aeee954435e1a3a77c3e65976cc507d090d66516920badd0bb382c84b68e5066cb583cf1b2283e796e3df0d1c2bdc5b2039b20a3d640165eb452aecd61a7ea3f45af6fa6caebcd336dc5b20bc1f11cf83e23965489979ba9acec344f7b8164c9e5c42ebd2aa2dbc346d8f526663644069f5c79b2bad1581771e89fae042e9d81a2dbab8221b83eb8de8b5095d57198db2047ef7026c9f0e9935e12212dc34864f, 0x7408fdf0d16ead71a3f7c3a848f864be9ec816eed819cdeb8b36574242fb23085bdd8c24b7c0b38af864737aa885f6ddd1acec2465d77f4663700516ddfd1547ad5359d6ea5d3ce2d71dd6a82e7c247f4f8169d1efe874b96e92fdc344f9b802db1e8b5094da3132bb2038af81eb02f090abf962a4bf22d11d363ec61f0f8adfa07b8bba2d22165800bae8fc4e3c9912ef320359d71e703ae2d325ca0932f434425b848905ee04e2bca093cf3a738af81ebe9eedd6abe121acea5512cf5ba2fb6dc8995ca091cf43a3a7d5ba4cb687c84f971addda66283e7dc385e8fc993d77132b9f411cf606b776954d674a08bef38b71775ba715effca0f9c0b757a1205db7a2715ebcccc76123f778f61eaf7f492de714453e0325578ed1b9b71623a65608879168a2ba2d45b77ac1c5ee3db55d79a4bec1f17cf38a507cb7536bca083cf38f45b775a713a9e125ecc6932f3f4240f60652fcfe8e4bccc027d9ac331d42423b6e3cd6751f9c57c1f38af38a531ee2c5f5605b037a1214bb4cc1766a2c1e6ca612ef2b5221b868b777090e5bdc093c7bc2776f4cc3a76b8cd675c5afebae32a9b640b55ec0d1cf516910ba6d47ef71e0aaeb00905e05b287c1f12ef5bab57692ca979600e9bb185c6f43e483cfbce2bdba932bc245aef4e69577004aa3dbda6dbb814cdb2cc4daeb00995d21a3f7ba3425b7024c9f0d11cdd2a941f2dd38ab45a82af03d16de00a1ff3c24cdb5aa2396b8d6abe0fb2c7c01702f4da8b6ec0d605cd90b6bbf5264f49672fb090cabe00a78dadd23bb3305536b8d16ddfa90b7c24581780274fb07d36bd6792fdc0f3bfd844981f0f9d23e122bad99326578169b5f0d19d5de88597a23237d71e747a998476e0fc0f7add17d97f4fe9ee04903dc582ebac017d5868cb1f02d2abca6141f42e5aaf282483cb7521ed2598df40b02af3580b9b091d23d62ac0bac034975c609f68e519bdd69d4e9c0221d5801def0056abdc088e7afa298f71e84b6b8ca3f8e6910eb755bbb45a4caeb54d63d1c9b2ea33264f86899b6fe87b3dc088e5a664c3b81e507d0f1c0bd2a998d94c0b2f43e4836c0d096dc5a6dbaa2175b282176d0d0ad7916a12da17365e5ba177707c903cd91ace8e905ce47e84969051fbd25a3f7add5aab378663ab00475e0f91b7c0f47ef848cbeeb00d6756e90ddb032afe5aa9b5ed6c70dca6147f4243a1d, 0x5c6b02e8fc173db0910bc0b75af868e3ee8fc4fbd6e94cdbb36eaf75aa4f68fc74ba0f94c79ac0bbd5800b8eb0136de0594c7a2d05d743e856eb556abe12141f424716f4aa88fb02c883e19275dae34e7b748715ee2ca61dc5b81bbbd702f716531f07ca9bdd6a66dc24702f4242fb70d0e9f60795af385331d38a2dee7d0472cd6132ec0b26573a2531f02c5f35c0941f3ad4f3b8684bdeeedd6be0f278dbee1d2e6f6662f02200bdefa4b7bfa17cd38a093b07c173dbaa2dbbfa05cf8688fde9992aecd6071e9d1331d4c04caee2c86ddc5995bc245bbb43e4834fe8903d219c579c5379d71e8fdf07dbabdc0a665c24754f5ba3b76db0e2bdc0b037bf4220f7f4661f0911fbe059987ac038b76c8716ecb0cc6d3302e5ab5265b7f4b8f687d096ca088ef23f0baf6eac9aeb5ca63d51a55d99825db7f4dd5edd4e275ba9d3ebdb114f3380bb685ccc7a07bfa7c242b7e5aa92de7b038f57f2e3dc34702f816239eca12add60255b9ac11d9774b55e8fd06be1d36c7b8f283e6c2482eb7474ea1e15af3ad6597849005efe992bdd6a2dbc234cdb7166bef02c633dad0e9b30e581781eb776e3cb5f951920da6d04fb52e2736e3cf474e29527b75425b47e531f03ce2bd602c0bae3425b5aa239e8fd093e1241f7bfa17cf47e239f005c5de1e266dad5364f5c67b3ab74886d6aac03a12365b70a715ed6874ddfd01c7a1241bb7f046de980cc6d1f8be6c0b640f4da9836e2dc0bcd6110eac52657640507c2f81736120e57c34581747e441f0910fed941c57bf5364f3583a78ae8906dfd3207b5b365783e3a5c92cd67590212da120bbb868d9ae86ccc7962932b40b6eaf874531e4806ded719c4e8e917dc848e2ce6b074f5c59d1bbc2702f26c0baeb54d3bd2aa17f30347ef0ba0b8e6b04774d61acea12415b702999e71497bcd90c57bdf138f45a0b8f07c2e9dc2b817a6c497b848b476a885f660f80f7a73331b83e661e85cc9fa121c57c0f2afe4f248368fcd93e0fbad7a36265d6eab02f0d1e8bd3a920dadd241b6586cae8b4cc5dc7adddc1f398f69492ef02c903d8fa2dbac03595816e3df02136be17aee7b6a265747e8a1ec7d855d02998ec243a9d63e6b3a8fc5f3e07b2bbba1717711c0b96b8d306d6e88eda120bb346c533a560907a041c57ae32a9e59e5336dd4ac78cc120d998103d8026b3b091c5de122d579b22657, 0x5ba9b568e4a0f9fa1987ad50e8f614b8eee0474be1a2437ad75aaf28223b503d6abdd695bf147221e81ee2deae884edc5932ba1f432f6248b6eb5438bd85303b954221e330443ae2d903e0f212dad5576f45a716efbd36bcd605daac033178489e56e71babd6a9107b81298f81e165e8b4a65dc58bebbad58177160b8ee04883e07b2fbbad702f81642df02c991e1a32cbbfa0ba775a8fdf0902cbe122fa79bc26574aa84b6e2d2ade0f9323b263657802b776ff9903dc0b817c24547b7ea441eff897bddd2c0bb18606f640745e8488865fc1207ad54aaf6ea87fd0f93cecfb9f47b6421b75c655345fc3e78990e1bb66265745a272ec80155dd514c7c3481ef330507d03d3e6e1a141b9200f9e75ae2eeb55605ca0941f431816f802743a714e07533132da66079b81e6b3ab8ca0f89b02e3ba34d9b7f49b5f02e05be1a1547acc4cdb7163a6d069fd3e05ae37c24816f6740aaf004a0f933141da1b32be746e05e74488756a8e9732059fb4cc3a750d1903d06132dadd05cb844dd5f00595ddfd3037c0147ef816745e9985f65168e9bc0165d7496507c99925edd9ae37c0f702f4cc7176848172dc08be7b81496f6ea9ef6ab86dee059af7b8f3a35716c0ee8b4475d5d198dc0b1d2f58092eec0cd6755c1c5db9c496f71eb55ee3d45eca60e57c1f264f6c2662e6b0a6756ead57c0b5f0f4f24caf0d2043dc085d7b6429977f4715ec0d3aedc5920bb85497d6c8442edd51fbd94132bbfa44ef71e52fd0913cbda8932bc345aaf2e8137d0b20fbd6a85d7c1e47ef2403d5eb005f5dc594cbba7331b446483a44054f899110f43483ef868b75e5489078e5998ead538af496817afe9d6be0588e5b814daf83f07df0d05b5d1b12feb8f487d868d6ee77cce6e058e971ac349d878507d02d193d33093dae33a1d7f49cdee90a63dc01aceaf85c7b47e84b70b9975d0f9aceaba359d6b4396ecad25de058be7c0f71677f4441f07d79be1a1d4e9b228375aa531f0e5fd3e07a66dbcb078f71eca2f03d3c6e1932fbad4283e7ee715ef08a0f97197ff4241b7b81e737b0b8d67581941f2d517cf38a2e9e734d97600add7c1f58af64099b6b8c906caa132f401298f2983736cb971dd62932f34610d77ce531eb002edc5f08ecae355db6a22daf02dc79d68920db205dd783e2f9a7dc8874a08eff35b4ab783e6636864cc3dfd05d7add1d3b, 0x2d5580f6c2426e3a42eda1d158f38b27f781e8e7ac7d1fbdc58c2ba6d283e3a24caf07dc7bd79998dae34cdb75a52fcb00474e00bef7add4abb6fa64eefe874bd028d3eb8b4837868506ce2c1eddf28be7a79298f45a8a2e670172e0f9b27b81640f38a6b3a954995dfa1097ba34cdb5ae4cbc8fd16ddceb817b725bbb80259bce8d16dd6e9a9dadd57db63e84b69b5096d5c10ddb8f4f9b80284b69551fbd6a9ac6a66299b80299b684874e9c7a6cd94117dc71692eead485ed961c57ad1237b4726cab0d0a63dc5b75b966043e6fa956ee59096d71a41f4244ebb4cc4436c2925dd6ea4bdc247cef7163a6eb74cc6dddb037a1238bb5ba71770d1beddc7b8bbadd0e5b65ec0ef0056eae12287d94c043e80c661edb136bdfd36a7ae3465e56a6cb69b4453dd9bad7bfa11cb5aa174e25c4b3dfc1327b7b32b75fc66366b090656e9b2db81282e63cb7770b9605d11932ec34748f868cb0eeb56eecfb881eb035a3b3be093add56abdba941f3814c2f44e6636e2c2eddeb2e37a12139b83ccaee9b50dfa0088a7c014f7b83ec0de9b4d675331b2dbad359d868e2eeb54903ce29547bba389d42484b6b74aa6d79998cc017f4f7ca2c5e6c8a0d909110db8f702f75aaeb70c8abf9ddb8f7c244cdb75a507ccfc38dd1f9207c3464d7282177d07d3cbd3305ddb7d6eb77f4b8d7020cabe121acdc347def816e3eec817d3d6ba4bf40b0baf802b02f091ff3e0f9937c1f4aaf6ea9b370913ced96132ba121d3b634b55eea9c7dc9902ab9ac17dd868229ec0d6abe0f8e97b8b38b7702505ee8d1fbc630c57a8704fb64c956ee3d605df3b207add05db], [0x21a42426478489b52aad2a932221658a954995a07b8b38a781e71417360fa55330b71ee2dc09cd9132221617c23817260094c264e5bab54a62c748be0bb4848b8caa6971ad55807848b8ce2ae1a4244f2b43e66090687488e0bb284900571ad71add5aab848b8d604d6e9c5298b71e6c8cc55ba94c26568684c8979c4705d05c381e714cc35ba9320bb64726c899558199811d986903c991e1238b38a7716714a61dc79b2283671ee04d91e1a14c264786903dc79e1a38f29875c6b54d634cc132221c848b8d6aadc7b81282e5c6b00904e1a42465875c648047696ea6d298b4724c888705f05d05c5868e3ce8d61a13222164968fd092e0094c05ce848b8d36ad7194c241a868e3d901d8199822195c6b54902c5f08e0bb1848b8cd6652a99826531d2238172925a2d4253869091c79d719ac2419868c80991c748be05cc868e3ca0da059b22647816e3cd91e12401330b8489b4cc2d0f998221c71e998d94dc7b814ccb8486608865c79b20bb586909171ad71ac03595868e3d334dc7b03331957466088660fa5526474968fd169d79a5533196fa954cc4d71932241a848714cc2e1a32005c71d2174171a1226d05cb802b74a62dfd198240b33048088661a2dd298b4aa660886571a4b241a869090cc2dc7a4b365571e714d955c5b2038a75a2954994e1a38f70276ea4c88859c5b8138a77f4b8c902c748be11d8606714cc661a3204aa76cc4c88859c7a66283a848660caadbaae32656], []]
  | 6 => [[0x2ef94354], [0x25ef81600e2f7cef39af641a869a44ef124f26574db43312299a6d4f4c0f6ccf75b41d2f2650220f6eb0848f028f64174daf25cf184f47e00aaf58af4cc912ef048f5aa071f71b6f7b6f152f068f64cf11cf4ab416cf09af71f238b229907f404aaf45a5482f574f497083ef63ef580584945c703bef034f81f2042f81ef264f546f11d443ef21af496f802f784f864f4ccf1c2f849a6e4f2a8f002f05c047ef882f6eb72e8f088f816f874f1ecf6b6f74ef3657716f380f2b0f746f32af0baf0c2f0b2f04ef1daf4249810f396f162f5f8f868f17d2472f23af2a4f35ef36525aaf6eaf054f216f5baf464f486f378f28ef4ab7078f114f38af650f138f221218cf1a6f10cf754f3d0f878f1d2e580f5ba985cf4f2f212f364f5dcf0f8f102f5f0f01cf1d305f4f75af358c80308697716522100bb73eef70af17cc83e071ef674f4a4f33144dba174f87cf5fcf5c6f3a2f4eaf0ba5774f330f83cf5c74803a6d8f81fa497250ef68cf4e6f7f4f640f5e6f010f55cf0a2f358f241031af6faf1caf748f5aef326f702060721e2f7fcf282e200f75b7240f702f11c9282f6daf7a2f298f236f607417cf2ccf424f7eef658f38ba40af606f45af24142fef05cf198f7def526f05da5a2f6a2f0ccf], [0x8489b5e6c8c9fc17027fb7517dd1d20bbd09136fccc02e79b22657240477e0b8173dd1b75fc4105cf17c0bbe1742cddc7998fb20299f8486cbf0d0887d718befa55497f220427e2f85f7e1a3adfc0f299f496717e90ca67dff132fb750bb78790d3e0b8153d13920fa6d38bf80223be2382eec880e9f2f8365f71e6cbf03d36fd36a55fa6d299f7b623bf07a00fe1a26df94c05cf5c6483c48074fdf38beec246ebf2402fbab8d25fd68932fbad5c7f802177e9b4997c9011bf9981d3e4da0b9f09074fa17401fa1f331f38a23b6eb536fdd6834f9b2365f802176f092127db6b20fa4b221f11c176e3a400fce2995fbef1d3f6402fbf004887e0782ef88e0f9f58a957f09074fcc68befc3e849f17c177a9b474f95d110fb03365f2202fbee3c5f742e82eb8be05dd4da477e954cc6c9912ffb7538bf70ac83f0d2123ce29aff97f11df84903ff004cc7d71a55fc0f71ff17c23bb03c74fa07998fba7641f75a51feeb42edc17001f82e048f4aa64fe714e2fc8802e7a554abf1d20b9f0d0d97c748e5fc24331b848c83edd49978a605dfae3359d24023bf0ba127e00a73fa4b299f81edd7eeb474fa121c5fc34607f869093e954177d2aa52fc343a3f33023be4c8173c990befa4b425f1d2007c4c8907ca608edb03331d1d2387f0d200fde1303fbc275bf4da3a7e440887e07b20f88e05df4aa176ed445f759024bfb2038bf36442ff090077dc782ef8e91cbe7a2177e530907d25a4bf88e0bb3640483e174173ccc110e94c21bf81f03fe4c8887e009c5fb75365f3ee23b644074fd258befb5b1d3f4aa533edd4177d81aeef9320bbf3640b9e92ccc7dd688efb204a5f05c09de4405f75d68bef82e043f6ea3a7d090a67c4707cd8e90bbe4da2fbeb8c177d191b2fc2411df81e176ed98887c4705dfc0f607f6ea6f3ec8074fe12401785d05c73644cbeea936fd2588efc0f241f11c0b966c8477e1a0bee97f11db7ce2fbf090cc7dba8bef91021bf87903fe480907c748d3f3ad607f83c92fedd4997e1a2e3fc0f221f8023a7c714a63d36a4bfb03221f38a177eb8ccc7c1702afc32849f4aa717f004997d4985df82e05df774b8fe1742efe00b8ffb030bb722042fe23800ec5f02e7c015c7f74692fe9b4907d6e94cfb034dbf71e957e954cc7dc785dfc01397f4724cbe4802efdc788edc34241f8166c9ee3ca0fce2998fc08331f, 0x264176e92c74fd36998fc3a803f264443c0b800bc748bef0be05cd6ea533e53074f92a8e9f19811db17c2c7ae8dc7fe07932f998265f4aa0b9e714d97dd6910f8e91b7f8166cbe92d1fbe12303fb72299f2642fba3a46df82e85dba5517dd3d0177ee3d81fdba8e9fb0317df81e957ec0d71fc900e9f25512ff2982fbb0d05f7e1a434fbad265f330657e92c4e7ccc198f88e05db5c6b02ec0c476c9005dbb200bb755c3a7edd4477e1a3207c0f2a5f868717e9b4497dd6a55b8e91d3f640177e3a44769f78e9f3ad4abb17c2a7ec805f75028e9f0e911df606663ec7d71fe1a132fc3a6ebf81e23beb5d36fd2582e7a6d11db81e0b9ec0c2efe07ae3fb03241f6064bbe530a67c748bee2e3299f8684cae4402efe12154fc3281ff4964cbe6605f7da308efa550bbf2982fbec80177ca60edfc411d3e848b8f709125fe2085dbbad299f17c23b66602edd719acfc245c7f81e92fed6c74fa00920f92017df7f4483ec8181fcd90befc1f4aaf716717e92d096cfb88efae311db4da23bec0c477d818e9f38f11df802531e6602efd718e9fc01641f0ba136f004d97d81a4bfc3e75bf17c2dba480887dc7941f401607f3d0176e23840fe1226dda4b45bf802dd7e6c82efd7185df9c50bb74da9b7e598177d71ad5fa4b1d3e8683a7cc81907d2a88ed93205df6ea0b9e440807dfb910f9100bb7640443e2f800fdd6b8ff82e049f606533f00474fdbaa55f85d0037848176eb8d71fc47001f9c5241f5c61c7f0d02edc748e1f05d05df4aa4cae6c8d7fdbaae3fb75241f364533e2f858fe208bee91005df5c66cbeeb525fdd68e9fb2005cf5ba53369b4a63c7488ef0e90bb64da2fbae3d337d3685dbc34331f11c23b70d0047e0082efc014abf75a957f03c0a7e0788ed85d09bf640b8fe1742cfcc68beebad17dd8822fbf090907e1a38fbb2011df6060b9ec80997dc7920fc2405cf88223b6dd581fccc120d91011df8484cbec80cc7c5f05df8e91a7f5c60b9f0d074fce290dfb03331b6740b9ed18476c9910bfb8f365d7b623b710474fd36a52fb8f1d3f71e92fe2f8477d518bef8e917dd0ba156ec80d7fe19303fbad241f6ea4caf0912afe1a158fbad6ebf848177f0d207bcd90e9fb7d331f8680b9f07d2afdc785dbc3405df868177ee3d907e1f434fc0f38af802eb7eeb5907ccc02efc2417dd6ea92fe2f85f753685df8be003d, 0x24023b6dd42efd8182efa4b221d6404bfe48084fdd69b2fb8f221f6ea443efe8903e008bef85d0abf5c69b7ec0d2afce2932fc0111db38a2fbf0d1907dc59c5b82e042f5fc717e3a4177d90255fb20365f0ba007f091d6fe078beec01299e878e3fe954907c748e9f40f651f5c63a7ca1c173d9026dfbad75bf38a2fbb0d12afc990e9f14c23bf5c6176e17428dce282e79c5221f330333f104177de138ffc24659f802533e77c177dc79c5fbba6ebf3642fbb1042efc9908eda4b365f38a3a7c92c177d818beeae3221f38a3a7f0d125fc4702e78be0bb750e0bbf03cd97e079c5ea6d365f802c9be660907d9008edb75331f3643a7ce3ca67d518beebad11db84823b6e3dc7fc7482e7303265f81e9d7e5d02edd2a8bef94c11df1d2177e77c173dba844fa4b221e4da443e6c8177e120befc01497f4968b6ec0c337dc7b81796605cf11c22b70d0a67ccc0e9fae3265f71e0f3e9548dfd4985dbae3241f496176f0d0477dbab6cfbad381f71e99b7091c7fc5f0b6f88e103b81e177ec8030fc9908ef88e10df640715e3a42eddc7932f94c0bb775a177ee3dbafc9911bfbad38bf330443e530887e079c5f8be153d868c82eeb4173e1d434fb0338bf364443ec0d7d7ccc109fa6d05df71eb8ff03c74fe008beeb8f1d3e38a533f104477ddd3adfb5117df49623b6238477d71ad57b201d3e11c21b70b971fc9002e7c3481ff55c3a7d0d0476e07c01f9b2241f7a2176f00600fdc78befae311df5c62fba92c2efd71920da4b241f868dd7e6c8cc7dc7b81fb1f497f71e6cae92c5f7536995f9c511df75ae93eb8d607e1a14c7a5511df36431beda8907e0082e79b211db6eac83edd5bafca6132f8e911db6ea23b70d1c7fc99132fb3a05df6ea983e2f82ed5d682efaf34abf17c23b24c874fdbaa6dfc2438af33064fe714177e1202efb8f05cf38a30be17428fcd905db88e115f4aa6cbf03c5f7c5f0baec2439bf2983a7e530177c900f6fbad331f8689e7eb8ce2fd8fb03fafc4dbf4aa4cbe95474fc748befc24803f2400bbec0d81fcba05dfa4138bf848443e53097fc8808eda55221f71e9b7e92d1ffccc14cf99817dd40a3a7f03dd6fe00a6dfc1e81ff17c2ebf0040d7d818e9f9321e3f], [], []]
  | 7 => [[0x1f], [0x4dbf17df1d3f11db75bf299f803f38bf05df5c7f221f869f365f641f331f81ff4abf1d3e607f6ebf0bbf265f17dd241f11df0bb705cf497f71ff849f], [], [], []]
  | 8 => [[0x1f], [], [], [], []]
  | _ => []

def C9_S (s j : Nat) : List Nat :=
  qGroupedState C9_initial 5 32 11 C9_patterns C9_values (C9_counts s) (C9_specs s) (C9_records s) j

def C9_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C9_initial (C9_counts s) (C9_specs s) (C9_seeds s) ws

def C9_groups : List (Nat × Nat) := [(21,0x22c82080), (28,0x62486000), (10,0x4800), (3,0x2480880), (6,0x404080), (9,0x2002800), (17,0x2080000), (12,0x6000), (18,0x480000), (26,0x4a484800), (20,0x400000), (5,0x2080), (24,0x2000000), (1,0x2082880), (2,0x480880), (4,0x80)]
def C9_cover (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then dirCover C9_groups ws else diffCover 0xffffffff C9_groups ws
def C9_Z := barBudget 0xffffffff 0xeac8e880 C9_cover C9_S C9_N C9_idx
def C9_flat := certAt C9_Z C9_N 9

theorem C0_diff_good : diffGroupsGood 32 0xffffffff 0xe8a8a8a8 C0_groups = true := by decide +kernel
theorem C0_dir_good : dirGroupsGood 32 0xe8a8a8a8 C0_groups = true := by decide +kernel
theorem C0_initial_ok : ∀ s ≤ 5, C0_initial.length ≤ s+1 → found C0_S C0_N C0_idx s C0_initial = true := by
  have h : ∀ s : Fin 6, C0_initial.length ≤ s.val+1 → found C0_S C0_N C0_idx s C0_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C0_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xe8a8a8a8 x ≠ tableFn 0xe8a8a8a8 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C0_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C0_initial := by decide +kernel
theorem C0_goal : encL (tableFn 0xe8a8a8a8) allRows = 0xe8a8a8a8 := by decide +kernel
theorem C0_proper : ∀ zs ∈ C0_initial.sublists, zs ≠ C0_initial → diffCover 0xffffffff C0_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C0_b0 : span C0_flat 23 0 = true := by decide +kernel

theorem C1_diff_good : diffGroupsGood 32 0xffffffff 0xe8a8e888 C1_groups = true := by decide +kernel
theorem C1_dir_good : dirGroupsGood 32 0xe8a8e888 C1_groups = true := by decide +kernel
theorem C1_initial_ok : ∀ s ≤ 6, C1_initial.length ≤ s+1 → found C1_S C1_N C1_idx s C1_initial = true := by
  have h : ∀ s : Fin 7, C1_initial.length ≤ s.val+1 → found C1_S C1_N C1_idx s C1_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C1_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xe8a8e888 x ≠ tableFn 0xe8a8e888 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C1_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C1_initial := by decide +kernel
theorem C1_goal : encL (tableFn 0xe8a8e888) allRows = 0xe8a8e888 := by decide +kernel
theorem C1_proper : ∀ zs ∈ C1_initial.sublists, zs ≠ C1_initial → diffCover 0xffffffff C1_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C1_b0 : span C1_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C1_b1 : span C1_flat 64 64 = true := by decide +kernel

theorem C2_diff_good : diffGroupsGood 32 0xffffffff 0xe8e8e880 C2_groups = true := by decide +kernel
theorem C2_dir_good : dirGroupsGood 32 0xe8e8e880 C2_groups = true := by decide +kernel
theorem C2_initial_ok : ∀ s ≤ 7, C2_initial.length ≤ s+1 → found C2_S C2_N C2_idx s C2_initial = true := by
  have h : ∀ s : Fin 8, C2_initial.length ≤ s.val+1 → found C2_S C2_N C2_idx s C2_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C2_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xe8e8e880 x ≠ tableFn 0xe8e8e880 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C2_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C2_initial := by decide +kernel
theorem C2_goal : encL (tableFn 0xe8e8e880) allRows = 0xe8e8e880 := by decide +kernel
theorem C2_proper : ∀ zs ∈ C2_initial.sublists, zs ≠ C2_initial → diffCover 0xffffffff C2_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b0 : span C2_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b1 : span C2_flat 64 64 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b2 : span C2_flat 64 128 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b3 : span C2_flat 64 192 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b4 : span C2_flat 64 256 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b5 : span C2_flat 64 320 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b6 : span C2_flat 64 384 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b7 : span C2_flat 64 448 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b8 : span C2_flat 64 512 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b9 : span C2_flat 64 576 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b10 : span C2_flat 64 640 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b11 : span C2_flat 64 704 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b12 : span C2_flat 64 768 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b13 : span C2_flat 64 832 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b14 : span C2_flat 64 896 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b15 : span C2_flat 64 960 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b16 : span C2_flat 64 1024 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b17 : span C2_flat 64 1088 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C2_b18 : span C2_flat 13 1152 = true := by decide +kernel

theorem C3_diff_good : diffGroupsGood 32 0xffffffff 0xeaa8a888 C3_groups = true := by decide +kernel
theorem C3_dir_good : dirGroupsGood 32 0xeaa8a888 C3_groups = true := by decide +kernel
theorem C3_initial_ok : ∀ s ≤ 8, C3_initial.length ≤ s+1 → found C3_S C3_N C3_idx s C3_initial = true := by
  have h : ∀ s : Fin 9, C3_initial.length ≤ s.val+1 → found C3_S C3_N C3_idx s C3_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C3_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeaa8a888 x ≠ tableFn 0xeaa8a888 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C3_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C3_initial := by decide +kernel
theorem C3_goal : encL (tableFn 0xeaa8a888) allRows = 0xeaa8a888 := by decide +kernel
theorem C3_proper : ∀ zs ∈ C3_initial.sublists, zs ≠ C3_initial → diffCover 0xffffffff C3_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b0 : span C3_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b1 : span C3_flat 64 64 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b2 : span C3_flat 64 128 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b3 : span C3_flat 64 192 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b4 : span C3_flat 64 256 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b5 : span C3_flat 64 320 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b6 : span C3_flat 64 384 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b7 : span C3_flat 64 448 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b8 : span C3_flat 64 512 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b9 : span C3_flat 64 576 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b10 : span C3_flat 64 640 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b11 : span C3_flat 64 704 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b12 : span C3_flat 64 768 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b13 : span C3_flat 64 832 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b14 : span C3_flat 64 896 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b15 : span C3_flat 64 960 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b16 : span C3_flat 64 1024 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b17 : span C3_flat 64 1088 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b18 : span C3_flat 64 1152 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b19 : span C3_flat 64 1216 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b20 : span C3_flat 64 1280 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b21 : span C3_flat 64 1344 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b22 : span C3_flat 64 1408 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b23 : span C3_flat 64 1472 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b24 : span C3_flat 64 1536 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b25 : span C3_flat 64 1600 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b26 : span C3_flat 64 1664 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b27 : span C3_flat 64 1728 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b28 : span C3_flat 64 1792 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b29 : span C3_flat 64 1856 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b30 : span C3_flat 64 1920 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b31 : span C3_flat 64 1984 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b32 : span C3_flat 64 2048 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b33 : span C3_flat 64 2112 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b34 : span C3_flat 64 2176 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b35 : span C3_flat 64 2240 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b36 : span C3_flat 64 2304 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b37 : span C3_flat 64 2368 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b38 : span C3_flat 64 2432 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b39 : span C3_flat 64 2496 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b40 : span C3_flat 64 2560 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b41 : span C3_flat 64 2624 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b42 : span C3_flat 64 2688 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b43 : span C3_flat 64 2752 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b44 : span C3_flat 64 2816 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b45 : span C3_flat 64 2880 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b46 : span C3_flat 64 2944 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b47 : span C3_flat 64 3008 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b48 : span C3_flat 64 3072 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b49 : span C3_flat 64 3136 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b50 : span C3_flat 64 3200 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b51 : span C3_flat 64 3264 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b52 : span C3_flat 64 3328 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b53 : span C3_flat 64 3392 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b54 : span C3_flat 64 3456 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b55 : span C3_flat 64 3520 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b56 : span C3_flat 64 3584 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b57 : span C3_flat 64 3648 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b58 : span C3_flat 64 3712 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b59 : span C3_flat 64 3776 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b60 : span C3_flat 64 3840 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b61 : span C3_flat 64 3904 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b62 : span C3_flat 64 3968 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b63 : span C3_flat 64 4032 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b64 : span C3_flat 64 4096 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b65 : span C3_flat 64 4160 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b66 : span C3_flat 64 4224 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b67 : span C3_flat 64 4288 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b68 : span C3_flat 64 4352 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b69 : span C3_flat 64 4416 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b70 : span C3_flat 64 4480 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b71 : span C3_flat 64 4544 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b72 : span C3_flat 64 4608 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b73 : span C3_flat 64 4672 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b74 : span C3_flat 64 4736 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b75 : span C3_flat 64 4800 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b76 : span C3_flat 64 4864 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b77 : span C3_flat 64 4928 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b78 : span C3_flat 64 4992 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b79 : span C3_flat 64 5056 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b80 : span C3_flat 64 5120 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b81 : span C3_flat 64 5184 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b82 : span C3_flat 64 5248 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b83 : span C3_flat 64 5312 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b84 : span C3_flat 64 5376 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b85 : span C3_flat 64 5440 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b86 : span C3_flat 64 5504 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C3_b87 : span C3_flat 35 5568 = true := by decide +kernel

theorem C4_diff_good : diffGroupsGood 32 0xffffffff 0xeaa8c888 C4_groups = true := by decide +kernel
theorem C4_dir_good : dirGroupsGood 32 0xeaa8c888 C4_groups = true := by decide +kernel
theorem C4_initial_ok : ∀ s ≤ 6, C4_initial.length ≤ s+1 → found C4_S C4_N C4_idx s C4_initial = true := by
  have h : ∀ s : Fin 7, C4_initial.length ≤ s.val+1 → found C4_S C4_N C4_idx s C4_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C4_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeaa8c888 x ≠ tableFn 0xeaa8c888 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C4_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C4_initial := by decide +kernel
theorem C4_goal : encL (tableFn 0xeaa8c888) allRows = 0xeaa8c888 := by decide +kernel
theorem C4_proper : ∀ zs ∈ C4_initial.sublists, zs ≠ C4_initial → diffCover 0xffffffff C4_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C4_b0 : span C4_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C4_b1 : span C4_flat 10 64 = true := by decide +kernel

theorem C5_diff_good : diffGroupsGood 32 0xffffffff 0xeaa8e880 C5_groups = true := by decide +kernel
theorem C5_dir_good : dirGroupsGood 32 0xeaa8e880 C5_groups = true := by decide +kernel
theorem C5_initial_ok : ∀ s ≤ 8, C5_initial.length ≤ s+1 → found C5_S C5_N C5_idx s C5_initial = true := by
  have h : ∀ s : Fin 9, C5_initial.length ≤ s.val+1 → found C5_S C5_N C5_idx s C5_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C5_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeaa8e880 x ≠ tableFn 0xeaa8e880 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C5_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C5_initial := by decide +kernel
theorem C5_goal : encL (tableFn 0xeaa8e880) allRows = 0xeaa8e880 := by decide +kernel
theorem C5_proper : ∀ zs ∈ C5_initial.sublists, zs ≠ C5_initial → diffCover 0xffffffff C5_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b0 : span C5_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b1 : span C5_flat 64 64 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b2 : span C5_flat 64 128 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b3 : span C5_flat 64 192 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b4 : span C5_flat 64 256 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b5 : span C5_flat 64 320 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b6 : span C5_flat 64 384 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b7 : span C5_flat 64 448 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b8 : span C5_flat 64 512 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b9 : span C5_flat 64 576 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b10 : span C5_flat 64 640 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b11 : span C5_flat 64 704 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b12 : span C5_flat 64 768 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b13 : span C5_flat 64 832 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b14 : span C5_flat 64 896 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b15 : span C5_flat 64 960 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b16 : span C5_flat 64 1024 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b17 : span C5_flat 64 1088 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b18 : span C5_flat 64 1152 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b19 : span C5_flat 64 1216 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b20 : span C5_flat 64 1280 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b21 : span C5_flat 64 1344 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b22 : span C5_flat 64 1408 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b23 : span C5_flat 64 1472 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b24 : span C5_flat 64 1536 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b25 : span C5_flat 64 1600 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b26 : span C5_flat 64 1664 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b27 : span C5_flat 64 1728 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b28 : span C5_flat 64 1792 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b29 : span C5_flat 64 1856 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b30 : span C5_flat 64 1920 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b31 : span C5_flat 64 1984 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b32 : span C5_flat 64 2048 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b33 : span C5_flat 64 2112 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b34 : span C5_flat 64 2176 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b35 : span C5_flat 64 2240 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b36 : span C5_flat 64 2304 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b37 : span C5_flat 64 2368 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b38 : span C5_flat 64 2432 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b39 : span C5_flat 64 2496 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b40 : span C5_flat 64 2560 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b41 : span C5_flat 64 2624 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b42 : span C5_flat 64 2688 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b43 : span C5_flat 64 2752 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b44 : span C5_flat 64 2816 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b45 : span C5_flat 64 2880 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b46 : span C5_flat 64 2944 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b47 : span C5_flat 64 3008 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b48 : span C5_flat 64 3072 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b49 : span C5_flat 64 3136 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b50 : span C5_flat 64 3200 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b51 : span C5_flat 64 3264 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b52 : span C5_flat 64 3328 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b53 : span C5_flat 64 3392 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b54 : span C5_flat 64 3456 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b55 : span C5_flat 64 3520 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b56 : span C5_flat 64 3584 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b57 : span C5_flat 64 3648 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b58 : span C5_flat 64 3712 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b59 : span C5_flat 64 3776 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b60 : span C5_flat 64 3840 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b61 : span C5_flat 64 3904 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b62 : span C5_flat 64 3968 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b63 : span C5_flat 64 4032 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b64 : span C5_flat 64 4096 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b65 : span C5_flat 64 4160 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b66 : span C5_flat 64 4224 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b67 : span C5_flat 64 4288 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b68 : span C5_flat 64 4352 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b69 : span C5_flat 64 4416 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b70 : span C5_flat 64 4480 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b71 : span C5_flat 64 4544 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b72 : span C5_flat 64 4608 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b73 : span C5_flat 64 4672 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b74 : span C5_flat 64 4736 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b75 : span C5_flat 64 4800 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b76 : span C5_flat 64 4864 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b77 : span C5_flat 64 4928 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b78 : span C5_flat 64 4992 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C5_b79 : span C5_flat 5 5056 = true := by decide +kernel

theorem C6_diff_good : diffGroupsGood 32 0xffffffff 0xeaaac880 C6_groups = true := by decide +kernel
theorem C6_dir_good : dirGroupsGood 32 0xeaaac880 C6_groups = true := by decide +kernel
theorem C6_initial_ok : ∀ s ≤ 6, C6_initial.length ≤ s+1 → found C6_S C6_N C6_idx s C6_initial = true := by
  have h : ∀ s : Fin 7, C6_initial.length ≤ s.val+1 → found C6_S C6_N C6_idx s C6_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C6_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeaaac880 x ≠ tableFn 0xeaaac880 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C6_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C6_initial := by decide +kernel
theorem C6_goal : encL (tableFn 0xeaaac880) allRows = 0xeaaac880 := by decide +kernel
theorem C6_proper : ∀ zs ∈ C6_initial.sublists, zs ≠ C6_initial → diffCover 0xffffffff C6_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C6_b0 : span C6_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C6_b1 : span C6_flat 38 64 = true := by decide +kernel

theorem C7_diff_good : diffGroupsGood 32 0xffffffff 0xeac0e8c0 C7_groups = true := by decide +kernel
theorem C7_dir_good : dirGroupsGood 32 0xeac0e8c0 C7_groups = true := by decide +kernel
theorem C7_initial_ok : ∀ s ≤ 5, C7_initial.length ≤ s+1 → found C7_S C7_N C7_idx s C7_initial = true := by
  have h : ∀ s : Fin 6, C7_initial.length ≤ s.val+1 → found C7_S C7_N C7_idx s C7_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C7_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeac0e8c0 x ≠ tableFn 0xeac0e8c0 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C7_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C7_initial := by decide +kernel
theorem C7_goal : encL (tableFn 0xeac0e8c0) allRows = 0xeac0e8c0 := by decide +kernel
theorem C7_proper : ∀ zs ∈ C7_initial.sublists, zs ≠ C7_initial → diffCover 0xffffffff C7_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C7_b0 : span C7_flat 17 0 = true := by decide +kernel

theorem C8_diff_good : diffGroupsGood 32 0xffffffff 0xeac8e0c0 C8_groups = true := by decide +kernel
theorem C8_dir_good : dirGroupsGood 32 0xeac8e0c0 C8_groups = true := by decide +kernel
theorem C8_initial_ok : ∀ s ≤ 4, C8_initial.length ≤ s+1 → found C8_S C8_N C8_idx s C8_initial = true := by
  have h : ∀ s : Fin 5, C8_initial.length ≤ s.val+1 → found C8_S C8_N C8_idx s C8_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C8_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeac8e0c0 x ≠ tableFn 0xeac8e0c0 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C8_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C8_initial := by decide +kernel
theorem C8_goal : encL (tableFn 0xeac8e0c0) allRows = 0xeac8e0c0 := by decide +kernel
theorem C8_proper : ∀ zs ∈ C8_initial.sublists, zs ≠ C8_initial → diffCover 0xffffffff C8_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C8_b0 : span C8_flat 1 0 = true := by decide +kernel

theorem C9_diff_good : diffGroupsGood 32 0xffffffff 0xeac8e880 C9_groups = true := by decide +kernel
theorem C9_dir_good : dirGroupsGood 32 0xeac8e880 C9_groups = true := by decide +kernel
theorem C9_initial_ok : ∀ s ≤ 8, C9_initial.length ≤ s+1 → found C9_S C9_N C9_idx s C9_initial = true := by
  have h : ∀ s : Fin 9, C9_initial.length ≤ s.val+1 → found C9_S C9_N C9_idx s C9_initial = true := by decide +kernel
  intro s hs
  exact h ⟨s,by omega⟩
theorem C9_hnc : ∃ x x' : Fin 5 → Bool, tableFn 0xeac8e880 x ≠ tableFn 0xeac8e880 x' :=
  ⟨pt 5 0,pt 5 31,by decide +kernel⟩
theorem C9_inputs : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a allRows) = C9_initial := by decide +kernel
theorem C9_goal : encL (tableFn 0xeac8e880) allRows = 0xeac8e880 := by decide +kernel
theorem C9_proper : ∀ zs ∈ C9_initial.sublists, zs ≠ C9_initial → diffCover 0xffffffff C9_groups zs = false := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b0 : span C9_flat 64 0 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b1 : span C9_flat 64 64 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b2 : span C9_flat 64 128 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b3 : span C9_flat 64 192 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b4 : span C9_flat 64 256 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b5 : span C9_flat 64 320 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b6 : span C9_flat 64 384 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b7 : span C9_flat 64 448 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b8 : span C9_flat 64 512 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b9 : span C9_flat 64 576 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b10 : span C9_flat 64 640 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b11 : span C9_flat 64 704 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b12 : span C9_flat 64 768 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b13 : span C9_flat 64 832 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b14 : span C9_flat 64 896 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b15 : span C9_flat 64 960 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b16 : span C9_flat 64 1024 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b17 : span C9_flat 64 1088 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b18 : span C9_flat 64 1152 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b19 : span C9_flat 64 1216 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b20 : span C9_flat 64 1280 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b21 : span C9_flat 64 1344 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b22 : span C9_flat 64 1408 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b23 : span C9_flat 64 1472 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b24 : span C9_flat 64 1536 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b25 : span C9_flat 64 1600 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b26 : span C9_flat 64 1664 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b27 : span C9_flat 64 1728 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b28 : span C9_flat 64 1792 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b29 : span C9_flat 64 1856 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b30 : span C9_flat 64 1920 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b31 : span C9_flat 64 1984 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b32 : span C9_flat 64 2048 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b33 : span C9_flat 64 2112 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b34 : span C9_flat 64 2176 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b35 : span C9_flat 64 2240 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b36 : span C9_flat 64 2304 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b37 : span C9_flat 64 2368 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b38 : span C9_flat 64 2432 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b39 : span C9_flat 64 2496 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b40 : span C9_flat 64 2560 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b41 : span C9_flat 64 2624 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b42 : span C9_flat 64 2688 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b43 : span C9_flat 64 2752 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b44 : span C9_flat 64 2816 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b45 : span C9_flat 64 2880 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b46 : span C9_flat 64 2944 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b47 : span C9_flat 64 3008 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b48 : span C9_flat 64 3072 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b49 : span C9_flat 64 3136 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b50 : span C9_flat 64 3200 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b51 : span C9_flat 64 3264 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b52 : span C9_flat 64 3328 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b53 : span C9_flat 64 3392 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b54 : span C9_flat 64 3456 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b55 : span C9_flat 64 3520 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b56 : span C9_flat 64 3584 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b57 : span C9_flat 64 3648 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b58 : span C9_flat 64 3712 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b59 : span C9_flat 64 3776 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b60 : span C9_flat 64 3840 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b61 : span C9_flat 64 3904 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b62 : span C9_flat 64 3968 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b63 : span C9_flat 64 4032 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b64 : span C9_flat 64 4096 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b65 : span C9_flat 64 4160 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b66 : span C9_flat 64 4224 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b67 : span C9_flat 64 4288 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b68 : span C9_flat 64 4352 = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem C9_b69 : span C9_flat 21 4416 = true := by decide +kernel

theorem C0_checked : ∀ s ≤ 5, ∀ i < C0_N s, C0_Z s i = true := by
  apply certFlat_sound
  exact C0_b0
theorem C0_cover_ok {s ws} (h : NatRun 0xffffffff 0xe8a8a8a8 s ws) : C0_cover s ws = true := by
  unfold C0_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C0_dir_good
  · exact diffCover_ok_of_good h C0_diff_good
theorem C0_no_run : ∀ s ≤ 5, ¬ NatRun 0xffffffff 0xe8a8a8a8 s C0_initial :=
  noRun_from_barBudget (fun h => C0_cover_ok h) C0_checked C0_initial_ok
theorem C0_lower : ¬ HasCircuitSize 5 (tableFn 0xe8a8a8a8) 5 :=
  encoded_exclusion (tableFn 0xe8a8a8a8) C0_hnc 5 allRows C0_initial 0xffffffff 0xe8a8a8a8
    (diffCover 0xffffffff C0_groups) (fun h => diffCover_ok_of_good h C0_diff_good)
    C0_inputs (by decide +kernel) C0_goal C0_proper C0_no_run

theorem C1_checked : ∀ s ≤ 6, ∀ i < C1_N s, C1_Z s i = true := by
  apply certFlat_sound
  exact (span_join C1_b0 C1_b1)
theorem C1_cover_ok {s ws} (h : NatRun 0xffffffff 0xe8a8e888 s ws) : C1_cover s ws = true := by
  unfold C1_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C1_dir_good
  · exact diffCover_ok_of_good h C1_diff_good
theorem C1_no_run : ∀ s ≤ 6, ¬ NatRun 0xffffffff 0xe8a8e888 s C1_initial :=
  noRun_from_barBudget (fun h => C1_cover_ok h) C1_checked C1_initial_ok
theorem C1_lower : ¬ HasCircuitSize 5 (tableFn 0xe8a8e888) 6 :=
  encoded_exclusion (tableFn 0xe8a8e888) C1_hnc 6 allRows C1_initial 0xffffffff 0xe8a8e888
    (diffCover 0xffffffff C1_groups) (fun h => diffCover_ok_of_good h C1_diff_good)
    C1_inputs (by decide +kernel) C1_goal C1_proper C1_no_run

theorem C2_checked : ∀ s ≤ 7, ∀ i < C2_N s, C2_Z s i = true := by
  apply certFlat_sound
  exact (span_join (span_join (span_join (span_join C2_b0 C2_b1) (span_join C2_b2 C2_b3)) (span_join (span_join C2_b4 C2_b5) (span_join C2_b6 (span_join C2_b7 C2_b8)))) (span_join (span_join (span_join C2_b9 C2_b10) (span_join C2_b11 (span_join C2_b12 C2_b13))) (span_join (span_join C2_b14 C2_b15) (span_join C2_b16 (span_join C2_b17 C2_b18)))))
theorem C2_cover_ok {s ws} (h : NatRun 0xffffffff 0xe8e8e880 s ws) : C2_cover s ws = true := by
  unfold C2_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C2_dir_good
  · exact diffCover_ok_of_good h C2_diff_good
theorem C2_no_run : ∀ s ≤ 7, ¬ NatRun 0xffffffff 0xe8e8e880 s C2_initial :=
  noRun_from_barBudget (fun h => C2_cover_ok h) C2_checked C2_initial_ok
theorem C2_lower : ¬ HasCircuitSize 5 (tableFn 0xe8e8e880) 7 :=
  encoded_exclusion (tableFn 0xe8e8e880) C2_hnc 7 allRows C2_initial 0xffffffff 0xe8e8e880
    (diffCover 0xffffffff C2_groups) (fun h => diffCover_ok_of_good h C2_diff_good)
    C2_inputs (by decide +kernel) C2_goal C2_proper C2_no_run

theorem C3_checked : ∀ s ≤ 8, ∀ i < C3_N s, C3_Z s i = true := by
  apply certFlat_sound
  exact (span_join (span_join (span_join (span_join (span_join (span_join C3_b0 C3_b1) (span_join C3_b2 (span_join C3_b3 C3_b4))) (span_join (span_join C3_b5 (span_join C3_b6 C3_b7)) (span_join C3_b8 (span_join C3_b9 C3_b10)))) (span_join (span_join (span_join C3_b11 C3_b12) (span_join C3_b13 (span_join C3_b14 C3_b15))) (span_join (span_join C3_b16 (span_join C3_b17 C3_b18)) (span_join C3_b19 (span_join C3_b20 C3_b21))))) (span_join (span_join (span_join (span_join C3_b22 C3_b23) (span_join C3_b24 (span_join C3_b25 C3_b26))) (span_join (span_join C3_b27 (span_join C3_b28 C3_b29)) (span_join C3_b30 (span_join C3_b31 C3_b32)))) (span_join (span_join (span_join C3_b33 C3_b34) (span_join C3_b35 (span_join C3_b36 C3_b37))) (span_join (span_join C3_b38 (span_join C3_b39 C3_b40)) (span_join C3_b41 (span_join C3_b42 C3_b43)))))) (span_join (span_join (span_join (span_join (span_join C3_b44 C3_b45) (span_join C3_b46 (span_join C3_b47 C3_b48))) (span_join (span_join C3_b49 (span_join C3_b50 C3_b51)) (span_join C3_b52 (span_join C3_b53 C3_b54)))) (span_join (span_join (span_join C3_b55 C3_b56) (span_join C3_b57 (span_join C3_b58 C3_b59))) (span_join (span_join C3_b60 (span_join C3_b61 C3_b62)) (span_join C3_b63 (span_join C3_b64 C3_b65))))) (span_join (span_join (span_join (span_join C3_b66 C3_b67) (span_join C3_b68 (span_join C3_b69 C3_b70))) (span_join (span_join C3_b71 (span_join C3_b72 C3_b73)) (span_join C3_b74 (span_join C3_b75 C3_b76)))) (span_join (span_join (span_join C3_b77 C3_b78) (span_join C3_b79 (span_join C3_b80 C3_b81))) (span_join (span_join C3_b82 (span_join C3_b83 C3_b84)) (span_join C3_b85 (span_join C3_b86 C3_b87)))))))
theorem C3_cover_ok {s ws} (h : NatRun 0xffffffff 0xeaa8a888 s ws) : C3_cover s ws = true := by
  unfold C3_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C3_dir_good
  · exact diffCover_ok_of_good h C3_diff_good
theorem C3_no_run : ∀ s ≤ 8, ¬ NatRun 0xffffffff 0xeaa8a888 s C3_initial :=
  noRun_from_barBudget (fun h => C3_cover_ok h) C3_checked C3_initial_ok
theorem C3_lower : ¬ HasCircuitSize 5 (tableFn 0xeaa8a888) 8 :=
  encoded_exclusion (tableFn 0xeaa8a888) C3_hnc 8 allRows C3_initial 0xffffffff 0xeaa8a888
    (diffCover 0xffffffff C3_groups) (fun h => diffCover_ok_of_good h C3_diff_good)
    C3_inputs (by decide +kernel) C3_goal C3_proper C3_no_run

theorem C4_checked : ∀ s ≤ 6, ∀ i < C4_N s, C4_Z s i = true := by
  apply certFlat_sound
  exact (span_join C4_b0 C4_b1)
theorem C4_cover_ok {s ws} (h : NatRun 0xffffffff 0xeaa8c888 s ws) : C4_cover s ws = true := by
  unfold C4_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C4_dir_good
  · exact diffCover_ok_of_good h C4_diff_good
theorem C4_no_run : ∀ s ≤ 6, ¬ NatRun 0xffffffff 0xeaa8c888 s C4_initial :=
  noRun_from_barBudget (fun h => C4_cover_ok h) C4_checked C4_initial_ok
theorem C4_lower : ¬ HasCircuitSize 5 (tableFn 0xeaa8c888) 6 :=
  encoded_exclusion (tableFn 0xeaa8c888) C4_hnc 6 allRows C4_initial 0xffffffff 0xeaa8c888
    (diffCover 0xffffffff C4_groups) (fun h => diffCover_ok_of_good h C4_diff_good)
    C4_inputs (by decide +kernel) C4_goal C4_proper C4_no_run

theorem C5_checked : ∀ s ≤ 8, ∀ i < C5_N s, C5_Z s i = true := by
  apply certFlat_sound
  exact (span_join (span_join (span_join (span_join (span_join (span_join C5_b0 C5_b1) (span_join C5_b2 (span_join C5_b3 C5_b4))) (span_join (span_join C5_b5 C5_b6) (span_join C5_b7 (span_join C5_b8 C5_b9)))) (span_join (span_join (span_join C5_b10 C5_b11) (span_join C5_b12 (span_join C5_b13 C5_b14))) (span_join (span_join C5_b15 C5_b16) (span_join C5_b17 (span_join C5_b18 C5_b19))))) (span_join (span_join (span_join (span_join C5_b20 C5_b21) (span_join C5_b22 (span_join C5_b23 C5_b24))) (span_join (span_join C5_b25 C5_b26) (span_join C5_b27 (span_join C5_b28 C5_b29)))) (span_join (span_join (span_join C5_b30 C5_b31) (span_join C5_b32 (span_join C5_b33 C5_b34))) (span_join (span_join C5_b35 C5_b36) (span_join C5_b37 (span_join C5_b38 C5_b39)))))) (span_join (span_join (span_join (span_join (span_join C5_b40 C5_b41) (span_join C5_b42 (span_join C5_b43 C5_b44))) (span_join (span_join C5_b45 C5_b46) (span_join C5_b47 (span_join C5_b48 C5_b49)))) (span_join (span_join (span_join C5_b50 C5_b51) (span_join C5_b52 (span_join C5_b53 C5_b54))) (span_join (span_join C5_b55 C5_b56) (span_join C5_b57 (span_join C5_b58 C5_b59))))) (span_join (span_join (span_join (span_join C5_b60 C5_b61) (span_join C5_b62 (span_join C5_b63 C5_b64))) (span_join (span_join C5_b65 C5_b66) (span_join C5_b67 (span_join C5_b68 C5_b69)))) (span_join (span_join (span_join C5_b70 C5_b71) (span_join C5_b72 (span_join C5_b73 C5_b74))) (span_join (span_join C5_b75 C5_b76) (span_join C5_b77 (span_join C5_b78 C5_b79)))))))
theorem C5_cover_ok {s ws} (h : NatRun 0xffffffff 0xeaa8e880 s ws) : C5_cover s ws = true := by
  unfold C5_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C5_dir_good
  · exact diffCover_ok_of_good h C5_diff_good
theorem C5_no_run : ∀ s ≤ 8, ¬ NatRun 0xffffffff 0xeaa8e880 s C5_initial :=
  noRun_from_barBudget (fun h => C5_cover_ok h) C5_checked C5_initial_ok
theorem C5_lower : ¬ HasCircuitSize 5 (tableFn 0xeaa8e880) 8 :=
  encoded_exclusion (tableFn 0xeaa8e880) C5_hnc 8 allRows C5_initial 0xffffffff 0xeaa8e880
    (diffCover 0xffffffff C5_groups) (fun h => diffCover_ok_of_good h C5_diff_good)
    C5_inputs (by decide +kernel) C5_goal C5_proper C5_no_run

theorem C6_checked : ∀ s ≤ 6, ∀ i < C6_N s, C6_Z s i = true := by
  apply certFlat_sound
  exact (span_join C6_b0 C6_b1)
theorem C6_cover_ok {s ws} (h : NatRun 0xffffffff 0xeaaac880 s ws) : C6_cover s ws = true := by
  unfold C6_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C6_dir_good
  · exact diffCover_ok_of_good h C6_diff_good
theorem C6_no_run : ∀ s ≤ 6, ¬ NatRun 0xffffffff 0xeaaac880 s C6_initial :=
  noRun_from_barBudget (fun h => C6_cover_ok h) C6_checked C6_initial_ok
theorem C6_lower : ¬ HasCircuitSize 5 (tableFn 0xeaaac880) 6 :=
  encoded_exclusion (tableFn 0xeaaac880) C6_hnc 6 allRows C6_initial 0xffffffff 0xeaaac880
    (diffCover 0xffffffff C6_groups) (fun h => diffCover_ok_of_good h C6_diff_good)
    C6_inputs (by decide +kernel) C6_goal C6_proper C6_no_run

theorem C7_checked : ∀ s ≤ 5, ∀ i < C7_N s, C7_Z s i = true := by
  apply certFlat_sound
  exact C7_b0
theorem C7_cover_ok {s ws} (h : NatRun 0xffffffff 0xeac0e8c0 s ws) : C7_cover s ws = true := by
  unfold C7_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C7_dir_good
  · exact diffCover_ok_of_good h C7_diff_good
theorem C7_no_run : ∀ s ≤ 5, ¬ NatRun 0xffffffff 0xeac0e8c0 s C7_initial :=
  noRun_from_barBudget (fun h => C7_cover_ok h) C7_checked C7_initial_ok
theorem C7_lower : ¬ HasCircuitSize 5 (tableFn 0xeac0e8c0) 5 :=
  encoded_exclusion (tableFn 0xeac0e8c0) C7_hnc 5 allRows C7_initial 0xffffffff 0xeac0e8c0
    (diffCover 0xffffffff C7_groups) (fun h => diffCover_ok_of_good h C7_diff_good)
    C7_inputs (by decide +kernel) C7_goal C7_proper C7_no_run

theorem C8_checked : ∀ s ≤ 4, ∀ i < C8_N s, C8_Z s i = true := by
  apply certFlat_sound
  exact C8_b0
theorem C8_cover_ok {s ws} (h : NatRun 0xffffffff 0xeac8e0c0 s ws) : C8_cover s ws = true := by
  unfold C8_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C8_dir_good
  · exact diffCover_ok_of_good h C8_diff_good
theorem C8_no_run : ∀ s ≤ 4, ¬ NatRun 0xffffffff 0xeac8e0c0 s C8_initial :=
  noRun_from_barBudget (fun h => C8_cover_ok h) C8_checked C8_initial_ok
theorem C8_lower : ¬ HasCircuitSize 5 (tableFn 0xeac8e0c0) 4 :=
  encoded_exclusion (tableFn 0xeac8e0c0) C8_hnc 4 allRows C8_initial 0xffffffff 0xeac8e0c0
    (diffCover 0xffffffff C8_groups) (fun h => diffCover_ok_of_good h C8_diff_good)
    C8_inputs (by decide +kernel) C8_goal C8_proper C8_no_run

theorem C9_checked : ∀ s ≤ 8, ∀ i < C9_N s, C9_Z s i = true := by
  apply certFlat_sound
  exact (span_join (span_join (span_join (span_join (span_join (span_join C9_b0 C9_b1) (span_join C9_b2 C9_b3)) (span_join (span_join C9_b4 C9_b5) (span_join C9_b6 C9_b7))) (span_join (span_join (span_join C9_b8 C9_b9) (span_join C9_b10 C9_b11)) (span_join (span_join C9_b12 C9_b13) (span_join C9_b14 (span_join C9_b15 C9_b16))))) (span_join (span_join (span_join (span_join C9_b17 C9_b18) (span_join C9_b19 C9_b20)) (span_join (span_join C9_b21 C9_b22) (span_join C9_b23 (span_join C9_b24 C9_b25)))) (span_join (span_join (span_join C9_b26 C9_b27) (span_join C9_b28 C9_b29)) (span_join (span_join C9_b30 C9_b31) (span_join C9_b32 (span_join C9_b33 C9_b34)))))) (span_join (span_join (span_join (span_join (span_join C9_b35 C9_b36) (span_join C9_b37 C9_b38)) (span_join (span_join C9_b39 C9_b40) (span_join C9_b41 C9_b42))) (span_join (span_join (span_join C9_b43 C9_b44) (span_join C9_b45 C9_b46)) (span_join (span_join C9_b47 C9_b48) (span_join C9_b49 (span_join C9_b50 C9_b51))))) (span_join (span_join (span_join (span_join C9_b52 C9_b53) (span_join C9_b54 C9_b55)) (span_join (span_join C9_b56 C9_b57) (span_join C9_b58 (span_join C9_b59 C9_b60)))) (span_join (span_join (span_join C9_b61 C9_b62) (span_join C9_b63 C9_b64)) (span_join (span_join C9_b65 C9_b66) (span_join C9_b67 (span_join C9_b68 C9_b69)))))))
theorem C9_cover_ok {s ws} (h : NatRun 0xffffffff 0xeac8e880 s ws) : C9_cover s ws = true := by
  unfold C9_cover
  split
  · exact dirCover_tight_ok_of_good h ‹_› C9_dir_good
  · exact diffCover_ok_of_good h C9_diff_good
theorem C9_no_run : ∀ s ≤ 8, ¬ NatRun 0xffffffff 0xeac8e880 s C9_initial :=
  noRun_from_barBudget (fun h => C9_cover_ok h) C9_checked C9_initial_ok
theorem C9_lower : ¬ HasCircuitSize 5 (tableFn 0xeac8e880) 8 :=
  encoded_exclusion (tableFn 0xeac8e880) C9_hnc 8 allRows C9_initial 0xffffffff 0xeac8e880
    (diffCover 0xffffffff C9_groups) (fun h => diffCover_ok_of_good h C9_diff_good)
    C9_inputs (by decide +kernel) C9_goal C9_proper C9_no_run

theorem table_lower (T : Nat) (hT : T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset Nat)) :
    ¬ HasCircuitSize 5 (tableFn T) (upperBudget T - 1) := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact C0_lower
  · exact C1_lower
  · exact C2_lower
  · exact C3_lower
  · exact C4_lower
  · exact C5_lower
  · exact C6_lower
  · exact C7_lower
  · exact C8_lower
  · exact C9_lower

theorem solution :
    ∀ T ∈ ({0xe8a8a8a8, 0xe8a8e888, 0xe8e8e880, 0xeaa8a888, 0xeaa8c888, 0xeaa8e880, 0xeaaac880, 0xeac0e8c0, 0xeac8e0c0, 0xeac8e880} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hfan _hnot heval
  apply monotone_equivalent_of_upperBudget_le T hT gates
  by_contra! hsize
  apply table_lower T hT
  refine ⟨⟨gates,o⟩,hfan,?_,heval⟩
  change gates.length ≤ upperBudget T - 1
  omega

end PEqualNP.Outside.L_meta_1425.Cert
