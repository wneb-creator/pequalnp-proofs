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
theorem C3_benchmark : span (C3_Z 5) 32 0 = true := by decide +kernel

end PEqualNP.Outside.L_meta_1425.Cert
