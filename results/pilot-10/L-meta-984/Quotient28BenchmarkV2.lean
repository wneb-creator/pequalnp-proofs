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


def mapBits (js : List Nat) (w : Nat) : Nat :=
  match js with
  | [] => 0
  | j :: rest => Nat.bit (w.testBit j) (mapBits rest w)

theorem mapBits_testBit (w : Nat) : ∀ (js : List Nat) (i : Nat),
    (mapBits js w).testBit i = (js.map w.testBit).getD i false
  | [], i => by simp [mapBits]
  | j :: rest, 0 => by simp [mapBits]
  | j :: rest, i + 1 => by simp [mapBits, Nat.testBit_bit_succ, mapBits_testBit w rest i]

theorem mapBits_and (js : List Nat) (a b : Nat) :
    mapBits js (a &&& b) = mapBits js a &&& mapBits js b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, mapBits_testBit, mapBits_testBit, mapBits_testBit]
  by_cases h : i < js.length
  · simp [h, Nat.testBit_and]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem mapBits_or (js : List Nat) (a b : Nat) :
    mapBits js (a ||| b) = mapBits js a ||| mapBits js b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, mapBits_testBit, mapBits_testBit, mapBits_testBit]
  by_cases h : i < js.length
  · simp [h, Nat.testBit_or]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem mapBits_run {y s ws} (h : MonRun y s ws) (js : List Nat)
    (hy : mapBits js y = y) : MonRun y s (ws.map (mapBits js)) := by
  have hm := Run.map (mapBits js) (inv := fun a : Nat => a)
    (inv' := fun a : Nat => a) (fun _ => rfl) (mapBits_and js) (mapBits_or js) h
  change MonRun (mapBits js y) s (ws.map (mapBits js)) at hm
  simpa only [hy] using hm

def cachedBits (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (js : List Nat) (w : Nat) : Nat :=
  let i := lookup w
  if i < count ∧ keys i = w then values i else mapBits js w

theorem cachedBits_eq (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (js : List Nat) (hcorrect : ∀ i < count, values i = mapBits js (keys i)) (w : Nat) :
    cachedBits keys values count lookup js w = mapBits js w := by
  unfold cachedBits
  dsimp only
  split
  · rename_i h
    rw [hcorrect _ h.1, h.2]
  · rfl

def orbitOrient (prefer : List Nat → List Nat → Bool)
    (moves : List (List Nat)) (ws : List Nat) : List Nat :=
  match moves with
  | [] => ws
  | js :: rest =>
    let candidate := ws.map (mapBits js)
    let other := orbitOrient prefer rest ws
    if prefer candidate other then candidate else other

theorem orbitOrient_run {y s ws} (h : MonRun y s ws)
    (prefer : List Nat → List Nat → Bool) (moves : List (List Nat))
    (hfix : ∀ js ∈ moves, mapBits js y = y) :
    MonRun y s (orbitOrient prefer moves ws) := by
  induction moves with
  | nil => exact h
  | cons js rest ih =>
    have hhead := mapBits_run h js (hfix js (by simp))
    have htail := ih (fun p hp => hfix p (by simp [hp]))
    simp only [orbitOrient]
    split <;> assumption

def barOrbit (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(scr k s pool (ori zs)) && !(found S N idx s (ori zs)))

theorem barOrbit_sound {k S N idx ori pool} {s i : Nat} (hb : barOrbit k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [barOrbit, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(scr k s pool (ori zs)) && !(found S N idx s (ori zs))
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool (hr hz), Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barOrbit_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barOrbit k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := barOrbit_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barOrbit {k S N idx ori pool cap i xs}
    (preserved : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (checked : ∀ s ≤ cap, ∀ j < N s, barOrbit k S N idx ori pool s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun (goal k) s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact barOrbit_all preserved checked cap (Nat.le_refl _) i hi
      (Run.perm hinit (extend_run hrun hs))


def qInsert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if a ≤ b then a :: b :: rest else b :: qInsert a rest

def qNorm : List Nat → List Nat
  | [] => []
  | a :: rest => qInsert a (qNorm rest)

def qLex : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then qLex as bs else decide (a < b)

def qPrefer (a b : List Nat) : Bool := qLex (qNorm a) (qNorm b)

def qRowMap (k bw row : Nat) : List Nat :=
  (List.range (2*k)).map fun i =>
    if i < k then fld row bw i else k + fld row bw (i-k)

def qMove (stride ob pairs code : Nat) (ws : List Nat) : List Nat :=
  if code = 0 then ws else
  if code ≤ stride then ws.getD (code-1) 0 :: ws else
    let q := code-stride-1
    let pair := fld pairs (2*ob) (q/8)
    let ai := pair &&& (2^ob-1)
    let bi := pair >>> ob
    let a := ws.getD ai 0
    let b := ws.getD bi 0
    let w := if q/4%2 = 0 then a &&& b else a ||| b
    let rest := (ws.eraseIdx bi).eraseIdx ai
    w :: kept (q%2 == 1) a (kept (q/2%2 == 1) b rest)

def qParentState (cap k bw stride ob pairs mb ab : Nat) (initial : List Nat)
    (rows : Array Nat) (pb records : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => initial
  | t+1, j =>
    let s := cap-(t+1)
    let width := pb s+mb+ab
    let packed := fld (records s) width j
    let parent := packed &&& (2^(pb s)-1)
    let code := (packed >>> pb s) &&& (2^mb-1)
    let auto := packed >>> (pb s+mb)
    let ws := qParentState cap k bw stride ob pairs mb ab initial rows pb records t parent
    qNorm ((qMove stride ob pairs code ws).map (mapBits (qRowMap k bw (rows.getD auto 0))))

def qIndex (N buckets flag seedBits seeds : Nat → Nat) (s : Nat) (ws : List Nat) : Nat :=
  let h := hk ws
  let code := fld (seeds s) (seedBits s) (h % buckets s)
  if code ≥ flag s then code-flag s
  else ((h+code+317)^3 % 11400714819323198549) % N s


def G28_N : Nat → Nat
  | 5 => 25
  | 6 => 341
  | 7 => 1644
  | 8 => 2735
  | 9 => 968
  | 10 => 28
  | 11 => 1
  | _ => 0

def G28_pb : Nat → Nat
  | 4 => 5
  | 5 => 9
  | 6 => 11
  | 7 => 12
  | 8 => 10
  | 9 => 5
  | _ => 0

def G28_records : Nat → Nat
  | 10 => 0x264592848d17406404023f43106465000119c401984519b4911346900c950540d1542d
  | 9 => 0x13cb1b08e11022515484286b9d91c4185c16d519dc7ae19e75ab625d8631904c420818c03ebad6c08cc024c80314778a1a1db4c0700a000dc79692a91a481a98e1909b116528cca2d718383a6446b019b62ad00412c18a981c2927716f98a948337284c48a04d801a51c4e1f0cd188a2a405d1e9073cd51b902010d05130b6b1e4e08ba3368a30134a02801718835165a4bce75ba099b7ed334c6d691301b6e108019610b0c5373a9401b05761b4680900d7c62bbb728c6c0109138286b371c1999c252d6e30a46d24436465680c0c124c3b875630a829486131a4401185129da9246610a84db03240360011519685b2374426e069b00520b51109841282b903421c0c333053a211c009441203aa24420c02299188a34544dec15900a330775ac0297032b01442cdc2b42022896d11acc149220043006ac1980733266e2cb85548bc70b4c10b079a833a254a749a3798f39bb4832c038c4096136e6e82b5c86e617ce748819882a4266c4bd865ba3240048015837151a50e5844a68d703253eac46ee356c5a532562fac6dd86a8166231da957193b1b423c90f1c862a265c3b1c59d8aa61a6e5c9051a80160861022cd1c5ba41c6e50e419013300c6470d85571931b75c34cc6d821161e6e4b9041184eb224566ec918120e0a4414dd1971e2b304d76d811905d3404a76c05db802900f75ac894282b5236c08d84b285b99d464c1505cc09b098450a4391023b9d6c72940141a268f5a54cc9028400065020c091313729e0c0c243570b35184e008c93b213914641b8c2048b2104521cb42d68335246e14ac030193200b650c85d80db32344749089dcca217d0013acd30aa200943694d1106fb31e566c62520e2d08496eac99d87b5174848b859206ab38771690311023822585ca4dd3c4b9394863ec55a5736324d14b41914f2814446ede3db57913a575fc851c840e9d4846e891213291a7606dc4d90d30104474c08930ee70bc41ee41139a293916011c2fb5bb4287026ac4d489b3896514d803601a92764189641dcf07984c16c0c1b8bab34773acc8dc5cf2344844ac0dd802f24448c98a9110b814e3140c0131325414838c885189aa018a78923d588291560339c4c55b8b056d30a01159d29aa100cb467b5da50642379c19c09a807594638e9d1f88874c0b9630110a98a042acca92862301a65cc405a15371564368a404923b244632ec31801b61cea08be9698ab500b0099299c23301550069ae5900d6175260d8c3d8721106e130e6899a37144873ec31702c48c062c983918ba223c846a48d8183116560cec892182a3c4b0ba018913ae2648189889b0e251450015c4d6d0a618562eb919c173718615ce43ba86241a4c085c9129b760e5634949fa81a726661a9503cc60003ce14c0032052318d078a406221261df21cec8d9972a815c16da619d6b13a7606e0e5d8634454a6e8ea824a041bf270991915baa1c66069001814c4022c0a8e05dd6a40e0454a055c1832247010dc2f9c09205580aa011805bb1af68c4915204e20e488a10a170d288d7201349d359911e6409945288f3009742e940b30836246c26e5015c5391a461acc3140ca904500a803bc910e1b5268c23049475082e428aa9640a505761ce04d30048a608642e175032608042c8855d8c372a4c10880328ca521580824e1c867ba1762ce275d833203503caebd590b730721004e15c5ab1ae575e604317a9074480d495c0ab146662a44e1b97b61777023660344a6164154e089bddbb39cc7ea06948c242a6a18d835202ad1e5312ac7114500194862ec75a84e3c565271101447b2427650b495b099a3a5b60ac01c13ad4652012c55b40aa1e4c52d51836292426c8cdc2e162a685d637eedd28ce80a4008dc6531d2500a62ece2d50aeb3a6e38e019c94e40449205e3ddce351e76639ae3917f60402071f1469a39156e0a943198e30166c4aec61a0ca330602ca0d1b03ae0e4a3c943100a3827520c0e1ddd3138bf662a89160ca8a91c42ba7511c2e00575aa459ca029008972b44f1138e3c760ca62881c2424535ec6361c2c30d582e9a2f30c222a6c5ea904b0f2a044c10402d9881210402cc00319c2a0e4c02de5870f2e81482ce8e971c7bb36c0accff2182d940d62c8c48cc36042028a62924ea9b8da62c49621d2a886402c06d90f361a568cb2c394cfbae4c016505b152e2e6068b81724e393c6c6ea402a2037b7e552b859781b3054c44b8011047a9e675aaa2934eb046503892b994d070d7628da3d5578b00771e941b517a414562ae402a872806462cc86900e079000428051989bb30cd026403c4c0e166610b82148f22155712b61e103e238601f0aa9085e30d5400cc59189ba1755200a2528e3b2a6464a81d20ea0196c2a8715d8d27055737cc6dc47a6345818a41951bb00c775a4475ca325885610843f1c5250bd000b09b350b6146e54905db2059295220c841cd6bb2f76170e29d91b713c85dd8612923a42640c1010382aa136a20ae05b5bb12a575a98e55a0bb887638a466380762a7648103f10221
  | 8 => 0x18575094e6a41b9285e600df51da12a63772d5160031c8d41a1bd560b98b2d9d7155758c9dd99b9c86c363a59428d273cb5b075e00b9969a3890c594998392344a16501272091ea5d18f3e44b3905e4b96068c133e2f7c699885059b18d88d261838d84e0dfb009c01c20e52386e0e13b9eab4265751bd0498594af1df16ad0aa20983b181c5750f848a607b8999e062a425ea48a13b0e26046ba9087c025ce53196aa5d8faa153a1420a637805a221944a9b4202421e2d9e531db519b8a0facf01de01a4e6060e9b3d9d2413299f7a166c40b94e36f3ead4b81a5752257500ab30984e05a0826ce5a7a3f40dab05ba73a405256ea93b1e25a8a33d043841ab4bc1c890fb090f1b9fe0c6c407a4f3fc81160111c33b380882aab5145e682e1233f7a1b96a066ea065948437d0383cbadb518fb09e01742aedafce52671c900c0896ea8c17800994bae3403f89247c687b2ab7c5c17a1e186c49e20737836a43780acfc0fbb7a88a12db0e0381c0e0110bb3836c5c8b0811f934119993a6ea0bd043857501901963bb265e618e3cc8b9f19e2b812ea3fddb098412244d27fb00b5753bf780fe9a1bd32059b33a5e60ff788db30061784994916491450d004ed21344d1a6c4236ea875948d8b4284b80ed270042012d5303f0b8a1782811c0607440cb52582530378318a829a258fbc50f86590301288a73a44a26f0c282072d8870ff7d01cb889420239ad9822b05a330b91d09878242d2859dd3241a1bd75119e4395e6a837a85a040e4b89a1ab09ce911a25c52801001126d7137a5b38db583e2a09fb63002093a332813a8799927bb28d865194b804f7ab8e7f40ccf01de6283012db1827a4403b4d1cbaf358c5280018949187516280d21bf7aa5d9d29d9d1871c09c4c1db6b239791b0170b999886c49b4b8942a40ca7e47ab52124f039509a25e9fa9f0629aa6020385f53be5e239341c7c633c7b15207245011a41a0ddd10bad60b44d39aa58f91e0c10481194081182871c938d23fc1215e092706c1b2071c4b9281db2f8c309ab1028522f83d8d5161777646a37065f530d563989e1350114d3eb8e6a1da2b8a420a7a2703b1d221af0604c23cf091b308d6b3030810c5e60ddab029b3015e619a7d258cc04f36375f53071c8f8e191a040813b00b1c2609327838a32091bc7b8f9868780109a818b99e2583826e3c0424f064e6040a015ab703838918b4986ea0624f0d89e877620f837036c445017a622a210890e3260c25e8b1b323a38b8e3c398f7c626a85e6431164a6160192070c57507d55309128791eb7f3e0fce90c0369593419a122f44a0f8340e71c0a4b80441a098832371c055f59d8fd00d751483e0be9a8c13bbac368bb8a261af9c0683389017838150bd19e1c9b8599b96e298a1a1575245e0198ca1bf3b2571c9a22b098691db0b1c4208db40811e02f762b15759b99f040811659423c68a7ab5038e31bdb99811c1a71c0a9730941a03a1f405169a101196ea0f918238bc21001838ab0d81eb496d8a33d98ad6101be119fb40b7c3f41ac6bb728b851a7622bac9040118f8dc03c9313011287621bb6bae44a961b317f898f9a434a6614c02165f503aef9ba489da6d9386e86c02a1a0919e1226212101b30ce3c385941c78e01d16386c4327760ac42328778a0a0118a9408600b516a106c19f3b195e0a613e054202479aa220928b7802cd2167c02e12d33e5e055e0885948fb4322405210740df7623a4b3880c17e2b3a575901bc384051a7762221e30a96459dd15d9c016c48904c23ed214b8d3f8383f6c4b72d00df9a12844a6334224208598b8b9509c22ac023c23336c13b08da8187a2d241af41234b2f781897c0830102e2a2f8852f92199ab532b61041e99bbaf0bdf50422ba9a3705d260b7c627ea49bb6183a8d91b2b3426a25db5130179196b42aacafd9d3b0ac3ff7814a75394b83496cb02092824f28f78157c68d8690c4e60d44a1df0b03daf23d602e1dfb7fb0918f507c659babe07f012397f8bf7a27d82154208d9998951631f7a2a02519ca531d8fb1491ab9499d80c0383a9bbba07c010ff7a0984c185e69d98daffb02a906280f02daf7146ea118d803e1c1a95817c021c7c0045e0a78bc8a001858f50b9dd13d3b87a981a44a8bf8721d9c25a5b306b3b14058c38116b3c37ab5876eab1a9b265168597309a7115ddf4508139b612444d85af80b850157763039a0380f0fa631ae8099a6d0c5162e362b944a009f52271cb7d8f05cf00e5f5929e3325e629fb60b952b0e808fa88046eaa5157aa24b12a5d93bbfa61b48d9513220a0bc6509c65234200131c8d42017a2b2341a2678e07a7715f628be3c810202522b1c6c485b29099c8983369405c056ea0dc20a61b509848174b82171c1024f15e2b322a8891b39a0e53fc200181a258f01821e1b9341da84089b00030128a261544d14ea413db32f8efc205c264913041a1644d0c4910396e179fe999e18bec4875e6878b41544a0da251ca3403ae00cdb530bb8898c1282d213c998c16519daf07e4f00ac425bc2a79cc222d20b865259e391a88195018f93c0fd9d4281d32516a62a493a3f1f8e326d040ccfea15942808917ad70bc01061c193ba703b7203938190270c3b42e5758c089285f5056c4240f0411ab1b280261329831c041f7878502844d04212b7d040a0110df7a2322ba620a960051b0d23a41a03a441fac123981196c4139b83048125a27c49279a3840bf010d95227a313bdab8944a8e04c0802e8c0e9131b31622b3278e8c20e058f009999bfba5a141a887629b907939cc1f83a1184519594a520909c028c065165759a22aa5c42901489844a0991d23aa417e129bb3b134202822b096c48dabc2d87e09f013f027221b33a49123d279d2073c20927d8f0f8892eb562d5f53f44d2850125c2520882226ea8fb470033419b3b85a9a0989a0b9040641a085162593a25a3fb14e6404201421c03ba30bacf0801103f8493aa44078e839680dd04a415f15c6c0fa3d39a4423b5903b5f3b8c52ec5c2596d003b401c1a0f952129b301516a137a9b71c21934034209b9812544a85b43ab8bc8d50103a982fb032644a1e21e13c4c0b6c48db260025e088b223825060258c1482e164c105c39f7a9e1be342a8a78468f99e2e6b3051d10d9fb326ea095010df7815c36469772e39a90326310021e8c50b945a14059e22b038dc383783844a319a58ce6a05852c123c8a6ea004911aa7a2794b281b3242a4c8b1627bc2919c81df3b0fb2623de5385e096207015e005a8a8e6c48837d2785a8faf8019f50d8a913594a15010a6c4055940bb01039dd041783844d19a841c9aa18838245753850144f7817a6d05d601196a060010bfae38a7e27878b18ad0b8692e71c0417525a752421229aa42e2a80e0e92ba3f3380b2fbc32357539db53a44da58362ec420dc2e1a0f408acb13ed2175012ffbb13cf041ab51015518b2d2e21d3c94214575a41b324762a771c0fc651c09325a3346b331de121295324fb0238d023822289818a04831fb0879e409bb63271c098d1305758d92c0db381d8ca164208a3540ef78bfa3c05825995f5af0543f94910097081c1881550e001a9bc222384036ea1a969041329630c2625c1421e065169db463ff341c4e6919b00e24f428d92424b25d3ab89d8380cf26dd123b6a0991e065e6018b8c23b003b97814203486d34156159eb9a2071e81d0544d93a220804806118341553971ca61538599e9bb9c2fb20238debfbb00ff268d8d111a1b87973938f018827900cb407c6c527f0184a080893a78e211b31a39a24e3ca7a060f8ed23a3f17b3b17fb48cfb003b6b384209821c85ba1999b50020c26c5c095e046ac837d5634a5d2985a199580996b8f1b30b96b078d417e1e379b030a7c244e6a144d11a849dad7259b89bad7276ea190d225b6833f7809ba30e4202185f0091621c889e1af0871c1441a1185f4041a40a64059810bb90a922b9d9981eb9c1c30ba807424d8f0d9a937de00ed05386ea338c5379b5325751c0120604805aa427db53885d060f039f9ac21b5aba27452d217d7504048a59b5b7ce5c4a379e3b599d8f99e808e95d4693f06491452a48dab7a61df2aac9918dca5ab515d752e5161583d0b4201c0f4260f4301b5b0e3cc5ad60e516003b03896b24a19359c2c51279c3ac85b3093b34279989b516c63b00a71c39878071b30024f85c604683fb144d25f6f09acb9d8440aa041980a0dd4815b6b0421e9ba2b23a2295a2b1422b312a88f8b4aa2a80b8a92630b31e3c1fa4d25ac33213e9b908b942001f1c05491ae420234e60807413ea403bba3888b83870177622982221ba4ad1643a50144a228d93b234b89c21207c021da1e0c0209622a1dba493a12ad5e007a3f2f78e4081ea15e018d8f263b404e2a39bb203a123ee3c3c96d1f9689029a8a24f0b59409a742478e00f1c940f093ad23297d389a402d1c84301324e6ad491af1644525e179e5035e607c4d0e1f7264200db259bbb31471cc51e22113b19d049722a2244a3044a1183d987628584810081b9e3c0ddb5aa80717812184912dde527b280dacf37ad609a9a93f7a03bb304a4d24ad783b2e9e09719ce5398592e7c00f81006b8d02c1207f26199982ef3e9d22a1bce506148bd80b981b305d181c76207d9c32954875752449193a6d145f58389423e4bb7e3c0bde59a37899ad6045e611a630517889b47a423483b1208575461b5b7d94ae6ea1a011001043413e002d28fb3037b2004a639013b36d5509a4f2413a9199e8f8468ba5b0ac6841dab2ab6799e3c9c1530dce519ab7b9c5c3380e9a3ae1aa80100010dfbb0b71cc11fd226b33289b9a36f299d31b3bb0795599b2090089285169b8681f8ca2676218011a6207aff113190e25a7b034b830aec0db6100d16080cb4523cafc5cb3e340e07483d538144a184b811a9eb720923ea431bb28fa7204d5301ac49bbb23c20718776223363393f8d7c6038fd1ae3c8db290359403e1e04e121844d89b5428aa50fb9005e2b815941d9341adb5a79e127d16305f5a2b42b9d8f0f811235e005575175941440525d044009d0c71c83a9a2789e93a27a9336c130c0e1b39d941a41df32209c223cb7f8799e4927a25886ea31c20a31b325ca5880e6a237a1cad83eab52b9791a4918db2b32132343b4a337a1315341926076c4a15f52390c1444d09a5324f11970d22122b2622b1c21e406ea13c8910048239498404c34a94220f019a44080c01a42027a08142122224b09f2683c1705ea402f3624de52f6ea00516859fb0986505b040829a8a3810184dc891519a7a00212a5e3c1c44d25bb8aa0990bb250e32929c25380209a04a1ce3425b6715a88044203fcf032a9b09b28982ea2bae609bada6209136b30dcd03f71c2425c081b39a1830ba04395f5302a817f3b03f9a97207960d22ee3c008911771c938380e59405918c89a32e50105ad240a342844a340422ed8fa98eb9e18317c120ead18bf110c1b50a4050dc010644d27d9d93e099193c0b6ea0faab385e62644d9e33b05ddb09f760820e99fb0035161449101b1c8749123cff07d718a29a859b01df7816ed002db32e036ae76228ab032164139dba633640e34081be1978e199c90f8d82430b0a1b328a51b18460c14a179988596b3caa00dd562a2a498093283818c29aa609919858299062988d8dbb99191e8dc740ede20582a2a8a4aa13a217763f5e637acb8791d19d321db3b180120585a3415304e09450f09b9c22677613d753fc1718c5c0e1652241ab2de2238f0a42a8099f81bbc3af5f5a19df13a1e03941305010071c3244d8841a939810bce50dc650f8623f1e02e40587c740dc36213013aa5109e9a1cf782e4912422b9424b27c8883ac19ba9b0341a17b2d3fe4b11b310edab9420c058228381230b6811b200f8a9099dd065e08d8dc8a301a14e615c024520c0c4b80b9b583b793d99e83a481a50140936a62a8b8c200b9872fdb5875f5a31df9dae04071c00aea489490ffbb1671ca606c04db3154918d9dc246b31344a998e19d0d293a8a135168d99e3f5751644a9e212161be25c688d9ddb17620c07b0fde513f343aae98f97323c2518a92bc80e141db155010aafd08ef6ad44a8a32619b4d895941b22a1ae6a469288d8740ba250057501d01245f5321b4c537a3c8c5058bc261db0f9e4063010e08941b5919a2b3f50119a5b2d99e4631125aa400164a8157081f736e3c019750e06587b012f49109a0405f34a5ad62f5e02a882243840586e0fa9a938220a516aa1df224b8899dc88fb403cf42eb18baf961bdaf1dc681bf11259b101c4d83a04c4de205979a60362f44d8c33d153b50e762059240b9a413bc209df5174911c41aa506c1c776b2e348fba1981d13f981324b9395751ac5c0fab8006ea8a44a8a07b8fa2f1bc36041b315fb4038d4262d2005941a5e62471c12e09269b7b4b9faab8b8a1650b80101d753013ea58e10bdd112f7a91af81af541f861245940020946b8d0671c2588b099b02250109e091314a25e0c1fb6b9fa6d101182e13205a3f25b8ab9762a81df2641a0dd3b2f57524f3e1d2341c384a407b0fa840626009e0e9833b03998264b8a57761a9d8a5fb025a6d411d126b0c85c74172d0c03b01996e9017822df5a5b208797145012149d88f8f502c5c1ca8e07996308a8185e08a260311320a49101c9107ea48b9dc9a0369c11c8fb2b2aa818c0018f96b0571c04e2b340a519d7598354254b8a20603a2d0884912f71c4593f1bfb0237622722b42b149605c1fb05341df019e68d6c4afd8f31e341a7c6045160bab5399810c2340e57505c4809a2d05e9aa61b30ba9aaa06c9da4831c7b11acf19db52841a0fb380724fafd041922a2f9b585a27404914524b8c301227c6b8fb015b5dad4208fa7d07a258d59409afd255e6165e00c9a48ba7225575a1491858d440aa51014a1bba4987c693ddf083819e21c03d83040291fa8d24336062d23ea3c0802919a55392d029d9c325f51941aaab42221db1c5f590260324b82278e098aa2389d1c22b169c709b262e5e63871cad0a513d3a08001185f51fa88405751b6ea0f999af3b41de2b09cc11980c2442036fb00384409a7d3a85e01575166ea3fe0c8d920406c432a1613101307768df294615683d011621e2f41a3af9a1b8ca327c0a0c02136ea19b6b1089a2e41a155f53a9bb942d28386815516810910b925aa1d212db3263840544a2390617a128dbada820913e4f9b59424c5c05c6535a94a3516241e5240252544dc6a3da613a1cae907c172e1e5af132380363fbb21c21c1a9e1240d022516184e6008202733609a9825a721be3484089a6025b15942421c0c0818d87e0ba2d8a0650471c8db278f841196b3939b100c4d85a4732de505d3a03b0b8c04c09b531851699f3e0694b3fed28a081198380fa2526594325940e6ea9a2120616519dd10f9ff099ee2fab5266ea2106599f11b15e00fc1100d0104ddb1951623ad7037623a4b809abc271df2e002919dc05934227761744a239d318c271339a09950448223a7760c41a083268ba7d0bdb53a5e0155943a71c0c37833dab09c489037d078c32813b176b31de1d9c0ff21b7fa9913aa0aeaa22a981af8585f46a22428e41fb8faba22055169b41a27e3c19bba17d558bc5c0824f04491186b303b462b981194050fdb58d9ff2537a27594301df87b26874202230b87b25ad7c61f98d239c0bbe3442bb79e22aa60f0900a00005c3ad2d287c60e4912991d045942222b0df1107001228ef17f54468eb2804c47ba913f010c42041db54982203a1e93ea817516a994b2fad60371c0fa6c0c7761c5e00fce5130f4a437a9c2079e0d23f96a18a0229ab193a2a175f523a3330420409ab87b2b811f5058a9961d11841a176c428d822efb032036066c40fd6521e3c040011944d23b18a415385874b8aeb09a310da06b171c245e69825e160129b4911e30b1ba4421c3626b671a5f5aa29925979244b80d081240999e3363db0ea68c82b90c0fc481bad933db500eea9020e3a7c6419b5265013bc7b3fa04baf783f44a08178453349ba6d031b303a351d9fe258223999f3a4209dad61fb1223ba73ed16239e5349c2b8f782412d8da2db487109c8904cd2c4d27099fb09e4f1dd320171c99c4204f0b099ed0fd189a3361fab726db51a01231f111c594035f51a6ea09a632f996210c10d1b324334407762982509b01a62d0001d198420061b323ad22580c225f5a637ac49e2a51df29ea41976220ddfbaf7a03c120f89a265e01571c87acb176ea91af1305e699a272541a1c4918bd9d816ea49b638b8dc8429a8c0c0245162b9b848a271187709e07388da119522680c9b501c623c0ae3c06329a625101175175e69a33bc530c9a1b3046c42791d1bdb505e0c4694f1192083a6d8d49127ba7038aa87301859202359423b3985abc038359bad611b3825cf0306ea451db99c5c998eb1541aa5c5c162129d83a89b0e0dbb28741a9a0d235942119dd2a22b2444aa60812f594b72071b844098019b776265f58485f2db4783cd28da430fa81134e68771c28575a5f0c840121371cafe3c000018787423d551bf780a87a32c9b385163244a900650da632fb5d1f9fe21516c2311259818c1e92f13e164b8015f5258bca5153982121971c0794c36d8fa5f3ea42092233425fae05d561c71c01aea0833d0f84528822b1501156c40e3232806513c019033d1be2b0430b44d9c30db58971c85f2930164a31534017e8aca50497d0fad34044a164e69002e0ba6399ae006575bf82f1a4b89392486f62019169a14a055010db152a4ff8a59442a3d03e121de1e2104c034910580005c25069d804daf2e776aa3349c0d2220d227ae68a25e2094e31c5c14420135f5998e59997728326246eab4819ad5949e3ac8a148064209b5e60bc361eb8dc018f95979006c403858878aac118f8fb7d381b547a731401219934bf8802dea3287761980f284b90ccea8d85026cea4286f13a08a806c3204d468bf28a3125a22181e525ba73996a8bb13bcb5804118a81531191d0afb0938bc9b9a5a51b30ba219004c379b7224e6979de0b4e69a0200f9c831f780ef6611810b7db53fc0239a6405ed23113e2221283a1d25501b8c7b13d320bf6f0d801b300214bb8a215396336195e693ae6aa20c404b919abe2f91b2f864165e60111687ba3878dc01fc0168a20b88345b632e5f5145940e5e0326b32730c04e1eac8710bcd045ab529a221a44d9f838badab0a8e1241568f9dc0ea3f9a093194911dd108d4e6235e60e38103bc32392825cff9b998340ae0d878451b585f7a89b30199fe0fc899d3bb97b540c6ea1be3c3fd60384b819b469a1b5a144a19bb312e2b04f8446ab50004c034052696793c742f5011a40500c4a9e3842796a384e6aa336377760c1b3407621a5940df260de3c0b4912833603a4a0e41a05ae616a6d0023c3ec88156ea3fc99040c00b9fb2788d884208d71c304b88bfb00015513d603f4b89b44db141aa81b4943341349117d3232501b144a000ffad13e2715332420af00232890259c08f9fb039c90a0a5001b3
  | 7 => 0x25d988bf4b630a5dc964a707827a964fd25904c665580392a502a9d8b969cc679a9592dcde3e30dc3724ea528b95de3674209a64c102b625aa782647a8590ac563008f80bc8e313a195a88e5e18d83b4fe23725aab22e4759b80189607e378790263e3181cccde1b914a39c527130b83a64e9192e27186e4dd1792a496a93999e18261339ba76c2e3d98981821e1208da8b8de8a10b9a96660b10b8fceca6f69b8fb0be3eb0d95780e2511487a66621d8983704e9492599b4160e9258d62363f32de7189624d0de5b2664a715a8388e24d039b74ea3e4130dd8960132381fa0e30ebf999427662098940fc793179bf42e9df29a1d43e615058f48176e50b9fde6032985a77c26258838e76565db199a003632ba780d4146af148dac3e8193195462e14a8d9720832a48f84cc2e2a0a5a3d4de0b19b96b82e21d2395a837341279898987e70586524e436179835027bb839776ba69605aa4e9e20c25890c269d4188fca166152196d4928c0219dac8ea9333a698c080627cd24547ab039da2275cc07a524be4d3059bd5028281da3742e8d30d8d205e7680388e0268bd0d93350295b83e1742e82839a46c766dd399d3c6a7f4459362668f5319eca666ba83aab816177939c282e2a79a0f442e3c23f11acb21513f910a0e2e20012526e5e717d2d8ba26a8b98f48e16a238c9c828502f86c21a0b88b994a2e6a10b89401f21621816cb69fd8807e027301038fb44f624978e2816a520bcd04964ff3faa404c85d8d877e205bf078a2c32a6009a5f04c07a259c8ec45ef21c1fe4e24d2d88eafea408f8a541e96f09a34e365242783488e66d87a100fc67703a3740f61313cca5124b30610046636f1ba334b609c20d3c0568ba458790b62859b86c0668770294602e47a099cf49618f1b8fb636a210d9bd44e3df9d9120571a2a780642e0b1298e9a206af14888496177199e98fc6af059d7cfb5654080a8265fc041aea661fb37909a3e475138652664d3b2a0a2769610fa0603e4f525a8302f96c3f1252e3806ae8a0e6e23385881a4e3d22792de4e0e909846800596039fc83008a9b8d2c3e8910382f41637a859dec0e613002898967a63a8b584a4a9ae92260f37607a064526919398b41e5558785cc16881178b89029dc37aa34220e499a56a58766838d00ce6b331853216443209d0c5e6d62583a42257c859e6cbe63d17a336b43b70fa71e5e3298983b69604a13e7584a0c49b84ac1e0393fd7326861393a934ff806859492ba8380b80e6669da8d8cce3e871a584303a69c0ba060dc40893a3402f99e149440be80509a3bc976779386821696c0b912c863df3793f4005158794665e8800b953cbe90b0ba5f2660e90793341e08d31d24c1e8be07c68b1220f3ed5161e74203deac688100599529e56a399a08de39e05a71e964862d8768de013001abc7655893a336765e7182718173be21a5d89f54583c4666e3c225a096362982f82c4de1b08d960c2e190038fc45f0d831879096462379c8cb69c62e99750249817a466503432592dc8e6369397862e0ed95a698ce8a71393249e194998dea6e053409a222608d982aa45e212001020da0af3788f6967140b9038fe619338792a04011d88485e2f70d815c9e215899948c754585a8b8df3430f97f09ea901483e6369dfa5909a6e5582981fa268690a27182a9eb8d84cc9aa6009a8863e14fb2a9b02796c0d8ad03e9cf15a3368a94d0ba5be6e800a3817c161f9298a5a589ed13a72e0f6ba1489282e03d27d730369c7449c1cdf5968b99964ea900f8d20b75150c201a5e8dc398db43ea210b94d2160c0999450961f90b9d08e62be279dc85e7a59b88108734921a8eca674027d6d020545858372285bf09827a2e6a3838dbcee2099b9caa1e650039df6706d90599aa96a8d0ba7680b9353e87c016343058d74c840186ddfa682d0b28e6276a05938de82629d4095c4dfa65038aac964dd0ba6788b99eae9a061e9f8998018173432993fe661b49988cc861779ba7ccfe0e92894ba4e35819a3b4ea02e0b8960dc30195a5846662925a790ff1a20b95bc276e5001514de05f0ba17e180dcad085a7032983a568de21d22c1fe168d39b85302e94e1ba838679d693a95c2e13385d450962968da1c4a666d0d93d69ea358b932a3e7e63f9028269c6898a0e4e5252590b43605f07d516167f731a7f40c1f89da56876919a62678262be08918c2e86f2f82a86ea750b81ac5ea759385d2e66ef1d8f722e9460da0624e07e1ca56e1625840907a688060b8fac2fa650593264e7c91ba3861e21e059f24a62f42d16a42660d2d8ca05e8ed17d51438401958a14e65148b9ea0b67af8b9822965c5b91dfa2e9540781842ea7707909ca62f10b960e3e30e8f92c89a34a2815060e5c78d92c88e52539d7301f3b719a7cc576ba878cccc30a025c10e0f2d02392de9e1a00f9ac4fa0c1099a1e164752790040e2780f9e7e6e9b9258bc26081429937c2e97e8f83b6c6578098f54907331d8be48f34923a0b4166c1328ab4966361ba1dc8e6c1079ebc520ba9782fc0e91919dae81f119a59db64e0082990da1e24b3ed6d21e9cb0598d8177e73f863ce077e14a5f8369a38b9ffa16a9e239c4e6e4200f91e8de1c705a9366817985a60e60669278e94c39c60f90ae1e2b40b856c6e3d0979df28e7cc2d1d5cc81190da7f4365080993d62ea9e0fa1ae5893523a7902e1fa8825b02a02b0d8318e266eae89e6167153f10e64e3273fa49c36a852e9b58b66822f8722960b117a2ee663eb259ea01e2583edd5e221518f9328faa69ad04666610c05d006661b005e5b09a93d2d817e3e563838dc8164ff8fa7e01624d9825e26e2513f1b8a264752fd8881e9c70586482686f998fe02e8400b86509656f981ead1266517a376162b4959dac3e7420ba01e7062427a71e768004086309f4010b8f8cbe1fa238d620e6119812d8bf4b50590041e51793937c3aa0f25a2361668797a751021b309e2f4e4630940ca62e9cb8d8f66260f4148b523694c0ba71c0030c8992c816290841abe16975961abc5e7e393981c327f493a8d4824b10397c05e30017a21c1f82e05aa42686ba09a5d61e2500427585e263a98935129130d8b24007ab3e80f6365c117a56aea3980da5f26679737aa74de7a8389103022c10f9a1c2e90b148cb4a66364493fd028ec9396765e0d8448e15122b509836466362298bc096a4d0b9b5c6e98b859fa452762218884364274480b8520d62e1df90226199814eb47de0a12da3e5c80b827a166fa1b9b76862cb158a2c367259d8bdc8e18f148b2c66750099f64be3c237d1ac5f9d60687a4de1c809a32a4e1f917984cfa0fe3f2248df6e203a2e81e0e48388cc4e9c70c2678371e3a586e4be21d0013c2686f91d8fc4363f81520506e4a93f86b8161742f9bb49708a97a95c0085d448e964e7409b9d0c3847d37dabc822053795981e2920592dc2e1ac89a60e66574269ca26e9210a8a0e6034989d6ac9697215d3c0df780038f724a6bd21d7be2633d040ca4963279996605e8e1449e88a69a8449bc48f4010f9334660c326a47416a35978afa16a210d8a9e5e9fd3f8bf8260af15ddf8e217f0b93241e125960ca42e1c89b8bdc3623897d0226634a982758de4a7242718e008a2fc2822e1209b89e0ee0e10b861c5f99e8d910e0f129058a5a689d605949457a65158f7e2e1e427a72c368918391d5022083fd4560e9211c9db0363a99ba56a4e2f4258bd23ea6ea9a5d81e2858da37cde4b637d2daa6a93ac94b09734389a5b0266f5170f0c1f95c3aa9388e0af14a18a4e77c0796be1633d859820de8f58b8595022dc09c10c2ea6a078d22666a8839cc88777e4087c2162c98fa1002679bb29b68577e244a8501e7fe19d84cdea649792d8de3c209a01c8e2beae9458575c9038750662121d8d8a0e6af9424d44ca43a3a7f6769f33a9a8a3e86f998bdd02775001640208bd379660b67190a09b2168ef9a1eae3e0f48b83a08e8621d92804c11931986c8e2a689972016436278f7c0ea0e0f99409e32b09d454be99e2fa9a8005bf37886c1847d8f910c8e4ff25912c5e4223f921a4e34383958c3e319239674369bd0d99ec9e5a28788543e97c3f1fe8bea8d259d00529830583b2269702fd988668ba0b934c667680b8d205a5462e8eb28e39c0dcc044e034078652961b00791e8a604f1591884a8ba25a6248253183dabc163dfa587e8de71409a3080e8cd238a40de9fd1393fc3e96fa620188e62609a414c082e258020361ea89958c60a26221434a2a328b84949623f131abcbe7143ed8082e2b42e9efc6c9781d83c4266a389a51e0e64a8616fc265198b8cceea38b0797209e177099fdc9674b99912c2e8ca9b9da02e37a039de0265f097817cea7bb0f88e01834319d9da0e98b3e86e66e46444a4788e88d2398960e7f8a78a98fa1fa09910c887e7999c525e68225cd06606af238e2a66a058d9fdc2e82505de00360d9130b408e1a00bdf9c36807408d5ce84010ba81a16120178df20e6298f9e6c2e5fc37aa7a964d3409a1a9e8be83d314de44b198fc63624b0011ad123009b81f22382e05a5f2968a117a81452a180f98462e3c009a0965646e8795de160d903884826615239f84265249b9b345a6420283501676b2e81e2274080d9a1c6f6130789ba280dc1991905278b85a064de1fb2614365677c941004c658f148bac8e60d039a020e07c8a1abeb740899a0c02e08a398824de04e2ea5f8be7a8189226a65140c0e50162430f8f646a2008ba60c9656a9d8c00261653f18c0db341838bdc3645185a3281e3a93f060c4e2580f9fdc1e8443aa3102e1b9a9a624de63d03e0500e0ac09a5bc6677d8f8528de1fa8980ac3e5f03ee88c1e14a2192dcb73012388e8926a40ba016167fe8625b0005b41da2ea2896c259b0436819058680368ef37dcce6612f279dae169f92fdb66fe47f13a9d4661ad23a9d26e60137a2082e26e239dae2614f13a1dc0e72a25d004be9da878a623e5831c8982585149a290e0e0531da334bf34185a72cb60af9399b51268627dd5c0e77f0baa343e24b1992a51211423e0b84f4011b9f8cc099e0f9f810204b0fa3b4a63279385dc2633312a8a82e8f50388526630036a4f04e4a0938d76ca1b60980e6669d68fa318668e109932822668881b9466a75899b94260d193890c969da149a7c3e9df1288842624b9782bcfc59627856c6e6809820405f6ba85813c1e818449a74164cd99984c26a062f804d022d840a8c82605f07a0943e21517d84c5e3620313c0e08068f84826e3f1149fe2666f1058d6502a6915a3b6367e60f909c9208e21a69a663c227a830003ae0b9334365fc9987eaa0766248e14279c64187205e9ce13a3761614f4099d05e3ed448b389652525813cfaa2515a0c0de9bd938e942684087a558106130997ec3e6f51798a42661113d84c16327178038a66c109a7f4fe229239d008e33b9b8dbe161bb98184e7677c17cca51661b23a200764a9ad2570de84129a205126ac8da7e2ea30999969e2e30e8783d0974b525a5d8de0e99a1c246e2149a04642e6150b8334ea77544a2de4e18f0f9ec45617c03a1de169059a0dd80e9f3039c28961948f95dc6672a978714be42d000dd8a6358098c3a2eaa587a886ea4fd0f8de02e0b8379d749e0c637a76a4e4011da838ea9470b9bd49a206198aae5679717a7ce668a10b90b4262b407dd5c3629d2fc10e3e459239a082ea850d91e8162f805a060be76da58f0a0ea753186e60e6ba23937c9e9498b91c02e650128b2ca616a17c2288e560159e960f07a07aa14fa4413389ba0f3c318a65c2e77888d5140c5bf39e7181f5411ba2ea3e12507a6d06698bae8a861e04f13a0964e4b7139dfe16583198f724e578238bc016238379cbc9e5550004641e5fdc494b8822cb099bbc262c905a0b49663d938a986600d38a20e5e5140581ae681e323cd0c1e09c32818d12a350f906c4e5a29ba738ca32a8ba1124e3299990804f34309a77c2e4a725a0b42e517322570be26e178fc4666dd219b24e099e2fe6782e1f30b892cc0a230395608e60714a21a4e16a2593268a64f17d8c24e2f12d8a487249283a1bd029999a1e848e00805a094fc4b698111e6e39983a2d42e8ef0ba8b89e8250b9490270dc0da7b80e4a00309b0662149398da269cb1d9da2ca20f8f9ff82e1b01785ac2688e0988548e177379e98c007f898a602e67b8d91dc361fb8d85285634b408ab60e00683c6082e8a12d8a2e2ea640b804c2e611178e64be0e98b8a1a4e0e20b9c503611a8b9720a69e497a75a4e6c10992da703c32596744e313329650288bd939dacff9c6
  | 6 => 0x1134c48583813c580db4e10f6573ea1381d5561e150170ec14cd04cd3221e3151737c099b6cd0dae267f6475c113ac49b89221e94b0b47f9b93e84c5582e43b0b0a8848e285cc1c2e8cc4331d2f81c02cf8226c0d1b5b68bb084cc78a2e3a7375ac13a7242d88c2eb606f56127af001d78826cd45f0640783241c9b8b6cd50b44b301b581d04a16c000b0cc07a2a0455ec26bc94b5e3239fdc4cdd41e95249c3a878e409d12c168ec3353d83974c2d95e1e3a65b61e2f9de4cd874fa5da1761817b21c9d300de3310f6230d87613d5825688d1745d238b04ccc78b6a5307506999e444c0bcde0700fa790ba0903caee66b583358d2de710a71ae5e7f65f65f938adc1ce10260702716405a8541cf220e88c2b4199ba4ec9d1189eaa30b51e2daa911d78c9e5e21708d17ac6c4c1c0b75382b167999be0ad01c8e30c472ba2daad41d4c8de8d4134d621942cbc0e0be323071df8c1b58ce9c20e0a42f1443805603ced6261513736a0583584d0482e070273338da2ec5d88c8accc0b5c18da6241d6365e0720f65899a7dc1c6da1eb07275c10996a93c1848e5365b3fb198898dd634307da0b1dd219f00ac8460e7aa7d14d9995a9f440c1e3f3072ad1a8bbc9d1d8be7c40f371249321bf0ea1e8f41319017afa89c57c1e3a13740787841c1c788844e07d6032eb1285ce3e0e2127d1a81589012c4ae0ec872b31d25a81cacb2a6e7aa2b1329993717d07a1e4da2f2ed3eab196ca6e661ce0b1d00587641cd6e681591318a088f246c74c86cbe7d0d2079b042d310968d44b2f431a0a97cc1e0e63d2b0648da2a13d378dc8f12f4460483309d800faa2d1b61083a5004ea70166ab0f5b62d81c43c1c05a93a7d4f005d3802d4da263912f36d23b0f4cce56687db1b6573e95cccd698260862b1b5239b691d5589e84e5b646a58cd44c4260e1ab2b36a838e09bd1e4160c333407379c3cccf62261067d57083a27c1d81a26a53330d7138fb17c2348ea525f118259cc96cae8fabdd130ae09a6bcacf541e8ba27a708d85743c2b81e594131d00009a41d3bc6e2272b26d97b3518c5ec8eab46f572838e505c5ec1ec75071fc15ad604d3266e395171090b95a1f54460e56b1347a1383083d81a668206f3968ba2a44d88e6689f1355209ab642c74e666270b092098881bc6665eab413a48378c5ccca6426aac4342f07a6146cdd4b6bc80f433139690602b0368250f4c497a9483c42626caf4b5708d88485c6465e383075ac
  | 5 => 0x5d0f17a96130c84e6c84c6107a6e0f1a01e6b16c619796a4b0860e1809c9d939cb073d8263584c7d15a6e0b2748e0552c80059b21337c0ea596cd3
  | _ => 0

def G28_buckets : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 7
  | 6 => 86
  | 7 => 411
  | 8 => 684
  | 9 => 242
  | 10 => 7
  | 11 => 1
  | _ => 0

def G28_flag : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 256
  | 6 => 8192
  | 7 => 4096
  | 8 => 4096
  | 9 => 4096
  | 10 => 256
  | 11 => 2
  | _ => 0

def G28_seedBits : Nat → Nat
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 9
  | 6 => 14
  | 7 => 13
  | 8 => 13
  | 9 => 13
  | 10 => 9
  | 11 => 2
  | _ => 0

def G28_seeds : Nat → Nat
  | 0 => 0x1
  | 1 => 0x1
  | 2 => 0x1
  | 3 => 0x1
  | 4 => 0x1
  | 5 => 0x390021a024080208
  | 6 => 0x4802f065d0ec00280a20c1c00700201081f3c00306b077a002411300f4002855401b01a434900340ac0018001018d947003436900280030004044168800102d4007830c0b600081b5005c141001400400c4007005401b083c003010018b0004003002802481d803d000c03a001400b021c007819c0c706700020010005006c0e506e0006075c018016005402040120018013003a033
  | 7 => 0x4c06400f00e0694010111000800c49001c0008b106d2893051032432163721f0d6417263203c8558296048083031402a00100100d6cd8961009970407c05500c866000400fadf8b7c7e80f1083000401c1090028aceb74003ad68044a7200301a00d06220770368038c8800112b03fc09039d0cf87d40380a9036825801802004a800444158b021008c09a02500102e401004d00c01180362e806a02a6af0006b360c5c00357400c00dc0a806b0090028aa401303b80cecd82b102c800ea960ed00103cc00209700507cc2500bba93807801e0010048388100001012802055e008003014017a04a0039b2400e0e1b36001acd80e707382042eb4fe01352a40d80f7b36000c008069037802c6f60cd00d80942260c809b80380660050048154504003a4182080060ae057827820a0a400311fc40000f182011400341e01a801801e0c7282146815f3f800c003011803b10a800406f3c0001cd0c00602900301ec02a05a001001001a0c101c023800c05400b80280860160c400ac16e002002001e5c60d2004800407166c007856c00401293a80ac03e05a01980b00020d800203c803e001002001c04e0199308004234009004043402200192403c015603400100240a8004013805805603f00083ac024026003802407803a002802004601000207e403c00d04180f40020ab922864011c04b0058024016006001003645722400e800404c0560c080080fa047015045001b66c01400464160090188004054001003800c01802f01200900460010010006336002004802c0041a700e000802e0028b300381ba020005c4c014e0ec00e80d61d0002037821400806400380c6cd8028006d9b00ca01301c000619401100181fc05803b001801c0ab0c401180380ee006002000c00403102a0074002004001426c01003d047406400b66c
  | 8 => 0x16c81fc008bf10e309b834da1f000e80800b9f06d780086340011e80460068003026acacad800201d81b80464002f8047000261a02f800f3c0839011800c04a07c11b001015d9ac12101b023805e0cd840437032ed5786600320040ef00172d022400100040429d002c00932940b7004832431011aca380046e24b5c7063101a625413191102e644d04c817001c7be039000407c233001884027a005001015c26401a00e927c42e01807a003cafe026015827803a0040f0830711a047c33099b0c8035113803018a3f30e6801004c00308313e403f7dd057821400b78d1b180cc23e07d05701c355e89fbc100c00ac00206582b0084027008004c0100a4007803801e003bb082440300010ad0026e9200600c001000201e03782a80340061a001ec00803d07484a4016106006830c31200f2ce002000e004b970b8401c0be00500b06280b4b5e890405208100884a003f6b605f0660026001b4a00584aa04500380c804200300200780160470ad00080380af00207e82fe0040e20006c3c007128800f55e030000846abcc03912f803015606f029018016410902b800c0d75ca01580b809c0dc001072802600c016807c1260990a5000c00a03e01882680480130e456dc49800514c012442800800504c0002002013025c002090000d6b002158300387080040a2012804803e07a00413942501f1004801aaf401a00b016c05002204b000800403f028002c0260010048040008001116d49aa2407400b81581514f8019d290006002003101800d47b004810400c2c7005000c004002d5780401f405805586941be004003047401e01a022801001806c00400640421b7d578c3c0b13f70014f6c02816200080bc0060bb0284ed804c035015eabc01600304080080560010038038136029005808f55f38c025000402400600080680301d100e066809607e029801e70801f9bd01c405800102581700ae030012800401828d107000c00a004003017814c01f05e80182a4001000815c00a001000807c326002000800c00200100380c806600606a000c08401800600545bc021011800c5a936f9a7801808600c0b4009805b336009023c0072fc0040040006006002801806a01c005803815600e08e8a5406a03d04400165e60da01600d810608f96400340fc143002000403010706800400020020020010008001946003401e01f94088440760b2003825a256191049827016804902e8010060099001808823a00302f44240070ce00d800400601f0fa803415c0100b8004400c030018004407401704d002801000b06e009405e03a026003800805900201d413608f01200a401e099028802c05000d002006000c00200b002218f0bf000800402202b0038008004053006814823a0060040020004001026001616800b00f82141a0015016000800400a00c804801a002001805401a00800480dc002001002015a0a20130608454092039004003c09400600f801355e0d700400e804c00500080100720eb00a805c00600700680080a8014003807404808300081d800c00300c03d000902e
  | 9 => 0xb6325179cde01d484b004124c016156029871c01e01c01f009008800d0cb8a4c1f0683000834c7221a50c5007000400100504000040a923c00740e33c800102ec0a407f9e44d9800646e00081bc01a3fe010001041e1e2004800c3ce003058cd641860ae0f900340240019a0801413600400c006401600601280700532ee01100a679000f0e60768612002024803e516021010498001602a8f400d002e00700283f80800c90064674028008024813803001c0008370203171041800401800600f803435d145006001000400a09d01a010200184e830a79007f035062c0040be01484c003600302a88b402002c01884500093c8001047010616e000803c1140020018428528002072857c078024006003c0790971d6007679005b84800100480d900301b004e003039800806000c013802610a01800080940aa0089e401a80f6005035800449806007b00a001800a013c20400407402f80ec03604d001413c11605d008811009a0160ab00cc00b020005002000d01f0020004002004014000c00200100d01d4002012
  | 10 => 0x12062016031c2002
  | 11 => 0x2
  | _ => 0

def G28_actionRows : Array Nat := #[0x3ef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040, 0x2381f8a171b79d69759961349551138d40f28930bfbbebdf37db9e35cb1d33badc2fb29a2baa59279881441c60400c2]

def G28_initial : List Nat := [0x1e0f0783c1e0f0780001ff00003fe00, 0x2412090482412097fc0000ffffc0000, 0x6231188c4623118803fe000000001ff, 0x9048241209048247fffe00ff8000000, 0x188c46231188c4620000000007fc01ff, 0x24120904824120900000000ffffffe00, 0x30180c06030180c07ffffff000000000]

def G28_S (s j : Nat) : List Nat :=
  qParentState 11 63 6 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 1 G28_initial G28_actionRows G28_pb G28_records (11-s) j

def G28_idx : Nat → List Nat → Nat :=
  qIndex G28_N G28_buckets G28_flag G28_seedBits G28_seeds

def G28_moves : List (List Nat) := G28_actionRows.toList.map (qRowMap 63 6)

def G28_ori : List Nat → List Nat := orbitOrient qPrefer G28_moves

def G28_pool : List Nat := [20276122991265857, 60818386252271687, 60848111714630723, 50675391484984386, 60838225776805952, 50705136278896703, 40552187925955648, 10133118560306239, 40552197593826374, 50695240678444100, 30419127422224453, 60798624035050566, 30399307217699909, 50675430141787204, 10133147553430593, 30409212489172034, 30419098426999877, 40542292324454471, 40532416044008511, 60838177458420802, 60808490646570048, 10133147552382017]

def G28_Z (s : Nat) : Nat → Bool :=
  barOrbit 63 G28_S G28_N G28_idx G28_ori G28_pool s

theorem G28_moves_fix : ∀ js ∈ G28_moves, mapBits js (goal 63) = goal 63 := by
  decide +kernel

theorem G28_ori_run {s ws} (h : MonRun (goal 63) s ws) :
    MonRun (goal 63) s (G28_ori ws) :=
  orbitOrient_run h qPrefer G28_moves G28_moves_fix

example : qNorm [3, 1, 2, 1] = [1, 1, 2, 3] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_decoder_diagnostic : G28_S 8 0 = [0x1e0f0783c1e0f0780001ff00003fe00, 0x2412090482412097fc0000ffffc0000, 0x3e1f0f87c3e1f0f80001ff00003fe00, 0x6231188c4623118803fe000000001ff, 0x9048241209048247fffe00ff8000000, 0x188c46231188c4620000000007fc01ff, 0x24120904824120900000000ffffffe00, 0x30180c06030180c07ffffff000000000] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_benchmark_one : span (G28_Z 8) 1 0 = true := by decide +kernel

end PEqualNP.Outside.L_meta_984.Cert
