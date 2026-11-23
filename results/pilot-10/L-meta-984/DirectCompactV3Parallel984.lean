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

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

def lo (k : Nat) := 2 ^ k - 1
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

theorem next_one {y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : MonRun y s (a :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun y s ys → f ys = true) :
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

theorem next_two_sorted {y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun y s ys → f ys = true) :
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

theorem next_two {y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : MonRun y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, MonRun y s ys → f ys = true) :
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

theorem next_complete {y t ws} (h : MonRun y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, MonRun y s ys → f ys = true) →
      next (s + 2 - zs.length) zs f = true := by
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

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

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

def fastDiff (a b : Nat) : Nat := a ^^^ (a &&& b)

def row {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => Nat.bit (p x) (row xs p)

def pop : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => a.bodd.toNat + pop n a.div2

theorem pop_zero (n : Nat) : pop n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [pop] using ih

theorem row_lt {α : Type} (xs : List α) (p : α → Bool) :
    row xs p < 2 ^ xs.length := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih =>
    simp only [row, List.length_cons, pow_succ]
    cases h : p x <;> simp [Nat.bit] <;> omega

theorem pop_row {α : Type} (xs : List α) (p : α → Bool) (n : Nat)
    (hn : xs.length ≤ n) : pop n (row xs p) = (xs.map (fun x => (p x).toNat)).sum := by
  induction xs generalizing n with
  | nil => simp [row, pop_zero]
  | cons x xs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      simp only [row, pop, Nat.bodd_bit, Nat.div2_bit, List.map_cons, List.sum_cons]
      rw [ih n (by simpa using hn)]

theorem row_and {α : Type} (xs : List α) (p q : α → Bool) :
    row xs p &&& row xs q = row xs (fun x => p x && q x) := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih => simp only [row, Nat.land_bit, ih]

theorem row_or {α : Type} (xs : List α) (p q : α → Bool) :
    row xs p ||| row xs q = row xs (fun x => p x || q x) := by
  induction xs with
  | nil => simp [row]
  | cons x xs ih => simp only [row, Nat.lor_bit, ih]

theorem row_fastDiff {α : Type} (xs : List α) (p q : α → Bool) :
    fastDiff (row xs p) (row xs q) = row xs (fun x => p x && !q x) := by
  induction xs with
  | nil => simp [row, fastDiff]
  | cons x xs ih =>
    unfold fastDiff at ih ⊢
    simp only [row, Nat.land_bit, Nat.xor_bit, ih]
    congr 1
    cases p x <;> cases q x <;> rfl

theorem value6_additive : ∀ a b c d e f : Bool,
    value6 a b c d e f + ((a && (b || c)) && !(d || (e && f))).toNat =
      (b && !d).toNat + (c && !d).toNat + (a && !e).toNat + (a && !f).toNat := by
  decide +kernel

def swar (x : Nat) : Nat :=
  let x := x - ((x >>> 1) &&& 21845)
  let x := (x &&& 13107) + ((x >>> 2) &&& 13107)
  let x := (x + (x >>> 4)) &&& 3855
  ((x * 257) >>> 8) &&& 31

theorem swar_blocks : ∀ hi : Fin 16, ∀ lo : Fin 256,
    swar (256 * hi.val + lo.val) = pop 12 (256 * hi.val + lo.val) := by
  decide +kernel

theorem swar_correct (x : Fin 4096) : swar x.val = pop 12 x.val := by
  have h := swar_blocks ⟨x.val / 256, by omega⟩ ⟨x.val % 256, by omega⟩
  have he : 256 * (x.val / 256) + x.val % 256 = x.val := by omega
  simpa only [he] using h

theorem swar_row {α : Type} (xs : List α) (p : α → Bool) (hn : xs.length ≤ 12) :
    swar (row xs p) = (xs.map (fun x => (p x).toNat)).sum := by
  have h : row xs p < 4096 := lt_of_lt_of_le (row_lt xs p) (by
    change 2 ^ xs.length ≤ 2 ^ 12
    exact Nat.pow_le_pow_right (by omega) hn)
  exact (swar_correct ⟨row xs p,h⟩).trans (pop_row xs p 12 hn)

def sum6 (a b c d e f : Nat) : Nat :=
  swar (fastDiff b d) + swar (fastDiff c d) + swar (fastDiff a e) + swar (fastDiff a f) -
    swar (fastDiff (a &&& (b ||| c)) (d ||| (e &&& f)))

theorem sum6_row {α : Type} (xs : List α) (a b c d e f : α → Bool)
    (hn : xs.length ≤ 12) :
    sum6 (row xs a) (row xs b) (row xs c) (row xs d) (row xs e) (row xs f) =
      (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum := by
  have hadd :
      (xs.map (fun x => value6 (a x) (b x) (c x) (d x) (e x) (f x))).sum +
      (xs.map (fun x => ((a x && (b x || c x)) && !(d x || (e x && f x))).toNat)).sum =
      (xs.map (fun x => (b x && !d x).toNat)).sum +
      (xs.map (fun x => (c x && !d x).toNat)).sum +
      (xs.map (fun x => (a x && !e x).toNat)).sum +
      (xs.map (fun x => (a x && !f x).toNat)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have ih := ih (by simp only [List.length_cons] at hn; omega)
      have hv := value6_additive (a x) (b x) (c x) (d x) (e x) (f x)
      omega
  unfold sum6
  simp only [row_and, row_or, row_fastDiff, swar_row xs _ hn]
  omega

def fastEntry (y bw : Nat) (coords masks : List Nat) (code : Nat) : Bool :=
  let a := fld code bw 0
  let b := fld code bw 1
  let c := fld code bw 2
  let d := fld code bw 3
  let e := fld code bw 4
  let f := fld code bw 5
  if a < coords.length ∧ b < coords.length ∧ c < coords.length ∧
      d < coords.length ∧ e < coords.length ∧ f < coords.length then
    sum6 (masks.getD a 0) (masks.getD b 0) (masks.getD c 0)
      (masks.getD d 0) (masks.getD e 0) (masks.getD f 0) <
    eval6 (coords.getD a 0) (coords.getD b 0) (coords.getD c 0)
      (coords.getD d 0) (coords.getD e 0) (coords.getD f 0) y
  else false

theorem fastEntry_no {y s ws} (h : MonRun y s ws)
    (hl : ws.length = s + 1) (hsize : ws.length ≤ 12)
    (bw : Nat) (coords : List Nat) (code : Nat) :
    fastEntry y bw coords (coords.map fun j => row ws (fun w => w.testBit j)) code = false := by
  have get_row (i : Nat) (hi : i < coords.length) :
      (coords.map fun j => row ws (fun w => w.testBit j)).getD i 0 =
        row ws (fun w => w.testBit (coords.getD i 0)) := by
    simp [hi]
  unfold fastEntry
  dsimp only
  split
  · rename_i hh
    rcases hh with ⟨ha,hb,hc,hd,he,hf⟩
    rw [get_row _ ha, get_row _ hb, get_row _ hc, get_row _ hd, get_row _ he, get_row _ hf,
      sum6_row ws _ _ _ _ _ _ hsize]
    have hs := eval6_bound h hl (coords.getD (fld code bw 0) 0)
      (coords.getD (fld code bw 1) 0) (coords.getD (fld code bw 2) 0)
      (coords.getD (fld code bw 3) 0) (coords.getD (fld code bw 4) 0)
      (coords.getD (fld code bw 5) 0)
    exact decide_eq_false (Nat.not_lt_of_ge hs)
  · rfl

def fastScr (y s : Nat) (coords : List Nat) (bw : Nat) (pool : List Nat)
    (ws : List Nat) : Bool :=
  if ws.length = s + 1 ∧ ws.length ≤ 12 then
    let masks := coords.map fun j => row ws (fun w => w.testBit j)
    pool.any (fastEntry y bw coords masks)
  else false

theorem fastScr_no {y s ws} (coords : List Nat) (bw : Nat) (pool : List Nat)
    (h : MonRun y s ws) : fastScr y s coords bw pool ws = false := by
  unfold fastScr
  split
  · rename_i hh
    dsimp only
    apply List.any_eq_false.2
    intro code _
    rw [fastEntry_no h hh.1 hh.2 bw coords code]
    simp
  · rfl

def orbitActions (prefer : List Nat → List Nat → Bool)
    (actions : List (Nat → Nat)) (ws : List Nat) : List Nat :=
  match actions with
  | [] => ws
  | action :: rest =>
    let candidate := ws.map action
    let other := orbitActions prefer rest ws
    if prefer candidate other then candidate else other

theorem orbitActions_run {y s ws} (h : MonRun y s ws)
    (prefer : List Nat → List Nat → Bool) (actions : List (Nat → Nat))
    (preserved : ∀ action ∈ actions, ∀ {u zs}, MonRun y u zs → MonRun y u (zs.map action)) :
    MonRun y s (orbitActions prefer actions ws) := by
  induction actions with
  | nil => exact h
  | cons action rest ih =>
    have hhead := preserved action (by simp) h
    have htail := ih (fun p hp => preserved p (by simp [hp]))
    simp only [orbitActions]
    split <;> assumption

def barFastOrbit (y : Nat) (cover : List Nat → Bool) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat) (coords : List Nat) (bw : Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => cover zs && !(fastScr y s coords bw pool (ori zs)) && !(found S N idx s (ori zs)))

theorem barFastOrbit_sound {y cover S N idx ori coords bw pool} {s i : Nat} (hb : barFastOrbit y cover S N idx ori coords bw pool s i = true)
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (hr : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (h : MonRun y s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun y q (S q j) := by
  cases s with
  | zero => simp [barFastOrbit, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover zs && !(fastScr y s coords bw pool (ori zs)) && !(found S N idx s (ori zs))
    have hF (zs) (hz : MonRun y s zs) : F zs = true := by
      simp only [F, hcover hz, fastScr_no coords bw pool (hr hz), Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barFastOrbit_all {y cover S N idx ori coords bw pool} {cap : Nat}
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (hr : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barFastOrbit y cover S N idx ori coords bw pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := barFastOrbit_sound (hc s hs i hi) hcover hr hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barFastOrbit {y cover S N idx ori coords bw pool cap i xs}
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (preserved : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (checked : ∀ s ≤ cap, ∀ j < N s, barFastOrbit y cover S N idx ori coords bw pool s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun y s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact barFastOrbit_all hcover preserved checked cap (Nat.le_refl _) i hi
      (Run.perm hinit (extend_run hrun hs))


def swapBits (lo d w : Nat) : Nat :=
  let delta := (w ^^^ (w >>> d)) &&& lo
  w ^^^ delta ^^^ (delta <<< d)

theorem swapBits_bit (lo d i w : Nat) (h : lo &&& (lo <<< d) = 0) :
    (swapBits lo d w).testBit i =
      (if lo.testBit i then w.testBit (d+i)
       else if (lo <<< d).testBit i then w.testBit (i-d)
       else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [swapBits,Nat.testBit_xor,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem swapBits_hom (lo d : Nat) (h : lo &&& (lo <<< d) = 0) (a b : Nat) :
    swapBits lo d (a &&& b) = (swapBits lo d a &&& swapBits lo d b) ∧
    swapBits lo d (a ||| b) = (swapBits lo d a ||| swapBits lo d b) ∧
    swapBits lo d (a ^^^ b) = (swapBits lo d a ^^^ swapBits lo d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,swapBits_bit lo d i _ h] <;>
    split_ifs <;> simp

def validStage (lo d : Nat) : Bool := lo &&& (lo <<< d) == 0

def step (lo d w : Nat) : Nat := if lo = 0 then w else swapBits lo d w

theorem step_hom (lo d : Nat) (hv : validStage lo d = true) (a b : Nat) :
    step lo d (a &&& b) = (step lo d a &&& step lo d b) ∧
    step lo d (a ||| b) = (step lo d a ||| step lo d b) ∧
    step lo d (a ^^^ b) = (step lo d a ^^^ step lo d b) := by
  by_cases hz : lo = 0
  · simp [step,hz]
  · have h : lo &&& (lo <<< d) = 0 := by simpa [validStage] using hv
    simpa only [step,ite_eq_right hz] using swapBits_hom lo d h a b

def routeStages : List (Nat × Nat) → Nat → Nat
  | [], w => w
  | (lo,d) :: rest, w => routeStages rest (step lo d w)

def validStages (ps : List (Nat × Nat)) : Bool :=
  ps.all fun p => validStage p.1 p.2

theorem routeStages_hom (ps : List (Nat × Nat)) (hv : validStages ps = true)
    (a b : Nat) :
    routeStages ps (a &&& b) = (routeStages ps a &&& routeStages ps b) ∧
    routeStages ps (a ||| b) = (routeStages ps a ||| routeStages ps b) ∧
    routeStages ps (a ^^^ b) = (routeStages ps a ^^^ routeStages ps b) := by
  induction ps generalizing a b with
  | nil => simp [routeStages]
  | cons p ps ih =>
    rcases p with ⟨lo,d⟩
    simp only [validStages,List.all_cons,Bool.and_eq_true] at hv
    have hs := step_hom lo d hv.1 a b
    have ht := ih hv.2 (step lo d a) (step lo d b)
    simpa only [routeStages,hs.1,hs.2.1,hs.2.2] using ht

def compactGoal (negative positive : Nat) : Nat := (2^positive-1) <<< negative

def compactCov (negative n : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => (if w.testBit n then 0 else w >>> negative) ||| compactCov negative n ws

theorem compactCov_bit (negative n j : Nat) (ws : List Nat) :
    (compactCov negative n ws).testBit j = true ↔
      ∃ w ∈ ws, w.testBit n = false ∧ w.testBit (negative+j) = true := by
  induction ws with
  | nil => simp [compactCov]
  | cons w ws ih =>
    cases h : w.testBit n <;>
      simp [compactCov,h,Nat.testBit_or,Nat.testBit_shiftRight,ih,List.mem_cons,
        Bool.or_eq_true,exists_or,or_and_right]

theorem required_compactCov {negative positive s : Nat} {ws : List Nat}
    (h : MonRun (compactGoal negative positive) s ws) (n : Nat) (hn : n < negative) :
    compactCov negative n ws &&& (2^positive-1) = 2^positive-1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  by_cases hj : j < positive
  · have hy : ¬ (compactGoal negative positive).testBit (negative+j) ≤
        (compactGoal negative positive).testBit n := by
      simp [compactGoal,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hj,
        show ¬ negative ≤ n by omega]
    have hc : (compactCov negative n ws).testBit j = true := by
      apply (compactCov_bit negative n j ws).2
      by_contra! hh
      apply hy
      apply bits_le h
      intro w hw
      specialize hh w hw
      cases hx : w.testBit n <;> cases hy : w.testBit (negative+j) <;> simp_all
    simp [hc,Nat.testBit_two_pow_sub_one,hj]
  · simp [Nat.testBit_two_pow_sub_one,hj]

def compactCover (negative positive : Nat) (ws : List Nat) : Bool :=
  (List.range negative).all fun n =>
    compactCov negative n ws &&& (2^positive-1) == 2^positive-1

theorem compactCover_ok {negative positive s : Nat} {ws : List Nat}
    (h : MonRun (compactGoal negative positive) s ws) :
    compactCover negative positive ws = true := by
  apply List.all_eq_true.2
  intro n hn
  simp only [List.mem_range] at hn
  simp [required_compactCov h n hn]


open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem encoded_mono_exclusion_general {n : ℕ} (f : BFn n)
    (hnc : ∃ x x' : Fin n → Bool, f x ≠ f x') (cap : ℕ)
    (rows xs : List ℕ) (y : ℕ) (cover : List ℕ → Bool)
    (hcover : ∀ {s ws}, MonRun y s ws → cover ws = true)
    (hinputs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL f rows = y)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → cover zs = false)
    (hno : ∀ s ≤ cap, ¬ MonRun y s xs) :
    ¬ HasMonoSize n f cap := by
  rintro ⟨C,hmono,hs,hev⟩
  obtain ⟨s,hs,zs,hsub,hr⟩ := mono_encoded f hnc cap rows C hmono hev hs
  rw [hinputs] at hsub
  rw [hgoal] at hr
  by_cases he : zs = xs
  · subst zs
    exact hno s hs hr
  · have hc := hcover hr
    rw [hproper zs (List.mem_sublists.2 hsub) he] at hc
    contradiction

theorem encoded_compact_exclusion {n : ℕ} (f : BFn n)
    (hnc : ∃ x x' : Fin n → Bool, f x ≠ f x') (cap : ℕ)
    (rows xs : List ℕ) (negative positive : ℕ)
    (hinputs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a rows) = xs)
    (hgoal : encL f rows = compactGoal negative positive)
    (hproper : ∀ zs ∈ xs.sublists, zs ≠ xs → compactCover negative positive zs = false)
    (hno : ∀ s ≤ cap, ¬ MonRun (compactGoal negative positive) s xs) :
    ¬ HasMonoSize n f cap := by
  exact encoded_mono_exclusion_general f hnc cap rows xs
    (compactGoal negative positive) (compactCover negative positive)
    (fun h => compactCover_ok h) hinputs hgoal hproper hno

theorem routeStages_run {y s : Nat} {ws : List Nat} (h : MonRun y s ws)
    (ps : List (Nat × Nat)) (hv : validStages ps = true) (hy : routeStages ps y = y) :
    MonRun y s (ws.map (routeStages ps)) := by
  rw [← hy]
  exact Run.map (routeStages ps) (inv := fun a : Nat => a) (inv' := fun a : Nat => a)
    (fun _ => rfl) (fun a b => (routeStages_hom ps hv a b).1)
    (fun a b => (routeStages_hom ps hv a b).2.1) h


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



def qIndex (N buckets flag seedBits seeds : Nat → Nat) (s : Nat) (ws : List Nat) : Nat :=
  let h := hk ws
  let code := fld (seeds s) (seedBits s) (h % buckets s)
  if code ≥ flag s then code-flag s
  else ((h+code+317)^3 % 11400714819323198549) % N s

def qParentAction (cap stride ob pairs mb ab : Nat) (initial : List Nat)
    (act : Nat → Nat → Nat) (pb records : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => initial
  | t+1, j =>
    let s := cap-(t+1)
    let width := pb s+mb+ab
    let packed := fld (records s) width j
    let parent := packed &&& (2^(pb s)-1)
    let code := (packed >>> pb s) &&& (2^mb-1)
    let auto := packed >>> (pb s+mb)
    let ws := qParentAction cap stride ob pairs mb ab initial act pb records t parent
    let raw := qMove stride ob pairs code ws
    qNorm (if auto = 0 then raw else raw.map (act auto))

def qInputLookup (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: rest => if a = w then 0 else qInputLookup w rest + 1


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


def C28_initial : List Nat := [0x792, 0x94c, 0x18a1, 0x2468, 0x6205, 0x900e, 0xc070]

def C28_values : Nat := 0xffdfffbffdfdfd7efcf9fbfdfbeffb7ffb4ffafffaf5faaffaa5fa0ff8f1f79ff66ff60ff47ef478f46ef468f30ff28ff275f20ff20ef205f200f07ef070f00ef000ed7cec78eb7deb4dea75ea05e97ce870e7fae7f7e7f2e797e792e67de678e675e670e66de668e605e578e4f8e478e470e468e400e375e305e2f5e2f0e285e275e270e205e200e170e0f0e070e000dfffdffedff3dcf1daf1d9ffd9fdd9f1d97ed97cd94ed8ffd8fdd8f9d8f5d8f3d8f1d8f0d8afd8a1d87ed870d800d7fed7f2d79ed792d47ed470d27ed270d20ed17ed170d0fed0f0d080d07fd07ed070d06ed04ed02ed01ed00fd00ed001d000cffecff2cd7ccd70cc70cb7cca70c9fcc97cc970c94cc8f0c870c800c7f2c792c770c6f0c670c5f0c570c4f0c470c400c3f0c370c2f0c270c200c1f0c170c100c0f0c080c07cc078c074c072c071c060c040c020c010c000bfffbffebdefbd6ebcefbce9bc6ebc68b94eb8afb7feb79eb66eb56eb4eeb47eb46fb46eb468b40eb400b20eb06eb04eb02eb00fb00ead6cac68a7faa668a568a4e8a468a4009fff9fde9fbf9fb39f9e9d4e9caf9ca19b4e9aaf99ef99ed99ce99af996e995e994f994e994c990e98ef98e198bf98b198af98ad98a998a598a398a1988e984e9840982e980f980e97fe97de97be979f979e9792960e950e948e946e944e942e941e940e9400930e928e921e920f920e918e914e911e910e90ae909e9090908f908e907e906e9060905e904e903e902f902e901e900f900c900a900890069004900290008fde8f92896c895c894e894c882c8800879e879a87968792846284008142811c810080a28080806c8060804880408028802580208010800e800c800a8008800680048002800180007fff7fed7fb77eed7ea57ea17ce97bed7ba57b4d7aed7aad7aa77aa57a857a0578a17797766d760574687305728572056fdf6f976f6d6f4d6f4c6e6d6e056d6c6c686bcd6b4d6b056a856a05694c67fa679767926785676d6768670566ed66e86685666d6668660d66056600656864e86468641064006385630562856265624d624562256215620d6207620060005fb35aa159ed58e158b158a558a1579250245000494c4792420040604040402040003fff3ffb3fb33ee93ea13ded3de93da13d6c3cf93ced3ceb3ce93ce83ca13c683aa139ed38e938e138a938a538a137fa37923668356834e8346c346a3469346834003024300930002ffe2ffa2fde2f922f6c2f682e682dec2de82d6e2d6d2d6c2d682d4c2d002ce82c682c002b4c296c294d294c28492824280027fa27e82792276826e82668260025e82568250024e824802478246c246a24692420240020001fff1ffb1ff31fde1fbf1fbb1fb71fb31f921ea11ded1da11ce91ce11cb11ca91ca31ca11bed1ba11ab11aa51aa31aa119fd19ef19ed19e919e119cc19b119ad19a519a319a1196c194e194d194c190218f118ed18e918e518e118b318b118af18ad18ab18a918a718a518a318a0188118801848182018041801180017b2179e179a179617931792148814221400128412031200118c110010a010811080106c10681060104810401032102110201010100e100d100c100a1008100610041002100110000ffe0fdf0fde0fda0fd20fb20f9e0f960f930f920f4c0dcc0d6c0d5c0d4e0d4c0d200cc80c000bcc0b5c0b4e0b4d0b4c0b010a840a0009ec09dc09ce09cd09cc097c096d096c095e095c094e094d0948094409400930090c09080904090008d008a0088e0881088008680860084c084808440840082c082108200810080d080c0808080408020801080007de07da07ba079e079a07970796079307800580050c05020500040003800310030c0302030002820280020001e801e0019001850182018001780160014c014a014801440140012001120110010c01080106010401020101010000f000e000c800c000aa00a100a000920090008c008800870084008200810080006d006c0060005e004c004a004900480040002d002c002800240020001c0018001400120010000e000d000c000a000900080006000500040003000200010000

def C28_patterns : Nat := 0x2955959655995565549546515915615575559656565956655595465459156155665596565559516515855599565559155d556955995655591561557555a5565558555d55655555545549551554154955155445505525546551654555145445505519545951594555151451511541550511654565156455515445451454455055255456515645561554554154454514544550554154

def C28_N : Nat → Nat
  | 5 => 25
  | 6 => 341
  | 7 => 0x66c
  | 8 => 0xaaf
  | 9 => 968
  | 10 => 28
  | 11 => 1
  | _ => 0

def C28_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | _ => 0

def C28_patternBits : Nat → Nat
  | 8 => 7
  | 9 => 7
  | 10 => 7
  | _ => 0

def C28_slots : Nat → Nat
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | _ => 0

def C28_recordBits : Nat → Nat
  | 5 => 37
  | 6 => 47
  | 7 => 47
  | 8 => 37
  | 9 => 27
  | 10 => 17
  | 11 => 7
  | _ => 0

def C28_records : Nat → List Nat
  | 5 => [0x5a8fc96b3ab07e4300153d0e3800b257b0e005a94396ac262378a000c830792ce8cd5a0c00560fc96815f95d090016750e3aceac2100a00561439600000b347ba2c1af61ab0a39f9255854e6f05ac2a7304359d314661ace7e5740c0034ec1e2002d4b383c0ac1af68800af2b74c0050f1996]
  | 6 => [0xac205660054679926c400ac2a7a39180151a8c8ab2002cea25f91c005468a926d0008157b59918015851ce89300000ac2a74e00466e8ab45800002b15fd380000001391f00224714dea800000c1af19800b3a638cc380102ae8ad32002b0a9dc54c0040afd2e84c00002a83cd98000054691b5000005e115cc0048cca9823800002cea3078011240aad3200205745742600000cf1f9a800001153e79000c3a4071610000062520ca00547159e64c00002cea247800004e4fc9e001ad5d0de2a0056153c0a8c0061d3e497080168518cf8b002a361d254a000014833cac00ac9d15e03800901c44cf00000051cfce531c48fd3965000671835ef1000c3306bde4002b2a9df10e00000c1927d0000016724f28000056b592700000ac2626c0051319bf258008c97845630000054efcce002a38ac932a00000be22b98004f9252678001674c6fd0e001ff5c1208a000008a92fd000002b0715b00158af091a50022b5e1158c005469f126c400a9e7498870013a40aba1300224815f9a40051d2318268000028e5d198000048c609e00000aca1b66003e28a9e748000023251a980153c486f450026849099680000151afe9c00002a35f1380158c6491950025b454f3640000154126d4009a189491280158c648a96002b15e0934b53cc702bf428000019260f3000002f28ae60019f60d25cc00000cf28f8c009197b4553000002ce79e3002a79e8c11c000016a3a25c00ac5464559000d6ae86096002b17c5780e0048ccaa6a1c00b419f3f25001674f49a8700000490fce800564e2926d000ac578455300151af079a3002a38ad780e00546bc12694006b5835ed300159468fc96000007457a2e00001673f3380000262744f0000054649b5002337e5552c004c719bf25800ac2a79893000004c51236002a798a055400464a322b4800002d6b3878015851d31320000061d24ca0059d3d3f23800b3a7a304700153c0aba23002ce91a330e000008a927d000b29835ee3000cea8a756100000a8cfb66002f0a322b8800001835df300153c8c608e0017845493c800001231f87800ac2627e8b00153b8aba260000059898ca004b68a926d00091935304b000003a2ba1700000ac546660000153cc4b8000012d497a0015940abc23002ceaca330e003e2bc22b1800ac9d13cc9800cfb06a462000006b55e3c00000005167c00a9e8e98950015851d0893002b09d2622c0000151af09c005c1202672001593a2499500000b38c19c004e8bda2b1aa798e247e83001593e2e296002ce9ea051600000a322bc800002055e9980151a4a4cb40000000122ea000008a9f7c800a9e637e87000002cc7de3002ce989d11c004b6f8a2a5800002a3261a8000000157b7002d68cdf92c0059d3d4661c008ad784fa180167466aa87001d15d15a2c00565539269400a8df15e0380153cc5122600000a897b4e00314c1a4b9000ac2a799d28015854ee5a5002a7890c18c004ca92132d000a8df124ca80153cc5088eacaa7845250a004568a9275000b39d15d03d6508b8a9294002b0a9e110e000015e54eb800000009f4f8015954e608e002b0918c12c004569f1274400002a7332580153d11310e00000b3a721e00456a322b4800001835ef300000562f8970018749099c800001539f93800ac6325e038000056147330000054115e400001674c4b800002a35e5380107a484cd4002b0a39fa2600000c122f9800001a960f30000059c9ac7002ca67d48860000143ba278008c97851a18009f22a49f0002ca6717b860059d31bf23800002725d0b80151bfe9295002a74d4de8a0033ec528b8400b3ab28d0380158af0a3230020f625248a003f2e8ae85800ac2637e8b0000029a8af200000b3ab04e00001394665c00a8d7845530015938a79b20021181574260054f122b49800002247e6b0000050f391e000004a099e80000158af09c00000008c6b80153cc4fd0e001d15d15f26000013932a3c00ac6325189801584c4519600000b3ea81e0054f319823800a9e8930474c71240afd1200000ac4f366000016a4e45c00002b15f138008a9e649f0002a7814c1940000115a8d4c00001835eb300131c48fd16, 0x16b59d1987001784f915c40000158926d400ac2a79d038000031292650025b5e1154c0056133cc4d00000246330d80159466fc96002b2a9cf346003e28a9275000002a35199800bfa2e506400000ac6322e00564e2af09800aca0524d880167564fc8e0000060cf3e40000092133d000ac288988b0015854e5187002b2815f1260059551af61c00490e226780013d466fc96001ff49099a80051d311466800b3a338161800bc22a79e2002ce8ce108a00312921c58400001153cf900119c0afcd2002638cdfa2c00001674671c00002a325da80000000bbe700000aa1784e0059d19bf31800815c55d1900115a2a79d2001d15ed660e0000153ce43c00002337e6b00000560e8970019d52125c200001674fc3c0000000a997801474e8ba13002b0a9dfa0e00001593e05c00002a33e5980153a6a60c600000a9cc19c005a0cfa8b0c00a8d153cd900158af079a3000009c8c13c000015c2f09c00ac262844b0016748cfc8e002a37c4f32600312901339000002b148da8000040aba33000004ac99e800312921339000a45835ed3000005613917000009c9352e00000c1a8dc800002b6a9d380151af08da5002a7988a31c0048c9a9bc5400002ce9e878000056f5127002b0a3a742600546c1af69800a8d784f9180167560e8870000045498e800561231bc54000017f45730000054679b3]
  | 7 => [0x995785e0000071183e800ac5845e1380153cc6fd0f0018749520ca000013d3d67c00000e21afc800004fcf11f0018445cf3e400001685187c00002a78ae7800002e02f6d0000074574ae0000148ae8dc00002686257800004b6bc2f00000002597e0000102a1bcc00b42a35ed380131bf2e89e00000a8d875e0000000562fc00b3a7a744780000000bb770027a4d4c16c00564e2a4ad800001eb43eb800000003d7d000005e120ce00001192f13c00ac8f324f88000054eeecf002a798a465c00000fb2f93c00000005d7b800004a6f11f001ff5c05e9a000013a32b3c000017b457b0000022e49f50000089083ea0000129ba27c00002a35e1380000000677b00251434836a0000119c0bcc00001d165678000024076f300000890deea005a13d32a3c000000067b7800004bebc2f0000094d0d6e0000133310bc00002a3145b800002e8b7e7000005c06bda000013d30ebc00000008fbb8000022e7cf3000006553ed60048cca9463c00b3a33746380000546e89f002a7814a396005a15851ccc008ad9f5229800c3a404ce60000079d12af59422d6a4a5400001093cf98000054f3a4f00000a8dff3e00000fc2f13c005ed5545730013d3a2609e0022b4f925a600000710efe400002b0921b80115a909f53000005690fec0000092133d00000251435b800002484cf6001484f915e400000004f4fc00001b65d1b800002f04cee000000007bfa002e0900bd9400001e7306f00132bfe4c9e002b16117b4e00000003ab7c006498445f300097a4a4cf4002246b4deaa0000154cc4f8000022b436b800002e08967000007fc4bba00001674233c000028c744f800005631957000005bc99dc000012e2f8bc00aca637c4b8000040a9073001e75c10f8e00000002f9bc00388990c7c000005464cbe00000ac8fbe6000013d3ce7c00000006777800003a2c3cf0000026479f800000920e9d4005c0e217b4800004ac9ab7001e243483aa00000e2adfb800001ff266f0000056479f3000005bce2d60000000225dc00002a78467800000009cf70012438874e20024a8b933d000002a7a8978000030692f60000067548d60000151b24dc00002515e178000032aafeb002b26b4f36600000bc22b98000027a5bd780000000e9df0000071595dc004b68b9e6cc000010d3cf9800003c49cd7002a7919c55c0056548be25c005ed3e4579000005a13f1f002b28d20566000015851ccc00002b148da8000054692b700000002a27e00000b81e3ac000022b43eb80129ae087a70000094d0f6e00000b7a6b9c000025b715f000004c7123700000918a53e000000044fdc000018748338000000060fe00000995875e0056508b8a7800b3a919e878000000153ef002745d15aac005a15498338000000044fb800003e2b7cf002b2a9e055600000ba133d80000000443b80151af6b32700000a40cc7600561234225c00002247aeb80132ae02f2d0000089074ea00000f126b5c00002657acf8000027273f5000006b4ccb600001122bfcc00001952677000ffb0e904700000a8d086e00000f8a1b5c00002537c4f8000054f51af0000061d0dce0059cfcba3380000000955f8000032c9ce70000096de73e00000cfb07bc000027444ab8013d3f2e89e0011728051e80054ee2947380000000971f80000000c077000005bd0fce0000063885e400aca34715b000d6ab4519e000007fc34ba0000066183e8009a20f1d0e800f8a2e79d3000007fd20ae0040aba2aacc000013e44b98000032c7eeb0000098dd73e0000000506fc000010d20fa800b821e2f6500000745742e00000004a6fc000017a59f38000048cc3af0000060d74ec00000f89837800ac632610b80107a483a5500000a46723e00000002fbdc00959eb448b800ff9323a5c002a367d4866005613148cd8000023044ab8000048ccaaf0000083c75ba000013f272dc00001e261e780000001676f0000061d3ed600001603a27c00001d15d1b800004a6f39f002a7890a38e00001123ff5c00001ff0f6e8000054f2aaf00000ac5784e004c6fd3607800001701bf6800004caff9f00000995356e003fe901335800a46745d0b8000026a76f3, 0x1873885ed2000013a2df3c000010f3cf980000456a45700000959746e0044908c0b4c000010f3b79800004e8b84f00000a9cf3d60027c92941c400001745c338000021e71730025379d0f2e00000004e47c009e9954d538000032a86e700000a9c74da0000000582fc00001c55c3700151a4a8ab600000a8cf3e6005652d9e6cc00002a779e780151a908ab600000918aa3e00000e2a25d8006249917b60000040aba3700224715556c000012c228dc0000204486b80000000e2fe00000995d13e00000bc2e99c000020f0c6e80153cc71227001ad5d15a6c000012a220dc00002535c1780000496ba37002b27c4f3a60027c928bdc400001ee44eb80160308bde6000008acc1bc00000f11837800b42a99e8780000550a4370000099a043e00000002ffbc00b3a7a28c78000049512370000096d875e00000ff9837800a9e6384478000054660be00000945705e00001674679c00001d11bed8000044879f3002b2892056600001232e8dc00a9e467e87800002e88af6000004405eea00000798e9e400a9e245553800004e912570000000178de00001463fe7c000015a437b00000494ba370000045512ec000008a9e7c800002ce9ea780000000b8ef00000ac546e60000158c64dc0000000487b800003d686d7000007c520ae005a0caa6b1c00000990dfe00000338ba7300000958747a000013d4e87c00001ff0eee800001321dfc00000a9e24ce003fec386334006298748328000021e30f500000ac2627c0000000275dc00001d1482b800004b690370000000170de00000003a97c0062920267a000004a6b7af000009596f5e00000caae99c00a8d25179a800005508937000007dd0fae00456bda2b58000013e437980000560fd57002b09d2462e00456a41fb4c0000246305f00000546b82f00268490746a00000004fcfc00002b0a39b8000000119f7000005e10bce000012b3a27c000017a5939800003fececf002056b57466000015912fd4000027a4d5b8000000135bf00000a8d4f6f6855331bf43800002b251b98000021e2f750000098dd33e0051d231466c00521153f7900000594ba5700000a9d74ce00000878e9d400001871d36800002408af6002b249499e800000f3a1b5c0000000437b800002f0b367000009710d6e0000129c48dc00744ea17ac80000448e2f6b42b2aa6340e000008aa23d800a4574569b000003d6ba570000081499f4003fe4c86370000017f3e75800004d04cbe0000000120ee00000ba2bfcc000019543f38015ed4f31ae0000079d789e00000710e9e400001d15c27800004a2f39f002d0654c19c00001671473c00002b0a45b80153cc4d6ae0026561c995c004c71238ad80083ce21d2c80115a4a8ad6001fa6b5742e0000107b133c00001f161e7800004a8b8af0000074474ba0000168550bc00002a33cdb800005463a3d0000043c69ea0054f124231c000027e744f800000009577001ff480eaaa00000b7a259c0000183523b0000024045f5000009d099bc000000056bbc000010f3e79800004c4d6be00000ac5256e0054efd38b38000022478ab800004670875000005c45eda00000bc0e9b40000265305f0015851d233300000a9cc79e00000b81c5ac000000097df8000049ce2be002636117acc0000102a1fcc00001953077001079c418d900000944747a000008aa11d800001701d7680000001293f002637e9cb3c00561233f45c00b3a057465800004babfaf000000015efc004f4d6b2a3c0000246298f80000324b3670000033099f4000013d224dc00acaa93cd98000022a87f6000007c50fae00000cf199ac00a25ad304f001594b6f897002b298c936a005a13d1827800002a35edb800f3ae0714b00000919705e004e8ba2bf4ed07e99f3f6500167564e88f0000062475da0000000313bc0096d1724da80153cc702ab0025b5e1174e005a09a9bd540098dfa744f0000059d02eb0000065520cf594c71a3f4580000253481b8000056491f5000008157466005a0cf98338000028c515b800000008b770000043c83ea0000132ae8dc0000000959f800003fe86d7002b261d25ca00000001f9f800001ff332d800004f4ec1f, 0x789789e000015854e9c0000263744f800003cecacf000004d474ea00561231465c009d2465d0b8000022647f500000a9dc5dc0054692a36d400001ff43eb8000027c9af30019f59948c600000ba2b5d800001241e7a8000028c92f30021171431b8000012da1adc000015f43f9800002f08be70000096c747a003feb806334000027a481b800003ce905700000891d5ae00448e294758000013538b98000021e3f750000048093ea00000f52215c00002587bcf80000523313e00000440e2e6002909298fc4007fd0f17aa800d6b2a60ce002d0ac2a94e000013d3aa7c00002b15e338000041e925700000ac97cce0054f1239794000022b482b8013d3a2ca8f002b2aa4936a000004c8eff000001741d3a800004caf39f002467e8fd3c0022e79927c400b427a4d4b8000054649f50000049518ea00000ada6bd4007c51724ea80000560d6b70021181431b2005a0cf98f2c00002046227800004a2e89f00000891cbea000012b2e0bc00a457457d9800003a28957000000013bee00001539833c00001891d3680153a6a51c7002a798dfa1c000005b0e9e400000e21e7c8000021e31f50000061d12ce00000f12255c00002b0989b00128ade86a7000004550dec00001340e8f4000012020fa800004a69ab70000000223ee00466e8aaa5c000026543db800003e2b84f00000a8e246e004c702bf47800002915e9b800003fe9ad7000007fc74ba00001601e7cc00a46337e6b00131c48fd3600000a9e4c5e00000d918378009e9ad304f000004acbd37000004951aea00448e5b8bd00094de75c07800004484cf60000026475f8000013d3fe7c00001f844ab800002e89f73000009e9785f594c6c22f6980000000746f800001c437f90000041c74ea001c44c8e9e000002a72da780153cc6fd4e000003b474f200565539463c00001701876800f3ae02f4d00262918a33c000004c885f0000025b265f000003c4905700000002a87e0030e9006394000018743f3800003b060de00000a9ce2d6003ce710bd640000246435b80159466e8970000067d45e60000132a1adc00001f6436b800003feba570017026431d800000dbae8dc00a9e057175001341c43a39000006bcc1bc0048d088627400002531e5e800004cc4cbe00000931d13e00000e2b0fb8000011020fa80000580bc6700000b39f99e000008b8a9d8000000065f78000059d1a4f00000002907e000009c9fbcc00001ff5e27800004f7399f000008ae24ae00000eaa6b5c0043ce217b8800002483df50018949074ca002f08b92794000015f307d000003d69ad7002b2a78f36600422d6ae85c00a9e636117000003c4b7cf000005d167ce000004c897f00000112267b000003ce87d7002b2a9d484e0056553c489c00000009c9f800005647cf3002a35ed156c00001021996c0000256265f000002de89e7002a3494a06a000000028fdc00001c54d7b000b81322f6c000008c946e600000000e9f40079d0f38a9800001321a7c0017038874d200546a427ccc000000066778000000152bf002464d4a32e0000128a40dc00000004b7f0000044876f3000007fd709e0000071133e800002565a178011235a60d600000975f73e00001412f55c000025b744f8000021e37f5000004f90fe6000000050afc00480ea267a000002f084e70019c5ed66c600000afa25cc00002b148db800c22f68ae600000945746e004caff8627400001ff1dee800003a2e2de001ff38831b200001652915c00ac2a76b5380000456c3cf002b2a9e344e00000c22f59c00945e2434b800c3a9092e5002915ed664e002484c8e9d000001663cf98000000165bf000009a0797a0000158a8cdc00001953b75800d6a6a60d6000005d093ea0000076933e800001a959b38015935a609e00000b4144d60000000500fc00001e74d6b80000448f3d70000096d356e00000b81dbac00001835efb000001c431f9000005c063da00000bd2b5d8000022456bb00132a404cb60000096d0f6e0000148ce87c000016f3b75800001f22f79000004807cea00000f5a415c0000000aab7800004ac60be00000a9e4e5e00001681837800ac9d15ecb800004e89057, 0xa3a627c00594bdacd1c00002b0925b8015bd6553a700000a3a743e0000153c8ebc0000000517b8015938abdb6001d15d1552e0033eb324b9c000022b422b800c22f08be60000038869f200000bc21b9c00002537acf800c4a487ee500000961705e00000ba183d8000010f267b0015935abc270027a8cdd12e000012b3c47c00001d36567800004c719b7002b2a45784e00000ba1e7cc000025b425b80151b08bda7002b0a9e464e00000e8af13c00001153cf9800003e24cde000008cdf9ec00001674f73c000000096df80102b8a51da00000a9df19e000012321edc000015a1d3e000005469ab700000b3ab25e00000a29f9d800002a3788f800004f487b70000096d6f5e00001539513c00a9e248171800003129265000007fd6f9e000015851dcc00002b18c8b8000059d19d7002b2a44936a00000c4a499c00002a73b75800004f43a3d00000995126e000013d448dc000000073ff000001823a7c0000062099dc0000132b2abc0000000961f800001e23a790000043c93ea00000b7a419c0000000b0f7800002be3a79002b2745482e00000d698378000017422fa80000594cfcf0000053d15ec00000b7983b800000004d3b800003de8a57002d0a9e625c0000153cb6bc00000990c7e00000448b7e70000096de23e0000153abfac00002a7296780119308a3530020f624749a0000129b8af8000019538b58000000113770000044874ea000006c133e800002b2744f8000000128bf67d8452117c400000e2a1fd800002b15edb800003f2e8de00000994747a0000128982f80000267989f0000054e906700000744c1bc00000901bdd400002a774e7800002e8717300000a9e635e00000ec26b5c00002b0929b8000054f316e002b296c936a00000004a0fc00002a33cd980092a404cf400000001d2be00000de2e8dc000020544b980153cc6518f000009450f6e00467083a35400a8d483f59800002e2716b00000918c1bc003ce710e964000000047fb800004a6c3af00000ac9f8ae000008b9e7cc000028c67578000048c9ab70000051915e600000838ebd4008ad48456b00129a1e2f350000062983dc00000bfa1f9c000027a1bdd8000000112f7000007ad709e0000115ae13c00a9e117167000b821e71630000000188de00000f5a255c0054948457900148b3eba3300000999216e00000b3127d400001eb1d2e800002e034ed00000a9e625c00000f5adf3c0000112307b00000001463f00000a8d6f5e00001020637400000d81d3c8000028c91f5000005c114ce000013d3ae7c00002054d79800000003bfd000007c50bae00000f121f5c009e9953057000002e060ee000007fd879e0033ea422bc8007fce217ac80000564f8d7001845ed17cc00001674213c00002a35a578013d26a6f350026543c5e6a000012fa24dc00acaa75ed380153cc6fd2e0000051917e6000015424adc000015f4839800002cea4670018926474d80000119bf55c00002a324da8011240ae2f2002a38ad7b2e00000f8a6b5c00001835ef7000004a8f51f0000094d746e0000153ca2bc0000224657380153c8c518f000000026e7e0000153cf4bc00892057ea980129bce2f1d0000048483eb53cc6fd35a38000011524fa800003c486d70000096d126e00000f8af13c00480991d3a000001f23a79002b27e5d13c0000112117d4000022b6567801299c43a39001243f499e800000c922bd800001783077000002f08ae700000a9cc1dc00000921c5cc00001173ef9800003a4e2de00000919206e00000f8b2b3c0094ce2179c8000059d3d2f0000096d955e00001584c4dc000018a517a800000003cfd000004d515ec005a12326a5c00000005bf780153b5a60ce000007456f9e00001593a67c000024e744f800003d64cde0000079d74ae00000f3b0f3c0098e2472da800000012bbf00000ac97fce0054f123f51c0000256449b800004a29ab7000008ad789e00000003ad7c00002a7746780000448ecd7000004505eea004ca4c862f00000146457b000002f6b3e7000005e172ce00000004a8fc00001ad3f2f000004b6ba3700000a9caa9e0033ec524194000022b266f000003c44cde, 0x172ee000013d3a67c000015a483b00000001523f002d68cdd12e00466fcba3580000000aadf800c228c8af2000008cdf9ac00000c3a6b9c000027a8acfc68fd2907ed2002535c05e5a00001593f2f8000017838b580000546ba3700000000cdf600001673f53c00acaa77e87800004f4e89f000007bd709e0000000319dc00002566557801123f47ed6001fa658fdd400000b8a219c00002a778a7800c39323a6c00000b4233ae00000cfb07b800a9dad5d138000022a8776002a798dc55c0000076983e800002745e2780153cf4518f000006245eda00000a322bc800000990f7e000004f4ba370000067125e6005a09a98358000025661d780000466ead70000061cf3d600000c49c5ac00002d04e6b800004f4f89f000008d146e60059d31ba23c00001b0306f000c22f08ae60000094c997c000000026bdc00acaa7495380131c48c23600000b0093ea004ac891dacc00002b15e1b8000027c4cfa0018743c5eca000008b931d40060d7b59b300159468e897000002647bf80000153bd73c00002741d2e8000048c541f00000995206e004ca4c8e8f00000124267a800003ceb84f0000057c99f400565489e6cc0000144497980151af69f33000007fd12ae0035aba1465c000014846fa8016856153a7000003887bf20000153ccabc000027a65578000056153e7000009590d6e0056554be25c0061d203ab2800002e86f75000009d135ae000013a4e47c000024c891b8000022a3a7c00263891fa2c000011928d4c0000230522b800004a68937000005e112ce0059d233a23c000022424fa80168da13d0f0000089170ce00564f892754000017043f3800002408df500000448e2e60000153a259c00002ce8ce780153c2218cd000007c512ae005469f24acc00000f3267d000711322f78000007fcfcbc004c6d698278000013522fa8013a35aba1700000ac5785e000000032dbc0000000657780000306bde700000490a0ea0000089107d400ac9f16b4b8000054e86e7001e743c5eaa00001230e8f40000251449b8000022476f3000000010fee0000129af0bc00002a35e178000030e60ee00000002667e004c6fd35a780000123457b000002f087e700000ac9f7ae00000c42439c00002b28cab8000054e60ce000009750f6e0000153933b800000004f3f0000054e534f0000000229ee00001231467c00001153cfb000003528af6000003c45ef2000012b21edc000022461f3800003e2ba5700000a8d0a6e003e2bc22f1c0000135267b000c228c8bf2002532643178002de8690794000016f4373800002e079eb000003885ef200000f5af13c0096df145cb80132bfec38f000007450dae0000153a6b9c0000246891b80168553312e002b260d7bcc00000e5a6bd4000013546fa80000000ebdf00000b02a75e00000ff885740000000157f00000000fcfe00000a9cc1bc00000b8133b8000016f1d368000021679f3000005211eea0000153bb33c0000246304f80000000007f0000071574ec0000151be27c00001701d36800004563a5d000009956f5e00000f10e974000000060b7800001c43af9000004f920e60000159127d400a460a5d19800751822f78000009456f5e00000ba1dbcc0000000333d800000008677000003ccc1f400000f39337800001ad5d1b801592f049e500000945c57c00000830e9d400002536557800002f88be7001ad5ed664e0000153c94bc000011524fb0015398251ce002517896f1e00000da18378000013e1d3c8009a9bc60f4000009a20f3e00000caa6b9c00002b0a9db80159448e2b600000789959e00448fd38b5800001d2306f000001d02f79002cea46338e00564f8af11c000016644b3800004e8c3cf00000a8c936e0000158a8ccc00a9e749187800000003b7d000009f9965e000012b448dc0052125267a000003fe1bdd000006b55c3e0000128bd67c000011422fa800004489f73000008ad74ae00000901e7cc0000224457b000002b489760000000075fa000000030fbc000010d267b000004d09237000007c474ba00000e2af1b80000232522b800003d660de0000062499dc000009f183e800514ea31f88000033a7e6e, 0x7b96f9e000007e0e9f000002b18d1bda148cf6cf8b002b26b4936a0000115a6b5c00b3a917e670000028a6f75000008cdd1ae00000004dafc00ac5845199800004a31237000009d174ae00000cea8b9c005d15f56b900131c48fd1700224845c5ac0000131baa7c000016744b38000021a63f3002b29020566000012d982f80083d243f6a80000512e89f00000a9d0fce003fec393338000015f4d798015940a92b300000a9cde9e00000caa259c00002a78175800002de63eb00000a8d126e004c6fd364780000120267b0000054f232f0000081574e600564e8a4a5c0000253305f000005644c750000043c6bea00001584c5d800002a379cf800000012d3f0000096e246e00573592f09c00002a3521b80000306bde6000009196f5e00000e28e9f000001e25c278000021a3a7500000918c13c0000000561dc00002b0aa5b80129bfe189d0000074535ae00000fcba578000017b5cf380000001343f000005c135ce000011240bcc000027228cf80000546bc370000065474da0000000223dc00aca055ed9800004f4b82f00000002617e00001393a27c000027443eb800005a09ad700000891d1ae000009f215cc000022446fa8000059d232f00000658c1dc00000b3a4b9c00480990c7a000005a0a2d700000480c1ec000004c8e9f0000027a8cdb801684f4cf8f0000045493e80000123132f8000022438b9800fd2727ef2000005a112ce00001674c6bc00715ad5d1b000002482f7500000a8d206f31c48fd35a5800002ce8ce38000054f24af0000081474f200001542f6dc00001eb61e7800c49c43a69000000017aee00000004cafc00acaa784478000000151bf00000ac9c57c00001673f338000013e49798000028c91f30000052115ec00000be21b9c00001d21e6e80131c48fd560018726431d80000128b2abc000023251ab800003a23cdd001242645ee800000710c3e40000000893b8000054e51cf0000061ce2d600456a42375400002b2989f0016848c609e002cea467b1e004f4750bce4004951517ba0000056123370027a745352e0000151a1adc007fd48496a80000546caafb423467d4886004d0c48e8b4006b57457d980168561313600000a8dc57c00000a3999cc00480e217b880131c4902b300000994997c000009a907d4000010d35b9800004084cde0000048074ea00000f132d3c00002ce9e87800000012ebf521253f4a0e000000dd2e8dc000027a748f8000056553af0013e49515e40000153cacbc000015f43798016833e9ac70010f26431e800001584e95c00001ea5c6780000448fd570000061cd8d6004a6879c4cd9f6294849708000030e3aed0000095dee3e0000066063e400acaa95e1380151c56929700000a8d78ce0032a9a9bd9400001e25d2b8000026a79f3000004d493ea0000128b0ebc000017f45f380132b0e18ad00000919d13e00000901c5cc008920555598000030eba67000009e8c17c000012b240dc00a45d15d0b8000054f242f002a7891c5cc0000115a255c0043c9917ba000005a0665b000006b57a6e00000b821b9c000010d3b798000056291f5001954d4c1cc0000159388dc0094d7038958000054e9f6b001ff43c31aa00352c222f9800001953cf5800004caf11f0000089178ce000000055bbc000000043bb800004cb12370000000174ee000012badebc00002b0a9d7800001981bf90000096d705e00001584c6dc000011725fa8000048c5b1f00000944997c000009a983d80096df15e078000048c6f1f00000ac9c36e00000e8a1f5c00a8e2b520b800bc22e79e300000a8d0f6e00000ad26bd800490fd283a000002de6b6b002653885e720054f02ba32c000013537ba800003eebfcf00000890c1ec000013d132f800002a77ea7801592f079e300000448f3e6000013a18378000010f1efa800002fe2f6d0000044cede600001592f19c00a8e11495a8000016c4cfa0010f38874e200000bc2239c00a25f9744f0000041e3a5d0000061cedd6000013d3f2f800000fc333d00000564fb57000005e115ec000013d21adc00891ad569b000ffa4018d500000434c1ec000012ba26dc00001143c79800004ace2be, 0x2b298cf36600001232f0bc000024631cf8000021a45f500000891f1ae0000092a2bd80083c991d2e0000059ce8cf0000079c77ba00000e893378000027e305f000002403df5002a791a244e0000158a90dc000010f307b000000008a770026826474780035acaa6b1c00002658acf800004d3313e00000ac9d23e000013a21b5c00002d03f2f000003fea2d70000043c7dea00000f38e974000017b59b38000054f10cf00000994797a00001079337800995ff480b800d6a6a6f550000061c99dc0000000331dc0099587481380115af69f53000008cdf9ae000013d38af800b42a94d63800004a63a3d002b2715486c00000e2a41d800002a794d78000028889730000074874ba0000128bc47c00002a77fe780000546d4b7000007fd959e0056553b8ab8000000063b78000040a60fa000004550cec0000123224dc008ce057469800f393218dc000005e135ce0056531af09c00918c128cf001682f68ae600000b39d39e0000000249dc000027a788f80153c8d088f0000083c77ba0000132b8af8000014848fa800003d6cacf00000a30fc7c000008aa15d800002655c178000054f313e00000a9e625e003d6891db4c0000139307b0015940aa433002638cdd12e00546a4236d400001c5437b000c530890650000048499ec0000000133f80000170483380000001323f002b296d784e00000ba107d400000fc0c7e00153bf47ece0018445c93e800000004bcfc0000000981f80000456b7cf0000043c8bea00000869c5cc00001e2332d800003fe18dd00000a8deb3e00001673f3b800001e75be7800004acbc2f00000448fbe6003c4b7a1b1c00002657c4f80131bf4da1e002056b4c1b4000016b3a27c008920574698000022a28f6]
  | 8 => [0x990c55000003ce4c00520c74e00000fd2d00195084d00108868a8000004b5a004c6bc1a0000013168012d8101c00000595a004f40087002681d15000af8069c00002a73a00126042a002a35203800ffb0e300000099a0003c418913f4e21d12800ad00ab0009d174420056528870000053d6801288621d48494a03e00422b79a001a51795000901fa8400845c558005652607000a00c5500154d4e6800001cb5a003144cac0012f2656000e2b3eb0006297834001323a2a0025b17838005007aa80074428220030e009a0000043d133e7e940980096c210e00001328b000001b56b5aca94630004340842004a687a1002a7828d468fd1fa40008447454002247ea10017012cd2908b9fa790f388313c002de019a000f328138014cd221c000019d340000100ad002246110d6508a4a7de743c311a00000142d000001956800710169c00744a02200000bc1a94d0f0c418000018cb4000022c5a00422ca9a001785e0d000cfad06800002765a003e2059167d8a184c00140ca61c00480ea42000fa18aa000e202138000023cb400000b55a004d2eb91000003fd68004c832b00056808580000087a4001700c4d000c38106800002995a0021e51a10026552038000026b10005d16642001e225a70028d9943800901328400000df5a0000079ad000007896800003b8b4006b57034000013a1300170178c001595521c00a627a0e0022e87a1891ad28c6800004eeb4000021d5a001bc042a001c50156000d50eaa8009a0fd0e002de929a000003216d64a41fa7800ac91242000004d2d000008416800e8a904400002195a002f6bc1a001701795000890428400b425b0e004ac50070022b0148800003b0b400000b45a003d475110020a4d508011238a85243f4743e00000372d0027b43d0800e8ba2459f610fd2e004f6ba21001954d4d0000054e70007e8c158000003f2d00000a056800004e6b4007fca022004a6cf87002a7714c800cfad4680049508420027c0427002e167cd4c6d694604005d15a420054ed69a0011502d60015384268007c4a322004f4010700291305600153bf468000011b5a00414b79ab429167cbcc6e2b5a1800000455a00448502100135305059d48ba23000a45d72348cc6fd060025b0143801288bc1c00ac9f11a00448c521001eb3b48800878bca800448054200001442d0011b085500034862a80000135440054ee29a00174005080154c981c00788a0220000045ad0022b02088012a0841c006110f420012602aa0027a00c3800001c0b4004480b42004f7122100000731680000158b4005c0343400000212d001815c0d00151a908400001eb291240ad69e0020a43d080132c681c0082987340021a419f001ad5d018000017cb400b39d118cfa90929e0000077d6800ca98268007880b220052319a10026372c3800c22d86800001f35a0010601aa002d04d5080000126b4000002a5a001c43a250017828cd4e8ba2aa34005ed7034004d2c39a0025120c380000094b400b22910e00314b79a002a728c60011a30e6800000825a000001dad002a95a0d000bc1fa6800a9e2442000006b2db42919ec08013d0421c00b40a322004f72b070010f17908007e8aeb0009e99534004caff87002b26bc38008301684004183142004ac7e87, 0x1c5281600060832b0007896f3400420e891002919d0080131b601ed067cfd2e00000b0ad994ea1782800f3ae069ff61c5e18005a15187001d23f48800891d4840061c9934003ce1091000007416800000b0b40098e24420000023ad000f30153800003e2b40094d0f06000c218aa0017845cb00128bc41c00001f95a00000a72d000008b5680000184b400001c65a00000d8ad000001d16800001c6b4004350d42004a705070025379c38013d4d21c004945f540021e18a1000002a9680060806b000a1a5b0e00448e5a10027b43508012dc141c0096c0b0e000000fad001740850b5aba2aa0e24845ad1a0030890210016f3f4d00000204b4005f14834004f6e891002a9994380128ade08004480242004e8af91002248290800005c8b400000405a004683a2a0025128c3800ba2e88400000a05a0032a519a0019f5c0d0015bc488400b42a935683f4cf8c001fa6c08800928c6a800a46530e004a6b802002df98c38000024084000011442002483a21000007548d22750bc9400000ee5a005a4b79a0019f4810801299d41c00aa50f42003ce1a11002b22656000ba2908400994995800001328a9945e0c42800f89d444009e8ea0e0056686a1000004616800768bc9c00000c16ac3a4a2f18000007796800001c4a1873a85e3000564902100125185500172cc61c00654083400000752d0022b3f48800caa6a580054c7b540056531870000035d68008780a84009ed703400000e2ad0012000d080000006b400000996b08ae01898002ba449080108b3a68000003c5b3d3a25181001ad5d10801318b2b0000018786901d42f1f002699303bc48684234007c431220035a5291002a7280d000b89d468003b4a04e003a22f11002635bcd000cab08680067cc158002e0011a00000266300153c8c6800001e75a002de501a002a995838015fd641c0061c9958000009f2d0000083968013d1bc1c006540234004b72d8700000885680000172b69162984340022445a100000ac438015180a1c00b95d122003089aa1002510643800e880a4400944030e0043ee2ac000006a96800002e0752545c5e3e00468a421000fd1e55001328621c005e00b3400000692d002246f108008304284007e87754002400421000001a9680000482b40067d943400000982d0021144908008694684005ed2042002404cac001cb015500041810a8000011a5a00448aaa10018a610d00000422b400001c25a003f44cac0022b52068006c0bc9c00000a55a00000732d000004e168015954e0a117e8371e0000107ad0000003d68000000ab4009e9d10e0022e86a100000449e800000d8b4008900142002f6b79a0025328c3d64bdacc5800000905a005a057110016f02cd0008680a84005c008340054e019a002694d50800f880644006292042004ca3487520fd2813000003f8b400000375a005223a2ab40c128c80012b1da1d254805e3e002908521001fa3f56000004f428007e5d1580021e01210022467d0801424ac1c0067cc15a000009ace002a7814d001340e81c00a9c19340032a019a001cb71560009f0629c003a86954003a200910000085d6801574a61c00b7dd322005a12987001120650cc71235a0c004f9253c004b60107001ea10888015ccb61c000027a16004e85191, 0x2a728cd00092982b0000008c5a00140212a0000002d68009094084000007954000004dad000004056800c381668006545e34000012e87002bda9cd00108876a80083c7454000002ead000a31d150000046684007fc21220054f3182000001c968000024ab6b298d7b060000035ad002114d509fa50062a4009a574420000015ad0015f28d380108896a800829204200000972d001c57156001288541eb2aa57b06005232707000ea1bd5000900048400002a80e004cafd07b42a98d065a0cfa905c00aca650e00000e2b5001ff0c47800f39464400946110e001fa60ac0000028d680131cb61ed0aa611195935a92830000085968013d2901c00a457406000012a07002a7520d3fe750bc3c007fd4822000000ead000ea1855000002408800ac8f33c005a0cf9a0025b0043800798169d252645e5200564e8910000074d680148bf2b000001445a003e21091002a70c4d000eb9d44400891fa1a0048c75070010f388f0015921084004800543594c71a03000f300d3801680e8a80061c613400546bda1002538d038013d26a0c007441922002e82f21aca918d018013d0321c000028e5a00000b79a002919ec3801464221c0067d74420030e519a002110f5500060816b120178313e002e8ab2100000245680131ae068009e80b0e002be0427002560043801078e83c00002248928ade10820025652038013a00a44007e5d121684f4518100000a5d68012b1d41c006b50d420029089210027a3f438010886ea800884cc4e0024a35aa002b29050800c52e06800891fa4200000a5ad0025101438013280a1c00002ce34000009023000fd2816000c39326400aca7a0e0029092a1000008316cd07e8e81400aca560e0031431aa00000455800000426b4005ecc15800001539b0018a61cd0008b9e678000012088000015189000008a96800d694c44008d1d1220000123090025349438000051eb40075548220046912210016f43508013d32a08003887454004480121002a30043800000f0b40094dad0e00546500700117449080000412b400b40c7220021e05a100256958380148b2a68009ea630e003349aa100000a7d6801364ac1c00000a65b3d35a5181000004910800004488400b459534000012888001352810800fd30e6a116b4311e00000542d0000026168004c804b0003cc314e0000053ad5c0a00c4c00128bf41c00001959a0033e89a1000740655000ad146b000000fa5a000011ead002b292c3800001d2b6b27e9ad02000009aa4001ad43d080172c68840000195864c8e82f2900000225680000448880094c030e001d44cac002d03048bfe4c8bc4000b4178340032a60ac001fa4e5080159182b000000625a004143a2a0019f31d380000348b4007fca322003c40411002050c538011a2e068006917034002e087a1aca246b41800003fab6b2845ad02002b602aa002b29090c68a41fa7800aa570340038a042c00187480d0012b4141eb298dfa0c002f6b316002dda9cd000000f6b400000955a0033e3a2a0011724cf80163a408400000215a000007ead002650843801121fa8400944fd0e000010d2d0019f30d680148ce81c009ed6f34003f49021001845b8d0014f4b61c00545124200001122300263265632a9a946580055512420027c05a7, 0x13502108000021f1000000ba5a002f68aa00015f0153801328161de75c031180038ad7ac001cb02d50013a0bc4400959eb0e000007c2d0012f4810800003ae458717831300054f539a002b26a50800c48e86000a8c020e002dea41a000001a568008b8f6a80098e4f0e0021e01a10017402108000040cb4004809940004c726873f4ea1792801634c61c0096ca00e0000105ad001cb0c55001538bc68009fe510e00310379a0015b0c55001562de6800001e15a002de189a0015548108011235a84003040258001d42f2a000003cd45a0fd1fa40005550f42003242f2a0000068968000021f3800000fb5a00000afad0010f43d08009e982b00079c3322005a158210000052568015940a1c00002205a000e8042a0005e0dd5000768169c00a46650e0033ec21a002561783800500e8a9893f47430005229021002c06b438008781084003f477540054f2302000ed0853800004feb4007e5d1220044805a1001481d1500131c0a1e11828311e000013a2d002b25e0d00112290867a4d4a30600553288700000a8c5000c22f66800000f75a003143a2a001875ecd000f580644001d00154002b401ac001743a9080000284b400890314200000ca9d0000015d6800769169c00000775a000000e2d001fa6d08800c52d6680043c3d4200000dcad0023442d0800a721e840049469540038a51ac00135305080060802b00028c9958004f6c39a002210dd55a154c8c0800a9d8a34004f40287000000c16800c50cca800001eb5a0033e4cac000008d1680108ae06800a30c70e000014aad0000047568009f00a9c00a8c080e00001712d000a00ed535a6094640004b1124308bf4188f000002716800fd2f06800ac8933e000bc18aa0029f7e96000710069c000025f0e0000038ad00000471680119ba234009d0fd22005a1539a000991bd600159126840089021436856123030025b5203800c50d2a800945250e0035ac39a00289305600151c561c00995250e004ca51870026930560011a2408400002a3100031487a1000006b168000051ab400001b45a005532987001f10148800c922e8400b416a3400001222d002d04d4880092a1a84005ed0d4200000c39a000000456800ffb0e68008ac2122000012b07002530c43800a421284000000a5a004a31a0779c5e0c478008300e85ff4805e1a001e649a70025b7c438013d15c1c00acaa30e00422d811001ff02c88000021b380079c37220058f3287002a94350800b781068000013942001fa3aaa0027b4d5080108ba246d08d19f18004acd687002ac944380131a24840096dad0e002908d9f00234715600000052b40079cea22005524cac0000006d6d5331bf41800000e85a003a0e2ac0000010d6801289401c00ac9782c0012618aa002636c83801318f2a80094de7020030e189a0021126560015932a68008299534005523a2a480991790000c38be680094c3b0e000e818aa0011228108015848c84007fc9958003d61891000fd2656000a7a2e84002649958004ca9003a45f974480011586244005e00534004403baa001cb1795000e8b5a4400714fd580024a9021000001e56800005bab5845ed172a0021a7ea198d9f628d0000012cb400449124200498d687002915d10800001c4b400000c95a00422ba21, 0x2bea8c3800004f8b400001be5a9a9bc519f002658443800f5a243499178315200322bc1a0000034d68011238a800096d9f0e00552ba21001ff4810cca928bc14000027428003ce878d0027a844380000240f400001335a000000a2d000003056801230421c00844c1580000060ac000008d9680154c9c1c0061c1934004b708870025b064380148ba444005ed12420032a531ab424628c08006080ab000001485a00336ca9a001fa5d1080000114b400448314200564f8a1001350650800768069c0067d0f420000086bd0000050d68000010cb4008922442f1106108f0029a94c3800f394044007e9703400000622d0000050568002f0a2a800001789a0000089440014c4d508016b4f41c00304a55800580a421002636d03800003fcb61143c313e0000042ad7e9ad3f48000002bab40067d12420038a012c001a85e0d000bc22e8400002a7340035a6091acaa98d01800005c2b400002375a0032ac51a001041d1500153d226800b4d7034004ca4c87002ae5c0d2e0710625c0059925420021e1da10024600c380119ba2866998dfa0c0044892a1000001516800e88d244005ed7442004ca0087000005c0d001028429c000017f34c530e2f180022445d080000408b400b42510ec224a8ba0000005316800005ceb4009a47454004a2cf87002681d028014dba244005bd6f34004e04cac002a702cd0010538ab000001747a0040a51a7001e22d888013d982b00098e4b0e004ca33070000067d680000012b40000195340035a6391000002dd6801592f08400b40c158002909aa1002a798c38000030e6c00891ba42004c6e887002510a03800002cab400814084e00000d0ad002519443801298041c005ed0b42004f42f0743483084f800ff8624400ac97034005467507002b253d08000037ab4005d0a3420044804210017000cd000e2816b00020c425400000ba23002116bc8800cfb0e68005ed154200565539a00000a75680000064b4001d0055553bf4d68c000003f16000ba2ae84003b4a34e00422d9110018143d080000370b400001325a00564c9215c10f0c4b00000160b4000007474004ac4587000003296800004ca1c00001bf5a000003e2d001ad28c8800c7a4084007fc9922004c686a1001fa6c888012d9e61eb2a454806002e80121aca6352018000028cb4005c0e234005a0ba210000094c500092a2a8400b416e340054e041a0000054568000031068fd2647452002e88ba167d8a520b800bda2e84000023f5a0054e011a001743f508000015eb400001e728000009bad002918910800a422e84008d0c15800522b81a001e702c8800c39d468000021e5b59468d6830014845508000038ac000002570e004480ca1000002ad68009f1409c00000cb5a00414b81a0029b98c3801518161c00000a15a000011c2d00000305f800a421a84000010d48004ad1a070011b0215000ff9d444004345e420000060d098dfa6b40800002a6b6d0aa663040026a92a1001a5610d000458bca800000755a00001742d000007216800830108400ac987340022a02ac0006f0c550012b00a1c00810a02200000e6ad6114845d000115a36440098d2042000012d8b001780c4d0000006cb4000029e5a0030ec39a000009a038000018318009180b0f685533d8c, 0x12543d0800608bcb0009945e0e00000e893000006716800e2a4ab00000112460000086a1001254490800004eab400a8d9f0f48ae8aa8300000a69680000198b40078823220010618aa000009f838007e8b8b000001045a0000000470000031d6800ba06286b267d2542002e0109a002d07448800004b624009a5124200308b81a00195304ccc6fd35e40007fc082200422bc1a000ea1ad5000d6af06800995ff020021e0ca10027a3056000638429c0094c380f053f47e900000030d6d64928bc7c00ac96f3400000132d0026994c3ca70886214004f8034e004b8a4070027a8d03800f58164400002055000000382d000741795001681bc4400001355a0000060b0002919c43801329321800b416c3400000bc43001891d150007e18eb0008d10842005471a0700256084380000144b4005210f42000012c07002967448801109fab0009ea0a0e002aa9aa1001d828c880148ca21c007ac08220047289210011b02d50006f0bca800a7c7954005654f87002df7448800878a285ad554a30200001192d001e75208801230bc1c0022c0b5400414bc1a002a798cd0000027eb400788ea2200000ff94002a974c88012b2240c004f85e4e000006c2d00178020d000fd35e44000007d5a00182042c000fd2d93800b81fa68009450d06000013f2d001ff3f4880000002b4007c40822000003a4f001ff00c8d64e2b5a18008ac0b22003685191000005d2200080982b2d0844311e003149aa10015b1795001328321c00002395a002908da10027a7e83801288421c00b6ea30e00572bc1a000009e56800f380a4400ac93542000009024aca346f0180134ae06800a9c0534004ac05870027b4810800cfad2680098d74420042218aa0012000508009aa2e86535c03104005a052910010d20d0800000c0b400788a322001c43a2779ca00c4780159468840094c190e00000762d000004e56800d6a248400001da5a004a62f0700195280d4a2f1042040061d48340059d489a001ff31c8800c3a4058002647458001da18a7a9e466b4100000524b5845ed1740003d6a411001060890800ca8326a246b55506004d2b79a00195004d000aa932b000000ed50000005ead00000265600132b5a1d9f521173c0013201ac002a75ecd00000476b4000015f50002f6b321000001716800f121a84007c4932200314b41a6117b45cb001020de46d08459f1800000e4adb42a928c60000009ab400000335b48cf6e88100000199680000088b4000025b0e000011e2d0008b0215000004f42400002a30e00001012d995ff1780800ba2be7a1179c311e0030e2f1a0017043cb32a6094664004545e580035a60ac001a3654d54f1235a58006286b5400000904e0005e0f550014fba246d067ca31800000b81c001fa4d50800798109c0045c9342001262f2a0000074c8800003a2440094c210e004c72987acaa94941800af8bc9c003885e5400448e59f002114810800e2806b000a8d2506b790610987fd8a1787800e89d44400000495a0024a37aa000002496da09a94634005550d420026a51a100234654d000c52288400aa56934002fe289a002050153800bdad4680026421580013202ac00000551680000000c400a8c190e004f49aa1000007ac980000018b4007ac5e22004b67e87, 0x2911bd3800e2832b000a8c030e001d463a70011b17950008b8a284004e4b642c52402f1f000005916800d695444000007456002e892a10026943d0800928bca800aa56f3400000b84d0022b5208800003a2518a6105e30004f72d870025302c3d64d694604009ee510e004ac8921001ff480680137cb61c0098dfa5800310501a000004850800418dea800a8c310e00000722d0018700cd0000005cb400788fd2200468bc1a0025b3a8380134a1a8400000dc5a00422c39a0020502d3800869d484009ee650e00001298b002915e0d0011a2de680098d95340021a0121001c5085600148ba244000016f36005652d8700265481080000100b4005e0a034003d689210027b2656000c22f0680095c490e002f0799a000008e96801329401c00944080e00308b79a00195290d00087940840067d6c3529bce18810013502d0800bc0066800000195a003a2cf91001173cd0801602f68400a9ca32308bf47e90001e25bc6000ad140b0000002d5a0035a541100187280d000a78bca8004f8214e0000115ad00178064d000001b4b4009d021220024a8aa0002631d15000ca9fa6800001f65a00552ca9a815ad28c70011a2e884009460a0e001ac10a7000de01552e8afaaa79484945e3e00000fdad0025b24c380000360b4004180342002408ba100117429080151a361c009e9ad0e0054692a1002510083800000a4b40083c7422003fe18aa002246c9080049816a800829d1220000117ad0000044d0cc6c53086400a7e690e000012887002b26b43800e28bcb2918cdd11a004565191002b2714380148a1a8400001a35a004d3328700000891200000514b400448ed3c00422da11001d14948800d6a6a840098c5758000001c2d002460203800003dcb40098e510e710e818a50029f7488800000b6b400000005cc5290929f000001a1680148d141c00001035a003c42f11002653a8380000000b400000845b299c41884002a35201800002f074005e001340058b539a002a7494d000bf21a84009c2650e005a1328700187084d000ca8626800b5d48435933ec51a001841d15000002df34000025610004221c2a0025b00c380105132b000494745568468a40d000001bd68013dc961c000028c5a0024a8ba1001893f4d0000019eb4009a59534003fe2f110025b5e010003a016a80098e4e0e0055351879450d08418009a9d4840094d703400000022d0025301438011236e8611521253e0013218a9000de00d50012b3f41c009022442004c72b07001aa628d0007680a9c005bc8334001da0427002c898c3800d68e8a800aa587340030ec21a000005016800750c6aab2494a03e0022e2bac49505178f800002df0c0072c2154004226627000005156800004a61c00001365b53cc6d682002a93056000d32e88400b41351a004ad088767cfd1d12800f110644005c17034000001a2da466974408016aae884000027a0e002b410ac0010d005080000132c0005bcea34002cca4210011742108011544884006b4c1200056492a1000007d56800f381044007e90f42003543a2a0026500c380000034b624715ad400024005a100000b816800ba2be84009d0ea220041486a1002636b43800001e0b4009d1482200564e881002b23cd0c1e7e8e83c00918a00e00000682d, 0x17b5a0d0016b26a840062912420026a02a1944830842800000ceb6b267d483c00000082d00129435080153c4858fd2807452000009abd000001916b0e900bc58006b49958000003daa002b091818012b0041c00264085800000a52d0012019908011fa4084006557b34001bc60ac0000094458013f16c1c00001b35a000013288001891d0d00000164b4005bc0134005133d070000023d6801593a21c00b416f34005a0b81a00195494d000798429c004d4ae42005224cac000630c55000f580a4400001d222004e80191001254250800c50dea8006c0a322003a6cf91001101090800b784268005d15a40004567511002a94d50800001deb5ff4945e1e00001172d0012006508012dc681c00000745531b08bd990016f434b26a60946800054c74540038a00ac0011508560011a21e8400002155a002be18a78d19f520f0000040eb611388314a002de249a000007b56800002f86800000b15a005473487002b27143000004f4200094d480e005a05b11002b26c0380153c486800388a04ea424a359f000009444800002e88400828c1580024a85a1002d02988800cfb146ab28d1fa1a000003fad00193265600000220840094ce20e002e0501a0023843d08009a982b0009604b0e002e805a1000005d11000f894044008921142000bc1daa001fa654d000005181c00002225a002b418ac001a9610d00154cc61c004d42142004c69aa1002465203800881d484004340b42004ac51870016f178d0008683284007e8cc4e0000086a2001484810da153c8c0800001635a004a2a407001f13f488000032c6800001749c001fa3a2a001e20848800ad810a800520c1580034a30aa000000e56800000e6b40000145420021e10a1002d02a888008a806b000002935a0016c2f27002201d15000003a2b400b410d42000014a2d00170494d00129c221c00001879a002f69aa10011200d0800f59164400a46690e0014a3a2aa46637440800a40f6a800000ed5a000003baa000004f940000021a8c008ac5e220032c5b1a00251788080128ade68005e09334005a0b59a000f328d39d4518bc94008297442004ba2887002114350b0e4c8bc6400b42244200001123d0006b0c550000002ab4000010d88004f6e2ac002111095000004b62000aa5d1220056f539a001f15e06000878bc7dfa3f4b64c0059951870018a1855000ff93240009a5d122ff8bc188f002a79ecd000b7844680065535436848ccf820000030168008300a8400001f958005469287000fd1696000003d4b62472dad3e0030886a1000006ad6800ad016b00098d7a42e2b5a519000000a6d6cc6fd35a1800304a058002402f21002a77e860011a2248400480a04200001328900000569800151d461c00ac948420000006ad00000795680153b966800654de34002f63a2a002a76c0d0003a004a8000010f7a004cac39a001121790ccac38bc0800b118734002aa3a2a3a8991794801615461c000008d5a0022a18ac000002d968009004284006a51742004d32887002d0654d000004564c00330a04e0000087a3001e743d0b3ec50bc6000000535a00000e8cc002a38283da13db3e30000017a42000012988002692656000fd0acb00067d6d34004a2058700083085554ed69463000001e85b123f4d68d, 0x265f80000152b400001e226000fc18aa001f13cc8800bc0bc6800a458734004cb32870029d9583801518421c009e9d1035935abd830024629038000013ab40098c5a5932a402f030026992c3d4f08b5a3000002a786ba2b4aaa0002914490800000c2b400001f25a00000fa2d002a36b43800e88104400b4187340024a4cac0000070568006f016a800000b35a005a12b07002694810800ba2b084008cdd1220024018a1000000bd6801605221c004185e42000012989000001d55001682408400001e05a005643a2a0019b3056000e88044400aca24420000070ad002a398c38005006ea800001c75a0018251ac001d128c8800a9a4a86d067ca619298bc18850027b654d0007100a9cfd3a8744a003f486a1002a94490ae02f0626000844fc58000004fad002650203b3ec51fa5c00000275a002b610aa00000715600045806a8005e02134004482f21000a026560009a86284001d02154000007cad00205179380050096a800a9e052e0000062ad00000105680049842a8003cc5e4e0030860ac000de0c55000002de70005c148353d182518600170014d0000022488000005a5a005229aa1000008927001331401c00000075a004684cac002b214508012735a1c005bc0234000001ead0000036568008680684000007468005672887000001d1f0008684284001783454004f49a8700000ac10a1e2f0627c0094cfd0e005b4cf9a000e217938008a810b000001295a000014e2d000003c56800003eeb400000815a004a60087002516b4380153c22680052099580038a18ac000009ed6800c22d668009e8310e00001159400192610d00123146040061059580028a63a1a9e056b4b801230621c004183442000006627000991d14a907e8e89400aee630e000001fad49517280f8000052cb400001005a0032a751a0000020d6800cf8eaa800388a34e0033eca9a0022889108000027ab4005c00b34000f82f2a001353790800cfaf06800001d75a00001052d0018a435080000062b400944ea0e005655387000002fd68013dca61c00890ea4200536eb91002637448800af9409c00b39d134001fa2cac0025b4943800fb2904400a456f351a3f4a40d002b443d08000009eb400001e65a00326c39a0018a1795000002c0b4008917b420021a1521000006bd68013f3f41c00001e35a005531221002695e0d0000015cb4007c57834004689aa1002a7844600041816a8007e9cb22004d52887000009096801159404400000065a00590a4210000058968000035cb40031c315400224042100000b8d680000376b4007154858003645191001740150800f38bc44009ee7a0e002e8aaa1000002b56800ff8c24400aea560e00522e991000008156800cfa6a86656285e0a00000f1140009300d5000c3a4a6800304315800308ba210022400d08000013cb4008843154004f6892100117265600154cb61c009e99f0e00000d6ad001211bd080148cc61ed0acaa9040041e7e91000c1305600134cb61c00001ce5a0030e011a0000005d68000024cb40072c0854003f4cb1a0017e5bcd000003f0b4007e96f3400000b843002b294c380000530b400002a316001d460ac002dc61cd000bfa4a6800a8ca30e0054ecf9a00000654e00000048b400a8d3e0e002e07117, 0x37968000021e840000112420022e3a2a000000d5680148cf41c005ec995800000102d000008496800003fe4c009a6630e004aecf870018a5a8d0013d3a2440098cc15800000894e0011312508013a06244004f8a34e000000b2d000008c168013a010440062d6f3400564bda10000090d680000312680000171340026a6f1f0008b0855000b783268000025114004d31221000008cd6800901468400ac90a4200000bc1b002a38443800ba032840063d8734001402b2c001352a1080000044b400996630e002f4aca1000008d568011ba1a840079d701800000792d001c53a960013d4f41c00000dd5a003083aaa00000a856800002b8b40098e240600552902100000755680151af60c0044801420054ec21ab42a97e8600129ca61c002643158004f46086002510043800c222484007e9c558005a04cac00178520d000000acb40043c0142f12de108c000000f968008d80aa8004d4fd4200000272d0029f1d15000bc24a68005c00134000006a2d001eb3a88800001ecb400000f55a000e83a2a0000077568000043eb4005ed0942005232d870026582838010f132b0003a87454002f687a10027a0203800a78d6a8002640b58000bc212a98d9f610c80090240840061099580026a9aa1001d102c8ade8684258004d40142004ac0c87000003956d6548ba204004343142000010c2d00205744880153cd268000002c5a002908aa00005e12d50011240a7800000885a000006dad0011228d0800f386244008ac0322003c40291002b494c3800c22da6800b66b24200523260700000021680102b8ab000a464f0e0021e7ea1001d100c88012b0621c0061c053400000f4ad001fa1d150003a006a80096ca30e0000011ad000002ed6800879d484005c44234000005c2db42b28d0680000024b4004d40342003f4e8910000025d68004180aa800001ec5a00001202d001e700c8800b780a6800001ca5a00001042d001ad48108000026a8c00814034e004b6fd07002a39ec380000540b4000016f3a0027a9aa1001eb0848801212908400b40a8220046886a1000007bd6800c39fa6800002145a0021a5021002a73f4d000003feb400000a45a004ca0107001ff18c8800a426084006bca322005474887001855d108016fd641c0067d0d420033eb79a0019502cd000005b6b4006554834004c6c39a001783a8d3144c8bca4009e8c10efd1fa3a29002c049508013d1401c00000465a002b42f2caca914941800c6ae884002640158004b6bc1a001eb28088000032a6c003f47b54004a65007002b2a44380000132b4004d402420054e751a001742810801050eea80028c6f4e000002f2d00170064d00129bf41c008900542001825b2c0024628c8800f39fa4400b5e910e001c410a7000009e168008a0968400b40c12000001002d00269958380172baa44e2178314a002483a1f001d10c4880153c6868007894822002f0011a000009585800f121a34005c0ea34004ca7e87000007656800f59fa4400a464d0e0000073ad388a00c528015921284004d45e420000106ad000009703801673a244000011248004f45187001ad654d00148b8ab000448ed435954ed682002919583800b8146690f280313e005462f0700000791680154cf41c009d0a022000012d8a, 0x105224840072c03540054e009a000002396800ad816a800b4112420000093ad0026343d0800d69bc4653280310a00552bc1a0025667c38016821e840022c0554004e8ba0d002248150801298101c00280345548cf4e881000008716800c52e88400001a05a004f63a2a001ad5bcd4d2cfb086800001873a0030e9021002661bc3800ff80a440030421580035a5b11000006d56800879c48400a8cfd0e005893287000005c0d800c22d268002005e54000004a2d0015f085380132b3e1c009e9250e000005e2d00000958480128a1a84004806b420048c5187001d10848800fd2248400002e95a0011618aa002d19e838000004ab66367d843400000d2ad00000b7968000038b1800001f128001c42f250022b4f888012a1d41c00975250e0056526870021143d0b5a9a94634009958704004ac9287001e7388880000074b400628c1580032aca9a00000345680131ba20400002660e00476a4210025b0c43800002e89000a8dfa0e000012b0a0000080d69fa751409800000875a001c418a70000061ce00108a8a8400001d124000008cadaca6349418000054f34007c54822000007f2d002460143800418bca80057c0b4e0056486a10013e4950800710849c0046c31540024034a1001241d150000026a840056c0354000003a45001243f50800e89fa44007880322002e8ada10019a654d0013daf06800001235a003de2591000006c9680115a908400000f45a00000a92d0016f28cd5a0ca9463000000d55a0032a029a9e99528c14ca4c8bc1800000025a0000122ad0014842d08012b0101c00000fc5a002e02f1a002b243d0800ce98e6800a447954a424a7e9e002d09e83800005ccb40022c4b54003e22f11000004c56800000a2b400378215553b8ad699002dfb40d001121468400001d25a0038ad6ac0011b00d5564c22f65800b02a90e0052287a10025600c3d6548af60eb2aa548060000148ad002052813801593aa44000005f5a004e805910009917960016c2f06800001db5af39c4188e98dfa6b40000000c6b400ac97442000000036001eb28c8d64d6a900c005d003420048c7e87002637488800003e24c00001c05a005ca92a1000005e0e000001d6b400002461400522ea91]
  | 9 => [0x5bc215a00006c6342b96800552d0014f5afd140b60a01968004cad828215a000051d840216c14012d90a115b681d4b4ea3a96aaa042d28c315a50062a80045d8cc61dad0023462b784268590216cd2332d0005e800c010b6116b56d654887001305b68422b4050056800e8914d4a342cf804b4003f68d64d6870010f4308a4ab4fd1796bf4a42d520035a00476b69b3a9686205ad0000b6200140b5ad0216b3e502d178315ac21d4b400a9cd2f6042d494665a0014cb40076969322f2d000315ad68bcb54852169fa3a2d0019f62004f6b93528d6d65318700031a27500ab4000029a0a01ad98c085acf946b4a301568000136520215a75016b413015680051ad828a35b1a468b59f1856800d7ad060055a00016b4830856800502e8d0315a24016b6d0aa4d35a012dac94842cf806b58a17951fa18ad4945e5a00354b52545d0b5a05ad388315a00010b8006956cd2fd2da44085a2d016b6a928d6ca618879a4085b48842b67b28d6d2234ad064055a0f006b4002828c6802ad000ed5a00006ba3402d6b1410ad000a380828bcb40000ddbf41bada9dad34000bcba630856d2218ad414085b5480ab4001996d14fd2d0008b5aa4140b40098d886202ad002696200308d8ea0856ad205ad6284b5b101fab40000255a0522d28c085aaa940b400001c4c6d687002698e00002b5ad6b5686210ad002de5a0029144030056c22012d002636cfd1fab29167d6b3e10adac9fa5b1a1fab4480856800d6b1b42345a82842b44800d6d22502d000695aaa946b60a7e968001c2d5ec035a004c71c500216b08112d120085a00106b40001688007eae5eca35a92842b59f0156c15052d002915aa40bcb58a0156800012d000a35cd6842b60a18d6a900cad000006f1a0bcb6e5a456d222f2d304a35800000b8190096b8ad6adb7a0a5a1080ab587179680051b1000035ad6802b4009d16c680e2d494055a00414c4009943a4a92ad8d2115a28006b4fd3f56d53052d414315ac2068b4001696800f02db66345a0000ab6346b56a4a7ead8459f5aff8bcb6d028d6b4a752d906345b54b60b400905680005c0001ad6c7e810b4003056810012d554035a00414b400009735a18ad084085b38940b51701568000cad6117b34fd032b54828d6cd27ead002115d681fab5fa6b568002f2d000009308bf4b6340096800c2319ecfd5a00314da690856a2e152d, 0x9ec085ac50beb4ea2a96d233487a460a5b59140b5aa3f56800e2acac8fd5a929d4b5ad2816800112d000215ac21fab6632816b3e7ead654a35ad680ab6118296800712d02c055b489d4b40000e39d4012dac80b5a004b61e7b8456800042d008025aa7a4ab6917448cd201ad001fa633d95cb4004957000d82d000ea5c00396b400aa58c1405ad00187355924a86b28296940012d002d08e51802b699845694037ad788215b3dcf6b400845680007ad944210f08940b4003696ae0189ab40a05a003ceb5ad495680010b1280215acf810b400761680005b69ec035b0c1d4b4fd28161d401ad628315a41842a8000a169fa02ad0022442005a0c4000657000aab1944215af3862b5fa0856da02f2d828ea5a0026a86b2085680148b6a46345aaa842b6345216aaa02ad9e8a35b48c22b69102d6cd308ad520fd5b02b5ab5484950c1418ad000036d3d940b6969ed6b0810ad002185aaa862b400629880060ac038035aa9a90b6a900d6cd2502d002215a2f0bcb4005d10a2e2f2d828085a82140b400001e0005031002918e0f00ab42102d6a4a28ad002345b3d80ab59f1796c22752d844c75b68522b4002a16d220cad8d19f5a00062c4e20c53c220cad001256368010b4000f56a908ba100291630502ab6d008568a018ad424035a000b8b450085680075360000b76001a4b4a01796da0fd2d67c495a00014b4009edb1a805ad45c315b1a1d4b5aa67d6a1a10a19edfa5a82816b66901569a002adaca115a000c2b400845b0ac012d3a8315a00536b691a456d22e8adb419f34c20bcb6919ec3d3e7eadaa5485a75032b67b02d6a9005ad628ea5b5900ab6999ed6800f5ad0019f6c00096b40054d680063ad1400b5a00290b611521683205ad5eca05b10bf4b45e009680089216a5485a10802b6da7e968320cad000009134862b57b0c56aaa05ad0007c5a0035b1c310216d522f2d000d05a86842b5533f569fa05ad844085a6d032b6415216c31052d001b25aa4062b4001d154f6a42d020015a8b842b4001f96a402f2d0027b63549d4b5050156c2202ad0019f5c004f41ed028c8b28502d000217734870b4008463c2210ad98dfa593dc68b4009a5b290012d002055b48bf4b4007ea38000aad000218e9824ab6e18456cd2da2d084195a3e004b6b25216c851a2d6b4195b34c14b5d80096801452d00003a308946b67b6b568007eb1, 0x9ec195ac2140b40300d680002ae000b65afd1fab400b856a90042db41485b3d9d4b4009ed680067ad828235b088bcb4fd00d6d52fd2d828fd5a51832b5ad3a96c83052d000d65a00414d800aa6383200ad3a8085b3d81eb4a02816cf62f2dac8ea5a000111dfa3a96b1451ad0000ba334a90b40001588002f470000880000010a0a5216b0851ad001ff5a002f06987178d0009021a44fd5a00032d800179b3f402ad178215a000331e3400d681601ad67d8a342800ab57b02d6daf1a2d6b5485a05810b40035168000039000fd6c5000ab66352169400cad28c025a00532b4310656801298798c0b5afd33eb400b41b260502d9a6345a5001ab400521b29e752d8d1fa5a003a2b4000c63b3e92ad494025a0035ab5ad28d6801052e000065b319fab6de67d6c14d6ad000216c00010daa902d68bc0cad0000d5a8b814b634021686200ad45c035a51806b52500d6c9801ad00005773d804b4002b96c68502d0000862bda2e86345210d233dadac97b4200084b4005bcd0014b2d064085a00000b40088169322f2c520a85a000c6b4008458bf4fd2d000075a0014744003f63d533187178035a87862840017988015936844035afd016b58a00d69fa502da44285a000171c005ed8c1492ad494315aa41d4b548015680052ad6b4a3228500ab4001bd6c42502d98c315b3da4ab400071680001c0014025a003f4d800001b0000052000215c004151d0f0c56800a431001f15ac2016b634829683201ad9a6630f08862a9700c56d22a42d0027b8f3d862b6b20c5680011ad5a4085a92832b4003f56801593198c055ac2006b5fa0096c6892ad494a05acf94cb40000259d451ad0019535349d4b66517968b80cad98ca35a000e8b58a5216800002f98c2a5a0053eb6d00c56d651a21881fa5b68414b4ea17950007551844335b0533eb5840c56d153dad002a30e6f146b66928d6cf610ad828035a00484b5fa2d96b14c21a7e9255a50006b6a90216800754767d8434cf862b4003616a4a042d002345c0024b1e7b07168006f2d45c0b5a2f062a9170f5680018c0178085a7e9d4b5745550d655487001488ea7a90b5484956842012d6b4035b549fab40015d680050473a8425b59010b4007e96b5acfad5545e5b319d4b4001656c9c042d0c4315acf9d4b67b67d69d42f2db400b5a000bceea90856cca2f070000082003c4b61102d68ae02ad, 0x1256c0c006b691495680115ad00021a267806b4004f9694605ad04c035a928bca80b02d6af610ad0002a5a00148b52502d6b1405ad002510e518bcb6b200d684210ad628fd5a00208b4000c570002fad120055a04010b59f52168005040a5a915aa40d6b4080156862012d6285e5b31806b400002a5caa42d8820a5a0024ab40076569a4042d000058e00146d82100d6800402d001ad5c01002b40012569fa51ad934055a0f016b4005edb476fd2d5ec1c5a002beb60a065681600ad7882122fd010b5043f568001bada6e915b1a032b5840156ca618ad1f4035a7e804b4001f56b96d6ad002560e00132b29128d6bce1891014055a000bd45043a96a2e042d02c025a18806b400aa5b41402ad000935a000a2b4a00c56d2201ad000026200066b45e0056b3e0cad28ca35b59364b59528cd0011a36000a06c000acb66917969fa52ad3f474542f00ab40002d71fa0cada46630f54940b56800d694005ad715ad580026ab50a02d680079adac85e5a0004300005c0d006012d0000064fd006b4c128d6b3ecfad001c55a00290ba968296d2202ad0019f8ec5010b5201790800043b28c215afd062b66902d6bba0cad002b28f050bcb40001600bc05ad6959f5b1dc68b6a90c5681001adb40035a8b940b400a45700035ad00000660000ad80028e39d4032d280085a00032c52528d6cc6fd2d7e85e5a00236b58a281680018b6001dd5abd80ab6636bd680a01ada7e915abd8bcb400002380086a1909255b0c422b4000d1683c042d0019f5a00000c6113f56d22d6ad5ecea5acf816b4fd0856800fd2e9e8a30f3dc14b5ad3f56c14502d844315a00062edff17889d4502d98c5e5a001d4b40002288011a47b7e915b59146b6340856b0803ad846115b1a146b6910096800da2d28ca05a00076b4003a98c48d6a17e8a35b10c22b6d00156c9e05ad]
  | 10 => [0x17010b6115a00310656800b5ad5b1a2d00968bcb5255acfad8296cf6b4035aa42d01569d4b5fa5a10ad28d6816b4006c7ead0c56940b4008f48ad]
  | 11 => [0x7f]
  | _ => []

def C28_buckets : Nat → Nat
  | 5 => 7
  | 6 => 86
  | 7 => 411
  | 8 => 684
  | 9 => 242
  | 10 => 7
  | 11 => 1
  | _ => 0

def C28_flag : Nat → Nat
  | 5 => 256
  | 6 => 0x2000
  | 7 => 0x1000
  | 8 => 0x2000
  | 9 => 0x1000
  | 10 => 128
  | 11 => 2
  | _ => 0

def C28_seedBits : Nat → Nat
  | 5 => 9
  | 6 => 14
  | 7 => 13
  | 8 => 14
  | 9 => 13
  | 10 => 8
  | 11 => 2
  | _ => 0

def C28_seeds : Nat → Nat
  | 5 => 0x4dce052c8602c01
  | 6 => 0x2802103e000e003414b676c29b0a880ad0248685000c104008008e028c05e02080a5000800921cc225005403d0018002000a12200a00080958135001400903240a2001000f001444e05a0002009801e023e0ef0010024007801d0084002002400c00080370038001000400100040010050003016409700981c3004800b00e000a010c0040600110009804900c0005000400b00e800d
  | 7 => 0xc00a40e0159790b0a00625a804800417a0060c480e8741070813887c670039d9a463222ab28800412605db0f8cec012eb2042803800413a002002013212a01180f406601200200180055d222e048d41e00f038008c17069c07c80110e609a01e80040100d2011062cdd15b00e981ec13e2e211200c8156084b36075c54c27c01100a41b600902b020800606801c82f42e20f5010803401e2e9013800c01c005042004c0060ad01d800ab4600300e82e80b0005000848800401f1ee56800ba04eaca009c05204900303f48ea02f45e05b009e012abd80240195780488360004004007057847c009b3600540040020618eb80840010520012aae00200580040f20fb099800453800e029001420000a00185a6a8c3480938660021494066802411c0c604000e803400400f018800c03003d0048270288003804851a001034d0500080b600c82e400c01305b003400a0010a6cf0801c057018005a77a029973804405c0b2941800c0140030768066cd8001000d9b02da3eb0d9000408413f02200dc1881a700080bc06800c009806401000100100441d0014001800417c00e92f87e818801b0018602cd924a923000647a02e004024c03721000100700283dc000c73401000102702500200e38e4c60802600c8b98070074005004803c01c05300d00062b407a005805807a1ac007000402a00300ac4f40fa00c034802409e001007827c06f12200c846400403c00700ac00402202a800400204700580120e20030020026cd804e02b0004052001015800805400200203c8034004b3600180020080c280081f200a01381b80f8003000803405c01601e59b009a007007414001603202581d2cd80040058058032006000800402c019001800601c00500080c005a0120310008074044001800c00202b027011c00200b01e0294006001
  | 8 => 0x4eeaaf00145280940f122ddc3ab00e41e6071800f03802d90a4c00210880d90560fea1090176750c1d401c403a04600b300fc07c0df427f201c00eaa306d70aeea8100583a003f876b1968002001c032055800a0024006008002e01b50280582aaf0070005012c0b6001c013035801f003297f01d80010e9434a0014048162eaafa58c417042800a000c11fa578053025e8c702a4001a09c2b1057801500340050270002016400102a42b100142fe01e41af00b801b0064034a06802004849c70e98153000c01d002c00108e00030100322181800309f8009000c39602880270a42aaf000805d02627f01b640ac04a047f000c26500940ca0b8c0fa0ef40df002eaaf020011101681aa021813d022c0500020001003402500e012d138001f000a7b4009c03007a03f907cc00503c404c01c279500d02eb00940090710018002000a02742620010005056001200100020098021199001c0008016001400100080d300e013c02a40049df00cf00080010614016000807505e400403b410a02e672f00042c3000821503341780282714007c0a10028008091c0a4000aaaf0bf004f0018002107412300f000200d800300080059c0002e00626f7021402b09f813905d66f1142c03700240b4aabc24500ec0109aa000300b8040993007d0074023007000500d401200040d50004005002407a03c40210042635006062d021c18b01d8560aabc1d602b000200e260a00400fd024c00a014814d00f000a014c03b002400400040520004004007c00300cc05b00e40250060015000800400565fa00301cf026c014033802f013400200bc0740004003aabc3cd000c0010034145aabc0c701ec010972800104500f302100cf0094002036c00406a816202080080008009940005f00480010024013016c10b004401d000a4da001007301b004b92ee492921245b02f808b001801c000806f0428018002aaaf00b0052001c002009244e01e00eb00c2443005404e90e808b05cc1d390d6416901c028000800501a800d000c0018f0803201680810040013003c00101580110114130001c013067c02c8ef80620090005021c017017801905faaaf8b9a2c8001805900a014700e801500062c600a00440026285000400200580110870004025c029011c0018a041d50154002003001c004c049005e279000804b8950001894002c002000a893401d019c012002c00d87b4015024c12d002c0010080024878003a01700010008004000c001067c018002000403000140058002018aaaf013c008018e1c0008400700e002201d800800d40d00062aaf003404600e80060348170003c04101e402b000c008005eaafaabc018005803a000400100a400300b4019005400f00201e7006a1ae0008001019400d0018001002008e004002a000400201c801b011c0050014003000410401120de000400b00400020144189038c0358220087000802500ac015000406000d00160018009004c018040c001000c0010004011002c008000c048002003800200050004005026000b00f607c00380170038010034c005018e041803c016aabc00101e000b006c00d00280060018021001405f000c00400480010080001042c005000c00804ec0660020011000c02100040040048028000401c00080100004005001c00e00100020014001
  | 9 => 0x2778097111086c0ec00b05f80a800600200080905b842000113dc0022c32e980d003201703c002406202500680080080101008d654b003e016813a74f38800081026d003700200291bc0c100401a408a002161008a6740070f30c0c0c800501380c80040bc201025001407213204ac9ce1ad040001411200100c001801c0b9027000800533800e00a005000d0a085a813e08500b80f400c1b4001003c00200a22b4c384580b797600140380640008bb448800896982fc0ec003002825000204c03280080021a99e400e406800b96381bc06d1d60aa023802802c1d9009c006020005802c02e01a00a01e419004200180080b8143032811c09200e000802c04118b000800c23000b042804803600f00380241bc087019800403c05d01181e80140049e400062fd1630788030284026009005016218c000806c04a007000802c00c0999e4008401a00c007800400e01200080b80a00a7892c490016013084000c05400100ac2a8003093005001210600600180602d507c06780100140020034028008008024801c03401d
  | 10 => 0x4c13953f030f01
  | 11 => 2
  | _ => 0

def C28_S (s j : Nat) : List Nat :=
  qDirectStatePattern C28_initial (C28_countBits s) (C28_patternBits s) C28_patterns 16 10 (C28_slots s) C28_values
    (fld ((C28_records s).getD (j / 256) 0) (C28_recordBits s) (j % 256))

def C28_idx : Nat → List Nat → Nat :=
  qIndex C28_N C28_buckets C28_flag C28_seedBits C28_seeds


def C28_routeCodes : Nat := 0x5550000032100000050e000000100000000000000000000001000000101000005550000000000000000000000000000000000000000000000000000000000000000000000000
def C28_masks (auto : Nat) : List Nat := (List.range 9).map (fun i => fld C28_routeCodes 32 (9*auto+i))
def C28_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C28_rankPool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505]
def C28_inputActions : Nat := 0x2e4631ac688

def C28_inputRows : List Nat := [10, 33, 44, 52, 65, 82, 84, 3, 5, 9, 17, 6, 34, 24, 72, 96]
def C28_xs : List Nat := [0x792, 0x18a1, 0x94c, 0x6205, 0x2468, 0x900e, 0xc070]
def C28_f : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
  (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) ||
  (x 3 && x 6) || (x 5 && x 6)

theorem C28_enc_inputs : (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C28_inputRows) = C28_xs := by decide +kernel

theorem C28_enc_goal : encL C28_f C28_inputRows = compactGoal 7 9 := by decide +kernel

theorem C28_proper : ∀ zs ∈ C28_xs.sublists, zs ≠ C28_xs → compactCover 7 9 zs = false := by
  decide +kernel

theorem C28_initial_perm : C28_xs.Perm (C28_S 11 0) := by decide +kernel

def C28_routes (auto : Nat) : List (Nat × Nat) :=
  (C28_masks auto).zip [1,2,4,8,16,8,4,2,1]
def C28_act (auto : Nat) : Nat → Nat := routeStages (C28_routes auto)
def C28_actions : List (Nat → Nat) := (List.range 1).map (fun i => C28_act (i+1))
def C28_ori : List Nat → List Nat := orbitActions qPrefer C28_actions

theorem C28_routes_valid : ∀ i : Fin 2, validStages (C28_routes i.val) = true := by decide +kernel

theorem C28_routes_goal : ∀ i : Fin 2, routeStages (C28_routes i.val) (compactGoal 7 9) =
    compactGoal 7 9 := by decide +kernel

theorem C28_ori_run {s ws} (h : MonRun (compactGoal 7 9) s ws) :
    MonRun (compactGoal 7 9) s (C28_ori ws) := by
  apply orbitActions_run h qPrefer C28_actions
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨i,hi,rfl⟩
  have hib : i < 1 := List.mem_range.1 hi
  exact routeStages_run hz (C28_routes (i+1))
    (C28_routes_valid ⟨i+1,by omega⟩) (C28_routes_goal ⟨i+1,by omega⟩)

def C28_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 9) (compactCover 7 9) C28_S C28_N C28_idx C28_ori
    C28_coords 4 C28_rankPool s

theorem C28_decoder_diagnostic : (qNorm (C28_S 8 0)) = [0x792, 0x94c, 0x18a1, 0x1fb3, 0x2468, 0x6205, 0x900e, 0xc270] := by decide +kernel

theorem C28_fair_decoder : qNorm (C28_S 8 2358) =
    [0x792,0x94c,0xf92,0x18a1,0x2468,0x6205,0x900e,0xc070] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_benchmark_one : span (C28_Z 8) 1 2358 = true := by decide +kernel

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

example : span (certAt (fun _ _ => true) (fun _ => 2) 3) 6 0 = true := by decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_0 : span (C28_Z 8) 1 100 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_1 : span (C28_Z 8) 1 101 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_2 : span (C28_Z 8) 1 102 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_3 : span (C28_Z 8) 1 103 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_4 : span (C28_Z 8) 1 104 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_5 : span (C28_Z 8) 1 105 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_6 : span (C28_Z 8) 1 106 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_parallel_probe_7 : span (C28_Z 8) 1 107 = true := by decide +kernel

end PEqualNP.Outside.L_meta_984.Cert
