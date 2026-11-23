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

def fastEntry (k bw : Nat) (coords masks : List Nat) (code : Nat) : Bool :=
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
      (coords.getD d 0) (coords.getD e 0) (coords.getD f 0) (goal k)
  else false

theorem fastEntry_no {k s ws} (h : MonRun (goal k) s ws)
    (hl : ws.length = s + 1) (hsize : ws.length ≤ 12)
    (bw : Nat) (coords : List Nat) (code : Nat) :
    fastEntry k bw coords (coords.map fun j => row ws (fun w => w.testBit j)) code = false := by
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

def fastScr (k s : Nat) (coords : List Nat) (bw : Nat) (pool : List Nat)
    (ws : List Nat) : Bool :=
  if ws.length = s + 1 ∧ ws.length ≤ 12 then
    let masks := coords.map fun j => row ws (fun w => w.testBit j)
    pool.any (fastEntry k bw coords masks)
  else false

theorem fastScr_no {k s ws} (coords : List Nat) (bw : Nat) (pool : List Nat)
    (h : MonRun (goal k) s ws) : fastScr k s coords bw pool ws = false := by
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

def barFastOrbit (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat) (coords : List Nat) (bw : Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (s + 2 - ws.length) ws fun zs => covers k zs && !(fastScr k s coords bw pool (ori zs)) && !(found S N idx s (ori zs)))

theorem barFastOrbit_sound {k S N idx ori coords bw pool} {s i : Nat} (hb : barFastOrbit k S N idx ori coords bw pool s i = true)
    (hr : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (h : MonRun (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun (goal k) q (S q j) := by
  cases s with
  | zero => simp [barFastOrbit, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k zs && !(fastScr k s coords bw pool (ori zs)) && !(found S N idx s (ori zs))
    have hF (zs) (hz : MonRun (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, fastScr_no coords bw pool (hr hz), Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barFastOrbit_all {k S N idx ori coords bw pool} {cap : Nat}
    (hr : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barFastOrbit k S N idx ori coords bw pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := barFastOrbit_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barFastOrbit {k S N idx ori coords bw pool cap i xs}
    (preserved : ∀ {u ys}, MonRun (goal k) u ys → MonRun (goal k) u (ori ys))
    (checked : ∀ s ≤ cap, ∀ j < N s, barFastOrbit k S N idx ori coords bw pool s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun (goal k) s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact barFastOrbit_all preserved checked cap (Nat.le_refl _) i hi
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

def distances : List Nat := [1,2,4,8,16,32,64,128,64,32,16,8,4,2,1]

def routeFixed (masks : List Nat) : Nat → Nat := routeStages (masks.zip distances)

def validFixed (masks : List Nat) : Bool := validStages (masks.zip distances)

theorem routeFixed_hom (masks : List Nat) (hv : validFixed masks = true) (a b : Nat) :
    routeFixed masks (a &&& b) = (routeFixed masks a &&& routeFixed masks b) ∧
    routeFixed masks (a ||| b) = (routeFixed masks a ||| routeFixed masks b) ∧
    routeFixed masks (a ^^^ b) = (routeFixed masks a ^^^ routeFixed masks b) :=
  routeStages_hom _ hv a b

theorem routeFixed_run {y s : Nat} {ws : List Nat} (h : MonRun y s ws)
    (masks : List Nat) (hv : validFixed masks = true) (hy : routeFixed masks y = y) :
    MonRun y s (ws.map (routeFixed masks)) := by
  rw [← hy]
  exact Run.map (routeFixed masks) (inv := fun a : Nat => a) (inv' := fun a : Nat => a)
    (fun _ => rfl)
    (fun a b => (routeFixed_hom masks hv a b).1)
    (fun a b => (routeFixed_hom masks hv a b).2.1) h

def cachedAction (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (w : Nat) : Nat :=
  let i := lookup w
  if i < count ∧ keys i = w then values i else fallback w

theorem cachedAction_eq (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (w : Nat) : cachedAction keys values count lookup fallback w = fallback w := by
  unfold cachedAction
  dsimp only
  split
  · rename_i h
    rw [hcorrect _ h.1, h.2]
  · rfl

theorem cachedAction_function (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i)) :
    cachedAction keys values count lookup fallback = fallback := by
  funext w
  exact cachedAction_eq keys values count lookup fallback hcorrect w

theorem map_cachedAction (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (ws : List Nat) :
    ws.map (cachedAction keys values count lookup fallback) = ws.map fallback := by
  rw [cachedAction_function keys values count lookup fallback hcorrect]

theorem cachedAction_preserves (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (P : List Nat → Prop) (ws : List Nat) (h : P (ws.map fallback)) :
    P (ws.map (cachedAction keys values count lookup fallback)) := by
  rw [map_cachedAction keys values count lookup fallback hcorrect]
  exact h

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

def bExpand (d x : Nat) : Nat :=

  let x := if d ≤ 64 then (x ||| (x <<< 64)) &&& 0xffffffffffffffff0000000000000000ffffffffffffffff else x

  let x := if d ≤ 32 then (x ||| (x <<< 32)) &&& 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff else x

  let x := if d ≤ 16 then (x ||| (x <<< 16)) &&& 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff else x

  let x := if d ≤ 8 then (x ||| (x <<< 8)) &&& 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff else x

  let x := if d ≤ 4 then (x ||| (x <<< 4)) &&& 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f else x

  let x := if d ≤ 2 then (x ||| (x <<< 2)) &&& 0x3333333333333333333333333333333333333333333333333333333333333333 else x

  let x := if d ≤ 1 then (x ||| (x <<< 1)) &&& 0x5555555555555555555555555555555555555555555555555555555555555555 else x

  x

def bPool : Array Nat := #[0x0, 0xff00, 0x200000, 0xff0000, 0xffff00, 0x8000000, 0x8100000, 0x24810000, 0xff000000, 0xff00ff00, 0xff00ffff, 0xffff0000, 0xffff00ff, 0x55557aaaa, 0x800000000, 0x800000080, 0xffffc0000, 0x1000000000, 0x1111111111, 0x2080000000, 0x2222222222, 0x3333333333, 0x4444444444, 0x5555555555, 0x6666666666, 0x7777777777, 0x7f015c3870, 0x80001c0000, 0x8888888888, 0x9999999999, 0xaaaaaaaaaa, 0xbbbbbbbbbb, 0xcccccccccc, 0xdddddddddd, 0xeeeeeeeeee, 0xff00000000, 0xff0000ff00, 0xff00ff0000, 0xff00ff00ff, 0xffff000000, 0xffff00ff00, 0xffffff00ff, 0xffffffff00, 0xffffffffff, 0x1b00e000000, 0x288a0902d40, 0x29da0d7805e, 0x40000000000, 0x80000000000, 0x80008000000, 0xf9f602f6710, 0x1110024d5110, 0x119720180000, 0x1221f9774527, 0x191502c45719, 0x1c38751e0387, 0x1dec819ab880, 0x200000000000, 0x200024810000, 0x213d7f03db6f, 0x21a7201839ff, 0x254200192400, 0x25efa5000000, 0x280800028080, 0x2850a1e14285, 0x2ad5b49692f5, 0x412000248100, 0x412024a18100, 0x444444444444, 0x47648089a820, 0x48bb25d75772, 0x4ce933848e12, 0x55ef2500a7db, 0x57bedf66db7e, 0x5c28a0000288, 0x5eaaa8949547, 0x72e1bb68ede3, 0x749e2258f6e3, 0x800000000000, 0x80e000030000, 0x85f60018bd00, 0x8879004e1600, 0x888888888888, 0x8f7fd8ef9d4c, 0x93a0a15d3a24, 0xa14280142857, 0xa49a00b2f600, 0xa51f00185c22, 0xb00d00000000, 0xb6bad254b6a8, 0xc100fc003e00, 0xc180fc1c3e00, 0xcf5200000000, 0xcf5200808da7, 0xd48fc4e49b00, 0xdf0000006fd3, 0xdf2900400000, 0xe00df00e0000, 0xe040800e0408, 0xe1b0fe0c0000, 0xeeeeeeeeeeee, 0xf5b78dbd3918, 0xff0000000000, 0xff000000ff00, 0xff0000ff0000, 0xff0000ffff00, 0xff00ff000000, 0xff00ffff00ff, 0xff8670ffe9b0, 0xffff00000000, 0xffff0000ffff, 0xffff00ffff00, 0xffffff000000, 0x1000002aa8000, 0x102d400016800, 0x1142000214004, 0x115dc7a5bb351, 0x12a2408004800, 0x13952ab5d6aad, 0x14040fe6210df, 0x142850f0a1428, 0x148ab82bd05f4, 0x149452dab4957, 0x1508fe23208c8, 0x15100006804c8, 0x1520542ab6aad, 0x1546d417a3500, 0x154ad557b61c8, 0x1552bf4aa97fa, 0x1556aa7aa8000, 0x155dfbc3333bc, 0x15e9fda67699d, 0x16cddcc66f1a4, 0x16f25cc66f1a4, 0x17cadf5d9e3e8, 0x18b662da7091c, 0x18ee64497121c, 0x1991014520000, 0x19e9e20e79500, 0x1a36e8ae5d412, 0x1b0eec3848e12, 0x1c07f0143c78f, 0x1d4285002850a, 0x1d52a4b696d0a, 0x1e3c7851e0380, 0x1fa021a6aacd8, 0x1fd4204fbd342, 0x2000000000000, 0x2000008000000, 0x2009d00000a00, 0x2082002aa9454, 0x2380810238081, 0x247f010247f01, 0x2602022ba8a20, 0x2845421548af8, 0x2a0ba81f79554, 0x2ab50005eb838, 0x2bbfdd2777770, 0x2d2ff4227df85, 0x2e28100352080, 0x2e9d477f7ba10, 0x2ece9ab5fdce9, 0x3000000290000, 0x300be939f9e20, 0x373b700a9d9bf, 0x4008cdc8088d0, 0x4122028457240, 0x4400008000000, 0x44024ca976c42, 0x4880988545710, 0x4c51340088800, 0x4cc0014cc8810, 0x4e2a498b77ab0, 0x4efe65bba3a2f, 0x6003fc6004b24, 0x62d31004b0300, 0x66f0010017f80, 0x69f5010010000, 0x6aa3400b92810, 0x6aac4a013d2ba, 0x8102400810240, 0x84086c084086c, 0x9000080030000, 0x92870a5000000, 0x95209a50239e7, 0x98d0080033300, 0xa800000a80000, 0xbbbbb08177fee, 0xc002093909e00, 0xd0000f2600000, 0xf0000001f0000, 0xfbfff009fffff, 0xfffff001fffff, 0xfffff002fffff, 0x10000000000000, 0x10000201000020, 0x10111001011100, 0x1021b600839c00, 0x105a29b634d3bc, 0x15540002200000, 0x187ffe6f5b804f, 0x18805b6f5b0000, 0x1b623301b62330, 0x20000000000000, 0x20000080000000, 0x20110262011026, 0x20331502033150, 0x204020de200000, 0x20ff21de200000, 0x22200002220000, 0x22222222222222, 0x242700080f0000, 0x24f40808f88080, 0x28008882800888, 0x28507242850724, 0x2b50a802b50a80, 0x33001583300158, 0x3468d663468d66, 0x3ebcc9f3ebcc9f, 0x404cbe40269e00, 0x40788f80b55800, 0x40b18f71d9a739, 0x40cf80ffda10ff, 0x420b67ff1b34bd, 0x425e0804854300, 0x44444444444444, 0x45820100184200, 0x489b560489b560, 0x49962000000000, 0x4d91fd64d91fd6, 0x4f0000001f0000, 0x50140805014080, 0x50280005028000, 0x50615e450615e4, 0x50a142850a1428, 0x556aa80556aa80, 0x5a755e45a755e4, 0x61008000d60000, 0x6190b04fcb4000, 0x66666666666666, 0x6ad57256ad5725, 0x700c0001006000, 0x710c6c017c0c00, 0x72080009205aaa, 0x7208a00b280000, 0x74602207460220, 0x76677447667744, 0x77777777777777, 0x7ac12577ac1257, 0x80000000000000, 0x800000001c0000, 0x80200000080200, 0x808a800235c000, 0x80e244880e2448, 0x88888888888888, 0x8998800a033300, 0x8fe70108fe7010, 0x957eaad957eaad, 0x99999999999999, 0x9a16a859a16a85, 0x9b230bc9b230bc, 0x9f0d096912c000, 0x9f54f4c41b1070, 0x9fe6f24f46c8bd, 0xa0140ada0140ad, 0xa028150a028150, 0xa1e257aa1e257a, 0xa809080a809080, 0xae06bd5ae06bd5, 0xb4c40000d60200, 0xbbbbbbbbbbbbbb, 0xc003160c003160, 0xc08ce64c08ce64, 0xc4e806ec4e806e, 0xca02ac4ca02ac4, 0xcb972a8cb972a8, 0xcc00100cc00100, 0xd02c0100c03e00, 0xd7378c8d7378c8, 0xd7fcdd8d7fcdd8, 0xd88dd10d88dd10, 0xddd9980ddd9980, 0xde402000000000, 0xe449ff69299660, 0xe70fe080580700, 0xe71ff080a75077, 0xeeeeeeeeeeeeee, 0xf0400000e00000, 0xf062bb1f062bb1, 0xf120a1a2097000, 0xf26060f2f20d00, 0xf2c3796f2c3796, 0xf4f40f00f8f81f, 0xf7efdc4f7efdc4, 0xf8000001f00000, 0xf998926f998926, 0xfb8bfba209da0a, 0xfc3807efc3807e, 0xfc47f00fc47f00, 0xfcdd3efc00ff80, 0xfcee0df00ee0bd, 0xfe4060de2121df, 0xff000000000000, 0xff00000000ff00, 0xff000000ff0000, 0xff000000ffff00, 0xff0000ff00ff00, 0xff00ff00000000, 0xff00ffff00ff00, 0xff00ffff00ffff, 0xffb48caffb48ca, 0xffff00ff00ffff, 0xffff00ffffff00, 0xffffff00ff0000, 0xffffff00ffffff, 0xffffffffff0000, 0x100000000000000, 0x100000003000000, 0x11c0408e0204701, 0x120636062df95e7, 0x1209c9e62df0000, 0x123f80fe0204081, 0x1b00c0000000000, 0x1b00c000e000000, 0x300fe002500bc00, 0x393ece0701d3e0e, 0x4000cf707fff780, 0x400800019224000, 0x400d70807ff0000, 0x402010c38600000, 0x4081204bf610040, 0x5a3566857b45eca, 0x6004ea4485b03ff, 0x6007189484b0000, 0x7ff000007ff0000, 0x800000000000000, 0x80101fb81102040, 0x8155400822aa955, 0x82b000010160000, 0x900000004000000, 0x9e01f729ff27fff, 0xa80000000400000, 0xbf600000ffc0000, 0xbf670008ffcc000, 0xbff0fff07ff07ff, 0xd900000c3c00000, 0xdff00009ff20000, 0xdfff200ffff6000, 0xdffff600dff0000, 0xf00fe009300fc00, 0xf80ff009360fe00, 0xff8ff803df2ff40, 0x1000000000000000, 0x1111111111111111, 0x147029d1422220b8, 0x148a452297000000, 0x15722a09522260b9, 0x18902232e2a22150, 0x1af4a50000000000, 0x1af4a500a50242bf, 0x1afda50000000000, 0x20038038086d4490, 0x2004020010040100, 0x2008211008469620, 0x201b3331108ea220, 0x2095c00df002a820, 0x20a01008e0009000, 0x2222222222222222, 0x241e0000946b0000, 0x241e000094eb0000, 0x241ec180946b4200, 0x25f483d004be907a, 0x2601023010020150, 0x2604f74f0862bb09, 0x2611373b1088ab26, 0x261a931508496926, 0x2850a142850a1428, 0x2885dfc28235c028, 0x2dfb2d003edb3e00, 0x37eaef5e7629c8af, 0x3a1401d0a00e8500, 0x3a81d5047601c800, 0x3aa1566057941e4a, 0x3b00c00400000000, 0x3b40000000000000, 0x3b40008400000000, 0x3c1e1d08440001d0, 0x3c26f1e4370f1e3c, 0x3d180ce0700180f4, 0x3e10384417051c0e, 0x3e9209a82bc120fa, 0x4000000000000000, 0x40006104c0bf0000, 0x4000d4ffc0bff840, 0x400ff400001ff800, 0x401b108400af0000, 0x401b3b1084b41bcf, 0x4024000a88824100, 0x40810020b76edc04, 0x40810040b76edc08, 0x4096eddbc8010204, 0x4172b9a82bd72b05, 0x41933a4c173262d1, 0x433f433f03bf03bf, 0x43a70de43770e1c3, 0x4408e02008811c04, 0x440aa02a8a234088, 0x4482010018420000, 0x4482830118424200, 0x451d0628e8314741, 0x4582010018420000, 0x45c0008800222e00, 0x45c11f7847de2e08, 0x488101fb890fdfbf, 0x4890800009121000, 0x4c96eddbc9810204, 0x4d0b542d5ab57d05, 0x4f4f00001f1f0100, 0x50f12bd50ab43d00, 0x515544aa2aa8abfb, 0x51d0010088002000, 0x51d200aab7f00004, 0x51d210aab7f12004, 0x5480082000000000, 0x5482092000000000, 0x54f204a1ab7500df, 0x56542200d4d11100, 0x56a6090addc2615a, 0x5800202060800200, 0x5aef250000000000, 0x5aef6502a5005800, 0x6000000010000000, 0x600020000d808000, 0x600c100000830000, 0x600c9ff30183ff10, 0x610208b0800004b0, 0x613cb8be073cf4fd, 0x619600bfffff61bf, 0x620000021a088000, 0x627d00003c130000, 0x62804602b8209900, 0x649a4d2d534b24d2, 0x66680000ccc00000, 0x66805e8ab920b9a0, 0x6969ad2d6b4b4b4d, 0x6a0840429a889010, 0x6ad5ab56ad5ab56a, 0x6d64df6d4eccef0e, 0x6dffffc03affff80, 0x6e445ba89b80d96a, 0x6f7f1f1f3f3f2f2f, 0x6ff8df009bf07f00, 0x700c100000830000, 0x707f028290ff2cac, 0x70b85c2e170b85c2, 0x71fc7ff9f3f8bb93, 0x724062a237326c04, 0x75b6ea1b022f82e9, 0x7770000877711080, 0x78002020f0000240, 0x7affab2ad3ff0e85, 0x7b00c204c4bf3f40, 0x7b5b00e440af7b40, 0x7bf7ee24bf610244, 0x7e1c03f0e01f8700, 0x7e23f80fe01fbf7e, 0x7f600000ffc00000, 0x7f80000000000000, 0x7ffffffffffc0000, 0x8000000000000000, 0x8000000000200000, 0x8000000800000080, 0x8000014050200000, 0x8000014450201e80, 0x80006f8000070000, 0x8000bfdf0007078f, 0x8003bc480029f640, 0x800fffff001fffff, 0x8010005d502aac00, 0x801578000a100080, 0x80202b800a138150, 0x8024005b00000000, 0x803c005b6fdb90a4, 0x80f0001f00000000, 0x8123f80810247f01, 0x81801a00241bfd00, 0x819963b20731c93d, 0x84001355c0020008, 0x8437721563fb2444, 0x849b804996320000, 0x849bf600ff20963f, 0x84d2f620d6a000df, 0x8888888888888888, 0x8e9400008dcdc000, 0x8ff842fdeff814ff, 0x9000000040000000, 0x9000800122008800, 0x90b07f7f4242bfbf, 0x979418f7676890fd, 0x979900108dcec000, 0x9999999999999999, 0x999eeeeecccddddd, 0x99c8aa8340a2cc63, 0x9a8888c022300c44, 0x9accc4cb3132e6e6, 0x9bbb3775ccee66e0, 0x9c00029f00000000, 0x9c00029f42dfbd20, 0x9d20029f00000000, 0x9fbf00003f3f0000, 0x9fe7201800000000, 0x9fe7601a6018de20, 0x9fff00003fbf0000, 0xa225545577fa8aaa, 0xa880022010080400, 0xaaa55608aaaaa880, 0xaaaaaaaaaaaaaaaa, 0xaba0081545761557, 0xad154280502b4550, 0xad2a816e502b40ad, 0xad302b800a14954a, 0xad3500150a1696ad, 0xad3b940ada028150, 0xb000000000080000, 0xb0404400f4000800, 0xb1a4404b00000000, 0xb1a4404b485bb710, 0xb500018004001bd0, 0xb532229563f70044, 0xb74000003e880000, 0xb7a4404b00000000, 0xb96f0000b05f0000, 0xb96f4ff2b06f0000, 0xb96ff69dffff4200, 0xbb082a0a02201480, 0xbbbbbbbbbbbbbbbb, 0xbbbbbf6677777733, 0xbd55ba7dfe99e7bd, 0xbd65e7be7fd6bdbd, 0xbdb4b8477f96f449, 0xbdd22cc1fec93e80, 0xbf8020ffbf8002ff, 0xc884022040884442, 0xcf7f000000000000, 0xcf7f024000000058, 0xd0280100c0300000, 0xd0282d01c0303e00, 0xd055028205541550, 0xd0ff6f0b60ff9f0f, 0xd1280000c0300000, 0xd2250000c12c0000, 0xd2ff0008c1ff0000, 0xdf6008ffff9002ff, 0xdfbf000000000000, 0xdfbf1008000000ef, 0xe888a6900e408c64, 0xeaaf414200000000, 0xeee00000ccc00000, 0xeff8100000000000, 0xeff810001000c07f, 0xeffe100000000000, 0xf000070800000000, 0xf0001fff00000000, 0xf20fffff3c2fffff, 0xf40027080ffff800, 0xf4f4f4f9f8f8f8fc, 0xf8f0f000f8e0e000, 0xf8f80000f0f00000, 0xf9252d00da2c3e00, 0xfb7fbcc0f7bffc40, 0xfc00fe0001e30000, 0xfe000000fc000000, 0xfe10158ec952b254, 0xfe51959ec953b254, 0xff00000000000000, 0xff000000000000ff, 0xff00000000ff0000, 0xff00000000ff00ff, 0xff000000ff000000, 0xff0000ff00000000, 0xff0000ff0000ff00, 0xff0000ff00ff0000, 0xff00ff000000ff00, 0xff00ff00ff0000ff, 0xff608000ffc00000, 0xff609fd0ffc06fe0, 0xff80679880079f40, 0xff90f002ffc0102c, 0xff90ffe0ffc0ffd0, 0xfff0000060900000, 0xfff00000f3fc9e00, 0xfff00000ffe00000, 0xfff0200060900000, 0xffff000000000000, 0xffff00000000ff00, 0xffff0000ffff0000, 0xffff00ff0000ff00, 0xffff00ffffff00ff, 0xffff00ffffffff00, 0xfffff400fffff800, 0xffffff000000ff00, 0xffffff00ffffff00, 0xffffff10fffffe00, 0x10062966121ffde48, 0x10204081020408102, 0x11740002011740002, 0x181a80100181a8010, 0x183580c18306b0183, 0x19404432480220300, 0x23653e64023653e64, 0x28283810083b71800, 0x2a5f497d054be92fa, 0x30003000000006000, 0x330d301104ccca000, 0x3496cd830692d9b06, 0x3b69c003f5e000100, 0x3c3031b0003000300, 0x3d8b0dc387b161b87, 0x48902448891204891, 0x6030180c06030180c, 0x67b0cfe24fb046f80, 0x7a995900689f71768, 0x7e02f40ae01554bd0, 0x810f02071021e040e, 0x810f0a161021e142c, 0x8dbc80e533c88e729, 0x996844f24b8225313, 0x9e01008f620660100, 0xc0000c49010205c80, 0xc864328c0c864328c, 0xc88a40800c88a4080, 0xcd04c049410e853a0, 0xff01fc0df03aa8ff0, 0x102040810204081020, 0x111000000111000000, 0x111111111111111111, 0x112244891224489122, 0x12fd4be92a5fa97d25, 0x1380f01e42701e03c8, 0x15ab064c9ab560c993, 0x16803ab40d050ea800, 0x17049d430609d53308, 0x18080acbc3bc00486c, 0x181361d89b9c1a6563, 0x1b0001e5b360003cb6, 0x1b060de5b360c1bcb6, 0x1bac0a131a29524200, 0x1d80801203b0100240, 0x1d8489ee23b0913dc4, 0x1e8011140805028000, 0x1f00000000e0000000, 0x1f03ff0000001f0000, 0x1f11926b31f11926b3, 0x1f1f03001f1ffce000, 0x20507003aa8d0010a0, 0x205fb4efb49f906293, 0x209f91cbc2c0c0cb00, 0x222222222222222222, 0x222995cd763904c46b, 0x23604c112440c83220, 0x255dcaaa5255dcaaa5, 0x2760c3512245c03374, 0x29402a000e0a069400, 0x2aaab5555400000000, 0x2aea2555eea0155c00, 0x2c22084822c2208482, 0x2c7f0fe1bd8fe1fc37, 0x2d0041e905a0083d20, 0x2f000b80e000030000, 0x300000200084000000, 0x300008800330010000, 0x311118888800000000, 0x31748b701891da2560, 0x3176c458529d8a7a99, 0x3229e09998e9524603, 0x32339c8e7762c4e623, 0x32a8c8242064412164, 0x333333333333333333, 0x33333cccceeeee7777, 0x33fc83310330013760, 0x3633eca7a662ccf133, 0x380001420a042a1c05, 0x3c366cc00786cd9800, 0x3e3bf713dfc77ee27b, 0x3e7c59f007cf8b3e00, 0x3efdfbf7efdfbf7efd, 0x3f7e23f807efc47f00, 0x3fdf9f6a8df00bfd70, 0x3fffffffffffffffff, 0x40003000c400380400, 0x402000800402000800, 0x402010008402010008, 0x408890040408890040, 0x420011e001fc003e00, 0x434606110434606110, 0x443226644443226644, 0x480012090a07c28000, 0x488c53344488c53344, 0x4af553e804af553e80, 0x4ca65336c4ca65336c, 0x500a80200500a80200, 0x555400008555400008, 0x555555555555555555, 0x58dd6202058dd62020, 0x60097270f280e0f6ed, 0x600be0e0e0e9e07200, 0x630003400100000800, 0x640400088884400000, 0x655e9bb7d655e9bb7d, 0x66a6ed599b973bfe77, 0x67000d000000003000, 0x67e69234c36d199000, 0x6920243411a7009150, 0x696f7f04001e5e9640, 0x69baa46e369baa46e3, 0x6b0003f491fe205280, 0x6b886c569524fd991e, 0x707e3178e707e3178e, 0x7704166a8800400110, 0x771092be4771092be4, 0x7a68e33b88f87bb747, 0x7a889eae07a889eae0, 0x7e9f3e003e834e0000, 0x7f2ff8007fc07f01ff, 0x7f901eb157f901eb15, 0x800020000800020000, 0x800f00817f00f00100, 0x802888881802888881, 0x802c9050906090df00, 0x81001a006620384000, 0x82363e1a0083271a9b, 0x880022110703c1c000, 0x888888888888888888, 0x8a002294ba07d28000, 0x8b55550008b5555000, 0x90fef0001f0003fe00, 0x9103b142b006000000, 0x916611102200000200, 0x918ae8815918ae8815, 0x973f96a69e084e0000, 0x9787090100eeac2000, 0x97b56d0000b6844829, 0x986698806a8dfee64d, 0x999999999999999999, 0x9a00268cb9c3d27000, 0xa00029d40a00029d40, 0xa00032012545219a00, 0xa00a802a5a00a802a5, 0xa071d4c50a071d4c50, 0xa178a9d42a178a9d42, 0xa196a120b1b6317100, 0xa22008000201011100, 0xa24414674a24414674, 0xa3008124803d803600, 0xa44472ff250177f744, 0xaaa800000aaa800000, 0xaaaaaaaaaaaaaaaaaa, 0xab2602010262033150, 0xb03f334c4db6fddfcb, 0xb089329930c9702f00, 0xb1b7d922f97eb04d32, 0xb39006500300033500, 0xb45566200b45566200, 0xb8ac6f7c6b8ac6f7c6, 0xbb2c27210b84477240, 0xbbbbbbbbbbbbbbbbbb, 0xbca3af404420004000, 0xbfdfefe88bfdfefe88, 0xc00013444206499900, 0xc18991080c18991080, 0xc310000c11ed003350, 0xc336d68c3780f7315e, 0xc404e020e000000000, 0xc8aed88b374f37718e, 0xcb830c911584001000, 0xcccccccccccccccccc, 0xccf23dd542205bbfd0, 0xd51800800d51800800, 0xd818d818f8e0e00707, 0xd95ad863f82fb0f707, 0xdddddddddddddddddd, 0xdfdeffedbf9e90de48, 0xdfffc808025555c000, 0xdfffc808a8ffff6aa0, 0xe01fdb89f6063609ff, 0xe0e000001f03000000, 0xe1701a00e720b8e080, 0xe319afb1de319afb1d, 0xe7458c13240c066cf0, 0xe7bd15ee01fc00ff80, 0xec800200246004c000, 0xee1001088102837c00, 0xee9011888103877c00, 0xeeecccc00eeecccc00, 0xf11922464f11922464, 0xf187f1f4b1c030b17e, 0xf4fc38f9c4ff38f880, 0xf67b3d9ecf67b3d9ec, 0xfe38ff83bf83304242, 0xfe446c696196d84100, 0xfe6622e81fe6622e81, 0xfe97405fdfe97405fd, 0xff0000000000000000, 0xff00000000000000ff, 0xff000000000000ff00, 0xff000000ff00000000, 0xff000000ff0000ff00, 0xff0000ff00ff00ff00, 0xff0000ffffff0000ff, 0xff78818080ffc62020, 0xffff00ff00ff00ffff, 0xffff00ffff00ffff00, 0xffff00ffffff00ffff, 0xffffff000000ff0000, 0xffffff0000ff000000, 0xffffff0000ff00ff00, 0xffffff0000ffffff00, 0xffffff00ffff000000, 0xffffffffffffffffff, 0x1008040221ff007fc01, 0x100df1820ef00000000, 0x200f0000d4200000000, 0x27d4002fd80ff7cbfff, 0x27d9900008058000000, 0x2b12320202622024020, 0x300ff20fcffa1ffdf00, 0x30180c062301ff00603, 0x310ff18fcef86ffdf00, 0x39a00e69346182d86fb, 0x4a4d115400472bba640, 0x5028140aa5fd017f405, 0x5a00168015540540000, 0x652e88e2c16f4cc4f3c, 0x668edb42624f880df33, 0x70381c0e580381c0e07, 0x78801e20ef8f83e3eff, 0x7f8d90400013e0c8500, 0x800402012cd00000000, 0x808ea0022001401a310, 0x820fbdfdb005a005e00, 0x8f8400000e509a40000, 0x96c9368419e20210000, 0x96cfff3d7fe499efef7, 0xa5002940b50aa802ba0, 0xa8a82a2b6ab502ad40a, 0xb9a02e696bb5fd2d60b, 0xbf70000000000000000, 0xbf70000000002000100, 0xc4243128cc8077320cc, 0xc9c0d730df2003d0500, 0xcd36e000df208300000, 0xdd3ba22e990f8bb0eac, 0xe48839236eb703adc0e, 0xf5803d60b0b783ede0f, 0x10080402010080402010, 0x10a1e021040809c15bd0, 0x1100fb0024ff00000000, 0x1111002a83a9a3235400, 0x13000c00001110c02220, 0x13200e00021910e022ac, 0x134bec00100000000000, 0x134bec001010ef61df00, 0x14355052a1c0af702e80, 0x14990666202822055440, 0x1505e82a06a500154000, 0x18f7608180126d600100, 0x1900e000000108222220, 0x1de800000017fa480000, 0x1e14b01916da9c7064c3, 0x20005bffdf10df000000, 0x20334440020088000020, 0x20840040200060000020, 0x2100c000c0da25c00000, 0x2110bc1e028783d843d0, 0x2110bc5e3d184bdbac29, 0x2153d4d6c63e3bc57fd0, 0x219c402620889d400220, 0x22113c1e1d0783d7abd0, 0x222aca9f43e868aa5dbc, 0x2311bcde62b85bd0462b, 0x23a340a8a710b80fdf50, 0x2413341b90ef9f406090, 0x24138043904b000b0000, 0x242d4f42404287850040, 0x24724640c366cc8ca8d3, 0x2618cc00044992eee66c, 0x29675d8c236a00dbc063, 0x2969f90000d6ff960000, 0x2a0ad41504aa00168000, 0x2bff000021ff03000000, 0x2bffc00021ff0b000000, 0x2ea133718ad5907588cc, 0x2ed40000081bf5840000, 0x333300000099b3200000, 0x33cc00000833ec800000, 0x384aecd030ed32680200, 0x38e0071c00e0001c0000, 0x38e0071ce0e0fc1cff80, 0x3bc0f230002ec17c2400, 0x3ec338408183c3008102, 0x3ec38783000000400000, 0x3f400f00009b40058000, 0x3f402ff8809b4005fe00, 0x3fc21031403e58302440, 0x40201008040201008040, 0x40c131c5304e000e0000, 0x40c1404a334e3f408978, 0x4200104001a0001c0000, 0x42001040e1a0fc1c3e00, 0x42211088442211088442, 0x43b70001003ffe920000, 0x448bfc2fc5108cee4220, 0x46231188c46231188c46, 0x4810c40069b701200000, 0x4b10081048f7bf8f0000, 0x4d97960080a925756040, 0x542a00001807c3d0a980, 0x552a80000587c00b45a0, 0x562b00001a07c004ada0, 0x572b8000000003dc0000, 0x58d9b22a6d2a2ef576c3, 0x5a3dbcbba75f1e595e00, 0x5a4e5a40182008086690, 0x5d2ec0a045afd7f755a2, 0x5d7333b2cb82e5218dcc, 0x5f24fb24059a059e0000, 0x5f24ff77059b059efe44, 0x5f2fc020000807fc1000, 0x60681087200000000000, 0x6068108720000020c780, 0x60919146002980140000, 0x6091914624a9bd943f80, 0x61800200010000000000, 0x61800200410000004800, 0x6340816262110da0a310, 0x67df8800a75f58fa0000, 0x6969296900961e96bf00, 0x6b6f3dfa053c897f41cf, 0x6c9782679049e8d9ad33, 0x6e290042004f29084200, 0x6e680110401bfe0c4000, 0x6f004b00007f001f0000, 0x6f404b0080ff8c1f0000, 0x6fd06b462047f06b4220, 0x78c786d8b640be718000, 0x78fb300830ed227a0000, 0x7bff0000000070000000, 0x7bffb40020009fff0000, 0x7e621110511731c08c00, 0x7f2bee978c75611eef50, 0x80000000001000000000, 0x802b0302c000b030b9dc, 0x80402010080402010080, 0x80800302c05540322c8c, 0x80802020080802020080, 0x80b03670080822457c40, 0x818e3cf080e57dbe0000, 0x81f1dc400804b17f9c40, 0x82ab20aac40611018440, 0x84001100f700b5f66dff, 0x840041400000ca280000, 0x84422110884422110884, 0x86c40000b600411e0000, 0x880420008002040a8800, 0x88a2302404c2da22884c, 0x897ca25f33904ce41339, 0x8c2b101008c44eea008c, 0x8cd4dfc008c04dea008c, 0x8cd4dfeac8ca18bf7c8c, 0x8d7ea35fb7d06df41b7d, 0x90482412090482412090, 0x96120492600d800d0000, 0x9612f20d609d7f8096e4, 0x9e1c2aa8812c3ac54000, 0x9e696129000000400000, 0x9e699e40612969002108, 0x9f0649e900bf00029f00, 0xa804a888e4026c0aee40, 0xac04dd2b04550110a310, 0xac8800400ac4664440ac, 0xaf19b278887d42b7fc9f, 0xb2002c80140f9503e540, 0xb2a3303ccfb8e54c17e3, 0xb3002cc014079d01e740, 0xb30cb7cd01588f315440, 0xb4ff000834ffdb030000, 0xb68c3bbc69b7fe976a00, 0xb7002dc0100042e01100, 0xb8243881108188300440, 0xc00000000780f8000000, 0xc0000f8087fff8200180, 0xc0ffdeedc0da9e3f2500, 0xc1002ce0001ac0e51a00, 0xc2100235f6c33dbc93ff, 0xc2100808c200da010000, 0xcb36074134ffdf0f0400, 0xcc0e6454402c689a1320, 0xcc86a10000f670718000, 0xcc87b00080f6f1718040, 0xccd4efdaccc6e440accc, 0xcd98d52842ec4e7ab20c, 0xce66fa1cc3e93b3ae7dc, 0xd068341a0d068341a0d0, 0xd100908c803080c03320, 0xd3bb34eece39238e48e3, 0xd9787826304e7f80c930, 0xd9789158300680060000, 0xdb0092ad00b902309f00, 0xdc10d448e60902e0877c, 0xdc49db3104c94fb34e4c, 0xddefdc00df1800f70000, 0xe1a133146f39408c5f73, 0xe2800d60009200490000, 0xe2800d60c292f949f380, 0xe4b81807000800000000, 0xe4b8180700084008c780, 0xe5df0820fb0014ff0000, 0xe700877a00ad020df600, 0xe79f3c7c007e3e9cde00, 0xe922a100b00000000000, 0xe922f822b048b0000007, 0xed1e1612103f61342540, 0xeda4e7b6cdfa4e5b44df, 0xee03b8404d383c4cde63, 0xf078713881309841e0f0, 0xf07871b8c31188c1e0f0, 0xf2177200f2000a600000, 0xf217fbf7fbf6f1960180, 0xf4ef58fc48f7007c0000, 0xf820e000e00000000000, 0xf820f820e418e0000007, 0xf87c3e1f0277c3e1f0f0, 0xf87c69349a429e81f000, 0xf87c69b4da6d30600000, 0xf8a53e294b55c02a8000, 0xf8a73e29d4ea03c68000, 0xfa7d3e9f4da82c160af0, 0xfaa53ea954aa102974fa, 0xfc01a60000f710d58000, 0xfc7e3f1f89c7e40df8f0, 0xfc87c1e880f75170fe40, 0xfe773f9dcb15f0397cfe, 0xfe7f3f9fce17f3fa02f0, 0xfefdfefdfe0001e30000, 0xff000000000000000000, 0xff00000000000000ff00, 0xff00000000ff00000000, 0xff000000ffffff00ff00, 0xff0000ff000000000000, 0xff00ffff00ff0000ff00, 0xff00ffff00ffff000000, 0xffff0000000000000000, 0xffff000000000000ffff, 0xffff000000ff00000000, 0xffff0000ffffff00ffff, 0x100a54028000544540000, 0x10180c0603e17f40602f1, 0x10201d2d0001c043ca000, 0x1030aeb284940aa516ac0, 0x10381c0e079c7e40df8f3, 0x1041044ca29869a654000, 0x1048216cb7ac2de93f904, 0x10582968b45a2d7160b05, 0x10582c160bda82c160af5, 0x10683164b3eef717a0d06, 0x107839e0f0783c79fff07, 0x10783c1e0f6783c1e0ef7, 0x1087c421f0b87bc01eeb8, 0x108840482412f2fa210f0, 0x108841c0e187381c1e0f0, 0x10a95462851451c410050, 0x10c8604c27c4e2732190c, 0x10d8684825e509055eb0d, 0x10e870c463c6e373a1d0e, 0x10f879c0e070c3e3e1f0f, 0x1101888a884c092222000, 0x110884422110884422110, 0x11120ceeee64101666ec0, 0x11159180da7394fa76e73, 0x111b32020022000200020, 0x111dfececca315575513c, 0x120400170006868005c00, 0x12e112613de420620efd3, 0x13435747b1b6076cda3d3, 0x136004d800807b201ec80, 0x136004d80140fb503ed40, 0x13ac762bf530581d70f30, 0x149fcd27f349fb527ed49, 0x14c7e531f8bc062f018bc, 0x14dfed37fb4df9537e54d, 0x15122ecccca3744ccef7c, 0x15307162fd91bf440ef33, 0x1590783279acc6b30280c, 0x15a0056940205eed42aa0, 0x15cbf446ec2b19f66607c, 0x1658b0eecc685133ef7bc, 0x1694043fb9aebdb2d205f, 0x16ad72e87007cd76ba320, 0x172005c8008079201e480, 0x173005cc0080062001880, 0x173065cc188cf9a33e68c, 0x177005dc0100044001100, 0x177045dc1108fbc23ef08, 0x1792ff4e40b6205d88423, 0x1810cae0c9104080e1110, 0x183c1bc1e1d07840fa9d0, 0x18408da186108050d2210, 0x18a146c0051042b512510, 0x192c964b2592c964b2592, 0x19851f4c8801111ce6220, 0x19d222000026800c8aa20, 0x19ece521cce8c667899dc, 0x1a006ede11000f4d50c40, 0x1a9d4fe7f3a1fcc24bda1, 0x1abd5feff7a3fdff0f9a3, 0x1b04ce70591414c840390, 0x1b181337621a3a9895400, 0x1bef52e2f00ffeb1f5f00, 0x1c0900214884e46302c0c, 0x1c491473622c446322c0c, 0x1c8cc8128448c4720040c, 0x1d4ea753a9d4ea753a9d4, 0x1d5eac2a142a85408442a, 0x1d6eb75badd6eb75badd6, 0x1d7ebc221008783dfae08, 0x1f09572e3595db6416af0, 0x1f0b57c2d56ab002ac000, 0x1f0b77c2dd6eb003ac000, 0x1f2022080005008ce8020, 0x1f8fc7e3f058fc7e3f000, 0x1fafd7ebf4a5fd017f400, 0x1fcfe7f3f823fe7f3f800, 0x1fda4d7b6cdf59af2d9df, 0x1fe7a4f7823cb667f445f, 0x1feff7fbfc21ff007fc00, 0x2000030e410101804fc00, 0x200a424f40000868cde00, 0x2012b1300120310010120, 0x20733120dc3008a311753, 0x20a546c00a50817a01a50, 0x20bdd7c25a50a57ea1e50, 0x21002d0840018301e8600, 0x22033445100e48b333020, 0x224d4000c4081e0cc1440, 0x228018a006404b9012e40, 0x22b429c1808cd085a1200, 0x238319443256913c01390, 0x239118e446633098cc263, 0x23dc9dc8c4200089b846c, 0x2412c4d0da732da0ad8d3, 0x2668f990004079662c040, 0x275e4f1be64bd06f679cf, 0x288360a06804009402500, 0x288a8620280c044352800, 0x2890937b288c0882b0540, 0x2898b93c288c0c4a6a440, 0x28d78f2019ee2316c8f73, 0x296299c30202818e0a310, 0x2a8fd572108014c414550, 0x2aaf7ffe9c83f7e87fff0, 0x2ac5bab3c4815ff057fc0, 0x2b54a8c4448df68782020, 0x2bd0b4b3900df09617920, 0x2c0011802e08030100c00, 0x2c38118e2e098305a0c23, 0x2c39018cc0e37518dd463, 0x2c46d2980608c5721148c, 0x2c89f0cc0dec63d88d1ec, 0x2e4a878c0600368caabf3, 0x2ffdfdbbf00efe77fbf20, 0x2ffff5faf10fff7c37f00, 0x3106a8810a2841e420050, 0x310ac0000000000000000, 0x310ac6fb4ffff6fb4ffff, 0x31c23d6455b0199e627f3, 0x322092cc4422b01164040, 0x32f93c30f11b7747cbf40, 0x333000000013388800000, 0x33300ccccc91100ccc660, 0x333b30000011911000000, 0x33c369e6e4e2776cca3d3, 0x3505e8015085a00168000, 0x350fe9c76e7ad3e429070, 0x354a4723180ea25fa44cc, 0x363018cdc100337bca820, 0x3644fd852a095fb257ec0, 0x364bf664004997fcd9540, 0x367bd0800b8486f000000, 0x3765088d4263f558fd563, 0x37a322044dc014013cdbc, 0x37ddfecec0159d4448400, 0x37f000302cafd40302c0c, 0x3909ee425104430110c00, 0x393d44cf5186c30a70c23, 0x3987f998004229a262000, 0x39c966e9d12d8b0fb205f, 0x3a0ad402a0d5500294000, 0x3a86198610c3846401350, 0x3b1132020c5b7faaa6ae0, 0x3bf201008095701008040, 0x3bfdfefc80dfdfeff6ae0, 0x3d9071203d0c51ef240cc, 0x3e82367b2c2e73bf58ccc, 0x3efc0101010bf44910000, 0x3f7d39829b84a00fd9000, 0x3ff0b030acafff0302c8c, 0x3ff7fccccc1f7ffeeeee0, 0x400284440011088466220, 0x400802440011028888000, 0x401232222244923220000, 0x409a10600000470030000, 0x40bd3b90006803a7b0000, 0x40da15604800470330040, 0x40e2e198084069e44c840, 0x42b0c40f306848784bf00, 0x442100044811000ccc820, 0x44212eaaeec40106666c0, 0x46e0d51f2d122ff930000, 0x46f18a44440159622a220, 0x474a1bd94da44116ea2fc, 0x493032210e73980080a73, 0x4ae069100d12600680000, 0x4c6d00444859888a6663c, 0x4f400c00808de08020000, 0x4f400c80808de08c20020, 0x63d1d0002022d0f000000, 0x63ec99e7588cbb0c8cb20, 0x67781060008cfa40c0400, 0x6a0684d9104d098562640, 0x6c22fe25d22d20dc09f20, 0x6d58622989e2da55160d3, 0x801070280840681087840, 0x803bd2b2c41201f375e20, 0x8400200009a4405a00000, 0x8434b4908012170520100, 0x850471790e7368108f873, 0x88410780a806000300340, 0x88750f80ac5e004708f43, 0x88c71084f30974910fe00, 0x8b0c2bf844439407bbf00, 0x8cf8c301210fe94002000, 0x8f830000404f630000000, 0x8f8c0000404fcc0000000, 0x8ffc20f809a4445a08000, 0x925604800004842160200, 0x9312101f68168e84c1040, 0x95a282080e39d4c426273, 0x961240c0020505a9a1040, 0x990403a0081180cee0000, 0x990403a0483180cee8c00, 0x9969776448021a3152040, 0x9c03008ea87f2e00c35d3, 0xc0000900c01000a920900, 0xc0010900c020048680a00, 0xc020c82ad0201022d3e00, 0xc022f6f0d020187970700, 0xc02ff370d0120f5376120, 0xc0f309d6a103c4210fe00, 0xc424c62ed420102d1f200, 0xc6e8f10d190fe34018100, 0xc7f804ee800f41808b500, 0xcb0c00684403900000000, 0xced007e1210b7133b4340, 0x1000100010e00007ff0000, 0x1000102000f000f0001e00, 0x100bff0000000000000000, 0x100bff00000000de000000, 0x100c10e000e00000000000, 0x102000fc10ffff07ffc000, 0x102480c200013c00000000, 0x102480f7cb0b7c2593fe00, 0x1040102400a74802000000, 0x109be2e00000f9a3830100, 0x10c22d2b9010a03f3aba20, 0x10c932af20b748b5485800, 0x10dfffdfffe0002ffffe00, 0x1200003e00406000df0000, 0x1208007e2052cd00df6000, 0x12121c000020240f000000, 0x1212d0002020305a000020, 0x1218f75edf402092dffe00, 0x121e000c2020a500810000, 0x12d200e02020f000c00020, 0x1881c37e00811fc0000000, 0x18893c1e83811e3e61df00, 0x1fe00000001fe000000000, 0x1fe000fc001fe0fffc0000, 0x200e373000201e0f001000, 0x200ef007f4301ec017fd20, 0x2020101c10103000060000, 0x202010d010101800c00000, 0x202c2c1010101e1e000000, 0x206b94d320200996990000, 0x20a41cdfd760f6961f9f40, 0x20cd2e1fc211b7fca5d600, 0x20cfe0d10c10ff5a03b000, 0x20e0e0101010f0f0000000, 0x2446b690b040013d2c2c00, 0x24bd48f6b744fe10313f40, 0x30004470c4400048402c00, 0x30c64b790b402d07d39200, 0x4002000000000000000000, 0x4002008f30fef5cfb1ffff, 0x40437e001f20c000000000, 0x40437e001f20c0fedf0100, 0x41f69c2096096000000000, 0x4202ed803f6042ad60df00, 0x42ff006d4040bd000d0000, 0x8000000000000001700000, 0x8000003180004009708000, 0x902fb2d0dda9fe568d9e00, 0x9057256000a9fe80a80000, 0x906f90020210bf10390100, 0x909cb0615190f2703c0c40, 0x969016f900406940f6bf00, 0x9690760000406900000000, 0xc37e1c8100006100000000, 0xdb7e1cff00006100bfc000, 0xff00000000000000000000, 0xff00000000ff0000000000, 0xff00000000ff00ff000000, 0xff00000000ffff00000000, 0xff000000ff000000000000, 0xffff00000000ff00000000, 0xffff00000000ff00ff0000, 0x1020000fe1001ff00000000, 0x1020102fe10fdff01e3fe00, 0x12022df5800df405c000000, 0x120dd20dedfdf4820d78300, 0x1a9b6018000403f00000000, 0x1a9b6018000403fff3f8000, 0x20002000240f0000df60000, 0x20008dfbffe80c0bcd78000, 0x2004200fe409d420df60000, 0x20048e128cd001200000000, 0x2004ae5adcd301a2affdd00, 0x20081a0420000c0cf3a0000, 0x200fd026fdab0009ff6fe00, 0x21900e2fd26911cc16cbf00, 0x21d00c2d126001c00000000, 0x2400000ec100000007c0000, 0x2400000fcb41000387cfe00, 0x2408000ec100010007c0000, 0x27d00000000000000000000, 0x27d00000080000000000000, 0x2c3107c0004080300000000, 0x2c3107c000408034b0cbc00, 0x34becb41000000000000000, 0x34beef4fc001000009e0000, 0x3ffffff0000000000000000, 0x3ffffff00000000fc000000, 0x40018df160f09bdcbb5ee00, 0x4006600681009bd10080000, 0x48084067000fb48bf000000, 0x48084067000fb48bf030000, 0x60000000000000000000000, 0x6000000e73c40bfffffc1bf, 0x600003dfdfa02000bffdf00, 0x6003fff00000000d0000000, 0x7fffffb0000000000000000, 0x7fffffb00000000f8000200, 0x8000004380003ffc0000000, 0x80007ffcffb03ff3fff0a00, 0x80023ef080020ff9e000000, 0x80023fff81020ffd6120000, 0x8600092419e200000000000, 0x8600092619fbf69b24001ff, 0x87381040000401a00000000, 0x87381040000401a7fbf0000, 0x90049004200f5bf0a4a0000, 0x900bfff26fff5bf42e7af00, 0x90802f70034cb0000000000, 0x90802f70034cb000833df00, 0xc0000000c0000fd00c00000, 0xc0000000c0001ff00000000, 0xc0003ff0fff01ff03ff0000, 0xc0040a30ce300fd023d0000, 0xc00507e0ec340fdbf070b00, 0xc00afbc000040fcb4040000, 0xfffe00000001ee100000000, 0x12001200edfff0000bff1f00, 0x1200edffc000d00010000000, 0x12c01e00c01b002500000000, 0x12c01e12ed1bc025e5db9a00, 0x2000000ec7c020003fef1000, 0x200000100000000000000000, 0x20000010f0001fff00000000, 0x20000fff00000000e0000000, 0x20002c401400930401000000, 0x20002c409840d304fe04fe00, 0x20100043df2800969609bf00, 0x20106bf71c20209609600000, 0x2051f69cbdb6096049f60000, 0x22dfdd007c00fcbfa3dfdf00, 0x23ffdd005c0020bf00000000, 0x24009040f9f0403c502cbf00, 0x2400b0409040003c923c0000, 0x2fffe00000001ee1ef900000, 0x3800070000e0001c00000000, 0x3800070007fc00fc001c0000, 0x39ffd000dc022fd2fffc0000, 0x3fffd00000002fd200000000, 0x400200009a44012000000000, 0x400a00009a44012005a00000, 0x406800872000461800000000, 0x4068008730874e7800003800, 0x40ca219ca5100a4200000000, 0x4200000001a0001c00000000, 0x4200000011e001bc001c0000, 0x423ffefd00c0010200000000, 0x423ffefd00c00102fdce0000, 0x48c78630b600410800000000, 0x48c78670b600410841fe0000, 0x49ca219caf10de4212581800, 0x5e2400800108204000000000, 0x5e2400802109fb6d440001ff, 0x608002000100000000000000, 0x608002000300010000000000, 0x609000420029801400000000, 0x60900042916f803480140000, 0x67f498404e089807b063df00, 0x67f798400808000700000000, 0x700f80a10340000c00000000, 0x700f80a10340000c0030bf00, 0x78df21a70120964800000000, 0x78df21a701209648976afe00, 0x7bff84000000000000000000, 0x7bff840000000000f4000000, 0x804000000000000000000000, 0x8040000080f0001f00000000, 0x840013480000000000000000, 0x8400134809ff48000429fe00, 0x89f7f7ad1008004200000000, 0x89f7f7ad10080042fecb3c00, 0x9020025d4f00fda201f9df00, 0x9020127d070058a200000000, 0x910020040000000000000000, 0x9100200487a17efdcff97eff, 0x9612608d0000000000000000, 0x9612608d00000000600d8000, 0x9e6961000000000000000000, 0x9e6961000000000000009e40, 0xa00010480000000700000000, 0xa00010484efdffffffffffff, 0xc00000000780780000000000, 0xc000000007807800f8000000, 0xce3300700000f60900000000, 0xceb300700000f609717e0000, 0xd05529b200a8560500000000, 0xd0c529b256a87e05fea92100, 0xd2bf030401006cfb00000000, 0xd2bf030401006cfbfffffe00, 0xd2c12e08b97c41c2fffc0000, 0xe00004180000000700000000, 0xe00004181fffffffffffffff, 0xe20005000092004900000000, 0xe20005000df200d900490000, 0xe48348370040b70800000000, 0xe4834b37a440ff1850ffbf00, 0xe4b010070008c43000000000, 0xe4b01007180fe4f800003800, 0xedff10000c20ffffffffc000, 0xf01709e00200040900000000, 0xf01709e0060876092e7f0000, 0xf3630c900000f20d00000000, 0xf3639c906200fe1d10bfbf00, 0xf6c12e08003c41c200000000, 0xf7ef8348000058b700000000, 0xf7ef83484800dcb758fffe00, 0xff0000000000000000000000, 0xff00000000ff000000000000, 0xff00000000ff00ff00000000, 0xffef000000001fff00000000, 0xffef00000c00dffffffffe00, 0xffff00000000ff0000000000, 0xffff00000000ffff00000000, 0xffff100000002fff00000000, 0xff000000000000000000000000, 0x200100000000000000000000000, 0x20010000000f0000d4200000000, 0x3001a20f4df0000000000000000, 0x3001a20f4dffb0024ff00000000, 0x3102210dcef0000000000000000, 0x3102210dcefdf1820ef00000000, 0x800000010000000000000000000, 0x80000001000402012cd00000000, 0xfffd40020080000000000000000, 0xfffd40020080000000029ffde00, 0x8000000000100000000000000000, 0x8000000000100000001000000000, 0xff00000000000000000000000000, 0xff0000000000000000ff00000000, 0xff000000000000ff000000000000, 0x310ac241080400000000000000000, 0x310ac2410804000000000904b0000, 0x8b0c22f0444310000000000000000, 0x8b0c22f0444310684403900000000, 0x102480c20001080000000000000000, 0x102480c2000108c200013c00000000, 0x1fe00000001fe00000000000000000, 0x1fe00000001fe000001fe000000000, 0x4002004081b10e0000000000000000, 0x4002004081b10e00000000304e0000, 0x404b3ebc0900c10000000000000000, 0x404b3ebc0900c1001f20c00120df00, 0x41f69c000209200000000000000000, 0x41f69c000209202096096000000000, 0x969016690040690000000000000000, 0x969016690040690000406900960000, 0xc37e1c810000200000000000000000, 0xc37e1c8100002081000061001e0000, 0xff0000000000000000000000000000, 0xff0000000000000000ff0000000000, 0xff00000000ff000000000000000000, 0xff00000000ff000000ff0000000000, 0xffff00000000000000000000000000, 0xffff0000000000000000ff00000000, 0x1020000000000000000000000000000, 0x102000000000000fe1001ff00000000, 0x2004ae58504301a0000000000000000, 0x2004ae58504301a28cd00121020cf00, 0x21900e26c2491100000000000000000, 0x21900e26c249110d126001c00000000, 0x34becb4100000000000000000000000, 0x34becb4100000001000000000000000, 0x3a9b600760040890000000000000000, 0x3a9b600760040898000403f00c0bf00, 0x600000038c3c1000000000000000000, 0x600000038c3c1000000000000003e40, 0x8100fffdc0020000000000000000000, 0x8100fffdc0020000000000021ffdf00, 0x8600092010c00000000000000000000, 0x8600092010c0000419e200000000000, 0x87383057600408a0000000000000000, 0x87383057600408a0000401a80e5bf00, 0x90804f74200b7080000000000000000, 0x90804f74200b7080034cb003ccb0000, 0xec3107cad0040020000000000000000, 0xec3107cad0040020004080340f9b700, 0xfffe000000010000000000000000000, 0xfffe0000000100000001ee100000000, 0xffffffff80000040000000000000000, 0xffffffff80000040000000007fffc00, 0xffffffffc0000000000000000000000, 0xffffffffc0000000000000003fffe00, 0x12c01e122d01c0040000000000000000, 0x12c01e122d01c004c01b002500c03f00, 0x23ffdd00000000200000000000000000, 0x23ffdd00000000205c0020bf83480000, 0x3800070000e0001c0000000000000000, 0x3800070000e0001c00e0001c00000000, 0x3fffd000000000020000000000000000, 0x3fffd0000000000200002fd200000000, 0x40020000000000000000000000000000, 0x40020000000000009a44012000000000, 0x40680087200000000000000000000000, 0x40680087200000002000461800000000, 0x40ca219c241008020000000000000000, 0x40ca219c24100802a5100a4250af0000, 0x42000000000000000000000000000000, 0x420000000000000001a0001c00000000, 0x48c78630300001080000000000000000, 0x48c7863030000108b600410800000000, 0x4e3ffefdbdc001020000000000000000, 0x4e3ffefdbdc0010200c00102023dfe00, 0x5e240080010000400000000000000000, 0x5e240080010000400108204004920000, 0x60800200010000000000000000000000, 0x60800200010000000100000000000000, 0x60900042000100000000000000000000, 0x60900042000100000029801400000000, 0x67f79840000800020000000000000000, 0x67f798400008000208080007b0420000, 0x748f80a106007a000000000000000000, 0x748f80a106007a000340000cf8000000, 0x78df29b78720de580000000000000000, 0x78df29b78720de580120964878970000, 0x7bff8400000000000000000000000000, 0x84001348000000000000000000000000, 0x8df7ffad760808520000000000000000, 0x8df7ffad760808521008004209b5f600, 0x9020025d080075a20000000000000000, 0x9020025d080075a2070058a2a05f0000, 0x91002004487800020000000000000000, 0x91002004487800020000000030068100, 0xa0001048492200050000000000000000, 0xa00010484922000500000007b0000000, 0xc0000000000000000000000000000000, 0xc0000000000000000780780000000000, 0xce330070000086080000000000000000, 0xce330070000086080000f60900000000, 0xd05529b2008806000000000000000000, 0xd05529b20088060000a85605a9560000, 0xe0000418182000070000000000000000, 0xe00004181820000700000007e0000000, 0xe2000500008000000000000000000000, 0xe2000500008000000092004900000000, 0xe4834837000083080000000000000000, 0xe4834837000083080040b70858b70000, 0xe4b01007000800000000000000000000, 0xe4b01007000800000008c43000000000, 0xf01709e0020004080000000000000000, 0xf01709e00200040802000409f0000000, 0xf2bf13042d40fcfb0000000000000000, 0xf2bf13042d40fcfb01006cfbd2040000, 0xf3630c900000900c0000000000000000, 0xf3630c900000900c0000f20d1df20000, 0xf6c12e08003801000000000000000000, 0xf6c12e0800380100003c41c200000000, 0xf7ffa34808107cb70000000000000000, 0xf7ffa34808107cb7000058b7b7480000, 0xff000000000000000000000000000000, 0xff0000000000000000ff000000000000, 0xff00000000ff00000000000000000000, 0xff00000000ff000000ff000000000000, 0xffff0000000000000000000000000000, 0xffff0000000000000000ff0000000000, 0xffff1000000002000000000000000000, 0xffff10000000020000002ffff0000000, 0xffff20000010ffff0000000000000000, 0xffff20000010ffff00001ffff0000000]

def bMasks (codes auto : Nat) : List Nat :=
  (List.range 15).map fun i =>
    bExpand (distances.getD i 1) (bPool.getD (fld codes 11 (15*auto+i)) 0)

def qCachedValues (initial : List Nat) (table auto i : Nat) : Nat :=
  initial.getD (fld table 3 (initial.length*auto+i)) 0

def qCachedAct (initial : List Nat) (table codes auto : Nat) : Nat → Nat :=
  cachedAction (fun i => initial.getD i 0) (qCachedValues initial table auto)
    initial.length (fun w => qInputLookup w initial) (routeFixed (bMasks codes auto))

def qCachedGood (y group : Nat) (initial : List Nat) (table codes : Nat) : Prop :=
  ∀ a : Fin group, validFixed (bMasks codes a.val) = true ∧
    routeFixed (bMasks codes a.val) y = y ∧
    ∀ i : Fin initial.length,
      qCachedValues initial table a.val i.val =
        routeFixed (bMasks codes a.val) (initial.getD i.val 0)

def qCachedOrient (group : Nat) (initial : List Nat) (table codes : Nat) : List Nat → List Nat :=
  orbitActions qPrefer ((List.range (group-1)).map (fun i => qCachedAct initial table codes (i+1)))

theorem qCachedOrient_run {y s group : Nat} {initial ws : List Nat} {table codes : Nat}
    (h : MonRun y s ws) (hv : qCachedGood y group initial table codes) :
    MonRun y s (qCachedOrient group initial table codes ws) := by
  apply orbitActions_run h qPrefer
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨i,hi,rfl⟩
  have hi : i+1 < group := by have := List.mem_range.1 hi; omega
  obtain ⟨hvalid,hgoal,hcache⟩ := hv ⟨i+1,hi⟩
  have he : qCachedAct initial table codes (i+1) = routeFixed (bMasks codes (i+1)) :=
    cachedAction_function (fun j => initial.getD j 0) (qCachedValues initial table (i+1))
      initial.length (fun w => qInputLookup w initial) (routeFixed (bMasks codes (i+1)))
      (fun j hj => hcache ⟨j,hj⟩)
  rw [he]
  exact routeFixed_run hz _ hvalid hgoal

def G8_N : Nat → Nat
  | 7 => 5
  | 8 => 8
  | 9 => 1
  | _ => 0

def G8_pb : Nat → Nat
  | 6 => 3
  | 7 => 3
  | _ => 0

def G8_records : Nat → Nat
  | 8 => 0x1072c00100043011c00c220
  | 7 => 0xc842d201b80f4c0e9
  | _ => 0

def G8_buckets : Nat → Nat
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def G8_flag : Nat → Nat
  | 7 => 8
  | 8 => 64
  | 9 => 2
  | _ => 0

def G8_seedBits : Nat → Nat
  | 7 => 4
  | 8 => 7
  | 9 => 2
  | _ => 0

def G8_seeds : Nat → Nat
  | 7 => 0x68
  | 8 => 0x1881
  | 9 => 0x2
  | _ => 0

def G8_initial : List Nat := [0x183060c1830603f8001fc07f, 0x2850a142850a0007ffe03f80, 0x50a142850a15fc07f0003f80, 0xa142850a1429fff80000007f, 0x142850a14285000000fffc07f, 0x2850a142850a000000fffff80, 0x3060c183060c1fffff0000000]

def G8_idx : Nat → List Nat → Nat :=
  qIndex G8_N G8_buckets G8_flag G8_seedBits G8_seeds

def G8_benes : Nat := 0x800a61b05822f4600000022e162144190720001004e0460ca2e0b3968000000b30b70a01144f8780aa2481a8ae29883909000000834a68af0701cc4708b10c2946e83c3fe7f8000003fc0d06d8ab0fe22c2a04b1421dc9f9fb3f8000001fa2802284c84a0a81303e8a81bc120d71ad000000d683e1b82a43c88709a268410c60be8a9148000008a4300c511226c440841222cc2b8d025a4680000023433c2b0b20f8214238831582782ea2043e0000021f0b82545307b1181e850074076320f11e1000000f08c907a1d44b08f0821d8568df312734bf8000005fcc40e01541f82c88d05c0d8248430740e40000007201c2103305a0681b88113a350a32344620000023129034c4987112000000000000000000000000000000000000000000

def G8_inputActions : Nat := 0x14e5c4356608c7aa10e74b1568cd19450635c5852dd38455e3029950ce95306e70a1ac688

def G8_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G8_benes auto)

def G8_cacheKeys (i : Nat) : Nat := G8_initial.getD i 0

def G8_cacheValues (auto i : Nat) : Nat :=
  G8_cacheKeys (fld G8_inputActions 3 (7*auto+i))

def G8_act (auto : Nat) : Nat → Nat :=
  cachedAction G8_cacheKeys (G8_cacheValues auto) 7
    (fun w => qInputLookup w G8_initial) (G8_rawAct auto)

def G8_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 4 G8_initial G8_act G8_pb G8_records (9-s) j

def G8_actions : List (Nat → Nat) :=
  (List.range 13).map (fun i => G8_act (i+1))

def G8_ori : List Nat → List Nat := orbitActions qPrefer G8_actions

def G8_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 50, 51, 52, 53, 54, 55]

def G8_rankPool : List Nat := [5532039, 4398508, 6376859, 6306424, 5377213, 1072266, 6564729]

def G8_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 49 G8_S G8_N G8_idx G8_ori G8_coords 4 G8_rankPool s

def G8_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def G8_rows : List Nat := (([25, 38, 49, 50, 70, 73, 76] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 7 ([3, 5, 10, 20, 40, 80, 96] : List Nat)).flatten
def G8_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G8_rows)
theorem G8_nonconstant : ∃ x y : Fin 7 → Bool, G8_f x ≠ G8_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_enc_goal : encL G8_f G8_rows = goal 49 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_proper : ∀ zs ∈ G8_xs.sublists, zs ≠ G8_xs →
    (covUp 49 zs &&& lo 49) ≠ lo 49 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_good :
    qCachedGood (goal 49) 14 G8_initial G8_inputActions G8_benes := by
  unfold qCachedGood
  decide +kernel
theorem G8_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 49) s ws) : MonRun (goal 49) s (G8_ori ws) := by
  change MonRun (goal 49) s (qCachedOrient 14 G8_initial G8_inputActions G8_benes ws)
  exact qCachedOrient_run h G8_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_check_7_0 : span (G8_Z 7) 5 0 = true := by decide +kernel

theorem G8_checked_7 : span (G8_Z 7) 5 0 = true :=
  G8_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_check_8_0 : span (G8_Z 8) 8 0 = true := by decide +kernel

theorem G8_checked_8 : span (G8_Z 8) 8 0 = true :=
  G8_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_check_9_0 : span (G8_Z 9) 1 0 = true := by decide +kernel

theorem G8_checked_9 : span (G8_Z 9) 1 0 = true :=
  G8_check_9_0

theorem G8_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G8_N s, G8_Z s i = true := by
  interval_cases s

  · simp [G8_N]

  · simp [G8_N]

  · simp [G8_N]

  · simp [G8_N]

  · simp [G8_N]

  · simp [G8_N]

  · simp [G8_N]

  · intro i hi
    exact span_ok G8_checked_7 i (Nat.zero_le i) (by simpa [G8_N] using hi)

  · intro i hi
    exact span_ok G8_checked_8 i (Nat.zero_le i) (by simpa [G8_N] using hi)

  · intro i hi
    exact span_ok G8_checked_9 i (Nat.zero_le i) (by simpa [G8_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G8_initial_perm : G8_xs.Perm (G8_S 9 0) := by decide +kernel
theorem G8_no_run : ∀ s ≤ 9, ¬ MonRun (goal 49) s G8_xs := by
  exact noRun_from_barFastOrbit (k := 49) (S := G8_S) (N := G8_N)
    (idx := G8_idx) (ori := G8_ori) (coords := G8_coords)
    (bw := 4) (pool := G8_rankPool) (cap := 9) (i := 0)
    G8_preserved G8_checked (by decide) (by decide) G8_initial_perm
theorem G8_no_small : ¬ HasMonoSize 7 G8_f 9 :=
  encoded_mono_exclusion G8_f G8_nonconstant 9 G8_rows G8_xs 49
    rfl G8_enc_goal G8_proper G8_no_run
theorem G8_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G8_f x) :
    10 ≤ C.size := mono_lower G8_f 9 G8_no_small C hmono hev

end PEqualNP.Outside.L_meta_984.Cert
