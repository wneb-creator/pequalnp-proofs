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

def G0_N : Nat → Nat
  | 4 => 2
  | 5 => 20
  | 6 => 54
  | 7 => 71
  | 8 => 13
  | 9 => 1
  | _ => 0

def G0_pb : Nat → Nat
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 4
  | _ => 0

def G0_records : Nat → Nat
  | 8 => 0x1b84709c0f84b09e0000580201e0041d83f
  | 7 => 0x495e070a1e802d18340268800c4c4785300e826e18182025010d000882c602a000392c52a821304aa88009048b836a172882002d926a81c0260310c0075447004e105ae1090450062500010ba62b092d509b203470ae65e74e2e208c32d00eb09c9228c12a80e8838a12640c8029743d60f540a404a40720984c06a42eb43ca9a680764265
  | 6 => 0x25844102729aa50e20000a4423781ca00c3f81aa43206838e6062948914161c8181822a88181c260648cce07290cca008a929aa01ea82a81908a8258e89639048e81619818f222064482b0a0a0a8c412260709caa41258341e208391496260483426021506022a90c8f01e39448813823078190a194d06f0a16
  | 5 => 0x1094c1c3841540e06c19340cc81e200717298383854424a911f07898845d263e07220705e0c181c682614
  | 4 => 0x3918181
  | _ => 0

def G0_buckets : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 14
  | 7 => 18
  | 8 => 4
  | 9 => 1
  | _ => 0

def G0_flag : Nat → Nat
  | 4 => 4
  | 5 => 2048
  | 6 => 8192
  | 7 => 512
  | 8 => 32
  | 9 => 2
  | _ => 0

def G0_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 12
  | 6 => 14
  | 7 => 10
  | 8 => 6
  | 9 => 2
  | _ => 0

def G0_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x47002c02d002004
  | 6 => 0x131b17002c002004c00600140ac80d801f0a6c008000403c
  | 7 => 0x69206c0022bceb19002050101e247064020881b82802
  | 8 => 0x15e343
  | 9 => 0x2
  | _ => 0

def G0_initial : List Nat := [0xe1c3870e1c3870003f8001fc000, 0x1224489122448901fc000fe0007f, 0x142850a142850afe0007f0003f80, 0x68d1a3468d1a3400000000003fff, 0xa142850a142850000007ffffc000, 0xc183060c183060fffff800000000]

def G0_idx : Nat → List Nat → Nat :=
  qIndex G0_N G0_buckets G0_flag G0_seedBits G0_seeds

def G0_benes : Nat := 0x1d848c7b1281e66a4d400000069c7a1212302d4748d91f04808d9ea3d6390000001c87a48290b20843c6d0e526c418c61ce30200000180316178718ca2263a88611623a76d251d3000000e99da2384006b8ea206404939074288542c000000161098ee1ea0fc8509721033496063286508000002840b0308c31ce4a49280f232488ae15b000000000002b42f4688eb16800000000000000000000000000000000000000000

def G0_inputActions : Nat := 0x284ad112b2858d116395942c65095a22c688

def G0_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G0_benes auto)

def G0_cacheKeys (i : Nat) : Nat := G0_initial.getD i 0

def G0_cacheValues (auto i : Nat) : Nat :=
  G0_cacheKeys (fld G0_inputActions 3 (6*auto+i))

def G0_act (auto : Nat) : Nat → Nat :=
  cachedAction G0_cacheKeys (G0_cacheValues auto) 6
    (fun w => qInputLookup w G0_initial) (G0_rawAct auto)

def G0_S (s j : Nat) : List Nat :=
  qParentAction 9 7 3 0x35d2cceb8f2aa26b1a61651c28818408 8 3 G0_initial G0_act G0_pb G0_records (9-s) j

def G0_actions : List (Nat → Nat) :=
  (List.range 7).map (fun i => G0_act (i+1))

def G0_ori : List Nat → List Nat := orbitActions qPrefer G0_actions

def G0_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 57, 58, 59, 60, 61, 62]

def G0_rankPool : List Nat := [4401547, 7609806, 5275034, 6626216, 7425741, 3174108, 7670697, 5520265, 2112650, 6454168, 2182298, 6303405, 5340570, 7559563, 6650776, 5270922]

def G0_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G0_S G0_N G0_idx G0_ori G0_coords 4 G0_rankPool s

def G0_f (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def G0_rows : List Nat := (([10, 12, 17, 18, 20, 33, 34, 36] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 8 ([3, 5, 9, 6, 24, 40, 48] : List Nat)).flatten
def G0_xs : List Nat :=
  (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
    (fun a => encL a G0_rows)
theorem G0_nonconstant : ∃ x y : Fin 6 → Bool, G0_f x ≠ G0_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_enc_goal : encL G0_f G0_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_proper : ∀ zs ∈ G0_xs.sublists, zs ≠ G0_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_good :
    qCachedGood (goal 56) 8 G0_initial G0_inputActions G0_benes := by
  unfold qCachedGood
  decide +kernel
theorem G0_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G0_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 8 G0_initial G0_inputActions G0_benes ws)
  exact qCachedOrient_run h G0_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_4_0 : span (G0_Z 4) 2 0 = true := by decide +kernel

theorem G0_checked_4 : span (G0_Z 4) 2 0 = true :=
  G0_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_5_0 : span (G0_Z 5) 20 0 = true := by decide +kernel

theorem G0_checked_5 : span (G0_Z 5) 20 0 = true :=
  G0_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_6_0 : span (G0_Z 6) 54 0 = true := by decide +kernel

theorem G0_checked_6 : span (G0_Z 6) 54 0 = true :=
  G0_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_7_0 : span (G0_Z 7) 71 0 = true := by decide +kernel

theorem G0_checked_7 : span (G0_Z 7) 71 0 = true :=
  G0_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_8_0 : span (G0_Z 8) 13 0 = true := by decide +kernel

theorem G0_checked_8 : span (G0_Z 8) 13 0 = true :=
  G0_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_check_9_0 : span (G0_Z 9) 1 0 = true := by decide +kernel

theorem G0_checked_9 : span (G0_Z 9) 1 0 = true :=
  G0_check_9_0

theorem G0_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G0_N s, G0_Z s i = true := by
  interval_cases s

  · simp [G0_N]

  · simp [G0_N]

  · simp [G0_N]

  · simp [G0_N]

  · intro i hi
    exact span_ok G0_checked_4 i (Nat.zero_le i) (by simpa [G0_N] using hi)

  · intro i hi
    exact span_ok G0_checked_5 i (Nat.zero_le i) (by simpa [G0_N] using hi)

  · intro i hi
    exact span_ok G0_checked_6 i (Nat.zero_le i) (by simpa [G0_N] using hi)

  · intro i hi
    exact span_ok G0_checked_7 i (Nat.zero_le i) (by simpa [G0_N] using hi)

  · intro i hi
    exact span_ok G0_checked_8 i (Nat.zero_le i) (by simpa [G0_N] using hi)

  · intro i hi
    exact span_ok G0_checked_9 i (Nat.zero_le i) (by simpa [G0_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G0_initial_perm : G0_xs.Perm (G0_S 9 0) := by decide +kernel
theorem G0_no_run : ∀ s ≤ 9, ¬ MonRun (goal 56) s G0_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G0_S) (N := G0_N)
    (idx := G0_idx) (ori := G0_ori) (coords := G0_coords)
    (bw := 4) (pool := G0_rankPool) (cap := 9) (i := 0)
    G0_preserved G0_checked (by decide) (by decide) G0_initial_perm
theorem G0_no_small : ¬ HasMonoSize 6 G0_f 9 :=
  encoded_mono_exclusion G0_f G0_nonconstant 9 G0_rows G0_xs 56
    rfl G0_enc_goal G0_proper G0_no_run
theorem G0_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = G0_f x) :
    10 ≤ C.size := mono_lower G0_f 9 G0_no_small C hmono hev
def G1_N : Nat → Nat
  | 5 => 8
  | 6 => 22
  | 7 => 36
  | 8 => 18
  | 9 => 1
  | _ => 0

def G1_pb : Nat → Nat
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 5
  | _ => 0

def G1_records : Nat → Nat
  | 8 => 0x500480d100100004c01085c00600200c0600d40440300d802c0d2
  | 7 => 0xd20330095490c409e131129c005e08300307e2f8036521a2200678063f17de06401e118b290181e058fc5d2a38ac0bde05e001078003c009e1b22036001696074e088f05078263c4d4e090f
  | 6 => 0x81d5915d5c5f2889560d18c000d02634275502654279506513094c80d70344e03558104009f54275ac25343461c2734345f
  | 5 => 0x44d280e94076813a50b94c2e98095b8ba8
  | _ => 0

def G1_buckets : Nat → Nat
  | 5 => 2
  | 6 => 6
  | 7 => 9
  | 8 => 5
  | 9 => 1
  | _ => 0

def G1_flag : Nat → Nat
  | 5 => 128
  | 6 => 128
  | 7 => 4096
  | 8 => 256
  | 9 => 2
  | _ => 0

def G1_seedBits : Nat → Nat
  | 5 => 8
  | 6 => 8
  | 7 => 13
  | 8 => 9
  | 9 => 2
  | _ => 0

def G1_seeds : Nat → Nat
  | 5 => 0x8253
  | 6 => 0x80461090149
  | 7 => 0x67562806c018008002000a04868b
  | 8 => 0x77b0520ec1
  | 9 => 0x2
  | _ => 0

def G1_initial : List Nat := [0x1e3c78f1e3c78f1e3c0000003f80000007f, 0x22448912244891224407f01fc000fe03f80, 0x24489122448912244bf80fe0007f01fc000, 0x489122448912244890000fffc00001fff80, 0x50a142850a142850a3fff000007ffe00000, 0x810204081020408100000000007ffffffff, 0x810204081020408103ffffffff800000000]

def G1_idx : Nat → List Nat → Nat :=
  qIndex G1_N G1_buckets G1_flag G1_seedBits G1_seeds

def G1_benes : Nat := 0x534a4981b1e707532fc5f7bef52dc22d26049b53f2694e4c61893a1afb85309e13af8e816cb174c067942aa360ac6dc5516bbd776eed15712bdd832812e699941b08520e8ec5e22c43886c53a25e2c014329b4c69c5682f87db6771862fc5f671f72ee59ca554227d544c51363f5b618f31de3bb5efd163316540aa955aa158ac2dfe5a3c658c718da27f6b8161aa432aa2154277596e96c4e20c3f87ec43a45849d149a874fe9e16630d79e6d6d0da0b40001e72e35909b93825f500bf18e3f7b699031fe3fb66fd958af952cab1352a95eca3db8c95bad756eac946e4b617f28e4de791052f562ae32c0618c2f85ebfb8b56abbd44aae55aa61732c0798552cfd9eb3c001e5ac15c27792e27c55ea9d34381aef83b06e0daece013229e2da9e55800d54cc2a035aec758e71cdad80ac114fa9700000000000000000000000000000000000000000000

def G1_inputActions : Nat := 0xb8a706a5382e45c1aa2e0b8a8c6a5462e4631aa318b9c286ae142e8ca1ac650b9c446ae222e8d11ac688

def G1_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G1_benes auto)

def G1_cacheKeys (i : Nat) : Nat := G1_initial.getD i 0

def G1_cacheValues (auto i : Nat) : Nat :=
  G1_cacheKeys (fld G1_inputActions 3 (7*auto+i))

def G1_act (auto : Nat) : Nat → Nat :=
  cachedAction G1_cacheKeys (G1_cacheValues auto) 7
    (fun w => qInputLookup w G1_initial) (G1_rawAct auto)

def G1_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 4 G1_initial G1_act G1_pb G1_records (9-s) j

def G1_actions : List (Nat → Nat) :=
  (List.range 15).map (fun i => G1_act (i+1))

def G1_ori : List Nat → List Nat := orbitActions qPrefer G1_actions

def G1_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 71, 72, 73, 74, 75]

def G1_rankPool : List Nat := [7708636, 3165914, 6445998, 8417229, 8478159, 2125483, 6651594, 9473755, 6328284, 4227021, 5414844]

def G1_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 70 G1_S G1_N G1_idx G1_ori G1_coords 4 G1_rankPool s

def G1_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def G1_rows : List Nat := (([33, 42, 44, 50, 52, 65, 74, 76, 82, 84] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 10 ([3, 5, 9, 17, 6, 24, 96] : List Nat)).flatten
def G1_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G1_rows)
theorem G1_nonconstant : ∃ x y : Fin 7 → Bool, G1_f x ≠ G1_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_enc_goal : encL G1_f G1_rows = goal 70 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_proper : ∀ zs ∈ G1_xs.sublists, zs ≠ G1_xs →
    (covUp 70 zs &&& lo 70) ≠ lo 70 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_good :
    qCachedGood (goal 70) 16 G1_initial G1_inputActions G1_benes := by
  unfold qCachedGood
  decide +kernel
theorem G1_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 70) s ws) : MonRun (goal 70) s (G1_ori ws) := by
  change MonRun (goal 70) s (qCachedOrient 16 G1_initial G1_inputActions G1_benes ws)
  exact qCachedOrient_run h G1_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_check_5_0 : span (G1_Z 5) 8 0 = true := by decide +kernel

theorem G1_checked_5 : span (G1_Z 5) 8 0 = true :=
  G1_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_check_6_0 : span (G1_Z 6) 22 0 = true := by decide +kernel

theorem G1_checked_6 : span (G1_Z 6) 22 0 = true :=
  G1_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_check_7_0 : span (G1_Z 7) 36 0 = true := by decide +kernel

theorem G1_checked_7 : span (G1_Z 7) 36 0 = true :=
  G1_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_check_8_0 : span (G1_Z 8) 18 0 = true := by decide +kernel

theorem G1_checked_8 : span (G1_Z 8) 18 0 = true :=
  G1_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_check_9_0 : span (G1_Z 9) 1 0 = true := by decide +kernel

theorem G1_checked_9 : span (G1_Z 9) 1 0 = true :=
  G1_check_9_0

theorem G1_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G1_N s, G1_Z s i = true := by
  interval_cases s

  · simp [G1_N]

  · simp [G1_N]

  · simp [G1_N]

  · simp [G1_N]

  · simp [G1_N]

  · intro i hi
    exact span_ok G1_checked_5 i (Nat.zero_le i) (by simpa [G1_N] using hi)

  · intro i hi
    exact span_ok G1_checked_6 i (Nat.zero_le i) (by simpa [G1_N] using hi)

  · intro i hi
    exact span_ok G1_checked_7 i (Nat.zero_le i) (by simpa [G1_N] using hi)

  · intro i hi
    exact span_ok G1_checked_8 i (Nat.zero_le i) (by simpa [G1_N] using hi)

  · intro i hi
    exact span_ok G1_checked_9 i (Nat.zero_le i) (by simpa [G1_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G1_initial_perm : G1_xs.Perm (G1_S 9 0) := by decide +kernel
theorem G1_no_run : ∀ s ≤ 9, ¬ MonRun (goal 70) s G1_xs := by
  exact noRun_from_barFastOrbit (k := 70) (S := G1_S) (N := G1_N)
    (idx := G1_idx) (ori := G1_ori) (coords := G1_coords)
    (bw := 4) (pool := G1_rankPool) (cap := 9) (i := 0)
    G1_preserved G1_checked (by decide) (by decide) G1_initial_perm
theorem G1_no_small : ¬ HasMonoSize 7 G1_f 9 :=
  encoded_mono_exclusion G1_f G1_nonconstant 9 G1_rows G1_xs 70
    rfl G1_enc_goal G1_proper G1_no_run
theorem G1_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G1_f x) :
    10 ≤ C.size := mono_lower G1_f 9 G1_no_small C hmono hev
def G2_N : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 25
  | 7 => 41
  | 8 => 27
  | 9 => 1
  | _ => 0

def G2_pb : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 5
  | _ => 0

def G2_records : Nat → Nat
  | 8 => 0x80a40141c090ac2a0010109b00844270c8310505511e040a0160480304c6c028
  | 7 => 0x4b4555c0fc0d3449ad104869211e803a3284a4cb4b56a4a393e058b056814202b5a07382e803c82e7211412d1abae075a63c03da81ae856a8ec035a95d047b48e80b10ce27345069c0a6824b5
  | 6 => 0x3455c566098a264d0b6229424783264b1156515b69c317a1344021662948314263660755278a0bc31cca97c361ca034c2fc3
  | 5 => 0x25017320b66128c55194b847528ee19d013a9
  | 4 => 0x2760757
  | _ => 0

def G2_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 7
  | 7 => 11
  | 8 => 7
  | 9 => 1
  | _ => 0

def G2_flag : Nat → Nat
  | 4 => 4
  | 5 => 64
  | 6 => 256
  | 7 => 256
  | 8 => 512
  | 9 => 2
  | _ => 0

def G2_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | 9 => 2
  | _ => 0

def G2_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0xc0346
  | 6 => 0x452020105a200205
  | 7 => 0x1712c210fa485004070082001
  | 8 => 0x100c164a0cc0500f
  | 9 => 0x2
  | _ => 0

def G2_initial : List Nat := [0x78f1e3c78f1e3c78001fc0000000000, 0x89122448912244880fe0007f01fc07f, 0x9122448912244897f0003f80fe03f80, 0x10204081020408107ffffc000fffc000, 0x1224489122448912000003fff0003fff, 0x20408102040810207ffffffff0000000, 0x2448912244891224000000000fffffff]

def G2_idx : Nat → List Nat → Nat :=
  qIndex G2_N G2_buckets G2_flag G2_seedBits G2_seeds

def G2_benes : Nat := 0x328824bba1a2e25c827000000138b80ed2d677cc194140e5d90c9983344f00000027865c7116c3b2744df1791fe2e4ab956000000000002ac2d8538fc2f000000000000000000000000000000000000000000

def G2_inputActions : Nat := 0x8f5286b19423d511ac688

def G2_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G2_benes auto)

def G2_cacheKeys (i : Nat) : Nat := G2_initial.getD i 0

def G2_cacheValues (auto i : Nat) : Nat :=
  G2_cacheKeys (fld G2_inputActions 3 (7*auto+i))

def G2_act (auto : Nat) : Nat → Nat :=
  cachedAction G2_cacheKeys (G2_cacheValues auto) 7
    (fun w => qInputLookup w G2_initial) (G2_rawAct auto)

def G2_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 2 G2_initial G2_act G2_pb G2_records (9-s) j

def G2_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G2_act (i+1))

def G2_ori : List Nat → List Nat := orbitActions qPrefer G2_actions

def G2_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 64, 65, 66, 67, 68, 69]

def G2_rankPool : List Nat := [8813978, 6524844, 6303387, 2189981, 6655659, 6442940, 6438345, 6577593, 6381500, 6455196, 6586011]

def G2_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 63 G2_S G2_N G2_idx G2_ori G2_coords 4 G2_rankPool s

def G2_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)
def G2_rows : List Nat := (([26, 28, 50, 52, 74, 76, 97, 98, 100] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 9 ([3, 5, 9, 17, 6, 40, 80] : List Nat)).flatten
def G2_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G2_rows)
theorem G2_nonconstant : ∃ x y : Fin 7 → Bool, G2_f x ≠ G2_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_enc_goal : encL G2_f G2_rows = goal 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_proper : ∀ zs ∈ G2_xs.sublists, zs ≠ G2_xs →
    (covUp 63 zs &&& lo 63) ≠ lo 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_good :
    qCachedGood (goal 63) 4 G2_initial G2_inputActions G2_benes := by
  unfold qCachedGood
  decide +kernel
theorem G2_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 63) s ws) : MonRun (goal 63) s (G2_ori ws) := by
  change MonRun (goal 63) s (qCachedOrient 4 G2_initial G2_inputActions G2_benes ws)
  exact qCachedOrient_run h G2_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_4_0 : span (G2_Z 4) 2 0 = true := by decide +kernel

theorem G2_checked_4 : span (G2_Z 4) 2 0 = true :=
  G2_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_5_0 : span (G2_Z 5) 10 0 = true := by decide +kernel

theorem G2_checked_5 : span (G2_Z 5) 10 0 = true :=
  G2_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_6_0 : span (G2_Z 6) 25 0 = true := by decide +kernel

theorem G2_checked_6 : span (G2_Z 6) 25 0 = true :=
  G2_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_7_0 : span (G2_Z 7) 41 0 = true := by decide +kernel

theorem G2_checked_7 : span (G2_Z 7) 41 0 = true :=
  G2_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_8_0 : span (G2_Z 8) 27 0 = true := by decide +kernel

theorem G2_checked_8 : span (G2_Z 8) 27 0 = true :=
  G2_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_check_9_0 : span (G2_Z 9) 1 0 = true := by decide +kernel

theorem G2_checked_9 : span (G2_Z 9) 1 0 = true :=
  G2_check_9_0

theorem G2_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G2_N s, G2_Z s i = true := by
  interval_cases s

  · simp [G2_N]

  · simp [G2_N]

  · simp [G2_N]

  · simp [G2_N]

  · intro i hi
    exact span_ok G2_checked_4 i (Nat.zero_le i) (by simpa [G2_N] using hi)

  · intro i hi
    exact span_ok G2_checked_5 i (Nat.zero_le i) (by simpa [G2_N] using hi)

  · intro i hi
    exact span_ok G2_checked_6 i (Nat.zero_le i) (by simpa [G2_N] using hi)

  · intro i hi
    exact span_ok G2_checked_7 i (Nat.zero_le i) (by simpa [G2_N] using hi)

  · intro i hi
    exact span_ok G2_checked_8 i (Nat.zero_le i) (by simpa [G2_N] using hi)

  · intro i hi
    exact span_ok G2_checked_9 i (Nat.zero_le i) (by simpa [G2_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G2_initial_perm : G2_xs.Perm (G2_S 9 0) := by decide +kernel
theorem G2_no_run : ∀ s ≤ 9, ¬ MonRun (goal 63) s G2_xs := by
  exact noRun_from_barFastOrbit (k := 63) (S := G2_S) (N := G2_N)
    (idx := G2_idx) (ori := G2_ori) (coords := G2_coords)
    (bw := 4) (pool := G2_rankPool) (cap := 9) (i := 0)
    G2_preserved G2_checked (by decide) (by decide) G2_initial_perm
theorem G2_no_small : ¬ HasMonoSize 7 G2_f 9 :=
  encoded_mono_exclusion G2_f G2_nonconstant 9 G2_rows G2_xs 63
    rfl G2_enc_goal G2_proper G2_no_run
theorem G2_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G2_f x) :
    10 ≤ C.size := mono_lower G2_f 9 G2_no_small C hmono hev
def G3_N : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 23
  | 7 => 45
  | 8 => 31
  | 9 => 1
  | _ => 0

def G3_pb : Nat → Nat
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 5
  | _ => 0

def G3_records : Nat → Nat
  | 8 => 0x6c140c8000b002580a0d0409b5600aa91e4e01188a40e2a0980c121403138140400b30
  | 7 => 0x173569c23d48fd15d450e045496a0eaf8ebe4a71e9d63e50903a82ce001092a1a500a9da303bd132453509af92dd4238ed1a740e9c6a75abc3d024949f44dc25b743c15af1aa133858f137b0adc7a8
  | 6 => 0x11d414b411574c9ed18a3ab21d897b1155cab497d85fb11e623a226598e929b60eb447558e851da34ec2950
  | 5 => 0x2b6529a4acceae4ab389d72a12c0ab0
  | 4 => 0x9d2
  | _ => 0

def G3_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 6
  | 7 => 12
  | 8 => 8
  | 9 => 1
  | _ => 0

def G3_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 512
  | 7 => 8192
  | 8 => 1024
  | 9 => 2
  | _ => 0

def G3_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 10
  | 7 => 14
  | 8 => 11
  | 9 => 2
  | _ => 0

def G3_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x2302001
  | 6 => 0xa1201d3e38606
  | 7 => 0xc92f00004042000e01d04b4001001c01a00a2007
  | 8 => 0x1880e0713781806002802
  | 9 => 0x2
  | _ => 0

def G3_initial : List Nat := [0xe1c3870e1c3870003f800003f80, 0x142850a142850afe0007f01fc07f, 0x3264c993264c9901fc000fe00000, 0x40810204081020fffff8001fff80, 0x48912244891224000007ffe0007f, 0x81020408102040ffffffffe00000, 0xa142850a142850000000001fffff]

def G3_idx : Nat → List Nat → Nat :=
  qIndex G3_N G3_buckets G3_flag G3_seedBits G3_seeds

def G3_benes : Nat := 0x7e9112203c8d91c42c0000001603623c45d1120c400000000000000000000000000000000000000000

def G3_inputActions : Nat := 0x23d415ac688

def G3_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G3_benes auto)

def G3_cacheKeys (i : Nat) : Nat := G3_initial.getD i 0

def G3_cacheValues (auto i : Nat) : Nat :=
  G3_cacheKeys (fld G3_inputActions 3 (7*auto+i))

def G3_act (auto : Nat) : Nat → Nat :=
  cachedAction G3_cacheKeys (G3_cacheValues auto) 7
    (fun w => qInputLookup w G3_initial) (G3_rawAct auto)

def G3_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G3_initial G3_act G3_pb G3_records (9-s) j

def G3_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G3_act (i+1))

def G3_ori : List Nat → List Nat := orbitActions qPrefer G3_actions

def G3_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 57, 58, 59, 60, 61, 62]

def G3_rankPool : List Nat := [7695241, 3165884, 1060250, 5442728, 6576523, 3235468, 3239306, 6650776]

def G3_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G3_S G3_N G3_idx G3_ori G3_coords 4 G3_rankPool s

def G3_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def G3_rows : List Nat := (([28, 49, 52, 74, 76, 97, 98, 100] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 8 ([3, 5, 9, 6, 18, 40, 80] : List Nat)).flatten
def G3_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G3_rows)
theorem G3_nonconstant : ∃ x y : Fin 7 → Bool, G3_f x ≠ G3_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_enc_goal : encL G3_f G3_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_proper : ∀ zs ∈ G3_xs.sublists, zs ≠ G3_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_good :
    qCachedGood (goal 56) 2 G3_initial G3_inputActions G3_benes := by
  unfold qCachedGood
  decide +kernel
theorem G3_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G3_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G3_initial G3_inputActions G3_benes ws)
  exact qCachedOrient_run h G3_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_4_0 : span (G3_Z 4) 1 0 = true := by decide +kernel

theorem G3_checked_4 : span (G3_Z 4) 1 0 = true :=
  G3_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_5_0 : span (G3_Z 5) 9 0 = true := by decide +kernel

theorem G3_checked_5 : span (G3_Z 5) 9 0 = true :=
  G3_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_6_0 : span (G3_Z 6) 23 0 = true := by decide +kernel

theorem G3_checked_6 : span (G3_Z 6) 23 0 = true :=
  G3_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_7_0 : span (G3_Z 7) 45 0 = true := by decide +kernel

theorem G3_checked_7 : span (G3_Z 7) 45 0 = true :=
  G3_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_8_0 : span (G3_Z 8) 31 0 = true := by decide +kernel

theorem G3_checked_8 : span (G3_Z 8) 31 0 = true :=
  G3_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_check_9_0 : span (G3_Z 9) 1 0 = true := by decide +kernel

theorem G3_checked_9 : span (G3_Z 9) 1 0 = true :=
  G3_check_9_0

theorem G3_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G3_N s, G3_Z s i = true := by
  interval_cases s

  · simp [G3_N]

  · simp [G3_N]

  · simp [G3_N]

  · simp [G3_N]

  · intro i hi
    exact span_ok G3_checked_4 i (Nat.zero_le i) (by simpa [G3_N] using hi)

  · intro i hi
    exact span_ok G3_checked_5 i (Nat.zero_le i) (by simpa [G3_N] using hi)

  · intro i hi
    exact span_ok G3_checked_6 i (Nat.zero_le i) (by simpa [G3_N] using hi)

  · intro i hi
    exact span_ok G3_checked_7 i (Nat.zero_le i) (by simpa [G3_N] using hi)

  · intro i hi
    exact span_ok G3_checked_8 i (Nat.zero_le i) (by simpa [G3_N] using hi)

  · intro i hi
    exact span_ok G3_checked_9 i (Nat.zero_le i) (by simpa [G3_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G3_initial_perm : G3_xs.Perm (G3_S 9 0) := by decide +kernel
theorem G3_no_run : ∀ s ≤ 9, ¬ MonRun (goal 56) s G3_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G3_S) (N := G3_N)
    (idx := G3_idx) (ori := G3_ori) (coords := G3_coords)
    (bw := 4) (pool := G3_rankPool) (cap := 9) (i := 0)
    G3_preserved G3_checked (by decide) (by decide) G3_initial_perm
theorem G3_no_small : ¬ HasMonoSize 7 G3_f 9 :=
  encoded_mono_exclusion G3_f G3_nonconstant 9 G3_rows G3_xs 56
    rfl G3_enc_goal G3_proper G3_no_run
theorem G3_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G3_f x) :
    10 ≤ C.size := mono_lower G3_f 9 G3_no_small C hmono hev
def G4_N : Nat → Nat
  | 4 => 2
  | 5 => 18
  | 6 => 51
  | 7 => 79
  | 8 => 44
  | 9 => 1
  | _ => 0

def G4_pb : Nat → Nat
  | 3 => 1
  | 4 => 5
  | 5 => 6
  | 6 => 7
  | 7 => 6
  | _ => 0

def G4_records : Nat → Nat
  | 8 => 0x1817138d80296000ac2a301784808140c8a869981481e03a815e44620900c680200990381026d602c6a07002be1a0a0980c
  | 7 => 0x5d517a6b0d517b6a1997c5078a002ad111b263649558825497ad879b4f2abd1d36c386268a2366ceaa1b5457b6b18984d87690f94a1085a38d5206a8be614cab4c41e80dd89a422f9ba6a61d297eda9db528ead29b268d95168025015e50f52afb7717d36dd74732a8ad4d4c527535715154974aab9b2aa81d4db280d40a794006c3a05369552ab5a5333ab5b56d2b1343a10018
  | 6 => 0x4eb568bf4f040f460e8754a056bd228b4dc64fc10a8b5ebda6934f844e8452934ea54ecb06af17c60004134152be4f260eb54ebf6a9dafc62a9b0ec80e935e8a5da617044e9b60ac5c9d5e995e900e9554ac129b53c65fc65ec0138460ad4f22ab8452995104
  | 5 => 0x13a953652aae1d95736ae6e12ae9da4ba4a7674dc8b99cbab274e4e8cb96d4a00947
  | 4 => 0x4c8c3a7
  | _ => 0

def G4_buckets : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 20
  | 8 => 11
  | 9 => 1
  | _ => 0

def G4_flag : Nat → Nat
  | 4 => 4
  | 5 => 128
  | 6 => 512
  | 7 => 1024
  | 8 => 1024
  | 9 => 2
  | _ => 0

def G4_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 10
  | 7 => 11
  | 8 => 11
  | 9 => 2
  | _ => 0

def G4_seeds : Nat → Nat
  | 4 => 0x1
  | 5 => 0x470d0c8985
  | 6 => 0x1a50380121cac0480200a190181200a33
  | 7 => 0x2e15c0400f86692c3400d39603c1000f002060009740060240301d
  | 8 => 0x14028037fc2ca0a0170ba2c808007
  | 9 => 0x2
  | _ => 0

def G4_initial : List Nat := [0xe1c3870e1c3870003f80000007f, 0x1224489122448901fc000fe03f80, 0x142850a142850afe0007f01fc000, 0x40810204081020fffff8001fffff, 0x68d1a3468d1a34000007ffe00000, 0x81020408102040ffffffffe00000, 0xa142850a142850000000001fffff]

def G4_idx : Nat → List Nat → Nat :=
  qIndex G4_N G4_buckets G4_flag G4_seedBits G4_seeds

def G4_benes : Nat := 0x4c10919c4ac2d8fa1f2000000f9036168620e825400000000000000000000000000000000000000000

def G4_inputActions : Nat := 0x358ca1ac688

def G4_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G4_benes auto)

def G4_cacheKeys (i : Nat) : Nat := G4_initial.getD i 0

def G4_cacheValues (auto i : Nat) : Nat :=
  G4_cacheKeys (fld G4_inputActions 3 (7*auto+i))

def G4_act (auto : Nat) : Nat → Nat :=
  cachedAction G4_cacheKeys (G4_cacheValues auto) 7
    (fun w => qInputLookup w G4_initial) (G4_rawAct auto)

def G4_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G4_initial G4_act G4_pb G4_records (9-s) j

def G4_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G4_act (i+1))

def G4_ori : List Nat → List Nat := orbitActions qPrefer G4_actions

def G4_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 57, 58, 59, 60, 61, 62]

def G4_rankPool : List Nat := [7756171, 4205722, 3239644, 2112425, 5467530, 3165096, 4357852, 3153034, 5537178]

def G4_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G4_S G4_N G4_idx G4_ori G4_coords 4 G4_rankPool s

def G4_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def G4_rows : List Nat := (([49, 50, 52, 74, 76, 97, 98, 100] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 8 ([3, 5, 9, 6, 24, 40, 80] : List Nat)).flatten
def G4_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G4_rows)
theorem G4_nonconstant : ∃ x y : Fin 7 → Bool, G4_f x ≠ G4_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_enc_goal : encL G4_f G4_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_proper : ∀ zs ∈ G4_xs.sublists, zs ≠ G4_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_good :
    qCachedGood (goal 56) 2 G4_initial G4_inputActions G4_benes := by
  unfold qCachedGood
  decide +kernel
theorem G4_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G4_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G4_initial G4_inputActions G4_benes ws)
  exact qCachedOrient_run h G4_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_4_0 : span (G4_Z 4) 2 0 = true := by decide +kernel

theorem G4_checked_4 : span (G4_Z 4) 2 0 = true :=
  G4_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_5_0 : span (G4_Z 5) 18 0 = true := by decide +kernel

theorem G4_checked_5 : span (G4_Z 5) 18 0 = true :=
  G4_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_6_0 : span (G4_Z 6) 51 0 = true := by decide +kernel

theorem G4_checked_6 : span (G4_Z 6) 51 0 = true :=
  G4_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_7_0 : span (G4_Z 7) 79 0 = true := by decide +kernel

theorem G4_checked_7 : span (G4_Z 7) 79 0 = true :=
  G4_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_8_0 : span (G4_Z 8) 44 0 = true := by decide +kernel

theorem G4_checked_8 : span (G4_Z 8) 44 0 = true :=
  G4_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_check_9_0 : span (G4_Z 9) 1 0 = true := by decide +kernel

theorem G4_checked_9 : span (G4_Z 9) 1 0 = true :=
  G4_check_9_0

theorem G4_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G4_N s, G4_Z s i = true := by
  interval_cases s

  · simp [G4_N]

  · simp [G4_N]

  · simp [G4_N]

  · simp [G4_N]

  · intro i hi
    exact span_ok G4_checked_4 i (Nat.zero_le i) (by simpa [G4_N] using hi)

  · intro i hi
    exact span_ok G4_checked_5 i (Nat.zero_le i) (by simpa [G4_N] using hi)

  · intro i hi
    exact span_ok G4_checked_6 i (Nat.zero_le i) (by simpa [G4_N] using hi)

  · intro i hi
    exact span_ok G4_checked_7 i (Nat.zero_le i) (by simpa [G4_N] using hi)

  · intro i hi
    exact span_ok G4_checked_8 i (Nat.zero_le i) (by simpa [G4_N] using hi)

  · intro i hi
    exact span_ok G4_checked_9 i (Nat.zero_le i) (by simpa [G4_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G4_initial_perm : G4_xs.Perm (G4_S 9 0) := by decide +kernel
theorem G4_no_run : ∀ s ≤ 9, ¬ MonRun (goal 56) s G4_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G4_S) (N := G4_N)
    (idx := G4_idx) (ori := G4_ori) (coords := G4_coords)
    (bw := 4) (pool := G4_rankPool) (cap := 9) (i := 0)
    G4_preserved G4_checked (by decide) (by decide) G4_initial_perm
theorem G4_no_small : ¬ HasMonoSize 7 G4_f 9 :=
  encoded_mono_exclusion G4_f G4_nonconstant 9 G4_rows G4_xs 56
    rfl G4_enc_goal G4_proper G4_no_run
theorem G4_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G4_f x) :
    10 ≤ C.size := mono_lower G4_f 9 G4_no_small C hmono hev
def G5_N : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 21
  | 7 => 52
  | 8 => 40
  | 9 => 1
  | _ => 0

def G5_pb : Nat → Nat
  | 4 => 3
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | _ => 0

def G5_records : Nat → Nat
  | 8 => 0x561a00ebe2830038d42c15188386c181a64c012a0c8a4022c09000062f13806008406024100a00a4450320b834
  | 7 => 0x5f3265117eca9d952c0c5196a6b25269487511b290f4f0688c5158aeb4601ec2d191ab0074f5ec09d76bb0555d8ac2253d84cab9970c4d9997acb4e41ac255104aea84617b35f655a6af42a69a9a905b08b60169e1d35b2e0d4f6c857128da21744
  | 6 => 0x2795529555c5a2f2fe24ee35f885f1305460b00d9c4a709712a9ca7897a326a25ea0bdac4d11f4f
  | 5 => 0xaae0e904a65eac4ae4ec1723
  | 4 => 0x4e8
  | _ => 0

def G5_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 13
  | 8 => 10
  | 9 => 1
  | _ => 0

def G5_flag : Nat → Nat
  | 4 => 2
  | 5 => 32
  | 6 => 512
  | 7 => 2048
  | 8 => 1024
  | 9 => 2
  | _ => 0

def G5_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 6
  | 6 => 10
  | 7 => 12
  | 8 => 11
  | 9 => 2
  | _ => 0

def G5_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x481
  | 6 => 0x254c83e0300a01
  | 7 => 0x49605c80e8090731b403000400500101c00e0b8
  | 8 => 0xa020830281d00f0780201e823
  | 9 => 0x2
  | _ => 0

def G5_initial : List Nat := [0xe1c3870e1c3870003f80000007f, 0x1224489122448901fc000fe03f80, 0x142850a142850afe0007f01fc000, 0x2850a142850a14000007ffffff80, 0x60c183060c1830fffff800000000, 0x81020408102040ffffffffe00000, 0xc183060c183060000000001fffff]

def G5_idx : Nat → List Nat → Nat :=
  qIndex G5_N G5_buckets G5_flag G5_seedBits G5_seeds

def G5_benes : Nat := 0x4c10919c4ac2d8fa1f2000000f9036168620e825400000000000000000000000000000000000000000

def G5_inputActions : Nat := 0x358ca1ac688

def G5_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G5_benes auto)

def G5_cacheKeys (i : Nat) : Nat := G5_initial.getD i 0

def G5_cacheValues (auto i : Nat) : Nat :=
  G5_cacheKeys (fld G5_inputActions 3 (7*auto+i))

def G5_act (auto : Nat) : Nat → Nat :=
  cachedAction G5_cacheKeys (G5_cacheValues auto) 7
    (fun w => qInputLookup w G5_initial) (G5_rawAct auto)

def G5_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G5_initial G5_act G5_pb G5_records (9-s) j

def G5_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G5_act (i+1))

def G5_ori : List Nat → List Nat := orbitActions qPrefer G5_actions

def G5_coords : List Nat := [0, 7, 14, 21, 28, 35, 42, 49, 56, 57, 58, 59, 60, 61, 62]

def G5_rankPool : List Nat := [7695241, 1059752, 5258957, 7409068, 5336202, 5405850, 4413835]

def G5_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G5_S G5_N G5_idx G5_ori G5_coords 4 G5_rankPool s

def G5_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def G5_rows : List Nat := (([33, 42, 44, 74, 76, 81, 82, 84] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 8 ([3, 5, 9, 6, 24, 48, 96] : List Nat)).flatten
def G5_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G5_rows)
theorem G5_nonconstant : ∃ x y : Fin 7 → Bool, G5_f x ≠ G5_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_enc_goal : encL G5_f G5_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_proper : ∀ zs ∈ G5_xs.sublists, zs ≠ G5_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_good :
    qCachedGood (goal 56) 2 G5_initial G5_inputActions G5_benes := by
  unfold qCachedGood
  decide +kernel
theorem G5_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G5_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G5_initial G5_inputActions G5_benes ws)
  exact qCachedOrient_run h G5_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_4_0 : span (G5_Z 4) 1 0 = true := by decide +kernel

theorem G5_checked_4 : span (G5_Z 4) 1 0 = true :=
  G5_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_5_0 : span (G5_Z 5) 7 0 = true := by decide +kernel

theorem G5_checked_5 : span (G5_Z 5) 7 0 = true :=
  G5_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_6_0 : span (G5_Z 6) 21 0 = true := by decide +kernel

theorem G5_checked_6 : span (G5_Z 6) 21 0 = true :=
  G5_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_7_0 : span (G5_Z 7) 52 0 = true := by decide +kernel

theorem G5_checked_7 : span (G5_Z 7) 52 0 = true :=
  G5_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_8_0 : span (G5_Z 8) 40 0 = true := by decide +kernel

theorem G5_checked_8 : span (G5_Z 8) 40 0 = true :=
  G5_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_check_9_0 : span (G5_Z 9) 1 0 = true := by decide +kernel

theorem G5_checked_9 : span (G5_Z 9) 1 0 = true :=
  G5_check_9_0

theorem G5_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G5_N s, G5_Z s i = true := by
  interval_cases s

  · simp [G5_N]

  · simp [G5_N]

  · simp [G5_N]

  · simp [G5_N]

  · intro i hi
    exact span_ok G5_checked_4 i (Nat.zero_le i) (by simpa [G5_N] using hi)

  · intro i hi
    exact span_ok G5_checked_5 i (Nat.zero_le i) (by simpa [G5_N] using hi)

  · intro i hi
    exact span_ok G5_checked_6 i (Nat.zero_le i) (by simpa [G5_N] using hi)

  · intro i hi
    exact span_ok G5_checked_7 i (Nat.zero_le i) (by simpa [G5_N] using hi)

  · intro i hi
    exact span_ok G5_checked_8 i (Nat.zero_le i) (by simpa [G5_N] using hi)

  · intro i hi
    exact span_ok G5_checked_9 i (Nat.zero_le i) (by simpa [G5_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G5_initial_perm : G5_xs.Perm (G5_S 9 0) := by decide +kernel
theorem G5_no_run : ∀ s ≤ 9, ¬ MonRun (goal 56) s G5_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G5_S) (N := G5_N)
    (idx := G5_idx) (ori := G5_ori) (coords := G5_coords)
    (bw := 4) (pool := G5_rankPool) (cap := 9) (i := 0)
    G5_preserved G5_checked (by decide) (by decide) G5_initial_perm
theorem G5_no_small : ¬ HasMonoSize 7 G5_f 9 :=
  encoded_mono_exclusion G5_f G5_nonconstant 9 G5_rows G5_xs 56
    rfl G5_enc_goal G5_proper G5_no_run
theorem G5_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G5_f x) :
    10 ≤ C.size := mono_lower G5_f 9 G5_no_small C hmono hev
def G6_N : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 29
  | 8 => 23
  | 9 => 1
  | _ => 0

def G6_pb : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | _ => 0

def G6_records : Nat → Nat
  | 8 => 0xc0100780580540050bc07401804802800b02401700201400007c0800030010c0044
  | 7 => 0x8af025a242bd099685b60b9080d243360c1c9616580b9805d6d32d67d8010b4f8420ab000d021681876c0e340258321a4055e053302500648585560166
  | 6 => 0x33b60de00ed811781a373bdbb0ae4107602b3225cb0ab9846803b0
  | 5 => 0xd501150bd860da0411
  | 4 => 0x68
  | _ => 0

def G6_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 8
  | 8 => 6
  | 9 => 1
  | _ => 0

def G6_flag : Nat → Nat
  | 4 => 2
  | 5 => 16
  | 6 => 256
  | 7 => 64
  | 8 => 1024
  | 9 => 2
  | _ => 0

def G6_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 5
  | 6 => 9
  | 7 => 7
  | 8 => 11
  | 9 => 2
  | _ => 0

def G6_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x152
  | 6 => 0x6c8047a04
  | 7 => 0x38341b70a30d81
  | 8 => 0x700297500b800806
  | 9 => 0x2
  | _ => 0

def G6_initial : List Nat := [0x2040810204081027ffe03fff01fff80, 0x3870e1c3870e1c38001fc000fe0007f, 0x48912244891224480fe0007f0003f80, 0x50a142850a142857f0003f8001fc000, 0x183060c183060c1800000000001fffff, 0x2850a142850a1428000003ffffe00000, 0x3060c183060c18307ffffc0000000000]

def G6_idx : Nat → List Nat → Nat :=
  qIndex G6_N G6_buckets G6_flag G6_seedBits G6_seeds

def G6_benes : Nat := 0x3327a0f99c54968cc61000000000ac9b73da840be14b3986fd1224918032c000001960010895232c588b220538e6d0c9a3929e000000002aa830d9a0f2fc64904175436290ee1d5000000ea8a221a5a4f018534088cb29c02f489c07000000039132383548b0d113e40c5d10e22244a4f0000002788848a96a3b0740001a6374801241dd196000000003a47f4dd1a500067d009f5384930608c20000006100035e000f398f31c68d0c2352b095c17800000000a98003de690c819d2a22ec920bf31461c0000030e2f88f80618e540e7a033948d8a724f000000000004764f5169d729400000000000000000000000000000000000000000

def G6_inputActions : Nat := 0x972645993226a991a54c8ba2646b13225cd11666889ab44695a22e8d11ac688

def G6_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G6_benes auto)

def G6_cacheKeys (i : Nat) : Nat := G6_initial.getD i 0

def G6_cacheValues (auto i : Nat) : Nat :=
  G6_cacheKeys (fld G6_inputActions 3 (7*auto+i))

def G6_act (auto : Nat) : Nat → Nat :=
  cachedAction G6_cacheKeys (G6_cacheValues auto) 7
    (fun w => qInputLookup w G6_initial) (G6_rawAct auto)

def G6_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 4 G6_initial G6_act G6_pb G6_records (9-s) j

def G6_actions : List (Nat → Nat) :=
  (List.range 11).map (fun i => G6_act (i+1))

def G6_ori : List Nat → List Nat := orbitActions qPrefer G6_actions

def G6_coords : List Nat := [0, 7, 14, 21, 28, 42, 49, 56, 63, 64, 66, 67, 68, 69]

def G6_rankPool : List Nat := [5258684, 2103945, 5339800, 4353483]

def G6_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 63 G6_S G6_N G6_idx G6_ori G6_coords 4 G6_rankPool s

def G6_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def G6_rows : List Nat := (([17, 26, 28, 33, 42, 44, 65, 74, 76] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 9 ([3, 5, 9, 6, 48, 80, 96] : List Nat)).flatten
def G6_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G6_rows)
theorem G6_nonconstant : ∃ x y : Fin 7 → Bool, G6_f x ≠ G6_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_enc_goal : encL G6_f G6_rows = goal 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_proper : ∀ zs ∈ G6_xs.sublists, zs ≠ G6_xs →
    (covUp 63 zs &&& lo 63) ≠ lo 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_good :
    qCachedGood (goal 63) 12 G6_initial G6_inputActions G6_benes := by
  unfold qCachedGood
  decide +kernel
theorem G6_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 63) s ws) : MonRun (goal 63) s (G6_ori ws) := by
  change MonRun (goal 63) s (qCachedOrient 12 G6_initial G6_inputActions G6_benes ws)
  exact qCachedOrient_run h G6_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_4_0 : span (G6_Z 4) 1 0 = true := by decide +kernel

theorem G6_checked_4 : span (G6_Z 4) 1 0 = true :=
  G6_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_5_0 : span (G6_Z 5) 5 0 = true := by decide +kernel

theorem G6_checked_5 : span (G6_Z 5) 5 0 = true :=
  G6_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_6_0 : span (G6_Z 6) 13 0 = true := by decide +kernel

theorem G6_checked_6 : span (G6_Z 6) 13 0 = true :=
  G6_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_7_0 : span (G6_Z 7) 29 0 = true := by decide +kernel

theorem G6_checked_7 : span (G6_Z 7) 29 0 = true :=
  G6_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_8_0 : span (G6_Z 8) 23 0 = true := by decide +kernel

theorem G6_checked_8 : span (G6_Z 8) 23 0 = true :=
  G6_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_check_9_0 : span (G6_Z 9) 1 0 = true := by decide +kernel

theorem G6_checked_9 : span (G6_Z 9) 1 0 = true :=
  G6_check_9_0

theorem G6_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G6_N s, G6_Z s i = true := by
  interval_cases s

  · simp [G6_N]

  · simp [G6_N]

  · simp [G6_N]

  · simp [G6_N]

  · intro i hi
    exact span_ok G6_checked_4 i (Nat.zero_le i) (by simpa [G6_N] using hi)

  · intro i hi
    exact span_ok G6_checked_5 i (Nat.zero_le i) (by simpa [G6_N] using hi)

  · intro i hi
    exact span_ok G6_checked_6 i (Nat.zero_le i) (by simpa [G6_N] using hi)

  · intro i hi
    exact span_ok G6_checked_7 i (Nat.zero_le i) (by simpa [G6_N] using hi)

  · intro i hi
    exact span_ok G6_checked_8 i (Nat.zero_le i) (by simpa [G6_N] using hi)

  · intro i hi
    exact span_ok G6_checked_9 i (Nat.zero_le i) (by simpa [G6_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G6_initial_perm : G6_xs.Perm (G6_S 9 0) := by decide +kernel
theorem G6_no_run : ∀ s ≤ 9, ¬ MonRun (goal 63) s G6_xs := by
  exact noRun_from_barFastOrbit (k := 63) (S := G6_S) (N := G6_N)
    (idx := G6_idx) (ori := G6_ori) (coords := G6_coords)
    (bw := 4) (pool := G6_rankPool) (cap := 9) (i := 0)
    G6_preserved G6_checked (by decide) (by decide) G6_initial_perm
theorem G6_no_small : ¬ HasMonoSize 7 G6_f 9 :=
  encoded_mono_exclusion G6_f G6_nonconstant 9 G6_rows G6_xs 63
    rfl G6_enc_goal G6_proper G6_no_run
theorem G6_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G6_f x) :
    10 ≤ C.size := mono_lower G6_f 9 G6_no_small C hmono hev
def G7_N : Nat → Nat
  | 5 => 3
  | 6 => 11
  | 7 => 40
  | 8 => 34
  | 9 => 1
  | _ => 0

def G7_pb : Nat → Nat
  | 4 => 2
  | 5 => 4
  | 6 => 6
  | 7 => 6
  | _ => 0

def G7_records : Nat → Nat
  | 8 => 0x900c22301b004a6008515400d90205050270b0a4161a00cbc4d8903c200e350b86002aa06000
  | 7 => 0x16c0bd1942ce851ae8c4d166a5074b12aeb179324a689a6a41e2c7b007520ec09b269e583455c906d153601745168ca51b5a909600f9261066b0094a6c9c1f2daa32e4a8a9455174c5a651
  | 6 => 0x1d073ce9ce00ecaa5042aa85a0a7ba8d553244544
  | 5 => 0x1d642a69d9
  | _ => 0

def G7_buckets : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 10
  | 8 => 9
  | 9 => 1
  | _ => 0

def G7_flag : Nat → Nat
  | 5 => 4
  | 6 => 256
  | 7 => 2048
  | 8 => 512
  | 9 => 2
  | _ => 0

def G7_seedBits : Nat → Nat
  | 5 => 3
  | 6 => 9
  | 7 => 12
  | 8 => 10
  | 9 => 2
  | _ => 0

def G7_seeds : Nat → Nat
  | 5 => 0x1
  | 6 => 0x318020b
  | 7 => 0x900167414702710300100203500e
  | 8 => 0x3f85801111ff0720b04c02
  | 9 => 0x2
  | _ => 0

def G7_initial : List Nat := [0xe1c3870e1c38701fc07f0000000, 0x12244891224489fe00000fffc07f, 0x244891224489120003f80fe03fff, 0x40810204081020ffffffffe00000, 0x48912244891224000000001fffff, 0x912244891224480003fff0003f80, 0xa142850a142850fffc00001fc000]

def G7_idx : Nat → List Nat → Nat :=
  qIndex G7_N G7_buckets G7_flag G7_seedBits G7_seeds

def G7_benes : Nat := 0x781171b028d272500720000003949a2f08a0d51ac00000000000000000000000000000000000000000

def G7_inputActions : Nat := 0x2e8ca1ac688

def G7_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G7_benes auto)

def G7_cacheKeys (i : Nat) : Nat := G7_initial.getD i 0

def G7_cacheValues (auto i : Nat) : Nat :=
  G7_cacheKeys (fld G7_inputActions 3 (7*auto+i))

def G7_act (auto : Nat) : Nat → Nat :=
  cachedAction G7_cacheKeys (G7_cacheValues auto) 7
    (fun w => qInputLookup w G7_initial) (G7_rawAct auto)

def G7_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G7_initial G7_act G7_pb G7_records (9-s) j

def G7_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G7_act (i+1))

def G7_ori : List Nat → List Nat := orbitActions qPrefer G7_actions

def G7_coords : List Nat := [7, 14, 21, 28, 35, 42, 49, 56, 57, 58, 59, 60, 61, 62]

def G7_rankPool : List Nat := [5401464, 3235194, 4275595, 5262473, 6507143, 1059757, 3239033]

def G7_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G7_S G7_N G7_idx G7_ori G7_coords 4 G7_rankPool s

def G7_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def G7_rows : List Nat := (([14, 28, 42, 70, 81, 84, 97, 98] : List Nat).flatMap fun x => List.replicate 7 x) ++ (List.replicate 8 ([3, 5, 9, 18, 36, 72, 48] : List Nat)).flatten
def G7_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G7_rows)
theorem G7_nonconstant : ∃ x y : Fin 7 → Bool, G7_f x ≠ G7_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_enc_goal : encL G7_f G7_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_proper : ∀ zs ∈ G7_xs.sublists, zs ≠ G7_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_good :
    qCachedGood (goal 56) 2 G7_initial G7_inputActions G7_benes := by
  unfold qCachedGood
  decide +kernel
theorem G7_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G7_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G7_initial G7_inputActions G7_benes ws)
  exact qCachedOrient_run h G7_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_check_5_0 : span (G7_Z 5) 3 0 = true := by decide +kernel

theorem G7_checked_5 : span (G7_Z 5) 3 0 = true :=
  G7_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_check_6_0 : span (G7_Z 6) 11 0 = true := by decide +kernel

theorem G7_checked_6 : span (G7_Z 6) 11 0 = true :=
  G7_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_check_7_0 : span (G7_Z 7) 40 0 = true := by decide +kernel

theorem G7_checked_7 : span (G7_Z 7) 40 0 = true :=
  G7_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_check_8_0 : span (G7_Z 8) 34 0 = true := by decide +kernel

theorem G7_checked_8 : span (G7_Z 8) 34 0 = true :=
  G7_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_check_9_0 : span (G7_Z 9) 1 0 = true := by decide +kernel

theorem G7_checked_9 : span (G7_Z 9) 1 0 = true :=
  G7_check_9_0

theorem G7_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G7_N s, G7_Z s i = true := by
  interval_cases s

  · simp [G7_N]

  · simp [G7_N]

  · simp [G7_N]

  · simp [G7_N]

  · simp [G7_N]

  · intro i hi
    exact span_ok G7_checked_5 i (Nat.zero_le i) (by simpa [G7_N] using hi)

  · intro i hi
    exact span_ok G7_checked_6 i (Nat.zero_le i) (by simpa [G7_N] using hi)

  · intro i hi
    exact span_ok G7_checked_7 i (Nat.zero_le i) (by simpa [G7_N] using hi)

  · intro i hi
    exact span_ok G7_checked_8 i (Nat.zero_le i) (by simpa [G7_N] using hi)

  · intro i hi
    exact span_ok G7_checked_9 i (Nat.zero_le i) (by simpa [G7_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G7_initial_perm : G7_xs.Perm (G7_S 9 0) := by decide +kernel
theorem G7_no_run : ∀ s ≤ 9, ¬ MonRun (goal 56) s G7_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G7_S) (N := G7_N)
    (idx := G7_idx) (ori := G7_ori) (coords := G7_coords)
    (bw := 4) (pool := G7_rankPool) (cap := 9) (i := 0)
    G7_preserved G7_checked (by decide) (by decide) G7_initial_perm
theorem G7_no_small : ¬ HasMonoSize 7 G7_f 9 :=
  encoded_mono_exclusion G7_f G7_nonconstant 9 G7_rows G7_xs 56
    rfl G7_enc_goal G7_proper G7_no_run
theorem G7_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G7_f x) :
    10 ≤ C.size := mono_lower G7_f 9 G7_no_small C hmono hev
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
def G9_N : Nat → Nat
  | 4 => 1
  | 5 => 13
  | 6 => 38
  | 7 => 49
  | 8 => 20
  | 9 => 1
  | _ => 0

def G9_pb : Nat → Nat
  | 4 => 4
  | 5 => 6
  | 6 => 6
  | 7 => 5
  | _ => 0

def G9_records : Nat → Nat
  | 8 => 0x180130a011f81c0a80a400c00e01000d07807400400300101402000009c
  | 7 => 0x21a712d8806960a500261017800683094646a752500068407d783d2d1d9093c04f5d05a704f588fc0115a23e100d882940035023a000d9e8ea0114e01ae045600624ab4001a60184858b8266209f281b588fc810d6026b00b483a8010e401eb0174807044be09728
  | 6 => 0xda00364821671349875344b6400d34975a0094a3056015a8cb4c8459c035ac0e0c0360c161d10c30ad041d8300d47054c49966474c045a8084f09d9c1262c1d4805c701d9f1f4ad1d17054712f8e155a01a0d4764
  | 5 => 0x945025560347415141d548452e03542258e115f4155607418a15c8941
  | 4 => 0x75a
  | _ => 0

def G9_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 10
  | 7 => 13
  | 8 => 5
  | 9 => 1
  | _ => 0

def G9_flag : Nat → Nat
  | 4 => 2
  | 5 => 64
  | 6 => 256
  | 7 => 512
  | 8 => 2048
  | 9 => 2
  | _ => 0

def G9_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 9
  | 7 => 10
  | 8 => 12
  | 9 => 2
  | _ => 0

def G9_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x16040b4
  | 6 => 0xca333380808080382c04cc
  | 7 => 0x1f0d4100140a02038011f40145306801
  | 8 => 0xf28047a3011003
  | 9 => 0x2
  | _ => 0

def G9_initial : List Nat := [0x1010101010ffffffff00, 0x2020202020ffffffff00, 0x3f3f3f3f3f00000000ff, 0x414141414100ff00ff00, 0x4242424242ff00ff0000, 0x84848484840000ffff00, 0x8888888888ffff000000]

def G9_idx : Nat → List Nat → Nat :=
  qIndex G9_N G9_buckets G9_flag G9_seedBits G9_seeds

def G9_benes : Nat := 0x56054000250464bc970000004b8118250000000001f02a0001282325e4b80000025c08c12800000000110150000200202504600000023006090000000000780a800010010128230000001180304800000000042054000090d29011f0000008f8340230000000001d02a000048694808f80000047c1a011800000000100150000903323e47c0000023e0cc08c000000000700a8000481991f23e0000011f066046000000000320000002a0da9492880000094436803000000000150000001506d4a4944000004a21b4018000000000b8000000a002003000000000000060040000000004800000050010018000000000000300200000000030000000000d29152180000090c34000000000000140000000006948a90c000004861a0000000000000b00000000000000000000000000000000000000000000000000000000000000000000000000000000

def G9_inputActions : Nat := 0x72e40b972223b9031dc8873540b9aa223d5031ea88b9c40dce22357103ab888ba340dd1a2358d03ac688

def G9_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G9_benes auto)

def G9_cacheKeys (i : Nat) : Nat := G9_initial.getD i 0

def G9_cacheValues (auto i : Nat) : Nat :=
  G9_cacheKeys (fld G9_inputActions 3 (7*auto+i))

def G9_act (auto : Nat) : Nat → Nat :=
  cachedAction G9_cacheKeys (G9_cacheValues auto) 7
    (fun w => qInputLookup w G9_initial) (G9_rawAct auto)

def G9_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 4 G9_initial G9_act G9_pb G9_records (9-s) j

def G9_actions : List (Nat → Nat) :=
  (List.range 15).map (fun i => G9_act (i+1))

def G9_ori : List Nat → List Nat := orbitActions qPrefer G9_actions

def G9_coords : List Nat := [0, 8, 16, 24, 32, 40, 41, 42, 43, 44, 45, 46, 47]

def G9_rankPool : List Nat := [1059685, 3153016, 4209574, 3278972, 2104214, 4205736, 1064087, 3165061, 2116743, 4392539, 1064103, 4201334, 4205672, 2112599]

def G9_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 40 G9_S G9_N G9_idx G9_ori G9_coords 4 G9_rankPool s

def G9_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)
def G9_rows : List Nat := (([1, 106, 108, 114, 116] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 5 ([3, 5, 9, 17, 33, 65, 6, 24] : List Nat)).flatten
def G9_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G9_rows)
theorem G9_nonconstant : ∃ x y : Fin 7 → Bool, G9_f x ≠ G9_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_enc_goal : encL G9_f G9_rows = goal 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_proper : ∀ zs ∈ G9_xs.sublists, zs ≠ G9_xs →
    (covUp 40 zs &&& lo 40) ≠ lo 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_good :
    qCachedGood (goal 40) 16 G9_initial G9_inputActions G9_benes := by
  unfold qCachedGood
  decide +kernel
theorem G9_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 40) s ws) : MonRun (goal 40) s (G9_ori ws) := by
  change MonRun (goal 40) s (qCachedOrient 16 G9_initial G9_inputActions G9_benes ws)
  exact qCachedOrient_run h G9_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_4_0 : span (G9_Z 4) 1 0 = true := by decide +kernel

theorem G9_checked_4 : span (G9_Z 4) 1 0 = true :=
  G9_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_5_0 : span (G9_Z 5) 13 0 = true := by decide +kernel

theorem G9_checked_5 : span (G9_Z 5) 13 0 = true :=
  G9_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_6_0 : span (G9_Z 6) 38 0 = true := by decide +kernel

theorem G9_checked_6 : span (G9_Z 6) 38 0 = true :=
  G9_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_7_0 : span (G9_Z 7) 49 0 = true := by decide +kernel

theorem G9_checked_7 : span (G9_Z 7) 49 0 = true :=
  G9_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_8_0 : span (G9_Z 8) 20 0 = true := by decide +kernel

theorem G9_checked_8 : span (G9_Z 8) 20 0 = true :=
  G9_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_check_9_0 : span (G9_Z 9) 1 0 = true := by decide +kernel

theorem G9_checked_9 : span (G9_Z 9) 1 0 = true :=
  G9_check_9_0

theorem G9_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G9_N s, G9_Z s i = true := by
  interval_cases s

  · simp [G9_N]

  · simp [G9_N]

  · simp [G9_N]

  · simp [G9_N]

  · intro i hi
    exact span_ok G9_checked_4 i (Nat.zero_le i) (by simpa [G9_N] using hi)

  · intro i hi
    exact span_ok G9_checked_5 i (Nat.zero_le i) (by simpa [G9_N] using hi)

  · intro i hi
    exact span_ok G9_checked_6 i (Nat.zero_le i) (by simpa [G9_N] using hi)

  · intro i hi
    exact span_ok G9_checked_7 i (Nat.zero_le i) (by simpa [G9_N] using hi)

  · intro i hi
    exact span_ok G9_checked_8 i (Nat.zero_le i) (by simpa [G9_N] using hi)

  · intro i hi
    exact span_ok G9_checked_9 i (Nat.zero_le i) (by simpa [G9_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G9_initial_perm : G9_xs.Perm (G9_S 9 0) := by decide +kernel
theorem G9_no_run : ∀ s ≤ 9, ¬ MonRun (goal 40) s G9_xs := by
  exact noRun_from_barFastOrbit (k := 40) (S := G9_S) (N := G9_N)
    (idx := G9_idx) (ori := G9_ori) (coords := G9_coords)
    (bw := 4) (pool := G9_rankPool) (cap := 9) (i := 0)
    G9_preserved G9_checked (by decide) (by decide) G9_initial_perm
theorem G9_no_small : ¬ HasMonoSize 7 G9_f 9 :=
  encoded_mono_exclusion G9_f G9_nonconstant 9 G9_rows G9_xs 40
    rfl G9_enc_goal G9_proper G9_no_run
theorem G9_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G9_f x) :
    10 ≤ C.size := mono_lower G9_f 9 G9_no_small C hmono hev
def G10_N : Nat → Nat
  | 4 => 1
  | 5 => 15
  | 6 => 67
  | 7 => 101
  | 8 => 43
  | 9 => 1
  | _ => 0

def G10_pb : Nat → Nat
  | 4 => 4
  | 5 => 7
  | 6 => 7
  | 7 => 6
  | _ => 0

def G10_records : Nat → Nat
  | 8 => 0x80a80178b048786013802005015020170c27040846a1704e062c360c0a8020c006440593136883b141780c240a0287c
  | 7 => 0xe5112d20b885ab079596972e2c9ae079c3b924d257ab8ca706bc1d134c482c94cd2a55d4298f5616a81f253a605cb17964d685a6095e232a150fc28859513924f704a2026a2739ad68ea408951298272c1ab20532280d948f6a9f5b16af2d45a2926873b12b18cbaba6e22bc535105f14d5e0a9735303c586431316756a6ab85c9178f8d00fa0075b43b8762d3a1875a3ad02da05a2058b14a62f241a607560a804f24ed01d491ec61d787a9094b29b8255824e156a0dc44e254342157
  | 6 => 0xae212a13ab0c2db2eb112e26aa10a920b5f12b01ad80ea096a512d452d5138c0b8c0f8c16de1294068726b0e2cb26cc22db0ae03aac96bc96a30ac3968512d83a8526d106940a8e058c235f39df0ad812970ad496943aa606cd0abc0e9a3eb00aaf12a53ec23cc412851ac50ab023270adb4ce026d43ac90a9d329f0e9426dc26d50ed44c99
  | 5 => 0xe9e92a222ad229c0a9c0e880a8c0aa20aad0a9e12bc228f06880a80268c
  | 4 => 0xd6
  | _ => 0

def G10_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 17
  | 7 => 26
  | 8 => 11
  | 9 => 1
  | _ => 0

def G10_flag : Nat → Nat
  | 4 => 2
  | 5 => 8192
  | 6 => 4096
  | 7 => 2048
  | 8 => 128
  | 9 => 2
  | _ => 0

def G10_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 14
  | 6 => 13
  | 7 => 12
  | 8 => 8
  | 9 => 2
  | _ => 0

def G10_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x15016000e00f
  | 6 => 0x10f35a80b806a0450d5800800400e04b8014002ac7821804400b033
  | 7 => 0x8901843500500306101f0040960060a500102382d1b500107902c06100601d00103600200900b
  | 8 => 0x3610fa50544788f180328
  | 9 => 0x2
  | _ => 0

def G10_initial : List Nat := [0x1010101010ffff00ffff, 0x1f1f1f1f1f0000ff0000, 0x2222222222ffff000000, 0x4040404040ffffff0000, 0x6161616161000000ffff, 0x848484848400ff0000ff, 0x8888888888ff0000ff00]

def G10_idx : Nat → List Nat → Nat :=
  qIndex G10_N G10_buckets G10_flag G10_seedBits G10_seeds

def G10_benes : Nat := 0xa000000098058080000000000001000c0000000000000000000000000000000000000000000000000

def G10_inputActions : Nat := 0x2e8d11ac688

def G10_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G10_benes auto)

def G10_cacheKeys (i : Nat) : Nat := G10_initial.getD i 0

def G10_cacheValues (auto i : Nat) : Nat :=
  G10_cacheKeys (fld G10_inputActions 3 (7*auto+i))

def G10_act (auto : Nat) : Nat → Nat :=
  cachedAction G10_cacheKeys (G10_cacheValues auto) 7
    (fun w => qInputLookup w G10_initial) (G10_rawAct auto)

def G10_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G10_initial G10_act G10_pb G10_records (9-s) j

def G10_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G10_act (i+1))

def G10_ori : List Nat → List Nat := orbitActions qPrefer G10_actions

def G10_coords : List Nat := [0, 8, 16, 24, 32, 40, 41, 42, 43, 45, 47]

def G10_rankPool : List Nat := [4340328, 2181477, 2103943, 4204121, 3221626, 2165336, 2111861, 3279222, 3295879, 4331862]

def G10_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 40 G10_S G10_N G10_idx G10_ori G10_coords 4 G10_rankPool s

def G10_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)
def G10_rows : List Nat := (([42, 50, 65, 108, 116] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 5 ([3, 5, 9, 17, 33, 6, 66, 24] : List Nat)).flatten
def G10_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G10_rows)
theorem G10_nonconstant : ∃ x y : Fin 7 → Bool, G10_f x ≠ G10_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_enc_goal : encL G10_f G10_rows = goal 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_proper : ∀ zs ∈ G10_xs.sublists, zs ≠ G10_xs →
    (covUp 40 zs &&& lo 40) ≠ lo 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_good :
    qCachedGood (goal 40) 2 G10_initial G10_inputActions G10_benes := by
  unfold qCachedGood
  decide +kernel
theorem G10_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 40) s ws) : MonRun (goal 40) s (G10_ori ws) := by
  change MonRun (goal 40) s (qCachedOrient 2 G10_initial G10_inputActions G10_benes ws)
  exact qCachedOrient_run h G10_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_4_0 : span (G10_Z 4) 1 0 = true := by decide +kernel

theorem G10_checked_4 : span (G10_Z 4) 1 0 = true :=
  G10_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_5_0 : span (G10_Z 5) 15 0 = true := by decide +kernel

theorem G10_checked_5 : span (G10_Z 5) 15 0 = true :=
  G10_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_6_0 : span (G10_Z 6) 67 0 = true := by decide +kernel

theorem G10_checked_6 : span (G10_Z 6) 67 0 = true :=
  G10_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_7_0 : span (G10_Z 7) 101 0 = true := by decide +kernel

theorem G10_checked_7 : span (G10_Z 7) 101 0 = true :=
  G10_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_8_0 : span (G10_Z 8) 43 0 = true := by decide +kernel

theorem G10_checked_8 : span (G10_Z 8) 43 0 = true :=
  G10_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_check_9_0 : span (G10_Z 9) 1 0 = true := by decide +kernel

theorem G10_checked_9 : span (G10_Z 9) 1 0 = true :=
  G10_check_9_0

theorem G10_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G10_N s, G10_Z s i = true := by
  interval_cases s

  · simp [G10_N]

  · simp [G10_N]

  · simp [G10_N]

  · simp [G10_N]

  · intro i hi
    exact span_ok G10_checked_4 i (Nat.zero_le i) (by simpa [G10_N] using hi)

  · intro i hi
    exact span_ok G10_checked_5 i (Nat.zero_le i) (by simpa [G10_N] using hi)

  · intro i hi
    exact span_ok G10_checked_6 i (Nat.zero_le i) (by simpa [G10_N] using hi)

  · intro i hi
    exact span_ok G10_checked_7 i (Nat.zero_le i) (by simpa [G10_N] using hi)

  · intro i hi
    exact span_ok G10_checked_8 i (Nat.zero_le i) (by simpa [G10_N] using hi)

  · intro i hi
    exact span_ok G10_checked_9 i (Nat.zero_le i) (by simpa [G10_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G10_initial_perm : G10_xs.Perm (G10_S 9 0) := by decide +kernel
theorem G10_no_run : ∀ s ≤ 9, ¬ MonRun (goal 40) s G10_xs := by
  exact noRun_from_barFastOrbit (k := 40) (S := G10_S) (N := G10_N)
    (idx := G10_idx) (ori := G10_ori) (coords := G10_coords)
    (bw := 4) (pool := G10_rankPool) (cap := 9) (i := 0)
    G10_preserved G10_checked (by decide) (by decide) G10_initial_perm
theorem G10_no_small : ¬ HasMonoSize 7 G10_f 9 :=
  encoded_mono_exclusion G10_f G10_nonconstant 9 G10_rows G10_xs 40
    rfl G10_enc_goal G10_proper G10_no_run
theorem G10_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G10_f x) :
    10 ≤ C.size := mono_lower G10_f 9 G10_no_small C hmono hev
def G11_N : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 110
  | 7 => 227
  | 8 => 193
  | 9 => 23
  | 10 => 1
  | _ => 0

def G11_pb : Nat → Nat
  | 4 => 5
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | 8 => 5
  | _ => 0

def G11_records : Nat → Nat
  | 9 => 0x600700d0550000350590710fd0fc02d86d10100104d86506900203903102f051011
  | 8 => 0x18a00002101cc80bdc228703b3000c01e1001b2c703430231a1c0ab2097301bd21b642263039100c1c3f0c209603f3020500ae18d0d04d100c3108280a2d114a08190404406d148306304013640e320019432883f1e070b0fd102888979008131141865bc154405f603770250429cc2251108b242003e9f81ef06f6018b41be8020b0fc900a2c1b4406f144c8466020a2822431148807200bea002d8283833d80c05168003b78081c1be38cce04fa4813c25e0898f038a1135014642044227a241003f052266071100a1d28de004d0fb782ccb180001e806f45182c046405cd02f6c0f500616030003888203218ec07ef055681fd0135b46070cf7833b829de05e60775481bc1cc606ef03ea008201c1008070732000880dc01f4286d6889a80ed484130fc803b201dd010e003590183407e803110307016b705a201870fca88a403ead82f101b08821128cc0d2d059107d880b9c0713104801b501bce021303f5017bc3f1413ef1146015d84500188103110659897d118804938000583edc06049047c39a83302170002f90679812c21094113887e100bd40dc8
  | 7 => 0x861106766102b0116240553c000320263b1024b0362806e9f04a9e106b01123d0888e0dc58413660fc66106410a08e80f6a80f7a0e4210195802ebd03ea902ebe0b6a80fa4803ebc226730fc2102c57c6697067a88232102f660fc5781e730fc3202f8e106bd03e278962406e3b036a303e4f03057027a8c6ead112a706e110c65c0de2f09e6c06f66c387a06ea70fa570675700e1101e5c0277002f3225ea70008e0023c0fc0702f6e0764d0fc8e0977a4a64d1128121f560e475c56a50fa2d257660e0320fb570e76e0525c00a5cc167144c43010660513c00158000570deb549208c66b60fa881123e06e4d80e8e02e240653c0063c03e67c6eb00feb0c58951122800e4d4a2500e832102130366702ead4a26381ea9912ab0b8a802f21102bd2262702ba803e42460a845eb50138e076118666c0364d06f8e028a80708c036421129a03627c707c11273023320fc431121dc0f43026b50dd580fa1a0364e0b6b500043112bd06e4f04aa50e021112300769f06f680bf7025e4d0faa125e9f0105710249896ad0295803a7804f6602e1ac6e24c6865c683c036a40bfa80a0660678e02758088660fc2d1121a036841029402f5644c6a0fc6a0693c026a80365c036bc0fa4b02abdc1673c76240364541628902638bac0030650fa63c207a00c57c567d0fc56c1603036730de320fca00315802f6a0e47001e67112851127e81e4e036a980e540769d02f4306e5b059570108e902500cea4c605c11271112871122381eb204a3884e5c4a2ab02667c68220262805e11
  | 6 => 0x80ed5c283ac368d04a6e02e31026020263f84ed80003080e62c369002e200daa5c26750673a226170b64002e522c096c26a402e860283f06a310973a8e21b05705c0e900264001e71c66d228ea4a1e900b8c82261609eab0848380e6c0fa98c2ebc80e9c456710fa0106eb10c7a80da0280ed8896310be5f8b25a036170273f02eb602e324167b02ec661e8d0b602022b30fada84e8425eb10b83f04e0002e9d02e5f41e64c26bc8166904a8c02e5c482d62b6460fac5086ce45695036690db3a01bc8057c88669b026c209e9b0daab8666544a48096ab49a2480ebb00eb1c66e18b2864603f03684000c80309640c3ac68960b63f02e660e6450da5f02e3881e17a1e0e85ea4ab2cf21e660fabd0b66780e9d
  | 5 => 0x4172e026b78cc9e13a1843470960184c4505a500f1285e4251c84178c80d5d2b6a003cc02d8686d462b6b68acc017970130d85e3851d5507a384b4a
  | 4 => 0x3c3
  | _ => 0

def G11_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 28
  | 7 => 57
  | 8 => 49
  | 9 => 6
  | 10 => 1
  | _ => 0

def G11_flag : Nat → Nat
  | 4 => 2
  | 5 => 1024
  | 6 => 4096
  | 7 => 8192
  | 8 => 16384
  | 9 => 512
  | 10 => 2
  | _ => 0

def G11_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 11
  | 6 => 13
  | 7 => 14
  | 8 => 15
  | 9 => 10
  | 10 => 2
  | _ => 0

def G11_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x5c3387f0050640c2ee
  | 6 => 0x837008830000a81e2ae81b4001814839407c0b43fe803006603e0028fe01ac09b0bd001804a004000c084016001
  | 7 => 0x457d02c205060a5002000c02fa09f039801b024204b10bc00200645d3001603b06e0008838c0e400f002e003803300f000a004414f01c011b003800180b000b002000d00f0003012000300bc017015000201340090004001000402400600290048004
  | 8 => 0xb0062171d1378222050a0b701e8814380ce025408f005d00cc013408380060022000c0268048000201ec020809a0006002c0080002000600480130002001a003c0098008009c0004000800200a8001000140310028000403b00fb
  | 9 => 0x5ec090281e03d95
  | 10 => 0x2
  | _ => 0

def G11_initial : List Nat := [0x1f1f1f1f1f1f1f1f1f00000000ff00000000, 0x21212121212121212100ff00ff0000ff00ff, 0x222222222222222222ff00ff0000ff00ff00, 0x4444444444444444440000ffff000000ffff, 0x484848484848484848ffff000000ffff0000, 0x808080808080808080ffffffffff00000000, 0x9090909090909090900000000000ffffffff]

def G11_idx : Nat → List Nat → Nat :=
  qIndex G11_N G11_buckets G11_flag G11_seedBits G11_seeds

def G11_benes : Nat := 0x5fabf4003266474a6f45e7bcf49d913260000016e2f45fa0011fb282674aa9352625cc9593800000b7173afd00091e0bdbfc9992f25dbe82cc90000005b8b717e80064f056dee4bc9792edec14648000002dc54a0000032c83970f2864fc9f70a0d8230000000027b000001950702664b80000025c08c35000000001488000000020f5bfc9d93726dbe83a0000000000000000000000000000000000000000000000000000

def G11_inputActions : Nat := 0xd4a706a8b8352a31aa318d5c286b194357111ac688

def G11_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G11_benes auto)

def G11_cacheKeys (i : Nat) : Nat := G11_initial.getD i 0

def G11_cacheValues (auto i : Nat) : Nat :=
  G11_cacheKeys (fld G11_inputActions 3 (7*auto+i))

def G11_act (auto : Nat) : Nat → Nat :=
  cachedAction G11_cacheKeys (G11_cacheValues auto) 7
    (fun w => qInputLookup w G11_initial) (G11_rawAct auto)

def G11_S (s j : Nat) : List Nat :=
  qParentAction 10 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 3 G11_initial G11_act G11_pb G11_records (10-s) j

def G11_actions : List (Nat → Nat) :=
  (List.range 7).map (fun i => G11_act (i+1))

def G11_ori : List Nat → List Nat := orbitActions qPrefer G11_actions

def G11_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 74, 75, 76, 77, 78, 79]

def G11_rankPool : List Nat := [239352137, 272842092, 134398253, 206711086, 136330604, 205798731, 235024751, 272710026, 135281066, 172177769, 137642381, 135479629, 134299051, 136561037, 205764970, 135380395, 272809260, 136560941, 205699370, 205765002, 239254828, 272873866, 172211595, 136593741, 170013007, 241315118, 235023695, 206713166]

def G11_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 72 G11_S G11_N G11_idx G11_ori G11_coords 5 G11_rankPool s

def G11_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def G11_rows : List Nat := (([42, 44, 50, 52, 65, 74, 76, 82, 84] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 9 ([3, 5, 9, 17, 33, 6, 24, 96] : List Nat)).flatten
def G11_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G11_rows)
theorem G11_nonconstant : ∃ x y : Fin 7 → Bool, G11_f x ≠ G11_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_enc_goal : encL G11_f G11_rows = goal 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_proper : ∀ zs ∈ G11_xs.sublists, zs ≠ G11_xs →
    (covUp 72 zs &&& lo 72) ≠ lo 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_good :
    qCachedGood (goal 72) 8 G11_initial G11_inputActions G11_benes := by
  unfold qCachedGood
  decide +kernel
theorem G11_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 72) s ws) : MonRun (goal 72) s (G11_ori ws) := by
  change MonRun (goal 72) s (qCachedOrient 8 G11_initial G11_inputActions G11_benes ws)
  exact qCachedOrient_run h G11_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_4_0 : span (G11_Z 4) 1 0 = true := by decide +kernel

theorem G11_checked_4 : span (G11_Z 4) 1 0 = true :=
  G11_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_5_0 : span (G11_Z 5) 25 0 = true := by decide +kernel

theorem G11_checked_5 : span (G11_Z 5) 25 0 = true :=
  G11_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_6_0 : span (G11_Z 6) 110 0 = true := by decide +kernel

theorem G11_checked_6 : span (G11_Z 6) 110 0 = true :=
  G11_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_7_0 : span (G11_Z 7) 227 0 = true := by decide +kernel

theorem G11_checked_7 : span (G11_Z 7) 227 0 = true :=
  G11_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_8_0 : span (G11_Z 8) 193 0 = true := by decide +kernel

theorem G11_checked_8 : span (G11_Z 8) 193 0 = true :=
  G11_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_9_0 : span (G11_Z 9) 23 0 = true := by decide +kernel

theorem G11_checked_9 : span (G11_Z 9) 23 0 = true :=
  G11_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_check_10_0 : span (G11_Z 10) 1 0 = true := by decide +kernel

theorem G11_checked_10 : span (G11_Z 10) 1 0 = true :=
  G11_check_10_0

theorem G11_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G11_N s, G11_Z s i = true := by
  interval_cases s

  · simp [G11_N]

  · simp [G11_N]

  · simp [G11_N]

  · simp [G11_N]

  · intro i hi
    exact span_ok G11_checked_4 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_5 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_6 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_7 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_8 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_9 i (Nat.zero_le i) (by simpa [G11_N] using hi)

  · intro i hi
    exact span_ok G11_checked_10 i (Nat.zero_le i) (by simpa [G11_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G11_initial_perm : G11_xs.Perm (G11_S 10 0) := by decide +kernel
theorem G11_no_run : ∀ s ≤ 10, ¬ MonRun (goal 72) s G11_xs := by
  exact noRun_from_barFastOrbit (k := 72) (S := G11_S) (N := G11_N)
    (idx := G11_idx) (ori := G11_ori) (coords := G11_coords)
    (bw := 5) (pool := G11_rankPool) (cap := 10) (i := 0)
    G11_preserved G11_checked (by decide) (by decide) G11_initial_perm
theorem G11_no_small : ¬ HasMonoSize 7 G11_f 10 :=
  encoded_mono_exclusion G11_f G11_nonconstant 10 G11_rows G11_xs 72
    rfl G11_enc_goal G11_proper G11_no_run
theorem G11_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G11_f x) :
    11 ≤ C.size := mono_lower G11_f 10 G11_no_small C hmono hev
def G12_N : Nat → Nat
  | 4 => 1
  | 5 => 14
  | 6 => 68
  | 7 => 91
  | 8 => 34
  | 9 => 1
  | _ => 0

def G12_pb : Nat → Nat
  | 4 => 4
  | 5 => 7
  | 6 => 7
  | 7 => 6
  | _ => 0

def G12_records : Nat → Nat
  | 8 => 0x12054300034580503030170bc180801e07c160140b024060011d802518880a006000101d044360d41ec75
  | 7 => 0x45418d5b5ddd118d5360519d15cb17cb21cd26c15d5b6142138d475b1e005dcb47500140b85a059d06001e5c0040000d27581edd139d16490b588d50245f26dd2f4211801d490b5b45492049118b280003600b4220530a00a181274f0f51115417420100150011004581160020000700008051411d001ecd05c12f0099600500394211c10b510554275b51811f4f058000001200130005511ecba354534c47515d4f055026cd30001c5526cb275104001cc0140000c0
  | 6 => 0x7440a2e147423ab251688eaec751e3c81d74c85a684d563a98115011b3c75383aba094e9aa775d3c0b021d4a8f2e04d760ea6615728a544d103ad11d5ba2b44553a0b8211815a2bc72720a8e434f02a080a7223b9516c88a0a7e040e8507420ea25154c0721134a8eb6475063ad61d5802ae1456e399311c10ea34755942a015dc912cc15403acd8b518ea984d2ea3da
  | 5 => 0x7122209c055088a310d4c2286114dcaa9255160ab0095901a2c454e3e99
  | 4 => 0xdb
  | _ => 0

def G12_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 17
  | 7 => 23
  | 8 => 9
  | 9 => 1
  | _ => 0

def G12_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 512
  | 7 => 2048
  | 8 => 128
  | 9 => 2
  | _ => 0

def G12_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 10
  | 7 => 12
  | 8 => 8
  | 9 => 2
  | _ => 0

def G12_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x56030434
  | 6 => 0xc20182e01526244438b007910032080260d3c0a801
  | 7 => 0x4a01e524c03814d06604b0af07e00102a00312301900785b00f00100200280d002089
  | 8 => 0x35031615012384015f
  | 9 => 0x2
  | _ => 0

def G12_initial : List Nat := [0xf0f0f0f0f0000ff0000, 0x1212121212ffff000000, 0x2020202020ffffff0000, 0x4040404040ffffff0000, 0x7171717171000000ffff, 0x848484848400ff0000ff, 0x8888888888ff0000ff00]

def G12_idx : Nat → List Nat → Nat :=
  qIndex G12_N G12_buckets G12_flag G12_seedBits G12_seeds

def G12_benes : Nat := 0x3c0700002601602000000000000040030000000e0140000001300b01000000000000020018000000000e01c00000000000000000000000000000000003800000000000000000000000000000000000000000

def G12_inputActions : Nat := 0xba2645d1a2358991ac688

def G12_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G12_benes auto)

def G12_cacheKeys (i : Nat) : Nat := G12_initial.getD i 0

def G12_cacheValues (auto i : Nat) : Nat :=
  G12_cacheKeys (fld G12_inputActions 3 (7*auto+i))

def G12_act (auto : Nat) : Nat → Nat :=
  cachedAction G12_cacheKeys (G12_cacheValues auto) 7
    (fun w => qInputLookup w G12_initial) (G12_rawAct auto)

def G12_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 2 G12_initial G12_act G12_pb G12_records (9-s) j

def G12_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G12_act (i+1))

def G12_ori : List Nat → List Nat := orbitActions qPrefer G12_actions

def G12_coords : List Nat := [0, 8, 16, 24, 32, 40, 41, 42, 43, 44, 47]

def G12_rankPool : List Nat := [4340344, 2181509, 3155545, 3279222, 2103895, 3295879, 2111861, 4331910, 4204666, 2165368]

def G12_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 40 G12_S G12_N G12_idx G12_ori G12_coords 4 G12_rankPool s

def G12_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)
def G12_rows : List Nat := (([10, 18, 97, 108, 116] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 5 ([3, 5, 9, 17, 6, 34, 66, 24] : List Nat)).flatten
def G12_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G12_rows)
theorem G12_nonconstant : ∃ x y : Fin 7 → Bool, G12_f x ≠ G12_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_enc_goal : encL G12_f G12_rows = goal 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_proper : ∀ zs ∈ G12_xs.sublists, zs ≠ G12_xs →
    (covUp 40 zs &&& lo 40) ≠ lo 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_good :
    qCachedGood (goal 40) 4 G12_initial G12_inputActions G12_benes := by
  unfold qCachedGood
  decide +kernel
theorem G12_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 40) s ws) : MonRun (goal 40) s (G12_ori ws) := by
  change MonRun (goal 40) s (qCachedOrient 4 G12_initial G12_inputActions G12_benes ws)
  exact qCachedOrient_run h G12_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_4_0 : span (G12_Z 4) 1 0 = true := by decide +kernel

theorem G12_checked_4 : span (G12_Z 4) 1 0 = true :=
  G12_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_5_0 : span (G12_Z 5) 14 0 = true := by decide +kernel

theorem G12_checked_5 : span (G12_Z 5) 14 0 = true :=
  G12_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_6_0 : span (G12_Z 6) 68 0 = true := by decide +kernel

theorem G12_checked_6 : span (G12_Z 6) 68 0 = true :=
  G12_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_7_0 : span (G12_Z 7) 91 0 = true := by decide +kernel

theorem G12_checked_7 : span (G12_Z 7) 91 0 = true :=
  G12_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_8_0 : span (G12_Z 8) 34 0 = true := by decide +kernel

theorem G12_checked_8 : span (G12_Z 8) 34 0 = true :=
  G12_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_check_9_0 : span (G12_Z 9) 1 0 = true := by decide +kernel

theorem G12_checked_9 : span (G12_Z 9) 1 0 = true :=
  G12_check_9_0

theorem G12_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G12_N s, G12_Z s i = true := by
  interval_cases s

  · simp [G12_N]

  · simp [G12_N]

  · simp [G12_N]

  · simp [G12_N]

  · intro i hi
    exact span_ok G12_checked_4 i (Nat.zero_le i) (by simpa [G12_N] using hi)

  · intro i hi
    exact span_ok G12_checked_5 i (Nat.zero_le i) (by simpa [G12_N] using hi)

  · intro i hi
    exact span_ok G12_checked_6 i (Nat.zero_le i) (by simpa [G12_N] using hi)

  · intro i hi
    exact span_ok G12_checked_7 i (Nat.zero_le i) (by simpa [G12_N] using hi)

  · intro i hi
    exact span_ok G12_checked_8 i (Nat.zero_le i) (by simpa [G12_N] using hi)

  · intro i hi
    exact span_ok G12_checked_9 i (Nat.zero_le i) (by simpa [G12_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G12_initial_perm : G12_xs.Perm (G12_S 9 0) := by decide +kernel
theorem G12_no_run : ∀ s ≤ 9, ¬ MonRun (goal 40) s G12_xs := by
  exact noRun_from_barFastOrbit (k := 40) (S := G12_S) (N := G12_N)
    (idx := G12_idx) (ori := G12_ori) (coords := G12_coords)
    (bw := 4) (pool := G12_rankPool) (cap := 9) (i := 0)
    G12_preserved G12_checked (by decide) (by decide) G12_initial_perm
theorem G12_no_small : ¬ HasMonoSize 7 G12_f 9 :=
  encoded_mono_exclusion G12_f G12_nonconstant 9 G12_rows G12_xs 40
    rfl G12_enc_goal G12_proper G12_no_run
theorem G12_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G12_f x) :
    10 ≤ C.size := mono_lower G12_f 9 G12_no_small C hmono hev
def G13_N : Nat → Nat
  | 4 => 3
  | 5 => 46
  | 6 => 236
  | 7 => 466
  | 8 => 322
  | 9 => 28
  | 10 => 1
  | _ => 0

def G13_pb : Nat → Nat
  | 3 => 2
  | 4 => 6
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 5
  | _ => 0

def G13_records : Nat → Nat
  | 9 => 0x132008269010023f64a8918c20440a8518c0154328060060c40005d0321302c86981e0b44680d
  | 8 => 0xb0f04af0d2f06070e01201619fb8e12070a89ee0c5400290574022f0c93126584a300149684000f1913480289e107e2040d077b9693032909f509ed22d609a309a90063e27b0c740ae60043109183af0d2381e91b95073411a311a981f6146a0de2006f86110629008f82f48c188bc6030d22f616e7969007f8021900160baf0983020d099002081d7b0a2f10af9887042f0d2601f9004f0aaf12365bfb0b2f141206760c730338052f8c06168602af16a31d3b099889c1098c4dc185f381fb09af0223070007110c2f1464040e05039b8b4df99687850805af000e46d14de10a8716ed04d19b73099b00a31080021545fb01e105f1907311120e6a1082131503fb85119b870e7b4cfb0415996400180ef88d1681e562649787056518238bd40ba34dd98c1b097902a30c9402f11097031102268c1422fb098b0d290be6624a81e605e505a3997b83c20b8f9478020e8c16020192d61dfb0e5b82fb850d09960bf412e50c531c2f16f59b9007278c19002f81f80a01040248159b9a0993098505f483e24ce60e9b00cf0a470cf6048d05f60e7804120bd982d110a304ef23341b8d01d90623166f032f969b0523172f01af01a30c2609e81f94033605a91b88860d070e16830229941b17900cd98b1245f80cf4122f02a90a67628a1088108e098a53f6626a9b920a29042309940a231081098746f182f700c311238cd60bf912f607fb1b9103f3139216af2005147b0408109581f4062f0bed07c21092098f058d108d8c0504f11b990bf50a9201c181f30efb076492920e190b26001b0206000d930e03028e0482c20616057301a68d190989000581c697a31f851723480d05d10400931605d601ef10fb00130cf91fd60323077809841713130d057601e382e20b23
  | 7 => 0x11ca8000b00aca705c500e4250050a05d1b22c4f0221602c0110e7f0b0ec624b302eec03e9d974194dd2b81e6c11c3c02a1605c9985d3e53c33000da09cfb0021611c339748a11d0f57e5f8c0b081c7981e9753cce020eb04d04e24408dcf801e730ae22174ed1746789d158c07c00a168ac671b4f906cf490d0f82d3586070020a30b12e81c2401d1d8b0731105f5ce509041985d3109a1603c6e04c0f82d2a8b4670300281ea38a85b0bca804ca889c5c8301606e4382c07167410a30a110320bcb51bc500981d058701241917c1909897122a296b0a01cfb0ab0a05c47030a102c89060a101a1681e2a1f89d81c2dcdc2d81e341f834166321109c0b8730bc490263201d011654104cf704c470ac3c130ec174290950201d151c21605c2e8cc926243681f23122161130a968d311c0f90c860aceb10ea30960d060a2104b507d280a46d0e48e46d358700e0bd1503e6e1f4c90030a81e1d0a4bc1bb0a81f371646704cea0bcb80b80d1230a8ccff12c336448b123230181603c3c82c47180da1721605d288cc2d0948683d1a10b0a930a203c010c30a03c801100d0ae700521603e7f10ce9164af10e5f2240757e6e01eec8c0110b74103eb081e9d8ace91253e0a4610944104c3f10f3789c670a507098430aea304b0a1d4af018da194e203e8f0980d22511110738bcf81f44f04d1b10c9103cf5840701121601f0101e9c4cea310ed30dcd281ca304eec0bc0a8a10a8cc7f106da16d0f8b0a305d0810cac03e9701cb181cf804e324dc0a0bd3e58ce958c3c01cae1f44510c5f1fcb81660d000d30001601c4902d4089ca38207081e8f03e5f11b0a8466e0985f0ae7c09cb203ea38a0a30950f83d11098348b07681eeb1165f46c980e49601c2c0940d1bc0f11cce0dcf00c4810406e1b4f210eb08b05f969370421617c991946c05c5917437175270a4104dc4204e5f06123166ec05d2303e7c020a18cc50098d30041682d2810c190e4f810e5b10e701fc0f0989d018700ae7f01e7606c641c30a81ecd11ca581e7f81c6705d0401e4306c478ba160aeeb0330a1f52c8bc8c02cd58d0a211a1681eb0020320e40c8cc8a8d05b8b0431bc6702eb205c891b50783c078bc6785cab4dcfd01d0705c92ccca30aa1616c86cdc6703a1604a160bb0a098a217c2404d288307093c500b30a89c1f03e5b8387016473840160081610c41000704dd1581ea20dcd80061610a1603f3701f0a04cab05f231b44483d2a1687f0aeda11cbc8c0d30005f1669c81e5b1f4e70be5f8c0349687c624f18d0b001b0a22c50164a71f4ba11c8682b0a1f50b0bc2d1ba161730a60cf88bc0f04e7602cce8c0950b85b0430a0b21609d1b05e99000750e4408ccb6108ec81e9513032048700a216168738b0a101e3220c4f4d8b00530a0e4a692c198bd3000b0a0c21603b0a8cc4f0230a81e5f0c85b4dc49224ee105348e09709918098ec0946109d2b166730321646d110e53b0e4c1840da05cad0ce7f124e30207f04c2689cb505c4f0e20e16a168b05b82c980b87684d310211d82cc381c7f92c4f0a90a8c09d05c014dcfb174ac89c1a8b06e8507046d0410e9d4dcb513e4309b0a02c460aca30987581e7516c0f03ed381ed304cb8
  | 6 => 0x105cf1659d1657403d288ad291067b8bcc901cd745ccf165ab03f6883c8d09c7309dcf018bd8bd82841698bc2d03ceb0015645c181bd5e09dbf0167b01d2251d3103c951bcf904c580bebd84c4d11c8145c8b10c641fda217db481c2403c5d0181610994096de1144f8bdb48bc35094518bc6411cb21f49203c6201d6b0a07b0b5a901dc701cca8b15681cc60948981d5903d1509ccd8313b1c5768cc5583c4d8bd0b02f3b8310106d5e8bd718bce04be1445d8c81d711b4ac10d1b03c388b07cccc968bcbf1fc4cc5c4d17d2501dd104d951652d8bd6b03c18c5cef0390104cf18bcc00acc30adc71648e025780ad171fc5704d7509f69019940ad2281cc98bcc411c6701d0616cec8ad1c8419401d5056f56ccc85115a952ccd8bc050ac968ace010cc901c0e82101041568bd6e0ad100c07b04c9d84cbf1f4da0d2bd8bcd70ad2703f2856c9e02c440201456e7c04c8102d2410ccc0ac6c09c958ad990945d1644403d5689c4610d2516c8106c9d8bc33cccdd81d458a07106c3281c0582ccf8301681d1c840bd0acca8bcab10db409527108fe03c6c84d7281d828ad350cdc75f57606d15094eb8a0141b8bd0acaf01cdf8ccaf8bcc381cc384ce184cef81d0401d1703db4c5ce189cd616523025291659a0ac620add110c5a89ced1bdb203d290a8de8cc6c10c1709e148cd0403daf8bd598413b10d3e909690ac0e04d8c0453a81c2d1651805d98094de03f561107c0ad6e8bc62cbd5303da310cb91656116d4d01c1403d4410cc002c9d81d7ec5c5a0987c09d3a8bce8095430d45613d5e0407109c148cd2a1f46f8bc85
  | 5 => 0x2b148164909d1005928001680f2d44da815b9807054264902c1f07ad0411500ea583c9320a002616e262e095860785e0b4988e8b09c2e15b205b3f0b66604d44158942b0501e7e09c0d1392e2759c5e4001c96979802571016d403c4a0482429308164209d8805a20277081e66
  | 4 => 0x4e24073a03aa
  | _ => 0

def G13_buckets : Nat → Nat
  | 4 => 1
  | 5 => 12
  | 6 => 59
  | 7 => 117
  | 8 => 81
  | 9 => 7
  | 10 => 1
  | _ => 0

def G13_flag : Nat → Nat
  | 4 => 4
  | 5 => 2048
  | 6 => 2048
  | 7 => 8192
  | 8 => 4096
  | 9 => 128
  | 10 => 2
  | _ => 0

def G13_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 12
  | 6 => 12
  | 7 => 14
  | 8 => 13
  | 9 => 8
  | 10 => 2
  | _ => 0

def G13_seeds : Nat → Nat
  | 4 => 0x3
  | 5 => 0x202a00b60800a00200f00603a00a00506b
  | 6 => 0x1004b00102000569200203d8c200500a00600808910016901d6c20d50223192050ba0040010121d200311b00103800220207805a01f13006a00386700108c0348551840a10c500700a01901000302f02f0c90170a300184e
  | 7 => 0x7403c000f00b61b3009c001001022686a08d4137c00200040ec00700010040001016c08d0194007019002f0034006009917300bc00a011466c019c003031004a002a1930070df9000a16f00600e40028005006c02310d21640b56151003808805e800317582b5010400a00f800800c001a003c008032002b0d6405c025009c000416305fe115004800203b0147004400a874803100040e4000800b0088013844400f000602c020202a00080bc008c00100080370014026002c00401bc08b0314004020800302ac00b006c002
  | 8 => 0x13f89480096e30e3103c2ec00400807000042ca03b00780340b601c0090cc400828601d42ac3f41b2002814c019085113023813402c001813c00a0138a108440061bf01c450809a00b029814000914200700060882088a1002813804881b408027e0320d880040f601c00080bc018109071823001d00e00b84b000203000b803000200b
  | 9 => 0x2323042220164c
  | 10 => 0x2
  | _ => 0

def G13_initial : List Nat := [0xf0f0f0f0f0f0f0000ff00000000, 0x20202020202020ffffff0000ffff, 0x31313131313131000000ffff0000, 0x40404040404040ffffffffff0000, 0x525252525252520000000000ffff, 0x8484848484848400ff0000ff00ff, 0x88888888888888ff0000ff00ff00]

def G13_idx : Nat → List Nat → Nat :=
  qIndex G13_N G13_buckets G13_flag G13_seedBits G13_seeds

def G13_benes : Nat := 0x21c3f8001350144b8970000004b8000080000007f1021fc0000006e47c8f80000047c198000000003f8690000004dc3812e25c0000012e0461a80000000000000000000000000000000000000000000000000

def G13_inputActions : Nat := 0xb918c6a8c62e8d11ac688

def G13_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G13_benes auto)

def G13_cacheKeys (i : Nat) : Nat := G13_initial.getD i 0

def G13_cacheValues (auto i : Nat) : Nat :=
  G13_cacheKeys (fld G13_inputActions 3 (7*auto+i))

def G13_act (auto : Nat) : Nat → Nat :=
  cachedAction G13_cacheKeys (G13_cacheValues auto) 7
    (fun w => qInputLookup w G13_initial) (G13_rawAct auto)

def G13_S (s j : Nat) : List Nat :=
  qParentAction 10 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 2 G13_initial G13_act G13_pb G13_records (10-s) j

def G13_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G13_act (i+1))

def G13_ori : List Nat → List Nat := orbitActions qPrefer G13_actions

def G13_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63]

def G13_rankPool : List Nat := [6577818, 2115707, 4287912, 4341369, 1067678, 4402810, 2121163, 4418727, 4349079, 4263562, 4202121, 4205464, 3239371, 5458590, 4328327, 4397991, 4218264, 3295902, 4275064, 4397959, 4205432]

def G13_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G13_S G13_N G13_idx G13_ori G13_coords 4 G13_rankPool s

def G13_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def G13_rows : List Nat := (([44, 52, 74, 82, 97, 104, 112] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 7 ([3, 5, 9, 17, 6, 34, 68, 24] : List Nat)).flatten
def G13_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G13_rows)
theorem G13_nonconstant : ∃ x y : Fin 7 → Bool, G13_f x ≠ G13_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_enc_goal : encL G13_f G13_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_proper : ∀ zs ∈ G13_xs.sublists, zs ≠ G13_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_good :
    qCachedGood (goal 56) 4 G13_initial G13_inputActions G13_benes := by
  unfold qCachedGood
  decide +kernel
theorem G13_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G13_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 4 G13_initial G13_inputActions G13_benes ws)
  exact qCachedOrient_run h G13_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_4_0 : span (G13_Z 4) 3 0 = true := by decide +kernel

theorem G13_checked_4 : span (G13_Z 4) 3 0 = true :=
  G13_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_5_0 : span (G13_Z 5) 46 0 = true := by decide +kernel

theorem G13_checked_5 : span (G13_Z 5) 46 0 = true :=
  G13_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_6_0 : span (G13_Z 6) 236 0 = true := by decide +kernel

theorem G13_checked_6 : span (G13_Z 6) 236 0 = true :=
  G13_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_7_0 : span (G13_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_7_256 : span (G13_Z 7) 210 256 = true := by decide +kernel

theorem G13_checked_7 : span (G13_Z 7) 466 0 = true :=
  (@span_join (G13_Z 7) 256 0 210 G13_check_7_0 G13_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_8_0 : span (G13_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_8_256 : span (G13_Z 8) 66 256 = true := by decide +kernel

theorem G13_checked_8 : span (G13_Z 8) 322 0 = true :=
  (@span_join (G13_Z 8) 256 0 66 G13_check_8_0 G13_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_9_0 : span (G13_Z 9) 28 0 = true := by decide +kernel

theorem G13_checked_9 : span (G13_Z 9) 28 0 = true :=
  G13_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_check_10_0 : span (G13_Z 10) 1 0 = true := by decide +kernel

theorem G13_checked_10 : span (G13_Z 10) 1 0 = true :=
  G13_check_10_0

theorem G13_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G13_N s, G13_Z s i = true := by
  interval_cases s

  · simp [G13_N]

  · simp [G13_N]

  · simp [G13_N]

  · simp [G13_N]

  · intro i hi
    exact span_ok G13_checked_4 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_5 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_6 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_7 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_8 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_9 i (Nat.zero_le i) (by simpa [G13_N] using hi)

  · intro i hi
    exact span_ok G13_checked_10 i (Nat.zero_le i) (by simpa [G13_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G13_initial_perm : G13_xs.Perm (G13_S 10 0) := by decide +kernel
theorem G13_no_run : ∀ s ≤ 10, ¬ MonRun (goal 56) s G13_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G13_S) (N := G13_N)
    (idx := G13_idx) (ori := G13_ori) (coords := G13_coords)
    (bw := 4) (pool := G13_rankPool) (cap := 10) (i := 0)
    G13_preserved G13_checked (by decide) (by decide) G13_initial_perm
theorem G13_no_small : ¬ HasMonoSize 7 G13_f 10 :=
  encoded_mono_exclusion G13_f G13_nonconstant 10 G13_rows G13_xs 56
    rfl G13_enc_goal G13_proper G13_no_run
theorem G13_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G13_f x) :
    11 ≤ C.size := mono_lower G13_f 10 G13_no_small C hmono hev
def G14_N : Nat → Nat
  | 5 => 4
  | 6 => 27
  | 7 => 53
  | 8 => 30
  | 9 => 1
  | _ => 0

def G14_pb : Nat → Nat
  | 4 => 2
  | 5 => 5
  | 6 => 6
  | 7 => 5
  | _ => 0

def G14_records : Nat → Nat
  | 8 => 0xa0020e152d0780606002004411320733a580280401ac28d1608210b04826080c8ac
  | 7 => 0x28af39a28f00b21a703c882af23246bb328e2b00bc07b75fa62d0a68cf3d16ecfd069263b740e68b058a86b72b262bb43428d08ed52af39a64b739d11d016dc1a32e8cda30b2522a42beea71eeca224f25a6844c63bb8a891afbe90eb7
  | 6 => 0x125005b0d1688ae145c28b49f52b2d2456e2b305590b3c25c97a31569abd4c585a2543aa42e145648cf45404ee455c91acaf72
  | 5 => 0x12a82b622d84a7
  | _ => 0

def G14_buckets : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 14
  | 8 => 8
  | 9 => 1
  | _ => 0

def G14_flag : Nat → Nat
  | 5 => 8
  | 6 => 4096
  | 7 => 512
  | 8 => 128
  | 9 => 2
  | _ => 0

def G14_seedBits : Nat → Nat
  | 5 => 4
  | 6 => 13
  | 7 => 10
  | 8 => 8
  | 9 => 2
  | _ => 0

def G14_seeds : Nat → Nat
  | 5 => 0x7
  | 6 => 0x2758004043006801000201b
  | 7 => 0x149f82c2803805008374d8050c0768d481
  | 8 => 0x2111910249060c23
  | 9 => 0x2
  | _ => 0

def G14_initial : List Nat := [0xf0f0f0f0f00ff000000, 0x1212121212ff0000ff00, 0x2020202020ffff00ff00, 0x31313131310000ff00ff, 0x4848484848ff00ff0000, 0x8080808080ffffff0000, 0xc4c4c4c4c4000000ffff]

def G14_idx : Nat → List Nat → Nat :=
  qIndex G14_N G14_buckets G14_flag G14_seedBits G14_seeds

def G14_benes : Nat := 0x2b00002400800000000000000000040000000000000000000000000000000000000000000000000

def G14_inputActions : Nat := 0x1a3ac1ac688

def G14_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G14_benes auto)

def G14_cacheKeys (i : Nat) : Nat := G14_initial.getD i 0

def G14_cacheValues (auto i : Nat) : Nat :=
  G14_cacheKeys (fld G14_inputActions 3 (7*auto+i))

def G14_act (auto : Nat) : Nat → Nat :=
  cachedAction G14_cacheKeys (G14_cacheValues auto) 7
    (fun w => qInputLookup w G14_initial) (G14_rawAct auto)

def G14_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G14_initial G14_act G14_pb G14_records (9-s) j

def G14_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G14_act (i+1))

def G14_ori : List Nat → List Nat := orbitActions qPrefer G14_actions

def G14_coords : List Nat := [0, 8, 16, 24, 32, 40, 41, 42, 43, 44, 45, 46, 47]

def G14_rankPool : List Nat := [3295589, 3230567, 2111611, 1063529, 3279704, 4397928, 3157079, 4401494, 3152229, 3213654]

def G14_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 40 G14_S G14_N G14_idx G14_ori G14_coords 4 G14_rankPool s

def G14_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)
def G14_rows : List Nat := (([10, 44, 82, 97, 116] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 5 ([3, 5, 9, 17, 6, 34, 24, 72] : List Nat)).flatten
def G14_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G14_rows)
theorem G14_nonconstant : ∃ x y : Fin 7 → Bool, G14_f x ≠ G14_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_enc_goal : encL G14_f G14_rows = goal 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_proper : ∀ zs ∈ G14_xs.sublists, zs ≠ G14_xs →
    (covUp 40 zs &&& lo 40) ≠ lo 40 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_good :
    qCachedGood (goal 40) 2 G14_initial G14_inputActions G14_benes := by
  unfold qCachedGood
  decide +kernel
theorem G14_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 40) s ws) : MonRun (goal 40) s (G14_ori ws) := by
  change MonRun (goal 40) s (qCachedOrient 2 G14_initial G14_inputActions G14_benes ws)
  exact qCachedOrient_run h G14_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_check_5_0 : span (G14_Z 5) 4 0 = true := by decide +kernel

theorem G14_checked_5 : span (G14_Z 5) 4 0 = true :=
  G14_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_check_6_0 : span (G14_Z 6) 27 0 = true := by decide +kernel

theorem G14_checked_6 : span (G14_Z 6) 27 0 = true :=
  G14_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_check_7_0 : span (G14_Z 7) 53 0 = true := by decide +kernel

theorem G14_checked_7 : span (G14_Z 7) 53 0 = true :=
  G14_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_check_8_0 : span (G14_Z 8) 30 0 = true := by decide +kernel

theorem G14_checked_8 : span (G14_Z 8) 30 0 = true :=
  G14_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_check_9_0 : span (G14_Z 9) 1 0 = true := by decide +kernel

theorem G14_checked_9 : span (G14_Z 9) 1 0 = true :=
  G14_check_9_0

theorem G14_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G14_N s, G14_Z s i = true := by
  interval_cases s

  · simp [G14_N]

  · simp [G14_N]

  · simp [G14_N]

  · simp [G14_N]

  · simp [G14_N]

  · intro i hi
    exact span_ok G14_checked_5 i (Nat.zero_le i) (by simpa [G14_N] using hi)

  · intro i hi
    exact span_ok G14_checked_6 i (Nat.zero_le i) (by simpa [G14_N] using hi)

  · intro i hi
    exact span_ok G14_checked_7 i (Nat.zero_le i) (by simpa [G14_N] using hi)

  · intro i hi
    exact span_ok G14_checked_8 i (Nat.zero_le i) (by simpa [G14_N] using hi)

  · intro i hi
    exact span_ok G14_checked_9 i (Nat.zero_le i) (by simpa [G14_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G14_initial_perm : G14_xs.Perm (G14_S 9 0) := by decide +kernel
theorem G14_no_run : ∀ s ≤ 9, ¬ MonRun (goal 40) s G14_xs := by
  exact noRun_from_barFastOrbit (k := 40) (S := G14_S) (N := G14_N)
    (idx := G14_idx) (ori := G14_ori) (coords := G14_coords)
    (bw := 4) (pool := G14_rankPool) (cap := 9) (i := 0)
    G14_preserved G14_checked (by decide) (by decide) G14_initial_perm
theorem G14_no_small : ¬ HasMonoSize 7 G14_f 9 :=
  encoded_mono_exclusion G14_f G14_nonconstant 9 G14_rows G14_xs 40
    rfl G14_enc_goal G14_proper G14_no_run
theorem G14_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G14_f x) :
    10 ≤ C.size := mono_lower G14_f 9 G14_no_small C hmono hev
def G15_N : Nat → Nat
  | 4 => 1
  | 5 => 40
  | 6 => 222
  | 7 => 488
  | 8 => 406
  | 9 => 41
  | 10 => 1
  | _ => 0

def G15_pb : Nat → Nat
  | 4 => 6
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 6
  | _ => 0

def G15_records : Nat → Nat
  | 9 => 0x9c1c2a140142601910d44201c185c4808160740000d58d318110041c021e10ca40c120686016040c850461a1b001
  | 8 => 0x1253aca71f4c624d40a33a617211e1166588a8553c4fa16d4078f71a72f8db7389c947c35648740e9d442c05a68c06b85e17107450ce92b8613ba01507e838e1dd083f742e822a01b480098fe1a38a9348485d7d4128b0e2848506c8239a0b983a645d01d8f0faaab2e4aead681bc8574936585df6b3d2590345079d0ed01851a869a99572a9209a4f365933283f711e18f64493297185d30bd40a2eaa4c3f1ac141fbe8a5075085430b064b2d4e783cc2ec06a9ce4780281d0436091a1e9606cce271d20a00d426d0db665ec2bcb22861330de50f9d0b8e1249b41344d3791ca987ec0c0d341a66481c20b84474a1ea020a0f501baa35907f2228842a8007864f1de84bbad368066b69b43106e49c63999e498cae48bd2ee5a13b802515c8f299ddb41f1558a2d8113b52f30f06989e06283a6cda91dd20b863740286a19341347f2c6aedd9a3788470cd5338611b32ae741ee07c90796ae7950a2b901b403e677470ba543028a4da7331991f981a3d5ce0fcb7198868828a2b9f714286955c39b9917ce3e912501aa10ac806501e92acf2f40ae31c532dcbbb3234347068fe3471e105da60b6ce07aabda064455520b922f803f41ec64b32305068a0d9d0bc82c509d42b803340d3789e336da49021f1db40a38b71902e88e6323a85bd086787ae941405aa8c51a6683df453caea01e4adca2d1c1d411cf0ddd222e87510e6a10d43c08664f0a0dc56c1a8b181c921843b50722c5a817d4001664342a833994704b2041e2ab9843286e074f069d959944e3c6e4afa6470888525e8124b474eae15a729a81dd34db6c70a1952218827906cf0d946d324a3d5c4df43478c1e40b5123a0bb08460db61345ebf06685018b85d50fa0d2353e587dd3028da9d1c1a714481a86802c81d6807b08698c8a34ce07c72f547d02be81d4c96043ae95c42fc11e948c588144b4c1a6888a2c99581a0d488ce97a2ab50001e4ceabca0f988835b2ddfa859361f70dd0208456d0a681c6e0d500b482d81a620f81374c3f1cde91a9b57462a95253131415087f389c58a8e02283e41b212197
  | 7 => 0xa8103a62399bd7add0e809a33170ca0f57f0e48132e80a43c6b5570e548aad27bc4ea236c89cbf2043a44b24556c5512669281114462fa44aa831694b93935339373641ad9c5a6656b66ab1ad2998412043559a63c692451a9413d1154911a8cc5b87699d4fb802e998ab820cc582920168646acb0f8990cf122a108c6f66e0c935269ac0ee6f432c10a351760392da698c45a043043c2aa1a7191110f1eaa8ca294e481b2bc69d59544656dc15a3906b98cee46cd19a34a46e44da9469cf05e91aaa64846f474c47b5226e24490f1ab197a1c709387b94191186a1361a14eb890ae50caef47118ba35bea0dc2c568834e3782eb09c24b1343d0c31708811e6f1e8207ae22697e4b244ee28d2b9be8bc0520bb5715d0060b1efaae135fc1a99694f1a242429ccbb210eb890266332448b8a69d4db2da435203b2443531ac784e9b4992033190f7531ac91a29722bbf4a358b54da73126a61720a4ee01338ed2d44e9201a8290c8a72d450a4332da34f204eab533916eb2d0e58338c44a216edd0f90f0eb717ad52eaa8ad0f699e7724533ba4050f153917a8e06e08ac123fe01b31b4680d0aaa434f05b656c98cd328d7b91a372544803b694d9d50e461843d7a9848d18bce46ed244aaebf9e01626d2b0aab0612daf4e46130483a8ed2af4cb0646d385e4670ad28d532292cb4e4024810c543a97db31d68d190ab5000c46adc2a88da6c36cae001531eb711b9542d015c913ad4d43162bd106c01d6b2db28c5c8a986126caacc44642b75831f70b31c27306481761216b76fb95431e64ae22ed453b160e8281c3126d384d440e8124a0a92c8b4adb2f918c544218c42b8f56bcd1a4b2b9e24aa84fe006ee468865a38768c9dc34956a387a0a46d7cdb68192473b7768838cacb06c6aaa8b5e97d0aa222b99c37d4ec30510f34af02a4b1680914910ab19a33c96e324b5546b81a53113214bc6f22a9d330156ddb4e91bed38ad7f4cda45f201ab890d2f68c850ac21ed54c478269010f20430043aa82ad10eb8a304806a040c480c49156903731832a64929c5697c5ce45ee249a8e69c9c836c1b2443b89005311ee4171bc03204ae54cf5d689cf4f4c26872fb443abdc5a07164802a52249dd1a40534003b674330d225e27ac0da990b1bda52722e550c7569b90fa4b184802120709ac6af31ab36ff4470bbdc2e642b5541202aab96a5f0ee324ac642865877f708ad72063a92da32506c08cac458d48ef003aa3814f138818457f6989b4aaa1e810aa781b5117c3c075763c790a8086d4c70d38be01224811a2c571190b084291b722c0ae2aab6870a087a07444806a0768cc86c462c43ca57f1a9489f004abcdca97699511a7b4d9e55a0843118cc460b899aa7b419bdc33b091bc3a216cb21c33212d102b65e3cfb4f4b42978912023bc43b220e81cbadb1acf45b5168dd4cae66cae4a1209284c6b921a8090d5c92dbc8b2269a150f4b1edd9c31c2f54cad371b1e1a3113c4824af316b574a502f1901b060f1d5a6866ac202b4e0e8a82a0a
  | 6 => 0x2e9cc008642b702a59131502a5a42e746ad912a923a352ab9e2a5c46d0c4c862eab83aed0ac0da3992eeb85a7968af90bae12ea97ac012e484f440a8e46bdf0eac91a4d4f1513b4413ab02b7e3fd105ade42f169af906a99a20f0af744bd52b2913d4416b642bb63281c2b4342e4c8ab432b7da2988eb65a30d12811a33b168d10b7d2aa91a32b1ac543a6722dfb73c406edd0a378ec69a2e91abb4ab10a6efc4ba95cb74ba93428324aed42c086a2042874ead526934caa60a935753813a913a800a89e9ad72af54badc46965821e16c949b9f16b513f442b759a21c68c80c29142eb42bd20692d0a8046a00aa1e00510fba922f628a5ca6d5d7a04429f82af516b89832142cdcba8e8e8508cfb132848224bec886bb622964cadc0eb54ad792e812fb10628f4af3822a017a275cf15728a2a810e6fb689d03ad706b7183a268c7d83a50ad390b438ad59a2d8c2b50ba924eac14b3242b26fa1246b05a37c132b1a20e42e58af4417de4bbc0badb14b2726e8c1a02aa92d3ba95dde4aadd4ebe4acac44e8932e51ab884ab01ace49d4d4ca144d440af7da2362ba903b420ec804add2921b4a4612d102ac10ac684ca442b648ac1d2db04aac56e7d3ca14295c8b57329c13ad726b548bd24eb54bb7c2e8c48a272eb505adc689dc3af52cee5a210429184af568f0d3b1652d0afa04168102a80
  | 5 => 0x2a9a874082aee5daa38a3d36f48aa8854f12b527464aa4c25b75c9c135f84a241d5d2ae1a761c4b1899d38a8e89556faa34d27d2cf075ec9a0475bb2ac389628bb141dbd12caae6b0ab6f85810aaa536248ab075c4
  | 4 => 0x749
  | _ => 0

def G15_buckets : Nat → Nat
  | 4 => 1
  | 5 => 10
  | 6 => 56
  | 7 => 122
  | 8 => 102
  | 9 => 11
  | 10 => 1
  | _ => 0

def G15_flag : Nat → Nat
  | 4 => 2
  | 5 => 512
  | 6 => 2048
  | 7 => 4096
  | 8 => 8192
  | 9 => 2048
  | 10 => 2
  | _ => 0

def G15_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 12
  | 7 => 13
  | 8 => 14
  | 9 => 12
  | 10 => 2
  | _ => 0

def G15_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x58859009ae6581e0203a03c14
  | 6 => 0x1ef0973110c403d0710030080958da7ff01e00300901405700a0210012171bb22f06602b8b388a80500b26607a4070030e60010490020010cf00407a00403a00d05700300e03200102203d03204c00712302003d
  | 7 => 0x85000e8f447881f451703502463731a100d002c0071750d4459004e5e702a27540322bc2fe01bc0d400188e016c01600100080a0d0a0195b3009402204700181cc00607e016008000a01386a8ee409c001005c264406019011814407800e000823c0ca018001004400800204101301ae0010008ba20b403e00f00201151e803d00580571e8001019405404601f81280162040768018652002113017c09905600304301c202300102840200420980020011031008801001608015b814801c05401b0150006001
  | 8 => 0xc002000800d002800c0004001000c03b027c03485d42290068e2400ac109001547f00d8070030003f85640030088003016415410ec0500110076000408700040050010076058e196000c08000a000e005422b82fc0130c8000e001c031009806a81ec0090294081002003f00400f000040020008004013e05401640230100018000603203b40260004006022000104c8021805c013000a005051400301540010030020001c0670390006006000c0008001
  | 9 => 0x79900509e00505506f050007821812002
  | 10 => 0x2
  | _ => 0

def G15_initial : List Nat := [0xf0f0f0f0f0f0f0f00000000ff0000ff, 0x1212121212121212ff00ff0000ffff00, 0x313131313131313100ff00ff00000000, 0x44444444444444440000ffff0000ff00, 0x4848484848484848ffff000000ff0000, 0x8080808080808080ffffffffff000000, 0xa0a0a0a0a0a0a0a00000000000ffffff]

def G15_idx : Nat → List Nat → Nat :=
  qIndex G15_N G15_buckets G15_flag G15_seedBits G15_seeds

def G15_benes : Nat := 0xb780000019d2c8000000000000000019c0000000000000000000000000000000000000000000000000

def G15_inputActions : Nat := 0x357111ac688

def G15_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G15_benes auto)

def G15_cacheKeys (i : Nat) : Nat := G15_initial.getD i 0

def G15_cacheValues (auto i : Nat) : Nat :=
  G15_cacheKeys (fld G15_inputActions 3 (7*auto+i))

def G15_act (auto : Nat) : Nat → Nat :=
  cachedAction G15_cacheKeys (G15_cacheValues auto) 7
    (fun w => qInputLookup w G15_initial) (G15_rawAct auto)

def G15_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G15_initial G15_act G15_pb G15_records (10-s) j

def G15_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G15_act (i+1))

def G15_ori : List Nat → List Nat := orbitActions qPrefer G15_actions

def G15_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 65, 66, 67, 68, 69, 70, 71]

def G15_rankPool : List Nat := [2165678, 6519960, 1068169, 4284365, 2104987, 6622620, 4419210, 1060538, 4210573, 6455245, 7367817, 6311563, 4201624, 4340654, 7556265, 7616908, 4414616]

def G15_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 64 G15_S G15_N G15_idx G15_ori G15_coords 4 G15_rankPool s

def G15_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)
def G15_rows : List Nat := (([33, 44, 52, 65, 74, 76, 82, 84] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 8 ([3, 5, 9, 17, 6, 34, 24, 96] : List Nat)).flatten
def G15_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G15_rows)
theorem G15_nonconstant : ∃ x y : Fin 7 → Bool, G15_f x ≠ G15_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_enc_goal : encL G15_f G15_rows = goal 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_proper : ∀ zs ∈ G15_xs.sublists, zs ≠ G15_xs →
    (covUp 64 zs &&& lo 64) ≠ lo 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_good :
    qCachedGood (goal 64) 2 G15_initial G15_inputActions G15_benes := by
  unfold qCachedGood
  decide +kernel
theorem G15_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 64) s ws) : MonRun (goal 64) s (G15_ori ws) := by
  change MonRun (goal 64) s (qCachedOrient 2 G15_initial G15_inputActions G15_benes ws)
  exact qCachedOrient_run h G15_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_4_0 : span (G15_Z 4) 1 0 = true := by decide +kernel

theorem G15_checked_4 : span (G15_Z 4) 1 0 = true :=
  G15_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_5_0 : span (G15_Z 5) 40 0 = true := by decide +kernel

theorem G15_checked_5 : span (G15_Z 5) 40 0 = true :=
  G15_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_6_0 : span (G15_Z 6) 222 0 = true := by decide +kernel

theorem G15_checked_6 : span (G15_Z 6) 222 0 = true :=
  G15_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_7_0 : span (G15_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_7_256 : span (G15_Z 7) 232 256 = true := by decide +kernel

theorem G15_checked_7 : span (G15_Z 7) 488 0 = true :=
  (@span_join (G15_Z 7) 256 0 232 G15_check_7_0 G15_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_8_0 : span (G15_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_8_256 : span (G15_Z 8) 150 256 = true := by decide +kernel

theorem G15_checked_8 : span (G15_Z 8) 406 0 = true :=
  (@span_join (G15_Z 8) 256 0 150 G15_check_8_0 G15_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_9_0 : span (G15_Z 9) 41 0 = true := by decide +kernel

theorem G15_checked_9 : span (G15_Z 9) 41 0 = true :=
  G15_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_check_10_0 : span (G15_Z 10) 1 0 = true := by decide +kernel

theorem G15_checked_10 : span (G15_Z 10) 1 0 = true :=
  G15_check_10_0

theorem G15_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G15_N s, G15_Z s i = true := by
  interval_cases s

  · simp [G15_N]

  · simp [G15_N]

  · simp [G15_N]

  · simp [G15_N]

  · intro i hi
    exact span_ok G15_checked_4 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_5 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_6 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_7 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_8 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_9 i (Nat.zero_le i) (by simpa [G15_N] using hi)

  · intro i hi
    exact span_ok G15_checked_10 i (Nat.zero_le i) (by simpa [G15_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G15_initial_perm : G15_xs.Perm (G15_S 10 0) := by decide +kernel
theorem G15_no_run : ∀ s ≤ 10, ¬ MonRun (goal 64) s G15_xs := by
  exact noRun_from_barFastOrbit (k := 64) (S := G15_S) (N := G15_N)
    (idx := G15_idx) (ori := G15_ori) (coords := G15_coords)
    (bw := 4) (pool := G15_rankPool) (cap := 10) (i := 0)
    G15_preserved G15_checked (by decide) (by decide) G15_initial_perm
theorem G15_no_small : ¬ HasMonoSize 7 G15_f 10 :=
  encoded_mono_exclusion G15_f G15_nonconstant 10 G15_rows G15_xs 64
    rfl G15_enc_goal G15_proper G15_no_run
theorem G15_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G15_f x) :
    11 ≤ C.size := mono_lower G15_f 10 G15_no_small C hmono hev
def G16_N : Nat → Nat
  | 6 => 24
  | 7 => 78
  | 8 => 51
  | 9 => 1
  | _ => 0

def G16_pb : Nat → Nat
  | 5 => 5
  | 6 => 7
  | 7 => 6
  | _ => 0

def G16_records : Nat → Nat
  | 8 => 0xa4170618647468c88c2c44041c9c803028b0c0274c0378ac38903448025c0010c4d41454a02060d81f010b240ca80750580588
  | 7 => 0x3d785884dc87882d1a7ca45b4d6839b0b5e31305483d1834f8544d88bd457511d1874885b489f353cb52002000a2da27525548368357b1528db43b1253de431e7f64b00c4a4275c858a1d7835e1f20540d9847724bc4960b5ca972262256d2d44946195c8433da0f4f7d485c82e2001f27229512520b64c9b04b12548d4625a095ce18074f1a2856d
  | 6 => 0x351e3a5075b1aca35982a6475c1281155a3a649478ecc25104abb44e0e8815026a6454a86c7254c3a3c55c0a8f
  | _ => 0

def G16_buckets : Nat → Nat
  | 6 => 6
  | 7 => 20
  | 8 => 13
  | 9 => 1
  | _ => 0

def G16_flag : Nat → Nat
  | 6 => 4096
  | 7 => 1024
  | 8 => 1024
  | 9 => 2
  | _ => 0

def G16_seedBits : Nat → Nat
  | 6 => 13
  | 7 => 11
  | 8 => 11
  | 9 => 2
  | _ => 0

def G16_seeds : Nat → Nat
  | 6 => 0x2008cb300a001800402d
  | 7 => 0xa91040199f0110bc00a3b0020210f80400e0281e0033380120783c
  | 8 => 0x286600c1401d766020c006d17000a19818
  | 9 => 0x2
  | _ => 0

def G16_initial : List Nat := [0x80808080808ffff00ff00ff, 0xf0f0f0f0f0f0000ff00ff00, 0x121212121212ff0000ff0000, 0x31313131313100ff000000ff, 0x444444444444000000ff00ff, 0xa0a0a0a0a0a0000000ffff00, 0xc0c0c0c0c0c0ffffff000000]

def G16_idx : Nat → List Nat → Nat :=
  qIndex G16_N G16_buckets G16_flag G16_seedBits G16_seeds

def G16_benes : Nat := 0x0

def G16_inputActions : Nat := 0x1ac688

def G16_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G16_benes auto)

def G16_cacheKeys (i : Nat) : Nat := G16_initial.getD i 0

def G16_cacheValues (auto i : Nat) : Nat :=
  G16_cacheKeys (fld G16_inputActions 3 (7*auto+i))

def G16_act (auto : Nat) : Nat → Nat :=
  cachedAction G16_cacheKeys (G16_cacheValues auto) 7
    (fun w => qInputLookup w G16_initial) (G16_rawAct auto)

def G16_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 0 G16_initial G16_act G16_pb G16_records (9-s) j

def G16_actions : List (Nat → Nat) :=
  (List.range 0).map (fun i => G16_act (i+1))

def G16_ori : List Nat → List Nat := orbitActions qPrefer G16_actions

def G16_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 49, 50, 52, 53, 54, 55]

def G16_rankPool : List Nat := [5376940, 4413814, 3284107, 5458279, 5511017]

def G16_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 48 G16_S G16_N G16_idx G16_ori G16_coords 4 G16_rankPool s

def G16_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def G16_rows : List Nat := (([26, 33, 60, 65, 82, 84] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 6 ([3, 5, 9, 17, 6, 34, 72, 96] : List Nat)).flatten
def G16_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G16_rows)
theorem G16_nonconstant : ∃ x y : Fin 7 → Bool, G16_f x ≠ G16_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_enc_goal : encL G16_f G16_rows = goal 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_proper : ∀ zs ∈ G16_xs.sublists, zs ≠ G16_xs →
    (covUp 48 zs &&& lo 48) ≠ lo 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_good :
    qCachedGood (goal 48) 1 G16_initial G16_inputActions G16_benes := by
  unfold qCachedGood
  decide +kernel
theorem G16_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 48) s ws) : MonRun (goal 48) s (G16_ori ws) := by
  change MonRun (goal 48) s (qCachedOrient 1 G16_initial G16_inputActions G16_benes ws)
  exact qCachedOrient_run h G16_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_check_6_0 : span (G16_Z 6) 24 0 = true := by decide +kernel

theorem G16_checked_6 : span (G16_Z 6) 24 0 = true :=
  G16_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_check_7_0 : span (G16_Z 7) 78 0 = true := by decide +kernel

theorem G16_checked_7 : span (G16_Z 7) 78 0 = true :=
  G16_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_check_8_0 : span (G16_Z 8) 51 0 = true := by decide +kernel

theorem G16_checked_8 : span (G16_Z 8) 51 0 = true :=
  G16_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_check_9_0 : span (G16_Z 9) 1 0 = true := by decide +kernel

theorem G16_checked_9 : span (G16_Z 9) 1 0 = true :=
  G16_check_9_0

theorem G16_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G16_N s, G16_Z s i = true := by
  interval_cases s

  · simp [G16_N]

  · simp [G16_N]

  · simp [G16_N]

  · simp [G16_N]

  · simp [G16_N]

  · simp [G16_N]

  · intro i hi
    exact span_ok G16_checked_6 i (Nat.zero_le i) (by simpa [G16_N] using hi)

  · intro i hi
    exact span_ok G16_checked_7 i (Nat.zero_le i) (by simpa [G16_N] using hi)

  · intro i hi
    exact span_ok G16_checked_8 i (Nat.zero_le i) (by simpa [G16_N] using hi)

  · intro i hi
    exact span_ok G16_checked_9 i (Nat.zero_le i) (by simpa [G16_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G16_initial_perm : G16_xs.Perm (G16_S 9 0) := by decide +kernel
theorem G16_no_run : ∀ s ≤ 9, ¬ MonRun (goal 48) s G16_xs := by
  exact noRun_from_barFastOrbit (k := 48) (S := G16_S) (N := G16_N)
    (idx := G16_idx) (ori := G16_ori) (coords := G16_coords)
    (bw := 4) (pool := G16_rankPool) (cap := 9) (i := 0)
    G16_preserved G16_checked (by decide) (by decide) G16_initial_perm
theorem G16_no_small : ¬ HasMonoSize 7 G16_f 9 :=
  encoded_mono_exclusion G16_f G16_nonconstant 9 G16_rows G16_xs 48
    rfl G16_enc_goal G16_proper G16_no_run
theorem G16_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G16_f x) :
    10 ≤ C.size := mono_lower G16_f 9 G16_no_small C hmono hev
def G17_N : Nat → Nat
  | 4 => 3
  | 5 => 30
  | 6 => 167
  | 7 => 412
  | 8 => 337
  | 9 => 33
  | 10 => 1
  | _ => 0

def G17_pb : Nat → Nat
  | 3 => 2
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 6
  | _ => 0

def G17_records : Nat → Nat
  | 9 => 0x741e0003600522010120c001818004270a024050801508405c440b0d40080b180032f07c1605c0c00c
  | 8 => 0xcc74d8c1a9d06cb030d0894308117ca1b9d34c302da73c5089905c421e005df598a179715900b802f4a01944d8f0c0830d9001f00c8140d15d10dc40859216005d9855919c3228731df270d094c16930c0d4fcb02d702d0099910d289d105d3259d578109c80dcc874f001d0b5305db07da1e0d05e0858812c90c1404d30bd08740018d2f8a78d8070d0a142f0807cf2edf1f089d0d10cc01481414a8901c9f07c2095f4d4003cf349d14960b8a09d310d10a4311e00019a6590a83149f78c1000d034c4d4f10ce000078c7785810cb35140945301431811bc708d3056013d12083a1d905ce34d305c82f14068d0c811614a14a05d10bd902ca350d05a04b88160d15c59dd913d902409f0d02d90bdf11a0149931d8014d01140fc187db189b0bc00a0800130e9d0bd1170811141793249d21a0099f0094a10d09df15450bcaa5db9fc5579b1160308a300d13cb0b4a2f0d12a0a6992e9700011690789806d2a6962a14034f1594001b188117cb05cb0bce07d26f9d004d0c9b2fca345d35c30a0d334536d7854831d903c2031402e008d9850d4d80a1ca0b40180817140bcc0a9009c5038c080d23e0699b160804cb9f451f85329d07c090cd110d0bc216c989cc109939c134810e98319b001005c12f97218a8780001a1e99008d0b8c200d150d27900b144d4c19810dcf02d607cb03d3a9e0280d05080ac309db091409480c41859934d002dd09dd2fd90dd20b4c308702df1a9815850b0d87a00714098c63a0081463600dd11c5f02800988291413144fc22e93000b1cda002000540c47038f2e9809c12381169722da17c90dc0300802c9aa9b33856f87309b060878db02db170d0794174a87d902d3219324982fdf339d10cf07d60bcb178a4fce2ed903cc0c8780cd05d209859fdb20da2a0d1593878f02c1001605dda6d9090d2281089f
  | 7 => 0x9f5269acf5657dc2abf1d590002c805289a6b213a3c001d215213c345934722c9841d1304b49074cc233bce56a1405109dae3c2349966932883011a2ebec0f0e8e3371211a232b47d8304eef1d9e80ea283948c2a4715526f0b9a2d5388ab704e2ab2bd8cd240fa85305c8102342d791831309e200ec30a14817ab10960806c5471238173c9f4ec128c84c46838511159a0b9e044289aa482f52d0ac008046842bf109fe25cbc990e05af31611a20acc0f3a1ab0e095140ba480a6e4fa480940c178e82d33c2d4b1e59d072b4e558c3ab74b8750ecf4477a26a0f130a2709ec35a7cfe74785cb0a9493523016d71511ac6adc712f83ed7a84960dac82551abcd7105ff2bab47553c2a2004d083f3d0557d8eaba0d50c06ce8276d44aa7274812bb70224e8173107e546ca581d7a437100342c9752e877531a898569642a983d0304a930611a133681028a6b4c868e812afc253f0aa8534d1eaf1d0e117992ab0950b269fc0d7004b099f11a0bbb85d5102e31036533ec2a153bc2a70929e814146773a17cb293576129d8e5a01934802dde17c5499790a08d09ddc2eae9350b05b46035e4068e82724978510e6910f975569e02ed70a49606d3c0f59180513555854ca0216049b2915a3c5ea14e5a497b3c1742d3f8f8758b01649175763abd8553b03ef40f6725c97c21443bb45094c468d140f8804cf70b66c06a8c0d39c3eda8561213cc8c51cc3a6f05c925ea4c2d6a0eaaf1442a2c1452e8aa5a3a0556e18d401a73bc29f3092402a340d538388d140a20eb3e151d1ca850411a2eba42d7007b0e0562a0f369350da5b156354c170c42d2d02f1c0362c12cd8252a01c743668b0ac10410ab7c8f364484e14535608beea27dcf0a2352e6d2caba076989a888096405a76035da08d0e1d0b4fb0909d6405bd02d6884a722f57e2a144555d03f1002dd4f0a44274902d15094190b0ea0d0e01f150b6809a98a4d67a6af21111ac33d01f8a9408d8750c069d041a08011002d1e0b8e9658b17d3c079e921a741747ce88d0de793e894715b05aa207e3812d3c1d6d02f310a11a12b68113a81e3a0bdd523124178850aa21554e6aa4e7d3b82f1529e3c3a870138802f3c0b9a250b56a9460952f756724fbd02b881788d1c4303f2742d742ca730c51822ab60e4e85f102756ef0aacd9720188d09cba05974159b02a89094ee128940c2883c9d09de812c382718a6aa30740e4cb381d27c252f4d4a412c288d2002ef7069fe2eb50482881a6208e209ac309c4684ac00b61861cf0292a0aa2509d1eb2ca4004904a484d57e003d00b9503b2e276820bbd01f3c42a674d4b4f09ac004e84f310340e0a89817a586b3a4d40e06aea1f2480115
  | 6 => 0xd4ad22587cab6f055fc4e91012978fb3c10c7c128d92da442a115f6323a920259704a230569012c605584c9a05094885e8ba251401b431047a3ac281d9081a4b15614128449d740e256115624e8d0159588b210b63496b5c254683a36155a412ae4131f02b418546c0f8fa254908b0f0552412c68bd2902b97074e522d040d6a83ad11d5ac92a5025290e356154a50ac3c1d0e88b7e055a4070f871c542aed056fc20b100d7c8e228155ca60bd4094e04b6510cba5ebd41d6089d2f855225e93255a0972e0874b217b60155cc1b7210cdce89c00d4ccaa440347c38b00717583b2a066ac12800ad4b01b2e31612c28ec25a88ea25747102ab7ca93e82a7a095b20ad9415a313b25356e026cb99d4a15a1d096df06a34b9c188b7203c7c68d71558c9aabd838bb0a92c0b6c44b4d4b4fe22dd4410083a22a14e50a894251c34a17036fc12a1a7d29176d81d5332aba0553983afe095fc0ec48559704a4b855133e9c87d2205a910742212bc425a41a2d16f5e4deb7e158c03a91095132ab642548800a76f6b8109080daf83a96
  | 5 => 0x361c0d26104082d1c154720d8487583554803572198f036809da2555604d4f0353c0d41055801d3d2f4b92567875e041982e564a53d835204d9f274b0558e02d2e5573
  | 4 => 0xee41508233
  | _ => 0

def G17_buckets : Nat → Nat
  | 4 => 1
  | 5 => 8
  | 6 => 42
  | 7 => 103
  | 8 => 85
  | 9 => 9
  | 10 => 1
  | _ => 0

def G17_flag : Nat → Nat
  | 4 => 8
  | 5 => 16384
  | 6 => 1024
  | 7 => 8192
  | 8 => 2048
  | 9 => 1024
  | 10 => 2
  | _ => 0

def G17_seedBits : Nat → Nat
  | 4 => 4
  | 5 => 15
  | 6 => 11
  | 7 => 14
  | 8 => 12
  | 9 => 11
  | 10 => 2
  | _ => 0

def G17_seeds : Nat → Nat
  | 4 => 0x4
  | 5 => 0x45fe010c00e802b000400080010011
  | 6 => 0xd08269148ac039670124a80e1218a61f40a0050940200103f894108019c007a0ac444240480501d8490040100284b1ec0043c09a0020540f801
  | 7 => 0x96949c40c3023006a8664075020023c00700011b300150004a62000c02716f4066000800b000427a03ba136000400505cc106020211d00bc004045800186701b400100d900cc04f074c00402840cb02f4075000619c00a40f9005803884181840444036003402000642c9000800300220f2005c00200b8004000400300a8006024c00201c80018670278004a0d200c4004001219c005406f005800282380620160001809006c002008f02180f9005400a02e805d
  | 8 => 0x18430710c9370480023c00020148ea05e01a65e19d00d24b8a501c04800c2d20020025a000301715b02409205c03c0941a395104310a00104702400c09600402b0c81742e104003903e00900300a01904400603001408800710300300602e00e95119104900101700200300a01184a00100b01900a01b02a0600b300103883e
  | 9 => 0x230840a20cc056ce0042d002
  | 10 => 0x2
  | _ => 0

def G17_initial : List Nat := [0x808080808080808ffff00ffff00ffff, 0xf0f0f0f0f0f0f0f0000ff0000ff0000, 0x111111111111111100ff0000ff0000ff, 0x1212121212121212ff0000ff0000ff00, 0x6464646464646464000000000000ffff, 0xa0a0a0a0a0a0a0a0000000ffffff0000, 0xc0c0c0c0c0c0c0c0ffffff0000000000]

def G17_idx : Nat → List Nat → Nat :=
  qIndex G17_N G17_buckets G17_flag G17_seedBits G17_seeds

def G17_benes : Nat := 0x3e87b00013a26094c0000000000121242000000f61610000012aa424840000000000090898000000000f61ec0009649825300000000000484000000003d800000000000000000000000000000000000000000

def G17_inputActions : Nat := 0xba2646b1322e8d11ac688

def G17_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G17_benes auto)

def G17_cacheKeys (i : Nat) : Nat := G17_initial.getD i 0

def G17_cacheValues (auto i : Nat) : Nat :=
  G17_cacheKeys (fld G17_inputActions 3 (7*auto+i))

def G17_act (auto : Nat) : Nat → Nat :=
  cachedAction G17_cacheKeys (G17_cacheValues auto) 7
    (fun w => qInputLookup w G17_initial) (G17_rawAct auto)

def G17_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 2 G17_initial G17_act G17_pb G17_records (10-s) j

def G17_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G17_act (i+1))

def G17_ori : List Nat → List Nat := orbitActions qPrefer G17_actions

def G17_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 65, 66, 67, 68, 69, 70, 71]

def G17_rankPool : List Nat := [6491871, 6651032, 2112954, 7547276, 7695545, 5255086, 5271178, 2195437, 4340873, 2182554, 7426014, 2187181, 5340826, 3296408, 5250216]

def G17_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 64 G17_S G17_N G17_idx G17_ori G17_coords 4 G17_rankPool s

def G17_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def G17_rows : List Nat := (([26, 28, 33, 50, 52, 65, 82, 84] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 8 ([3, 5, 9, 17, 6, 40, 72, 96] : List Nat)).flatten
def G17_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G17_rows)
theorem G17_nonconstant : ∃ x y : Fin 7 → Bool, G17_f x ≠ G17_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_enc_goal : encL G17_f G17_rows = goal 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_proper : ∀ zs ∈ G17_xs.sublists, zs ≠ G17_xs →
    (covUp 64 zs &&& lo 64) ≠ lo 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_good :
    qCachedGood (goal 64) 4 G17_initial G17_inputActions G17_benes := by
  unfold qCachedGood
  decide +kernel
theorem G17_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 64) s ws) : MonRun (goal 64) s (G17_ori ws) := by
  change MonRun (goal 64) s (qCachedOrient 4 G17_initial G17_inputActions G17_benes ws)
  exact qCachedOrient_run h G17_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_4_0 : span (G17_Z 4) 3 0 = true := by decide +kernel

theorem G17_checked_4 : span (G17_Z 4) 3 0 = true :=
  G17_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_5_0 : span (G17_Z 5) 30 0 = true := by decide +kernel

theorem G17_checked_5 : span (G17_Z 5) 30 0 = true :=
  G17_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_6_0 : span (G17_Z 6) 167 0 = true := by decide +kernel

theorem G17_checked_6 : span (G17_Z 6) 167 0 = true :=
  G17_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_7_0 : span (G17_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_7_256 : span (G17_Z 7) 156 256 = true := by decide +kernel

theorem G17_checked_7 : span (G17_Z 7) 412 0 = true :=
  (@span_join (G17_Z 7) 256 0 156 G17_check_7_0 G17_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_8_0 : span (G17_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_8_256 : span (G17_Z 8) 81 256 = true := by decide +kernel

theorem G17_checked_8 : span (G17_Z 8) 337 0 = true :=
  (@span_join (G17_Z 8) 256 0 81 G17_check_8_0 G17_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_9_0 : span (G17_Z 9) 33 0 = true := by decide +kernel

theorem G17_checked_9 : span (G17_Z 9) 33 0 = true :=
  G17_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_check_10_0 : span (G17_Z 10) 1 0 = true := by decide +kernel

theorem G17_checked_10 : span (G17_Z 10) 1 0 = true :=
  G17_check_10_0

theorem G17_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G17_N s, G17_Z s i = true := by
  interval_cases s

  · simp [G17_N]

  · simp [G17_N]

  · simp [G17_N]

  · simp [G17_N]

  · intro i hi
    exact span_ok G17_checked_4 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_5 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_6 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_7 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_8 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_9 i (Nat.zero_le i) (by simpa [G17_N] using hi)

  · intro i hi
    exact span_ok G17_checked_10 i (Nat.zero_le i) (by simpa [G17_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G17_initial_perm : G17_xs.Perm (G17_S 10 0) := by decide +kernel
theorem G17_no_run : ∀ s ≤ 10, ¬ MonRun (goal 64) s G17_xs := by
  exact noRun_from_barFastOrbit (k := 64) (S := G17_S) (N := G17_N)
    (idx := G17_idx) (ori := G17_ori) (coords := G17_coords)
    (bw := 4) (pool := G17_rankPool) (cap := 10) (i := 0)
    G17_preserved G17_checked (by decide) (by decide) G17_initial_perm
theorem G17_no_small : ¬ HasMonoSize 7 G17_f 10 :=
  encoded_mono_exclusion G17_f G17_nonconstant 10 G17_rows G17_xs 64
    rfl G17_enc_goal G17_proper G17_no_run
theorem G17_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G17_f x) :
    11 ≤ C.size := mono_lower G17_f 10 G17_no_small C hmono hev
def G18_N : Nat → Nat
  | 5 => 4
  | 6 => 43
  | 7 => 138
  | 8 => 180
  | 9 => 25
  | 10 => 1
  | _ => 0

def G18_pb : Nat → Nat
  | 4 => 2
  | 5 => 6
  | 6 => 8
  | 7 => 8
  | 8 => 5
  | _ => 0

def G18_records : Nat → Nat
  | 9 => 0xa40400400848360440b0002a0065300c6b0b03505c0c0200041c14060270a0
  | 8 => 0x3da3b480d949b80002193c12929c6188e16a41a52d4a55645f9986102e10a9d2bddcb31a604d48b2c817b800a39c4549c2a49b4a0d885b60c27c2c409d62bc93f8b9ca69d20bac37201eb0c84116000c2cd20d9e55dc221a7eb142123dc27424ac87da47095693766082061981fc18630ea61738376035469f097913f40ccf03a41b2a7f9091078ce1b84e73889003e41b09a7505c41b949b31761a9ca0bd209acab385c993c43ac8d749b2a87d8e5285e48bc0032027609fa06ed6df0e11ca5c02109cae50419f527ed4d5855246a9b4e615b01f1136482f107700f6046616b89c6f0a909bb839078c41b98aa3800900163108679164a37dd2fa42760261a2841e912f8a4cc308413c4a649bca70940f30018154205c8a9180f425cf2ff007843f3a7ca359539de6f11b6a0b48313c56314d83552f1bc00783acde86d2a4bb196531dae1d2a4fc25c24fc82f382a04ba9
  | 7 => 0x51ac0a5358559135011742f7911025bc416c06961a758105444567155f54e582b5e035420b614b1694959cbf58854e425282763c2dab974dd9f5867cf01594074a0bf9f2f662896697661356703ced5e5a854041d23709601d625f4b88505074d43564848ec552e2c460a9660d588315d97d615e3b2f504365803ac57d5f4750d358507518d919296583d4e3658c95050b661652b6b4d4d546336280d6d346602f580f4a1c39f195b40d9d784620e805552e4f9a876b64d782d4d4773b85508a5782ba68125a0d4a0a313675c83d6478640416135961c16e1b5f52e00054140e5a1c6761597838309e9a34e6865880f615654b4d6ac657d126087182934d53574094b8463b074401d856b48c9d96495d0af3a2f48d1d1b69504c119114154e5a90e00a33a064580d5a538ecbd376bc4c1f9a538f01d96
  | 6 => 0x1453f5555f2542104441d46034b1ad40035f80d7f285c07d022750a5d562f4ad7d42c75751d7e11480ad08c5409a50f194280b062b58cd103514e8d1550758f1d83c759c155d26435ad30274ce250c955582555705501d0f8360d2d7e304434d33
  | 5 => 0x455469452e442e56
  | _ => 0

def G18_buckets : Nat → Nat
  | 5 => 1
  | 6 => 11
  | 7 => 35
  | 8 => 45
  | 9 => 7
  | 10 => 1
  | _ => 0

def G18_flag : Nat → Nat
  | 5 => 32
  | 6 => 1024
  | 7 => 32768
  | 8 => 8192
  | 9 => 256
  | 10 => 2
  | _ => 0

def G18_seedBits : Nat → Nat
  | 5 => 6
  | 6 => 11
  | 7 => 16
  | 8 => 14
  | 9 => 9
  | 10 => 2
  | _ => 0

def G18_seeds : Nat → Nat
  | 5 => 0x12
  | 6 => 0xe713386a3140600183a07009000806
  | 7 => 0x4b6000a00760057000100020003412400dd001a0134802b01a60321007b003a000200350009002b001a00100004000d00090007030c00010001048f00020004000500140004
  | 8 => 0x50020406101740cf0124036000510a0c44006079003100300b401182ec0004008001c041029800500140e0004010f000c07100c20a9006e02700040300070007001800100720b400480230054011
  | 9 => 0x4304202168042086
  | 10 => 0x2
  | _ => 0

def G18_initial : List Nat := [0xf0f0f0f0f0f0f0f0000ff0000ff0000, 0x111111111111111100ff0000ff0000ff, 0x1212121212121212ff0000ff0000ff00, 0x2424242424242424ffff00000000ffff, 0x4848484848484848000000ffff00ffff, 0xa0a0a0a0a0a0a0a0000000ffffff0000, 0xc0c0c0c0c0c0c0c0ffffff0000000000]

def G18_idx : Nat → List Nat → Nat :=
  qIndex G18_N G18_buckets G18_flag G18_seedBits G18_seeds

def G18_benes : Nat := 0x42e7b00013a26094c0000000000121242000000f61610000012aa424840000000000090898000000001021ec0009649825300000000000484000000003d800000000000000000000000000000000000000000

def G18_inputActions : Nat := 0xb9c286b1942e7111ac688

def G18_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G18_benes auto)

def G18_cacheKeys (i : Nat) : Nat := G18_initial.getD i 0

def G18_cacheValues (auto i : Nat) : Nat :=
  G18_cacheKeys (fld G18_inputActions 3 (7*auto+i))

def G18_act (auto : Nat) : Nat → Nat :=
  cachedAction G18_cacheKeys (G18_cacheValues auto) 7
    (fun w => qInputLookup w G18_initial) (G18_rawAct auto)

def G18_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 2 G18_initial G18_act G18_pb G18_records (10-s) j

def G18_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G18_act (i+1))

def G18_ori : List Nat → List Nat := orbitActions qPrefer G18_actions

def G18_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 65, 66, 67, 68, 69, 70, 71]

def G18_rankPool : List Nat := [3296408, 6491871, 7695529, 2195115, 7756172, 5320638, 5520569, 4284333, 6438282, 6454424, 2125451, 7687610]

def G18_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 64 G18_S G18_N G18_idx G18_ori G18_coords 4 G18_rankPool s

def G18_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def G18_rows : List Nat := (([26, 28, 33, 50, 52, 65, 74, 76] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 8 ([3, 5, 9, 17, 6, 40, 80, 96] : List Nat)).flatten
def G18_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G18_rows)
theorem G18_nonconstant : ∃ x y : Fin 7 → Bool, G18_f x ≠ G18_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_enc_goal : encL G18_f G18_rows = goal 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_proper : ∀ zs ∈ G18_xs.sublists, zs ≠ G18_xs →
    (covUp 64 zs &&& lo 64) ≠ lo 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_good :
    qCachedGood (goal 64) 4 G18_initial G18_inputActions G18_benes := by
  unfold qCachedGood
  decide +kernel
theorem G18_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 64) s ws) : MonRun (goal 64) s (G18_ori ws) := by
  change MonRun (goal 64) s (qCachedOrient 4 G18_initial G18_inputActions G18_benes ws)
  exact qCachedOrient_run h G18_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_5_0 : span (G18_Z 5) 4 0 = true := by decide +kernel

theorem G18_checked_5 : span (G18_Z 5) 4 0 = true :=
  G18_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_6_0 : span (G18_Z 6) 43 0 = true := by decide +kernel

theorem G18_checked_6 : span (G18_Z 6) 43 0 = true :=
  G18_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_7_0 : span (G18_Z 7) 138 0 = true := by decide +kernel

theorem G18_checked_7 : span (G18_Z 7) 138 0 = true :=
  G18_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_8_0 : span (G18_Z 8) 180 0 = true := by decide +kernel

theorem G18_checked_8 : span (G18_Z 8) 180 0 = true :=
  G18_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_9_0 : span (G18_Z 9) 25 0 = true := by decide +kernel

theorem G18_checked_9 : span (G18_Z 9) 25 0 = true :=
  G18_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_check_10_0 : span (G18_Z 10) 1 0 = true := by decide +kernel

theorem G18_checked_10 : span (G18_Z 10) 1 0 = true :=
  G18_check_10_0

theorem G18_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G18_N s, G18_Z s i = true := by
  interval_cases s

  · simp [G18_N]

  · simp [G18_N]

  · simp [G18_N]

  · simp [G18_N]

  · simp [G18_N]

  · intro i hi
    exact span_ok G18_checked_5 i (Nat.zero_le i) (by simpa [G18_N] using hi)

  · intro i hi
    exact span_ok G18_checked_6 i (Nat.zero_le i) (by simpa [G18_N] using hi)

  · intro i hi
    exact span_ok G18_checked_7 i (Nat.zero_le i) (by simpa [G18_N] using hi)

  · intro i hi
    exact span_ok G18_checked_8 i (Nat.zero_le i) (by simpa [G18_N] using hi)

  · intro i hi
    exact span_ok G18_checked_9 i (Nat.zero_le i) (by simpa [G18_N] using hi)

  · intro i hi
    exact span_ok G18_checked_10 i (Nat.zero_le i) (by simpa [G18_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G18_initial_perm : G18_xs.Perm (G18_S 10 0) := by decide +kernel
theorem G18_no_run : ∀ s ≤ 10, ¬ MonRun (goal 64) s G18_xs := by
  exact noRun_from_barFastOrbit (k := 64) (S := G18_S) (N := G18_N)
    (idx := G18_idx) (ori := G18_ori) (coords := G18_coords)
    (bw := 4) (pool := G18_rankPool) (cap := 10) (i := 0)
    G18_preserved G18_checked (by decide) (by decide) G18_initial_perm
theorem G18_no_small : ¬ HasMonoSize 7 G18_f 10 :=
  encoded_mono_exclusion G18_f G18_nonconstant 10 G18_rows G18_xs 64
    rfl G18_enc_goal G18_proper G18_no_run
theorem G18_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G18_f x) :
    11 ≤ C.size := mono_lower G18_f 10 G18_no_small C hmono hev
def G19_N : Nat → Nat
  | 5 => 4
  | 6 => 92
  | 7 => 337
  | 8 => 330
  | 9 => 34
  | 10 => 1
  | _ => 0

def G19_pb : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 9
  | 7 => 9
  | 8 => 6
  | _ => 0

def G19_records : Nat → Nat
  | 9 => 0x64843841d084073a49d000b90049137415014c5044a123489394398c62d010c900c250a4170d40d214b5
  | 8 => 0x24d809cd394405cb034423dd21d421110e440a15410601440a0f8b8231448601016028df05de1dcd3adb040f178d05dd040033d0860f044407c20a1a2d210fdb98cb05d021d134180986211f29df2d8d2e5908ce00e0211d21ca085f01849b448a0d056025110d8615dd2d0307c12498a58129c128c82d11449f33df210515da21100dc88581451f861e23440dc627590f86041522dd8e1e301d041289cb3a9b07c6101e2459080a32db298186061c440d4403592f2139cd0fc20c1208060c1aa4cb3acc2e0d41db3b0c2d060e5910023b0b0ec83b182d0f2444324401c49944100628440c1e078200150edfb91d28590f9e325905c60a59045f8e0a059e0a028e14286004598614add6a5c13b1d07de0d59100ac0db9ccc210c1a44398d031505d917cd0fd00c0293db246007442e4421193a8c44cd2211229d18c531d028882d02808405db2ed601199cdb0acb180d231d101531602a110ddb0a060bde861d0ad605c1371d06590fde2e01a3e0210b1000ba0d094408590fdf0c03859d33db0786aecb2a160f8209820a0a8b9e900525cb411693dd2d1abf0b15ca0959410505e00bd621592d60144498d81e0b0bcb0fc621162108a8cc09c2071528db841d39590d9e09c632cc13c485a031593ac83b0e0802079e001f9544100f06602dcd94e127e08e06381d32df041a9ddb238d0ad8240d8620242108df2d0a2908410b13e121182d172d1e2601210d898d211c251803cb3ad030442d1405d6bf16040a934429db15cf93cb2a0196dd8bc2000a2359c0ccb81b24c50dde075905df0a14081200440a4421442d15081e89d815d4225993d617dd0104a544001b1bcc224421043c1d2d4415d50a0341182fd6000b0c1444df264444db2fcbaddf0edb32d02109adcb05860644081523113f4423cd0bdf211b
  | 7 => 0x165150d8687351c3e1a10879859280b26c8332d0e52138b6170cc1647c3cfc13cf2892342ea2c1c9b249648948c266782cda21a570b44ca26e02ed1998082f3b8e69b42d48b788b0b440de0190510004c84339c0532105401c20e2f94a122d86ca3090f20f28d228e52911140325b51ce1321d4180d88c3413c9f49c4d363a8a6644341e168b264840f35f4ae267707d031b20f1c1e44c2183cef25a905e99082991d50605a2e271a81e67c2d151384d1725426a29d49ea39901323c175503ca993c3207ccc1d321052b899d01f33c1734052648e21a731881e351cc442886a5a99096620426489a325122867279652723c325b4da2c3cc4a640d0f2773a03e720de4fb79fc0f3911226c9eb0078a2133e5120613c934899a592b8b2021043e064c81f28c364aa250c17c9e0f0d00e9d41879044c8169909e8991e93a481a410a4fe9f8ec042e160733846e9d0988b8d8201b1440e81c9f12271e82b4ac827f83c9539d600f1644e0c8d107a5a200813e6483986431809e4b8646932164758c0f307414a08889ecb1b89e5316c560256ce1098e3279a0c695dd10d1389e1f23c8a0fc9e830392a13134261983c33070f24c9904f03c244922a80609901741c9ead21278890ac169f87cbe099463041c1e8a14c261989e0b40cb67407c46899c3170d1161a8d08b010c81b390da740540d87a623410c264b91cee278b717118ce95c50b0238605f00c9e080cc031789f1b1362e78450790aa8c304cc862d90465244c8752dce67404ce4879ce2744c268190f33134c90f416205c9045a0588c2e41e1e6d14cb415944471124f6882eb0059840b0b512920deb0179d00699084430a9072687d1337c36a28ace71320e45210e66f8bd19241611f36856829244517860264cc31321645d25a264f09a203c82f12308e650434b63105c2d241e94b47c553211c4987a5642194364787c33bed602b0f484581beb00f8a242214c6082240109a7e03190a28642cc89593e2813c269693e198d9b40713cea6c0c2640589a334e81e4d924562584c1f3e48e7442c5b18160133b62e0182ce4224c80f40c162882c950fa8b51060a689c4cda374c80bb2c962d97264228fe5b3b80b8383ced
  | 6 => 0x8da4f1301c4e6c43c13278aa412568e1009d0d3e8360742a1675c2c93059fb0f43a86239bc273e93c4b0805e03c2cf403a470b4002e2942c2083a4f439b0973618441079680f3f44e75c3d273e8090b1ec0e7212d1a8b9362935e2e939fc242182613470e24d1f454839a71316a8e16c2c8819988273d04e498ad0e209582f168367e85cf72f82707310fe8189c200b9fa0b100de7b89cb223a3a2f390c28e11c78098a50f1be162f89c88159d51326c0e2596c2c068642748cde488bd35860d83334cfa9a8c484199c83312e165942d2c0d9a06f0b0166845d1a
  | 5 => 0x379801c2c4e854341
  | _ => 0

def G19_buckets : Nat → Nat
  | 5 => 1
  | 6 => 23
  | 7 => 85
  | 8 => 83
  | 9 => 9
  | 10 => 1
  | _ => 0

def G19_flag : Nat → Nat
  | 5 => 8
  | 6 => 1024
  | 7 => 1024
  | 8 => 4096
  | 9 => 32768
  | 10 => 2
  | _ => 0

def G19_seedBits : Nat → Nat
  | 5 => 4
  | 6 => 11
  | 7 => 11
  | 8 => 13
  | 9 => 16
  | 10 => 2
  | _ => 0

def G19_seeds : Nat → Nat
  | 5 => 0x1
  | 6 => 0x30ee011806a880589e19c0280380511200c008160d81100b80300401000816
  | 7 => 0x80300082f81c722dec205110444b00500c08e32c16001999308050024265cc0512b410012a88c20820045080200f2f44c00612a5c43581b02827cab05604254a5d8268860b2a88cc06a1b4140380030faa88210084742280407e3280680308012a0402300814c0e1f20420440289a0020041b804
  | 8 => 0x59413600f89e003014f1140010a2030a003206003800402e00200dc03614d5e40ffa22402406100d05ce07f00e80900020740050058132001028452810a00400980b4016002000824000e15a03081b21f70e600281fa1ae01f868003003601c8a501900e606a865802c0230aa842007c0fb019000801229400300280b808600402000040fc001
  | 9 => 0x41dc0001011f0010012f802200be8022000f
  | 10 => 0x2
  | _ => 0

def G19_initial : List Nat := [0x707070707070700ff0000ff0000, 0x19191919191919ff00000000ff00, 0x20202020202020ffff00ffffff00, 0x2a2a2a2a2a2a2a0000ff000000ff, 0x44444444444444000000ff00ffff, 0x90909090909090000000ffff00ff, 0xc0c0c0c0c0c0c0ffffff00000000]

def G19_idx : Nat → List Nat → Nat :=
  qIndex G19_N G19_buckets G19_flag G19_seedBits G19_seeds

def G19_benes : Nat := 0x7f0ef1c24d00480000000000000000024000e100000000000000000000000000000000000000000000

def G19_inputActions : Nat := 0x34ad03ac688

def G19_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G19_benes auto)

def G19_cacheKeys (i : Nat) : Nat := G19_initial.getD i 0

def G19_cacheValues (auto i : Nat) : Nat :=
  G19_cacheKeys (fld G19_inputActions 3 (7*auto+i))

def G19_act (auto : Nat) : Nat → Nat :=
  cachedAction G19_cacheKeys (G19_cacheValues auto) 7
    (fun w => qInputLookup w G19_initial) (G19_rawAct auto)

def G19_S (s j : Nat) : List Nat :=
  qParentAction 10 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 1 G19_initial G19_act G19_pb G19_records (10-s) j

def G19_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G19_act (i+1))

def G19_ori : List Nat → List Nat := orbitActions qPrefer G19_actions

def G19_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63]

def G19_rankPool : List Nat := [5336441, 1059722, 5532280, 4206237, 6446715, 4283514, 6311595, 1064122, 2112664, 5447102, 6638215, 6576250, 2117001, 6634391]

def G19_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G19_S G19_N G19_idx G19_ori G19_coords 4 G19_rankPool s

def G19_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def G19_rows : List Nat := (([28, 42, 49, 56, 68, 97, 98] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 7 ([3, 5, 9, 6, 18, 36, 72, 80] : List Nat)).flatten
def G19_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G19_rows)
theorem G19_nonconstant : ∃ x y : Fin 7 → Bool, G19_f x ≠ G19_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_enc_goal : encL G19_f G19_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_proper : ∀ zs ∈ G19_xs.sublists, zs ≠ G19_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_good :
    qCachedGood (goal 56) 2 G19_initial G19_inputActions G19_benes := by
  unfold qCachedGood
  decide +kernel
theorem G19_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G19_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G19_initial G19_inputActions G19_benes ws)
  exact qCachedOrient_run h G19_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_5_0 : span (G19_Z 5) 4 0 = true := by decide +kernel

theorem G19_checked_5 : span (G19_Z 5) 4 0 = true :=
  G19_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_6_0 : span (G19_Z 6) 92 0 = true := by decide +kernel

theorem G19_checked_6 : span (G19_Z 6) 92 0 = true :=
  G19_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_7_0 : span (G19_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_7_256 : span (G19_Z 7) 81 256 = true := by decide +kernel

theorem G19_checked_7 : span (G19_Z 7) 337 0 = true :=
  (@span_join (G19_Z 7) 256 0 81 G19_check_7_0 G19_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_8_0 : span (G19_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_8_256 : span (G19_Z 8) 74 256 = true := by decide +kernel

theorem G19_checked_8 : span (G19_Z 8) 330 0 = true :=
  (@span_join (G19_Z 8) 256 0 74 G19_check_8_0 G19_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_9_0 : span (G19_Z 9) 34 0 = true := by decide +kernel

theorem G19_checked_9 : span (G19_Z 9) 34 0 = true :=
  G19_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_check_10_0 : span (G19_Z 10) 1 0 = true := by decide +kernel

theorem G19_checked_10 : span (G19_Z 10) 1 0 = true :=
  G19_check_10_0

theorem G19_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G19_N s, G19_Z s i = true := by
  interval_cases s

  · simp [G19_N]

  · simp [G19_N]

  · simp [G19_N]

  · simp [G19_N]

  · simp [G19_N]

  · intro i hi
    exact span_ok G19_checked_5 i (Nat.zero_le i) (by simpa [G19_N] using hi)

  · intro i hi
    exact span_ok G19_checked_6 i (Nat.zero_le i) (by simpa [G19_N] using hi)

  · intro i hi
    exact span_ok G19_checked_7 i (Nat.zero_le i) (by simpa [G19_N] using hi)

  · intro i hi
    exact span_ok G19_checked_8 i (Nat.zero_le i) (by simpa [G19_N] using hi)

  · intro i hi
    exact span_ok G19_checked_9 i (Nat.zero_le i) (by simpa [G19_N] using hi)

  · intro i hi
    exact span_ok G19_checked_10 i (Nat.zero_le i) (by simpa [G19_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G19_initial_perm : G19_xs.Perm (G19_S 10 0) := by decide +kernel
theorem G19_no_run : ∀ s ≤ 10, ¬ MonRun (goal 56) s G19_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G19_S) (N := G19_N)
    (idx := G19_idx) (ori := G19_ori) (coords := G19_coords)
    (bw := 4) (pool := G19_rankPool) (cap := 10) (i := 0)
    G19_preserved G19_checked (by decide) (by decide) G19_initial_perm
theorem G19_no_small : ¬ HasMonoSize 7 G19_f 10 :=
  encoded_mono_exclusion G19_f G19_nonconstant 10 G19_rows G19_xs 56
    rfl G19_enc_goal G19_proper G19_no_run
theorem G19_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G19_f x) :
    11 ≤ C.size := mono_lower G19_f 10 G19_no_small C hmono hev
def G20_N : Nat → Nat
  | 4 => 1
  | 5 => 21
  | 6 => 199
  | 7 => 651
  | 8 => 575
  | 9 => 51
  | 10 => 1
  | _ => 0

def G20_pb : Nat → Nat
  | 4 => 5
  | 5 => 8
  | 6 => 10
  | 7 => 10
  | 8 => 6
  | _ => 0

def G20_records : Nat → Nat
  | 9 => 0x2e5c28946a5582114280ccac55a008a20d0201cba55748b452c900a456aa10001432715e818423126bf44a1d2c9a46a394cb202a6136c05ca1f
  | 8 => 0x883caccb3d95e2a7360b022f0451daa81ca2300862f1e849196423ee488c403001922d10c5e889d7420c28634e0064233894029c70350e339bc736ce291998fb3252baaf044002b33113b238bca8a803117884040ef8878d1c0688643940fce0300b45472319d043a286049f232b10da21fc46e70c2410262031933a540535c61188120bf23880319c1e785ee2fa297c83f9002108805d9d2790667331c069da0c8967380830386e6a54643da57446060ace5fcf0811692a5ce5f9ca1018230801379e6d182941029618ed0218c080a706ce331c0c305cd61943501e0cb2460026299dbc7260e44348eb82e2a3464c80c89ca9317461dda290174d15dc141abb757e332f1759c93c59008781525816b8615bac274803080de8080d679cbb1188abf1a718eb89531731e73b840f103d232df4396fcc9be7040f1826383578ea7dc71a0363598a9c25808c270606425ae18802614b3388cb43b314292e801c00a80f0a13f10803000c3f34417badc5c80d08d7a32e67388c7168cf90140085ec66608e9c264b8d04600a321403c1eba74f02000113c884b03f38ba40fc88b2ca33860c2fd0ce6443388203bda9710720420e1b8c931000889d62da2407610d450713881e649b38bf1823420903e6a4676e22399cac08dc503ce4084ae0b00e13481f1031713407f1c6b4122022013b1e73b45e2bf1d64626918da00e0c205e1835c0715e30c80361400716192a8c1119a191e0a1012535526e998f8a202b69a073a3118127320c33b730275c1918478094681be304578d27d0645a359d96119c745b2a3c4d33b1d9171ca7b5d78a64689da3790b2319ce65a8e7214ee4531139a1518a20002d2bb200a206c05da11a218a0517a1dc60ce8fc610ebaed6e028d9c372a3c434806500060076748a0a7209822dc116ce01005002867684a3e147e2884649a4e518778c067179c589d8a3149553e2c77c28996018264891830805671f84404c5a303280fda33290a345ed381e3e917c713463188959c7c6881939bef058a6898da60808344dc797cf140a3b7c81006090ce30100c6e8fed0008039c0832199801c2e1608209c5379c1f44b2006131806004060f17ef0b1a30a421007d964800319d2316f01052f04e018a7c21db0c704806b4111c48c4959c705856e502890210802f1fe21e9c56213ee1bc435185108429339e6f61b898b4010367721120232c67e23119d6416d95048bfc471589da2c4c68384140fe42fa6a7091eb062b4ba41f0441087ce59b22bc9c2326ca14503691133a58e3bb8b6045f223d14f90b4c9ff140dc8130773c71400800c0a3015863162c4da06b1c40f180f068c9b394f7174032ce1d192f72d91082aa8b8cf888d93790100c2158bda485c209c023284689e312c5c9830d043820f98209ba6700cea8690f1ae0127aabb681c7ad4075b0999caa023d9341e0b9846b2d2d643210a01a00e05131a6f888029cf1653e3b50189ad0e8464b265680142e53826518becad31
  | 7 => 0xe312d1ce206d5e1b140ba70d10b7a18b82f2cc8f1159cc487e044f3649e6ccae0ea7a368b3d29e4a0bcf40a6277528cb46746c8f166272e8fc5e1283c6887cb10fa6e9e3318e258587d273f88e6c99005b1c0547175063d47c3e8b9c12b42ec64b5166ead92d641b4167d53cec3b82302c4e58115744cb8a1e0c2ca511f9d4499647e31060162e9323f099f55e8fc563443e42321203b2cc5e20cde6838db52ec4ec612cdc3ba7c5464144561b4ae6844999270eeee6652c21b18eb2bb5c86420ec5e0447e18c4e6189c4cbe3047e4b1ea865746cb38d8516038b025447c8f0d82b644521e5197edf0983f5005c2642c5e150591e0f97c3e59ddc870384a501a40e1dd74ad168715c8fcc602cc09bb79e61b0226e0ad8ca12181b433400e5359d0b939667d8a44e04544b70597e174642a6551c21b216a5f1ea1059400b7ad0d06728c68591fc15b01727d45ea62e91a3f3b9cf600b0bf5bc4cf2b19c9630280e0103ce4899151c1e8ce5743c00802102b0aaca8242c64218eb638165e1d460b299c2a00254c61544ca6a383963357023884622af986654048989d3e290d8644b0b0665343e90219d827250c881994e93382b1f288ee42c2068239d84f2704e7602e773195d7d88a6e488344a0d9631f2921a3e43c75bb9474f1709e349d4b48d9cf28c4e2687d9476a41078037cce0703cbc322102f28e291f87c640147e4d192367053e2299a22071c23e60c3c698990e754345600c7c4585ca40f1dec012d0a3f1494a0a8fc267a000ce8d8c2431de875c90c0e079e80d2ba0f590d0ce898c8270fabf1145c74a20050f92e563ac4c3344a185cc4e1e192046dae93e64162580157e02878450b3d0361f56c3693ca46715abe3451cbe079e50b0b0fc7451c1487e29672b2fe6593c2a058b85b114c80145cb189dc56300aea0b1fceca99fc17074a00a90c3695cdd030fc4e2e8bc3621d011b8964a5282ef5a1627461ba968310c68a38580f0aa360fdd4653b94d001ba3e7952c173287f643608e7d454ad1b96637178962e814fa99cd01b1d2be0218ca32d86646c4e930a8c23f28107811fa7648984abbe9c033008967f04ce082cb141170be34c7ce78b8c8271a48e51c2cf29319d0fb3a3e3e98c778fa012f3aec36f84c74a198e6417c700a93e691595d63442a6160ec3ba79c0132fc2673dc4fd39947643f62e1903cb38bdc50fb72b66dd9c270b83f1739e26730c0588795d0f0faca8444c3ea99c0530ccb266530259797c4725a86624bc873fc4b2b0304e0f89c21a69a989422a62e190ce800a26f1eaa01504c611d94d1713ece3d4cd062c9782a8fc16111dc723181c1f0140002c3313b204b1f4486812d9cee3847e488fcc84a98c01b09e90f9bb124cc3c6e179890144eb412c7c50339c62b31cbe4cc701507818171ea8b714023f320842f3dc588a49c170d9983729ab657510efbedb01008ace06180ef87ca24cc4e1f12cca3f448004c148167003eb90da246519e211f9bedf2f9df622ae0f675f8e2bea1e1b074c6639082a0f9e8273809e160dc253997c4229cc84dd1c2a978f75d3544d1f8300ea19fd470ccc68f194ef3386d473e86f6c03c0a168506db7c9189c2c173b9ee13330c63702cd91d8044b2148e7017ee28f83a5fbbe363e8bc9e97cd0652029627c3cc7138cc5d12ca07ac2c1eac8966730c8e0f52e170c04b010fc503482e2a32145773d01f1484c8f25a0142148ca6ad9c8195858593684e161146eb3a0c0b292ee1d4cc9122045133e8c355c7c74b804b59404668042c1f09973471985e4885ca218dbe53086a64a03e228dd6f2f008867254ce244a02472705e8e9905c8784e171b22d1f9406e97895622e456724bc3bb1db98919e1589c3d10a1db05d4269e0b98c36858393417cce16c3f0827c2e5a254ea404231397dc52f3cc0389cac70b747e281622589c4ca4939b20fb8a2e59d4cf3386271325b063bd9c2a998f55d272167610d1e1402e27170723898cb7338010c05cee1b1909fae830751b036305b4a7839152b038367a04a3f0b8a063332bd89c3cc4b01d10c8fc3e7043e952edbe5f38a88680a495ad820473ccce4a4bca687c0b530726a440d313961df6412e8441c5c089da3a433bec66d01c5e0383c6d31c847ae243fa782b641a05e1999cbc19966
  | 6 => 0xc21857c900796a5f0e8367f170b9879da7f2ec9634d3cca0c9d52b4081e35d6d2c059a30f1ccfa86cbcae15a681314e205141d440d94e4b098be1384c88be840331304e438ac32a590f0b0ac1e99c3d410b92e001b25e29c4c129b8342b1362e1584c9a27a82332dc885144c3a15822291ea58514dca8319676d1fc9e20c3c9e858d3371148626cac0e23a580701ac63989d2d2387c0b2964e34c4c4607e826f0e886070cd059b8984b076c28dc1cae2d925130ac9e8cccc9c078150f0441ea281c17898b20b1bcc60545cfe079fc302fe1e0ad8d172394b6d19416651bcb730a517d31e1e7f96c222c8540f200c21f05c60a19e60014a9e4445c43878972f268166952ce5879874f2965e4450c11219131348e0e260dc17af81c0f3621e6253cd283a0b5b514da2edf5139584e2f482361582d073196a094ae1e6705cb7258784f1181e2f178b98594a6f288965b83cf687a3c0f396bb9190cc4af8075f206be2758d453fa270f07a1e0983c8d939942f4e62e68d8cce0b8b22f0e81e0711c92af822133f8660d04ce32d8746f214c60dd7cc4858870f0ca167841cb3079ec071001693d7c7330868132405e1103cf0801590b32e362c84c22198d43305e609196432199666d2469683d6ea2b18d7270208e29db80dad8a7
  | 5 => 0xda4f6d0a2d9883c14b6734302a4a216c0abe360b4d218fd6c94860a5b41958fc2cb22601274d158289c9e1696
  | 4 => 0x16d3
  | _ => 0

def G20_buckets : Nat → Nat
  | 4 => 1
  | 5 => 6
  | 6 => 50
  | 7 => 163
  | 8 => 144
  | 9 => 13
  | 10 => 1
  | _ => 0

def G20_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 16384
  | 7 => 4096
  | 8 => 4096
  | 9 => 2048
  | 10 => 2
  | _ => 0

def G20_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 15
  | 7 => 13
  | 8 => 13
  | 9 => 12
  | 10 => 2
  | _ => 0

def G20_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x28454011a01
  | 6 => 0x2780d844a62da806400e501e0003073481cb002c0034020c0c7002a1d3c11b8002000a001000100090748000400d0195818e0004002802200aa01640040001818e01080d4000100420400008c0c701f6040401580090007031e0528036
  | 7 => 0x3d003a0600008099404d3812a80287ca1b8001820005400803f870c0ec0d80040bc0b60263907058401a4ea000804400c0cc1ef0314042011000826c21a083000903000e007168072c002069033056002002e0008fc4030001026807450a004000c4fc00805e01901580d41e2006812003804602f009803404800100b00421120a2001c0040380570158064001001800401e00e00d036000600601501b40d203600e000400202e00e80ba1fa001092420001c071009003400a005000801800400d00d007001202a00f800800205e00380a006e0560030068006007008ca2e05c01006500940f610301f81a420e01b0010128016001005800c2b201501f003c00200201801c4004010
  | 8 => 0x3000814a03a001000801602904a816800e7cd00e48440100a0214000402a00d03781363f603701205786fe01f001003001e0da030002001f1fa003013468404a058c4fc1260021e1810647e0200ff803062e20407e8031a0201202480040fe1170e2001647e04a10f014c061115000807c20523f009815005000100800661e70b3058020c0f707f000c8fc03602c00500f401506e00603740ee004040829008001a002004400201d02e8044002002002041c02200103c80a60d6003002004807e00e0630008004008001410800e04b009800804c04300084e002002302282a414013405c00580a8013
  | 9 => 0xe00f74f1bf08502901000108823f00200100d
  | 10 => 0x2
  | _ => 0

def G20_initial : List Nat := [0x70707070707070000ff00ff0000, 0xa0a0a0a0a0a0aff0000ff00ff00, 0x1919191919191900ff00000000ff, 0x40404040404040ffffffffff0000, 0x646464646464640000000000ffff, 0x90909090909090000000ffffff00, 0xa0a0a0a0a0a0a0ffffff00000000]

def G20_idx : Nat → List Nat → Nat :=
  qIndex G20_N G20_buckets G20_flag G20_seedBits G20_seeds

def G20_benes : Nat := 0x0

def G20_inputActions : Nat := 0x1ac688

def G20_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G20_benes auto)

def G20_cacheKeys (i : Nat) : Nat := G20_initial.getD i 0

def G20_cacheValues (auto i : Nat) : Nat :=
  G20_cacheKeys (fld G20_inputActions 3 (7*auto+i))

def G20_act (auto : Nat) : Nat → Nat :=
  cachedAction G20_cacheKeys (G20_cacheValues auto) 7
    (fun w => qInputLookup w G20_initial) (G20_rawAct auto)

def G20_S (s j : Nat) : List Nat :=
  qParentAction 10 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 0 G20_initial G20_act G20_pb G20_records (10-s) j

def G20_actions : List (Nat → Nat) :=
  (List.range 0).map (fun i => G20_act (i+1))

def G20_ori : List Nat → List Nat := orbitActions qPrefer G20_actions

def G20_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63]

def G20_rankPool : List Nat := [6637690, 6368924, 2104215, 4262552, 2178441, 5311678, 2121081, 3156874, 6445688, 5336747, 5532295, 5394043, 6373084, 4414072]

def G20_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G20_S G20_N G20_idx G20_ori G20_coords 4 G20_rankPool s

def G20_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def G20_rows : List Nat := (([10, 28, 81, 84, 97, 98, 100] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 7 ([3, 5, 9, 6, 18, 40, 72, 48] : List Nat)).flatten
def G20_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G20_rows)
theorem G20_nonconstant : ∃ x y : Fin 7 → Bool, G20_f x ≠ G20_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_enc_goal : encL G20_f G20_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_proper : ∀ zs ∈ G20_xs.sublists, zs ≠ G20_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_good :
    qCachedGood (goal 56) 1 G20_initial G20_inputActions G20_benes := by
  unfold qCachedGood
  decide +kernel
theorem G20_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G20_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 1 G20_initial G20_inputActions G20_benes ws)
  exact qCachedOrient_run h G20_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_4_0 : span (G20_Z 4) 1 0 = true := by decide +kernel

theorem G20_checked_4 : span (G20_Z 4) 1 0 = true :=
  G20_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_5_0 : span (G20_Z 5) 21 0 = true := by decide +kernel

theorem G20_checked_5 : span (G20_Z 5) 21 0 = true :=
  G20_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_6_0 : span (G20_Z 6) 199 0 = true := by decide +kernel

theorem G20_checked_6 : span (G20_Z 6) 199 0 = true :=
  G20_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_7_0 : span (G20_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_7_256 : span (G20_Z 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_7_512 : span (G20_Z 7) 139 512 = true := by decide +kernel

theorem G20_checked_7 : span (G20_Z 7) 651 0 = true :=
  (@span_join (G20_Z 7) 256 0 395 G20_check_7_0 (@span_join (G20_Z 7) 256 256 139 G20_check_7_256 G20_check_7_512))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_8_0 : span (G20_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_8_256 : span (G20_Z 8) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_8_512 : span (G20_Z 8) 63 512 = true := by decide +kernel

theorem G20_checked_8 : span (G20_Z 8) 575 0 = true :=
  (@span_join (G20_Z 8) 256 0 319 G20_check_8_0 (@span_join (G20_Z 8) 256 256 63 G20_check_8_256 G20_check_8_512))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_9_0 : span (G20_Z 9) 51 0 = true := by decide +kernel

theorem G20_checked_9 : span (G20_Z 9) 51 0 = true :=
  G20_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_check_10_0 : span (G20_Z 10) 1 0 = true := by decide +kernel

theorem G20_checked_10 : span (G20_Z 10) 1 0 = true :=
  G20_check_10_0

theorem G20_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G20_N s, G20_Z s i = true := by
  interval_cases s

  · simp [G20_N]

  · simp [G20_N]

  · simp [G20_N]

  · simp [G20_N]

  · intro i hi
    exact span_ok G20_checked_4 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_5 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_6 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_7 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_8 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_9 i (Nat.zero_le i) (by simpa [G20_N] using hi)

  · intro i hi
    exact span_ok G20_checked_10 i (Nat.zero_le i) (by simpa [G20_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G20_initial_perm : G20_xs.Perm (G20_S 10 0) := by decide +kernel
theorem G20_no_run : ∀ s ≤ 10, ¬ MonRun (goal 56) s G20_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G20_S) (N := G20_N)
    (idx := G20_idx) (ori := G20_ori) (coords := G20_coords)
    (bw := 4) (pool := G20_rankPool) (cap := 10) (i := 0)
    G20_preserved G20_checked (by decide) (by decide) G20_initial_perm
theorem G20_no_small : ¬ HasMonoSize 7 G20_f 10 :=
  encoded_mono_exclusion G20_f G20_nonconstant 10 G20_rows G20_xs 56
    rfl G20_enc_goal G20_proper G20_no_run
theorem G20_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G20_f x) :
    11 ≤ C.size := mono_lower G20_f 10 G20_no_small C hmono hev
def G21_N : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 176
  | 7 => 488
  | 8 => 432
  | 9 => 41
  | 10 => 1
  | _ => 0

def G21_pb : Nat → Nat
  | 3 => 1
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 6
  | _ => 0

def G21_records : Nat → Nat
  | 9 => 0x28398b150140e01800d40083108d802270302002858b87401b01104c28290b0785e11804442a12048a018040c080
  | 8 => 0x1500bb3cec1080a39cabe80e618dc8c6a93f550aa59504d0c9b08293a7d9302caa0cbc028d94f2e77189c7120a1bbeab500cb05ce4da032945eeb5cd102c1651367171607b47f444ea804a5bca9b8ce6086274f964a50bd030cf669676902a2a8802b969e342cc85854f161f798528a0a61989f50eef04167324736038513c623ce7e9c4e113161296716d042319139842d8d3d4118b13bc7344ec71f0a35381e8c5b00be41118a780a05200a2c2c562c3ed03d0142c6a49b0561a74502552c913a6de39286697c692ad972c0168ced3088661b1e30c01316840012878124e1d0a43a846808cc9cdc0016165cf2c03163014225d6492aa50a15e3453c31d16974a1e6c5d18be317cc265d06caf6039a401588cb2fcb25361d143af22e539c42a104e2b1d74e2c4b367e757a559387614b0505544ba2162cf0b34e80d285aa13a5939b4fca271cae50025f1247f2c34d80119b0be3944c29180734135149a491d4012c1f3984885a0078ed78001030a065387a3c5e709c80bcc37a09a84da063a40f577c18a8d27a08f50f6c4d5e0ac67b3c2c8a90a001cd62d0d005a55350c0585af216073ca1d8c4a28c912f2083106e285d417aa4e142f207d62b501e15841f8c105142f83ae929809fcca634c418019071273344ee97d0242c82a136cb4c43f160f2094c8c81378253617f009e42918bb613c0141673a25d41ab0111639ae3f0c8aa1c8a232889950e126c5133c0e40e67b4cd0fc62e803051390182d8e5136f89cb7386525c185071621327d2c9e4a2270932378cfec8bde4daa732c4c5a6da4088a23516c9e0a1bb4aa055051f970ace0628c48879e31922f20141028906a0a681ce09d959b46c694f278d912ec04e2540b11a59fba7c58a8522a5232e4e602c011670b8a7b7980519cd173c86502f38aa03db20f9901397c2c34a4e08ce491cab3204e994ec119b4dcc805bc2910866980aa444ec8dc7af063a48eaca6c951a89248e7035e85014736e6cf0da5442c73584af1d9b52c051604f311a73322223c2ed23a55150302934b9cc00f8a37791e1338b2323cf2db0b15970b4e4428fe80b8033a04e511489ce82b840f38e621ec20bc6166cf4c18a52fc047366b19c9b45064e64a4c3621
  | 7 => 0xf09982d011a8c533ad0e8c4e4bf0e90ce6ce2198c8ccd229f8829693481c2eb539066a893fd308a10069689b3c061604a6d238a09c2a0e8e86b732336c8b7268cd036173ebad2a8439b378aeb08e10e6f6ae944af5928dbb1a52168c6ca012b1445aff2092112de0ee4c8e2e12d803afe0539532b33f530aa7ee11041b930a8808b1722d7c8b5252e8dac419acc0ea7c22ca09b6c12af82a6705274eaad21120e77d0ba708b1f3f0b89a7f38e60f2aa0ec590261aedac2b170aaa82b5d2ecf08ce5f0e431b380b4c41b1266b057aff0b50c94c438db13ab05abf8ad6b1785c2a09228d48b6e0bcc4e76268bfcea013ca90862850d5012966886a6b16179057f432e91c4aeb6ca782abf5adec4ad63a8c59a7e228b81cc40b6948f1d16958305826e0c2a9f12cc17d2014ae93ac112959005838e3c3ae01185c2b5e39c74eb8d2310400cee2b582cf639b6c3b833e9fa6a26c5e9c01a726bbc2ca20aa489a7c3ed49320c2d8a03a0e0adb8e20923345b33452bc14ab12ba74ea530ec94af6b278a084c4129f8ea6d5f50c88733a82e6ab90ee2d7abd06b2cae633a90caa943ceb0e6d10aa10eb06239ec3b782681b1b492ad24ea2623268bb930ac5933682f9044a5322948aa51c6ca03a8942a483b7123017c36460a788e6522a7cab6b268302c054c8090fa70685486480e8989f6742d942b721b1043a9727b942ab612b8173aa26e342a4506dacf302c30ba6a3a06bd122cf0a9682a3216dc532910edec2b8542cf81d0c22e041f6bb2830238e0aa575ba322d94aac1688008d7d233d82d200aeace7a53ed31caff52bfc2a960b1ac1cd10ac96bc51081cd0aff9ab80e26a448c13b3a3edc4b70c44b502a0d0b85caaebaf5ac8ca264a2d02d32ac28e6410b36c2b470585c929539815a28b128c48a0b3f2708d05268dcbf4306a409a43af0a90b4c38d51aac13f1ec4b56078a8ba0146a38a6280b5f54ae42369cbe9d26bfacb930a8d45ae0c6e103b42268942c7b42ca05a2642cd8ea9822cd0fa843eb04e72022b0c8bab12b048da40a8401c2827405b2ab141610f43229682b313ec282d6220a6c8d1a2691c8a320691d7b430e9fc5f4326ac53b56000a10e410abe42c9a9ae7882b3b2c482a7e050a08d4300310fb3a3ea50ea9744d183a530b69cea8d42e102b38234802ccd054303af9281cceb83d6ac44b3a38c74aee5075ac3a982ebfcffa7236950b382b0a84b0a38d7d6b832e8309a28230ba6b783aae43b480718c4aec2ace802739718c9ae00b2716a8c0a9486afb390a26ac22cb4e6b48b2bd03ab92da759b0a228345a674e81d3b0a2c1ccca4723a703c280aa385b2b2b9445b360acd06a670b6908a804ccad0b494eaf883490b1049acb0ea582cd11688ceae03c1626af90b0abc23407274aa01c327122662b8a08501509148aba549814f430aa708ae022b445a350ac7c9e9d0785d0a354e9f83a675f904c23042e04e51d4ebad9b602ad590d4c2682d0fa5eaa114afa231ac2ae027d288a843cba02b0e2f8a3aa130ee8c2b49
  | 6 => 0x22d7cea8092f644bcaaaf650aff22e603b7ac2b31a2cf38b748b203ee0c8a0e12dbc1a415ed908b6e0494d7b7912ec4a3023e82c2b052294c4af212ab433472ae0c2af006ec82b6f5ef2c8aae38f34830f4eab48aff06c38aa41bea189b3b06df0ab9f12e0daaad388349abb6a83d0360ab6ef3b775e9cc8b6312de82aa496b24abb8051ac2b9f12f4c261f3e89d3a3d2ace08a6892c841b3b22b44aaad0af89ab830aaefa39e06eec1bd50eb245ab25da302ba026f743aa70a8048a4c24d7c1ba15ef6c8a1e279aebb9f06c148b9f22c917b8b06f281c1f6a9f01bb83edd80172ae9048ae00ef888b05276eeba63239ac932f38a082b6e388f88af896f4c9a1238826fc6b5e9604a7f075c82a0e24da08a633a9048bc40a9fc2aae68dd02b2496f2ba21b22b793b833b1ac4bdb069a4faad5e8d42bc42aaec3bd34ca7d3b3e06b7b7aba096ec2e6b0ab2087722ab457a4506c883b5d0eed5a3570abfc9bb25ea205b6f12ed43e1f4289daba53e8384b263ebfcbabd12b244be216954aade6aae01a630ae9da2ba3a8390bcb
  | 5 => 0x82b025613a9e1143c1b52458f22ad835408ae20d580ac782d9482181d100684075c81ae4152b20a51f4f02a200d455ed3105e81a8e0d7d
  | 4 => 0xab8135
  | _ => 0

def G21_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 44
  | 7 => 122
  | 8 => 108
  | 9 => 11
  | 10 => 1
  | _ => 0

def G21_flag : Nat → Nat
  | 4 => 4
  | 5 => 256
  | 6 => 2048
  | 7 => 4096
  | 8 => 4096
  | 9 => 512
  | 10 => 2
  | _ => 0

def G21_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 9
  | 6 => 12
  | 7 => 13
  | 8 => 13
  | 9 => 10
  | 10 => 2
  | _ => 0

def G21_seeds : Nat → Nat
  | 4 => 0x1
  | 5 => 0x4640c0501a6c5602
  | 6 => 0x8766e900101110584602900600200c0010040d50080fb00902207103d0020aa81e0134e000f32b00203b00901f2ae00701480600813b01c02903e0361250b60031c1
  | 7 => 0x13e23ba00500102751da8d9805235a10c062006000200400146940391460064500008002167800400210e00182f46eb0e50ebc32c00c00b02300342b40020220f4c6da02700285301741d42e1010c1151e800f819809e00400081ac01a001000803012c0618f442c000204008680f048805200281d417a08783b000c04904b00c804826211f0018004002231101831406c03981c05200040d0000803401003600100f00040280eb80600051e8013823c002030062801206a02d01081280440030188004024001
  | 8 => 0x80343e71a30018210940029002026000605b00a800c19519d009803c54a64f0042be80a600e00180e400e02500f00be2f20011b305f41ce0038a4c4c614603103c803052e013002832c0ac02406e040012e0330020014150055039007c009067831000407a01d829851400e00100e81fc00201000b800406000306b032404803f06f02644420010018008080001822807c00601d003006803810e002800e05400102481d002a004019800400e026
  | 9 => 0xb87e12450130d8260f40801803
  | 10 => 0x2
  | _ => 0

def G21_initial : List Nat := [0x70707070707070700ff0000ff000000, 0xa0a0a0a0a0a0a0aff0000ff0000ff00, 0x1010101010101010ffff00ffff00ff00, 0x19191919191919190000ff0000ff00ff, 0x6464646464646464000000000000ffff, 0xa0a0a0a0a0a0a0a0000000ffffff0000, 0xc0c0c0c0c0c0c0c0ffffff0000000000]

def G21_idx : Nat → List Nat → Nat :=
  qIndex G21_N G21_buckets G21_flag G21_seedBits G21_seeds

def G21_benes : Nat := 0xf61ec0009649825300000000000484000000003d800000000000000000000000000000000000000000

def G21_inputActions : Nat := 0x2e8d11ac688

def G21_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G21_benes auto)

def G21_cacheKeys (i : Nat) : Nat := G21_initial.getD i 0

def G21_cacheValues (auto i : Nat) : Nat :=
  G21_cacheKeys (fld G21_inputActions 3 (7*auto+i))

def G21_act (auto : Nat) : Nat → Nat :=
  cachedAction G21_cacheKeys (G21_cacheValues auto) 7
    (fun w => qInputLookup w G21_initial) (G21_rawAct auto)

def G21_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G21_initial G21_act G21_pb G21_records (10-s) j

def G21_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G21_act (i+1))

def G21_ori : List Nat → List Nat := orbitActions qPrefer G21_actions

def G21_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 65, 66, 67, 68, 69, 70, 71]

def G21_rankPool : List Nat := [6389402, 4340107, 7610079, 7756681, 6298792, 5255134, 6315658, 3157386, 3231130, 4288429, 3296152, 7367051, 6651032, 6373294]

def G21_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 64 G21_S G21_N G21_idx G21_ori G21_coords 4 G21_rankPool s

def G21_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def G21_rows : List Nat := (([10, 28, 34, 49, 52, 66, 81, 84] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 8 ([3, 5, 9, 6, 18, 40, 72, 96] : List Nat)).flatten
def G21_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G21_rows)
theorem G21_nonconstant : ∃ x y : Fin 7 → Bool, G21_f x ≠ G21_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_enc_goal : encL G21_f G21_rows = goal 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_proper : ∀ zs ∈ G21_xs.sublists, zs ≠ G21_xs →
    (covUp 64 zs &&& lo 64) ≠ lo 64 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_good :
    qCachedGood (goal 64) 2 G21_initial G21_inputActions G21_benes := by
  unfold qCachedGood
  decide +kernel
theorem G21_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 64) s ws) : MonRun (goal 64) s (G21_ori ws) := by
  change MonRun (goal 64) s (qCachedOrient 2 G21_initial G21_inputActions G21_benes ws)
  exact qCachedOrient_run h G21_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_4_0 : span (G21_Z 4) 2 0 = true := by decide +kernel

theorem G21_checked_4 : span (G21_Z 4) 2 0 = true :=
  G21_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_5_0 : span (G21_Z 5) 26 0 = true := by decide +kernel

theorem G21_checked_5 : span (G21_Z 5) 26 0 = true :=
  G21_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_6_0 : span (G21_Z 6) 176 0 = true := by decide +kernel

theorem G21_checked_6 : span (G21_Z 6) 176 0 = true :=
  G21_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_7_0 : span (G21_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_7_256 : span (G21_Z 7) 232 256 = true := by decide +kernel

theorem G21_checked_7 : span (G21_Z 7) 488 0 = true :=
  (@span_join (G21_Z 7) 256 0 232 G21_check_7_0 G21_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_8_0 : span (G21_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_8_256 : span (G21_Z 8) 176 256 = true := by decide +kernel

theorem G21_checked_8 : span (G21_Z 8) 432 0 = true :=
  (@span_join (G21_Z 8) 256 0 176 G21_check_8_0 G21_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_9_0 : span (G21_Z 9) 41 0 = true := by decide +kernel

theorem G21_checked_9 : span (G21_Z 9) 41 0 = true :=
  G21_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_check_10_0 : span (G21_Z 10) 1 0 = true := by decide +kernel

theorem G21_checked_10 : span (G21_Z 10) 1 0 = true :=
  G21_check_10_0

theorem G21_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G21_N s, G21_Z s i = true := by
  interval_cases s

  · simp [G21_N]

  · simp [G21_N]

  · simp [G21_N]

  · simp [G21_N]

  · intro i hi
    exact span_ok G21_checked_4 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_5 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_6 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_7 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_8 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_9 i (Nat.zero_le i) (by simpa [G21_N] using hi)

  · intro i hi
    exact span_ok G21_checked_10 i (Nat.zero_le i) (by simpa [G21_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G21_initial_perm : G21_xs.Perm (G21_S 10 0) := by decide +kernel
theorem G21_no_run : ∀ s ≤ 10, ¬ MonRun (goal 64) s G21_xs := by
  exact noRun_from_barFastOrbit (k := 64) (S := G21_S) (N := G21_N)
    (idx := G21_idx) (ori := G21_ori) (coords := G21_coords)
    (bw := 4) (pool := G21_rankPool) (cap := 10) (i := 0)
    G21_preserved G21_checked (by decide) (by decide) G21_initial_perm
theorem G21_no_small : ¬ HasMonoSize 7 G21_f 10 :=
  encoded_mono_exclusion G21_f G21_nonconstant 10 G21_rows G21_xs 64
    rfl G21_enc_goal G21_proper G21_no_run
theorem G21_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G21_f x) :
    11 ≤ C.size := mono_lower G21_f 10 G21_no_small C hmono hev
def G22_N : Nat → Nat
  | 6 => 12
  | 7 => 41
  | 8 => 31
  | 9 => 1
  | _ => 0

def G22_pb : Nat → Nat
  | 5 => 4
  | 6 => 6
  | 7 => 5
  | _ => 0

def G22_records : Nat → Nat
  | 8 => 0x13008181807250ac00004d02069a9020066a490681406191b0a0532c0a0600101c70a8
  | 7 => 0x14d3699c6abd3cdc2224f34af1ab17c70ab05ab001f4b32fcc7ac92b03ab92ada220ae8eb8a71f5e7bb1c6ba6cd5b268ee0baf56e05ba0d1e5af97cd6211eafb211ee89b852e03ba
  | 6 => 0xe929d966a49f472a8ebd9d4aaa7472acba53c4a3b460
  | _ => 0

def G22_buckets : Nat → Nat
  | 6 => 3
  | 7 => 11
  | 8 => 8
  | 9 => 1
  | _ => 0

def G22_flag : Nat → Nat
  | 6 => 512
  | 7 => 128
  | 8 => 512
  | 9 => 2
  | _ => 0

def G22_seedBits : Nat → Nat
  | 6 => 10
  | 7 => 8
  | 8 => 10
  | 9 => 2
  | _ => 0

def G22_seeds : Nat → Nat
  | 6 => 0x20051f
  | 7 => 0x14030d4d3413018f0a0883
  | 8 => 0x528cc03c170200502809
  | 9 => 0x2
  | _ => 0

def G22_initial : List Nat := [0x7070707070700ff000000ff, 0xa0a0a0a0a0aff0000ff0000, 0x1919191919190000ff00ff00, 0x242424242424ff00ff000000, 0x505050505050ffff00000000, 0x808080808080ffffff000000, 0xe0e0e0e0e0e0000000ffffff]

def G22_idx : Nat → List Nat → Nat :=
  qIndex G22_N G22_buckets G22_flag G22_seedBits G22_seeds

def G22_benes : Nat := 0x290640881ac35008000000000000101a0000440a400000000000000000000000000000000000000000

def G22_inputActions : Nat := 0x357015ac688

def G22_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G22_benes auto)

def G22_cacheKeys (i : Nat) : Nat := G22_initial.getD i 0

def G22_cacheValues (auto i : Nat) : Nat :=
  G22_cacheKeys (fld G22_inputActions 3 (7*auto+i))

def G22_act (auto : Nat) : Nat → Nat :=
  cachedAction G22_cacheKeys (G22_cacheValues auto) 7
    (fun w => qInputLookup w G22_initial) (G22_rawAct auto)

def G22_S (s j : Nat) : List Nat :=
  qParentAction 9 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G22_initial G22_act G22_pb G22_records (9-s) j

def G22_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G22_act (i+1))

def G22_ori : List Nat → List Nat := orbitActions qPrefer G22_actions

def G22_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 49, 50, 51, 52, 53, 54, 55]

def G22_rankPool : List Nat := [4413814, 5393547, 5389740, 2103655, 5458553]

def G22_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 48 G22_S G22_N G22_idx G22_ori G22_coords 4 G22_rankPool s

def G22_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)
def G22_rows : List Nat := (([33, 34, 36, 74, 81, 92] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 6 ([3, 5, 9, 6, 18, 40, 48, 96] : List Nat)).flatten
def G22_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G22_rows)
theorem G22_nonconstant : ∃ x y : Fin 7 → Bool, G22_f x ≠ G22_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_enc_goal : encL G22_f G22_rows = goal 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_proper : ∀ zs ∈ G22_xs.sublists, zs ≠ G22_xs →
    (covUp 48 zs &&& lo 48) ≠ lo 48 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_good :
    qCachedGood (goal 48) 2 G22_initial G22_inputActions G22_benes := by
  unfold qCachedGood
  decide +kernel
theorem G22_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 48) s ws) : MonRun (goal 48) s (G22_ori ws) := by
  change MonRun (goal 48) s (qCachedOrient 2 G22_initial G22_inputActions G22_benes ws)
  exact qCachedOrient_run h G22_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_check_6_0 : span (G22_Z 6) 12 0 = true := by decide +kernel

theorem G22_checked_6 : span (G22_Z 6) 12 0 = true :=
  G22_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_check_7_0 : span (G22_Z 7) 41 0 = true := by decide +kernel

theorem G22_checked_7 : span (G22_Z 7) 41 0 = true :=
  G22_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_check_8_0 : span (G22_Z 8) 31 0 = true := by decide +kernel

theorem G22_checked_8 : span (G22_Z 8) 31 0 = true :=
  G22_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_check_9_0 : span (G22_Z 9) 1 0 = true := by decide +kernel

theorem G22_checked_9 : span (G22_Z 9) 1 0 = true :=
  G22_check_9_0

theorem G22_checked (s : Nat) (hs : s ≤ 9) : ∀ i < G22_N s, G22_Z s i = true := by
  interval_cases s

  · simp [G22_N]

  · simp [G22_N]

  · simp [G22_N]

  · simp [G22_N]

  · simp [G22_N]

  · simp [G22_N]

  · intro i hi
    exact span_ok G22_checked_6 i (Nat.zero_le i) (by simpa [G22_N] using hi)

  · intro i hi
    exact span_ok G22_checked_7 i (Nat.zero_le i) (by simpa [G22_N] using hi)

  · intro i hi
    exact span_ok G22_checked_8 i (Nat.zero_le i) (by simpa [G22_N] using hi)

  · intro i hi
    exact span_ok G22_checked_9 i (Nat.zero_le i) (by simpa [G22_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G22_initial_perm : G22_xs.Perm (G22_S 9 0) := by decide +kernel
theorem G22_no_run : ∀ s ≤ 9, ¬ MonRun (goal 48) s G22_xs := by
  exact noRun_from_barFastOrbit (k := 48) (S := G22_S) (N := G22_N)
    (idx := G22_idx) (ori := G22_ori) (coords := G22_coords)
    (bw := 4) (pool := G22_rankPool) (cap := 9) (i := 0)
    G22_preserved G22_checked (by decide) (by decide) G22_initial_perm
theorem G22_no_small : ¬ HasMonoSize 7 G22_f 9 :=
  encoded_mono_exclusion G22_f G22_nonconstant 9 G22_rows G22_xs 48
    rfl G22_enc_goal G22_proper G22_no_run
theorem G22_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G22_f x) :
    10 ≤ C.size := mono_lower G22_f 9 G22_no_small C hmono hev
def G23_N : Nat → Nat
  | 5 => 1
  | 6 => 33
  | 7 => 154
  | 8 => 213
  | 9 => 28
  | 10 => 1
  | _ => 0

def G23_pb : Nat → Nat
  | 5 => 6
  | 6 => 8
  | 7 => 8
  | 8 => 5
  | _ => 0

def G23_records : Nat → Nat
  | 9 => 0x4e040086006019b1ac00a9140142e4a038505409004d4002c26830105327018
  | 8 => 0x10d60ab49d21388efa1f5ef430d642f4f1847b7591bc7811483d98fa81f41b2d4b217347469ac1b469780becd3c89d90bb576325815e05b49ac6618d1441b363ed39dd3e055215d897a16b254938463b48bc8175c3ad290c6c65504187a71864b9ab67ea51e49208fc84f01132ec659546585fb24b7081f4a85321544472ed46c91a7e2175aa4e9b41bc69fd11d897976f23debc6b3b851c66ba27e561b38411394d551b5c1e2972e3e21eb67ed07944d127e03d70c1da710ac0c583f4b27ae58cdc6c5623efe7182e5e51a6c8009e86c97de3f79fbd86eb9eaec32500ba809d376e37565d86aa07c600634e81bc02f02fa18580a1e3cc9add05616df4e607ee4d026c8fcc13a81cc3110df853486e29704eb26c9bc641f54ad21f3400613d001500232c60f487551b624b0cf983b727c85ad27e801255930d86d982d03bc85d18ec9360133044e0f34c4b57e4ed9bb32c4155804d717200141bb52e10d194f98fd23fa96a04f797b42cd55626e31bdc5489fdc8d7
  | 7 => 0x24b464fa90ad89d63a2a4eb58e10a026c764ab2256e4d48384e53b5675a8169ea14da5e6e5f370a8caf6f9626b35202ad5ad6546a84155e0d1bf54046a32254204ae4b58062461e1d4f54f84b95d523d6e0e86854cc9b1c9527a7551d666bd350f9a3b611dea67a24463868df02a4a8c822d971699f858c2a343d970ecba1a406adc61b69a8d074cecaae4f920ee0a96ccbb7c4e1d9a9e896955b322d54109f0b5dd536daf264ea76b63a9d35c23792bb838a10b7d35979aac85705b2fc998392905555c355487378ed41d6d45ab22d1a5fcecb6fa9c6e3533928d51e48bb4c26900ae3ac4b8eab4b53b22a6476385adc3d590aaa05435b2a0a92b3a9d802688a4e3d4252c76faa9b2cd2e561ae0b4ea89a497637d39bd46bb82fcbdcb8eccf55c86b0ebf370e8d725803b8e1d59abe534876fa967dab1ed2896ac1a143d1a1ebba149eed55c39d
  | 6 => 0xd11e0ebf855ecab10153d5e87455aa2b30556d9288175b41abea5890eb3475ee9aea1d3d22a48b624fad475753e882142b4aeb1d485e88275d48ad4157f26a4c96225affc141
  | 5 => 0x6940
  | _ => 0

def G23_buckets : Nat → Nat
  | 5 => 1
  | 6 => 9
  | 7 => 39
  | 8 => 54
  | 9 => 7
  | 10 => 1
  | _ => 0

def G23_flag : Nat → Nat
  | 5 => 2
  | 6 => 512
  | 7 => 2048
  | 8 => 32768
  | 9 => 131072
  | 10 => 2
  | _ => 0

def G23_seedBits : Nat → Nat
  | 5 => 2
  | 6 => 10
  | 7 => 12
  | 8 => 16
  | 9 => 18
  | 10 => 2
  | _ => 0

def G23_seeds : Nat → Nat
  | 5 => 0x2
  | 6 => 0x1b141a050249e0a41001811
  | 7 => 0x67c06e01e1da01502004e0080011d100f14300c8970440950070b40020010ee0870018770020a202602a12802500285200a010826052024036002
  | 8 => 0x5000357160010017d0338003100c4013601cb0001026e00010138003f012300030015037b005a02fc008a000a0025018700030009000d000300c0009700250001000100a080d500100222007e016d000900c3002e8023002a80d50007000f00090001003d0002000c0005
  | 9 => 0x224bf9000160000a00060014c0185
  | 10 => 0x2
  | _ => 0

def G23_initial : List Nat := [0x70707070707070000ff00ff0000, 0xa0a0a0a0a0a0aff0000ff0000ff, 0x1919191919191900ff000000ff00, 0x24242424242424ffff00000000ff, 0x50505050505050000000ffff00ff, 0xa0a0a0a0a0a0a0000000ffffff00, 0xc0c0c0c0c0c0c0ffffff00000000]

def G23_idx : Nat → List Nat → Nat :=
  qIndex G23_N G23_buckets G23_flag G23_seedBits G23_seeds

def G23_benes : Nat := 0x7f11e1c24ec9c9380000000000026002c000e11fc00000000000000000000000000000000000000000

def G23_inputActions : Nat := 0x2e7015ac688

def G23_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G23_benes auto)

def G23_cacheKeys (i : Nat) : Nat := G23_initial.getD i 0

def G23_cacheValues (auto i : Nat) : Nat :=
  G23_cacheKeys (fld G23_inputActions 3 (7*auto+i))

def G23_act (auto : Nat) : Nat → Nat :=
  cachedAction G23_cacheKeys (G23_cacheValues auto) 7
    (fun w => qInputLookup w G23_initial) (G23_rawAct auto)

def G23_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 1 G23_initial G23_act G23_pb G23_records (10-s) j

def G23_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G23_act (i+1))

def G23_ori : List Nat → List Nat := orbitActions qPrefer G23_actions

def G23_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63]

def G23_rankPool : List Nat := [6576760, 6491598, 2177927, 5328540, 1076651, 2112649, 4202173, 5532311, 6375546, 2182523, 5381241]

def G23_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G23_S G23_N G23_idx G23_ori G23_coords 4 G23_rankPool s

def G23_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def G23_rows : List Nat := (([28, 34, 49, 52, 65, 74, 76] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 7 ([3, 5, 9, 6, 18, 40, 80, 96] : List Nat)).flatten
def G23_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G23_rows)
theorem G23_nonconstant : ∃ x y : Fin 7 → Bool, G23_f x ≠ G23_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_enc_goal : encL G23_f G23_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_proper : ∀ zs ∈ G23_xs.sublists, zs ≠ G23_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_good :
    qCachedGood (goal 56) 2 G23_initial G23_inputActions G23_benes := by
  unfold qCachedGood
  decide +kernel
theorem G23_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G23_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 2 G23_initial G23_inputActions G23_benes ws)
  exact qCachedOrient_run h G23_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_5_0 : span (G23_Z 5) 1 0 = true := by decide +kernel

theorem G23_checked_5 : span (G23_Z 5) 1 0 = true :=
  G23_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_6_0 : span (G23_Z 6) 33 0 = true := by decide +kernel

theorem G23_checked_6 : span (G23_Z 6) 33 0 = true :=
  G23_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_7_0 : span (G23_Z 7) 154 0 = true := by decide +kernel

theorem G23_checked_7 : span (G23_Z 7) 154 0 = true :=
  G23_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_8_0 : span (G23_Z 8) 213 0 = true := by decide +kernel

theorem G23_checked_8 : span (G23_Z 8) 213 0 = true :=
  G23_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_9_0 : span (G23_Z 9) 28 0 = true := by decide +kernel

theorem G23_checked_9 : span (G23_Z 9) 28 0 = true :=
  G23_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_check_10_0 : span (G23_Z 10) 1 0 = true := by decide +kernel

theorem G23_checked_10 : span (G23_Z 10) 1 0 = true :=
  G23_check_10_0

theorem G23_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G23_N s, G23_Z s i = true := by
  interval_cases s

  · simp [G23_N]

  · simp [G23_N]

  · simp [G23_N]

  · simp [G23_N]

  · simp [G23_N]

  · intro i hi
    exact span_ok G23_checked_5 i (Nat.zero_le i) (by simpa [G23_N] using hi)

  · intro i hi
    exact span_ok G23_checked_6 i (Nat.zero_le i) (by simpa [G23_N] using hi)

  · intro i hi
    exact span_ok G23_checked_7 i (Nat.zero_le i) (by simpa [G23_N] using hi)

  · intro i hi
    exact span_ok G23_checked_8 i (Nat.zero_le i) (by simpa [G23_N] using hi)

  · intro i hi
    exact span_ok G23_checked_9 i (Nat.zero_le i) (by simpa [G23_N] using hi)

  · intro i hi
    exact span_ok G23_checked_10 i (Nat.zero_le i) (by simpa [G23_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G23_initial_perm : G23_xs.Perm (G23_S 10 0) := by decide +kernel
theorem G23_no_run : ∀ s ≤ 10, ¬ MonRun (goal 56) s G23_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G23_S) (N := G23_N)
    (idx := G23_idx) (ori := G23_ori) (coords := G23_coords)
    (bw := 4) (pool := G23_rankPool) (cap := 10) (i := 0)
    G23_preserved G23_checked (by decide) (by decide) G23_initial_perm
theorem G23_no_small : ¬ HasMonoSize 7 G23_f 10 :=
  encoded_mono_exclusion G23_f G23_nonconstant 10 G23_rows G23_xs 56
    rfl G23_enc_goal G23_proper G23_no_run
theorem G23_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G23_f x) :
    11 ≤ C.size := mono_lower G23_f 10 G23_no_small C hmono hev
def G24_N : Nat → Nat
  | 5 => 2
  | 6 => 27
  | 7 => 82
  | 8 => 118
  | 9 => 18
  | 10 => 1
  | _ => 0

def G24_pb : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 7
  | 7 => 7
  | 8 => 5
  | _ => 0

def G24_records : Nat → Nat
  | 9 => 0x64300a11321606002007001048040170120440000a000804
  | 8 => 0x4d1c1c8a7ee05aa1442136814628603000c142214eb090385838ce443ed26ca13e84e4b04e5c1cf132005d10ec406cc055003d101ed0bc402e586ed4f4f01ee044f176a0ba40ac42ca40ea404ed02ee976f15ef956b08d1cdec024485f142ca9a7086e285e704b1020386ea03c00b420483016e1468894026b126d10503026e505005ca945002ea85ea0a4701e60c4c17e7088304cf064c25cc01c40be409c014e8000005b14e6b946f018303c8c2aa81a485ee43f181e4034011cc83b10aa486f1976782eb4e2b0fd015cc0ecf26aa03cf146b154c002318670348cbef4fe4136b0ae42cc417ef514c04f1
  | 7 => 0x1b685e9d0fa1812b849f4e07d004ac070c9001b05f1d81e4812e0c9aca0fec09c78231201b8112c881b4a22a881b9109120ba0d40eb4f2ac1ab80bb9016c6513790ae60eb905ef40bb482a8326b54cf1d14fc80ca2c9fb326f10ea0c9a880ac4a0ed504a2250eb81a0c5cc306b982ae404ace12ca26b143ad20826c0ee00ca0e12dc05a209ae005b5404a805b9a0ac60347a26e4c2b2800160ee4822d5083a8208f0eb68538e09c485c912cb900eb826accaf12043943888
  | 6 => 0x1aea7c1b03069417ab80e8081a2cae8908b34cec709a26069c81a245ea31a2f90c8d082044eae1774126a742a450ebc13aac22994ba0926ab37a9852ab
  | 5 => 0x13a981ac
  | _ => 0

def G24_buckets : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 21
  | 8 => 30
  | 9 => 5
  | 10 => 1
  | _ => 0

def G24_flag : Nat → Nat
  | 5 => 4
  | 6 => 512
  | 7 => 1024
  | 8 => 4096
  | 9 => 1024
  | 10 => 2
  | _ => 0

def G24_seedBits : Nat → Nat
  | 5 => 3
  | 6 => 10
  | 7 => 11
  | 8 => 13
  | 9 => 11
  | 10 => 2
  | _ => 0

def G24_seeds : Nat → Nat
  | 5 => 0x2
  | 6 => 0x10b00c35846060fc02
  | 7 => 0x1683c4dbc4282f0d8038010a287c0bc038210130860780c04a15403801
  | 8 => 0x600609c029c32a00e46f086002806e8210010006001005800406c01b09401800160cb056807005e00500d01c8002005
  | 9 => 0x40300300415bab
  | 10 => 0x2
  | _ => 0

def G24_initial : List Nat := [0x707070707070707070000ff0000ff0000ff, 0x9090909090909090900ff0000ff0000ff00, 0xa0a0a0a0a0a0a0a0aff0000ff0000ff0000, 0x141414141414141414ffff00ffff00000000, 0x707070707070707070000000000000ffffff, 0xa0a0a0a0a0a0a0a0a0000000ffffff000000, 0xc0c0c0c0c0c0c0c0c0ffffff000000000000]

def G24_idx : Nat → List Nat → Nat :=
  qIndex G24_N G24_buckets G24_flag G24_seedBits G24_seeds

def G24_benes : Nat := 0xaf99932f48495192b2264408d2132e0000000027b57ccc998256833752e95d283009c0400000000183ae766402098c1aba774ae941647ccc000000522c3173b320004c996dc5b8b7159112e000000002915ceb700025865f4b2f65ebbd74ad913240000016e27b00000195a4647c8f80000047c199220000000016e2dc000cc596d28bd57a6f4d2764409c000005b800000000000000000000000000000000000000000

def G24_inputActions : Nat := 0x283ba221dd0a0f58887acba3286b1942e8d11ac688

def G24_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G24_benes auto)

def G24_cacheKeys (i : Nat) : Nat := G24_initial.getD i 0

def G24_cacheValues (auto i : Nat) : Nat :=
  G24_cacheKeys (fld G24_inputActions 3 (7*auto+i))

def G24_act (auto : Nat) : Nat → Nat :=
  cachedAction G24_cacheKeys (G24_cacheValues auto) 7
    (fun w => qInputLookup w G24_initial) (G24_rawAct auto)

def G24_S (s j : Nat) : List Nat :=
  qParentAction 10 8 3 0xfbdd7cd2cef3ae3eb2aa26b9c69859478c28818408 8 3 G24_initial G24_act G24_pb G24_records (10-s) j

def G24_actions : List (Nat → Nat) :=
  (List.range 7).map (fun i => G24_act (i+1))

def G24_ori : List Nat → List Nat := orbitActions qPrefer G24_actions

def G24_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 73, 74, 75, 76, 77, 78, 79]

def G24_rankPool : List Nat := [241447241, 201441743, 134264107, 135512494, 272738604, 67252586, 206650832, 134330733, 270744941, 275982636, 206585296]

def G24_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 72 G24_S G24_N G24_idx G24_ori G24_coords 5 G24_rankPool s

def G24_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def G24_rows : List Nat := (([17, 18, 20, 33, 42, 44, 65, 74, 76] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 9 ([3, 5, 9, 6, 24, 48, 80, 96] : List Nat)).flatten
def G24_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G24_rows)
theorem G24_nonconstant : ∃ x y : Fin 7 → Bool, G24_f x ≠ G24_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_enc_goal : encL G24_f G24_rows = goal 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_proper : ∀ zs ∈ G24_xs.sublists, zs ≠ G24_xs →
    (covUp 72 zs &&& lo 72) ≠ lo 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_good :
    qCachedGood (goal 72) 8 G24_initial G24_inputActions G24_benes := by
  unfold qCachedGood
  decide +kernel
theorem G24_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 72) s ws) : MonRun (goal 72) s (G24_ori ws) := by
  change MonRun (goal 72) s (qCachedOrient 8 G24_initial G24_inputActions G24_benes ws)
  exact qCachedOrient_run h G24_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_5_0 : span (G24_Z 5) 2 0 = true := by decide +kernel

theorem G24_checked_5 : span (G24_Z 5) 2 0 = true :=
  G24_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_6_0 : span (G24_Z 6) 27 0 = true := by decide +kernel

theorem G24_checked_6 : span (G24_Z 6) 27 0 = true :=
  G24_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_7_0 : span (G24_Z 7) 82 0 = true := by decide +kernel

theorem G24_checked_7 : span (G24_Z 7) 82 0 = true :=
  G24_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_8_0 : span (G24_Z 8) 118 0 = true := by decide +kernel

theorem G24_checked_8 : span (G24_Z 8) 118 0 = true :=
  G24_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_9_0 : span (G24_Z 9) 18 0 = true := by decide +kernel

theorem G24_checked_9 : span (G24_Z 9) 18 0 = true :=
  G24_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_check_10_0 : span (G24_Z 10) 1 0 = true := by decide +kernel

theorem G24_checked_10 : span (G24_Z 10) 1 0 = true :=
  G24_check_10_0

theorem G24_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G24_N s, G24_Z s i = true := by
  interval_cases s

  · simp [G24_N]

  · simp [G24_N]

  · simp [G24_N]

  · simp [G24_N]

  · simp [G24_N]

  · intro i hi
    exact span_ok G24_checked_5 i (Nat.zero_le i) (by simpa [G24_N] using hi)

  · intro i hi
    exact span_ok G24_checked_6 i (Nat.zero_le i) (by simpa [G24_N] using hi)

  · intro i hi
    exact span_ok G24_checked_7 i (Nat.zero_le i) (by simpa [G24_N] using hi)

  · intro i hi
    exact span_ok G24_checked_8 i (Nat.zero_le i) (by simpa [G24_N] using hi)

  · intro i hi
    exact span_ok G24_checked_9 i (Nat.zero_le i) (by simpa [G24_N] using hi)

  · intro i hi
    exact span_ok G24_checked_10 i (Nat.zero_le i) (by simpa [G24_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G24_initial_perm : G24_xs.Perm (G24_S 10 0) := by decide +kernel
theorem G24_no_run : ∀ s ≤ 10, ¬ MonRun (goal 72) s G24_xs := by
  exact noRun_from_barFastOrbit (k := 72) (S := G24_S) (N := G24_N)
    (idx := G24_idx) (ori := G24_ori) (coords := G24_coords)
    (bw := 5) (pool := G24_rankPool) (cap := 10) (i := 0)
    G24_preserved G24_checked (by decide) (by decide) G24_initial_perm
theorem G24_no_small : ¬ HasMonoSize 7 G24_f 10 :=
  encoded_mono_exclusion G24_f G24_nonconstant 10 G24_rows G24_xs 72
    rfl G24_enc_goal G24_proper G24_no_run
theorem G24_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G24_f x) :
    11 ≤ C.size := mono_lower G24_f 10 G24_no_small C hmono hev
def G25_N : Nat → Nat
  | 6 => 19
  | 7 => 84
  | 8 => 131
  | 9 => 20
  | 10 => 1
  | _ => 0

def G25_pb : Nat → Nat
  | 5 => 5
  | 6 => 7
  | 7 => 8
  | 8 => 5
  | _ => 0

def G25_records : Nat → Nat
  | 9 => 0x6a00048a990a20a612a4d01aa540880207200c0a81911a21444801
  | 8 => 0xb61130b126e88029e01020d576e10894bee5386178506e59489577007eb450549660ee74a640e87110998840cf00282880b078209691467040b92810000860c91c31309127044f18207018283031a058507020a860b0780c2e104e5998f45cb0e47d5010be143eb0c7117501306880507c507e50305c3cb09c347051b810e0f00010830c70c04e1978f07cb03800b0986020c7056840202198414e718040302a08e0800040003008605457012f0860409e302e305f009e6082106009784c80c148b046144f0928f001090f0036f45eb0a03c9e400020e671a2e82c30c6e520302e5860d84c5020c0cf105e5128e02c591e345c5040a06c50d0f0413d2890313124e12860280
  | 7 => 0xc403848491403e1b1c00413a012f8a89e8091d000f8581128272350a08e1285e0f27c0e1a07c24138692c23e561745c0105828170d8364f00095060081f278264902c420d8f11710e265bc9ea429828170909702c3c00079e01b06c1e5b5c02a0d92449308603d45cb60596d170e0a68047c1a27c08130203e1c0be0505804673c0260d07c420d848752dc263c84c380d871070685a0611e05099e24431050028bc340b93c47050222606caa05970513f1125e02cf021c08130900b4749e2aa2056751ac1052
  | 6 => 0x612653c4d131990cc04f0603c10452c4bcea1c3749ccc2b334bc03071442c11371043c754f3002c746f3a
  | _ => 0

def G25_buckets : Nat → Nat
  | 6 => 5
  | 7 => 21
  | 8 => 33
  | 9 => 5
  | 10 => 1
  | _ => 0

def G25_flag : Nat → Nat
  | 6 => 512
  | 7 => 1024
  | 8 => 2048
  | 9 => 8192
  | 10 => 2
  | _ => 0

def G25_seedBits : Nat → Nat
  | 6 => 10
  | 7 => 11
  | 8 => 12
  | 9 => 14
  | 10 => 2
  | _ => 0

def G25_seeds : Nat → Nat
  | 6 => 0x90b41b84d1e
  | 7 => 0x1706160302e8a90391441c0730160a0030390520700482400221803005
  | 8 => 0x85e32000903702c09c0038378040d601e00201d0390220224e803b04600301a00300e0040020862aa02900119f20f00a003
  | 9 => 0x125e00ec0080030003
  | 10 => 0x2
  | _ => 0

def G25_initial : List Nat := [0x707070707070700ff000000ff00, 0x9090909090909ff00ffff0000ff, 0x121212121212120000ff00ff00ff, 0x24242424242424000000ffff00ff, 0x50505050505050ffff00ff000000, 0xa0a0a0a0a0a0a0ffffff00000000, 0xc8c8c8c8c8c8c800000000ffff00]

def G25_idx : Nat → List Nat → Nat :=
  qIndex G25_N G25_buckets G25_flag G25_seedBits G25_seeds

def G25_benes : Nat := 0x1ee438778254820991f0000000011f0250003f87f10e21c3bc3780c05219800000000020118001fc0008f0d20001a0040080000000000001000c000001a400000000000000000000000000000000000000000

def G25_inputActions : Nat := 0x9ca706ac3b4a991ac688

def G25_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G25_benes auto)

def G25_cacheKeys (i : Nat) : Nat := G25_initial.getD i 0

def G25_cacheValues (auto i : Nat) : Nat :=
  G25_cacheKeys (fld G25_inputActions 3 (7*auto+i))

def G25_act (auto : Nat) : Nat → Nat :=
  cachedAction G25_cacheKeys (G25_cacheValues auto) 7
    (fun w => qInputLookup w G25_initial) (G25_rawAct auto)

def G25_S (s j : Nat) : List Nat :=
  qParentAction 10 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 2 G25_initial G25_act G25_pb G25_records (10-s) j

def G25_actions : List (Nat → Nat) :=
  (List.range 3).map (fun i => G25_act (i+1))

def G25_ori : List Nat → List Nat := orbitActions qPrefer G25_actions

def G25_coords : List Nat := [0, 8, 16, 24, 32, 40, 48, 56, 57, 58, 59, 60, 61, 62, 63]

def G25_rankPool : List Nat := [5532536, 5381788, 3279789, 5515927, 5389774, 3284363, 2121338, 5459081, 5467257, 4328622, 5450375, 4349306]

def G25_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 56 G25_S G25_N G25_idx G25_ori G25_coords 4 G25_rankPool s

def G25_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def G25_rows : List Nat := (([14, 17, 28, 42, 70, 97, 98] : List Nat).flatMap fun x => List.replicate 8 x) ++ (List.replicate 7 ([3, 5, 9, 18, 36, 72, 48, 80] : List Nat)).flatten
def G25_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G25_rows)
theorem G25_nonconstant : ∃ x y : Fin 7 → Bool, G25_f x ≠ G25_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_enc_goal : encL G25_f G25_rows = goal 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_proper : ∀ zs ∈ G25_xs.sublists, zs ≠ G25_xs →
    (covUp 56 zs &&& lo 56) ≠ lo 56 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_good :
    qCachedGood (goal 56) 4 G25_initial G25_inputActions G25_benes := by
  unfold qCachedGood
  decide +kernel
theorem G25_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 56) s ws) : MonRun (goal 56) s (G25_ori ws) := by
  change MonRun (goal 56) s (qCachedOrient 4 G25_initial G25_inputActions G25_benes ws)
  exact qCachedOrient_run h G25_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_check_6_0 : span (G25_Z 6) 19 0 = true := by decide +kernel

theorem G25_checked_6 : span (G25_Z 6) 19 0 = true :=
  G25_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_check_7_0 : span (G25_Z 7) 84 0 = true := by decide +kernel

theorem G25_checked_7 : span (G25_Z 7) 84 0 = true :=
  G25_check_7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_check_8_0 : span (G25_Z 8) 131 0 = true := by decide +kernel

theorem G25_checked_8 : span (G25_Z 8) 131 0 = true :=
  G25_check_8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_check_9_0 : span (G25_Z 9) 20 0 = true := by decide +kernel

theorem G25_checked_9 : span (G25_Z 9) 20 0 = true :=
  G25_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_check_10_0 : span (G25_Z 10) 1 0 = true := by decide +kernel

theorem G25_checked_10 : span (G25_Z 10) 1 0 = true :=
  G25_check_10_0

theorem G25_checked (s : Nat) (hs : s ≤ 10) : ∀ i < G25_N s, G25_Z s i = true := by
  interval_cases s

  · simp [G25_N]

  · simp [G25_N]

  · simp [G25_N]

  · simp [G25_N]

  · simp [G25_N]

  · simp [G25_N]

  · intro i hi
    exact span_ok G25_checked_6 i (Nat.zero_le i) (by simpa [G25_N] using hi)

  · intro i hi
    exact span_ok G25_checked_7 i (Nat.zero_le i) (by simpa [G25_N] using hi)

  · intro i hi
    exact span_ok G25_checked_8 i (Nat.zero_le i) (by simpa [G25_N] using hi)

  · intro i hi
    exact span_ok G25_checked_9 i (Nat.zero_le i) (by simpa [G25_N] using hi)

  · intro i hi
    exact span_ok G25_checked_10 i (Nat.zero_le i) (by simpa [G25_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G25_initial_perm : G25_xs.Perm (G25_S 10 0) := by decide +kernel
theorem G25_no_run : ∀ s ≤ 10, ¬ MonRun (goal 56) s G25_xs := by
  exact noRun_from_barFastOrbit (k := 56) (S := G25_S) (N := G25_N)
    (idx := G25_idx) (ori := G25_ori) (coords := G25_coords)
    (bw := 4) (pool := G25_rankPool) (cap := 10) (i := 0)
    G25_preserved G25_checked (by decide) (by decide) G25_initial_perm
theorem G25_no_small : ¬ HasMonoSize 7 G25_f 10 :=
  encoded_mono_exclusion G25_f G25_nonconstant 10 G25_rows G25_xs 56
    rfl G25_enc_goal G25_proper G25_no_run
theorem G25_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G25_f x) :
    11 ≤ C.size := mono_lower G25_f 10 G25_no_small C hmono hev
def G26_N : Nat → Nat
  | 4 => 1
  | 5 => 27
  | 6 => 137
  | 7 => 334
  | 8 => 400
  | 9 => 158
  | 10 => 9
  | 11 => 1
  | _ => 0

def G26_pb : Nat → Nat
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | 8 => 8
  | 9 => 4
  | _ => 0

def G26_records : Nat → Nat
  | 10 => 0x100220000028804d0004a1540068059
  | 9 => 0x61000d5803c2003d00168100300000800a44006910857523200224862f20051000b2001880030a206d0002200385402a880710404ae005094038104c00052640540002180297312a004040008b908270004a00444006800197001a6a0e40034918930000640039002528015411da4a0d40042900512002268094c6130901d300ba202e54008a001340172e00bc045a280211009a000350000900112116aa00549030800192816ae0008800ca000620002ea1540002a40b47003ea03748000a0001501fa0837540329309d000ba404148014a004d5a01ea007440109800d74860400608030900fc001321403c0841b800200020480a04044b800100000003848025a800b30002600755002a8c5f40022a4055c000c000b7000a600091012a801b500624000086138800f3012a400ac000c3d0600791a0025c0010a80dd40000a406400269002920036ea454003180031000022004100011802950122001451012a10847020013174000f8888d200a2a028408100a0604
  | 8 => 0x9210809b9d00212b804f0800a2d24070f0034b4a4661821046a8195a407f0580865101152800c66c028c880517c192cbca0cd0d8340e00000e0026e8042a2002515804d6900e3360165f0018c880107c211ca280a1400281c80100800acf4034a4c0439b44fa633128c428d5a500f8f004b01014e7402093142ab4807a0251fb3600364405cbe0076470203220210840001f804a01001cbe025d89e2f40200e18013e74004cc680b3624db1a00e2d24225a503728809684009c8e006cc402707000a67005635003dc4028cd9058392040420038e40481f8011910192d2317c2200702a0b991019e7541a0e801b1080047c81a4ec0028a462f09101b39001934004e5d00f108088310094320138a80084300c991a0a06c42b8480099ca8661200b336309c3800d8400865f00401c00418400d31b0956908bc590039c883007004a0214767404018a42f4200822e046e3c404c20461060016940132d24055f00431c82c591801c3a037e1223042004e5e00e05802b9fc0278700f64e801ed24210f802549b29d69017af800408422f960089725480a0a3f26e00718804d914050502428080441c80173950703c3098380079c8c26244172d28215c8136b4989a6318be7282d5f28341b042621017ae541e0fd5203080841e0062d203b938008b4a0b5695118729370d805eb4888571010e7201a66c0271c80d07440c0e80000d800744826f840030420165a40632f806f2c00003a0270fc07d0580217c010504a30a0011f4c80897c404322025ccc008be00557c0051348075f00434a0c2e2e481c9249b9fc06d12a0b44f801f0880982685a045016483126c490387c04228000191710ad201786000021904c6900265801793862f1c808439204d12012a5005c1c9015690182f80100840413028fc62041c8c02f5c500728800a9a0110e80040e68381b01019b004528a0b6440081e201d9110bf08007c840480422765131342088f99d47eb4800e0a0104480128c553c3a086a80801e620285a484727205e512098740220fc01931800b9a803c3c02a1d004f3f800e152006d242098c04202806f43801d08413004000028cb65f007322a1566e00f41003721000537003c7461392202f00a030500165c400710801a35045f36408078162b488a03f00233682e5ca0120280c28a01651200e66c0251d90543f21087e01b8b08074a40100580400a4065a401d8380627e15507e8085a4017a1804d9b0000420281d000d0420659b710af82230fc85183a4c036a0a000317cc40093280396900a06e6249884332fa8066920a87c89b66c0444202765f021c0400c0dc63305004a8aa0c040a8d64405ec8902050405cce0305a603f0900166d40500a02d97801407000e12a01e7e00391007f2720602c009e0a315e1101b338c577ca0503a89d8600301c88c8365480783199960133382361e00dee80150380481c805439a01e000405a42139090c216001ee8719a5000733804a66009e425258610023480887c00966280a09004705004a0c506b37007a66830198007912026f80070850430c000f12402cce20e084043328c577100300a025c000261b81183440504201287000b9f808308
  | 7 => 0x105504001d00011115014030004f130124cb401efa00146e009d0552043700b34a01f673190c14084c7921451e103d3e01100850cc4ba01d70004f01405cc504ceb8646c3f009d37012c44a01ca8183cf6801d88000b222130b8009540384d36006c9a446cc5016d7d416559801c08803cc551b883084c5b704c3f01f74a809cba00475070bcd501103060dd42190d76006d4aa0508301f54a801c76803c61003cc240acf3984c31104c2151f88b1054cba01c33001666801c4951f577783ccb197c7600e51760cd0f01051949b4ff60d0b5006ca000260852045308bcd858ad88004f22057ec3983d6a604618010d7801fd0f0c6d6a1474c3058cc220188360cc30a01eb88130b500994d009e5920300f406c9e084c29409e66001d0500143692047d006c5b002002802d3700e412446c31505c3118bc3c05fcba56256c802d1a212cf204e47f0104cd183e9700cf4a002d3609b414084c9ea0fc0c04e49218bcf204dd78384c5102256b20982801f683001c5ca02c426040fa00153778acba09b4d4009440801ccb403c2904e4f101115c001b2201b92200014a005f01051e83601eb5005c7741b41601043300955249b4cb084cb080c002001cd8184c85a020a800e47d801c68446d5800332200210210c47800dcf3014caf012d61601f3d384c6b04d8b500ed7800a42a183ea8006d1b18bd7800a097183f746060fa206d5e21045e503d69409ce400200878bccd014d2e60d03050594a190c7651f423802d4ea0417418af0218af5c0094f1384d3800309701249d40ec6890ac4960cd75a0dd0f01041300215c4909502098b500275c009caa190e0f20988b00ce30006c7901644401303041757d41653e21044f010538801d040098a8a05c39983ca2010cd8191c49117cc252049308ae30005cb9846ca219711d00947200be02a02c62801e02984d6f05d083a01ef800614a409cc2012c760053224047012104cf203d36184d1f384d1a44dd88002e97809d0f146d1f01058f51c901001ce800dc2e203d3818ae59401c9e4040a8403ca0009d4e38bc2649791d920577a0acc20224eb013e8300194a58bc82802c13783d0421046f31255218aeb800142a846c422140b8084ca0a02c36184d37012d88402c1e18af1501f94a802c3fb2055708bcf301041b089e02801409801c4b40dcdc184c26284d5e203d5e01f90160b123046d19801f5c001c2655f50b51f47d784d70105d6a403cb000714a003d0700c4d100b0a8010494096d1d2104e9801e080096f8783d7400cd21005c93503d1f009974801c02105d4b584c13210462001ea8046d69984c330094c8006cb0983c42983ca8001cf3046d4b40cc08484c1b0094f8010d05801d8f01bb22005cba116c6e013008190c6e000322401c32
  | 6 => 0x801c4300941755f45d0094bc802c3801f542404ceb983d36801c5c801c1111b52a801cf5845d1301bc9c983c5f51b50eb09c2f00ce2b205c382094cb01bd33006d06983c8b0970f8602d11409d23509c3755f41a801c7050ace220ccc7801c8201b41f118cce40cc3d483d11009540283c38604cc66050c6801c94005d42483c45a05c30983c5ba01d2000dcf9605d1048ac78405c52004c9e4036f8006d23801cb5983cf538ace0011c82401d38056d21083c5280ccd3012c0400202ba01c31111cd0416416005cce801d18005cc7801d30801c51605ccb483ca9a01ca580bc800d6d0841c47c009411201c7401cc9704be2b604d1a604c06801c08016cf060d11b011ce2104cff702cd011201d005d06801cd201b702644c97605ca9189e2b60cc3ca01c8580bc0341081d083d06645d1198acdca82cff68ac84012d06845c23004ec660cd20609c8401fd10192cd300ae0ba01d1398acf3401c78801d4a801c1e18acf5a01cd4020cda045d22801c03009483601c8478accd801d0d801c5a01bcb4604c7c005cad50441f0020090d6d0340349e016cce096c9c
  | 5 => 0x8179461130fb05e29110cc202f96980714848e2c882c2480989502f1608b633482c3f0038c9813160cb616882c4a80b9a425b1140265a404c2508981142728101e61a01c70b0581035b05a01e80
  | 4 => 0x10c0
  | _ => 0

def G26_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 35
  | 7 => 84
  | 8 => 100
  | 9 => 40
  | 10 => 3
  | 11 => 1
  | _ => 0

def G26_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 2048
  | 7 => 1024
  | 8 => 4096
  | 9 => 4096
  | 10 => 32
  | 11 => 2
  | _ => 0

def G26_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 12
  | 7 => 11
  | 8 => 13
  | 9 => 13
  | 10 => 6
  | 11 => 2
  | _ => 0

def G26_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x2f7b0133045f8d
  | 6 => 0x141f04b24c04f05b0040bf04e14108985b14101900219b06400e0040010bc00100601001000304400280b10b00602300101502b
  | 7 => 0x2f458c1af1f80f29700748a2386a0199e4e347b00311c02cbc00a92401c29866a9c0040d87d0040a07f32a0c60c4610982151bd398b625c0240080c01c0440980400c020c90ac04c028190fd0301dc340020cc0ec0180702200c0081401c0440e805024074208050080040081a00410a0780f
  | 8 => 0x84d807c0c7006462400e002003800975a02831401140422af001966c02a00300a003c19a0a204582d004e01400846400dc1908c80fb400a0420cc80cc00400c8bf8f782e8001020c5bc38d15e017002c07c005164007c01200489e0430072005001005002210d09184500ef12787680e408402900a800c09815c042803a155190001818c01800901e800c02201600182e40940e783880141d20c5006000400200e
  | 9 => 0x204b419804a27d000494002a73e966c0260c1001420c5b400200100484c200884f003801e09a817406c04003501d80040540010008048006028001000c064005
  | 10 => 0x163c2
  | 11 => 0x2
  | _ => 0

def G26_initial : List Nat := [0x7e3f1f8fc7e3f1f8fc7e000000000000000001ff, 0x8241209048241209048200ff803fe00ff803fe00, 0x84422110884422110885ff007fc01ff007fc0000, 0x10884422110884422110800007fffe00007fffe00, 0x110884422110884422111ffff80001ffff8000000, 0x221108844221108844220000000001ffffffffe00, 0x241209048241209048241ffffffffe00000000000]

def G26_idx : Nat → List Nat → Nat :=
  qIndex G26_N G26_buckets G26_flag G26_seedBits G26_seeds

def G26_benes : Nat := 0x852dc1f9c82a694cafb5f5beb4c69c48177ad18a4c2876b0e9febdfacf82b04e09accda1f04586aee521349e9ab2f2a558fc4d89712d8ea932ea6a4932c709632cce592ea2915e4bc778e91b777a133229b96864d05ffc83779562ff5fdbfb55da4480776e996dc308871c9c3cc1a757caf8df1a77315c14778b6ba218c9c6c93bab0d42c0580700d41ac53b1ee4ad8950be1db746e72fa6bdd8baf75e76cbb7decf62843c8b4dadeb4988096cb1f63dc7b6c5c94b37b0f4a04b9b90ee626fd5ab0b85b0ae15afd5666e35f90ce562cc3e90944ab9dacc9191f23dbaae94463f42e810e7e3a4d37cd476d3e36c6b8d6d351c7cb33e39b976df24271d216a36e723645c8b6e1a95209bb21605b6a75525a86d6eae178af0de1a335be8649773502a3147d9bce4e8f5a9c718df1bda8a3ed127147a7af1921b4c4820ec2c261ac33866c1bc281d2f6293db6872ae61cd04cf462f05dfbbf45dc74d29852c616c11890dba44b7fa6f7c2f7defa6cec63cbe48891459e3d46a6ebe5a58cc4988f11d8d946eadb63508590363fc4765341292de6bcb796925037f5156473696ab2a5da4eaac160b0e61bc37606aece67592a15c34d919385d729c5bf656ca5943c613dd6ce0916b75aa4a46b33aea3d99c598af15d98a913a5e6ca17aad31bb4356c34027edcdb99731a2cfc7f30cdaf43d7931b5f84ca7c7573005ffbff56decccb7d717e00c407532967cb99b358bb16e2db36e9e7c4a07e2db5e2c6c681336a6d78c2183f07d79a9d3259c45e8010adff48fa115a2bae04c0780eb1d6ba0f1c5e2182883236124d67b564714627c4f641c8cd88b922233c3f89f3028d539a6b71ee35c666b4ce8dcb984519a263ec95d43a7d5bcc9592724dbb9ef43e533be89713a3dbd170d36ebde12c23846bd4d170af0e3c44d8552c9bace8aa93cafd5f9bf33c6a9ce46c527e03c2773911a4536567772ee55ca668fca3ac687d103e11be98f912698571c1982f05d72a5f0e63b37b8190822bcc6922d76a25f4be77cea1b5c8e12de304126852b1be4e7abf51b04607c0f516af4e56c727634b3a6c0e3e2ec13a5d7baf6deda5a8ea10a656f11ad9f34b945452b6dabc8990f21daaad944e5533f8d4cce22cbf9254f69f5d1ba1741db53c8df2e20fc6e8c72d5adcc86f4d3ee7dceb9cd39bccc76b529de546176f0e27fb47673726e45c86b0fe280c5678ef2a2a3c888540ab25b5ca594728dc4acb3fa1bbb97d50d1f3bd36ceecec9e29c538a6c93b253ad99e33567212c1bf4daaa554303605c0b53ea8cd96fb2bdc438d61f26a854fb9e95aab4d694653be84c9961ce21e0bba96d442785c1ca994f29dc09e742e4dad577000000000000000000000000000000000000000000

def G26_inputActions : Nat := 0x29cb822e5c0a8ee08c77070ab84655c1c46e11a37029cd422e6a0a8f508c7a870ad44656a1c47511a3a82ae70237380ad5c08eae0b8a706a5382e45c1aa2e02ae8c237460ad6308eb18b8a8c6a5462e4631aa31872e28477141cd4a11ea50b9c286ae142e8ca1ac65072e44477221cd5111ea88b9c446ae222e8d11ac688

def G26_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G26_benes auto)

def G26_cacheKeys (i : Nat) : Nat := G26_initial.getD i 0

def G26_cacheValues (auto i : Nat) : Nat :=
  G26_cacheKeys (fld G26_inputActions 3 (7*auto+i))

def G26_act (auto : Nat) : Nat → Nat :=
  cachedAction G26_cacheKeys (G26_cacheValues auto) 7
    (fun w => qInputLookup w G26_initial) (G26_rawAct auto)

def G26_S (s j : Nat) : List Nat :=
  qParentAction 11 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 6 G26_initial G26_act G26_pb G26_records (11-s) j

def G26_actions : List (Nat → Nat) :=
  (List.range 47).map (fun i => G26_act (i+1))

def G26_ori : List Nat → List Nat := orbitActions qPrefer G26_actions

def G26_coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 72, 81, 82, 83, 84, 85, 86, 87, 88, 89]

def G26_rankPool : List Nat := [134300012, 235158857, 134331818, 167822638, 268584270, 272644529, 170930544, 236988719, 67323341, 235061548, 168018219, 67256747, 67157354, 33735981, 33635657, 201409966, 134299980, 268648812, 100910477, 201506090, 167984585, 100941257, 100712812, 268680586, 33669419, 234997134, 134497741, 201605451, 134267308, 100810153, 234964334, 100844909, 33800651, 167855438, 100810121, 201475470, 67157418, 201409902, 268517804]

def G26_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 81 G26_S G26_N G26_idx G26_ori G26_coords 5 G26_rankPool s

def G26_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def G26_rows : List Nat := (([1, 42, 44, 50, 52, 74, 76, 82, 84] : List Nat).flatMap fun x => List.replicate 9 x) ++ (List.replicate 9 ([3, 5, 9, 17, 33, 65, 6, 24, 96] : List Nat)).flatten
def G26_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G26_rows)
theorem G26_nonconstant : ∃ x y : Fin 7 → Bool, G26_f x ≠ G26_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_enc_goal : encL G26_f G26_rows = goal 81 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_proper : ∀ zs ∈ G26_xs.sublists, zs ≠ G26_xs →
    (covUp 81 zs &&& lo 81) ≠ lo 81 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_good :
    qCachedGood (goal 81) 48 G26_initial G26_inputActions G26_benes := by
  unfold qCachedGood
  decide +kernel
theorem G26_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 81) s ws) : MonRun (goal 81) s (G26_ori ws) := by
  change MonRun (goal 81) s (qCachedOrient 48 G26_initial G26_inputActions G26_benes ws)
  exact qCachedOrient_run h G26_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_4_0 : span (G26_Z 4) 1 0 = true := by decide +kernel

theorem G26_checked_4 : span (G26_Z 4) 1 0 = true :=
  G26_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_5_0 : span (G26_Z 5) 27 0 = true := by decide +kernel

theorem G26_checked_5 : span (G26_Z 5) 27 0 = true :=
  G26_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_6_0 : span (G26_Z 6) 137 0 = true := by decide +kernel

theorem G26_checked_6 : span (G26_Z 6) 137 0 = true :=
  G26_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_7_0 : span (G26_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_7_256 : span (G26_Z 7) 78 256 = true := by decide +kernel

theorem G26_checked_7 : span (G26_Z 7) 334 0 = true :=
  (@span_join (G26_Z 7) 256 0 78 G26_check_7_0 G26_check_7_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_8_0 : span (G26_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_8_256 : span (G26_Z 8) 144 256 = true := by decide +kernel

theorem G26_checked_8 : span (G26_Z 8) 400 0 = true :=
  (@span_join (G26_Z 8) 256 0 144 G26_check_8_0 G26_check_8_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_9_0 : span (G26_Z 9) 158 0 = true := by decide +kernel

theorem G26_checked_9 : span (G26_Z 9) 158 0 = true :=
  G26_check_9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_10_0 : span (G26_Z 10) 9 0 = true := by decide +kernel

theorem G26_checked_10 : span (G26_Z 10) 9 0 = true :=
  G26_check_10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_check_11_0 : span (G26_Z 11) 1 0 = true := by decide +kernel

theorem G26_checked_11 : span (G26_Z 11) 1 0 = true :=
  G26_check_11_0

theorem G26_checked (s : Nat) (hs : s ≤ 11) : ∀ i < G26_N s, G26_Z s i = true := by
  interval_cases s

  · simp [G26_N]

  · simp [G26_N]

  · simp [G26_N]

  · simp [G26_N]

  · intro i hi
    exact span_ok G26_checked_4 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_5 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_6 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_7 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_8 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_9 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_10 i (Nat.zero_le i) (by simpa [G26_N] using hi)

  · intro i hi
    exact span_ok G26_checked_11 i (Nat.zero_le i) (by simpa [G26_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G26_initial_perm : G26_xs.Perm (G26_S 11 0) := by decide +kernel
theorem G26_no_run : ∀ s ≤ 11, ¬ MonRun (goal 81) s G26_xs := by
  exact noRun_from_barFastOrbit (k := 81) (S := G26_S) (N := G26_N)
    (idx := G26_idx) (ori := G26_ori) (coords := G26_coords)
    (bw := 5) (pool := G26_rankPool) (cap := 11) (i := 0)
    G26_preserved G26_checked (by decide) (by decide) G26_initial_perm
theorem G26_no_small : ¬ HasMonoSize 7 G26_f 11 :=
  encoded_mono_exclusion G26_f G26_nonconstant 11 G26_rows G26_xs 81
    rfl G26_enc_goal G26_proper G26_no_run
theorem G26_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G26_f x) :
    12 ≤ C.size := mono_lower G26_f 11 G26_no_small C hmono hev
def G27_N : Nat → Nat
  | 4 => 1
  | 5 => 41
  | 6 => 315
  | 7 => 947
  | 8 => 1320
  | 9 => 481
  | 10 => 18
  | 11 => 1
  | _ => 0

def G27_pb : Nat → Nat
  | 4 => 6
  | 5 => 9
  | 6 => 10
  | 7 => 11
  | 8 => 9
  | 9 => 5
  | _ => 0

def G27_records : Nat → Nat
  | 10 => 0xbd0b90590020210c101d8310b501900482d01585501100000d001
  | 9 => 0x10db11006864840a4100f0015000d9e0d5c042101910300c10491f8a0154c36942d460b270617018aa255e0c6d05958128c2452122a0864c46c43a421430838091b0414901d2d42d382cbc265e0ac906188748e175d13b00c55874943056063004d8a181a155816b001f0c2ea40c4f0aaa82868069a234205110113810b816470ba30891838c20d5002240172c42813b581c2d0a11c38c418520d30236583cb024140029c5d6814b820ce0525019282c941a5509a983568019721da06260b5081db00ad4032b00738468c16120030016581090084e0c700111428c0018e00870012012b8056111a5018300c441b6106a90544018ae08060022803383ab01c1e17268c84842b42e56192348f4880b4040c0720a356080402f4e91ad0e9486ec60812173082d626ebc2d518baf835800ca03252032008c18480c0a4246eb0024c0f2408560b290581810b4166092a70e940303c210311ab0911833c0185e17210696843a63f541d2b00d491b8413c307280698860980e42072901858748117d214270714802400e4e0e230c96814901c4c01b10956836a42e5000d1101781414324109b0820581cbc2d4003e90a1080f2c2562122084d3e43bc2d101723015381cb416620329091684e98234c1129099884e8d375a1120101800810004003a00658c4ebcb1d202a5c2728439c05441429430585e1c284097ab8553c1a9c405602110c98036a819600a21115484cb61b42122f06d1c1cb8046122b009188009e155e10af0182816bc00a201a20b90070a8046203c10155815bc074684e10a16c428e90090dab1058e2eb0224f06a309c1836b60d4000100e97c289c0446233008d4844c01c43070b86550429c1a5600600e9600c8424e183ef002180f9c074201b08fd6800441c4e03eb03d621844066001a40590c49bc1c5645ec85d4070c4146202d10610874b80e5601a702b8074c4225b1e310850812a4305913a70612c1abc174a112a8fc684424004b07088c518649e9d62043088d00641c0e46063110150488415500a68820082fac225f84c50594016c0184603b00193a6e34224313a90280e2ea8065e122502f580b1406620caba39601cc0075e052d0fc80809c00a0082c021482ec41a4f0a29085804ac017420021429784a982ce10ab08c504500c0a52062f0550808a424db1db106d305004009c1c2f023484e800a4602268798884c42f4c072a001305291095e0e6c0c9580ea4b1920ab18034c50bf0983990c00158369c085e00310023a6da8401e16ab4dd5431a93ad992ab91538469005d607260210078b027560191803860fc0325e053106158440e0e0c0080019326d34094013308c9602b9c1b5e18a14db7c420c15d213a18712814a02ca003a7855685c23194e05aa02f80108c264e12f00717a46be0c5905cb4db680224195b0404
  | 8 => 0x86e200050b8386ff21c6fc8e8800711936cb4031d405e4a81b53018b7b01ca72ee61c51f7c07e6c0b3c1820a7c6b0bc4048385cd205f1b06f414b3a1105cde2c67227577d15b3a860d64933d1639ea488360be11803088002428f8f200d7f070b981b25536b8046d1c05fa600f4da1881c0b07a05f8886950f098e800021077ef80f23c02d07481d40c2568182c10943d480aa09eb80448f40726c0448501e51810846083a8113970e1a506e4bc2443c9e5620b27400bf5315c425dd0c0a65fa6d8382cc069bb7f2c6a884380e0db189b4da094a105930836adc9b80e2cee4e2f210079521dea80daba8058f6080f404d3723e4ac101742a154a15c0071a500ef041bb5c164c4af010c4ab603a72e03d1c86a7505adfe0b9460534a013420440d88d93e17cd00e0d946405c0138202eb00775426ee5c3e8e197c390de7b31f2f60fb6e10d8f8e41080710138b9c053c7427a1043610307848461e0de9800f858087821bef6304290608453007847c5789e326133581c72e00f4a016a4808f080087a155de01d08c100440da1e57e1e012c201cd28038e00c12f058bd80681013778165c48889791f1d00a4220346c0a0c0817e1417c420a9614bc68a0fa42050e69b450029de08256614cee1409205618043164261240461101e98809dce07aa22028082e6b162810011b105d33018491192843062c193c20174fa425a44087c58d638bcb3c7ef088d94384d3c01bb780fb5805a1e0a09202e4a97774c09ba807204a3502002c5813f5e030554fa85c2af0823cf584d138164284d4402f72e022040890f4423588f9aa03bc28840b02c0469b47a19204457491639741b8f108d1c4302a80f35815c6d06c780010200875008cbb98d0b0d69802b80e3f01d040030162411f28f07f6400d1629f49009b7d1872e1be0305f0f4465cc156fe140d6099cb82c4be0819609e16235cbe1345c3f8bf01c8543088c176d80d695071d4099e38007500069401b1623ec202c07a15ec70a21e0036c13b74807c0709a410230187d00400a940a47f84dcb8648f4062220565a0e018818b60167841513601b10c2b3901582e91ef605cb08424d80d8e846eb0056680418d8b3b610ddb3001bfa6ec5a8f9a5990778182905cf0600c3d0db4a82eda8381dc0569585c790ded5848c58b9c9e1234a10102070c5b15e7410a3d0fd8b07f1e0a7f0202e52059026680843fae059d99018c2e43ad83806c02d26836b800867c0843c0148301e4f86d1150c3988cd74c26ef02fd3c2ca0602cbd48dcb8025fc146fe2051a0896c6136d8058e804f2f21e2316716603a1a1fd0c0b27b85c87836b6a0d1734f23404b3a411b6d109730107d8348120615001ed880e3b00fc442640801c2e63e3816719c2da44020730b29ec2b3e00dfa8009970dc6b26000c21a80978770bdbfc0f4c2043838af1802b9f07200d36ac40234a021bf85af0a2547b206a829ec08384bd13f8e10c03058b086931c07b189b4d38551ea134d800e9505bc22c6981774dd36b391fa1eb13ef80714c0de9802cb005e1a006e5f300ee03cde1018b22b414319d60463607244b6741517a21040d60191e8079dc09f0a0321e0210200d1fe082220354988c42002d2a0c2c303c1102211c1c4440543c025cd0fe85c071d49199c8614f0feca046844249b40c04f0286b26d4382d2fe46dcda16ea963bd8320060cc0701e8985ac5831c6203718061a500b2480595385d8e083ca81c8f62f8060ce5d0162900165c07d3e110920838f4173c40462c10c3650a638070a41672e0258f016ea05ae5c220f41fce885de3c1c3ec162c62257a430ea17752e2aac801a118d67c1339480a06416403a40c320f94813e6c030b0026764100780443c1c39782d0202b1660e1ad0413682e2287f1b00747a09cdf085e15673af099bc03692427d7813b583047b06ceb0dc01807a102848202e160871b44a8780a43c1c02105e2b008844c59425dc56816c0d8430009cba016df05e910857102da180c3c70710262fdbe0b78252e04430c340c6060e17348c7684c2d01881023c6c06eaa82e4b80b1cc19d21537890df484288f5198ad05c4b03eef00b25e0db6e1cc78a3ea4c1c27e1585f8afc10b90884f2fc1b9ca0b2720ae8e41704d078e046caaa1e180448451806a03f7f0c668136f08057838be84826db81f1d80082202b7f090420348440bdac030730009b41c73219b4458cf88207d85a8f427b5c0272f0369b02345c348de857630580184af1d36a9d0607344fcae600860b47b480cb018c30741dc0589802397c561f0446042db2896890cb86000ba483a0ba9f53f0011ee2bec9301240be0301e5a4280f50ba451ace4457480076cc031060c450c871082b6c00a0aa5dc420569580f1e40578458f634ecef81c904308ea0b21110a3782c0c417d6001b7f63eb7248564147780a3160b9bfc01dfe0e2c3188770c16c40f84509f2a01a3d026eda1824c0dd718cc85061de6683000781919036c2698e5f0141862c02d8a8a097c49d392f23d98c5fc665a8084da11a26155bac5e732730fc21b3384c0105f6b01435013f980edb3816db80b27c35a8046cbf0a1cb85a5be130ee0be170581e91b614bb9350a71e912ee00e4602e78406401c0e2f04b9e805aeb06dcb0f69111b35803b0e1b8b00e42ed200c82d8ac0ac401225d87000e16cbb00c3d01e8b827b5833a60031360b74903380c07a220519f05601c100c8066940bd0c0d69580b9cc215b016d494dba72600d9b189047dd306e32005cbc13d2410e310409b62bb02079c858f2dc262ac171d2155b106c640996c11b9cc098c312a110dc8886e0b48dc5a91b7f00d0f030dff1a9d105d85c2eec05a08909c2c16e7a0b37bc674ae4380a02f81cc8e18430c1039e8941950104991f72c216940b21e0b2284172a6081550bc420377d8030781195217bc1236ea31f6d40100802da00151e807b7c0794e183970010f028d28238ac0be7300fb6a1b1c004d240be7a838556646c81602e203c20dfd580b61009a4404e550d6680419dc89e9484efb803cb814058002850ad630ce7c05e90423b2859d5dc2667007cbc2135e01f7300408889471389d403db50fdbf808f06211a81260b810b780145936a4e02c7e803e1202e5c3386002dcb04e55a136bc05df703c030570bc1c1541742216d372c6018003ec23a440bcb504fc083b468101f70b8df8aabd0701dc09da202090069cb82f0a43729803d370569806de548ddac0dd1001ab780f52409a1a001ab0998b44af080c05a84c7005da501318007c2e0d21e0861790733db972f99c4808f0f0338d81cfbe47cde236ef2475648df0a09ce90dcea19162c0994e0dd7001e0f82948616c061d02105ed9c26c582442212e030c1bf847108058180041e0761491f04c2172e02ca1028d78141ce00b7909a0482039805ae02532a0bfb281e0c01b3ec0408882f958b636426f080288c03d3c0ecd5805d840a26c0b083853e1e0fb4422c061dfdf8505c06081097e9485603c260b417286322c604ed404bb9e176283c9e21434a01e2183890418a3e0e2804da9de5c1df09818165c808f1089306c219a011d371127221715c05b1e110f6028ea03f5d1039fe9f45f23ebac1061a1343d063c11121e03f0a42577904d0c89d02013d6436e842440f8262b00f2f43043d04cd40e08f6142088f8fc03ca103b1ac172f421a570404fb22438370a63f72f03e5d016c70143ec2290a04e034dc6884c6041a38403da50650f11ba7c1a6ff03c5d00eba449cf93743c050aa00cea081122179d0134da4e6d70485cc26a780add2019e161325c2dba60378107ed980ae5cafc221c017031e105cc5a177780b3164267d86fb0307d80035180550f0500580e97e105d848d8b04915805d081b873017b985e0d9388b004e21060424380010391a02cfb0265d0433e211b6e1720485675889aa002ef616d4b01058034c5a152e60c43e082ca847268165b104082820e624341509e6c0217c236168190300540808ca10e1de27d4841820407eb809e3c2438f02f62c01d0a0de01800e5c157822021e0a09b01b4f00de6c1f56604f6a4354852f860182412360b1675221a902009c20b64900c27e311801cd704dca7002dfcb1c06108dc81ea0451d7a11bbc17a044b47b9634ac49ae018d700389b013ecb3023c9818100c2a87748a096940be5d45f7b00fc58061f6110030c9400424e80a160143c24ebefa5a1690db6a164080168a40fd8c21a600c21e092e704774e0813e97d40083a100a3ec0acba16e1e00039c445cc2d9350417b021cb8328f605afc2263c0656c04d39600c7a203970105c88312309a3846c73085bf806d2800809020840b2cc01284403ada03c7301e3f05a81021c2e0ad408510200f9ce01b2e85cd501eef4174f02cc1018cfd0c77ed2024e081ed0a92f0c1e0a1718025c2f0c60e016098912cc8f8181a46a23e4b82c3da082c602b1610e620328460e2de02f8580e4241c6141290a1c3c71023727d3a099eb20367700e24846d2808c2e47d0f82e0600b6d833aa31891e03baf4318213681d13626099bfc074cc226fe0ac2902f6040e20e900a49312f4233d080dfc1a25e86e3c0582e94f248bbb282023d016c2c35738219c90c80e01e4a80b6d40143c11e03a9de103774820a84214d308b2e8436c10c30a02dd325fd5c180000862c164da0001b04b7200617260c1b0b48b2714ed2f36504d0b2370b00f12c17eb307016851cb82ff52062c20cbc20231081582017c5a03e310b5e0849a4044f5603e36c17a101374c2203c47d3c02a9d8156502fc0611d0c04e4965c2d9398c8173970ef1a93746823c2e0d23d2365791b2c00000603db7
  | 7 => 0x107d02f1581c01322680e5b001e43023e4800f4f501e5a205c8d8059688130240fb514054b94b10e38053e58261dd0ac642a69d040710c0da8a25f448607a3f82937403661a8470ad36835c132d184c85684c4a83f14505fc9000b01706c5668d9f8481267c174c61ccd4c0b92a48117202ea3653c91c17a1a0433602360d06248ad218a0a119a301e4c212d12e8ba3d40f3cd0de05e92d3981a163933ba10b658616e67921c3c00f50205e3500a43881795600f23622665416cfc012875811a630296d80010f82cde986d3d54c038e85cfa40b85111b23e29642203c4aa080590344d22361448bcc0b15a6c86d02d096a2203d00c3f8a306d12ac1667a02cd502f862e314d48b64dc1954942cc5948130382686822cc628da05e5f06206e6041bcad01380041f1924da5dc8ae1e109a338271d9060654969478179f4c7d5150ba7d41bce220a195005ae829e88e974dd31593fc0744181688c0a05b70995287f20c81021889d05819a730345080de2da89ccf6079490814700360461bd3282d956917ca44be920110d741396805d27d2668e643e6789ba2e0893b14da12f04068c0790e80f32d01e5d852c3bd2189802f10601f07e03cc681c91582f9a30b21061252a3159ea87e12884c58f07c5348da65a5947601074210cb2837862c2f51802620c1212932d92200b10604e586d8c0e021a3591b2264864201b53288d9e425f39103e1f211c0e00004214b8350272da02e68c058ec80f05023630a44c5dc065b64174d90b61600dd1cc058fe05c4a40b216458c05c2d16e07f02141f4d583c28807811e2b44bc1e42011d12e078542172e1c261e206c7bc05c860890a18fc8de164d580994a0133e901e73f01d46007c8606f2ca2362f41b53a80998dc4d1340166f983cf500b9990261ce81e4f20ac314afc5400b12a0b27f20d033c148d88174180fe7da9d4ccc059a480fb840ea98f97cba8149a805d14241e39004d32807e1f40f3880fb6001bc0e02e91107216d02e1dc0b134825a6c82f47a0a05141fc50cc1a41c5b51102e0c853cff82180ba1319d8fa7de1f924b098ecd1b2a504c76916d047238bf811d0801e7c583c444a5c659390ac0de2af04d040138845172ec8360e816c1dc068ba62b13063635802c49c23121c100a801642252c8501ba0304300d04e57f82d3f0278ecd1b2db0b667c46c37c2de4806d0500da73603c8f80983406d46705667d07c1d10b9dec104a48fa7ce02c410059e702712204c87c4d51820987482739508652405cc60175b610b46381e04a09cab4375b607516400f72a03c4108bc8600a085486a030ac55e09a44c173759027b501cb5e0ba044811a401e44646c88e0b9890071d708699903c8e11796c01b26102e2e202487c0597682917402f2db01c8760781646011500001603c7f0a586582b0770da78984c5e92195621182707649e10c8e08da2f60f3f001e30906d27e0590ee3125a058a100dcb608d8a6a6d4ae01694507cdf41781784cb6c0b416405c6081a5b613322b236938000216135b6059293a369840a496007a65a131cd0ea91c1102712d89902bb9402e25602c6b1099c541342881e02f58c572078ae14b8ef2c6568118e530991180b023c2661045c2282ca8613347a01647305ce4709a2382f21001e5ae22ce460595685a03f8569d41bc7cd07a6702c49002e70418cce0059ea11b0d323639085c5b2038ba65f02003633a1b43280794a07f4190df2da0bc0cd21a485174100fe81a0bc0843f82d40f20f0b60f101c97b099aa04335601e7d204cfb41c84700b8ef8fa3e853c78402e3785b19e81688303cd8037a6602f19b8fa8e00a032cb7e3a07f3a0c1e89603632f09a4e01b1b580e9080303bc145b6033ae80de06046ce7c079c5006b6ca364bc06ccb42d9f4e0f3f3c1e2b01fc1764098a81f3e080e21062458c36a7987f4bc48804e22409015c8600b0e582e42a0acd581b9f28130d30da5c246ca570790e0074670b283e9b42a43fa1a02c1a34266921b4d2439a5e0003848945141beca824a3de1319280e33803c89607843c0f2b40ba3b885c66c18da584b49f017514062db0a78bf86324d81619745cd9a0c04285928f06839d97c9fe0781806f29201e70a06c4a836a46d4d0a602a67912c5fd15d7460f49f2362ac45c8842c9d340f25f01618809e3bc0b93085927d0de5e252e8830997604f28a0b22de1643e009e3a00b8cb81821809c32c3680f65f5180b66c005d12031a2100b0f98165d646c0ed0a8b78334ee0582d605cc34c49c801306404e2fe1bd39e07954a5932642e58857f4200f9c506d01a0b67c28acba2078ec86d1fc0164c21bccf92c9d502921241e6640a0e56059b001722306278e83c4642c89e91b30829e55a1fc8441401a84c28a05082d20548c8bdea00b4a411693e0002c808a7500f38227269c5fc6202224814f443c2639f02c5fc05e520334d98fc44003cd504497ba7508e00e8d6d8d12c0f9f691b2d10368b401f0f80d8728443bf82695a84c3960d8c94173e501e0c810d2f8c483013751808f38e17105a098a386e36cc1e90859530417dae82f3620872180ccba02d94902c09c82e2d30ac57015948e1315648e3b302c4308d80d16529a03645003c0ec2f0cf4282e82366680bc68909a2d60f26506872a85c6b0329f341347a0b35b81684301982e82c14006279e164faa09a20c074c204e8d60a446d8d97080f8e704e1de03c3e6b1a750002c704f19703cb2805a2d14bc6f82e1f246c8d807a2448145882e984054fce8d8841364d20981961649a837a3894f10810069602545e8d8fe00f4c60b470816d276188bc40f25e0b487c02cbb0058ac05c0110de4201669a81791385121408667c46c78507e8f11b04a05e2da53cce70808602721103671502c87c3a09404428a4269ea1bc174af98f4072d10fc65486d2b42c9e9817a8a01e1ab16d36508e4840f49408606102c3bc00065c0f13503e4c204c1740b96a42846f0664fe1b4f380fa2d12f32a01e9849b4f3e0982821302302e44c8b002c000bf02744e0de0ee0cc8420986f8591d408213e5fd364199d0213382066722108a281a1c74813460167da02c422059a7c0f2f125733c03d2b4b19c400f2a50863b203c1710b88302c3bf01e2ac1bcfa2079bf01309905e99406ce0837a2591b31b05f2da92cc608d83f48144480e6c0037118999d0a6350a08208618c3140580d61340b0860ee46ca520824813744f0de55946c3e407e5200f2ed0602da05c6741595a02f05d056524164cf00b8f313739100e20811c1c58d98d1334060565b006cebc3f0b69831418164bc1bc6e0bf18000b3e90de02503c6e18da2dc0c446c266c0112db0222158280ef03644a46c190159b006d35442641783c43005a1405b21104f0161c528c378ae4810e00de6ac0bc1a413dca8333180de7ae0ae32e0786297f4738207a80c4fce218e181b0e92362b084ca228da2086f01708e9a604cb08079dea433d50be55b84c1d00da4522c35d06a0f4851290218628132d48509a446c4101580ba1342405a41e014de28d99d91b2540868fe1f41192fa6980f4f30ea77646d40a0990e81706800e1a7534a140b82c91b11182e0b907cf88160541371d723662405cebd318a080b0590702da10c5fc07869a2bba10135141ccfa609a5214f0f705f92002cf8a05926c813a085601a62413c0586f81c1ed02e5da0b009e2d9bec1325e03e850d3ccf43789a81b1cd82e1be1b42488d96a05b25e0de47084d2283f0f680b3bd058a1c16e98e0f87887d37f0ce26a1bc0900f8728272d80364551f41008da0400b4ad
  | 6 => 0x20bab04c009409d3808626807aa400eaf40021108ad382cac402ed71a5a2e0269c437abc0604e009b220265a42d8194561d021ad648ec0a218450284e021f2b8160c62d8ad81ed10378b3066aa9af97d41ed002c9100dc4a809b0201e09b07a9981e4d638b15296bf837a48c1e8d03f8840bec342087244e5e2af84a09a1e40bb1408eb5a05901c1ec2817d380660340b87d48ea5097b2283009420b1d0dc6ac21b8a48e9c41384c0faa4837b6f016ab909826066cde07a1d00bcd82fb892de8bc2195425ebd00787409e06707b46036aba0381004e1c40797005e9c413af30dcb942cb1b016d7109b0a816bcd14336066e5407b3e45678004b4f016c2a079df086de607bb02deb0e0baaa44e57c05b130222180589a0b26fc2df3bc0e57c2d874016354099ae81e2fc388e101a05805bae0e28f2078ee0dbccf07a1980e566059bb2669ee0584281edb405b9a80e46995b4780e586080d9abeb58058660fa3e6078150264e02d1f00b2256039bb04e65838a3901679815b4a0fa8f43fb6109649e0399d8162a005b48056c2897ae781e7ce13a9344ec392595580e4cc1589a41e7c6058ed0deb9e078f3026b1c25a0e2b736607976c1e33003adb41e09c099b04168680582601bcac059f104e78207b040b27181289001ed702c8e904ee68a5944296bcc2cb490274a81397344e1042c83681604013a2c266e060989b0266fa05a6ac1ee5d1595f81e64e07ae106a6b8099d681e30c09a94057cae0796580e78924138016e5e03b4501ee6a0bb95a2636e0382804e55017a3905e4e0059d929699507aae2663a8199e1456870379b04bea241a025266a9c13a4384e78804850082028379e981e5de05a2e06e6c6079230164ae058f06961c709933826d7009a84a2e040adeefc1e10a059300b6a68059be0dcced239c10de1d82db79a1e24603b810fa36037b8e81ed3a039e00b28ab07b48016bc1a39ba04e3c01383180e6802caf1c0e47013a24a26ba2038df2de9c207ad6826a920587104e510389aec56e7123873016a3425973816890a189104ea90159e6066c5099a41826e8a0593a04e5842189301380437acf66657c97a7025e36c89a2f81e7de13b310139442184a816bf004b6202226205944026268a58f005f4a82db4a81e14507a8d0debd1222ef266b428bae10fa38607ad8826164059e981e2689790a00ea9ca5ae64867dd25a10
  | 5 => 0x4cbe01e4a80f1d00783a04cc901e2e013190139501049a44e8b02f3a6098c516d398269c86d1f5058c816d1f80e6d4072ac0587e10cd10162e40f35c1396689c3f0b66880f4b407a3f05d0982663a0f0842193a105350563a04301915a3e0ccc9a5e6d0431d013a1709cda
  | 4 => 0x784
  | _ => 0

def G27_buckets : Nat → Nat
  | 4 => 1
  | 5 => 11
  | 6 => 79
  | 7 => 237
  | 8 => 330
  | 9 => 121
  | 10 => 5
  | 11 => 1
  | _ => 0

def G27_flag : Nat → Nat
  | 4 => 2
  | 5 => 1024
  | 6 => 2048
  | 7 => 8192
  | 8 => 4096
  | 9 => 8192
  | 10 => 1024
  | 11 => 2
  | _ => 0

def G27_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 11
  | 6 => 12
  | 7 => 14
  | 8 => 13
  | 9 => 14
  | 10 => 11
  | 11 => 2
  | _ => 0

def G27_seeds : Nat → Nat
  | 4 => 0x2
  | 5 => 0x10593400115600c5e13502000800803
  | 6 => 0x93800a0504d61d543163703804e16d48a0210670a000200707793693b93001491e11e93b0b904901201d0a60470092330010020e593b25702c02b03a06b08a00214e01d2a300200100c0320b200101802301c00a00b0040019030300020120180140360010b385003900e02900200102e01481d013018
  | 7 => 0x234a02a00c8004d23e00f0e0916a03220010017185e3b30e240050032347030805b008d3a00024af40014042011002b19cc0360108187030801300080270024031001c06e082c04400140040bec0018ecc0c48a4405800041a40f6800100081640150005003c02088bc04101dc036027013600dc015002000d005a2260024447866c0dc019c00b006800d00301510a7804a004804600240018ecc232001000100b009b017801002c400b03b800185e43210ce80ce000818d007c065000807e820800b006c082000c24504ac04c07d0007002400f000400800140da0028208002026800700228ecc0a60058001021017700ae3b30014002006800100240060020002004800201a407d81b40810020001000c104002406400180110010038006800500080920040125004c04305c4014003c001031c004007402e0094047812000101ac003087801e004000c00500ad013c012001401380fc008009c011003200800080a4004c0330040005006c01e01bc0b60228074023812f026c05a01d00040058044007000d00100040004002002001000400d700b600500bc0020018136
  | 8 => 0x2a2802708281e818afcb0008034cc200ca81d3c001009f149805400220e09f800c0161300018b088ba00101c06d0198002a678108578003005807009aac900500580309e3a18800405a2d501bd07400452a0bd003800200a052000c0c5528001505c0093f9011810a7e07b000c806a7c9528003009801552802ea0fc00b39c17c8100002cf200e805c7b8282001800455e002025826c06c07f00080a402611402e8018daa0010b400e800200d0af81c03a044502000141540bf9bc800c016001014004c0021029a9017e63a16f01c04c80360120e08ca0126004004803026f2c7037023002011900884d404c1c000700181fc009006014c00e00400700d8292001019005024800100b05100960df001007802607c03a80d4006001001d4a00bc005033cb0c00a06b921003c00c0c427680063c40080008004074014006015400517602f802406a01d00480bc00601f01e83301b75281d0800810e056000806c006101002000e2e400901280e000404700401dc048038046004410c036295033c25c01a028857c040018003454c3a808a0010448021528003003019a061004803402602300600240080070154464002149002827002e018001000a1d10b2031054c0600250d380920d0002001004400e12100d801412c03000401001b75280e7029c01e00100b0020020002007808407605903a816c002015004011207202d00280500c605801d006401003900100080260410160004006037
  | 9 => 0xf7e8400f1bbc1f304540010004002878400f039807402aa1d2024e16b0334213091801a000414500040240c0804e02a830900061390004082003e0f20e2c0b902b400301101a4019c08c028803f0018001002c02705bc00401840010004011000c00b08cc12d00c010f004c01601640a905a0017003400b87840ff007c006019a0f00bec14b06ee0b10014002006c01000080060024035000c0240540011009c015003000b000402a003400501ac00182900c681a80a40164007000801f00e802c0004341000404e00040070024059004c001
  | 10 => 0x27d81807811067
  | 11 => 0x2
  | _ => 0

def G27_initial : List Nat := [0x783c1e0f0783c1e0f00003fe00007fc0000, 0x90482412090482412ffffc01ffff8000000, 0x389c4e271389c4e27100000000000003ffff, 0x422110884422110884007fc0000ff80001ff, 0x442211088442211088ff80001ff00003fe00, 0x9048241209048241200000001ffffffc0000, 0xa05028140a05028140ffffffe00000000000]

def G27_idx : Nat → List Nat → Nat :=
  qIndex G27_N G27_buckets G27_flag G27_seedBits G27_seeds

def G27_benes : Nat := 0x5f6b458d2f273d61f0f61dc3b619ceaea5f4ad15cabb5c4a312db4aaad7f2fddfbaaad258fabf4c2ba576acf56ea09f0cf6bb5766eccf57c4b1d6f3014eac756a2ca5caefecbe2ac558aacb3c05c89d95d26b588a51903108076df21641c836da012736123ed4cb215d6b5d69bdeb4b8d319e33b48f756b2b25789757fabd632a3545d06bb976eedd05514c453d2f356600000000000000000000000000000000000000000

def G27_inputActions : Nat := 0x72e05477029cd4151ea0ab9c446ae222e8d11ac688

def G27_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G27_benes auto)

def G27_cacheKeys (i : Nat) : Nat := G27_initial.getD i 0

def G27_cacheValues (auto i : Nat) : Nat :=
  G27_cacheKeys (fld G27_inputActions 3 (7*auto+i))

def G27_act (auto : Nat) : Nat → Nat :=
  cachedAction G27_cacheKeys (G27_cacheValues auto) 7
    (fun w => qInputLookup w G27_initial) (G27_rawAct auto)

def G27_S (s j : Nat) : List Nat :=
  qParentAction 11 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 3 G27_initial G27_act G27_pb G27_records (11-s) j

def G27_actions : List (Nat → Nat) :=
  (List.range 7).map (fun i => G27_act (i+1))

def G27_ori : List Nat → List Nat := orbitActions qPrefer G27_actions

def G27_coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 72, 73, 74, 75, 76, 77, 78, 79, 80]

def G27_rankPool : List Nat := [240336203, 102773001, 236077486, 137440591, 169062760, 203668778, 68338125, 201441678, 201401612, 136428843, 171064618, 203438512, 135512461, 67320136, 67219784, 203472138, 237023497, 67157258, 167854350, 236108076, 33631567, 169916848, 167983400, 134292748, 204487088, 68173067, 167884104, 100876749, 135446797, 236077454, 68301160, 240336171, 100876685]

def G27_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 72 G27_S G27_N G27_idx G27_ori G27_coords 5 G27_rankPool s

def G27_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def G27_rows : List Nat := (([10, 18, 33, 44, 52, 65, 76, 84] : List Nat).flatMap fun x => List.replicate 9 x) ++ (List.replicate 8 ([3, 5, 9, 17, 6, 34, 66, 24, 96] : List Nat)).flatten
def G27_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G27_rows)
theorem G27_nonconstant : ∃ x y : Fin 7 → Bool, G27_f x ≠ G27_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_enc_goal : encL G27_f G27_rows = goal 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_proper : ∀ zs ∈ G27_xs.sublists, zs ≠ G27_xs →
    (covUp 72 zs &&& lo 72) ≠ lo 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_good :
    qCachedGood (goal 72) 8 G27_initial G27_inputActions G27_benes := by
  unfold qCachedGood
  decide +kernel
theorem G27_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 72) s ws) : MonRun (goal 72) s (G27_ori ws) := by
  change MonRun (goal 72) s (qCachedOrient 8 G27_initial G27_inputActions G27_benes ws)
  exact qCachedOrient_run h G27_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_4_0 : span (G27_Z 4) 1 0 = true := by decide +kernel

theorem G27_checked_4 : span (G27_Z 4) 1 0 = true :=
  G27_check_4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_5_0 : span (G27_Z 5) 41 0 = true := by decide +kernel

theorem G27_checked_5 : span (G27_Z 5) 41 0 = true :=
  G27_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_6_0 : span (G27_Z 6) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_6_256 : span (G27_Z 6) 59 256 = true := by decide +kernel

theorem G27_checked_6 : span (G27_Z 6) 315 0 = true :=
  (@span_join (G27_Z 6) 256 0 59 G27_check_6_0 G27_check_6_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_7_0 : span (G27_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_7_256 : span (G27_Z 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_7_512 : span (G27_Z 7) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_7_768 : span (G27_Z 7) 179 768 = true := by decide +kernel

theorem G27_checked_7 : span (G27_Z 7) 947 0 = true :=
  (@span_join (G27_Z 7) 512 0 435 (@span_join (G27_Z 7) 256 0 256 G27_check_7_0 G27_check_7_256) (@span_join (G27_Z 7) 256 512 179 G27_check_7_512 G27_check_7_768))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_0 : span (G27_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_256 : span (G27_Z 8) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_512 : span (G27_Z 8) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_768 : span (G27_Z 8) 256 768 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_1024 : span (G27_Z 8) 256 1024 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_8_1280 : span (G27_Z 8) 40 1280 = true := by decide +kernel

theorem G27_checked_8 : span (G27_Z 8) 1320 0 = true :=
  (@span_join (G27_Z 8) 768 0 552 (@span_join (G27_Z 8) 256 0 512 G27_check_8_0 (@span_join (G27_Z 8) 256 256 256 G27_check_8_256 G27_check_8_512)) (@span_join (G27_Z 8) 256 768 296 G27_check_8_768 (@span_join (G27_Z 8) 256 1024 40 G27_check_8_1024 G27_check_8_1280)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_9_0 : span (G27_Z 9) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_9_256 : span (G27_Z 9) 225 256 = true := by decide +kernel

theorem G27_checked_9 : span (G27_Z 9) 481 0 = true :=
  (@span_join (G27_Z 9) 256 0 225 G27_check_9_0 G27_check_9_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_10_0 : span (G27_Z 10) 18 0 = true := by decide +kernel

theorem G27_checked_10 : span (G27_Z 10) 18 0 = true :=
  G27_check_10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_check_11_0 : span (G27_Z 11) 1 0 = true := by decide +kernel

theorem G27_checked_11 : span (G27_Z 11) 1 0 = true :=
  G27_check_11_0

theorem G27_checked (s : Nat) (hs : s ≤ 11) : ∀ i < G27_N s, G27_Z s i = true := by
  interval_cases s

  · simp [G27_N]

  · simp [G27_N]

  · simp [G27_N]

  · simp [G27_N]

  · intro i hi
    exact span_ok G27_checked_4 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_5 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_6 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_7 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_8 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_9 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_10 i (Nat.zero_le i) (by simpa [G27_N] using hi)

  · intro i hi
    exact span_ok G27_checked_11 i (Nat.zero_le i) (by simpa [G27_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G27_initial_perm : G27_xs.Perm (G27_S 11 0) := by decide +kernel
theorem G27_no_run : ∀ s ≤ 11, ¬ MonRun (goal 72) s G27_xs := by
  exact noRun_from_barFastOrbit (k := 72) (S := G27_S) (N := G27_N)
    (idx := G27_idx) (ori := G27_ori) (coords := G27_coords)
    (bw := 5) (pool := G27_rankPool) (cap := 11) (i := 0)
    G27_preserved G27_checked (by decide) (by decide) G27_initial_perm
theorem G27_no_small : ¬ HasMonoSize 7 G27_f 11 :=
  encoded_mono_exclusion G27_f G27_nonconstant 11 G27_rows G27_xs 72
    rfl G27_enc_goal G27_proper G27_no_run
theorem G27_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G27_f x) :
    12 ≤ C.size := mono_lower G27_f 11 G27_no_small C hmono hev
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
  | 5 => 7
  | 6 => 86
  | 7 => 411
  | 8 => 684
  | 9 => 242
  | 10 => 7
  | 11 => 1
  | _ => 0

def G28_flag : Nat → Nat
  | 5 => 256
  | 6 => 8192
  | 7 => 4096
  | 8 => 4096
  | 9 => 4096
  | 10 => 256
  | 11 => 2
  | _ => 0

def G28_seedBits : Nat → Nat
  | 5 => 9
  | 6 => 14
  | 7 => 13
  | 8 => 13
  | 9 => 13
  | 10 => 9
  | 11 => 2
  | _ => 0

def G28_seeds : Nat → Nat
  | 5 => 0x390021a024080208
  | 6 => 0x4802f065d0ec00280a20c1c00700201081f3c00306b077a002411300f4002855401b01a434900340ac0018001018d947003436900280030004044168800102d4007830c0b600081b5005c141001400400c4007005401b083c003010018b0004003002802481d803d000c03a001400b021c007819c0c706700020010005006c0e506e0006075c018016005402040120018013003a033
  | 7 => 0x4c06400f00e0694010111000800c49001c0008b106d2893051032432163721f0d6417263203c8558296048083031402a00100100d6cd8961009970407c05500c866000400fadf8b7c7e80f1083000401c1090028aceb74003ad68044a7200301a00d06220770368038c8800112b03fc09039d0cf87d40380a9036825801802004a800444158b021008c09a02500102e401004d00c01180362e806a02a6af0006b360c5c00357400c00dc0a806b0090028aa401303b80cecd82b102c800ea960ed00103cc00209700507cc2500bba93807801e0010048388100001012802055e008003014017a04a0039b2400e0e1b36001acd80e707382042eb4fe01352a40d80f7b36000c008069037802c6f60cd00d80942260c809b80380660050048154504003a4182080060ae057827820a0a400311fc40000f182011400341e01a801801e0c7282146815f3f800c003011803b10a800406f3c0001cd0c00602900301ec02a05a001001001a0c101c023800c05400b80280860160c400ac16e002002001e5c60d2004800407166c007856c00401293a80ac03e05a01980b00020d800203c803e001002001c04e0199308004234009004043402200192403c015603400100240a8004013805805603f00083ac024026003802407803a002802004601000207e403c00d04180f40020ab922864011c04b0058024016006001003645722400e800404c0560c080080fa047015045001b66c01400464160090188004054001003800c01802f01200900460010010006336002004802c0041a700e000802e0028b300381ba020005c4c014e0ec00e80d61d0002037821400806400380c6cd8028006d9b00ca01301c000619401100181fc05803b001801c0ab0c401180380ee006002000c00403102a0074002004001426c01003d047406400b66c
  | 8 => 0x16c81fc008bf10e309b834da1f000e80800b9f06d780086340011e80460068003026acacad800201d81b80464002f8047000261a02f800f3c0839011800c04a07c11b001015d9ac12101b023805e0cd840437032ed5786600320040ef00172d022400100040429d002c00932940b7004832431011aca380046e24b5c7063101a625413191102e644d04c817001c7be039000407c233001884027a005001015c26401a00e927c42e01807a003cafe026015827803a0040f0830711a047c33099b0c8035113803018a3f30e6801004c00308313e403f7dd057821400b78d1b180cc23e07d05701c355e89fbc100c00ac00206582b0084027008004c0100a4007803801e003bb082440300010ad0026e9200600c001000201e03782a80340061a001ec00803d07484a4016106006830c31200f2ce002000e004b970b8401c0be00500b06280b4b5e890405208100884a003f6b605f0660026001b4a00584aa04500380c804200300200780160470ad00080380af00207e82fe0040e20006c3c007128800f55e030000846abcc03912f803015606f029018016410902b800c0d75ca01580b809c0dc001072802600c016807c1260990a5000c00a03e01882680480130e456dc49800514c012442800800504c0002002013025c002090000d6b002158300387080040a2012804803e07a00413942501f1004801aaf401a00b016c05002204b000800403f028002c0260010048040008001116d49aa2407400b81581514f8019d290006002003101800d47b004810400c2c7005000c004002d5780401f405805586941be004003047401e01a022801001806c00400640421b7d578c3c0b13f70014f6c02816200080bc0060bb0284ed804c035015eabc01600304080080560010038038136029005808f55f38c025000402400600080680301d100e066809607e029801e70801f9bd01c405800102581700ae030012800401828d107000c00a004003017814c01f05e80182a4001000815c00a001000807c326002000800c00200100380c806600606a000c08401800600545bc021011800c5a936f9a7801808600c0b4009805b336009023c0072fc0040040006006002801806a01c005803815600e08e8a5406a03d04400165e60da01600d810608f96400340fc143002000403010706800400020020020010008001946003401e01f94088440760b2003825a256191049827016804902e8010060099001808823a00302f44240070ce00d800400601f0fa803415c0100b8004400c030018004407401704d002801000b06e009405e03a026003800805900201d413608f01200a401e099028802c05000d002006000c00200b002218f0bf000800402202b0038008004053006814823a0060040020004001026001616800b00f82141a0015016000800400a00c804801a002001805401a00800480dc002001002015a0a20130608454092039004003c09400600f801355e0d700400e804c00500080100720eb00a805c00600700680080a8014003807404808300081d800c00300c03d000902e
  | 9 => 0xb6325179cde01d484b004124c016156029871c01e01c01f009008800d0cb8a4c1f0683000834c7221a50c5007000400100504000040a923c00740e33c800102ec0a407f9e44d9800646e00081bc01a3fe010001041e1e2004800c3ce003058cd641860ae0f900340240019a0801413600400c006401600601280700532ee01100a679000f0e60768612002024803e516021010498001602a8f400d002e00700283f80800c90064674028008024813803001c0008370203171041800401800600f803435d145006001000400a09d01a010200184e830a79007f035062c0040be01484c003600302a88b402002c01884500093c8001047010616e000803c1140020018428528002072857c078024006003c0790971d6007679005b84800100480d900301b004e003039800806000c013802610a01800080940aa0089e401a80f6005035800449806007b00a001800a013c20400407402f80ec03604d001413c11605d008811009a0160ab00cc00b020005002000d01f0020004002004014000c00200100d01d4002012
  | 10 => 0x12062016031c2002
  | 11 => 0x2
  | _ => 0

def G28_initial : List Nat := [0x1e0f0783c1e0f0780001ff00003fe00, 0x2412090482412097fc0000ffffc0000, 0x6231188c4623118803fe000000001ff, 0x9048241209048247fffe00ff8000000, 0x188c46231188c4620000000007fc01ff, 0x24120904824120900000000ffffffe00, 0x30180c06030180c07ffffff000000000]

def G28_idx : Nat → List Nat → Nat :=
  qIndex G28_N G28_buckets G28_flag G28_seedBits G28_seeds

def G28_benes : Nat := 0xea17b3f26847325a0220000001124c8dcf817d02000000000000000000000000000000000000000000

def G28_inputActions : Nat := 0x2e4631ac688

def G28_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G28_benes auto)

def G28_cacheKeys (i : Nat) : Nat := G28_initial.getD i 0

def G28_cacheValues (auto i : Nat) : Nat :=
  G28_cacheKeys (fld G28_inputActions 3 (7*auto+i))

def G28_act (auto : Nat) : Nat → Nat :=
  cachedAction G28_cacheKeys (G28_cacheValues auto) 7
    (fun w => qInputLookup w G28_initial) (G28_rawAct auto)

def G28_S (s j : Nat) : List Nat :=
  qParentAction 11 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 1 G28_initial G28_act G28_pb G28_records (11-s) j

def G28_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G28_act (i+1))

def G28_ori : List Nat → List Nat := orbitActions qPrefer G28_actions

def G28_coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 64, 65, 66, 67, 68, 69, 70, 71]

def G28_rankPool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505]

def G28_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 63 G28_S G28_N G28_idx G28_ori G28_coords 4 G28_rankPool s

def G28_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def G28_rows : List Nat := (([10, 33, 44, 52, 65, 82, 84] : List Nat).flatMap fun x => List.replicate 9 x) ++ (List.replicate 7 ([3, 5, 9, 17, 6, 34, 24, 72, 96] : List Nat)).flatten
def G28_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G28_rows)
theorem G28_nonconstant : ∃ x y : Fin 7 → Bool, G28_f x ≠ G28_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_enc_goal : encL G28_f G28_rows = goal 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_proper : ∀ zs ∈ G28_xs.sublists, zs ≠ G28_xs →
    (covUp 63 zs &&& lo 63) ≠ lo 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_good :
    qCachedGood (goal 63) 2 G28_initial G28_inputActions G28_benes := by
  unfold qCachedGood
  decide +kernel
theorem G28_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 63) s ws) : MonRun (goal 63) s (G28_ori ws) := by
  change MonRun (goal 63) s (qCachedOrient 2 G28_initial G28_inputActions G28_benes ws)
  exact qCachedOrient_run h G28_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_5_0 : span (G28_Z 5) 25 0 = true := by decide +kernel

theorem G28_checked_5 : span (G28_Z 5) 25 0 = true :=
  G28_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_6_0 : span (G28_Z 6) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_6_256 : span (G28_Z 6) 85 256 = true := by decide +kernel

theorem G28_checked_6 : span (G28_Z 6) 341 0 = true :=
  (@span_join (G28_Z 6) 256 0 85 G28_check_6_0 G28_check_6_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_0 : span (G28_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_256 : span (G28_Z 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_512 : span (G28_Z 7) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_768 : span (G28_Z 7) 256 768 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_1024 : span (G28_Z 7) 256 1024 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_1280 : span (G28_Z 7) 256 1280 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_7_1536 : span (G28_Z 7) 108 1536 = true := by decide +kernel

theorem G28_checked_7 : span (G28_Z 7) 1644 0 = true :=
  (@span_join (G28_Z 7) 768 0 876 (@span_join (G28_Z 7) 256 0 512 G28_check_7_0 (@span_join (G28_Z 7) 256 256 256 G28_check_7_256 G28_check_7_512)) (@span_join (G28_Z 7) 512 768 364 (@span_join (G28_Z 7) 256 768 256 G28_check_7_768 G28_check_7_1024) (@span_join (G28_Z 7) 256 1280 108 G28_check_7_1280 G28_check_7_1536)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_0 : span (G28_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_256 : span (G28_Z 8) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_512 : span (G28_Z 8) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_768 : span (G28_Z 8) 256 768 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_1024 : span (G28_Z 8) 256 1024 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_1280 : span (G28_Z 8) 256 1280 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_1536 : span (G28_Z 8) 256 1536 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_1792 : span (G28_Z 8) 256 1792 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_2048 : span (G28_Z 8) 256 2048 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_2304 : span (G28_Z 8) 256 2304 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_8_2560 : span (G28_Z 8) 175 2560 = true := by decide +kernel

theorem G28_checked_8 : span (G28_Z 8) 2735 0 = true :=
  (@span_join (G28_Z 8) 1280 0 1455 (@span_join (G28_Z 8) 512 0 768 (@span_join (G28_Z 8) 256 0 256 G28_check_8_0 G28_check_8_256) (@span_join (G28_Z 8) 256 512 512 G28_check_8_512 (@span_join (G28_Z 8) 256 768 256 G28_check_8_768 G28_check_8_1024))) (@span_join (G28_Z 8) 768 1280 687 (@span_join (G28_Z 8) 256 1280 512 G28_check_8_1280 (@span_join (G28_Z 8) 256 1536 256 G28_check_8_1536 G28_check_8_1792)) (@span_join (G28_Z 8) 256 2048 431 G28_check_8_2048 (@span_join (G28_Z 8) 256 2304 175 G28_check_8_2304 G28_check_8_2560))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_9_0 : span (G28_Z 9) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_9_256 : span (G28_Z 9) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_9_512 : span (G28_Z 9) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_9_768 : span (G28_Z 9) 200 768 = true := by decide +kernel

theorem G28_checked_9 : span (G28_Z 9) 968 0 = true :=
  (@span_join (G28_Z 9) 512 0 456 (@span_join (G28_Z 9) 256 0 256 G28_check_9_0 G28_check_9_256) (@span_join (G28_Z 9) 256 512 200 G28_check_9_512 G28_check_9_768))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_10_0 : span (G28_Z 10) 28 0 = true := by decide +kernel

theorem G28_checked_10 : span (G28_Z 10) 28 0 = true :=
  G28_check_10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_check_11_0 : span (G28_Z 11) 1 0 = true := by decide +kernel

theorem G28_checked_11 : span (G28_Z 11) 1 0 = true :=
  G28_check_11_0

theorem G28_checked (s : Nat) (hs : s ≤ 11) : ∀ i < G28_N s, G28_Z s i = true := by
  interval_cases s

  · simp [G28_N]

  · simp [G28_N]

  · simp [G28_N]

  · simp [G28_N]

  · simp [G28_N]

  · intro i hi
    exact span_ok G28_checked_5 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_6 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_7 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_8 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_9 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_10 i (Nat.zero_le i) (by simpa [G28_N] using hi)

  · intro i hi
    exact span_ok G28_checked_11 i (Nat.zero_le i) (by simpa [G28_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G28_initial_perm : G28_xs.Perm (G28_S 11 0) := by decide +kernel
theorem G28_no_run : ∀ s ≤ 11, ¬ MonRun (goal 63) s G28_xs := by
  exact noRun_from_barFastOrbit (k := 63) (S := G28_S) (N := G28_N)
    (idx := G28_idx) (ori := G28_ori) (coords := G28_coords)
    (bw := 4) (pool := G28_rankPool) (cap := 11) (i := 0)
    G28_preserved G28_checked (by decide) (by decide) G28_initial_perm
theorem G28_no_small : ¬ HasMonoSize 7 G28_f 11 :=
  encoded_mono_exclusion G28_f G28_nonconstant 11 G28_rows G28_xs 63
    rfl G28_enc_goal G28_proper G28_no_run
theorem G28_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G28_f x) :
    12 ≤ C.size := mono_lower G28_f 11 G28_no_small C hmono hev
def G29_N : Nat → Nat
  | 6 => 74
  | 7 => 513
  | 8 => 1007
  | 9 => 411
  | 10 => 16
  | 11 => 1
  | _ => 0

def G29_pb : Nat → Nat
  | 5 => 7
  | 6 => 10
  | 7 => 10
  | 8 => 9
  | 9 => 4
  | _ => 0

def G29_records : Nat → Nat
  | 10 => 0xb501d0000b902103500d0110010040c58250074290390c9
  | 9 => 0x402102980cb182d80014031702998269021f4a570292021b031c0dd901f9010f0595820505f52a1708980e9046540b50040902950312405001048659105c8c02031625658253075e03930e1f0a5a0e1200d56c5800d48b800257007306190057429005918fd50dd5825d079046560b59028a49570415037303d7069b0b9c0e99001784d50ecb0e194dcb01f563922716007082d5255182d707110b5100118510101c0ca1006522fe0037418e00438dd107146cd981f205db0419101e0c5401d90b530ca00a18830802524770217e620f039f03f003d001136384431808978fd60b9d0f1169d801d0101b825102891055001f0e9846520ef0023506960e0e0559040f031e05990cb004100f1002dc03910111029a02580b91035f071200790edb099740514dc200598c824e0200d30d1145d10dd8820101dd0019015703f908926cd842910918011408884293001a035188d205d946d082088fde03150cd10754004688b225d5035302120b9501d303d82bf50c990414099e0e142e5846550e940bd628d784d1041e25854e5028c8015a101703792be507198fd20e5481e50197023201160e176389019a040e25508dd0057546d10e920bd24025216e100c255645d00a9847526a1200130015469401d50219011d6a080e1e01d209174755427903e94eb08fd702bc00000c920cc18e1169d20e9f03700a480b9005904699104c28d803ee430e01e946100297101a0908685810160791011f8511271584d047310596021001180e1b4c050c1b8281036902160b980b58039402550ec20e1a099c001003fe034f85150bdb01150b94418a0b990f1b03d6620903980404006709120e1802110399a69047514a5e4ed022ee03500b93041f0dde069582d68eb101100c9402130c160215475b0066019e00410c5001b5071006f100d1079505d40e1547500dd42e828ed10b5d01d1001e430a0c5988720c156a524756469205920c120759001d0c98051900dda691031a429d0dd70e5f00404ddb0390021846110d158fda1015021d2c520dda8fdb03d54dd282500f120615015e03330005004506140ed20a586fdc03b001d64020061b109c2e5900d0095e061e03d20cd40771101200df85160c9c113003db69c88e10684888570c904730
  | 8 => 0x213b4403b1a432d0289680856683f93657c29015bc8141e1098a808d7201eab81b0450602ed466d2bd68381c6909b184b18b0c7c401b8d90b50607d472bd5e9492040d99c224bc4056811780c2e693050730e2ae92c3083caa0080d44c691a431782652e18f0660e1503c62c0786c4551901e7e15eaa88fa36d89240354b879536102f606c8c2583ea0a1bc2157a07c8c45677067b150f9b88e8c22122a40fe200de681e44e01e6f8483582385a198f60c141a0655425af818d51826464131380857a008990b6b3a606600ad3697c4223678865a900453211c656fc2441f4f4bc23803d5b8254c82cde43990add0c20b4aa808af43389707d1c03e1b0001f4855a00b2d00354183c1bc3c248906982bd41848af415cfa4b14522e6f97f464011a04aad00854180f37485e389e56584da4d0c50001106001400368135523933881058a72923a92aaf43c9ae92e410ff4dc181cc0fa6d0814004f6b042de50fa4002379810aa9202ac0fd1602cf72363908426c2231104d572562f042aa83d92d1e49010a51c165143f57a1fd7c6387e0795804289b04abd033629171ca0c2aa03ed12155e81b3290d8a80f3404277e06540e080e6132d08260704b26d8fab2852990176b30f3ba0c13646c0f104800233c6a1d36192974e5c9800554286f21a56902755c10514099fa45c7c25e2687d9042d1ec44f1c2cc06020906145a0038d109941c1300d1b6921cd678266c1174088b99404f06467832850b0173160ecf109fbda0c29c3802e1e4b952628050a5c15f3003e366388401b440264c608c9c0d294b1b5640a13e1f989036ab80761001d7ac0caa1016801f5ca0628a51e980366c05516c0da0807eca71a51c0f12d0859805003276b4800b404057ac40fc84099b132ad0b9b804393021683104701be0cc409f2d248117138042acc8ce148ec4a0134085a3806acc0fa20c17248168d62050069d418622651a0e70806f43e6f8174d00f9b08608b0261bd172c83c1608db9305faa8203f03c8cf04c7209e6b00f33c48a9406f1c81e14b641f58ba3687d614271b42324921da007cf10373685ca6603a8a000a4067a000f4718806c1cd5da18bdb103282e10801eef0506541748d8b99ec6d51254c592fc7085a3287d19046aba0f04007cb945c020f25d2735a01c57a828736036831c2ac039d65bf1e0696820b1949e06650e7d01b4d80f2309c18457c5e00dbc83062d1b5a0202aa2761a80f4d841e42d277b0e16802032823acf0c9456be46c1c5141d8be1e569816a091b46c08d6045c31838bf05552e098f8804990666e426a64011545146a44ca2837a90960e614e0c0289a05aaf415d5288d1926ebb8204203057a016c27082442062d1bad0d270602e7e828de4add4884f8c69dc9b642a43bd48228bc2c62bc12a0e099f82039300d5ea4348d118208d18b01f54a71b148ba4e47c7203e9a07098c3a210042970c6b40690b8ae88009d3610141889af039e0003d94695418206301331618abd44c378301ccb2c1856f1c825a48854081d899045944180031c22e0390005d7222e7212c620422f603efc2bcbd8835f0325a10614543e0802f4ecb896f05c9b6384fa2337c000db16ca501e270373c4215a01dd6703eab8230dc8d9fa0207881f2193f5a4075a08aed02a29082caf609ab6076a471a1a81b1f0085541e42c03fa3843136245a007cca00eb192b3b00192e192bd01caac0f42c102ac06f002fe200273580a57ad6d852875486e3300dd8b04ad00ec582671780bd940a2bd021bc8074443a57a8e6a44188e117451061ac45d5b8d095412a5c2f9c416ce82be15872af58e19400abd6ca9c0173c433160e060c1013180829c016920786f4025e818b303a6f20451402f8407925827e0d1d6a42bd4ba1f59194e4802c100e08f0763fc101a21488403e0181f04432726203790ea6bd2630807d9400acc20e0901b56d17ace05ed40c1c981e5542fdc503c5ea182083c1cc0d9c222ebc0bfc405d04c3326a9e450029662071503a5a057c4082555034af54220c05d470d2b506626191ab247d1803ea6a1829c07cfa84cd12363f32300822e3857d9823ead81c631881161ccb72d27ca43dec091604cc810c76284cb301a72607ed1010a38092e43b20108d3d03753006b40099e24ac1c03b8f808b421008218ea40f6b492c5242fd3708145620748075d183b010318b0364e27502c0f9a31818803a6b81b4d221d30142cc4186a2486260831002a970286542ba613ae621d8ca256cc07dd000f9aea14f90e762943b880ca2807c9c0395e818af411b2815c650ca6282b970006f21e4f30356840f10009d9410c4b43001c685ec3759805000033c141365207b104ac2b0270182029e34248209450d6771174f40197a026d600d4cb1333cb48ce1e56a8285212b1001bd8b4d2990789990b1500fe68c7cee0bf2e2170dc239d003f1c25626a02e4dc4d36d460c4bc4c0690d50153280579057ac46410c03598044570c95520b35883c665940c0396800f34406da012ed60fd4b8754990528a186c50506b0622f4221ac84c1009a3511b460387271a12e0caa720f2040d53242d3d2e821a1b0402d532d44388266515f3b50a5a006b7962e8c0111c483d840df7b0355eb4f8308b80604f892563ec715508b9af0817e636b432333c859be14c6546dbca23150098c10515569bc105f370100f05e5020365d38a5000e1a21dd2605039c5f26e3385203c808408e11729c0fa2816b9386aaa0200d807a321857c0a1550035e44691c8e7358205200e3f08ac900e2d043065145484079941c15504e3291b5c8041f80550b0ff4207624c0dd940441400e18c5f5f026136d16930225806943c3b210ca69881037c6ed2495194c7c026208421b5843fcda4aa9981a2bd1b5c40f86e1973511662a6748c0053201c2602a3581f4fc2ed36020d102868913a6da5554022cc104829231c88bd4e20c9b074c5b16e4c2857ad4735004c9874a6594184d4c380eca3841bbc32a6a52cdc6824712b0a43ca2406b930862002001406dac1837984d6806631429d36000730cb36c0f1340a11705d7c07752000b322e14016a830577105cde5016f2c8c8c81e9184ba6c15692e009b0eeb4c141bc31532a14210369b074b3121b10172bd0594c80bcd12f24805e9b8408304bc000853290724a364902cd240f89c97cee01e8201229d1772600041036571174641a4c607e031266b947c18ade9248d5b0044ba0c42038b0046c9a0b54b87042095896226a4085c9a1805c101d298c5e67039c1c1cd0a6f31a09861ca280b4d103868860e91009515fe601726641f884366f88543c3c86a03c9c670c5844a5c0ed8a08003036ca038a6400d9801cef0603787eb302657a198338269f81f9b4066f205f4745e7400f1c91baa207f1c687c4018de4039aed2ad044c3990b35dc1cda0143181e15885012145321d9348c04d81451d302b045c450cb62808014143170586f024379170fc27dad07ca261e2150c41a899c250c542f08334eb41899dc062d00007795f3b20783887c54069bc8084d02a28007cae03f1b0774f491a3648d181042421b2b009ace22d4e2ee5280b23d300fa4b0a401eb9017cd18e06cc40d17042084b194285a00b5710362701cde5175a0198a08c85e01429e09a0804d724ef628761e42d55411ec2027cc12c6600020116c3b0966b0234d91dd8b19188
  | 7 => 0x9608181e1a92f93f48623837b730be4ea33bd14dae8807a9323e8d9099326b660c888526160ec9598e022188af9bb22e02a3182e02e8fc07b4b81e63809e3c036a8d8f9de0de72e8ba8b0c43d485a7305fbb407aa708681595a4883ead80f9490767a095a752bef7831a540e26b8338eea3e40c08b0003e2590babe8262101b9e844f61dc0b5c4876e0b29f7216acc40b2f03ed40001e349061c06db825629c31c8109ecf438999a3e9e015eef0162d432a3720ed2d0da4e01a9bc25fe942e448959bb8c8f50089f9486f6c058bc06f8f1c0b0701e441a532a0ca56e83948816678258432560301d8140deaf832af243e4480f8ed0c63c8078ed04edac85a3f2becec37f9049e9a8219ec256521ad9824262b92419e83e4b809fe982e4fc07bc101e76099abe01e2252f843227f500782501e8fc3723c09608c3faa7836a2d0fa0861697209a1f03e63007b7382e10c9798201e58d09a920e61110998c01ed3c8db4f4103d485aac0e67f80fb9f6be708379e8056da1c08ff112c0c07b9f0ca30832a8403ea4583b37236e340fb820262f08dab06bea0007acc0a0ca9a2eed01fbbc27940820204302e28361310f88943e9388dbaa03e0d20fa8b03ea4c8fb8d09628e0fa9c036110059380e6be62d97322e77c0b8eda26e803f8664c6570218f24c608a07a5402ec80302636bed120c0f543e4e089b4f02e11007b202161503716d036f05879de8265c683a8b0be665319c229051a8632511204209b1025e29c8dba0216b3085aa703eb302e2c9266f580b9dd83eb5045a56216ede07b556823f521a480143d595807630170af8f20882060e3d40b6639098ed81ee78328400261108b8968260960581c2de10c8b8258da6c82da9641e52605a8b45b8b022a0b85bb36321b80ca04c002010be5f88bb4f0be1a007ec60c699909bd20b81b807a92256c298b9754576e00db4b03e2f019a780c8b189b8ce0de1102e2e2036e5d8fb3782e32dafb4548ec41af9610006542f8b50c04e80b9596361bc07b8d81e544b780a04e67921a750e224c2fbdb2161308ba360c6cec23e2c0964fc858894185049588121644114ec681e7e42718705067925abe0267742f86a03609589a3622e3840792e03ef48079fa8c820437b590e0b18078e201be408fbaa4176798f86f0fe1180ba23656d148fa0d4862060da5a086032079bb0ce1a80fb2008e7910d91204e28c2f8d622739c8ba910760dd8fba0036dec0d83404e0182fab908e9a8312200fce42323900b29bdaf82200e4ec0db202bc6e13ab2723ed3c31be481e088219bb2169380fb3e25ec6409d4102e32609963256276898bb2de4410bb416be9203ebb2216cf83186803e775099f283e95d899de01bf50159e80c603131a48266d049586a83e0c403ac081e3c827d9e256d5825b6f2569502fa542b2c65af9ec02e2f03126301e8d839e12816bfcae92a426c802e2636be23885b9f2563c807a9c2164b807a7826ecf4218b58ce3983a9330161113188e26610c2dd444186792619e486dad3692909ac54078b88b6c003181b03e11207b450166302ead5838264b08300b7204859a502ea4837aac0362f18bba02be4f1058a303a0b807ab32be70425b61036cdda69ad01ee81218a982ec400d98c226ea98dbb70b84e80784c2ca1780006e04e4ed26187026448059128c620406a0c011f50238a311269c3282e81e2740bbd24626d289bc1112a6c95be421751885baa0c0b2407a4e24e0dc328c50365642d93a83e0ed389f282edbe0f97501efb88ba4e03739c3a2ed03ab749394060e26cafa660885120780c0375059598281e23807ad12368d81381c692c8d2182208663a31b3d0b6e184490c0c62d40d954ab668109bd943e8fc282cd102c689581b01ecdc0b98c486d560786825e238079a58168782186a2bed5585ab60e6dcd881410fe6d98b92e85e0dc07b3e4366849593c016efe03ade03ea8c07aac
  | 6 => 0x961d40b98366e5ea0b92d8164190392dab65d42d95a80e38c2d88a0c203c2f88a6b61e9098292166389597e04e6d52589204e38d059c101e0a6079b848e2200798e2160a60797e0be5f90b9288166f4978e305e6402f9df0de4a00b9036165a81597a0163e8138920b652e0d90641e3f42f9e505e5183e9a22b66e10988881e0c42389202640c0598302660dad9ef0fa35e038e9a260c4b78b924e1d48587c80e028058578be2e8179b50b6796ad8ba4b67190781d25619c2c9410865f80c9dc096080958fd42664037874
  | _ => 0

def G29_buckets : Nat → Nat
  | 6 => 19
  | 7 => 129
  | 8 => 252
  | 9 => 103
  | 10 => 4
  | 11 => 1
  | _ => 0

def G29_flag : Nat → Nat
  | 6 => 8192
  | 7 => 8192
  | 8 => 4096
  | 9 => 4096
  | 10 => 8192
  | 11 => 2
  | _ => 0

def G29_seedBits : Nat → Nat
  | 6 => 14
  | 7 => 14
  | 8 => 13
  | 9 => 13
  | 10 => 14
  | 11 => 2
  | _ => 0

def G29_seeds : Nat → Nat
  | 6 => 0x11ad004002d04f000103940ae000c0ec000c0010138038002c01700240280014006
  | 7 => 0x7f87bc02e2930320054c230032c115001a1ce06a80c2001405800e802500583be00253420030d6003f618103fc003002003585e42500008001023c3c700c61410a6c0af0318005012c0b184d801d1afc02c0004018000c0140bf8007002c00c0014004000400500180110048016006402d82d000102fc01802400e4000800404600150c6801d000c14803f40150280047008a08f8148002004204480c806c004403588040010014001047001a002c013007006f001000c00dc08300080010114002000c0138080016000401a00100020004006000801e0004035003001e000c002
  | 8 => 0x5c01c804cb77007801402c05000089088e015800082600c201b01a904547264b00b80141940a30349684170463366ce680ce00b00400100022c5001002cbac590019ccf424a3e5131cae800214e00285900101d402700049c400902d06d800a13819a4a50c4603901d825812601904500041d8004000800c01200108800fc00f3ef00d496000a17b0b186863824210028014174001001807c2c03a400b87d000c01100d05741800a803900f000209e004001c0071b100f8004108019018c5540930c5011017c030105003001c5f4006015001c080033001012403c1f4000836c1270bb022808800a00600100767de0020268248006018006002000a0b800a804808000103b055803c010001002000a004025802800c0e69f7800c03800201d04b409e0e6000800400a05a05f000807001100a021208f0119f780600561b2000814800e03c002001c012005002810c00201c038c0181fe0a0001005000801e007004400a1c4001819013a01c0018144156012004801809e00b032803009200a00e802800a003031817c01401501000e80e40a10178060004024
  | 9 => 0xced06400122401223100ca010805c00200a01a803800c0220de954848805008b00041b6022006061857316e0008048030008057807402e00a27980080c009e12e00e052c02b007070c01410001081b0048005005816c0c600401245ac0ee03806f804c02400f000810c26a009004024403600d003802400200600c8088004008003446006c00300100c000c02000c8058002003010007000a00300400ac01605800180d800800a
  | 10 => 0x499690012010
  | 11 => 0x2
  | _ => 0

def G29_initial : List Nat := [0xe070381c0e070380001ff007fc0000, 0x32190c86432190c803fe0000003fe00, 0x542a150a8542a157fc00000000001ff, 0x8844221108844220000000ff803ffff, 0x12090482412090480000000ffffc01ff, 0x24120904824120900000000ffffffe00, 0x381c0e070381c0e07ffffff000000000]

def G29_idx : Nat → List Nat → Nat :=
  qIndex G29_N G29_buckets G29_flag G29_seedBits G29_seeds

def G29_benes : Nat := 0xe323d3766f4f70941260000009300a6d8dc23c38c6f0f31f63e257ceb1d5000000ea80228851d0b18428a724e09f24500c4180000000c002a0b2dc720dc99c3f08ace195e00000000000000000ae9b03ee66cc89ab43c874e58cc196000000cb0266b10118d30c00000000000000000000000000000000000000000

def G29_inputActions : Nat := 0x339415a3a42cec08eae2074aca1ac688

def G29_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G29_benes auto)

def G29_cacheKeys (i : Nat) : Nat := G29_initial.getD i 0

def G29_cacheValues (auto i : Nat) : Nat :=
  G29_cacheKeys (fld G29_inputActions 3 (7*auto+i))

def G29_act (auto : Nat) : Nat → Nat :=
  cachedAction G29_cacheKeys (G29_cacheValues auto) 7
    (fun w => qInputLookup w G29_initial) (G29_rawAct auto)

def G29_S (s j : Nat) : List Nat :=
  qParentAction 11 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 3 G29_initial G29_act G29_pb G29_records (11-s) j

def G29_actions : List (Nat → Nat) :=
  (List.range 5).map (fun i => G29_act (i+1))

def G29_ori : List Nat → List Nat := orbitActions qPrefer G29_actions

def G29_coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 64, 65, 66, 67, 68, 69, 70, 71]

def G29_rankPool : List Nat := [2112664, 2182779, 5532295, 5250494, 5311951, 6637690, 6381484, 2117516, 5451421, 5258426, 3304841, 6576760, 2186617, 6426319, 2177943, 5447614, 5271211, 1064122, 4403101, 2125193]

def G29_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 63 G29_S G29_N G29_idx G29_ori G29_coords 4 G29_rankPool s

def G29_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def G29_rows : List Nat := (([28, 42, 49, 56, 65, 66, 68] : List Nat).flatMap fun x => List.replicate 9 x) ++ (List.replicate 7 ([3, 5, 9, 6, 18, 36, 72, 80, 96] : List Nat)).flatten
def G29_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G29_rows)
theorem G29_nonconstant : ∃ x y : Fin 7 → Bool, G29_f x ≠ G29_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_enc_goal : encL G29_f G29_rows = goal 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_proper : ∀ zs ∈ G29_xs.sublists, zs ≠ G29_xs →
    (covUp 63 zs &&& lo 63) ≠ lo 63 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_good :
    qCachedGood (goal 63) 6 G29_initial G29_inputActions G29_benes := by
  unfold qCachedGood
  decide +kernel
theorem G29_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 63) s ws) : MonRun (goal 63) s (G29_ori ws) := by
  change MonRun (goal 63) s (qCachedOrient 6 G29_initial G29_inputActions G29_benes ws)
  exact qCachedOrient_run h G29_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_6_0 : span (G29_Z 6) 74 0 = true := by decide +kernel

theorem G29_checked_6 : span (G29_Z 6) 74 0 = true :=
  G29_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_7_0 : span (G29_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_7_256 : span (G29_Z 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_7_512 : span (G29_Z 7) 1 512 = true := by decide +kernel

theorem G29_checked_7 : span (G29_Z 7) 513 0 = true :=
  (@span_join (G29_Z 7) 256 0 257 G29_check_7_0 (@span_join (G29_Z 7) 256 256 1 G29_check_7_256 G29_check_7_512))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_8_0 : span (G29_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_8_256 : span (G29_Z 8) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_8_512 : span (G29_Z 8) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_8_768 : span (G29_Z 8) 239 768 = true := by decide +kernel

theorem G29_checked_8 : span (G29_Z 8) 1007 0 = true :=
  (@span_join (G29_Z 8) 512 0 495 (@span_join (G29_Z 8) 256 0 256 G29_check_8_0 G29_check_8_256) (@span_join (G29_Z 8) 256 512 239 G29_check_8_512 G29_check_8_768))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_9_0 : span (G29_Z 9) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_9_256 : span (G29_Z 9) 155 256 = true := by decide +kernel

theorem G29_checked_9 : span (G29_Z 9) 411 0 = true :=
  (@span_join (G29_Z 9) 256 0 155 G29_check_9_0 G29_check_9_256)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_10_0 : span (G29_Z 10) 16 0 = true := by decide +kernel

theorem G29_checked_10 : span (G29_Z 10) 16 0 = true :=
  G29_check_10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_check_11_0 : span (G29_Z 11) 1 0 = true := by decide +kernel

theorem G29_checked_11 : span (G29_Z 11) 1 0 = true :=
  G29_check_11_0

theorem G29_checked (s : Nat) (hs : s ≤ 11) : ∀ i < G29_N s, G29_Z s i = true := by
  interval_cases s

  · simp [G29_N]

  · simp [G29_N]

  · simp [G29_N]

  · simp [G29_N]

  · simp [G29_N]

  · simp [G29_N]

  · intro i hi
    exact span_ok G29_checked_6 i (Nat.zero_le i) (by simpa [G29_N] using hi)

  · intro i hi
    exact span_ok G29_checked_7 i (Nat.zero_le i) (by simpa [G29_N] using hi)

  · intro i hi
    exact span_ok G29_checked_8 i (Nat.zero_le i) (by simpa [G29_N] using hi)

  · intro i hi
    exact span_ok G29_checked_9 i (Nat.zero_le i) (by simpa [G29_N] using hi)

  · intro i hi
    exact span_ok G29_checked_10 i (Nat.zero_le i) (by simpa [G29_N] using hi)

  · intro i hi
    exact span_ok G29_checked_11 i (Nat.zero_le i) (by simpa [G29_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G29_initial_perm : G29_xs.Perm (G29_S 11 0) := by decide +kernel
theorem G29_no_run : ∀ s ≤ 11, ¬ MonRun (goal 63) s G29_xs := by
  exact noRun_from_barFastOrbit (k := 63) (S := G29_S) (N := G29_N)
    (idx := G29_idx) (ori := G29_ori) (coords := G29_coords)
    (bw := 4) (pool := G29_rankPool) (cap := 11) (i := 0)
    G29_preserved G29_checked (by decide) (by decide) G29_initial_perm
theorem G29_no_small : ¬ HasMonoSize 7 G29_f 11 :=
  encoded_mono_exclusion G29_f G29_nonconstant 11 G29_rows G29_xs 63
    rfl G29_enc_goal G29_proper G29_no_run
theorem G29_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G29_f x) :
    12 ≤ C.size := mono_lower G29_f 11 G29_no_small C hmono hev
def G30_N : Nat → Nat
  | 5 => 6
  | 6 => 222
  | 7 => 1429
  | 8 => 2654
  | 9 => 970
  | 10 => 28
  | 11 => 1
  | _ => 0

def G30_pb : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 11
  | 7 => 12
  | 8 => 10
  | 9 => 5
  | _ => 0

def G30_records : Nat → Nat
  | 10 => 0x2863100402034690a49d894158e40319405000610841d2346d17451246710441913635
  | 9 => 0x95184e51a30104d15bc7b504682c9425889702d460f984138c362fca1028cd38aa2008806b851b8ce50cec08a0a5786302f442e9c3791d258b71829861dc82487940ae49dde2842f0c49163d493172852011a05c02b2bf4a76a011d612418527192dd20627135610b091847258f5d070501c916b36cb02c002403ad3c605cc85d287270a7042cd004c508185450bc17820b227d25ec88f4e2a31575769a717832e17505ee01fb922285cd080869422b218eb82322d30270330c4ed891362a5081042e84c30837064a420c612917a234611e8897e32529200d986980d33186f60905538ba604584994c93482c1067021265502260bee8226ed20622055449d49920ea408500aa4d13122881342cc8911a0a8236c1cdb153033623741ce06808c32464880e2ecd47171763709241587290c2e1feeedc073303670fa901494a60faf168c1fd11271e6478e9150932f148582b11501225214f16c084bd505084a28c02f55f852d6680c895a86f78c7606a05d9473b0be5829225601b0135e0c2901800c82f058aea41291a50c704280b931c760c5046c831587200bd81cdc4d41b8b004a74b04f80e2410702c8811c143b3c721ce8a580229005d764640014b6279242ab1548f20154a029e3db1131b9533ad0b9cd93a1e4810e4658072428505c9c0630d290c402e8e88219b210405aca07811bb1e67205ecd245a9001e72a2c43172200760c883148e3216e2809411089a537230804f129d38216834982518ba4814c14d40149d37bb7410ac1038e180ef77244017cea71674088821b83a52992001cf1483aec5600890c91062f136a32d60f309b2134e76ec034d882006c2084e1cceb2304a10cc5f082a51b7718d83940bb809af1ee69520524065402b80d002bb255800c31821924345e20c421b60953a6420e808805269a0c0082b9282253a502ca109a96b9080e3ac04dd80b2014813481db5cba2e437696a978de1183008bc217a03a0c2868888528200004814e8b5318a83a7274e85d80320405070dc3690c27306a14c475344a5464e52946178eb82d6e208ca8800d03a4860ea3d109b62d700cd0296ddb1902434aa65a030f9d6e08ce1eb97232e7039ec21d932c29446390e058e38ba440ede9010839246410a4d138f270b4a369228b804f304420c03990ea5034a128ab760b2f3964829ee52c7b0941276c88c18d22905d380421260853c621bd869d05220a6d201e7598c242a480ee22dd0c011a4f82d6e5c4f34215f12ecc135cb1216a529c18044ae2158370431c9c32384418b055789ae178214ec2f202b604111c4ad1204f20d498ab03041da70a53205429c8de4b14803482f287bb404c49b23d3052e0dc82c90fd38c2e00702edc6d84cb71e4200c8032823204410b28b99842e28201bec19d01af0c6e2ebcf130c318e011688e0d062626505e9801688220a6e18ca3d640859e023390e139e37af4846a241b09a6004e66e485b9425187030b0e180aa83c4e20982e9048721470b48113c5b91744756e175232614c48aa0e538c65062907e88d158a533711eac99399aa1dc247245b58d64c160149c4f4d92529475c91198572c036c068715c17a7074834bc55c0f25b44a289e3dd53a52a463cec61a1cb7074c5a08e9883ba33462a8c7941d9b19666ead1598a828e1070e80d39e288e5c12e6a8485f6065e389c5148d32144d4e980d253909e54469010a12278d7620ca07311ae23722f94b7a9d7bb259729823880b9ba4c4a9859383390368039cb54113a8c0460b101b86232246084c61303bb8b561fde4058523155844b017494a4c00a849499c80f83c76808ae94802a0072520c189119013481098517ccaf09d844d4020873000b072d885914300c685c0b15219b706764cd4199133703533abc915d8b8425848e82151c33c56a50dacd106000c7474d8013121008743b0625b4ca7b934809c91496a9154800dc69247a30dae66becd28d25bf600a983f916a2256030a07504835406a26c002d820f194a149495781e10c1407e0e1890a4046014a011b11b7037453a4610972009743696409823b41711e90bb28625081e4c8cbda94ac00500cc027d06b629740c9ec5d550440598294216dd301a70449051411a6454e34844d62105894976c069a822300e013dc7145864037078c8b941cf641531e9675410fa1d7670a461582a4065266a42b290b93a4634d0b9a8829252150248d80a32037605e031504380a60175c2d61c3800680698e520f37376318908540a251e6030c02e5173724138a8806c083b09706fa4712853206482668f1147072a4a34ecb831e38155200cee5cc0c49e5e1f4acc140a9266466a04d141058a2572c05d491250c2434d8710972938502cdc51202b0b14503969d81d27b14e54a48d584a6137402a029602f238461c9851dc7b8295c08b871816a7094e2eace1580b62f5e5e9469b80bb86136298cd342c9008e27de6590427082f68e915c942719c20014a984d1a3a1812a42580e2619832724a119376008a063e755003a384c0294bd403ac37c80c980284ca8
  | 8 => 0x571f22987b171717d501aa0f2467b23b4583a391a476086db3986f17d77a601b9813407f5abcb90119a21c31d0db2d098391e864aa0622469719dcea636a0f931057a71cad01732c170feaf5b605eafc1d178c58d0bf562840f4042029aad42b072b887056973a58d83b782988a8e2deb0dc3a219f0df111932c03929bb0591540e399d0165e2962c50bb5a409f419a379e07e959c603bb9135861a7178a186136412258aa2149a63ba8e12214379015b601b1787879235e229c629e05cc13bb098f80bdd19dae227b811cc9c3a00328c9095ac48389d266250dd9e0bd49a59493a5db403423f89e001f017cec0dabd004e6858d988f27051d48404baa3420b84f1989e0b4db9c1e50440e1ca910613114ab6aa1f608c598634609b713a999af4521a35e228d4afc470b8040b8f92e65a8f89a262af3fe11137a71b1c3b75e20c35a15ac2b958d95a9a05f792184d8580415b9237ba1a919f9e1830e93a1e01709f56229ac811b6118680c10e878572440f241ab260c840003236250dc8546a31958121a9c33a67b903561a71faf40e8a2ae02d07a29fb14a0f161830ad9f03d8013f8128d171a5e207f47890c83435e267179e32c91a022a970959dd24aef23aafb31f0bb1d18a30c938620958606c1b004690db763278e9035a17df023b2b8198da5420378e18946911888239c60e641901751bae2147a73498493c1b0ed178c46985bc106df00b8688a10e0471fbb3268fa0717a27041d48f0c81a6410436700c0f01020197a73a5e2c11c98e32d252efaf71f059d40d8f91789e09f1119d3411a772e58d23a570c35600820065db2ddd107380b11f00da43239d034963198571f89da55b6af4201b809065e205469960a88624caa19f181830db5629f799988f128312358a218493067b145e21dd50aa13609c1e3a9c21558d22dce1c7178d5e222f313a40f0905900a25aa3bb8f83419cec24868234e61a6259e1222381d0b92539bc51e831325db196972b84409f5a960c6839f5267a7a701b1bb5e84a770bb7a9c07e03f5c85cb38389e09b560f93f2436ab15e20c3679c35e8b83417b9a8c40f001171a40f2169703809941fe08452220a81c452046411812227dc6263081b67b858b18a0c88435e1c841016970fa2c0b8422ff811c356166970058d178454019fb2476198fc13f962240e17d34302be1580914a910fc138131723f423a0148e04b1a08c1b46920df0325e2b140f2158aa42dd9a34639297349c72de0393aaf8c219a599f06ae627862903b32417f1440f1194407ac7078f73a6db85b30084e6059b70829e38e1e900e3275e200c529e2fe244760d95bb75db02d0d01f1724017168fe46acf0578e1671723dd11d8fc276970c6db0f84f2a08c16b928d95147acf11a0dba9fdc48dd379a3c13c88b8b72636b29af918899a1b7016f319388f037a725b42b04769810d0d93a0be09098d9325762689922c0e8e586264db0da7485808403a309888402af164e683aee241800758a25a160a9acbf19fc13b4839a313f7b404529fa50179bb2d11d2410d001272e67bbc86423b21a40b9118f8942af3caf90db8d0bce340861858401e8a7a415417e548da020981e8fb6c039af03b5183866961d61781da540f0862513f5a1bd831c47685b761b983b762593d9f07f2202c7e8db6c06379b76970040e881220c5b605d7f859443981d382ae1a58d8c0341540f9c222195db07ebe28a9237eaf134200540f281838e36b16baf181770f82527f428d7a725cec2da03271ab0df6807625298830a8f219469321271a67b0df569fb78194762671f324e6333be85a738e29e13d758418335886175b6083b30989a879a30d8d923b3733886136dbad78e04ebe24da9259958b88f87b48149a42fae00e31d8584409f473a86415d83a619f0c8b1265db2d420b90fe2340f085b619983146252f35e8395d016db9e35c13e6c22df032832aa36a1c67b09925c033105c620992d3a2aea79f3187170a11e1567b0995c3820308641221770ba438e034161e2c69fb8c4763b31000f1f00b8e074e60ba8e95a73a1886098a90b882a201b8e131a42be3ca6a1dd8319d4909c7e8baee387a7b32ddaf476130c80146917a378b9122d3be85b25260969c46918697241fc005e2008690c094a5625176970caeea43630fc030b8d912d492840eaf4e606a911bb49134690f8bb0fd85843173a78e07fc637107175dbb3067a1a7793ebec0e710545293fba0c29e394db007179c1838a29f0c4522a18307c6742a6f1bdc323b0908baf0a1d48e0941b78e998ef341ce09df0260940013105d318bba1164520442011825183a40baeb26dfa3232c135b612d838d58d00052405b61735627f790a58aa83c63bf812d9d02b88a05dce291ab17b4983837260a8a22be1a58a0bdd4bf3bb27825263711b40e960c885abd0d84f0e6252140eb707e009e21fbb823469c0f2625f81216db1d98b42b3d149120beae29f7b309a809f68a801b14a4e0fb4013697001b61dac2aa2be001e23a3312817f12cc807d3190201901229398b3febec79f30098603e220fa0b38127131311e3562ea680ba42064201bac40a69701cdb045860fa132400c01e7b160232592ebb13683a141c01717f5e389061640f0029e400141b57605f5609ab404476218f9259af0758d167a7af58d406973a4763240e1c62507a4493b45308b2184523ca6e046973202339a5b3b2710729e8d65a406db0bf11bdb4c0fb7a0984f2b945bc0ad0999501c5285fc60c78e2440e3491207af61bf1725d0700fa704d772629e00db61658d036974699c19ba115697a83ba2435e4040e000c82640f00c0e901190a5869a1ab05b799e380060850010700697c51fa0747687b40001351778e0798500452144690986d321f0212af0ff1102c0f0713d23dc60f8402a11d1de190ddd4982030c3ad22f270019f881d79032d2618318dc93891a0835a1b5b60a3ad2aa1b242fb1c40f09944187a72e1f000de2264761469707df015dc6005b68940f1c5e2960e634b58305db082ec0810e0999c055b6006db040b585ab40ff0303e5422c471dac48c1d71fac4298e10ff5613f5624d9f076411bb2b246250329ec4e09028c8236db0013d09476878f8c040f074db818763a1ce09bc5811e203f1d861c61f89e1a2223a71f0bd310011e8118d2718383dd6319120598527f818e3678e40f078128383b388eb13af6a585b19bb80c05106df623e6c035e22e2038e15a18d9f19d83144db17d832db2917c171a35c228c58993401de20eaa3161310080e8ba02a38a20fdd4001f6080e30615a326971a5b62808caa0e81df5e07d853c2ae09a802b933284db9607e9438102efe0019e8fbc528476303ba42b453714909f8c0e5e2085e20dd3119d7434831185e2c6b1abf4528ba07274528390baa396938e189717241743b81d082f4381f00b8403078e1de540ff5a13c6222cec2669791b760158a25e098b0c83a4db894e60831140a780632d3b1b203641349d50629e14ae6243a338b9214df040396048f8235b60fabd29ec52588f215db18b2bb16db0db403267b0365a015e2b740f038da8bad90babd8b40e0f9ea8a01e94107199dd14b4427b4c1da3717e033265aaf5e227c62878f10f8f9055e2307170e4e625aab0358d27b4215af28e38c1f8091ea4ebf40f22a0a8e356841190ddfe191719b8ebb2f26848f91f9900d8408967b90347161d794331174768a1340171faf67b95983014521971f174db878680e576962fe9b07e93edd0342085f6385baf8793f169ac95b2caa14909c6705aff3485d86380a836a2145223c620b9d487b0d23b8113f423a38e8c13d3406729b219610715990078860dc341a40e0df4714476859cf1767b118420993a429fb08347191c993d491bf5e09b471fa371858d03c0c43a8a93b210640e3ae7128420224e613b5a3a7170d91e038f60fb0004e541caccb16259e1e513e9e2daae93a730fa0a0b8b005a260fb76161771a3a429b7b05f9640641179d022d351db5e1678e9c1d604b3925f2715d1d0fd3123af80e6db8bb7c1481a2e40f242038bb6c0df710e58a043478a1542e40e3f2ae06371165b6349ad20c20304db12fba2119f2425407c1e12eaf2e1f60d89aa54e6bb0feaa01b04f5e961c6036254026c97d358e0c805f813b0a80ea580465a0aaf51ba37aba6e0982522a1f00ddb8e2012837916a161fb492393e3a20385a070fe9ea62bec61fa082969038c8a1d723eef89aae23f278a2de97a03240a8413799c1712418304288155e20000f0ee711471f2471f3967b08576981fe0085217a8f2486f8a32d3b9d009bb623aae27f6a0158d8c0c8089a3285b60bd344685a13f6a40381a806219d770430c05de505f6a16f2724e1d0432d29f4206f61339d51e254242af2cf1d05420242ae9a17f2fd9f0dca88778e9c25313f6b1431109b1185b21138bb2258d8d6db2129e343ba323ba9038029baf05d8519d3521175245b6034e6b0697248d8084690c185252be0858d85a80a819f054e62678ea567b1435a4385b08308241c639a2703bb109cec1545283ad8308070791e1940e81c760bbad0dd9f3a0479807e0f8041435e0e5db055db0311908eae93b091a6972f17102dc69b1fe25b0903b73b167b1daf21a13d1671f895e22278eb74e68971f2158d1e31d8593f3a45205f428ad3403c17c1171118f1079b8149df880c881ba707b1107a2e8385728afa0bf5a25e1d0540e0567b01c20098bb1a00c1a6dbaa26c81241b94529e180175e223cadb15b60665a071191478e859c60c13185a7d156db0afbb85ebe1d1d60346919d9f9e35e3c95e0a40f385db030c801db68638104fba04625036db15625bf5b600e974071f0d8bb1b4db1510d2658a03fa4a73ba13d1918ab80da778b89a91a431c4208613d10096a72be1878e858f11440e1619e8c24c1fa8fafcec1a42033b3e19a8f2219e166db93cb91d98329f461889e001771d32619af209c8cb940f0f8d601edb818528e11d0b8d609aa4384db12aa9009db305760faa90c4e6bab2623a7326a0b05dc695ae09c01324eef228e10b95b14c67c1342178091e19e178c01c01e1535a08df01b9dd0f9448a3800440f17b2b2783a9e00c879311771fa82af042b99c1d725d34179832596a8801e8e3038588f02d3683de5a81fc0740f8a8cf1193f2688f13b7937f6a03a771340e08094369072f82727efb09a02396410f9af23e03255e20c697222540c29f11bc10f8f122c132917f839b1210c838d278392d8792d0001e188f5a740e145b60436b29b79038d10040f15df69c2fe9605c2e4528a367145db2a1ce0658a9c3a4812db1942009abd2267b429649e10716476a5697bb3273c0ec2264187f0dc119f1514f0a5e2879252202323ab585a0229b421846905dd4859d800d860a8fa429da1a86c2740f9036b016419818614df689a07a5717c12afb0625082882e2dd1a4e60daa3b12190605118a3e04c1b24f3146866ba1f01195baa3a381297166251467b2e91207697a7149981710a420c1219af40f22625017a7164db0c32d287174288b285e20b9f20dc9688219a41f628883c11a9039ae265b63a0ec144e60bc130fc342140f320670fbc11f8ef0d99b3cba8016250840e1578e274690b8f71827b428312642023eaf09b5aaf7a70d89504452980c8007a717eae0c2de057170998f1d1fe1f9dd2f8571b5db1a78e8a34709d1e9c35c04efe157178a13194342046db9386f09f8e0b8b18db15aa1c60ca8e05e6c85b4b0f9853858a1bb1513eaf25d35243a40746908e033cb0729b098d42090135942ef02a9a03eb30bfad8180f405e2135db2f1ce11a6f2ecec0a3111b5e2082010058630219961ab2b8e18bad385d9f3f40e1507ec111989697244e60f8d923baa17469045e21c17707b22ba209c61c385a9a8fa0293aab0d71f0fb5a3aae236d348488707d1e0dc1e3c9f38a29ec296e056252a9fb4287b3aa6d0b95dab88f31a000f29e9c17f3da27001491f8fc23f118f85503a48062de83a5737aae19e1d306db8131f065862135a323c6149f8a54521740e23a56186db1389e01a7b23eae89452aee090b9af189c98e35a1bb19900c82a87baf69700e7b24b210480d0bf6802c1327d172114923ac08e24c9838017aae97a8a8a3b38593a0340e0382c0986809eae2d8e70c38c07a6e42ba58e10e45aee9406218d3432452244693a7a78d5861a5db95886376db3498e0630885b6c458dd0036a2e219aa3c89a01baa2fb03d770e11e155db0e67b00209285db195b60fba68d89f146db3694927b7996331b9059002ae15c23038000af2707f11a62dd385b60a6db1386d25a8e0429e87a4229a730fb5300641302dd41127b42be8b93a1417700c200c5e223a270b9852445217f6118b6519625c12ef1f98b8634219ad9265e22fd4917b5e38b0f287a73fd271365a23697084764219f37d9f21bb80658d03bae81c0f09b253c2030f9a3a81abb14db0b88825dd10c11e1c5db251ab8584f03990070c8044db23b2825a579029eb07a70d9f128ad006469359d50bb562baf68100e27b21243960f8420fb0314b742bb9f07f4204d743ad270f9f209853384202611e2867b0405120c67a55db0771f02c5c9a1e52878ea8149263799831f29dc620d27ba07e1e08c1967b245db09a420782704d9f04dab30a000c20193b421c40e840c80da5815c6709aee8105211a428bbc51db510d83491bc51940f3865a099312322b1582316641c04768a36b00013b240f8588a243421c69783b1929183468ed35b3ea419f9015a00c69396972fb6f2e9df8e29f90085322dd1bafa2811d38641239731907ec6a951adc3056db858f99e2b3067a70dbc1301f00f868bb0ad005dba82be0daee979340bc1ea826c09b7626a640fc1e85bb819b5e30a8f03af20a3563840f1bd5032641b10672e7a705dfc3065ab040f0611e8e0b5359122b96ab140e2182385a89878530b93109a7438476bf225429c891abd422ae247171d9dd039dd076db22cad0bc3426b4f2488a0609683a9c0871f099a326a8f0d868269de0d842088590fa9e1d32c0bd750bd9e243810be1e1d990b75b619f178e1d7c058d0a83925f4611860a571f224200ba130740e19ab10bcec0da6300976b771f044e61a5860d931a414929e092a37917dce83c7e2e1c6398191858a2d9f0b767b15c5e1da54039780d8d6176db213710d4528d40f1584993b5eaa3c605ada281ce23ac81800c003421dbb82235e043710ec9c8593109dd10b91e261ab89aba0b853a83421b40f18f31001ce1bb510df2d0058a21183879af0d9950830c02f2c00e253a625aba36298441b8c00c58a25f111501b1a46910308858622bb0942a7f0d925054db21c231a1830e4db00f172385719fbb0d9d4409f7224521835e182ae13d5013dfc861072617f3040e220179192585e2b0fa423840e0bf8106452019db09f7136935002dd4683f06dc6bc96e2ba7342ba907452384520080f19b512e2ae9786e0557630641b932708175813a7baf260008c194db24cec8d6410bba6222af0840f8d86019ac2a57a70629f2e9b1868f12dc7e1bbb832b34bf5e2174e6c521e17452b21d60b9958e13d1307eb058d858d60446917a54087a70fa77b0dfa1b98b38bc20640f2e5db019e229862080962dc478a085a93ba0991e25f4200371009b605a9e1a7a73f9af221e5237a7858e142a212218384150810e61b6db09a770df5a85b5b15edd1a38089c131cf2685888858870e6970a89905d830bd9f42a4e2f88685d493f8711cb2615df0176250ba39333c69432c3201b03d741358d19abc003618b5b61d89e2386f014e68781e0bd1e23b423fe191a452bcb2f075861db9c051d702cc80634716cfe0836b275b6286db1640e9400f899d00a7a71840f3258a3aa712ed9fb071f02f3114b7017e1d981549c32c06edd1b8fc93a893965ab6f81134521bb789a1d6225e2980a8253ba1c08c0411e02dab00adb23452c51cc8da4287a6f1781783a9386062045db87af04020987842385e237b5d24177054762871f00ba703a3785fba0fbad18222038fc1d07e1c6db177a70711e8e30c0d93f01820878e9b757699a24085db900b5180170098d1517f2501b263429c1800db71099af2858d13f5e0e40e15f1783d7f1a8fa064e62da27078ff286252846906c67a719f28452407a78b1190d8f129a6e0345217f1712d9f09d310db470bd85404e614ab800edbbca503da6e14420082b99600f282fe1665a878252e5e21bb9c09b6cc13a30db5a006251331d2635a01ddb0458a83ad915420251830340f8904bb14768db199c1ab1789d2a19e0d8880165a0a9af0021d21c4b035b63a5b6a82dd8e4760bc850c71f395b60c7a7838ef903713cb4c215e28dbc5818e629d1744c143c32717c671797705fa3279c6341f01b99028586aa3ba93b811998b895db07df68589a878bba61499611719eb38c380264e6395e2075e200a9704d490811e05a5123a0303a29343c6b7717195e28f81904d83941368a03437d121999019f5e1892893b55861351d8c00e65a44f810e1d419e5485ac887a0c00c761c7a790131acdf0086970bdcc85b7a0d99c2478e1bb4318586099d81b4e6aa25f9c1221a8b402e542371fc51c300420220c881a97ad8f1a547616576384e62319f29c13410be198c026356066412640e0dd1e1997715b490fbb613cc813f790a5b6245e207f2c4010724a24055860c15ac0149839dc1b4768c04b0c1d407dd606bc937d9e0bdce87aee03c8c3c331aa92f0fb560ffad1513d1485d19ac4b77a71d809247a7b045287b47c0047188a7280c887b5aa558d19d501eb072297d0f95b85a770b9be370fe03953238e10638c04edd27b6a8604b24e033858d2faa585b4223d07b8a5089a8a1817423f813271f4067b8e051810761c5b6978fc2237987bc52f9682e64137e25324203c1ce3228d8e58d2e47615b5137fa31842006697154e60780515ebe918d90f92514380088eb0458d118f917afa83f2c0467b0d8041740f3bb9a9817f06995b258d194e617d1d0f9d48a0941825402a36405db3a4e642a953940e047a70662519b383ca2185a0a9e174aa2af326db24420b11f629887309df0d89622a3e0f8f7404db128c82f8f7981ab395db118d689371a8381c11fe93a0085b8181b1f0c6259b32c1f8c0281c6b41f685a749388a299c6218570afb409d34305e2274e60c420118bb15fba19a541083f1b4201db499407e0f9952a8b8015db2667b0f8f811995131228100f94013407173a95e85b28135e20813123cc7246db
  | 7 => 0x3654b85a6f21650abf021ca2750860a583e6ea2792e60e36a0d89088e15027a4d85e3378f994e1ea3f05846a0e7f63788e0368deaea2fc1685b0d86b8867920991645f27640a2ec3638e27a0d8e6a50390b22da929899a686e0688fa8fc1727f8d8cfc8e0b38f9fba2637c1c8d105b412078468365180ba0508e33731912c6e17f0599322e76905a6c826a4f259c80262fb879da49676e0da30a2618115c9d81e5dc25a7cc2ea35448c705f2f62782d4367208381a27659a258d44172999797f0266c20891a01f0e507a740a668109a3783e93d83a2202e7e2c486f05e43e8ba96c2f2c80791822e77f05a5782628a05a5a85669799a55c660780986802647c97928a563d2370fda0e51c939a044e7518595583e518099d881f2d90b8f061e76e079fb82e7e987a6a4261988e0c40666a80f8ed80e6b09da360826180da0509e95e89a6a45e17f139d041e8cb3181c8fc2c8b088bc1ea1e9812fc275f90fa0101e3aa8f9d4ca64b98f82c4e24a90fa1841e0809592e4272b18983a0c86b713a8b84a3e116a408368d92182ccb66e6999d140054517921c6e35b25c64702233878374262551481722e78a878f48365bd0987fc4f8b93a9a8c7674b858b1e168fd09956cea8b687a5b89e9db0da93e582aa2985e8b75e707c9fcea1b88fa44f027a5299b903667583907a262ed2da3e48e4b923a19c3e8d98794682666315971cb844d1c9d546a1aa000bd8962838f9ac8df087840a4c175f91795fe2012c93a0da4e95b15c684b63363800743e4061ba948de0b31b8da82602c059a58566bc1d99166643e899190362fc129c3e0f244000394b68953a9d48267512f8fe4564c43028886e6458d93e4521b43811368e55a9da2461678a0d8eb48e1c813a850b66a1248e905a0168991349e914338f48572938395fc600333fa7181671d389d2216836219c74b60c907a7a00e6bc14a380b87e88f9998fa365148ca4529152da7b46e14a2d8c902e19b0d9a802e675899fb8568881d8038266331c1284005ef25e2e6102768f9d94268fd099078ea95c0da1860e4431d8cbcbe24e15886e0e59a2d8618667928983ae2e7e3378e082611b3e85b0c82462fa888167e23e9dac2e5d48788fc2653a262888963f90b9be0e69ed3a8f6cfaa390da010924fb3281c8165cb03d284e23820592744e71d23973c267e82999b05893820dadcb72c80e24c66622d8ba5bc3629a279c742e9ee1324c426306138eaa16a43249d3a4e6f209a5f06e276858464567f003a470e22622200745e0ee278b1c260121ba55c1695221d048a671d858bf0be51a2f81e01672005a4da161c88b9100e05e7039a9c6e14817973c5e2a59d90f8860b523a4503e4f6959234da029078eea366b2898dd46f138391160c2410130910e61811587a41e1a09814709e46305a6544e5f4380bd8269ea09a6cd026641996c8b61801b9aa04e38f8b93d85277c19a25266317098c8b0275e23918ca68ca9385405f29314942452307839a7a4e4b583827c6680a3e9c88c85ef1791781e2fc29a548565fa0f82009ea0293918e169640dc9fcc6538978dd42604d0b9164761372480dc907e895a0d8ea38699a3604e8b90f9a5a160a30982ba2618613a5785e9e00b993c265a985a56cc62eb0b8eda0e792839b225801d44884cde3652fc22c2647f0988d4665c70bdc7cea5858393b8363c2859a9c5f8db098e74ea761c081bcb65d987886e0e604382660fc2e993816a165f91300ce6e10009a0126659a8c2248624fb179aa04a54d17a5747636a0d998c9e7a093978c20a1e859b9a369a92203eca65f48da5b826a358da3f6767453792d6165228b81e08a4852f99688b0f6a80aa85f51c0f99d4a64139d87a43e11b09a11c3693d0fa7ba16774998caa708858591241e6968385fe663d9878110570e523a56ebe5d92e80dc8e1cf2782cc0a1a90ba6c8ea685098eaa1649915a5462e71e8f81545e4ed15a028167511b8cbe4e9471d9e485a468878a601e7652da1a61617a278eaa3e3c2179e64fe3d20984648e578299330165f48b8fe60e24989964c5686907a4ba1646323904c3e8fcb284f46488539a1841f6b709a6c8303f689a9409604bc086c86e80a448fba4e0292d91362696e83d514866c10ba9749e5e398134ce08f91c8c0096a2585a4784e49d1b96683e26d0ba74236881999d2c0b2aa0ba6f42727f279870be3be8b94ea661680d9caa0e7180d8956ca7a50bd7e45e64517836a0e003289a92168ae0b88988e17a1b95fc56276859b90a6836099b505e1810ba6383e9ae058ea8e60c98589dc964cc449e04264318f87d88e6e4299e800f1d0979a86266a10b9ca8967418f93e4269898789082e080379d844e74f1394d44e57f8b94280e5d412a39e0e9e09784249e6811a88b06600327a5aa664ed9382162633727a7189044d1995a85e32f1785286e1e98599109e9529989240e86e038bc4fa27b08a28c8e38e0b887a4e76e8393b616914898cda288f915a6c4160ea0ba46a0e2a92383262e8470da6385f1480796f50209113a488263ba8f8e3b02213938c1c5a155179134a60be0b9b0862901148e84628ba0998408b8f625e6ac8e7a01800981e5d10d9cf03673d099bb0b618209cbda168148d8c6a1674f2d9e648e4cc3788cc2e0ea9d9a789e5562782fa2e03d1388420e7f0059ba83e1678fa11c4c5f9859ca8a63aa0d93fc5e08585a7b46e492238e5c1e18907a0506e69e07998c3ea4f858f383e0a3378fe49637f078e3a4e9c68626ae1696eae96e83e1c00e8f107283d14a13c4e6bc998fe4604a113a7b50218d3a8a560e915079ba86e97485920c3e942839916364c88384dc7600317a880ea3000b8bf01e6532de3e4168e48793dc226258593da7682383a24676a1f391418e2551140964ea12f39a5dcea4a90da6260e7239391260e4928b8f96362a33907549675125d72c5a37d098ed88b44d2987221684727893e185a11687cc9e7168ba3784e40f258eaa868203a850836235179e484e04b0884a8ea3310b84d86699e0688685e88889a4ba2e7c98ba8fcbb6171ba360261c43e83783e2bc2da360879ab05824c2e93d27d72c8b2f62da1483e8fd1ba862186fe2d89e82e5440792f656483138954263bb3890003640d1b134c4e10f20c09800135449a148e10913a4da162b885897e863d2859edc266a027a53c5290e131516167a00992f4605f90f90c42664b27a51c6e7233fa442ba390079c802685b1b92cc764929617881fa1e1bca4c6a8b7839d2c762399d917a0e1e217964c9e4130b8ed05e00a0997505651a9a28881e6ed3f0194df44d8f8a289f9aba592d45e9570b824e2648c369c5d127b717e7085e82903a948264f9159c74e3617378f281e26d0d99102e6638686d03626d379c5e1e8891393749625507d7e45246d1480f88e9ed1593dc6f2762f83c49671d2d8cde164cc1988e49e49d0b84608e031448d943e814099718a695b959764164591c84be500f63a8b443e13699a0742660e3a92043e2260589b46044d0996fcda75c858ec4265728581562e32237a254004770004b0965780da8fcc06b732075626109859c08666bc9590fe287e88ba784da4660b94ec863b189973cde318140098721661809fe665c913a30d020793f06863e2ed85a850e047783a5d04e9521788de3e7e30dd7e452560b098b86e7bb899ea886298178618366ea3882bc4e577bf022e160b5a19764764c41b90fa3e7aa8397264e55637a1d4b61b21422e44e7200988b85e0eba982d61694715d04a0e3179999e436a5b879ca80e2d08f9428b74580799d41a085038680be5be278bd46e0da3785302610f8b8c682671e25d85cb65cf1288b4ea6acae984c2669697a544e43580da5f0b62c987a0820ea1887a187125bb0b9ac0b63d9038cbe161508fa6a41e85b1792483611ac0a6291263f1785224e0b383a0282a22006a55c161368f83a03e57217d1342e6ea03824e2665317ce4c2744d278720278f6258bd0b60c5be9e54368930ba3f45e84439964c2218889871c8e94723a8502f27f2fe888dea4d2482c42635185a718267410d9eb43e6630fa5f2764ed8582c6163b6078e3e6645e15a08c2e861278ec41e7aa1ba780366299384960e1e993a808b60eb2824e0762372e97f416104898b247642b25893c3e7e23aa2ec265f403c9fce401d278840262b03a8d149e150079c7cb648c079d44e68442c9df06e7922dd1dc266900f9910b72b10d94ec2a8bf1b8de46a3400fa24e2844d33a0c8e60d41b9d2c3e1ff17a7b4260938fa626367aa83a0763e3220b89b4ea1c49783261686187840c1f71f0d8c060e56919a7806e776179d2e166ed03c520de8551981a20e8f52dd1360e8d80f965a3e508be927e2e5cf9da1b026844058bd08e0eb2e12fc56137078c06185f9839aa22e6b223a718be820160966162103ee8364e0da07a44cb72f699a0f03611b0b97720e48715a1b0df1a119a2202e516039840fe4b58388b48e66c93a08cce1038f94e89e8ec409d7e8e029b69b309e66c148c2f023c40f91003e11a1c99348e7162fc644266750b90c6165dc0f94c82e85b0d8682ba40a1309fe1e6ecacc4b0c008723a53c66593039dbc8e0be8592d60e6302e23e43610f858bd60e43e1d803cce5d92d8dd65e1e9001868960a487a786ba91a1497f4b6a508b8a6a3e8de2d9c343e72a87a010544a10fa1b42e11a22e888581710ba90e6018c238c1c260e23ea8182e6440b957c5ea508599b04e96a40809c520b085a6265e2930d9264c63d223a31cea16683a6a44e9781992486751c179810366ed8d9c7866487858e54002c82581c2da587839b1a3e9be2f8f408e48c838f65123028582cc1e2ed0f91648ea020b8df03e5d4279b98261ae15dade6e1380798d4da074279d3e260c5139b922e1190da7ba4e3ce099bb40e4c43991720e0da1ba2460f51c2386063e96e0b9a9d0271405a7404e2f4239e6616798089cf8265bd18a38456a1fbe98ba0e237179c8ca6150099c80b61099c20d02e610379134927ab27a8961694f1b97261e5d9078d9cbe48d14a2b4366d412a2201698e0f9455064523a9fbe5e2be3aa6c616078299c588621b2423e4a63b12f840c365528f8a684e4132881ca5e48c9794728e0b527873cfe0b38388686e4ed1bc520c65d90d94a8864f7998f422e07b938ec44e91419ca4e168b92597d02617799a546763ea89a4aa3653a0fa592661c5b29ef0a25ffb285585e80a1797248e556898e386f51c0a98189e57815878a2ea4f13a02a1051c1a90002656a0b9a5850171938bd43e6c2318400926011b8b42ba27a8584949e6f21d9eec5e00f8787c89e17a8983245f8f60782e41e0b1939aa0269ed299d3c8c2aa8ba624266b2859c7b02142838b848f8b985a8088ea501403f43e1198fa4b83e6a725a82c96577c098a03e6f821c6843686d198cbc8e74f139e60a66e6980efc2e5528591405e5b2198ab42e6ed0f8eea0e45e328be61ea3b09a364365160b87fcea42a
  | 6 => 0x9e4ec4f29737a964bc1b60e4560b14205a0e42c9da0e9db2f5912394b8b4950be8cf2f053079241bd12a5e49b0b24e858acc1d2fc6ea286f1e395834c6d4260e59d07053939a341c68ce686e2f56c0da0e16c5620ea290742c9590146c4921e4042730413939c4c0e8561cb074540d89a09c16cde35027142218a200065c8601c5b42b1796d41cb12261744b30c2d9ce9f45ee364411b3e61b82997d3505673f0b35a079df17caf4660b72b196138da9bd34c1629f0f0ea27979c6c5f01e4ba6f2392f9c31bc508fa414132a5139df8acee0824b7373b28587f83d26a36174274892f88ac9d0320ea600b273978e997c3aa5e87d2f3c803aad8ac16e4e8583342c8396a9cc4560e8aa5b00d8382142c5105e9f8270e79795349c9ca5e8582b42c319fc0ac3aa1e65b0b509078bc8bc5d8de2b0134a197a5f91c8d81e8442755b85854c1c2ea0e2df075483723a9155641677c6f5702d9014bc4944e6190b21f19a8a02d1760e0b61322a0da748ace088e77e0b3772f9b1c1c3bc1652e0f01683a5309d174de54a0f0e53797f89c2a42e26873205219798bc804be7a40f17cb0a39c1c744de56e6e3d08585d4bd210567f11b532378224bcb20523d26f03517a8a11d28e364d2073ac0989a0ccc08be1ca6f42b23a378bc56a5e4d65f4a01380f0b50762624907484999d91ccd9a360740b01e85a4490c39426838272971795541c6142e06b1b35a839d943c658e67d00f2d82fa3bdb48285e732171241b91586cf7cb68952f3539797bc1cd94564765f49a378f983d424b69a80b134378431bca645eab65f03e
  | 5 => 0x838d60e1236b6cb67a0997cb63c
  | _ => 0

def G30_buckets : Nat → Nat
  | 5 => 2
  | 6 => 56
  | 7 => 358
  | 8 => 664
  | 9 => 243
  | 10 => 7
  | 11 => 1
  | _ => 0

def G30_flag : Nat → Nat
  | 5 => 16
  | 6 => 4096
  | 7 => 4096
  | 8 => 8192
  | 9 => 4096
  | 10 => 2048
  | 11 => 2
  | _ => 0

def G30_seedBits : Nat → Nat
  | 5 => 5
  | 6 => 13
  | 7 => 13
  | 8 => 14
  | 9 => 13
  | 10 => 12
  | 11 => 2
  | _ => 0

def G30_seeds : Nat → Nat
  | 5 => 0x29
  | 6 => 0x86f009407c001030800901a11886b01d900803914500940f803c07c01e432805c001804c0830a9006804800204002103cc01a00a000809c00601500081340080a10009e3c1301d00068020226023002c10c1780a90068318005030
  | 7 => 0x6ae02400d818468b59518680140e201409a800eada703002005000201206a87800d601c012804c47b50f00100600321b400180242694e9002a5aa97e046013002000862f000820809c0482ad80d41b13f200d89d4470532005848ccb829400080688520ee0018d285f81640080d8033200200080440733b700acea401a0010090048092017028806813c0cd0024e6801c07c2c600403235950a181d404807f105ce0067c00806502a044b35c094802007f349013001c00205914280f83a804206b803c003339066003406e1c302a802008a00c04fca8e51833c012815806a01b00e49f003f5950ff001c1b255c01a001000218403e000401a2e80008022492023000802000202200685fc01e03301a0018064003002800414959502101b424f245019003c0925fa00180202f0021005005801800f00082a015809b05a0048004009008800c03a0d31ec0008004223001003c00405000383c0026001917020000207601048ac1af1f200081600520050f2804c05e019033008c04607c001002000400e00a81a833802503c009402c2ab03280100e200800082223a401b03d015008402700f00641640020008468050014003800806000304384fc1ce00400581c233000301582a00ac07504c002412a00f0020196b2a01b006800400e005026801800a0010cf0004002056045802419712007e00761e601d01c8458078004004804816e00e86c00420e803807f80d0022017075802603201180a80100af003007800801400a036008400e02e00080c007e00b0008020018007007000805200100301e80020fe
  | 8 => 0xca0b0b7c501064010f12545c4a9785550e5000ba928035a858002001001001645c8a7940df00600090004043004c00f0a2400b004107b0010288019014b033000100c8020000e9b4022802e0008008000423b0014001077404c002c008000c81900140130f96a5e000c02618d40e30008832008821da68c80100042bf0ecc3f40e5400400e4017004c1bb05dcff600640080008224000410a006c0ca001c0ed12fc008000a9670058194027404d00382d00774001016c002a4c8d8b00d4115a3241f401b41c4068401a002c01600fa85806c86de005808f0018059a0dc0b9a05837400100bd02c000902c801f0024003004803a00480180af40022d343dc04e40270006a5e0018090000c001013806d0008009007411a018679500080d4012aa5e15141480990277008444f17c402301fc0180454258a97801703e401a06804db0008006007400a002c01d099801603080bb0004001a978072005c0229de800a00d801a01e40050bf80060f7004505201110c340091ab000200040e90516a5e0164001000408c03040b39da4002003c00c0004002007000900040290558127046c0050238001a9780830e4c05e034403902a0300057400d02e8002001c00f021002f021c2c100100150100006008800a000802a00dc0479b9000700f800400b4002000c0030020610000c3d8034c0a3051c3519b7c01d0b24003001a6b700f800800140ef00040b5009cb7800a6a5e00e018a00240670b04002000400100a26a5001806d00180b0003401808a800401000ee00101e703880eb009c004000815500480e00cec0010548022063c0040068002000810e00440170034095000c0580028029008401000c8020000c3c200142d2000441a024000100040040004068001266b01926470794157980000204a417ea978001a97802e007c0ee027401596da475011001504cc05e911802f0688016002c084000408200600040168054002004f8fa41478f7803402e0002000801a04f016d02b2a5e00701758ed8001019c03a8d9c0bc8d1a3410284061011c0290170057009c1d7010c0a6004aa5e007c0020e3c03d0014002005c008000c2e1000c00100e0001002c013017800901040040114046003c0d78bd000e0024007007ea5e00200f102500090438035a978003014800900c40c303dea5e00280c201e40100314004079800202800020030003001800a04f801600201168b100048ae40140040004000402a000406c002801f00100d3000800300a000788dc067006800b0010308001401000dc028000401d01ac004004400b008400200500030004284001001f004e236002c006003c06d000400d0184004001400100b008500c801602aa1e400a010800ac0f903a8007007a1d600240af0008017075c17c000801c012c037004805302f800803b40ab002001a000400300dc0b601fc0e5003400100c00040008003003aa5e004c005000c05604700208660122009c002858c00300f0052000c0480138001856c00a000800f00060d3001000800140010064006041c01500080bd002400100040080470008000400f00ac0a00044002000800da9781cc8328065000c015000800f02781b3003000182a00080008003
  | 9 => 0x2000200b0d791d1e6827e2a910ac04000416500f41f46f904780183b41b900580504ee05414c803004200207700140c539400093dc038008213006802ecf60264f280020a800333fc0f13ca00280601601920058200042373007ce144d606c033004802aa992e007f00020080018020004a2b00500a0002005128146e794003004002401c0ad1a0824c18e00900180040620142248fc800400a42607812f400f00385b402e2489be014c2fc0b103a06ec03004396001740280e803800080f404109615f404c14c93fcf2806e00300681483b201300b802c05201102380ec01d279005002814d3ca01701cc1f005d003800401002000080080a0087002000c00c094000800e3b8176002000c0b231e000c73007604b000801c56200101f80043ae06100100042a6002072801810c00b0028078016001000c72a1ec07e007800604a001001802000c05701a80a404801500301e000e00a000800c0740089e500e8024002118c050004005013011c232001000cf28026058001000404200501a806800200200501b41b202e
  | 10 => 0x40d904900d418002016
  | 11 => 0x2
  | _ => 0

def G30_initial : List Nat := [0x381c0e070381c0e07007fc0000007fc0000, 0x5028140a05028140aff80001ff00003fe00, 0xc86432190c864321900003fe00ff80001ff, 0x32190c86432190c86400000000000003ffff, 0x482412090482412090ffffc000000003fe00, 0xa05028140a05028140ffffffe00000000000, 0xd068341a0d068341a00000001ffffffc0000]

def G30_idx : Nat → List Nat → Nat :=
  qIndex G30_N G30_buckets G30_flag G30_seedBits G30_seeds

def G30_benes : Nat := 0x189af059ab699b1e5a814fe9f8f966e9892f2ec56c00000000000000000000000000000000000000000

def G30_inputActions : Nat := 0x118357ac688

def G30_rawAct (auto : Nat) : Nat → Nat := routeFixed (bMasks G30_benes auto)

def G30_cacheKeys (i : Nat) : Nat := G30_initial.getD i 0

def G30_cacheValues (auto i : Nat) : Nat :=
  G30_cacheKeys (fld G30_inputActions 3 (7*auto+i))

def G30_act (auto : Nat) : Nat → Nat :=
  cachedAction G30_cacheKeys (G30_cacheValues auto) 7
    (fun w => qInputLookup w G30_initial) (G30_rawAct auto)

def G30_S (s j : Nat) : List Nat :=
  qParentAction 11 9 4 0x878676857565847464548373635343827262524232817161514131218070605040302010 9 1 G30_initial G30_act G30_pb G30_records (11-s) j

def G30_actions : List (Nat → Nat) :=
  (List.range 1).map (fun i => G30_act (i+1))

def G30_ori : List Nat → List Nat := orbitActions qPrefer G30_actions

def G30_coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 72, 73, 74, 75, 76, 77, 78, 79, 80]

def G30_rankPool : List Nat := [239122864, 201370952, 204553484, 241347849, 202619178, 167887278, 238235947, 68338063, 202386697, 134292747, 135511501, 67220746, 204614952, 202457422, 235028910, 135478605, 238207375, 171981232, 201567528, 235027820, 101725583, 201505034, 170110248, 67289549, 100843981, 68302122, 204517704]

def G30_Z (s : Nat) : Nat → Bool :=
  barFastOrbit 72 G30_S G30_N G30_idx G30_ori G30_coords 5 G30_rankPool s

def G30_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def G30_rows : List Nat := (([10, 28, 33, 34, 36, 66, 81, 84] : List Nat).flatMap fun x => List.replicate 9 x) ++ (List.replicate 8 ([3, 5, 9, 6, 18, 40, 72, 48, 96] : List Nat)).flatten
def G30_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a G30_rows)
theorem G30_nonconstant : ∃ x y : Fin 7 → Bool, G30_f x ≠ G30_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_enc_goal : encL G30_f G30_rows = goal 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_proper : ∀ zs ∈ G30_xs.sublists, zs ≠ G30_xs →
    (covUp 72 zs &&& lo 72) ≠ lo 72 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_good :
    qCachedGood (goal 72) 2 G30_initial G30_inputActions G30_benes := by
  unfold qCachedGood
  decide +kernel
theorem G30_preserved {s : Nat} {ws : List Nat}
    (h : MonRun (goal 72) s ws) : MonRun (goal 72) s (G30_ori ws) := by
  change MonRun (goal 72) s (qCachedOrient 2 G30_initial G30_inputActions G30_benes ws)
  exact qCachedOrient_run h G30_good
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_5_0 : span (G30_Z 5) 6 0 = true := by decide +kernel

theorem G30_checked_5 : span (G30_Z 5) 6 0 = true :=
  G30_check_5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_6_0 : span (G30_Z 6) 222 0 = true := by decide +kernel

theorem G30_checked_6 : span (G30_Z 6) 222 0 = true :=
  G30_check_6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_0 : span (G30_Z 7) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_256 : span (G30_Z 7) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_512 : span (G30_Z 7) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_768 : span (G30_Z 7) 256 768 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_1024 : span (G30_Z 7) 256 1024 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_7_1280 : span (G30_Z 7) 149 1280 = true := by decide +kernel

theorem G30_checked_7 : span (G30_Z 7) 1429 0 = true :=
  (@span_join (G30_Z 7) 768 0 661 (@span_join (G30_Z 7) 256 0 512 G30_check_7_0 (@span_join (G30_Z 7) 256 256 256 G30_check_7_256 G30_check_7_512)) (@span_join (G30_Z 7) 256 768 405 G30_check_7_768 (@span_join (G30_Z 7) 256 1024 149 G30_check_7_1024 G30_check_7_1280)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_0 : span (G30_Z 8) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_256 : span (G30_Z 8) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_512 : span (G30_Z 8) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_768 : span (G30_Z 8) 256 768 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_1024 : span (G30_Z 8) 256 1024 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_1280 : span (G30_Z 8) 256 1280 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_1536 : span (G30_Z 8) 256 1536 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_1792 : span (G30_Z 8) 256 1792 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_2048 : span (G30_Z 8) 256 2048 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_2304 : span (G30_Z 8) 256 2304 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_8_2560 : span (G30_Z 8) 94 2560 = true := by decide +kernel

theorem G30_checked_8 : span (G30_Z 8) 2654 0 = true :=
  (@span_join (G30_Z 8) 1280 0 1374 (@span_join (G30_Z 8) 512 0 768 (@span_join (G30_Z 8) 256 0 256 G30_check_8_0 G30_check_8_256) (@span_join (G30_Z 8) 256 512 512 G30_check_8_512 (@span_join (G30_Z 8) 256 768 256 G30_check_8_768 G30_check_8_1024))) (@span_join (G30_Z 8) 768 1280 606 (@span_join (G30_Z 8) 256 1280 512 G30_check_8_1280 (@span_join (G30_Z 8) 256 1536 256 G30_check_8_1536 G30_check_8_1792)) (@span_join (G30_Z 8) 256 2048 350 G30_check_8_2048 (@span_join (G30_Z 8) 256 2304 94 G30_check_8_2304 G30_check_8_2560))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_9_0 : span (G30_Z 9) 256 0 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_9_256 : span (G30_Z 9) 256 256 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_9_512 : span (G30_Z 9) 256 512 = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_9_768 : span (G30_Z 9) 202 768 = true := by decide +kernel

theorem G30_checked_9 : span (G30_Z 9) 970 0 = true :=
  (@span_join (G30_Z 9) 512 0 458 (@span_join (G30_Z 9) 256 0 256 G30_check_9_0 G30_check_9_256) (@span_join (G30_Z 9) 256 512 202 G30_check_9_512 G30_check_9_768))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_10_0 : span (G30_Z 10) 28 0 = true := by decide +kernel

theorem G30_checked_10 : span (G30_Z 10) 28 0 = true :=
  G30_check_10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_check_11_0 : span (G30_Z 11) 1 0 = true := by decide +kernel

theorem G30_checked_11 : span (G30_Z 11) 1 0 = true :=
  G30_check_11_0

theorem G30_checked (s : Nat) (hs : s ≤ 11) : ∀ i < G30_N s, G30_Z s i = true := by
  interval_cases s

  · simp [G30_N]

  · simp [G30_N]

  · simp [G30_N]

  · simp [G30_N]

  · simp [G30_N]

  · intro i hi
    exact span_ok G30_checked_5 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_6 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_7 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_8 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_9 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_10 i (Nat.zero_le i) (by simpa [G30_N] using hi)

  · intro i hi
    exact span_ok G30_checked_11 i (Nat.zero_le i) (by simpa [G30_N] using hi)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem G30_initial_perm : G30_xs.Perm (G30_S 11 0) := by decide +kernel
theorem G30_no_run : ∀ s ≤ 11, ¬ MonRun (goal 72) s G30_xs := by
  exact noRun_from_barFastOrbit (k := 72) (S := G30_S) (N := G30_N)
    (idx := G30_idx) (ori := G30_ori) (coords := G30_coords)
    (bw := 5) (pool := G30_rankPool) (cap := 11) (i := 0)
    G30_preserved G30_checked (by decide) (by decide) G30_initial_perm
theorem G30_no_small : ¬ HasMonoSize 7 G30_f 11 :=
  encoded_mono_exclusion G30_f G30_nonconstant 11 G30_rows G30_xs 72
    rfl G30_enc_goal G30_proper G30_no_run
theorem G30_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = G30_f x) :
    12 ≤ C.size := mono_lower G30_f 11 G30_no_small C hmono hev
end PEqualNP.Outside.L_meta_984.Cert

theorem PEqualNP.Outside.L_meta_984 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact ⟨PEqualNP.Outside.L_meta_984.Cert.G0_lower, PEqualNP.Outside.L_meta_984.Cert.G1_lower, PEqualNP.Outside.L_meta_984.Cert.G2_lower, PEqualNP.Outside.L_meta_984.Cert.G3_lower, PEqualNP.Outside.L_meta_984.Cert.G4_lower, PEqualNP.Outside.L_meta_984.Cert.G5_lower, PEqualNP.Outside.L_meta_984.Cert.G6_lower, PEqualNP.Outside.L_meta_984.Cert.G7_lower, PEqualNP.Outside.L_meta_984.Cert.G8_lower, PEqualNP.Outside.L_meta_984.Cert.G9_lower, PEqualNP.Outside.L_meta_984.Cert.G10_lower, PEqualNP.Outside.L_meta_984.Cert.G11_lower, PEqualNP.Outside.L_meta_984.Cert.G12_lower, PEqualNP.Outside.L_meta_984.Cert.G13_lower, PEqualNP.Outside.L_meta_984.Cert.G14_lower, PEqualNP.Outside.L_meta_984.Cert.G15_lower, PEqualNP.Outside.L_meta_984.Cert.G16_lower, PEqualNP.Outside.L_meta_984.Cert.G17_lower, PEqualNP.Outside.L_meta_984.Cert.G18_lower, PEqualNP.Outside.L_meta_984.Cert.G19_lower, PEqualNP.Outside.L_meta_984.Cert.G20_lower, PEqualNP.Outside.L_meta_984.Cert.G21_lower, PEqualNP.Outside.L_meta_984.Cert.G22_lower, PEqualNP.Outside.L_meta_984.Cert.G23_lower, PEqualNP.Outside.L_meta_984.Cert.G24_lower, PEqualNP.Outside.L_meta_984.Cert.G25_lower, PEqualNP.Outside.L_meta_984.Cert.G26_lower, PEqualNP.Outside.L_meta_984.Cert.G27_lower, PEqualNP.Outside.L_meta_984.Cert.G28_lower, PEqualNP.Outside.L_meta_984.Cert.G29_lower, PEqualNP.Outside.L_meta_984.Cert.G30_lower⟩
