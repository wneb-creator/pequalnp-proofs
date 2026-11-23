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

def qIndex (N buckets flag seedBits seeds : Nat → Nat) (s : Nat) (ws : List Nat) : Nat :=
  let h := hk ws
  let code := fld (seeds s) (seedBits s) (h % buckets s)
  if code ≥ flag s then code-flag s
  else ((h+code+317)^3 % 11400714819323198549) % N s

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

def qCompactRoutes (codes auto : Nat) : List (Nat × Nat) :=
  ((List.range 9).map fun i => fld codes 32 (9*auto+i)).zip [1,2,4,8,16,8,4,2,1]

def qCompactGood (y group codes : Nat) : Prop :=
  ∀ i : Fin group, validStages (qCompactRoutes codes i.val) = true ∧
    routeStages (qCompactRoutes codes i.val) y = y

def qCompactOrient (group codes : Nat) : List Nat → List Nat :=
  orbitActions qPrefer ((List.range (group-1)).map fun i => routeStages (qCompactRoutes codes (i+1)))

theorem qCompactOrient_run {y s : Nat} {ws : List Nat} {group codes : Nat}
    (h : MonRun y s ws) (hg : qCompactGood y group codes) :
    MonRun y s (qCompactOrient group codes ws) := by
  apply orbitActions_run h qPrefer
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨i,hi,rfl⟩
  have hib : i < group-1 := List.mem_range.1 hi
  exact routeStages_run hz (qCompactRoutes codes (i+1))
    (hg ⟨i+1,by omega⟩).1 (hg ⟨i+1,by omega⟩).2

def C0_initial : List Nat := [0x724, 0x949, 0xa92, 0x3403, 0x501c, 0x60e0]

def C0_values : Nat := 0x77fcee49d38fa70741fe839d00fa0070fce1c1c0738006af2d5c1a7a74f068e0cfc99c932f064e0c7c18782fbedbdfb4396576c0e573ca83944728004a9292931c920003fdb7edefa4df01bd4b7a06f00db93b7036c06d40cca497241ffe3ed87b68f241d2435245ed8b92169228004ac894d12962420480890010102004400072c0e4a1c00280040108000c0008401040202040000c00090010000c0008000

def C0_patterns : Nat := 0x559556555551545541515155

def C0_N : Nat → Nat
  | 4 => 2
  | 5 => 20
  | 6 => 54
  | 7 => 71
  | 8 => 13
  | 9 => 1
  | _ => 0

def C0_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C0_patternBits : Nat → Nat
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | _ => 0

def C0_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C0_recordBits : Nat → Nat
  | 4 => 20
  | 5 => 27
  | 6 => 27
  | 7 => 17
  | 8 => 10
  | 9 => 3
  | _ => 0

def C0_records : Nat → List Nat
  | 4 => [0xa93c601387]
  | 5 => [0x9f3598c027c35a2ab3c8809e9669f11c8c027ca1c0282b880243f80121e17157ad4404f9a380a740700a496200d8ee27cd6a1800128f013e58e02acf1e2ba3c48090b93]
  | 6 => [0x2fe800115f00bcaf2015a1d800098f800119f00020be000427c04f88b803c4b90000afa00e12e40210fe0000b37000293e00f15e404f6b980624b9009cee600029de29e24c808c55d0088778020b83c053967809eda700fd3ae00000fc01b0fc808abdb013e69f3e6b21d59e2588000fdf013e6af4e8cd1c01217c80003fe00fdb9e01423cc04556b803a5790115d1e000407c04140d805857500027ee00027dc00057baf5a4b10000b7a01412cc04f9a3807e75b]
  | 7 => [0x11538720065a744809829c40027900aa80175592201250052a20f23c40000500869e24df870002d00f680574f124008d009a805664c70000700c6803d403ba008546562f5a401594e680003000f4018b1490000e80254019a0228008a80094001a016d5e498027400da004d00d2807e0e87600e5002a800d4025a00ad01040035400ea0185009c803f4002ab55182304f64403ea483c]
  | 8 => [0x150f56d775153d4060155501c9509465]
  | 9 => [0x5]
  | _ => []

def C0_buckets : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 14
  | 7 => 18
  | 8 => 4
  | 9 => 1
  | _ => 0

def C0_flag : Nat → Nat
  | 4 => 16
  | 5 => 128
  | 6 => 256
  | 7 => 0x400
  | 8 => 16
  | 9 => 2
  | _ => 0

def C0_seedBits : Nat → Nat
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 11
  | 8 => 5
  | 9 => 2
  | _ => 0

def C0_seeds : Nat → Nat
  | 4 => 8
  | 5 => 0x7510500126
  | 6 => 0xc1300f8c01809012864004070305a05
  | 7 => 0x101ac51560401881b040048ad00518800c0081601001002961
  | 8 => 0x4e183
  | 9 => 2
  | _ => 0

def C0_S (s j : Nat) : List Nat :=
  qDirectStatePattern C0_initial (C0_countBits s) (C0_patternBits s) C0_patterns 15 7 (C0_slots s) C0_values
    (fld ((C0_records s).getD (j / 256) 0) (C0_recordBits s) (j % 256))

def C0_idx : Nat → List Nat → Nat :=
  qIndex C0_N C0_buckets C0_flag C0_seedBits C0_seeds

def C0_routeCodes : Nat := 0x51540000000200000b05000000000000000000000000000000000000000000004054000050540000000300000b09000000000000000000000000000000000000002000004000000041000000001300000b06000000000000000000000000000000000000003000004054000040000000001100000b0200000000000000000000000000000000000000000000400000001115000000100000000c00000000000000000000000000000000000000200000004000000151000000200000000800000000000000000000000000000000000000200000001000001054000000100000000c000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000
def C0_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C0_rankPool : List Nat := [4401547, 7609806, 5275034, 6626216, 7425741, 3174108, 7670697, 5520265, 2112650, 6454168, 2182298, 6303405, 5340570, 7559563, 6650776, 5270922]

def C0_rows : List Nat := [10, 12, 17, 18, 20, 33, 34, 36, 3, 5, 9, 6, 24, 40, 48]
def C0_xs : List Nat :=
  (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
    (fun a => encL a C0_rows)
def C0_f (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def C0_ori : List Nat → List Nat := qCompactOrient 8 C0_routeCodes
def C0_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 7) (compactCover 8 7) C0_S C0_N C0_idx C0_ori
    C0_coords 4 C0_rankPool s
def C0_F : Nat → Bool := certAt C0_Z C0_N 10
def C1_initial : List Nat := [0x3c21, 0x454a, 0x4a94, 0x90c6, 0xa318, 0x1001f, 0x103e0]

def C1_values : Nat := 0x1a318d0006431b00014a94a2afd152a87c140009e1fcf0860fc1040081ffc001a00030000718c357397842b3de598c29c60fad67c2127ef110008000040000210001800020000

def C1_N : Nat → Nat
  | 5 => 8
  | 6 => 22
  | 7 => 36
  | 8 => 18
  | 9 => 1
  | _ => 0

def C1_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C1_slots : Nat → Nat
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C1_recordBits : Nat → Nat
  | 5 => 25
  | 6 => 25
  | 7 => 26
  | 8 => 20
  | 9 => 7
  | _ => 0

def C1_records : Nat → List Nat
  | 5 => [0x215c742fae1a17571400100f44e34342fba0c078d0e042f87]
  | 6 => [0x193e000a9f0217c3810ae3804493c01c6e6011307810be9c085f1e89031985f443808963c08571f0ba88b00044f810aeb805d13c02280f8574470088e7406d73c04288f]
  | 7 => [0x441055408545520655040441565d1055513c1550105155744154013455511015544305551181550111555c4415501105554441555d1155006855500955511441556d10555128155442055401d551016155400155500b51551141550110566144055611055405d554012455614445500c5155120155]
  | 8 => [0x155551155521555455550155961555019550955501556441553d55551555445550d55519555015552955571555]
  | 9 => [0x7f]
  | _ => []

def C1_buckets : Nat → Nat
  | 5 => 2
  | 6 => 6
  | 7 => 9
  | 8 => 5
  | 9 => 1
  | _ => 0

def C1_flag : Nat → Nat
  | 5 => 256
  | 6 => 128
  | 7 => 0x400
  | 8 => 256
  | 9 => 2
  | _ => 0

def C1_seedBits : Nat → Nat
  | 5 => 9
  | 6 => 8
  | 7 => 11
  | 8 => 9
  | 9 => 2
  | _ => 0

def C1_seeds : Nat → Nat
  | 5 => 0x16805
  | 6 => 0x600a07011b5d
  | 7 => 0xc31a0800200c00800d848a8
  | 8 => 0x90625c3006
  | 9 => 2
  | _ => 0

def C1_S (s j : Nat) : List Nat :=
  qDirectState C1_initial (C1_countBits s) 17 6 (C1_slots s) C1_values
    (fld ((C1_records s).getD (j / 256) 0) (C1_recordBits s) (j % 256))

def C1_idx : Nat → List Nat → Nat :=
  qIndex C1_N C1_buckets C1_flag C1_seedBits C1_seeds

def C1_routeCodes : Nat := 0x54110000210300000909000000060000000000000000000000000000213000000144000055100000210000000d0200000040000000000000000000000400000021000000011000005151000021000000090b000000060000000000000000000000000000211000000144000050400000301200000d04000000100000000000000000000001000000301000000104000044110000122000000707000000180000000000000000000001000000120000000004000044440000121200000e0400000080000000000000000000000800000012100000010000004151000012210000070f000000180000000000000000000001000000120000000004000041040000120000000e00000000800000000000000000000008000000120000000100000014150000010300000009000000060000000000000000000000000000013000000140000015540000030000000c02000000c0000000000000000000000c00000003000000001000000415000002210000010f00000018000000000000000000000100000002000000014000000544000000120000000400000000000000000000000000000000000000100000000400001155000001030000000900000006000000000000000000000000000001300000000000001000000002120000090400000090000000000000000000000900000002100000000000000155000002210000010f000000180000000000000000000001000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000
def C1_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C1_rankPool : List Nat := [7708636, 3165914, 6445998, 8417229, 8478159, 2125483, 6651594, 9473755, 6328284, 4227021, 5414844]

def C1_rows : List Nat := [33, 42, 44, 50, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 6, 24, 96]
def C1_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C1_rows)
def C1_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C1_ori : List Nat → List Nat := qCompactOrient 16 C1_routeCodes
def C1_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 10 7) (compactCover 10 7) C1_S C1_N C1_idx C1_ori
    C1_coords 4 C1_rankPool s
def C1_F : Nat → Bool := certAt C1_Z C1_N 10
def C2_initial : List Nat := [0x1e40, 0x2295, 0x252a, 0x41cc, 0x4833, 0x81f0, 0x900f]

def C2_values : Nat := 0xdff0de40d83fd833d80fd800d00fd000c9f3c9f0c833c1fcc1f0c000b52ab29fb295b00fa52aa295a1f09ff09e4f9e40980f920f91f0900089f083f080006ab7652a63dd5fcc5e735e4049ff480041c040844040400c40003ed53e402d2a27bf272a220020000800020001c000840040000c00050003

def C2_N : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 25
  | 7 => 41
  | 8 => 27
  | 9 => 1
  | _ => 0

def C2_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C2_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C2_recordBits : Nat → Nat
  | 4 => 19
  | 5 => 25
  | 6 => 25
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C2_records : Nat → List Nat
  | 4 => [0xd83f5c86]
  | 5 => [0xe241c040a8702456300075580df20e05b21a000d0b81cdc1c0b6b33cc8806]
  | 6 => [0x76bd602c90f000407c0997adcba8070234138132b1c0024bc01c67900e33c0081b8c09203c001757035bcb81c403c0a64b4064ac702040b814d1640910ac05921f02f5eb016c06c0c649c07321e]
  | 7 => [0x77fbd0ae8119db4398125f00afa01bec086f811bf020be06afc0bef80dfb710ce01dfb94338113f014ee023dc05ff0097701fbe0407c04fb8135f000fe03d7cc27c80aef9a5bdaa0dc09efae876024bc021ddd42bcc857999ae054fe680f805fb]
  | 8 => [0x4155509555015562555569555cd5553d55505555315551955571555e55551d5550159501559655551555521555c15551155541515991550d55561555595550155501655]
  | 9 => [0x7f]
  | _ => []

def C2_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 7
  | 7 => 11
  | 8 => 7
  | 9 => 1
  | _ => 0

def C2_flag : Nat → Nat
  | 4 => 4
  | 5 => 256
  | 6 => 256
  | 7 => 0x400
  | 8 => 0x2000
  | 9 => 2
  | _ => 0

def C2_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 9
  | 6 => 9
  | 7 => 11
  | 8 => 14
  | 9 => 2
  | _ => 0

def C2_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x9bf0a
  | 6 => 0x62a020481c06fd
  | 7 => 0x8420084c0080480600100871c05866
  | 8 => 0x116e03fc0240038003000c001
  | 9 => 2
  | _ => 0

def C2_S (s j : Nat) : List Nat :=
  qDirectState C2_initial (C2_countBits s) 16 6 (C2_slots s) C2_values
    (fld ((C2_records s).getD (j / 256) 0) (C2_recordBits s) (j % 256))

def C2_idx : Nat → List Nat → Nat :=
  qIndex C2_N C2_buckets C2_flag C2_seedBits C2_seeds

def C2_routeCodes : Nat := 0x51150000213000000a0c00000020000000000000000000000200000020300000110000000115000003000000080000000080000000000000000000000800000002000000010000005000000020300000080c000000000000000000000000000000000000203000001000000000000000000000000000000000000000000000000000000000000000000000000000
def C2_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C2_rankPool : List Nat := [8813978, 6524844, 6303387, 2189981, 6655659, 6442940, 6438345, 6577593, 6381500, 6455196, 6586011]

def C2_rows : List Nat := [26, 28, 50, 52, 74, 76, 97, 98, 100, 3, 5, 9, 17, 6, 40, 80]
def C2_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C2_rows)
def C2_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)
def C2_ori : List Nat → List Nat := qCompactOrient 4 C2_routeCodes
def C2_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 9 7) (compactCover 9 7) C2_S C2_N C2_idx C2_ori
    C2_coords 4 C2_rankPool s
def C2_F : Nat → Bool := certAt C2_Z C2_N 10
def C3_initial : List Nat := [0x722, 0xa95, 0x1948, 0x20e6, 0x2419, 0x40f8, 0x5007]

def C3_values : Nat := 0x3a0ff419e80fd003803f000c9f393e320ce0fec1f1839b0005a97b52b67e2ca7d948b00f5c9eb915407a40f441e87c5000952b23e239144f885f107e20003d597a90e7b9ca42e9d5d2aabdd54aa7e64e769c8927fa40041c082110202022400c8000fb51d4836903edc74a8b9514001000100010001c002100110020000c00140010001

def C3_N : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 23
  | 7 => 45
  | 8 => 31
  | 9 => 1
  | _ => 0

def C3_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C3_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C3_recordBits : Nat → Nat
  | 4 => 14
  | 5 => 21
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C3_records : Nat → List Nat
  | 4 => [0x2187]
  | 5 => [0xd591a5a64380825d220c31122388fc3b5330da9ba4e1a99]
  | 6 => [0x385a7613c2ef9acb76d69806b6dcb536d49d35a4cb805a7c98ecad4ed384899bf331e2ad1ed555a2647180755daad3688f716ab2cb5666db998e90ce3]
  | 7 => [0xf09d700f2f802fde1136e4c5e76e76b802bdc0427e01adf6a9ad805efc0347e889f30047d804f7dbb6b600cef00aef80517c02dbe849e76e4eb802ddc00cfa00f7d0037ea6275c035f60007f4a4f39e27d402ebe0077d00b4f8021ec035b6014df008bd8062fc018ee009f700def8029dc0307edd69f]
  | 8 => [0xa55552aaaa195550aaaa84555402aaa0555500b2a9f55550aaaa0155926a8a82555402aac695558caaa93555602aaa1d55510aaa9c55551aaaa3d5556e8aabd5554eaaaa2555500aca8b555492aaa0d555]
  | 9 => [0x7f]
  | _ => []

def C3_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 6
  | 7 => 12
  | 8 => 8
  | 9 => 1
  | _ => 0

def C3_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 256
  | 7 => 256
  | 8 => 64
  | 9 => 2
  | _ => 0

def C3_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 7
  | 9 => 2
  | _ => 0

def C3_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x2e00c01
  | 6 => 0x22a81160080c01
  | 7 => 0x658281a0501acc2724008040c1b
  | 8 => 0x135410408e0254
  | 9 => 2
  | _ => 0

def C3_S (s j : Nat) : List Nat :=
  qDirectState C3_initial (C3_countBits s) 15 7 (C3_slots s) C3_values
    (fld ((C3_records s).getD (j / 256) 0) (C3_recordBits s) (j % 256))

def C3_idx : Nat → List Nat → Nat :=
  qIndex C3_N C3_buckets C3_flag C3_seedBits C3_seeds

def C3_routeCodes : Nat := 0x40400000323200000404000000000000000000000000000000000000101000004040000000000000000000000000000000000000000000000000000000000000000000000000
def C3_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C3_rankPool : List Nat := [7695241, 3165884, 1060250, 5442728, 6576523, 3235468, 3239306, 6650776]

def C3_rows : List Nat := [28, 49, 52, 74, 76, 97, 98, 100, 3, 5, 9, 6, 18, 40, 80]
def C3_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C3_rows)
def C3_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def C3_ori : List Nat → List Nat := qCompactOrient 2 C3_routeCodes
def C3_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 7) (compactCover 8 7) C3_S C3_N C3_idx C3_ori
    C3_coords 4 C3_rankPool s
def C3_F : Nat → Bool := certAt C3_Z C3_N 10
def C4_initial : List Nat := [0x721, 0x94a, 0xa94, 0x20e7, 0x3418, 0x40f8, 0x5007]

def C4_values : Nat := 0xefcfdc87a7c741fe831d01fa0070e7e1c1c01f80060ffc1f1839f0005a94b29f652ac03d727ae43501e883d0ffa1f1400254a49fa929523e23fcc72189f107e20704048804100620003d5a7830dce5b90b51869fed001873b0005528a7bd4a528e74fce9c85273a40043ce83810212021400e8000d4a172120003dac7908e9417bc2e5048008000800040007000480084008401000180010001c0010001

def C4_N : Nat → Nat
  | 4 => 2
  | 5 => 18
  | 6 => 51
  | 7 => 79
  | 8 => 44
  | 9 => 1
  | _ => 0

def C4_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C4_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C4_recordBits : Nat → Nat
  | 4 => 21
  | 5 => 28
  | 6 => 28
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C4_records : Nat → List Nat
  | 4 => [0x4e0f4e806]
  | 5 => [0xb951601161999ae9c1100ecf960152807014a787014200e0002517a135d0301425070140fc600ece8700b938701425879ae9a92a135a860142687011601a]
  | 6 => [0x9ae9713a135707014268f01423c700ecd9700027b7000284fa5466870120fd600ed0170048878014104700e9ada0001d9f0141ace0141d4b00023570135797014a597012d233009117100e9c590090ff2014208f9ad57160135d97012d71701426870140bc70148fd600b931701517170001576013571700ecb9700013e7000265700b8a9e0115d9b00b8fd60000ff600b9297012e417012cfb60101d9e0141d8f00025b7014269701426c70148ec701426a7]
  | 7 => [0x3fdc033be00ff65c5eb8043dc037be01dbf0142f8035de6ae3eb90570122f802dec03bbe0166f00d2f80a13e3aeae025b774badab41d802fbf0571f00bafcd655c020ee018df0109fcd5cdc01cee00ef700ebd803ddc035fc00c77a536bcd5c5c015fc008fb485f98033dc03e7e406f9a482b8037dc052bf466b7003be80617e5976f48dd7007ff482f5c047ee01d9f009bb80a1bdaaebc007fb004bf522f5c03f7f4174f0137bd2767c000fe7cbf600caf8053bd7143e00bf7a5467804bdc024f6025f79abab8096fc054ee01e5f]
  | 8 => [0xaaa885555eaaab3551546aaaa055555aaaa0955526aaac4555692aaa016550eaaa94555422aaa255551aaaaae55568aaaa5d51516aaaa8555402b2b355552eaaac15555b2aaa81515012aac9555402aac01559a48aa80655482aaa315550caaa8a5555caaaa155555c8aaad55540aaaa0d555]
  | 9 => [0x7f]
  | _ => []

def C4_buckets : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 20
  | 8 => 11
  | 9 => 1
  | _ => 0

def C4_flag : Nat → Nat
  | 4 => 8
  | 5 => 512
  | 6 => 0x800
  | 7 => 0x1000
  | 8 => 0x400
  | 9 => 2
  | _ => 0

def C4_seedBits : Nat → Nat
  | 4 => 4
  | 5 => 10
  | 6 => 12
  | 7 => 13
  | 8 => 11
  | 9 => 2
  | _ => 0

def C4_seeds : Nat → Nat
  | 4 => 4
  | 5 => 0x30650f11c04
  | 6 => 0x27502a1b000d00200101c8330010750060227c8
  | 7 => 0xb863800201a000ab0400c00300c801c01624382206a42ac034000805c04d04f
  | 8 => 0x9747207905e014014100180140084c
  | 9 => 2
  | _ => 0

def C4_S (s j : Nat) : List Nat :=
  qDirectState C4_initial (C4_countBits s) 15 7 (C4_slots s) C4_values
    (fld ((C4_records s).getD (j / 256) 0) (C4_recordBits s) (j % 256))

def C4_idx : Nat → List Nat → Nat :=
  qIndex C4_N C4_buckets C4_flag C4_seedBits C4_seeds

def C4_routeCodes : Nat := 0x1440000001200000004000000000000000000000000000000000000001000000004000000000000000000000000000000000000000000000000000000000000000000000000
def C4_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C4_rankPool : List Nat := [7756171, 4205722, 3239644, 2112425, 5467530, 3165096, 4357852, 3153034, 5537178]

def C4_rows : List Nat := [49, 50, 52, 74, 76, 97, 98, 100, 3, 5, 9, 6, 24, 40, 80]
def C4_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C4_rows)
def C4_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def C4_ori : List Nat → List Nat := qCompactOrient 2 C4_routeCodes
def C4_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 7) (compactCover 8 7) C4_S C4_N C4_idx C4_ori
    C4_coords 4 C4_rankPool s
def C4_F : Nat → Bool := certAt C4_Z C4_N 10
def C5_initial : List Nat := [0x721, 0x94a, 0xa94, 0x141e, 0x30e0, 0x40f8, 0x6007]

def C5_values : Nat := 0xe83fd07ba0070f8e1cfc383803f000d529a53f4a56807ce4f9c87203e107c1ff83e300054fea83d43e254a49fa929523e23fcc72189f107e207040488041006200039ea71c0df85a7f34e0683cc7818002a944e428000eaf1c1e35285cfcb90951e280040007b58f211d282f785ca09001000100008000e0009001000100018001400180010001

def C5_N : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 21
  | 7 => 52
  | 8 => 40
  | 9 => 1
  | _ => 0

def C5_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C5_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C5_recordBits : Nat → Nat
  | 4 => 14
  | 5 => 21
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C5_records : Nat → List Nat
  | 4 => [0x2307]
  | 5 => [0x362c3a03e320208f8f0c3b6281e3bb2d01d9a]
  | 6 => [0x10da478a523a6405d92db4d16d680d8d806c7e2c21f0db0f6c8c7b6263c88ff0021cf910c7c52d3931e1ec985986b67476c5ddb63d0d94b]
  | 7 => [0x37e806cfe2a39e022df010f78f19e4019ee016fe005bf0039fa1a69e021df009af8031ec014ee014df9098f802bdc01fde01a7700cbd8043bc02bbe019df007b780597c00ef601b1f0109fc5273c037beb535e4c6cf80873da26ae0126f009efb24d6c02abe0007f00bef807afc01df60107700dafc5893c011fd15b1f00a2f8021ec03a7e01cbf]
  | 8 => [0x34aaa80595492aaa3d5558aaaa8b555532aaa6d5550eaaabc5555c2aaa955555caaab5555452aaa0155600acac8555432aaa8955526aaabf555412aaa8d55518aaa80556442aab115558a8aa806555322aac555500aaa8455542aaaa2555506aaa81555404aaa5d555]
  | 9 => [0x7f]
  | _ => []

def C5_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 13
  | 8 => 10
  | 9 => 1
  | _ => 0

def C5_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 128
  | 7 => 0x400
  | 8 => 0x400
  | 9 => 2
  | _ => 0

def C5_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 8
  | 7 => 11
  | 8 => 11
  | 9 => 2
  | _ => 0

def C5_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x5608
  | 6 => 0xb6f2d020187
  | 7 => 0x14ec2ec0f80700e718018014ca00814c23
  | 8 => 0x4d840002970020cf05e0181bc14
  | 9 => 2
  | _ => 0

def C5_S (s j : Nat) : List Nat :=
  qDirectState C5_initial (C5_countBits s) 15 7 (C5_slots s) C5_values
    (fld ((C5_records s).getD (j / 256) 0) (C5_recordBits s) (j % 256))

def C5_idx : Nat → List Nat → Nat :=
  qIndex C5_N C5_buckets C5_flag C5_seedBits C5_seeds

def C5_routeCodes : Nat := 0x1440000001200000004000000000000000000000000000000000000001000000004000000000000000000000000000000000000000000000000000000000000000000000000
def C5_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C5_rankPool : List Nat := [7695241, 1059752, 5258957, 7409068, 5336202, 5405850, 4413835]

def C5_rows : List Nat := [33, 42, 44, 74, 76, 81, 82, 84, 3, 5, 9, 6, 24, 48, 96]
def C5_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C5_rows)
def C5_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def C5_ori : List Nat → List Nat := qCompactOrient 2 C5_routeCodes
def C5_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 7) (compactCover 8 7) C5_S C5_N C5_idx C5_ori
    C5_coords 4 C5_rankPool s
def C5_F : Nat → Bool := certAt C5_Z C5_N 10
def C6_initial : List Nat := [0x9b6, 0xe49, 0x1292, 0x1524, 0x6007, 0xa038, 0xc1c0]

def C6_values : Nat := 0xe1f8e1c0e03fe007e000d1c0c9c0c3c0c000a83872976e4f69b7600035242e4929b620001fb61f6d1f241edb1e921e491e001db61d241bb61a9219b617b617241400120010000fff0e000bb60a0008920806080002000092000600020001

def C6_N : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 29
  | 8 => 23
  | 9 => 1
  | _ => 0

def C6_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C6_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C6_recordBits : Nat → Nat
  | 4 => 13
  | 5 => 19
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C6_records : Nat → List Nat
  | 4 => [0xbf0]
  | 5 => [0x1e4f002b1eeb1c0d2f838cf0]
  | 6 => [0x308f1bec1eaa7ca7787805fc015ecb1dca998f52ab674de4c2dd006fb344f8]
  | 7 => [0x153f009fc050fd637b009fe022de025f8077f00af7021ee03ff951bb5233e018fa015f8057b226f3006fc00ff80a5f80877014fc011f8003f8107d02e7f6bd3c03bdb8b76]
  | 8 => [0x5155501556b55550d55519555515544555501559015650955501655355557955569555115558d55505555955550155531555155551955491555]
  | 9 => [0x7f]
  | _ => []

def C6_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 8
  | 8 => 6
  | 9 => 1
  | _ => 0

def C6_flag : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 128
  | 7 => 256
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C6_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 4
  | 6 => 8
  | 7 => 9
  | 8 => 12
  | 9 => 2
  | _ => 0

def C6_seeds : Nat → Nat
  | 4 => 2
  | 5 => 98
  | 6 => 0x4f4a0611
  | 7 => 0x708cc6a100082c0219
  | 8 => 0x81700452f0010060d3
  | 9 => 2
  | _ => 0

def C6_S (s j : Nat) : List Nat :=
  qDirectState C6_initial (C6_countBits s) 16 6 (C6_slots s) C6_values
    (fld ((C6_records s).getD (j / 256) 0) (C6_recordBits s) (j % 256))

def C6_idx : Nat → List Nat → Nat :=
  qIndex C6_N C6_buckets C6_flag C6_seedBits C6_seeds

def C6_routeCodes : Nat := 0x114000021100000000900000002000000000000000000000000000000100000010400004110000021110000000b00000002000000000000000000000000000000000000014400000144000021110000020e00000020000000000000000000000200000000000000411000004105000003130000080600000080000000000000000000000800000002100000011000004404000022220000010400000010000000000000000000000100000000000000440400000114000003020000080000000080000000000000000000000800000002000000010400000000000021300000000300000004000000000000000000000000000001300000000000004015000021320000000700000004000000000000000000000000000001000000000000000154000020130000020e000000200000000000000000000002000000000000004100000040150000001300000006000000000000000000000000000000000000001000000000000041400000201000000208000000200000000000000000000002000000000000004140000000000000000000000000000000000000000000000000000000000000000000000000
def C6_coords : List Nat := [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def C6_rankPool : List Nat := [5258684, 2103945, 5339800, 4353483]

def C6_rows : List Nat := [17, 26, 28, 33, 42, 44, 65, 74, 76, 3, 5, 9, 6, 48, 80, 96]
def C6_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C6_rows)
def C6_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C6_ori : List Nat → List Nat := qCompactOrient 12 C6_routeCodes
def C6_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 9 7) (compactCover 9 7) C6_S C6_N C6_idx C6_ori
    C6_coords 4 C6_rankPool s
def C6_F : Nat → Bool := certAt C6_Z C6_N 10
def C7_initial : List Nat := [0x750, 0x98d, 0x122b, 0x20f8, 0x2407, 0x4832, 0x50c4]

def C7_values : Nat := 0xe989c31361bec32d1f5a0cb203e0f8b39b63dac6254c4a58948ae8e24f72937f20023a840006c56c8ad6c7ac0753faa3e13fc27574ea0941d27fa4f8480087e1028203040508000dd79a2b2c564cac7ee8f5012002000200010000a000c00140022002000240018002

def C7_N : Nat → Nat
  | 5 => 3
  | 6 => 11
  | 7 => 40
  | 8 => 34
  | 9 => 1
  | _ => 0

def C7_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C7_slots : Nat → Nat
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C7_recordBits : Nat → Nat
  | 5 => 19
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C7_records : Nat → List Nat
  | 5 => [0x12398b8911f1a87]
  | 6 => [0x9a18e373900c67df32f2318f771b44e66de367c309dc63300e76]
  | 7 => [0x16ee054fc09ef80af7010f6033dc04fb80c6f014ee043bd32b380e760377e03fdc037f0067d8d3e603ddc0cb7808fb02c7e039fa24f3818f779dec001fc0b9f80c77798cee27d8073b80c67dd36e04df806f7815fb023f601fec0b5f80bf7]
  | 8 => [0x15954d51525555016550555581555a5555695552d5550d5554d55579515395559555579555a155511555bd55501556d95552155549555c1555015551955515555d15558955529555095551d555019557555501559]
  | 9 => [0x7f]
  | _ => []

def C7_buckets : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 10
  | 8 => 9
  | 9 => 1
  | _ => 0

def C7_flag : Nat → Nat
  | 5 => 8
  | 6 => 32
  | 7 => 0x400
  | 8 => 0x1000
  | 9 => 2
  | _ => 0

def C7_seedBits : Nat → Nat
  | 5 => 4
  | 6 => 6
  | 7 => 11
  | 8 => 13
  | 9 => 2
  | _ => 0

def C7_seeds : Nat → Nat
  | 5 => 7
  | 6 => 0x18093
  | 7 => 0xb860340dd0020950dc0201500f
  | 8 => 0x1015750000c4d102281103040080a2
  | 9 => 2
  | _ => 0

def C7_S (s j : Nat) : List Nat :=
  qDirectState C7_initial (C7_countBits s) 15 6 (C7_slots s) C7_values
    (fld ((C7_records s).getD (j / 256) 0) (C7_recordBits s) (j % 256))

def C7_idx : Nat → List Nat → Nat :=
  qIndex C7_N C7_buckets C7_flag C7_seedBits C7_seeds

def C7_routeCodes : Nat := 0x11040000203200000800000000000000000000000000000000000000200000001004000000000000000000000000000000000000000000000000000000000000000000000000
def C7_coords : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C7_rankPool : List Nat := [5401464, 3235194, 4275595, 5262473, 6507143, 1059757, 3239033]

def C7_rows : List Nat := [14, 28, 42, 70, 81, 84, 97, 98, 3, 5, 9, 18, 36, 72, 48]
def C7_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C7_rows)
def C7_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def C7_ori : List Nat → List Nat := qCompactOrient 2 C7_routeCodes
def C7_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 7) (compactCover 8 7) C7_S C7_N C7_idx C7_ori
    C7_coords 4 C7_rankPool s
def C7_F : Nat → Bool := certAt C7_Z C7_N 10
def C8_initial : List Nat := [0x1a5, 0x29a, 0x552, 0xa61, 0x140d, 0x280e, 0x3070]

def C8_values : Nat := 0xd1c3170c3c0f731f683bf06000800014001

def C8_N : Nat → Nat
  | 7 => 5
  | 8 => 8
  | 9 => 1
  | _ => 0

def C8_countBits : Nat → Nat
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C8_slots : Nat → Nat
  | 7 => 1
  | 8 => 1
  | _ => 0

def C8_recordBits : Nat → Nat
  | 7 => 11
  | 8 => 18
  | 9 => 7
  | _ => 0

def C8_records : Nat → List Nat
  | 7 => [0x43f4fd4fe5f87f]
  | 8 => [0x5555955515554d555755549555055595555]
  | 9 => [0x7f]
  | _ => []

def C8_buckets : Nat → Nat
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C8_flag : Nat → Nat
  | 7 => 8
  | 8 => 64
  | 9 => 2
  | _ => 0

def C8_seedBits : Nat → Nat
  | 7 => 4
  | 8 => 7
  | 9 => 2
  | _ => 0

def C8_seeds : Nat → Nat
  | 7 => 53
  | 8 => 0x7a4
  | 9 => 2
  | _ => 0

def C8_S (s j : Nat) : List Nat :=
  qDirectState C8_initial (C8_countBits s) 14 4 (C8_slots s) C8_values
    (fld ((C8_records s).getD (j / 256) 0) (C8_recordBits s) (j % 256))

def C8_idx : Nat → List Nat → Nat :=
  qIndex C8_N C8_buckets C8_flag C8_seedBits C8_seeds

def C8_routeCodes : Nat := 0x22130000010500000080000000000000000000000000000020000000000000001515000022130000010500000080000000000000000000000000000020000000000000001555000011230000020a000000400000000000000000000000000000100000000040000001040000101100000e0200000080000000000000000000000800000010000000010400000040000011230000020a000000400000000000000000000000000000100000000040000014110000101100000e02000000800000000000000000000008000000100000000104000014510000202200000d01000000400000000000000000000004000000200000000144000004100000212000000a0d000000200000000000000000000002000000202000000410000001440000202200000d01000000400000000000000000000004000000200000000144000011050000212000000a0d00000020000000000000000000000200000020200000041000001145000012100000050e00000010000000000000000000000100000010100000045000001515000000000000000000000000000000000000000000000000000000000000000000000450000012100000050e000000100000000000000000000001000000101000000450000000000000000000000000000000000000000000000000000000000000000000000000
def C8_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def C8_rankPool : List Nat := [5532039, 4398508, 6376859, 6306424, 5377213, 1072266, 6564729]

def C8_rows : List Nat := [25, 38, 49, 50, 70, 73, 76, 3, 5, 10, 20, 40, 80, 96]
def C8_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C8_rows)
def C8_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C8_ori : List Nat → List Nat := qCompactOrient 14 C8_routeCodes
def C8_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 7) (compactCover 7 7) C8_S C8_N C8_idx C8_ori
    C8_coords 4 C8_rankPool s
def C8_F : Nat → Bool := certAt C8_Z C8_N 10
def C9_initial : List Nat := [0x21e, 0x41e, 0x7e1, 0x82a, 0x854, 0x1086, 0x1118]

def C9_values : Nat := 0x7afb97d918c575fe6fc379ebcc5ce2e3d718b43567ab31538a8f546293d48698c4a7a50d19e8cc44e1fd6fe173f3979ca8e3e71538798fcc5e62a30f9854c1e52a28f90fc8204001ffcc7c62030f1818c0043e210100040c200010007800c002

def C9_N : Nat → Nat
  | 4 => 1
  | 5 => 13
  | 6 => 38
  | 7 => 49
  | 8 => 20
  | 9 => 1
  | _ => 0

def C9_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C9_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C9_recordBits : Nat → Nat
  | 4 => 19
  | 5 => 25
  | 6 => 25
  | 7 => 26
  | 8 => 20
  | 9 => 7
  | _ => 0

def C9_records : Nat → List Nat
  | 4 => [0x6da98]
  | 5 => [0x1a3c02b516018e0700c5e5806d79902b98e00fa39000337806d938da530c6d64e60003178040864]
  | 6 => [0xef8000efc00037e01be4f0090c780018bc02b4de01894f000317a00107c03694d815d27408cc78001dfc02ca1e00fa1b00ca87807263c03131e00017f194d0c80016bd000ade815b0b40ae7780562bc00033e00899d00690ca042678036b1c81418f00651ca000dfc00073e00015f1240cc800173d]
  | 7 => [0x25551017554407555100c56400ac551dec154401555400c554071555000a554681455465051440555514cc5540c295503045540090555008554783155003a5544f3155040c5541d4d550302554008c55500c558003155102815540015556535540c315505c555400855455d355400195544905054c0555074c5542a4d55088c554005955100a5540c0d55001a5545231550039155404551501d5540c15550]
  | 8 => [0x315553d5553155101595e15554d5555d55101556095554955531550415558955505555015650d55515554015551155515555]
  | 9 => [0x7f]
  | _ => []

def C9_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 10
  | 7 => 13
  | 8 => 5
  | 9 => 1
  | _ => 0

def C9_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 512
  | 7 => 512
  | 8 => 64
  | 9 => 2
  | _ => 0

def C9_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 10
  | 7 => 10
  | 8 => 7
  | 9 => 2
  | _ => 0

def C9_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0xb6a0901
  | 6 => 0x610040744740c0200180005
  | 7 => 0x1e80f06e8ac020e80a008042d00282001
  | 8 => 0xf1605087
  | 9 => 2
  | _ => 0

def C9_S (s j : Nat) : List Nat :=
  qDirectState C9_initial (C9_countBits s) 13 6 (C9_slots s) C9_values
    (fld ((C9_records s).getD (j / 256) 0) (C9_recordBits s) (j % 256))

def C9_idx : Nat → List Nat → Nat :=
  qIndex C9_N C9_buckets C9_flag C9_seedBits C9_seeds

def C9_routeCodes : Nat := 0x4500000120000000502000000100000000000000000000001000000100000000410000010500000200000000902000000100000000000000000000001000000200000001010000011400000213200000a04000000200000000000000000000002000000201000001104000011400000203200000a04000000200000000000000000000002000000201000001104000011040000033200000a04000000800000000000000000000008000000021000001140000011040000023200000a04000000800000000000000000000008000000021000001140000004040000032000000500000000400000000000000000000004000000010000000400000010040000212000000c00000000400000000000000000000004000000210000001000000001140000031000000802000000800000000000000000000008000000020000000110000001140000021000000802000000800000000000000000000008000000020000000110000004440000023200000004000000000000000000000000000000000000001000000444000000440000003200000004000000000000000000000000000000000000001000000044000001000000031200000804000000800000000000000000000008000000021000000100000001000000021200000804000000800000000000000000000008000000021000000100000004000000020000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000
def C9_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def C9_rankPool : List Nat := [1059685, 3153016, 4209574, 3278972, 2104214, 4205736, 1064087, 3165061, 2116743, 4392539, 1064103, 4201334, 4205672, 2112599]

def C9_rows : List Nat := [1, 106, 108, 114, 116, 3, 5, 9, 17, 33, 65, 6, 24]
def C9_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C9_rows)
def C9_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)
def C9_ori : List Nat → List Nat := qCompactOrient 16 C9_routeCodes
def C9_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 5 8) (compactCover 5 8) C9_S C9_N C9_idx C9_ori
    C9_coords 4 C9_rankPool s
def C9_F : Nat → Bool := certAt C9_Z C9_N 10
def C10_initial : List Nat := [0x21b, 0x3e4, 0x458, 0x81c, 0xc23, 0x1089, 0x1112]

def C10_values : Nat := 0x1ebbe55f08f22589dc44e072db7512a6cd1627ed3ed9f24e6e7253529994c6e62529b944c86e3371928a944ca1010007fe3f9dfc8ea373db9e1cc6e5c72db961c76e23651b1ed8f0c6362e316187ec2060e30017f8be451c287d438a1b50022710b883c41020610108044001ff0fc86d833c196ccb061b26c11e08804001ff8a6c50025b12008ec440218104880c40008002000800300090040010006001

def C10_N : Nat → Nat
  | 4 => 1
  | 5 => 15
  | 6 => 67
  | 7 => 101
  | 8 => 43
  | 9 => 1
  | _ => 0

def C10_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C10_slots : Nat → Nat
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C10_recordBits : Nat → Nat
  | 4 => 21
  | 5 => 21
  | 6 => 28
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C10_records : Nat → List Nat
  | 4 => [0x10a060]
  | 5 => [0x405f8aa5338c4de2a2d192d35c211be109d6484df0ce5ad273364e59e200ff93e6989cadc801df2]
  | 6 => [0x273e00b54f40000e7a00cd4f200e50660078df8013a61e000147600f19f200ccdf2013953600e97e601356f40080d720138d3a00cc57201527bc00f4d72000283e86e97640139a360139736017ae1701359f200e5a6600e4d6a00c0df200d087200e99f20139cae0001cee0121a3300dd7e3015251d00019f300a8d7200d5a630000d7a00028be00d0d7200b457400e576600016f500b4df4013e31e014e29e00e55660169a7201799b30000efa00cd6f1013903600018e7000167600e96f40001f6e00020ee01796b500021750110df200d0df2000293e00d08f200bcdf20101a7200b8d720001b73]
  | 7 => [0xb7b686fb3411cec34e6e97760179f8073bc04cfce9a765c37b0031ec01af401d7e0033f008efd01bec019f79a83b1b2bea5453e01aefbc81b80a7f800efc0007f003ff005ddd70aec030fe66839805bf4054fb3853e00e7f0069de7c57c018770137f2a15d9a1bf47cdfa5c6fb2015d802dee02cbf0083b8067cdd20ec02d7e342bd00b7dc01afc013f7009bb8047dc022ee01c6f00cfdc375b8040fc009fe0043f4d69d9c8adc014fe006ff0073b804bfc012f76ed39cd5dd800dfc005fe006bd809cf800afcd0df30113bc35dd4024eeb50750047f3a47d801efa02bfb017f78090fc012fc01577011af809cfc0497e00cfe005fda941d9a0aec010f7686f9005bd6b4f7c017f7]
  | 8 => [0x205555baaab1555536aaa345456c2aaa0195500aac815554daaaa5555564aaa945555d2aa90d55500aaa86555452aa8e955510aaa83555702aaa015955ca8acd555002caa1555508aaaab555452aaa2555504aaaae55543aaaa01565baaaab4555652aaa01556aaaaa9f55566aaaa81515]
  | 9 => [0x7f]
  | _ => []

def C10_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 17
  | 7 => 26
  | 8 => 11
  | 9 => 1
  | _ => 0

def C10_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 0x400
  | 7 => 0x800
  | 8 => 256
  | 9 => 2
  | _ => 0

def C10_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 11
  | 7 => 12
  | 8 => 9
  | 9 => 2
  | _ => 0

def C10_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x614202003
  | 6 => 0x246c4ac3087204e1d01086b084034060080080280a40b
  | 7 => 0x82c4910178211638140021780f203700e04701c16410102200705803403002d012865003015001
  | 8 => 0x240020d2d2e01e0f1b0261e0b
  | 9 => 2
  | _ => 0

def C10_S (s j : Nat) : List Nat :=
  qDirectState C10_initial (C10_countBits s) 13 7 (C10_slots s) C10_values
    (fld ((C10_records s).getD (j / 256) 0) (C10_recordBits s) (j % 256))

def C10_idx : Nat → List Nat → Nat :=
  qIndex C10_N C10_buckets C10_flag C10_seedBits C10_seeds

def C10_routeCodes : Nat := 0x1110000002000000208000000200000000000000000000002000000002000000110000000000000000000000000000000000000000000000000000000000000000000000000
def C10_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12]
def C10_rankPool : List Nat := [4340328, 2181477, 2103943, 4204121, 3221626, 2165336, 2111861, 3279222, 3295879, 4331862]

def C10_rows : List Nat := [42, 50, 65, 108, 116, 3, 5, 9, 17, 33, 6, 66, 24]
def C10_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C10_rows)
def C10_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)
def C10_ori : List Nat → List Nat := qCompactOrient 2 C10_routeCodes
def C10_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 5 8) (compactCover 5 8) C10_S C10_N C10_idx C10_ori
    C10_coords 4 C10_rankPool s
def C10_F : Nat → Bool := certAt C10_Z C10_N 10
def C11_initial : List Nat := [0x3e10, 0x42a5, 0x454a, 0x8863, 0x918c, 0x101f0, 0x1200f]

def C11_values : Nat := 0x7abbf97efbff0dfce6f84373dfb98cdc07ece33631fb18cd807ec00350dfa863d007e800323f991f0c8c66400313e78863c400607c300017ff5bff85fafefd6b7e10b3f7d953eca9563ffb157d8a96c41f600fb00051ffe8bf5454aa1fad0fc2854b41f0a0004fffe7fe13e709f0fcf842601f2a0f9407c983e481f23f091504883e440121ff90f8481be405f201f9001c800217e109f083f840fc2040101f380f8c0782030100e0803840182004100108001c0001fdeedd4a6df7b5739ab18d3ad69c6346319fdecd6b6631b2b9d90c6c54a6152afe717ce6be105cc62ce316318a8634dc6267bd331898634c0025e312b18938c45319fffcfeb47eb53f0819528c54a4d4a255291fbc8e9446a5220010f9485ce42e5215a90abc854e42a0211090814840040a020109001480003e701f188f84c44002010100188000140006000150008840420020501000078001c0007000318018400c000230010800800020000f00038000c00020000

def C11_patterns : Nat := 0x9556155855195555655565555554554555055155415501505515545451454455105415505115945611564555154454514141550544115015155455415445451504455056415605541540514055

def C11_N : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 110
  | 7 => 227
  | 8 => 193
  | 9 => 23
  | 10 => 1
  | _ => 0

def C11_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C11_patternBits : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 0

def C11_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C11_recordBits : Nat → Nat
  | 4 => 23
  | 5 => 31
  | 6 => 31
  | 7 => 30
  | 8 => 22
  | 9 => 14
  | 10 => 6
  | _ => 0

def C11_records : Nat → List Nat
  | 4 => [0x53d306]
  | 5 => [0x4d9f878b772230014e7f1802865438050ce8700a5771d432aee1a31dc78c50c0bb8a00a3771d4cae8a18029e88700534907a18a77140142ee3a61dccc54c3ba086a19d770c00aa8b88029115350cec5039895330600013e3c028a503b3a29f86]
  | 6 => [0x236f003bb59ea29e454c9e945f840001b8f80339c8f004531e4f48a7f1801dc8ae00003bde9895170f312b101c01ddb8f0033911d9895778c00ee853a4d14fe32ba29fc6a257451c0145243c019c94e80001e679877671c00ce687a6205de5004c3bce9888771c0142ae3c02addcf802a22e6a17a771c008a7f995d09043802a22e79e98771cae84662d2514ff10050bb8e672f1e32008a799800ec7b4803ba7ce00776a3c0118ee7a7a62543a9a6a4618b572233312b030c01cc79c80491fc7a29a771c010aee7800e88b480443b9e534d45c5528a7f1801dda0f54513b8e00a19d0e0142ce3c0285dc78050ce8fa19d7a0f4314ce2e89dd1c70055bb9ea29a950e00e444e685e9e074e229fa69c933f0e01408aba85dd5c7004c4ac79857410e00ce7c3e86759c38000339f0076455d4530ee3a615ccc58043bb9e0000843e00ae883e85dd9c7514f49870057421e00ce843c0114f730033a78f00a19d8e00eede7a315c78c80004bcf8b771e3400a4998c0285de70050cea77757421c00ae863c0285dd7004c338f772f1eb000eece7801dcfa74c3b8b8e005234d400ee7338029917300504c8f]
  | 7 => [0x15c60300003e7401e89510050226c01dc0d20000674e7a615c000773548015cd120000228c0000edd0078670c00d08a28b881e1c000096300743e18015c5c3006f630c000002500574218028a4cf0000904c01dd9d20098773c01bce4600007f4c0001ccb007a670d4d447990067060cd0bc79f7a2f1e4221dd5c200007748026254c002f2281f4bc79000453f71e9dd9c20067170c01e9a0300573e3c01e9e12008b2280000141d0000574c0001f53009034480001dd3008c570c018ce4f00453f6001f9dd200005a4c01e93cf0051496a85e99c0002f1e8000008e30080670c00019cb0057420000017d30098773a62215c000007790015c8910067080c014515d00ab570c019c78300776d4801dd652a298570001dd5d2572f1e4001dc5d20000644c000261d0088770c01387a000985e3c01dd2d20088570c019c0c300392e68015ce4f7a7867080108cda00a2457000b88a000987a3c01bd5c300857a0c019c2830067140c000175300a25b0c021d9c34f2f1e6400017130000752c0221dca006d670c01dc79200005b4c00019c4003938600001653002c10815d085c00000714c01348a000770a4a8a695c000003974000101d00774b4c0285e8f0000437402615cf00007754013cd1c009877700000d24008e7749dd9d5c29877573801dd9ca00857d0c01e8d12007b670c0262558007d4f3c019d9c30051457000018d30000682c019d2c30000248c02859cf0077670800019930091670c000218b003a1e69dd5c5c2009e9818015d3cf0077670c0214d0a0067010c000109d004631780001bcb47463f5c01dc19298955730019cbc3006a570e615c5c00088774801dc2120000447400d0422a25747000001de90057423c00019c30085570c0194f8f0098953c02307a00088770802188890078774802153c60000a17400b47a0007a1b48019cd430000704c0201dd20098963c0001f1300004f7401dc052006c423c02219c300453f5c0109058007a423c02859c6007710480221643006c670c01dddd200a16700019d5c30067100c01ad5c30000852c0001e5300007a4c015c68300721e20026205a9881573401fc891007a3e3e2d5c78100473d600001893887a780801e8e4f007a224401d91c600006c4c00019c500772f48013d298001e1580015cc83007d344801e9dd2007a6f0e14bc787]
  | 8 => [0xa25004896615dd80574d4d45d007e9401865001195dd5d3570a4d3c79d006995085dd00209400026006a94bc7a1006f2c01b25001f9401e94001a9402165001794012e6007a940226588572cd8d64004274019d3571e4c006e5007894005a563104c00365004f7400d25a29a755d2d3000995b05d37a354d5c5cb000c962e20b572f4de92d300397400d2477574a615cf002d9402225005b94d88a300299400c254d1e855c19300089400165007d4c00025001394008a551477400f9d000e955c05300839401dd2007795e829300670de851300774c009e57a670c02465005b4d5c0d300852d5c5c300199400aa535108de879378594c00ae57b7a4c02325917a4c018d37d1e4c78423001d94013a50000ace441d0059940052500574de95d37a104de99cb0057595d5d300228de99d3003795bc40b006f94001e57a6d4c019e5005895dd5e4004b94018e500809400d6557174d5cd5357084c003e5473f7400565005750015a52f1e800261d851e2c015ea001c9400be588570c0006557104de85d3002196796d3000394009a57a784c01f65006b94002e5000494004252e108621e93807a4e0a0137a784801eaa00129402ae588782de9e93341e9001b65006c4c01de47a084db55d300aa94007a5000a94023e50000a001e938b1e85e8193a24774019cb00189401825007a59e15d3000295e8bd3007b9400ca588574c00027000695e80d3005794016537e574de9e24]
  | 9 => [0x15e5009c7a56d9402b80941a50394d6508945e51095ea58895e2500992e57a4c02500a02a5574cbe5]
  | 10 => [0x25]
  | _ => []

def C11_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 28
  | 7 => 57
  | 8 => 49
  | 9 => 6
  | 10 => 1
  | _ => 0

def C11_flag : Nat → Nat
  | 4 => 2
  | 5 => 512
  | 6 => 0x400
  | 7 => 0x800
  | 8 => 0x800
  | 9 => 0x1000
  | 10 => 2
  | _ => 0

def C11_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 11
  | 7 => 12
  | 8 => 12
  | 9 => 13
  | 10 => 2
  | _ => 0

def C11_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x2010440d005c60090f
  | 6 => 0x76d1a40390e06400c5480416b19c0f8030e50f8068090080360601630e2ee048010ac00488001
  | 7 => 0x16e1470f017072a8d10110b119504b0e700113c00205607e00e02400102614501e00115f01504e0020100030057ef02c00201100200401c00311288100207000686585a02a85100302502000105300200200900c002
  | 8 => 0xb01010388856986503945900300303b01384b0010040ca0491740020320388370991de01f00102c00800100e00901002205b00700101c00182600902303a02005900e02b008002003
  | 9 => 0x2e14031801602e001
  | 10 => 2
  | _ => 0

def C11_S (s j : Nat) : List Nat :=
  qDirectStatePattern C11_initial (C11_countBits s) (C11_patternBits s) C11_patterns 17 8 (C11_slots s) C11_values
    (fld ((C11_records s).getD (j / 256) 0) (C11_recordBits s) (j % 256))

def C11_idx : Nat → List Nat → Nat :=
  qIndex C11_N C11_buckets C11_flag C11_seedBits C11_seeds

def C11_routeCodes : Nat := 0x45040000000100000300000000200000000000000000000002000000000000000104000054010000032100000600000000400000000000000000000004000000010000001044000050410000232200000c00000000400000000000000000000004000000210000001404000040440000120200000400000000000000000000000000000000000000100000000004000011450000210300000a00000000200000000000000000000002000000200000001100000004450000032000000400000000400000000000000000000004000000010000000440000010000000212300000c00000000400000000000000000000004000000210000001000000000000000000000000000000000000000000000000000000000000000000000000000
def C11_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C11_rankPool : List Nat := [239352137, 272842092, 134398253, 206711086, 136330604, 205798731, 235024751, 272710026, 135281066, 172177769, 137642381, 135479629, 134299051, 136561037, 205764970, 135380395, 272809260, 136560941, 205699370, 205765002, 239254828, 272873866, 172211595, 136593741, 170013007, 241315118, 235023695, 206713166]

def C11_rows : List Nat := [42, 44, 50, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 33, 6, 24, 96]
def C11_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C11_rows)
def C11_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C11_ori : List Nat → List Nat := qCompactOrient 8 C11_routeCodes
def C11_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 9 8) (compactCover 9 8) C11_S C11_N C11_idx C11_ori
    C11_coords 5 C11_rankPool s
def C11_F : Nat → Bool := certAt C11_Z C11_N 11
def C12_initial : List Nat := [0x1e4, 0x258, 0x41c, 0x81c, 0xe23, 0x1089, 0x1112]

def C12_values : Nat := 0x3d57e23e897277913c1cc896227039512a4ecc4a5b32588f6c7923371928a944ca1010007fe3f9dfc8ea373db9e1cc6e5c72c38fdc40e1c70037f1bc8c9c62e30f1840c1c60c3021808c005fe2f914f0a5c52c28714009fc4f222710b883c4102000cb86582fe179083040820210007f83e416c09e0480200040010004001c00c0020008001

def C12_patterns : Nat := 0x655590559556055595559555955555515515515544550551554515115425506541545545545551514155

def C12_N : Nat → Nat
  | 4 => 1
  | 5 => 14
  | 6 => 68
  | 7 => 91
  | 8 => 34
  | 9 => 1
  | _ => 0

def C12_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C12_patternBits : Nat → Nat
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | _ => 0

def C12_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C12_recordBits : Nat → Nat
  | 4 => 21
  | 5 => 28
  | 6 => 28
  | 7 => 19
  | 8 => 12
  | 9 => 5
  | _ => 0

def C12_records : Nat → List Nat
  | 4 => [0xe9c60]
  | 5 => [0x14271300d9ae10001bf100017720001d7200d1770870949200019630141a3100e186101417320101ab100809f00001a71]
  | 6 => [0x147300017730084af1010d4f20080e7400749f200013f30001e730001a7501010b50131035000107500a49f2011d4b300d90e500011f601412b300018f301254b300fd4b300e54e300a46f2000157300f94d301014b300707f200a4af101454e300d94e300d12f1000177200b94f200017f300014f30080a7100026f300015f3010e11e0001a710001a7300012f384f5493000137301054b300b92f2000167300a467100bc9f2013259700d43f10000e7600d4af100849f200ed7f200807f100a457100016f301414b30119af100e1af100d14f10001af3000117500a45f10130e360001776000187301154f1]
  | 7 => [0x84b1548129d2855258b3d4940205005273a3caecea54a52801af263d801f0c04570014e8ca4a00fa801c5291c500854021bc00b7006c400d4aa42954942951eb7aa4b2149402928026f0094a014d001b50022d00e4884a1508f2801ed76a4a01aaa12928024d01044a44157a9280a242e3ca01020029500536421d0a479548428048a70850e14962292805268c8500004292928034a00794a431404712912566a4ad549401570018e009540248804a5005ea0041ad4b154a92a90e5520ca00e240401003aa84f41247840195005e500614a41157942807e2]
  | 8 => [0x71005052552a6703aaa500f09107700108500170700122d01101d00900b01302905300150d08900110301ed0138d01f042a7b0]
  | 9 => [0x10]
  | _ => []

def C12_buckets : Nat → Nat
  | 4 => 1
  | 5 => 4
  | 6 => 17
  | 7 => 23
  | 8 => 9
  | 9 => 1
  | _ => 0

def C12_flag : Nat → Nat
  | 4 => 2
  | 5 => 32
  | 6 => 0x400
  | 7 => 512
  | 8 => 128
  | 9 => 2
  | _ => 0

def C12_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 6
  | 6 => 11
  | 7 => 10
  | 8 => 8
  | 9 => 2
  | _ => 0

def C12_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x302401
  | 6 => 0x20b5901e00433f00c21c0180b1e6028020018842c005802
  | 7 => 0x18908007908452254c0040b010143ed77004020641d074ce370c902806
  | 8 => 0x710615d8a8304760e
  | 9 => 2
  | _ => 0

def C12_S (s j : Nat) : List Nat :=
  qDirectStatePattern C12_initial (C12_countBits s) (C12_patternBits s) C12_patterns 13 7 (C12_slots s) C12_values
    (fld ((C12_records s).getD (j / 256) 0) (C12_recordBits s) (j % 256))

def C12_idx : Nat → List Nat → Nat :=
  qIndex C12_N C12_buckets C12_flag C12_seedBits C12_seeds

def C12_routeCodes : Nat := 0x5110000002000000208000000200000000000000000000002000000002000000110000001110000002000000208000000200000000000000000000002000000002000000110000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def C12_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12]
def C12_rankPool : List Nat := [4340344, 2181509, 3155545, 3279222, 2103895, 3295879, 2111861, 4331910, 4204666, 2165368]

def C12_rows : List Nat := [10, 18, 97, 108, 116, 3, 5, 9, 17, 6, 34, 66, 24]
def C12_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C12_rows)
def C12_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)
def C12_ori : List Nat → List Nat := qCompactOrient 4 C12_routeCodes
def C12_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 5 8) (compactCover 5 8) C12_S C12_N C12_idx C12_ori
    C12_coords 4 C12_rankPool s
def C12_F : Nat → Bool := certAt C12_Z C12_N 10
def C13_initial : List Nat := [0x790, 0x1073, 0x188c, 0x207c, 0x2903, 0x4225, 0x444a]

def C13_values : Nat := 0x1eebfd7efaadf1f9e233a25727fe44bbc0f6a5ed4ada07b12b593eb25d607a897481e7fdcff99ed73c8654ac8fd91f32256400c64b89f713e6225c0f98002fdedf9cbddf733ae465c4ab5ff6ab6c4657f7acff532aa3dd44aa4ef4896839ccca989528963ffc7da8f6b1e42365466f8c95189630045ca8a95132a20042a584eb099e11ac22784490886100c200804300060003ffc7fe6ffc1fcfbf9c7f20ebf1d4639ff73f8e63dcc639837300e5cdc91b9037200e3fdc7e38f07158e271c46388070f8e1cdc3838006ffedff1bf9b79061f8c20183fb07c60e6c1c180830005ffebff17c9af905e06ae0d581a98352fea5f1491a90051f8a24143e282450009ff13f827b44f389e4133e237c46488bf113e220043f886310be2170420083f104020704048804100620003ffe7e70fc81a8c331863fcc7e18ad31586270c47988d310061ccc0017f32fe05e4cbc81273230645cc87990f0210041fc83b907120e0418c818902320424080809901020184010801900120003e404400803100220003f807b10f261e443000280044208401008200030002400460084010001cc038807000c600c40128023004200800098010000a000c0008000

def C13_patterns : Nat := 0x655595164559146415651585561458155915595561556555655555545549551554154555055255491519546151654555145445510542550654155045405455515145151414455111415505141150154014555154454511541545551550551154051514505111414455114415505501510454055

def C13_N : Nat → Nat
  | 4 => 3
  | 5 => 46
  | 6 => 236
  | 7 => 466
  | 8 => 322
  | 9 => 28
  | 10 => 1
  | _ => 0

def C13_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C13_patternBits : Nat → Nat
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | _ => 0

def C13_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C13_recordBits : Nat → Nat
  | 4 => 23
  | 5 => 31
  | 6 => 31
  | 7 => 31
  | 8 => 23
  | 9 => 15
  | 10 => 7
  | _ => 0

def C13_records : Nat → List Nat
  | 4 => [0x12186624704c49e0]
  | 5 => [0x34b363428049c4e100e67d6800d275900001f7a6ae84785bd863a60011ae3900248eb80047436100863ae0011b0d8402461b0804c46e4937130c1231475824d90eb00038a070bf918a420001199401a4d30804ec8e1000098e9a59a745002f5f5a0070ee8700e6e42b26e249800246170dec6c321009b93c201c2e298024e0b08071d98e009271c4011afb9001c4d380049c0e1ac8f864201ad625802462b0e9431d30b3b18624011075c2fe28e9846c31d60]
  | 6 => [0x866ac601bf0ccc0248f78802f9374938f8ac201610ccc0274d38ed61588b00dfdb2e00be75d002b17db49c538e28d5f24c8010c4dc40218d388043127100b05f6c00dcbf9801a4f7280433763e2dec2177af274d002197f945369261008639e20001a2de3628eb2004947e300753ae9571448c74a18918806f38e6008d84ca010c6dc40001f7b5ec6bca5bd86246201b4bf9802cebcf0070b4a7bd8a3a690c7449c00218ff880003af5006634e2010cdb8c0001dfa8055370f00cc8dcb1b0c4984024e0b180661d74c9b3b13c010c53c40399d5aeab931a6009d4ae8010ce3c801a4a72805c4333007130e80126e3980002b8f80004b73000092e726c849840218b38e659d896d2cd5f2c00be61d002112ba0034a463b3b1632c01c18caf4a197d90046c365000069ce00be6fd00249cb18048be65000081ea01aabed801c5a7300002ff600ab86660000e3da197c9380064599e005f2ce8011495d002b2199d9d8c51700918aca0127059400035bb003e1d74de8f86c2011aff940249a7180492ff2005423cd7f1468c76acec4700004373b19e5f2c00d26196f6ee28a803c9d74006434e20166dd3a6618f7800431ef18d793ac923146984036a1b18046bae5009d3ae91ac6759001f5d7a006fb8b600993de80156bed80218eb9451d1a70006a5fcc00be69d0017d23958cf43138d7f3ac80167627b62cec4b59d8c99ebd7f3a697abe48d0017d279006ac93300ac644e011b1594023607280451a7100d286677b1b14964e2a0b0806ae817927263c400be49d001a48f334a59ee4d25f246800c8918c01f493a59d8a59e864b3de167631458017cdba0065d897007f3ae800e249d38b7b30380331d7400863ae33b26e58802188f96966bc1500007de8017aead64d90c3080431871008d86c6017b0ccc02462b0800044f5006d5fcc01c1a69c0219a7180319df4e2deb31d1b1421840382cd76966c31300a15fac0001cfcf8b0eccf4e49c561006924ca01251f940001dba8049c161d2cd3d2a011af3940218eb80059d71edaccb10e00c875d2cec490e00441271008a40e200fa75d000026fa8059c372009e701f7ac674d0017ca7a49c51d70938f86c20000fbd4034b34b80451d74008637e200d2bf98017ce7a006f38e7918a3dc20132fdd002e17db00431f7100863ae8017abed80276372e1c51d71009224e2011abf9801c4f7a00319d7400918ac6011b0d870e28eb800451c7100007bea0184bfcb4a18f588000417500d25f6d2715078402861a9e9669215]
  | 7 => [0x8a484399633c0400018d38043082100005f7401987a940001613800029a700005f5201a5142803357d3006c59a60072543000c6469a353490b00318da600860242000060c001c97d300003aa50000cb4e010cbe980210f9280002532004d244a000170380218550804ba4a10024235e011a107002f58c50061c3210000867a0156483003497c480319ca5009d3d4a011f0c94018ca52804f2fa600002b6000011a780229b4c5ec512080000694e011460940228fd280004227008d2438011474900002213800059b200a124220000d09c02e08c68049c521009d294a015f3c10022909080003ca7008d792c00f87a940002e470043122500863d4200d8be980002f47004518a50000564e010c7a9400017938043122100dac70c00f0be9af5349040059a5b200bd8a1400d2966000f841680451ea5008a3c4b14967a9000017538050b1900072634c00a83e60018cd928071660a009d244a0126be9802191d0e1c5121f00de5f4e004844b40000a5800002ca79d4b3d4801b9423de4e8912004a24210000405c00e646980002653d8cf498400cf8642016342100190f52800011b20053244a0158ac280001553804325a100926342007448bef5e4904004302a10049245b27144c7c01c5913004f43210063264a01a4c62802c2842006750900000ab1c01aaa82803497c50046b19893724b320001289c036b08d00002fbe00006b4e01b566740002193802faa2600b05a140160483001b98cc00319ba500cf5f4c0001249c000099800451d260000524e00f25294023628b0046811c00ba8a4a0000b89c0001a4c002b122500aba90801bf142a28f4d0f801d14af00bdbb08009c4c9402786820059b1a600635f4c0114d2600002b47005c120c007e5f4c010cbe840002c87004331a10000d84e0156da18034b340804304210075244a0001149c01b58cc006d45188a24103e01584830000169380004339b19e4b08fe74489000028c98000492100793d4a013ae498000244f46b1921600c35f4d271f145000e80978069678a938a3d3e00c6689400e841780451d25008a5f4c00f8689402f4e8680004ba700663d4a00c674900144912c9c5121fbd3a2417633cc6040001b4f0031a4a1008d8a30019366c80000b180000580e0050244a01a50c28023d50c0056450a008b86420000c49c0190c128058318a00ab8a14010c3e8402f634300318e2600793a4c00010c8400019d3802f80a600c7a108000048c0013c912dec69205008a714c00be8e9802a854200433921005f5f4c00be209801b890e00003aa7005a394a01716e10024e190c9c5321500bc86420158c629c98d50b80454321008a234c0167620c0218050804514a5008a834a0114828400015138050c993, 0x1e97d3005d961100a18a20017af228034b3450049b2180000703c00c6908401e49128031962500b38a4e9a744890018cf52804301a1009e6e1e010cbe800000c580059922f00df641400fe489402e198500666121005f054c0156a6280332cd30000628e0054244a01bcc860036b30c002f9226005f034c0170c6280001cd38066c321634b3d4800f2749002ce4d9005e920c00006e3d26e4c65f8b7a7800024122d005a244a0184c68402f17d30043322100005f560000e29c03a6190800032270064244a01d1848401b54cc00433c25de72632e011ebe98032278200003e270066234c01a448300228d0f802b242100998643633d14040000b98000017b000de864200cc7e940219b10801d042f00b19e08011a4c7002340ce00003fa70000654f1a74486c01a58cc00004ea700c2245a00be2a9801e4c1280454125008f8a4a011af260017c093451d122400b88a1400a66c940001bcf00004323008a364a00be48bc0228dd280004127938f8a2cc6744891c98c91200661225009c8a4a0001424c022891280451a2100c35f4e0167621002d6bc2006ab18a008a494200019c9c000368f0036921c00b31524018f66340001c530000153000ccba4bc5873c12f58c90446c51216007f3a480001989ef6ec90100372d18005f084c00010e9c00017d3005a2fa60086243f271f14576ac678000451aa500d75f4d633c4808017cf53002f86a6008678420114dc6001e4e92804306a100b3a12400c64894000288980319825005a4942007406bc0002fc70045132500ab631401147c9402c57d3000030270000664e01b4487003698cc00319d2600633a4a0132be980228e5280431e9f0000824a01bcbe9800016d3804eb4980066244a0000ae9c02764d08047c32100c28a4200dc926acec67818059d88d00002d6000fe749802852c9802f8fa6004e244a0148c6400234e8e803f9d25008d103801145894000095800007427938a722a0000c29c0110916c9c5181f00925442016714980228d1280433d21005f244a013a6094021a1908058450a00b46e1e00be489000017d3800000330000dc3c01a50c1c02d219080583706005f4b4c010c48b400021910058c321008a784a000074cad6d2c41c6bc9216]
  | 8 => [0xc7be1c7a20c18c1538072b30003676b424c00a583d31a78a8a4e01989d2ca5800452c000f660126cec58d3c031a70086671e04c276293802fa700634fd5149dc98d3805a3347246000c6b001e998020b300006f141a9c90918003c33004c67993c9e3e293da25b3004567633c38010d9ceb1a779244b6b68c800e991206b09324616926cc02f19c51ea73610607448bc01119ef31a700246c0090cd8c9138002339e634e0028cf0c9186f391e0024780072cec05470043219e9366c6049c01593cac5276c24600142cc007d9805e8e009c6600010402019c501a7661f4f14109ef0918001230001e66967ac934913a69225001c66c6969e2815380123100ea660034cf8b0d9802a2763244ae4c698900584509a7000a67bd149ed2293805bb3b39e640116cc02bd9c51825bb24600064ce4e2908003b30022669a069e29c93e7b1a74d024e004cc23c9181e843000c866008ccc02a598024b300635514209c00159bc923063246126e478f40984512308a644e00be98005d9e7c527b19367143e9c00c1831b1a724106000c6fe28c138061b3008a660066cc00259804ea7de246000c6ec02799805333009a660184cc03119f16f1ebd241d6296cd8c413c525a78d243d271e792c918002d27000066014ece3c21845c527008a5514049f0cb1863da8eb415271ec69c01993c781b08a7a4e0114a0028498060b3001266e496c800b19d8cf04c38a4f68c69c907d80052b38a3d4a7a30c2f2293800b33006e3c01149c00d99b186a700006b703e3802cd9370a9e63034f1a48c24c9981201b000534e01563ac49184f4527004b67a99e9d8c7d38009b38a30618f3c39c891846921c8f10600020cc009d9800ab324086000da7800a199202b000da3c0046cc0019980103300248126c69ef490600469e0019660114ff658d3ba31a7b42460004ccf3c9184ea5a7003d66001acc00a59804ab3002466016ccf8b1c7001f33001d66c62a9c02e07318927002c609a109c0045980043300026727149c018d4002133, 0x1e89180065338a634eda20780001a003ca700864f14d89c008598060330030671f149628913d8c527c3634e0018cc02819b631a74d104e008ecc02e998011b263544f3c48c002a19801bb3000b66f2489e792d9d5880e9e1527b53c78006199e9230000e66013ecc02cd9801d330001676b6238e8919001238240260463ec9685538032272415600036ce2891280580e3a24607a06c2291d3805db3008a76c6109d8cf53c50aa753104e007ecd8d1d38058b3bc634e0068cd8cf528075b3]
  | 9 => [0x15663ecc91982b3c366c69c01bda33476610cc09980337a6726cec599eb32461149ef1980348a6620cc01a80410d6696cc0d9cf33]
  | 10 => [0x7f]
  | _ => []

def C13_buckets : Nat → Nat
  | 4 => 1
  | 5 => 12
  | 6 => 59
  | 7 => 117
  | 8 => 81
  | 9 => 7
  | 10 => 1
  | _ => 0

def C13_flag : Nat → Nat
  | 4 => 8
  | 5 => 0x400
  | 6 => 0x1000
  | 7 => 0x1000
  | 8 => 0x1000
  | 9 => 0x800
  | 10 => 2
  | _ => 0

def C13_seedBits : Nat → Nat
  | 4 => 4
  | 5 => 11
  | 6 => 13
  | 7 => 13
  | 8 => 13
  | 9 => 12
  | 10 => 2
  | _ => 0

def C13_seeds : Nat → Nat
  | 4 => 4
  | 5 => 0x52ef80e80a0026e42600f00602c03008
  | 6 => 0x23344b80032c719400ec006011048945a01000c857a1b0005286820e1d800e01b00280020e803a00dc01001103d8010004005005000821e00c0008024052001008012409a0150018056138001000886000e0030010028018080013000e078108
  | 7 => 0xa05200502240060078dac04e106001002c0200013828102346a4300bc6300060420b900041c60e2190800e3100560178100a0402000080040f601e04402a013a00a04f800400600d001834c078041029058e286070058001810a00b06d001407600503381440140c5003800800a02700e002419c03d005000800400801d803c026004001010003200900a002e26a0cd001002c13c03d88141f20f2091003000c016003008807000804c00a000803801c809000400803c02901580060d7
  | 8 => 0x1d0b5842400c020000800400452104a865401650a53c000a2841f2025012000c001006004c00d13a0d5824c162007887004c0a603d001099c2eb0fe000c2ec084077003024409c00a847036c05800d008801000e009017800e10001900401440da00c032025800400380303c000800a081804800203a800015c00203100480040be00a
  | 9 => 0x930077c000200f056011
  | 10 => 2
  | _ => 0

def C13_S (s j : Nat) : List Nat :=
  qDirectStatePattern C13_initial (C13_countBits s) (C13_patternBits s) C13_patterns 15 8 (C13_slots s) C13_values
    (fld ((C13_records s).getD (j / 256) 0) (C13_recordBits s) (j % 256))

def C13_idx : Nat → List Nat → Nat :=
  qIndex C13_N C13_buckets C13_flag C13_seedBits C13_seeds

def C13_routeCodes : Nat := 0x14450000032300000400000000400000000000000000000004000000010000000440000011000000020300000800000000800000000000000000000008000000020000000100000004450000022000000000000000000000000000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000000000
def C13_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C13_rankPool : List Nat := [6577818, 2115707, 4287912, 4341369, 1067678, 4402810, 2121163, 4418727, 4349079, 4263562, 4202121, 4205464, 3239371, 5458590, 4328327, 4397991, 4218264, 3295902, 4275064, 4397959, 4205432]

def C13_rows : List Nat := [44, 52, 74, 82, 97, 104, 112, 3, 5, 9, 17, 6, 34, 68, 24]
def C13_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C13_rows)
def C13_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def C13_ori : List Nat → List Nat := qCompactOrient 4 C13_routeCodes
def C13_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 8) (compactCover 7 8) C13_S C13_N C13_idx C13_ori
    C13_coords 4 C13_rankPool s
def C13_F : Nat → Bool := certAt C13_Z C13_N 11
def C14_initial : List Nat := [0x1e8, 0x252, 0x41a, 0x625, 0x914, 0x101c, 0x1883]

def C14_values : Nat := 0x1ea7e41ea0f3f99ebcf4665f329983c8e64531878a3c40607300163db12d7f2bd141ea0e506a80125290e47f23d111c84e42020b903c8003cd5a3cd145ab2c5132895449a1fb4e4a67732d1948c7e5fa2f4106082441020410088003fa1f40d4848020002000800300120080020004001

def C14_N : Nat → Nat
  | 5 => 4
  | 6 => 27
  | 7 => 53
  | 8 => 30
  | 9 => 1
  | _ => 0

def C14_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C14_slots : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C14_recordBits : Nat → Nat
  | 5 => 21
  | 6 => 28
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C14_records : Nat → List Nat
  | 5 => [0x765e4c07e38032b4eca4a]
  | 6 => [0xecacb00ec74b00f5e0f00f0a5a00d15560084a6a0001dcf00fdb0f011181b00ed6cd0001c1f00f0d47000205e7880c4900cca5a00aca5a000175b00eda4700ed54e00a875a00c0a5a00f05cd01110ab000155e00ed7cb0001f4f00ecc4b]
  | 7 => [0x13df009af806f7c00afa01cbf00ef78088fc030be0067e003bd8021ec03cbe0007f00777bc2b6cc08f2fde4f004bdbc1d6c03d7ef104f007b7806d7d595b600a7e0096f80597d80eb65077a00aaf8039bc021de008fb010dfa41d6d08ed6007fb00e9f8027ed58eb60145f00eef80857e0abbc014df00aaf3b493de18b601dcf00aefbc473c01fdf1073b]
  | 8 => [0xaaaa355550caaa9655544aaaaad15530aaa83555472aaa8155504aaa80556472a8af115500ab2b15554daaaa6555500acaa255562aaaa2155546aaa955555aaaaa1555508aaa8055583aaaa01555]
  | 9 => [0x7f]
  | _ => []

def C14_buckets : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 14
  | 8 => 8
  | 9 => 1
  | _ => 0

def C14_flag : Nat → Nat
  | 5 => 32
  | 6 => 512
  | 7 => 512
  | 8 => 256
  | 9 => 2
  | _ => 0

def C14_seedBits : Nat → Nat
  | 5 => 6
  | 6 => 10
  | 7 => 10
  | 8 => 9
  | 9 => 2
  | _ => 0

def C14_seeds : Nat → Nat
  | 5 => 18
  | 6 => 0x101c0b3fe1383550
  | 7 => 0x801856116760a060e90104302c2102444
  | 8 => 0xe47405100080c36ba
  | 9 => 2
  | _ => 0

def C14_S (s j : Nat) : List Nat :=
  qDirectState C14_initial (C14_countBits s) 13 7 (C14_slots s) C14_values
    (fld ((C14_records s).getD (j / 256) 0) (C14_recordBits s) (j % 256))

def C14_idx : Nat → List Nat → Nat :=
  qIndex C14_N C14_buckets C14_flag C14_seedBits C14_seeds

def C14_routeCodes : Nat := 0x40000032200000500000000400000000000000000000004000000010000000004000000000000000000000000000000000000000000000000000000000000000000000000
def C14_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def C14_rankPool : List Nat := [3295589, 3230567, 2111611, 1063529, 3279704, 4397928, 3157079, 4401494, 3152229, 3213654]

def C14_rows : List Nat := [10, 44, 82, 97, 116, 3, 5, 9, 17, 6, 34, 24, 72]
def C14_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C14_rows)
def C14_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)
def C14_ori : List Nat → List Nat := qCompactOrient 2 C14_routeCodes
def C14_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 5 8) (compactCover 5 8) C14_S C14_N C14_idx C14_ori
    C14_coords 4 C14_rankPool s
def C14_F : Nat → Bool := certAt C14_Z C14_N 10
def C15_initial : List Nat := [0xf09, 0x12a6, 0x3150, 0x4432, 0x48c4, 0x80f8, 0xa007]

def C15_values : Nat := 0xf6b7f5faf577f572f1f8f150ef3fecf7e8c7e8c4e807e800e4ffe437e432e407e007e000d6fecffbccfec8fcc8f8c8c4c800c4fac4f8c432c0f8c000bff9bfafbf5fbf59bf09b5f8b550b3feb3f8b3f7b3f6b3a6b350b2ffb2a7b2a6b207b200b1ffb1f8b1f0b170b158b157b150b107b100b0f8b0a0b007b000afffaf0faf09ac07a607a507a407a400a307a207a200a1f8a108a107a100a0ffa0f8a0a7a057a037a030a027a017a00fa006a002a001a0009fff92fe92f892a6920091f890f890008ff98f098cf886f885f884f8840083f882f8820081f8810080fe80fa80f980f080c080b080a880a08070805880508038803080208010800880068002800180007f7b7df67d5079d4795078c477f675727550715069c468c464325fbf5ef65ea65ae65ac45aa659c458c456b656a65632543252a64fff4fcd4f3b4f094ec44dc44cf64cc44c324c004bc44ac449c448004632453244f244b644b24472443a4436443344304422441044024400403040224010400240003fff3f593f093d503750355033f633a6335032a631f0317231703158315631523151310030002f0921002050201020062002200120001faf1f091ea617a616a613a612f612b612ae12a712a0122212061200110010a0105010221010100610000fa90f590f390f2b0f190f0f0f0b0c00060005000430042204100408040204010400030002a0022202080206020102000150011001080101010000f000b000a800a600a200a00070005800500038003200300026002200200012001000090008000700060003000200010000

def C15_patterns : Nat := 0x95561558515955565556555655565555554554555055155445505540545551454455055155454514544550554145045405465518545951594559155455115145411494519145451114144550554151051411501515545541544545145445510541950594159055815505501510514055

def C15_N : Nat → Nat
  | 4 => 1
  | 5 => 40
  | 6 => 222
  | 7 => 488
  | 8 => 406
  | 9 => 41
  | 10 => 1
  | _ => 0

def C15_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C15_patternBits : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 0

def C15_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C15_recordBits : Nat → Nat
  | 4 => 25
  | 5 => 34
  | 6 => 34
  | 7 => 33
  | 8 => 24
  | 9 => 15
  | 10 => 6
  | _ => 0

def C15_records : Nat → List Nat
  | 4 => [0x1007d18]
  | 5 => [0x85b00ba30009242648cc51d80d94844086003e9cc6616ec718a8cc51ea15446430187abb1806000f5719c0027d098a331471868cbd5d82632f5718c0038d8c7232ec718a7abb1c66000f87b1976300ba6000f5761965180946217072e85762110309d8c6299800401d8680000751b003d5807000008b8f00465c639ecec3e09003e5d86616f5760900001e67401198a07003b1c66a170729867638d8c6000e630190042dc63801114087]
  | 6 => [0x76391826801184eab003b18168009d426a00328f63c00f5719d00002227c0114719e763918c64010b650f00001947c00ec739b003b1cc6decec641985c1dec1c00ca4c1b7b3b0c06625064087003b1012c01198a4785b19813000a2321e003b0f92c01198a2700001cc7decec601a76318986400ca1f1d00288be7580a22e9c76391806a16c0260e0042dd92c00ec4b4b44211039000ca299e003b0a76800f5761b003b08d6400006f1f00449d86c00e3651e00210ff9800ca3e0f0024095b1d8ca601a0039cf8b594601b99003298079e2e730197b3b03e65228c426400210fd99d8e4329a78980956000ec719e003b10969ecec4619003b11b2e1707260700281099a249e4d2300288aa6c00ec3653003292c3d308840e1003d5c670008f426c0032910758cc0261c003287a6c00ca400f00328c26c01198a0f7abc5c67000ec721b8cc51941c008430f200001ae7c00ec681b512592a1c006724e500465c6b8007a30e378bb5c668007a23e500190c1e000a2299e003288e740000854f003b1966e16a22e8d003b08f65d8c0261a00241159400ec2ed90042e0f1deaf1769900319817217077207003b09569445d299c65204ce1c008423f4003291a3c00f6761b003b0f72decc6601c003b1c66c00007f5b85bb18d25c8c6609c78a1103193c9a446185a88a63930914661003b1a86c0103761b7d3d9d8640119718e7b3b18c6400ca209d00328ba7400ca251e003c5d66dd8ca631976288ba6400ec6c1b763198162170760468cbd594340000765b00288ba75ecc8601c85bb1812800ec71da51211031800ec719a76288a669c8c6601c003d0bce400ec651b8cb8d943800007c5b85bd9d82c007c256c00462183deaec6519003d5c6f216f6600e78bb1c66800f65c1d7abb144640119718f003b1be6c00ca3617003d5447616ec720b003d120b5eaf176194c211038800ca231d003b19a6e32ec650b003b19c6c00f5651d80bb1c868005e257800415031c00f5719e85b918038011971ce7ab8d9471d8e3511a003298c7400ec6b9b003d5d86400e72f3900001b67c00ec71ba003b1b86c00ca421e85c1dd90c00e3511e7638d94680119764b003d5c77001198a070019cc78e16e4608e00328bc6d4496298e00000fd9e3314788783211031800f5765985c1d8d1632f1718e51258ba35eca22f190024d099800f4639d4f269098800ec1f59003b1986c010b604e003d5d87400008edb63288a67000f5763976204cf0e16ec650b003b18d66248440a6000018b7544602a197b288f8340119650f002751fa4008440e689261028c00ec4459]
  | 7 => [0x22109a001d8c0c800007e3c006500c489204ce480000ab7800c3253a0085bc540039d442001086cb800f1603a005114847b3b144080206a210000045ea007ab28d0032902200000e23c00f12c30008f2618001f06f4801ecec621707512000003b19003280a2001ecc03800a229860085b1a90000001b801d8606000a246a80085c1d4001f0974801d84b60000063bc653012f0002888ee001e27b50004a0fe8e460a88300001943801b87c2800ec0fb0006507c400001c27801944b1000fd6508000018f3003b1c82001d8656000a2423a006ab284003b06ec00000aa780000623c000018b3003b098c001d8e40400f14b2800652144001fccf3a89026740000041d6007b2e5c8cbc5940000006ebc00003e560000421e00200c3400001123c00b7233800723284001f0bd4001868d50000082bc0000303672301441801b8a21000a033ce003e1e6700001319801ec7ca4007b23520078929d000017af00000b278010b7214008cbc540023513380000d57800f56508984099e4003b102c00000ecf60c8133a00085b0137b28918142d80a24d228c33ca005c9f1400001d678000088d4011565080065030400001e0f00000eccc0106423a0082328400328122000005dd4010976300063303476329440801d81a6000005cbc004b2567003c5be23d9446008000068bc000032cf004493c500000ca200084135c0076269878a04ce800194011000ec6338000032850044a0c200000ca7800e454880078a21c000023cf00000b67800ca1e08a2299303003616e20010047a400ca338800431fe700279114801b07b2800005dbc007632180017897880224883400c6603800250fb444204cf28020c88700000743c00650084000016ef00000c278000036de008326180042e0e821102679800ca1b880078a01400001fef000ba53d1d8a22602007ab2820038d94200224f11000b73da8002f0fb172288ca1c2dc8a20000ec55b08642a0660042d44a001ce8d2800f176b00076bb1800000bd9801b0a210000085d600760318003b002c001166cb4008523da00001f6b789806eb00180a67400ec0730004b176900245095001e2417000a2402800511ed4003b18cb3c5dae404008133ce00511344003c530c3d5e2ca0800a22f30000025ab00000e1780000c378000078bc0076015800001339801d8ca1000ec63300073b0c47631944b3d980a20c0108362a0051221c002e4bcc288ba4c080000326cc660289b00288a82000ce61b000f12eb80065328400288ba68000041d400f123b8003d09a700001d8f001941a1000a22e88005113040031c7ce001f85e60010b7622005113c4003b022c0000061cc01196500008a328400449442001d8ca05d8e451020076215800288bae00000ec6800005fbc007ab29c00001dcf001326cb0010b762800788f58003d07c6801b04634000046d600338be7003b5942001ce603400a23e2800002f9e, 0x204d93801940710000071ec0080bb18001ecf13801a0a210000023ea0000299e00391442000c247c400df401400722ac40000194200000cc3c0109650800002b5e7b2883e100108819800ca6408007895980037cc26000007bac00f16c08005117420039d1868019ca210000040560076301d0037c8e68020ec074008440ce0084b01d0000091a80216c150000029ec007601d80000093a80194261000004bd600001b2f003b18d8801d8d66216a226000051185800328382001d8e46001077630000037cf0031980d80000e97800007aea007b32840037d44200144986000006e9e00789f14002892ca3c5d8ca0400f16688007b17b10044930627934679001196514004f1b27003915c2301444c0c00ca2608006a975c0000095b001d81460006723dae46328820030144e8011a8ca400ec33b000763b18002887ce001bebc10008440d400788f9c000019a7801d8ca31d8c0512e00789b15003552ca00000dc3c00004e5600002b1e003fcc2c00194651000984462008abb1800214c363c5c6ca0c00901f52005e1858000015ef00217095000f163380085b014003c4aec0000046d400f12338000015730000226780000ec6000f16e08007b29840024ccf38018ca270010b83ce004f212a00328222001444a75ecc651040064301d0044cd85800c04ad00000426d0b76289100351442001e2e374000054bc005e2014000011d580000ca1800f130b00000365e6328898100144533a16c65124005114dd003195ce00000ef7800f1763000002a1e001786f880000d83c008c2568004692aa0000160f00216c0a800fa76310b7b288000354a6e80000da7800ca0a080063305c0038d94700000b8780000206a006e2e44002888ce00001067800a22708007894dd0047dd8c001d8c06000f173880078b284003b180b80000ec8800ec6530005114c4003d9d8600000c6d400ec1330007b3b01003d95623d990a2080000701e007387cd00485942001d88c6000001f6a0078979800258a75000005fd40000651e0076390c0042d62a001ecec100119652800650384003b144c001d8c16000c6603a00489b27000007fa801acca1000007a1e007abc5c003d9442001e4ca1000ca3008007600980038d94e80194a2100000415600001bef003b006c00000a778000048560072318d00180a98801e2cb100000573c0071b28300329822001e2cc10009842640000289e00370bc6001446c5400bc23b8f176b281003c51aa001d809600080364e004c24680032918200216eca00000739e0000466b00449087001949a1000e7251c00002f1e51258980001e28475ecf1768200002e9e]
  | 8 => [0x3b33002f3778a69e51181e51045e7880de8919cf4899eb000e3700003b0017b378a15e000cb70009b74321760028a17b289e00289f51005e003c6160a89e3089b3000b3760289d00328f0030f700053700023778815e4d1973000af778899e72289e003c604f26b300299e5c87de0012b648a3350031b5000cf751009e7b2b9e000937000eb78319de0043f700236b7b23350030de00329e0008b7722884001877788f1e001ab70006770014770028b7510dde003937618dde0007f700419e0028f78d454f78869e0011b5000a376328b578851e002af78aa89e2306b5000977000fb70034f700073776289e72197600355e0015376a931e7628b360289e003db70013f7001e77002ade002d3778a05e002a773389af0012f751215e002637738dcf000bb78d436b0013b76028b678995e8aaa5e00289e0005b7002235000b770006370037370024f70013778ab90f003c7e002337300df52e933551051e003284004837000437000137001eeb001b3751269e78b59e001df70039cf0039f7000f377b3235001775003c7700202b0045b77887de90bc5e4c19f37899de4612f53d86ab0037f70041b7002d770006b7002dde4219f643206b0004b70025375100de000a770039770033b7000db7002cf7000f77003237001777002a5e001f2b002e77003df778b91e32983378981e7b3c5e0028be0000f778bb5e7b288f001c7751131e0002b700223700427778931e000038002177001a77000c370016b73e07eb000bf70011370029b70011f700448f000ef7000df7003b180046f70004f76b289e000d770002f7000e770008370030774f21ab0025ab0037cf0003f700370f00287751025e63289e78b2840017370005f70025770019f75e099e7ebc5e6f898f0021365b869e0005774099e7002f1e8abc5e0001b7002837004737003b1e0003370028a37b28842f07f3723076431b2f83a89e00457700363700303600183778b21e7892de003f777881de51015e0006f70008770001775112de0017b70003b778a31e0000370033f70021376e07cf78b05e84a89e6c068f00297751099e, 0xab785a89451031e0032b7003c5f78bb5872288f00163700487776aade78871e0001f7003277001177003b7751289e0048b74b132b0026b778a89e823c5e64305e0042eb51195e000fb551231e0013370021f748a1ab0016770015f784bc5e0019770002770040f700047700360f4f19eb460df55107de00263384b05e003c630040b77b3b4f0014374099eb4f246b001db74419f50007b70035370020770034b70007771b87f5001cf785a8ab0000b700007778839e0044b70028a04009ab86c25e5101de63289c0010f75119de001b2f001af700187378bc5e0035b776289878bb730041f70043b776a89e003ef7001e3700003f001a377b07f5001cb7003577000c770011f5003b3700003a788dde2389b50014b72993364289af51130f3012f551130400037778b29e000d370026f751205e002e5e0029377b18350015b78d27ab0041377b390f0014f70010b70019b7002df70011b72587f572299e003c5e0009f7468deb51039e000039002b9e00003c793c5e78825e002bb776b90f00343751069e78845e0008f700227778831e001ff70031b7250df600303778809e64289e0014f63292f6001d770016f70012b7003cb7001d37328fb578b28f004437]
  | 9 => [0x3c777b6ee4ddadba6b703ee00e01dbc57725eea2dd19b86b7007409dc01f87f70a6e26dc01ca89e02ee37dc99bc27776eec8dccfb803b08eef17819bb077006e81dc01e00f742ee65dc05b9837]
  | 10 => [0x37]
  | _ => []

def C15_buckets : Nat → Nat
  | 4 => 1
  | 5 => 10
  | 6 => 56
  | 7 => 122
  | 8 => 102
  | 9 => 11
  | 10 => 1
  | _ => 0

def C15_flag : Nat → Nat
  | 4 => 2
  | 5 => 0x1000
  | 6 => 0x2000
  | 7 => 0x800
  | 8 => 0x1000
  | 9 => 256
  | 10 => 2
  | _ => 0

def C15_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 13
  | 6 => 14
  | 7 => 12
  | 8 => 13
  | 9 => 9
  | 10 => 2
  | _ => 0

def C15_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x19d831300081e40020122920008002019
  | 6 => 0xd16482e45fd035834a01e004808b800d006800a0ae448901e803400080060008026002402900c00a5001826a010005801c400302da03a02cc0480004059000402c00a8003801400103140080004001013c01700b80310054007039400f0020018
  | 7 => 0x62f24320129dd0be03816a01c00300611c0500be9d60130d31940460439a723600204f02e0050240672a71ec05002703312010d00199a00163708a93600211f00300103e0420061749e800507b91500101000201204f02f05a00190100d0018e600200c06509700c8c60012f39e802b0610698ad87e0070ba03307900103704401309308603b02306d00a01806e0190dc0051d202300100306500f00884f9e800316502002406302510a02984c08081000e007801046
  | 8 => 0x213261880302da33d084801c0ce00406d929012717b0ee008c0d2224092007803315a00080500043510d400b40f601403c006c00200308943d4086022103823401006919682307f40df006001801001800b024409e1050a5009000c001050c3940020c3004807400800a002800e1c000100600b407604c06b00580a200f00e000c0170be0010014040001007c2d404404100700040ca00d035001414e04c025c11e082002
  | 9 => 0x968026e81852cd8dc380427
  | 10 => 2
  | _ => 0

def C15_S (s j : Nat) : List Nat :=
  qDirectStatePattern C15_initial (C15_countBits s) (C15_patternBits s) C15_patterns 16 9 (C15_slots s) C15_values
    (fld ((C15_records s).getD (j / 256) 0) (C15_recordBits s) (j % 256))

def C15_idx : Nat → List Nat → Nat :=
  qIndex C15_N C15_buckets C15_flag C15_seedBits C15_seeds

def C15_routeCodes : Nat := 0x4040000003200000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000
def C15_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C15_rankPool : List Nat := [2165678, 6519960, 1068169, 4284365, 2104987, 6622620, 4419210, 1060538, 4210573, 6455245, 7367817, 6311563, 4201624, 4340654, 7556265, 7616908, 4414616]

def C15_rows : List Nat := [33, 44, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 6, 34, 24, 96]
def C15_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C15_rows)
def C15_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)
def C15_ori : List Nat → List Nat := qCompactOrient 2 C15_routeCodes
def C15_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 8) (compactCover 8 8) C15_S C15_N C15_idx C15_ori
    C15_coords 4 C15_rankPool s
def C15_F : Nat → Bool := certAt C15_Z C15_N 11
def C16_initial : List Nat := [0x235, 0x3ca, 0x4a4, 0xc51, 0x1105, 0x2806, 0x3038]

def C16_values : Nat := 0xf1e7907e0fb838e01b4bcd0e33fac8f7238c4f7138c4170b8c1e3000b29ac57b146c06af3aa37a81a906a21a846a0024a48f2a2358001f757555c5164157b5569550552913cf4f293854d153354c15235461514544010003f6cf513bd4ed139d4e513544cf53344ca42f28a3520007ee1f287a41b906b51a9063516904e412004000ffc3350c002b50a002750900230089021108142040800100020004000c00240080011004000800140040008001

def C16_N : Nat → Nat
  | 6 => 24
  | 7 => 78
  | 8 => 51
  | 9 => 1
  | _ => 0

def C16_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C16_slots : Nat → Nat
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C16_recordBits : Nat → Nat
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C16_records : Nat → List Nat
  | 6 => [0xb681d4e5b5adad6c016f6708350077b9221f0017f6c0e672d41c8031ec0117a78e760041e9c2dcd3905a008fd5b70b803add55cae9ce275b9c7a8a1b401c6e]
  | 7 => [0x20fc023fe0159fce1d78017fc84dfa0136fbd73b8010fc01aef00db7801df80557e00e7b00abb8023f8020f402c6f5a3bb0031f804ebe010fe0053f0085bc052eec9776004bf6373b8034de024fb00b7f001ff8043ee00b7e0057f3967b801ffc013fe00bbf00c17c02cee030bf00fbd808bf8037fc01c6f00a3edb1cf803cfa0265f0107f00977d2a1f401cfea887d0049f405e7e0255f00b7b201de803fde02dbf0146f805bdc013fc00efb00c3f00aefc038dc01c7e0123e8041ec019fc00f7b00a7d80b2fdc0edc0007f]
  | 8 => [0x5d555572aa91155504aaadf5555caaaae555400aca80559432aab91555a0aaaae555532aaa855547aaaad4555712aaa2155556aaa8095541aaaa0195512aaada555402cab7155502aaa8a555472aa86d55534aaac0555402aad3d555c6aaab3555462aaa0155916aaa85555422aaa355554aaaa87555592aaa8555500aaac655569aaaa39555]
  | 9 => [0x7f]
  | _ => []

def C16_buckets : Nat → Nat
  | 6 => 6
  | 7 => 20
  | 8 => 13
  | 9 => 1
  | _ => 0

def C16_flag : Nat → Nat
  | 6 => 0x1000
  | 7 => 0x800
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C16_seedBits : Nat → Nat
  | 6 => 13
  | 7 => 12
  | 8 => 12
  | 9 => 2
  | _ => 0

def C16_seeds : Nat → Nat
  | 6 => 0x1e420228048104002007
  | 7 => 0x7d435901884984e0d500300507c01000100f00300100180005309f017007
  | 8 => 0x63900607501300925609301800100900f82b023
  | 9 => 2
  | _ => 0

def C16_S (s j : Nat) : List Nat :=
  qDirectState C16_initial (C16_countBits s) 14 7 (C16_slots s) C16_values
    (fld ((C16_records s).getD (j / 256) 0) (C16_recordBits s) (j % 256))

def C16_idx : Nat → List Nat → Nat :=
  qIndex C16_N C16_buckets C16_flag C16_seedBits C16_seeds

def C16_routeCodes : Nat := 0x0
def C16_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13]
def C16_rankPool : List Nat := [5376940, 4413814, 3284107, 5458279, 5511017]

def C16_rows : List Nat := [26, 33, 60, 65, 82, 84, 3, 5, 9, 17, 6, 34, 72, 96]
def C16_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C16_rows)
def C16_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C16_ori : List Nat → List Nat := qCompactOrient 1 C16_routeCodes
def C16_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 6 8) (compactCover 6 8) C16_S C16_N C16_idx C16_ori
    C16_coords 4 C16_rankPool s
def C16_F : Nat → Bool := certAt C16_Z C16_N 10
def C17_initial : List Nat := [0x8db, 0xf24, 0x1149, 0x1292, 0x6403, 0xa01c, 0xc0e0]

def C17_values : Nat := 0xf55ff1fdeffcef3fef24ecdfecdbec1fec03e8ffe4ffe4e3e4e0e41fe41ce403e400e0fce0e0e01ce000d2f2d2e0d292d1e9d1e0d149d0e0cfe4cf24cce0cae0c9e0c8fbc8e0c8dbc800c5e0c4e0c3e0c2e0c1e0c000bf7dba9eb9dfb3dfb29eb292b21cb15db01cafffaf3caf24ac1ca91ca8dfa8dba81ca41ca11ca0dca05da05ca03ca01fa01da018a008a004a0009adb9a9299db929291498f2488db880080188008800480007fdb7f6f7f037edb7e937e037ddb7d4b7cdb7c0377db770376937603754b7503740372926fff6f276f246f036e036ddb6d036cdb6c4b6c1b6c0368db670366036503644b641b640b6407640060003adb3a9239db3692329231492f242cdb2c1828db280024002018200820042003200120001fff1fb61f921f6d1f491f241f001edb1e921ddb1d491bdb1b921b491b001adb1a921a0019db19921959194b194918db180017921692154913db1392134913001296120011db1159114d114b11081101110010491008100110000fff0f6d0f3c0f2c0f270f250f000ddb0d000cdb0c490c000bdb0b0009db09180903090008df08d80859084b0849081b0818080808040803080108000500040404030401040003000149010801040101010000db00d80059004b004900480024001c001b0018000c000900080004000300010000

def C17_patterns : Nat := 0x65559546451854595565458515655591559556155655555545545550551554455055245461515545151154415055411501519145851554545145450511541550514054555154454511541550541554554154454514545141414455115015505501510454055

def C17_N : Nat → Nat
  | 4 => 3
  | 5 => 30
  | 6 => 167
  | 7 => 412
  | 8 => 337
  | 9 => 33
  | 10 => 1
  | _ => 0

def C17_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C17_patternBits : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 0

def C17_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C17_recordBits : Nat → Nat
  | 4 => 23
  | 5 => 31
  | 6 => 31
  | 7 => 30
  | 8 => 22
  | 9 => 14
  | 10 => 6
  | _ => 0

def C17_records : Nat → List Nat
  | 4 => [0x13cc583c3b860030f0]
  | 5 => [0x24d895706f61aa92d9905c440140c5c0022cef10023197084624bc001ddc03800ecd38003331f0d9625c6001147f8801896b8004ab161a18c87180114c5937a4d55100002cf200625ce00136c59205895706543b98ce5e3570d20c4b98003c39468000720f006259e001c10e3b67057090076718e]
  | 6 => [0xb6a3c98960ff86ce0ac16844b3bc40108bf98035221750c3bd0e008c87d800c491c4035f45e00692bb6005749e40000bfd80211cf600312bf4e5e3a61dc743083b65892d880695c9e949262c3b2b876c802216f30079728f66645ce001027f8c029d5fa000045ee0000abec0100af980228ef369422ba6008162ca01cbc63f8ea69ca804eb17400ad57ac01089b9b978e1c700312e7490624bc201acbed989604b800422566005f5de4014077c802b6127003124f100005bec008c59c801d54790049b165ca87681c00b67fc803516db72f18e8ed96258680102af9b62fe98e0050c61d000065edb382964e1d892f800002b76008a57ccc4b897c0000380fc0aa9de200e2845c00ae7fcbbb978c70072f00f845751c5cbc6aa3803978478031167800cc576db6b07ec803975d680332d72000088dc0114cd980329b87802e1df2006432f000aea3c8035a11700312c74e7877399a57308380188a7c72f1d38de9e1871c01087fa80274ff90050bd8f905c3bc401a508bb8e855cb0067422e008475cc019708b9896157800312e72000084dc014f09b00160ff9695cab96003b2de40194e67403655db48ac1fe2624b1de1c74f4c7189552f80000683e005c3fe400c4b9c366524918071d29e007357e8c4a097c003955f30054c26600dec32e00c4b9c403895db0054a8f2e5d8bf1a01cae734000123980482be600d9845dcbc7521c015d339692ba8b2004629e4019caed8035af4f006f49a7003b2ee40001d9b80208ef1806aabb6008457cd28c4abc362fea4a806eebb500e9e61e00c4add241896326cc82c26000057ec000069f18970ef8003125f1e3a9a82601a9787802118b6312e2af0d9904b4600b477c803776998065abb6009662e20000f1d8013d2f900004bee]
  | 7 => [0x57058c0001dec0000e83400013ec00a9a68c0211a1a00e27030029e1ea00e7578c01d562300baad480160fe3000026b00002a64009055680128b23008d846b8ea684100002bb0015c22300584d8f8e9a8430062588803b611a00d284140274ee300aca98c015cea3000032b000014ec00d42930015c7630058578c021df1a00e2ad1002fab510000beac0389d4900c5578c000232b005c3b7c012cfe000e3a110035154c00bb578c00015e40000a7ac00036cdd2571d200001da4000030b00001ceb00005f8c02115d500005b90032edc400a9588c00ec5e000a9878c024141a00a755a80001edb008762a802b555200840168000211d0084086802c21d2e3a1550c02107da006255a8000245b0000cb3402a55634b3b1d7c02355e300002ab0015c62300d255338e8474300b98468038e11a009c578c00021ec0000af4c033874c00584a8c032e1cc00573b8c00007ac00878468021035a0057018c038a1cce3a7a10802a6a2000d8a632fe361d80057558c0000b6c0066578c02fe11a005751800285e8400c8578c0329a0400804a597154edf00554a8c016ca6300d257240001029000054b0021dcea000033b0038d5e3000057940285cd1000086b00154f680000e234034944c00493b80000348d00d8a92400017ac009462880366509000098b3652cec7504b3b7c03664060000d6374a1074500604d8f978e84000731da803661cc00e5e310036540c0075558c02a69e200963b80000338d0090876800015e300841d68015c4a3005c578c01440a800841868020599600cb8018020155a00875f8c000241b00d62f30000221b00e7846803969d900cb4a24036588b000021b000018ab00665c8e5248ed400d2843003978c6009a8d6800015f300d91d3001a15e300e255300154fe80084516a412ced400e76e3c0000b2c00e5683c01444a800843b6801d5c230000ad4c000211b000029b00199623000071b0034ae4c0084846801892e0008403699960fdf00a91d8c0189623003b29a0000106900e1a11001611e3000027b000008ec0000ae4c000156c006250a800ecb28666458840190b2800ce5530022155a00d2bb30000201b00bb846803495c800e77344020075a00e5ad3c021d2a300005cb00160fe000554d8f62fe842006649800312b500000e56c00fc7680057038c0204ed600574b8c0000fe9005b558d6154edf0000b04c000211c00a1578c01d5ce200ce31325154edf00d21d3002e489200624b7801884a700583fa000016ac00d9c110021d363004a3f8000015f700ce8730024075a000022b001d5d2000845568034a1cc624b3b78000334d000089b00389ccb, 0xcb2c338e861c300008468021d5e300006fb0017cbe3000050b0015d4630084575ba79f8c00000886802b61d200a7a6a8039475a000099b0021191a90583b54036cfca00624b880160fdf57511d7c00016e300e5876960ec49f00928468000092c00e5e30003bb95a00461280038874c005129a000033cd00943f8199912de00ce4d240396a56000052b0018876a00d8ad10000282c00989068035a1cc0094578c000216c00001fb00190a68000084d801915e300553ea0012cee00000a5b002759a30079758c000209b0057517c01287630000a6b0026611a000025b0021e01a00e555680001c2c0000bab00000bec0057578c0144168008d8768021cfe800882968029c76a000000b400020ec00877a68000076c0057048c000364d000072b000017e400842f68028611a004d318c01712a300553ca0015c0a300751d8c018962100d2b91003095e3554b3b7c0002aac00bf578c02115e300f2a110000222c0046248c0001d6400623f9c0135320007355a80000c6c00c28468014492884571d54015c36300510da001cdc2a00004d91712cedf00583b8c00012a400802c68000212cd2b91d0c022601a0092578d8960ee100008f90021049a0000eeb0039699a00005db002e55e300e3ad10000146c00e5d8180170ee000840468032d54c00ceb81002b47520087758c0170ee300002eb0021015a00d2841a1d2cedf004d1d8c00031240000d43402418990084026b6560ec800cb1d339e1da0e00843a6800013a4005c3ea0033154c00d2b90c03a784400d9553000015e60081556800026ac00844b680244fd7]
  | 8 => [0x9b401b6d008db61c36c008eb40242d00b5b66956c943b9001ced681db000fed8d1fb00286d009ab0024ad0000c0012a40069b40036d0070b4001ad0087c61d92c9255b000c6dce18340056d00a6b55c7640037b52cee000806e1d2ec0096b64a1ec1d05b07462c00a8b4000ed0043b400dad00e7b40146d00b4b401574001db001d64903b6dcda2b5508b15476c001ab6fc8ac00c7b55462c5502b25156c0087b78c76c000bb6361da00578f16524bb55b001ceb0013b401631a1684f6284d6664aea686400b7b402b6d00b9b6361ec00579001ead841d6f4874d6455b19092c921db0038ed8d1db00211a007cb554eec8705b188eebc21db0019ed0044b61d56c000eb4030ad0087bc021f8001dbc01b2d873ab00022d0039b77f70d00a6b21cbec1d0db00012d0017b401f6d002cb401aed1d12b19076c9a87b002ced0005b68476c0000c800a6dc755b00142dbf87b1600ac3a1db000d6d0011b6519a40087d00132d1d1db000fe98e87b002b53d8d33402eedbf55b1992e4004bb5c1a2c005cb37360d5555b003aed0019b65249b0049b4008ad00a7ae1ceec00c6b54476ce3a1131556c00efb40062d0002b40082d66588c02dad550db00212c1d08b001fed0010b402cad5529b1540ec00906c0212d3b1db00386d00d2356156c00a3b4005ade387b140eec001fb160ee40055c5346242c12b37f164583b8c0092c571d8c0395b00a2b400a6c0070b00302d006ab401fad3b12a40172d006eb79c76c003ab40364d0050b000e2d0014b6e476c001dd23556c8d876d544ac0055e0032cde9e76e1c76c001fb40092dd93b34027ed5c4bb12c76c8768b000039e2683400b2c1d01b0018ad0087b21db6cbf1db30956c841d6a1076c0064b7a6b537568912cee4e787b003cad928d6fa78cd0051b0740acc287b29e86b00bfb59956c003eb61c0ece3a1374874ca187b21c62c583eb00006de5a16c0388d8787b002c6d, 0x1ed6755b1552ec0080b402e2da6a1b00156d001bb403d2d0042b6fe36b002fb39da1300f1b400771003db6ec76cd3bbb0c462c001cb57156c00c1b79d56c00e5b40002ed8bfac03aad8712b0008ac0012b4740ec00c9b40003500a7b40338d4a1292ee1ec00a9920049b0028b40156c000fb40076d001de15416c003cb400bed0074b5904a90055be1c0ac0045b5996248708b000eed0062ad604ac000ab72c48de9d8356016ce355b00292d553ab00032d00f3b400c6c9a92b21c12c5504b1a156c009ab40002d663fa40211bef87b001a2d004d907412c580db28556c]
  | 9 => [0x21ec3bb462d00b8030e7b70ad55b78ed00d64ad12b436d00c9a2d03b686d3ab412d00e476c1db6eed87b636d02b416d08b52ed64b556cbfb402d]
  | 10 => [0x2d]
  | _ => []

def C17_buckets : Nat → Nat
  | 4 => 1
  | 5 => 8
  | 6 => 42
  | 7 => 103
  | 8 => 85
  | 9 => 9
  | 10 => 1
  | _ => 0

def C17_flag : Nat → Nat
  | 4 => 4
  | 5 => 512
  | 6 => 0x800
  | 7 => 0x2000
  | 8 => 0x400
  | 9 => 256
  | 10 => 2
  | _ => 0

def C17_seedBits : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 12
  | 7 => 14
  | 8 => 11
  | 9 => 9
  | 10 => 2
  | _ => 0

def C17_seeds : Nat → Nat
  | 4 => 1
  | 5 => 0xa8c4004fa005940061e
  | 6 => 0x908971a70a301d60900206300c00e4101bd03407c86f0de00e0010060a58570050030010738a70060020170010451a081c28b00426a05d023021003016012
  | 7 => 0x228600f7c1520005007215900300ff00e003d011a19c062046000411f885601fd002a0ec110000107944ca867000500040f500b83c31c3400c001c41c00201a700b8061837e19c000c01d000c001004c001122c00100200040188081001c003867004a026800214be05f125000804d400100e00010204001000403a02ec0dc000402e811c074011000602980520074003000809901d006e00b01bb00500de001a033020c01607880b8000804b000601b0024003
  | 8 => 0x2e04a1381454561809817019058bac0c80809a1a06214001e2bc0203c2100f800d3f07a0052f8030f612ce480206824c0406e0a801c0201306a01024005146006a8818a5a4001182300200c07cb90075441087d06607cc201b0020042f01b0021103883000200811cb800a014028038ca02408c27
  | 9 => 0xcf040086c35070041301
  | 10 => 2
  | _ => 0

def C17_S (s j : Nat) : List Nat :=
  qDirectStatePattern C17_initial (C17_countBits s) (C17_patternBits s) C17_patterns 16 8 (C17_slots s) C17_values
    (fld ((C17_records s).getD (j / 256) 0) (C17_recordBits s) (j % 256))

def C17_idx : Nat → List Nat → Nat :=
  qIndex C17_N C17_buckets C17_flag C17_seedBits C17_seeds

def C17_routeCodes : Nat := 0x4115000020100000000c00000000000000000000000000000000000000200000404000000151000000200000000800000000000000000000000000000000000000200000001000004054000020100000000c000000000000000000000000000000000000002000004000000000000000000000000000000000000000000000000000000000000000000000000000
def C17_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C17_rankPool : List Nat := [6491871, 6651032, 2112954, 7547276, 7695545, 5255086, 5271178, 2195437, 4340873, 2182554, 7426014, 2187181, 5340826, 3296408, 5250216]

def C17_rows : List Nat := [26, 28, 33, 50, 52, 65, 82, 84, 3, 5, 9, 17, 6, 40, 72, 96]
def C17_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C17_rows)
def C17_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C17_ori : List Nat → List Nat := qCompactOrient 4 C17_routeCodes
def C17_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 8) (compactCover 8 8) C17_S C17_N C17_idx C17_ori
    C17_coords 4 C17_rankPool s
def C17_F : Nat → Bool := certAt C17_Z C17_N 11
def C18_initial : List Nat := [0xf24, 0x1149, 0x1292, 0x24c3, 0x481b, 0xa01c, 0xc0e0]

def C18_values : Nat := 0xf5ebf1fdeffcef3fecdfe81fe81ce81be800e4ffe4e3e4e0e0fce0e0e01ce000d2f2d2e0d292d1e9d1e0d149d0e0cfe4cf24cce0c9e0c8fbc8e0c81bc800c5e0c4e0c3e0c1e0c000bf7db5dfb3dfb29eb292b21cb15db01cafffaf3caf24a81ca4dfa4c3a41ca11ca0dca05da05ca03ca01fa01da018a008a004a000929291498f2480188008800480007ddb6fff6cdb6c1b681b64c35b1b5a9b5a925a1b595b5949591b581b52924f3f4f244d1b4c1b4b1b4a1b491b3fef37db36d3369235cb34c3329231492fe72f242cc325c324e324db24cb24c724c024412403240020c02041201820082004200320001fff1fb61f6d1f241e9217921692154913db1392134913001200115b1159114d114b1109110811001009100810000f3c0f2d0f2c0f270c00050004c00441042004040403040003000109010801040100004900480024001c001b00190018000c000b000900080004000300010000

def C18_patterns : Nat := 0x1955565555955595555551551551554154554554554555

def C18_N : Nat → Nat
  | 5 => 4
  | 6 => 43
  | 7 => 138
  | 8 => 180
  | 9 => 25
  | 10 => 1
  | _ => 0

def C18_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C18_patternBits : Nat → Nat
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | _ => 0

def C18_slots : Nat → Nat
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C18_recordBits : Nat → Nat
  | 5 => 31
  | 6 => 31
  | 7 => 31
  | 8 => 20
  | 9 => 12
  | 10 => 4
  | _ => 0

def C18_records : Nat → List Nat
  | 5 => [0x9e660e00014a3e299924300311a68]
  | 6 => [0x12ec2bca65d6cbd4803818d3008a493c0144ca9e8e7d98380452427009c843600013c7d6cd0bf4004dcaba00002cf32d21003aa199263001a17f896806f3401207f1c029a807802a1a6a00a67f9c0138beae2998e03cbc1179900342df0014f223c0280c5980302c6a009f488e00aa43a4029d825800047af005134f000be69a80150934804ac82e00605dd2006859e00228fcb804dcc39615e34d12e685ee002412670032a4e6]
  | 7 => [0x1c056bb0af10e9003831e6006849f000010bb804c923d004f3fe60114ccbc00017379a1790f800a0156e004229e40140d3d4b9790b900a83fae00005dec00c4c3c805448af00906ddc015093780000d3f001b16f9005347ce00a65dac0259bdd804faf4f00a848ce000126fc014093c802f2d6b00a0645e00011cfc00b893c8000395f009f669e00f4a73cd8d4bfc0053384f00a331e600a86dac0000c7d802e126d00908a5e0116f47c000251f80002b6f000041ee0114bcbc025a417801a087c00008b7e005621e40179637002890f900008d7e00c893b800019778050263b005631d600dedde40241f33800048bf000049fc00d27f5c00016f78000536f00006ff6012ce07c000093e80249ff60097823e011aacbc00009be800042fb006f6df4012e68f801508758000503f00003fee00ca7f9c0000cbd800036fe002f24f2005e43e65a01a4f001a17f8000040ee000118fc028125f0000267b000025fa010ae16c01ed5a7803d9fd7000057de000121bea198e23800019fb005b34dc000001fc02096e78000385f00342ff40000a7bc00d0bfc8000326f0090389e0000e37c019133580003ffe0000977e011af67c020942d8051cf9f006658dc00d29378000265f8048404f008d31760120dfac022cb9d802b1c67004c4bf2000144fc00013fd802da6e700a23f6e00f6636c01fdc2f001690f900a0703e0116a6bd6cbc874800039df004c49f40000abbc0228e0f804badaf]
  | 8 => [0xa315300398001180067800308003c8a866296920004c5000089721000828003b800aa800a98000090000a00347004d80027800798615e2005280089800642006b8003d86659200246a838100218004a80000c003a80048800a386f69500748009100056200378002880044800088001483115500532001782e105007d83510600ad800058342178b10000248001a8007c8000d8006380078800a184c38500018004e8001f8362f536246006688d1500049700970004b800818001980035800ab821106000c8007b800a0000238004380080800028001b8a85e25b2120018800348007a800838006c8002f800708643822f2152f2140070100168001d8803f300228006d70007869381006a8006985615200048002d85e59200208363570038896807008886638300ac80012800458804a74e383001080068800778008d0008b0a8922000f80051800768000b8009f89069250365006d800468000a86d6977b1510015838153007e800a48000e8003f3003e8003f8002e553102000380013800758006e800478a3701002980006886505a03809d9a09a96049387a3a10001e80009800315009029d865002a8a3960008780000b966900049850215005b2001c8006f5]
  | 9 => [0x4e82f803805800b00a4a82183580987d8668698388a1806800c008808009158048a38108838]
  | 10 => [0x8]
  | _ => []

def C18_buckets : Nat → Nat
  | 5 => 1
  | 6 => 11
  | 7 => 35
  | 8 => 45
  | 9 => 7
  | 10 => 1
  | _ => 0

def C18_flag : Nat → Nat
  | 5 => 64
  | 6 => 0x400
  | 7 => 0x4000
  | 8 => 0x1000
  | 9 => 256
  | 10 => 2
  | _ => 0

def C18_seedBits : Nat → Nat
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 13
  | 9 => 9
  | 10 => 2
  | _ => 0

def C18_seeds : Nat → Nat
  | 5 => 53
  | 6 => 0xd78530e900b014028010062a005010
  | 7 => 0x68008000300a4001801e0042036405a933e0483000e00d80030007062a005a0070013023e007000b80160050000401c0003000c053c009801001a000980008005
  | 8 => 0x9f93daa48c0040fd027821868800602e82144e801400100980b8049012050c27a06d001815400c13001742d00070b40018018008001823c2d0045036006000804e001001004c00405c
  | 9 => 0xf557044d4000816
  | 10 => 2
  | _ => 0

def C18_S (s j : Nat) : List Nat :=
  qDirectStatePattern C18_initial (C18_countBits s) (C18_patternBits s) C18_patterns 16 8 (C18_slots s) C18_values
    (fld ((C18_records s).getD (j / 256) 0) (C18_recordBits s) (j % 256))

def C18_idx : Nat → List Nat → Nat :=
  qIndex C18_N C18_buckets C18_flag C18_seedBits C18_seeds

def C18_routeCodes : Nat := 0x4515000020100000000c00000000000000000000000000000000000000200000404000000151000000200000000800000000000000000000000000000000000000200000001000004454000020100000000c000000000000000000000000000000000000002000004000000000000000000000000000000000000000000000000000000000000000000000000000
def C18_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C18_rankPool : List Nat := [3296408, 6491871, 7695529, 2195115, 7756172, 5320638, 5520569, 4284333, 6438282, 6454424, 2125451, 7687610]

def C18_rows : List Nat := [26, 28, 33, 50, 52, 65, 74, 76, 3, 5, 9, 17, 6, 40, 80, 96]
def C18_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C18_rows)
def C18_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C18_ori : List Nat → List Nat := qCompactOrient 4 C18_routeCodes
def C18_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 8) (compactCover 8 8) C18_S C18_N C18_idx C18_ori
    C18_coords 4 C18_rankPool s
def C18_F : Nat → Bool := certAt C18_Z C18_N 11
def C19_initial : List Nat := [0x3a4, 0xcc2, 0x106e, 0x1511, 0x220b, 0x480d, 0x6070]

def C19_values : Nat := 0x3f8ffcf2f4dfdfd7bbdf57feae3d5c3a88f470e7fdc9ff8b8707ee0e1c1bb8006ff6d9e5b30b5feebafd4ffa83f506ea00d0fba1c3406e800cae191c31ffe3f4c7498dc3178627bc4e1882f0f86170c1e181eb03ce072c0e381830106010c0017476e88dd0db9dd733ee615c0db7df6436c37d86eb01b6002a88d06e9a1b333e6614c8d981b2eb65d24b0d951b28364c6c90d911b20020003fdb7ddefb2de773cc26f7eddfdb8db7116c16d4459f7b3ee6616c9bd937320b60dcc0017f7aecb5d84b309505a60b475e8e91185a28b44d6892d117a22b4436883d105220944048805100206040808081008200a40128009000a0003fee7fb8ff31eee3d8477b8ee99dc23b227444e771cc238186fb8bff97ee2f6a5e90bc897112b2255fcab8956e2a6a54c4a8d95192a265400a0013ee27cc4f909d713ac27484db898512ee24dc48008f711c222dc4580886110021dc420083f106f20d441988311060208440b8816102420404040807100a2010400880090001fcc3f087610dc219a4330c5d207a40a000f981f203b4075c0eb41d603a6074a0e0018002800448088010502090408080810082000300049009001100208040408000a401400208040007000d401980310060006000b8016002400400044008000e001600280048008000600080008000

def C19_patterns : Nat := 0x2555951654165159415955645590559556155815595556555555455455505519545551154255055405455511544150554054555145445510541545551514515141445505541145551544545150451511544510554145

def C19_N : Nat → Nat
  | 5 => 4
  | 6 => 92
  | 7 => 337
  | 8 => 330
  | 9 => 34
  | 10 => 1
  | _ => 0

def C19_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C19_patternBits : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 0

def C19_slots : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C19_recordBits : Nat → Nat
  | 5 => 25
  | 6 => 34
  | 7 => 33
  | 8 => 24
  | 9 => 15
  | 10 => 6
  | _ => 0

def C19_records : Nat → List Nat
  | 5 => [0x3c9bf8001d23df6cd26cd3cd1]
  | 6 => [0x33cf3c400b3450f00268eba5e0e64e8d00290f3a5e8c4508b000015be5e8752e38001e4c7c400793871003e4eae400e636c700000f9e400ea4e4d003397d5400751af80036ceba400be5d5c003bdc0f0009b2e7800364eae4000031f3002f8b9e1c2be5d9c003e5926c00751b7800340da9c00e61d4d002f0a34c00c23af1003a9531c00a94e65001e8e9c400bc3ad900001e4ec00621cf1649e8ed4400d83ab9003d8f2e400783b71003bdcc7400be452d001d4b9e000dc3ab9003d0eae400cd31d300264eba5e8a13aa97a310ea6400d03ab900228eba400003af9001dcebc40000729f3f9e8e1c000792e780039ceae400c43ad900254eba588a13ac93c9c0c3c000fa77b5002f92ef000b33ad9001d4d9c400e63ad9001d4dbc400ce62d3001d4c7c400a83ae90034074b5e0a74ea5621d4b96000006579003a9b83c00fa79b300001876c00631cf1003d98e6c00a73af1002dceb6400c93ad9002d4eb6400003cf90031cf36400963ae9003ecc6cc00b43ad90038ceae400f4621b001d4cbc400a13ae9]
  | 7 => [0x2d47a680166613400581d3600631d5b002b936d80000b53c00be5d9c00001e5b003d07a30016a962800e668020000281e003a914500000b93c00b52a1a007b14460000073080000a764009b1eb600002b9e0000114a001cc3d34000031ac0079b40600000c2f0014e6158007d1d36003a971b003a0ead801ea756c00eb73820000179e00001e843d1883d0000eb3ab6003a845b00204da8001a03d1800e64e9400368e98003d0ea380154756c00002abc002e00dd003716e080000de20000038bc003a9720001d406d80000417800003ab6003a859b001d47ad8014e9b6000c4309a0000360800000fef00000c43c009930a400681c08002d07a680188a1280000731e0000165e001d4ead801528a4000002b3c004b185200258729801e0a71000b340820000129e003acda8000002b8800f43ab600521452003ac74980136616c00003ad2005e0f4d00228c29000009c8400001ebc005a984d00000011800ea0a6c0000283c00001f9e00360a03000003a8400d010860000239400000b0f000ea616c00f4518c000034c8001e8ead800003b84009d3ab6003a989b0039cc23000fc756c00a71eac000022d40000137080142754400bf3ab600002314003c1cc0801cc9b38006c1eac0000300f00000e6f001023a4c00763ab6002e069d00000b4f000005378008e30a4004d9d9b00384ead801ccaa28000031b2003a9c1b0015072d801883d34000037bc004d1852000017a780146756c0075243600001d5c002f9667000fe635800b4309a00001d66003e9a0200000b43c00f46202006c8f4600308c2b000006d6400d01e10005a8e4e003c0ead800005b78005c10ba006c98460033d82680000d02000f4508c00369616003419e0801c6bc0400be3b360063944d001d86ed80000a27800f462000036141600370da200178613400962a2400003688003f0ead80000ea3c007506b6005a140d000016e7800008d50007a3b3600003cde0030976580148614800002ebc005b8f4d0000088f000003f7800d85a02002e031d00001ec4000ec3a6de8751e8a00682ec1002bcead800ea026c003d1d36006e1606002eceadb10ea3d3000c7309a00509d5b00284829000007584007930b6006d985200000c0f001448a4800006910752e0f5a003097cc001e84918f476382a00621d4c00000eb6000006979e09d408400509d53003057cd8007a34599e7a3b2a003b0e5b001d434d801eac434005c03ba00621d5b002f8c2d80000427800cf3ab6006cad4100001f4c800ea016d88a11e92a13a8f51000008af001887538006d30ac001e8e5b002dc747001ded01c00002e3c00003648001d40ed800005478000054b2006c1846000018e780136978000cb3ab600002fa100001b84001b83d1800761c3600450f52003317cd801388a4c00a7502c006c1b043d1d8c4a801ba756cf4701e2e007b1846001b0c2b0017c3d6c00be408e003c945b, 0x6e22830000080f000004f78000031bc000039080000098f0016e6d2c00aa4da6006c8e4700398425001cca72c006d1eac000037c800000dcc800ea066c00b23ab60073184d003c1141800c63c5800e3308c006daf930000092f001b8611800751e36006e0e870028136d80102756c00006890002e035d001ec72d800ee6158000025bc006c9506001c0a2b00130756c00b43616003a9adb001d442d80000c93c00f4308c00003be10018452e8019e515800a12e2400002f0f00254c29001c2be1c00005b1e00308e9b003994068000052780000363200328f56001d4b8d0019ebe38007f3d3600319856002dcc2680000798400002bbc000011de000014af001a0611801013ab600002e0f003607a300142614800c42e1a005b960d001d418d80168952800f42e0c0000145e00000eb7000c41a5800004fbc00308e5b003d188680000467800002fbc007a1d45]
  | 8 => [0x123002aa3000363001863000da3000ba330835e30829e001263000ea10035e355105e0000a300185e00105e003d630036485d985e00398f518f5e3d1d9b001363508f5e002dcf3b069e003763004023003d23408f5e0000250001e3002823000423758f5e000c23000f230038a30036230021e300171e003c6350205e5920481e885e001163003408002163001923551c1930809e70a294002c6300226330859e001aa31e8f5e1e809e30845e53a059000f6f4e8f5e003f231e859e0036e31e835e00310f7a985e358f5e4e985e002b2375b3cf75985e550f5e75aecf0007a30020e300366300151e0029d9308f5e000f6767985e00115e00212300186736885900186a0024637e2a990026a3003708003563003b237827610001630026630004e3002ae30008635520540008a367b18f0019a33d185e001fe31e80de2e0f5e0026e13d0f2130985e0004a3000963000ca3002d0f0027a30009237e384830831e5f985e7e0f5e3081de0034230009e31e829e000aa31e8f1e00276373204f000f5f64185e0003233b185e000d23620f4f001d9f5b884f0026e355185e3d1c196e8f5e1e831e0015230003a30009a3000f6300386338185e00185f7820486c86882c085e00186f59185e7e185e0000e3003e23003ae31e81de000b23001423000563001ae374185e0023e330819e1e845e0022230029a351985e0013a30010e30002e300242375b4080028e37838480022944c185e00262367aecf7e3d4867afcf0000230021a35f2ca10005e3001b19000be35faecf001ca300125e4c0f5e3b01de000030003fa378185e7c185e0005230005a300006328059e0029e3000f6a000ce33b065e1c86a1759c237aa8de5a868f6e08480006a30003e30024e30001a33d1da10019e34088540035a3000463002d4f6c058875885430869e63185e7a0f466e985e00360838115e000e6135985e001b2300202300161e001b63001b59000763000a6370b748001963001a234b069400002840985e30899e1e805e00162370985e0024a3001c23000f5e1d0861380f5e3080de002c2375ba0f000223, 0x620f4d708f5e003523782fe13a8f5b001fde0006633f8f1e00286300002b00106330885e0002632a069e7a0f48003b63003f630000245a058f003de30017230040a31e819e001d61002f0f4da0617e125e001d5b0006230008233b085e000d63003d080008e33b031e0025a300145e30945e0020634e8f21308f1e000723000b634ea05453185e000c6300141e3f985e0002a300186d3b035e7a0f5e0025e37a8f5e00281e36059939185e0006e3003fe3002523758f230020a3001463003ba30022a3000fa3002563000a233a8f61002fa10007e31e869e3b00de003723]
  | 9 => [0x791aaa303466178071bae308c6168c7af0023004a0a8d03186a30646a38deb180243846218dbb181e30146618c015836335c6988d3b1bf2370c600c07b18028]
  | 10 => [0x23]
  | _ => []

def C19_buckets : Nat → Nat
  | 5 => 1
  | 6 => 23
  | 7 => 85
  | 8 => 83
  | 9 => 9
  | 10 => 1
  | _ => 0

def C19_flag : Nat → Nat
  | 5 => 64
  | 6 => 0x400
  | 7 => 0x2000
  | 8 => 0x800
  | 9 => 256
  | 10 => 2
  | _ => 0

def C19_seedBits : Nat → Nat
  | 5 => 7
  | 6 => 11
  | 7 => 14
  | 8 => 12
  | 9 => 9
  | 10 => 2
  | _ => 0

def C19_seeds : Nat → Nat
  | 5 => 51
  | 6 => 0xe34350837f849c0580d01e004110041f204c0a00d0031302b8f00050b013003
  | 7 => 0x18202183ca46900f5852008c846a0f2004c008006c0d603cc43e00b401200340950344005006400302540180e30065003c00106081f5000801202ae1510064003004001f001c05201bc06600040230180004043000200d4002019a1510004002000c16c0004002007000102f8027002c00100b40030194005064a050004c011002c01c00320340180057002800b00360230004062
  | 8 => 0x6440495c10010c448f00317a1ce2e32e500105c94902f00103406e04492c13200311200194a01300a8ff00402f05c0258a894a00903f02101510c00108d00300102011a8a308b13500106505187e12e00f01787102005200d0020010170090010ef1d286f05a07100e26300480800206d00394a00101c0f700a01100a
  | 9 => 0x1f038986c2491124f6fa
  | 10 => 2
  | _ => 0

def C19_S (s j : Nat) : List Nat :=
  qDirectStatePattern C19_initial (C19_countBits s) (C19_patternBits s) C19_patterns 15 9 (C19_slots s) C19_values
    (fld ((C19_records s).getD (j / 256) 0) (C19_recordBits s) (j % 256))

def C19_idx : Nat → List Nat → Nat :=
  qIndex C19_N C19_buckets C19_flag C19_seedBits C19_seeds

def C19_routeCodes : Nat := 0x40440000232200000000000000000000000000000000000000000000000000004044000000000000000000000000000000000000000000000000000000000000000000000000
def C19_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C19_rankPool : List Nat := [5336441, 1059722, 5532280, 4206237, 6446715, 4283514, 6311595, 1064122, 2112664, 5447102, 6638215, 6576250, 2117001, 6634391]

def C19_rows : List Nat := [28, 42, 49, 56, 68, 97, 98, 3, 5, 9, 6, 18, 36, 72, 80]
def C19_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C19_rows)
def C19_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def C19_ori : List Nat → List Nat := qCompactOrient 2 C19_routeCodes
def C19_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 8) (compactCover 7 8) C19_S C19_N C19_idx C19_ori
    C19_coords 4 C19_rankPool s
def C19_F : Nat → Bool := certAt C19_Z C19_N 11
def C20_initial : List Nat := [0x394, 0x54a, 0xca1, 0x207c, 0x3203, 0x480e, 0x5070]

def C20_values : Nat := 0x1fd3ff79feaff9fbf3c7dcffa7ff41fe83bd01fa00f0fde1f3c38780ef001ddefabf757ae8f9d1c39fe73f7e7e9ce53978727fe4f9c9cf9387203e401c5f38b870fce1e1c1f383c7074e0e1c0338006d7ed9ffaffb5cf6a0ed0fda1f34076800c7f98e5303e6000bfeb77eeebf5cffb9e37286e385bfeb41d63c2c3f5870b01d6002bff557aaae1552aa785470a7e94e529b852f0a4e147c28b850f0a0f941ea83c5074a0e541c68205020a02140027ef4fbf9bdf353a6a54d0e995f32866474c0e973d2e525874a8e941d263a487488e90fd213a417481e901f20324054804900520022a5439480e1010201040108019002a00240028000ffadfdbbeff7d46fa85f01bca17506e80dbefb77f6e96dd29b81b6836c06d5299ffb3fc672ece519c1b3036506c9fd93e32736496c90d911b2176426c83d905b2076400c1f182430206028c0017feafb55d42b7fd67eaca158f8aff15ca28fc50f8a0013ff27fc4fbc9e513a5257e4af8952928024fc48f890011fe23f447b88ed11ce239446f88d2117e22a044f889c1106220043f885f108020fc410081f903ea07840e881c1034205c4098812102020344058808100e2014402080310042004400480050001ea139425d28aa51394240041c082010202020400880090001ffe3ed47d08f941d4237ac6e50da11a9433c46748ce1196a32c46568cab194a328c6400c0017282200410080c10142010401080110001f783e507940e9417282bd056a0abc15682a7054b0a90150028505020a001200224044008401028201040108000fd01ee03d407680e781ce0396072a0e001800280042808401020202040208000c0014802800450088010a0208040808000a0012802400420081010001f003c007400e001a0030005c00a0013002500480084010001a003000580084010001c00280040007000c001400200030004000600080008000

def C20_patterns : Nat := 0x955651594519556455914595561558515955595559555955555515515541545551154155015255491519546151654555145445510541550454054555151451511541550511554551151451511544511114415055245461515545541544545149451914585151450511141445510541550550115

def C20_N : Nat → Nat
  | 4 => 1
  | 5 => 21
  | 6 => 199
  | 7 => 651
  | 8 => 575
  | 9 => 51
  | 10 => 1
  | _ => 0

def C20_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C20_patternBits : Nat → Nat
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | _ => 0

def C20_slots : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C20_recordBits : Nat → Nat
  | 4 => 16
  | 5 => 34
  | 6 => 34
  | 7 => 34
  | 8 => 25
  | 9 => 16
  | 10 => 7
  | _ => 0

def C20_records : Nat → List Nat
  | 4 => [0xb287]
  | 5 => [0x10b6423a5c2e0e480167a9070059dcf0ea34b30060039dbf8668e86ba20037daf900000a8270059ac61ecd4b87050039daf8aa34b3605a5c3a16440000b0170055ea29a970e8394b352e0e1800f76407003ddae58010b6bb2]
  | 6 => [0x166968f00521ecd40000959fa8d2dec94015aa8a700320fb9a970b8413004054b5801637b97003d94bd00113361d00546969c013e52d60056a16cc01483f35004b14b5801486527003b1aed8014829b500521ee5e7cbd52d2000028cdc00c052f2003514b9800e352e600294e1c8013393b9004114b5aa324840e003dcfa7800bd52f20000175d80151a42700521c69c010b83daa8d2e101c0152a097003554b980152642700379619400009df60059a7f1c014152d600294fdd000a529f49f2bd4b5000e838fa000014bd8014b7c1700521a89c014824350052100cc01483635005494ad9546d2bf000435bd34015191ae0054980cea34b2c0700522585c00f761970044cc078014885b300521cacc012791bc005214ad801616bd6004d1aed800a53674000029cdc014160530030ce18c013e5ed3004754ada96ec36150000298dc000059f6003294b9a913e579500544d934010b52f200424db6401486aa7003b1909e970b7b93a5c39ee56970f8593a8d2e1e1c01676447a8d2e168c0148811700520a8d4015152e600002a4dc01487ab600522125c010e85d900354abb0006d2af8002bd4bd00000b1375eabd4bc000e86be600520fad8015a7b9792421ec7000e86be7a42f55ec4015259350044d3a9c0128869d003214b98010b61b300002b6dc0166874d9242e10680000577500378abb000f752d60036dafd0012052b6004ce586c00a540720043a0f7001486bb6004094b580151a32700381af9a970b7b31004794ad800e56bf2a44f94a5801485eb300481909c01286f2da42f54ac8010952d6005227c5c010d36d9005215ed4012c4ec79a3a1868c00bd57f16aaa8af90014b99b300521b6d401486e279f2f55f44011352b600294a9d0014836b3004b54ad800e7646300425ab3400a5247400544c138016172d3a5bb0c05800df6465a42bd4ad001488097004954ad800006467005a2a49c00e56df1000027b5c00b252f400521909c014838330059a0f38010b63b300002acdc01482ab6003595598010b3eba0030ca99401346427003dd8e5c0166a5a7a5c2deaca913e5e93a5c1dee580161a417003714b98007137f80052e16cc00c059710035d919800006bf6001c8afe2cd4b7b870052dee5ea34b7aa600294dbc8013391ba0000290dc0148303600522085e96f67ab4]
  | 7 => [0xa5c21d8000055133100002902000ca411c0000216c000e3301f00001769c0000981a0031d008c014b7608003548078014b79880052e04580000829a0052e3a2001414e9600364fa9800ec3e8e005221020013e41160052d008c00002532000011a9c012c6396002a9008c0151859d004b5ee0800004e27004a0903400ec618800425045801096e1200001a49c000055a700491ee0801042a18002bd049400c8551c002940298000091b300522682000bd45a3002d4aa980055243100294ae98011e4d88000014a98015852a6002bd4a980109701800000fcc80148040800478da3296f57607005493a20016ba408004fdee58014807080044d0420014852a6002a8709800005227000029028000083b3005221e2000008732004f94a9801489488004b1005c014b8b8800520402000f7551600002643c0000a40900494aa380000a41100001889c000052a9004b0fa64014b7b250000282680164a408000015ec800a50aa600474a63401024d96005524020010141160042decb801483a8800475542000e02ab174361546c00e3551c00001ee68014804880054e902000006ba60052dc6700000412700301548c00b8302600001907001045016002bd54940000ae2700546960c00af52a500520b020010b3a8c00545ea7c00f7411600395868c00009fa700295049800824023002940698011355080052e125800822aa6a5bd9d818000052a7002f54a98000054a7004b94a9800d44c9c0038cd87801087b18002c09094006d2bae0044e100800c73f25000010a9c00aa3f2500586965801525508003dcea08014b3f2500294109800008a8f001b0c0c400c73ea600001709c0124641c0037890780148578600294269800803eaf004f97a5800af47a50052cc098012c4116002a8c09800003eb30052e7c59c0d8551b000020468014b6da500001589c0148970800425585800aa2a2500001409c013461880052d907000aa29a500480e03000d52b9e0052cfa9800e0619c000025a3c00af52a4000006ecc0148a008002f55eb800823f25000014aac012d4108000027c6801489f0000002903c00005aa700000dac000004a270038d707000004ea700521d8200000a7a700000aacc01484988003d9549400004030005769020010b7aaf00546481000007c9a005094a9800bd52a300002949c0000910f00521862001684e9c00479042000d4299e00405325801685c1600294e69800004c270029418980000a40b00520ae20000050a7000020c680000512700001129c012d360d00000a8c80148578d00002c69c014ba408002a94a9801092a9900001bc80000053a7002f5548c0000a9270000000d00125550800208fa997aaf4121000011c9c000052bf0052e163001489f08004a54a98014b89880052e0258016896820052daa7001346388000014ae4015a6c260049e263401132c0200001329c01667b920038d0470015aa988005221820012d5c0800001b88000004fa70043dea6400008e8f0054e962001256e04, 0x2954a9800a517a6843a0e6bc0000ad270052002200148578800545ec780000898f003b18e22d0e8399d57a95049001343f0d00405a84800a537a6004f94a5800e8619c004810420014b9a0800001109c00f5412600544b04800d54d9c001bcaac6970b7605003d9049401254108a42bd04180104551600002749c0000a41000001ecc80148a4085515c4c9001208202004314a9801247b0d005215e940000809a00001908000a50e2600475a810000061a7005214a1c010f6a9e00520de200000373200000e4c001349602005202a20011e81020052dee00000040b09f2f5044c014b9688004b4c0380161619600371047000007320005217a20011e6a8400001369c0133898c004b5c61000ac2aa600001ba8000d5369d00002c2680148200800475042000aa1ca6000012a9e90bd4105005a0c0640148528e00001b6c800c152a6004961208014b36a3000023c3d7aa5412200001aecc00006ca70042d548c0125700d0052dee58010f36ae00264a69400bd52af004f95e60010f52a6000024c3c014b8f080041dee640151411c00002a42000a54ea6004f1ea9801487008005217a8c000038b3003550470000063270052ce08c0000a8a0000014af00000851a005205e20012c5516005469670000045a700001cac00148098800002cc8001489f1600522482000dc561c0056a6820011d4c880042e105c01480608a5c3dd800008236a300001509c014b2aa6004914a980082362500002909c00aa3ea600479542000a510260052de820006f30ae0029512980000a90f002c95494000047a7002c54a98014b52a600208909400e0562500439ee60007e3eb1004f94a540000869a00000d8c80101551600476020800003033002944c98015c928892421d8040151879200000fec8000043270044d0e2001485f080052dca8c006d242e003614a9800d4551c0042d048c000051a700001349c0151a5880052dee200123898e00521d02001484108005227c08000024b2003d9eac4012c898200404a66000005ba700521a6200000940f00208e08c014801880042dee5c00aa38230000164c800007c1a00208a8940151a58400410e05c014b8216002a8909400aa2aa600001c68000bd57a500434906001683618005214a20014b2425a8d2dd80c016ea58800002403c0151551c004214a980102369700505545800c3179c00200fcb80000582700481402000b452a600569d820012556080052df658014b2a2500001f66800af52b100000acc801519d1c000023e3c010955160052dda2000a52026002f54a8800e052a6003a14a98014b7b8200280a894013a85a3003b14a98012c3f180052e4a20016852a6005215420014052a6a5ba1c070000048a70052de2200148010800001ae9c00a03823002ecc098e66f2bad005462610000045270000266c00000603000002929c013e5516000017ac000aa36250000096c800d352a600208f87000571b31000025e3c01202a0d005017a8c000056a7002f5048c000093b2, 0x908f003a0c2c001138782002a85c9a913e4100002a8da8c000029b20000206680000642700001f46801205508003013a8c0000462700274ea70014b6e1c003b0c064014b5ea3005217a3000d4411c000029a9c0148588800208c09800dc551c004d14a980000a3a70052e585800a502a6004f90e5800702a2e003d55498013e5ea300001a880000062a7004f97a5e7caf411400001ac800000532700002586800be52a60052da87000a53aa600361549800009ca7002941698014b790800208a6940124858c9f295045401480588005363a200000ac27000022c3c013e52990036d8694014f8f08a5cd2181401484588a5cd1ee00010441160052dae980000552700002969c0148028800001eacc013a7b250047a1e34014b7aa600001789c00dc2a9f004095458014b85a3002f5628c0000383000294b09a9734740500002126800a50126005217a1696ec2c000052e3020013a7aa600002283c0000821a00001aa8000004927000024a3c00bd57a300000c4c001480e08a4295041c014b57a5002e0d894000072200000090c8000063a700002a89c00d761a6000013c9c0000263200001269c01518412004244c6001026a920052e162000ec361800521b020013e5e930052cd89400aa26250052e4020013e5f1600520e620014b8585002c93a9400009e27001b480b8015352a6005204c2000be57a500424de6000005ca700001209c01343e8e004b55420015a641c000014acc0102411600355547001639688002941298014b29a50026cda8c0168a40800562902000a50726b454e960c000043a7002f55e84010f8597]
  | 8 => [0x742f980002cd0002268aa09a7000f5a001329c006568e86c20002953295049ca82f64e84127005204264409dd0e040000e3400031a00230d000eb694b760f923b07c20e6cc00d440007b32000fda00106d000016908412739921900268d00082580018b400355a00116d1ecec64003834005213ad9549c0015680034b4a9c907da1d080016e68bd4127298819200eac0006f68aa04a776160d002bed00012680044a700119a52e529c014b8129552700469a2bd04c801514168879aa582d3d2d629c0082695a55270032da42dd8c280be4eac2027004c5a52dd89d54204e007534a5c2138020468004864005627972a9380068d00079692c3a9a00405a00296e8014568007734000a9a002bcd268824e0008b4001b19002dad0de4064002c343689982a82a9ed073680071b40031d38013a9c00006c0077b40024da0026ad0009d692987b2a58813801d8d0001b68d84127003d5980220d1aa2640aa2ba7000bda00236d0007b68004bb400001c3a1549c00dc6934948f2b89990015ec8005364002eb400155a001a2d296584e00a2345509938007cd00043680071a0000e1a00008d1c057640052b4002a9a2a8069c0039680015b4a58393a08b09c00af680000350003da000ecd2a74b4f0f861a003d1a000e6d268751f4b760800075a2a9049c00186800903400491a424806801251e00961ab42093aa8b09ea6aa4e00823400295980032d0003c68002bb4a584d380254d296094e008f3400115a3b1549c0125694b862758aa93801d0d00155680011b45ea09852c069d7a8246002db4001e1a0017ad0006d600089340021d3801c4d0015a68004cb4001d1a002749c008f4e005634410bd38000cd17c824e00843400101a0025cd2d0aa4e004127a5a09380048d000007c007b9a6e10104d25c3e96c34e00213400331a50d549db0aa66552033a9d2c4002263c006d68aa05a7a5b813d2e682000f168004140003c9a0025ad252824e0089b400445a361549800c768e058b200355000100d21e824e003634923619801409c0035680019b400021a4a6483c0021680078340030d3d2c0a9d540e4ed844a700281a208169dc65841404127a5b4d3a080a9d54734e000f34, 0x741cd8180b0cd046f4e822ba79a4318000c6d00013680067345c1613ac5049cd85864004030550313c805e3c00827a002cb4003a5a34d049c010b60006a34a58bd3c3dd0d0014b7b534127002a960001ad001386800acb49a3a182a8109c015169347b9a761d47802026800e16800a5aa004787c21d86800d8693e4116000d9a001e6d0009668e02032b4160d0027cd000ed680003b400015a00286d154024e732bb300209d001fed0de576564a5a70020953504080006066008634b4420d2a9549c00dc4168898f92421980064d2972e4e0069b400329a5b2969c002569087434380bd80001cd00082500018349720938009ad0007e68009f1a69aa93a08189c00da6800133400471a381049c007d6948412700139a2a8de9c00fc68001034410813d2e689c01201f68a5a70052078004ed0002c68003034001f9952c809c002e680016b4a02a9380000dc01176800323400521a001fad184aa4f55a5a700149a0002ed0006a695349a7ad49138021ed000446882202700225a00154e8003b690c841a000e9a208269c014b514b552700341a1004cc8000076002fb40026d3aa80a9c010268c73aa700001a00155000104354ba5a70011da208069e966f4f1d100fa5b61380274d290821e000fb487c20d5a28068016a694b2ba7001ada002126a97404e007ab4550b5380004d000b6680061345527538019ed0fa756751762000179a494803c00f7694b3aa7a5ba13d2e489c00c968003e34005bda491549c007568823aa700295380296d2960c4e8241270019da00012d104154e0058b400185a002b49c00bd613e4127551d53801c0d17caa4e7e3ab200029a52c2a9c007d66820727af52d3abd049696084e000d3487bb0d00154f4009b68009b3400335a56a969e3c261f0f1332000020a08e69e96264e00968f52a0934b4b03d04024e0001b49d3b13d2d7c9c008f68008cb4003d9a404406ad12e354b9a0f820bcd0010ed269241e00143400171a000a8c800b868005c270052d6431549dc08f4e0027b4550713bd5d8ce9082114b39a752a099800a2d1041c4e0049a7a5bc13802d2d154254e000a3481098d4d1549c0153694b0127b421d3af9629c002968009634, 0x3b1049d04084f0c4127005a1a52c389e1eaa4e0094b4842a9380154aa1ee064aa202700501a00016d0006668a017a7879bd9000d0d0007060000834004747a6c4c9c008468e05527a5c3d39ccdec000bf693e411a0030da2084c9d5e824e005528001559800a6d0016c680020b4550bd3801fcd0010b68d8552700591a0023ad2d1534000a5a7001dda0017cd104014e00283400401a3a1169db4aa4e8204a700425a4a5c0caa74b1f244127703610001549c0054680045a7001e9a000b4d0013768002434]
  | 9 => [0x69b40e342c34412713345f345534003404b48434b434004102b43ab4a0347434552739b4703417b497346c34003701341034a9b405b487b400382bb48634923494b401b4413458b40ab4003e37b40036a5a7003b9a34a5b400352034043409b4063407347634]
  | 10 => [0x7f]
  | _ => []

def C20_buckets : Nat → Nat
  | 4 => 1
  | 5 => 6
  | 6 => 50
  | 7 => 163
  | 8 => 144
  | 9 => 13
  | 10 => 1
  | _ => 0

def C20_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 0x1000
  | 7 => 0x1000
  | 8 => 0x400
  | 9 => 512
  | 10 => 2
  | _ => 0

def C20_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 13
  | 7 => 13
  | 8 => 11
  | 9 => 10
  | 10 => 2
  | _ => 0

def C20_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x18a03338084611
  | 6 => 0x213909b84100bc01402409380940a624c49180040b801909f883000400300580b001201a82909f803013c01d04f808800100081040020da0034064006002002000403a004019405803b0c70008008026001
  | 7 => 0x13951d011f002c9e409800700207c008400193800080060840f103b4002001036845400600101a03349061c8209c9be5161a600085741b600805201d2496030000800800202f12282d004b23d008801c0dc04400147f448205107c00d426c00102f825c04a02a05480ac29800400105ac14800100f82cc0020010078350004010000c7c800401900547a000328b008800400e02407a026405a098002800801402821c009831c003008808c002044007c5940ae0ec00080d804e04901200f0003164052807406001f00201241460030030238196002014449000605d86b000802a01300e807619c00b84f00dc13c0d7001800400825b00281800a60b000d001824507b005005401a087
  | 8 => 0x3604714a701198941181a26e029900050025681420c0c84480605900a4fb120e14ea1356e01700a00c5ee12bf6750b39912f602af1298b867d806dad00e02c0305f03e2116c02f00213c170050040b8b483e02817064d480021a8085264e827043d1d054010cb81512805c008070580180181001f8fc0b80d4098fc4780600202a6e82a9b40140086a00a004090149778fc0fc9000c0041b0079191e402001c7e0182601507800c6702a8520960a0d500205c58c04016040238130080387d05607d8fc18837
  | 9 => 0x1b7008cd231958a40201227004cf0e81f
  | 10 => 2
  | _ => 0

def C20_S (s j : Nat) : List Nat :=
  qDirectStatePattern C20_initial (C20_countBits s) (C20_patternBits s) C20_patterns 15 9 (C20_slots s) C20_values
    (fld ((C20_records s).getD (j / 256) 0) (C20_recordBits s) (j % 256))

def C20_idx : Nat → List Nat → Nat :=
  qIndex C20_N C20_buckets C20_flag C20_seedBits C20_seeds

def C20_routeCodes : Nat := 0x0
def C20_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C20_rankPool : List Nat := [6637690, 6368924, 2104215, 4262552, 2178441, 5311678, 2121081, 3156874, 6445688, 5336747, 5532295, 5394043, 6373084, 4414072]

def C20_rows : List Nat := [10, 28, 81, 84, 97, 98, 100, 3, 5, 9, 6, 18, 40, 72, 48]
def C20_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C20_rows)
def C20_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def C20_ori : List Nat → List Nat := qCompactOrient 1 C20_routeCodes
def C20_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 8) (compactCover 7 8) C20_S C20_N C20_idx C20_ori
    C20_coords 4 C20_rankPool s
def C20_F : Nat → Bool := certAt C20_Z C20_N 11
def C21_initial : List Nat := [0x748, 0xa92, 0x10da, 0x1925, 0x6403, 0xa01c, 0xc0e0]

def C21_values : Nat := 0xfd3ff9fdf4dff0feee9feafee7fce75fe748e4ffe4e3e4e0e41fe41ce403e400e0fce0e0e01ce000d9e5d9e0d925d8e0d1e0d0fad0e0d0dad000caf2cae0ca92c9e0c8e0c7e8c748c6e0c5e0c4e0c3e0c2e0c1e0c000bf7dbbbfbadeba9eb9ffb93db925b91cb81cb7deb75cb11cb0deb0dab01cafdeaa9eaa92aa1ca81ca75ca748a41ca21ca11ca0dca09ea09ca05ca03ca01ea01da018a010a008a004a0009ada9a92992597da974890da90008a928748801880108008800480007fb77f6f7f037edb7e937dff7d277d037c03792577db774b750374db740370da6fdb6e936e036d036c036a92674b67486703660365036493644b641b6413640b6407640060003d253ada3a92392537da374834da30da30002e922a922748240020182010200820042002200120001fff1fda1f921f6d1f481f251f001eda1e921d251bff1bda1bb71b921b251b001ada1a9a1a921a481a0019ff19da19b7196d193d1935192d1927190018da18181802180017da1758174a174816da15da150214da140013da139212da120011da1118110010de10db10d8109a10921058104a1048101a10181010100810041002100110000fda0f920f480e920b920ada0a9a0a960a930a100a020a00090008920810080408020801080007da0758074c074a07490700060005000448040804020401040003000292024802100208020202000148010801040101010000da00d8009a009200900058004a00480024001c001a0018001400120010000c0008000500040003000200010000

def C21_patterns : Nat := 0x6555945651194159556455911641565558556115815595559555955555515515541549552154655155445509541550151554515115441505541150151554545145445511144150551554551151451511541545551550551151454415045151154445055415405441450454055

def C21_N : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 176
  | 7 => 488
  | 8 => 432
  | 9 => 41
  | 10 => 1
  | _ => 0

def C21_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C21_patternBits : Nat → Nat
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | _ => 0

def C21_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C21_recordBits : Nat → Nat
  | 4 => 25
  | 5 => 34
  | 6 => 34
  | 7 => 33
  | 8 => 24
  | 9 => 15
  | 10 => 6
  | _ => 0

def C21_records : Nat → List Nat
  | 4 => [0x7fe0ba40e0]
  | 5 => [0x81b9cf2440083417000204edc206813cb00019057c2190a398900415d04c00a340e800000edc568813ce0001a055c2190a300a00204f1c000b540e200204f3c00000858f00290c98400844070004156a8c0112860e002f103c000aa40e80028cd18606b43ca15b2ad038000813bf0]
  | 6 => [0x18de800f0471e00204f3c400783471002b8e7a600ae302a002c0f1a400f239b900000e3e401023c39002d4d18c00601ff80000193e4010c39e95a1e4c98400a339e900204e7e00100303a003e4c0e8005420f2001a03bc400f439b90019047c600e1570b58208c78800803af100288c1a8008031f20023cc1e0007733f1002b8c1a8010340ba003c11a3c00ab40f800000d1cc00811c78001d457e0009639f17c36d86716cab326100210efc40000307a00424c0e800003ef900320c1c801035a2b00204f3c000a34269002d103aa14bd301a003c4c0ea190a3a8b863e1b63800773072003edeef00114860f571ccc1a000aa20ec004421a3e00733038001907fc400a239e9853218654007c39f100400e6e400a33269003c4e6e400c839f10018071e0000040fa001dc83d000bd4d8f0015071c50279327079360ea64007c3072001dcebc6190a610e001e4e5c400bd529e411e0c7c00100709b0032cc168008e39f800208f1c6190a318b0018081e0010c306a7928ceaa400fc6e9d002c0c1a8007738f1000020e7c00ab347100414d0cc0073347100208bbc800a839e9002d903c8f24420f0001cc83e214bd399942208f3c000aa3ae9002a0c1a800c239f8002043be000963072004015cac010c850f00204f3d0010a621b00432103c00fc552d3c98063c0010c838f819e4c8c400a43ae9791dceac4010c7bae001ccc1e000773271003e4e6e401047bb60032ce76502793af0001dce7c400f2303a86428882c01047fb30028c83b00068117180384e664006830720021055e00102582b002f0c9c614c861168530d8471f0db641600411f6d40103739b00409c86c006820f20030cc1e00102303a0000107e600ae39a900424e6e4000039f900204f3e000007f3b000012fe6190a6407004311d3a190a628b519dceb86190a618d001e0c1e00081347200000f1e614c862930028ccfa4008021f4001e4d1c400a3306a00288c98c00a33ae980384c068010339b9001e4c9c400f4303a001a07fc400004a7a00204f3c800b439e9]
  | 7 => [0x9138010841980060084c0064315e001f0810000883778000039e400001ce7000015cd800e6649000ab33c8005c1ce400000736000ce1d90000052da0039876400431967801e4a31c0079304c00641d5e002f5342801f2752c00441c4800864280001cc872000f054900000494e0061b0ab001d455200000939c00a318b2000028db00000e7280204542c006018cc003a9ce4002acc130000073da14c85e82003a87a400002067000e6149000c861c000000fec0018cc130016c7390010e304c003000a6002d8c8f00200e108000065a800399ce4002c0a8c000006f9c00002f4e00871ce40030ceb200000589c00f8658a00218aab004251c680000a7b000e1304c00318b2600400e661e4ea647000c231cc0000106d000010330015c7364006821bc00001427002bce72001c24a440000264e003c991e0000101100108799000f9209a003b9d5e0042996280000919c010e469e0086218f00002007000e6449000004858003b8e200018c7120014677540086304c0030112600210e72001e8442c00411c5600541d587c36d7a20021863600109658a000016a700000b33801ca609800f1221600001fa7003d0c65800c04c9800df304c00802b870018031300000ce5000007c9cab531d56001ccc11801e8752d04793ab800003314004321428014c609801003996003a8824000015b3800c04398000032ce0039816400208c730015067600000424e0000289b000019aa000e66390010c2230000037ac0032cea8c01c24408008e3acc0039862400000933800ee4478007301c800398264003c9b0280088419800004db60031906600001953801c6609800773ac80030182600180133001f0c3300000234e006591110042524580194c39000f13196000015270043186c8018ac3900084343c005e1d6400211053000ea4090007330480000112700001ea700200ae1800003d4e000038a7001800f300102649800002bce0051911800000973800e64f900073014882318e23001f088f0010c739000793238003c906b0031585300212962000003e4400863e070018c5d30000060980000789c004923a6000009d380184449800002ece0057119800000e938000078b000602a4c0080180d00000d13800c01d98007303c910874280852f4ea100200ae2c0000306600571cd6802b888300000519c00ab324800319024001f0b8f00000f33800a33ab0003a88e400400e648012c6378008f31c8007c99cb00424885800c0059800f23b90003418de002d0c8c00200632c00bd39c8b6559d5600001911001567590010c642a008038450028888c000e6609800733848004b111e00000d0f00000739000ae302e004118260018c7f200204632c00f9319600002d1b002d8c130000042b000003052007c910b0023c89200160636000ae39b000260e24571cc88b001c2ae6000003c4f0030110a00400c0500000629c007731bc00003e8e, 0x19c833000002bb40070304c006418de00001e47000ac3f9001094798000018370040cea580162609800c7614c000017274118ca8e801e2562c00a820b4003c9d640000187600190c2840000304e0086309a002887ec801e85c2c00963abc003f1024002b8c130015c446000ab39c8003009260023ceb2000ee438000ea304c005115980038d5cc001e84030007318c80064111e002b8eac00146586000a331b10a5e98c2003c47e64298abd0800004ace00002ce2001903b200000679c00db39c800861d5800000eb380000a86c000026ce004208a4003e5b82801086098e66022460047a3ab00000c93800e6019000ec39c80030052600400ea58015c63600000334e0032061e00288c6c00000c59c00813acc00550e1900001ec7001f2a81e190a5e8000842f45003c5ae2800b84090004420480057181800401c25800e64691047921be00872393000019ea001e87c20000054b600541118003f0706000008fb0007a1fc80039832400000c33c297a44080075114800519d6400001313801464364f24418b80000182d003c8885800c0039800003c48008a2f4500400c058000040b000c23acc00719ce4001ccc15800010f3800df39c8005ea393000018f3800f0639000f46c8a00300066003c4ea580000dab400005536b64118dd001dc630001f2ab30009647c000001cec001e4c92000e61090010022160057181a00001036800ee587800a831b00000291b003c8ea580000c49c0000811c00571ce4000012d1000005f9c000074c40074b2d00028ceac801248f900000254e0055a1240032cc68800ea3c900079324000709ce4001dceb000001093800f864100000431b791d43a4a8cea1d580110840b0a612f440015062f00000819e00732212003a9a1e001d483300104547800003bc400852f45000007560015e609800ea39c800003d0e003c8b058014c739000de65a400420764001d4712001e2a21c00004cc4003c99e4001d4772001b4cb4c007c31bc006198e400000716001467558000031ce00802bcb00000e7d0018644900063154c003a9826001d43b20014475600000583600003f0e5718088b8011c4498008e31cc00300326002d0eac0012a8e9801093a9600411ce40025924f00000559c00441fc800001a2200401c65800821dac009647420000183b001e4e72000004f9c00002b4e00851ce4001cc4920000000b800ab20d6000023ad002611f200000c2b4007c3abc003a8fe4004318ac000ee7570010c850f0a61af4300428c13001c4cb4401093196000016e7002f4c13001e4632c0000394e0081990b0036cc131dcea1d71047931ba00782185]
  | 8 => [0x220067559d6c00362e0046ae00152e00306e00066e00182700022e642f620032d4769d674b21a24921a7220c6700102e00276e0001ae0003ae4298e73190e70018e75e9d67318627002f6e00046e88439b0023ee00226e3a98e73a8767220327001bae5791273180a7001727001f22871127852f4e001d7800422e00172e78860e00446e3191270023ec000f6e208c6d00232e3181673a81e70028db8721940008ee8832d42b06270035ee31826700096e001d74752da2001dee3c93e77eb7ec0029ae7318e700346e00113c000bae5ea1948518e700282e531d67318c677ebe0e319527000c6e5e98e731832700272e0007ee00056e5b11277c36ed0021ee18876c00286e001a6e0002ae001cec000035000d2e000031871d670001ee0039ae00466e001134540c5b00342e5b299b00152783404e001d68000cae001826571127001de20024a700072e003bae00062e001d7c000cee852f45000dae559d640018f83e09220025ae001eee70912700026e4111270000393a8867000a6e41132751061b00432e559127579d670035ae00192e0034ee00112e0006ae0005ae53112730112d0011ae6da9ad00452e8511270025a20034ae7198e74318e77c2f4e5590ec3a9d6755a99b2201e78718e70019e73c9127220527001cee00182e00102c0022ee7518e70044ee6d98e70030ec220427001ce40027ae00431b0024ae220267003e4e000eee00016e0018e8000fae80110e5918e70012ae001f2e3189270009ae000030003b6e002a2e003c4e00042e00462e3818e70018f4003aae001b6e751d673a80e72210e7559d672200a7338c670030ad00356e612f6d00112a0020ae001d6e0032ee3c9d675711180019273a80a73a8167003bee410e2c0045ee0015ae00316e3a9c273a876400116e3198e70018fc0027ee6d9127851d67000fee883e0e833f4e7191273a876c002b2e22076700032e0036ee00216e00289b001d6a431d6700212e2200e7558c6c2201670004ae7c8c4e0013e73991276f9d67002cae80110b0002ee5b18e7221127000fec00092e0009ee5b1d670011a74210e7, 0xe2c0043ae57111b4118ed0038ee0011274311270012a700386e3b87623c90ec47a1ac5b20a23a83271f862c3c9d647a090e88428e0042ae301127002bee411e623c98e700182d000c2e002bae4218e7719d6700352e0028ae3188a73a91270030ae3181e73a992761af6c00382e62af670021273a85270026ae3187673185270014ae0000ee3a862700012e00052e00076e3a90e700366e00086e0018ea002aee79074e00424e001ce784a18e22062700372e5318e721876c00236e833e0e7512a7000dee3a8c67002fae0023ae001aae411d670021ae00316700222e3184270018ee001aee001b2e00003d000bee5c9d67002fee0007ae003d0e00082e00302e000d6e4118e6001327001d670010ee6faaec5b11a700400e20092c00002f862f5b301126002a1b39912c00106d0022ae00006e7511270000ae4118e7001c2e0008ae0011282209275798e700132e00322e5e9127000a2e3180e72e09276f98e700162e00036e3a826771abe7002eee5b2bdb3189a76d9d670011380023ad000f2e002f2e2c0767833aa20013ee002b9b0019ee0006ee0003ee00106e421d6700002e000aae0045ae000b2e3991240037ee000b6e0004ee80b8e75598e70030ee0028ee3811273d9d67001e6e003c8e0005ee0032220015a7003aee6f91273a89273c9d6c4721ad0011ee002dae000e2e3a8427002e6e51875b4110ed002dee0014ee5b2adb3c8c6c00162700456e]
  | 9 => [0x1c2e0edc02b9d57092e0a5cdfb8c77002e085c00c4017c2ae435c05b8eb3a0ae224eabb8018062e01dcb6b813743ae225c07b8c7390ee535cbdb8eb736ee18dc00d4f37003d71dcafb801c832e]
  | 10 => [0x2e]
  | _ => []

def C21_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 44
  | 7 => 122
  | 8 => 108
  | 9 => 11
  | 10 => 1
  | _ => 0

def C21_flag : Nat → Nat
  | 4 => 8
  | 5 => 0x1000
  | 6 => 0x2000
  | 7 => 0x4000
  | 8 => 0x2000
  | 9 => 512
  | 10 => 2
  | _ => 0

def C21_seedBits : Nat → Nat
  | 4 => 4
  | 5 => 13
  | 6 => 14
  | 7 => 15
  | 8 => 14
  | 9 => 10
  | 10 => 2
  | _ => 0

def C21_seeds : Nat → Nat
  | 4 => 6
  | 5 => 0x25240700190008010002001
  | 6 => 0x3e2c0040070001008400700200f24d380ca002401a819c017003400406b000f00e41820040002002c02600fc003008005008400210034010007c00d003c00700140010078002002c04c002205c
  | 7 => 0xe800400141418130803e0bccd860000800108300bec0bb86b002c0063400d000283b201a004502aa000a09cc01401b100100b4c00080b3000406f80cc00da011e00fc035000300bc0264004800500040014017000301de00580258029031d066c0008185001200a608101560016002400b80390028000c02080140218000400200f80028004c0178002031a0024000800200160018046001200c707a0009803e000c005001400020030000c0020001000200e401e0003000f03d800140dc010501b40090062004200240010004003700480038066000a0160004800902d200140ca0004
  | 8 => 0x78016003802b023801701be1b000240031174080000c00818fc1e0054c06c00502de00e4970003c02507400d600ec02000340ba006403b456e1b002700750024002004003e00ca16b001000b00840200112123002800400980c600d400e0ba61b000040270010035001001300cc01602ec002844413c010006602680030018238001e0f6002404000140b701560b8000400700082d30014039006405500700020034072019c004826e0750008005000804e000804600d2057007c005
  | 9 => 0xb005388693f04c0301c0786401
  | 10 => 2
  | _ => 0

def C21_S (s j : Nat) : List Nat :=
  qDirectStatePattern C21_initial (C21_countBits s) (C21_patternBits s) C21_patterns 16 9 (C21_slots s) C21_values
    (fld ((C21_records s).getD (j / 256) 0) (C21_recordBits s) (j % 256))

def C21_idx : Nat → List Nat → Nat :=
  qIndex C21_N C21_buckets C21_flag C21_seedBits C21_seeds

def C21_routeCodes : Nat := 0x4054000020100000000c000000000000000000000000000000000000002000004000000000000000000000000000000000000000000000000000000000000000000000000000
def C21_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C21_rankPool : List Nat := [6389402, 4340107, 7610079, 7756681, 6298792, 5255134, 6315658, 3157386, 3231130, 4288429, 3296152, 7367051, 6651032, 6373294]

def C21_rows : List Nat := [10, 28, 34, 49, 52, 66, 81, 84, 3, 5, 9, 6, 18, 40, 72, 96]
def C21_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C21_rows)
def C21_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C21_ori : List Nat → List Nat := qCompactOrient 2 C21_routeCodes
def C21_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 8) (compactCover 8 8) C21_S C21_N C21_idx C21_ori
    C21_coords 4 C21_rankPool s
def C21_F : Nat → Bool := certAt C21_Z C21_N 11
def C22_initial : List Nat := [0x1d1, 0x2a4, 0x64a, 0x928, 0x1430, 0x2038, 0x3807]

def C22_values : Nat := 0x3d38f0dfc30f01faa7e75f92fe41f887e11f83fe003438d0c2938a4a2838a00264a8af22a487e61d184e20b881e202880820088001d3870c16b4592963057c553052c14703da8e4a2eb0aa427e490020007db1d286ca0fd43a40b902800400080010002800800080010001

def C22_N : Nat → Nat
  | 6 => 12
  | 7 => 41
  | 8 => 31
  | 9 => 1
  | _ => 0

def C22_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C22_slots : Nat → Nat
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C22_recordBits : Nat → Nat
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C22_records : Nat → List Nat
  | 6 => [0xae9b20773eb9ed61747c299b797540c27de753c2b97d623c0c8fdd5d3]
  | 7 => [0x165f000fe013f407b78184f0347f5c16c067780defc209e06afc0d9fd305d025be057efcc6780bef029fa023dc092f8077bbc8ae027f716a781edf023be0437c073d8057d018de04d7c0bef8115f020be01bec0baf805fdc5d9e061bc057d816df]
  | 8 => [0x1955a95551d55509555115551555541555a155559555e1555515550555581555bd5550d5553d55581155bd1552155519555dd55549555015593155501555cd55501556025557d555e555501595]
  | 9 => [0x7f]
  | _ => []

def C22_buckets : Nat → Nat
  | 6 => 3
  | 7 => 11
  | 8 => 8
  | 9 => 1
  | _ => 0

def C22_flag : Nat → Nat
  | 6 => 512
  | 7 => 0x400
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C22_seedBits : Nat → Nat
  | 6 => 10
  | 7 => 11
  | 8 => 12
  | 9 => 2
  | _ => 0

def C22_seeds : Nat → Nat
  | 6 => 0x74b043
  | 7 => 0x1002001422d8c0a0030080a41300c
  | 8 => 0x5da80181f1080ad0bb003002
  | 9 => 2
  | _ => 0

def C22_S (s j : Nat) : List Nat :=
  qDirectState C22_initial (C22_countBits s) 14 6 (C22_slots s) C22_values
    (fld ((C22_records s).getD (j / 256) 0) (C22_recordBits s) (j % 256))

def C22_idx : Nat → List Nat → Nat :=
  qIndex C22_N C22_buckets C22_flag C22_seedBits C22_seeds

def C22_routeCodes : Nat := 0x10110000212000000a08000000200000000000000000000002000000202000001010000000000000000000000000000000000000000000000000000000000000000000000000
def C22_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def C22_rankPool : List Nat := [4413814, 5393547, 5389740, 2103655, 5458553]

def C22_rows : List Nat := [33, 34, 36, 74, 81, 92, 3, 5, 9, 6, 18, 40, 48, 96]
def C22_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C22_rows)
def C22_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)
def C22_ori : List Nat → List Nat := qCompactOrient 2 C22_routeCodes
def C22_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 6 8) (compactCover 6 8) C22_S C22_N C22_idx C22_ori
    C22_coords 4 C22_rankPool s
def C22_F : Nat → Bool := certAt C22_Z C22_N 10
def C23_initial : List Nat := [0x394, 0x549, 0xca2, 0x1261, 0x280d, 0x500e, 0x6070]

def C23_values : Nat := 0x1ee7fd37f80ff01de037c007779eaffcffb9faf27fe4e3c9c3930f07ee0e1c03b8006cf2d945b1c3478687dd0e1a0374006579cae195272786470c7e98e531b862f0c4e187c30b860f0c0017efaf77ddefb95d728ac0757dfaedf553eaa4d50ea81d4ffe9cf526fa4c3483a887508ea0dd413e827502ea03d403e8065008a009400a8004ca28a930e5200640088009000a0003f6d77fae9b5d06b80d64c2b5356a4ad0d595eb289646ac0d573aae51586aa8d541aa635486a88d500095250001ff73fd67b8cf511ca234c25ff4bb497612e925984aa493f527284d84970927124da49a4932926324c049049101201240041808209020201840208021002200240007ff8fb61f443a886f58da217281f743e487940e9217242a6854b0a121420280040007e80f541ea03b4073a0e701cb039507000c001400260048208801080204040208000c00141028004400848108020804000420082010001240240014001c0034006000a001200200030005000800080008000

def C23_patterns : Nat := 0x195556555595559555554554554554554554555

def C23_N : Nat → Nat
  | 5 => 1
  | 6 => 33
  | 7 => 154
  | 8 => 213
  | 9 => 28
  | 10 => 1
  | _ => 0

def C23_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C23_patternBits : Nat → Nat
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | _ => 0

def C23_slots : Nat → Nat
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C23_recordBits : Nat → Nat
  | 5 => 15
  | 6 => 23
  | 7 => 31
  | 8 => 20
  | 9 => 12
  | 10 => 4
  | _ => 0

def C23_records : Nat → List Nat
  | 5 => [0x610f]
  | 6 => [0x411dd3b4af56ded7a8f0dfc5c1a35bb764ebcb1c6e0ed9b6a9e57159ca016c7eead19e1cdcbac715b40905e09bcd80572fb4a77588e53608d2ae1dc0fc4b01f76bcceb254eb69ce99b96b35e911dc4e74c837b33935f16956e5d97b1b937e9]
  | 7 => [0x1977800025f70000a37e0128b574030e0a78000415f005848ea006e47f00001bfd800017fd008e39b6014876ec00021af8047334f00b5af5e00014cfc0001db7805c2b3d00004cee015f219c017923980002efb00712eda0178deec0002cdf80002577000030fa0171047c0315733800041df0000a57e0170baec000207d803299ed00a1337a01431a7c01d57f3800042df008f34ba01796e7c0002a5f803a37f3000033fa017036dc014cdfa80001cfb00b5807a0140e6bc0235967801c977900a4347a0000ebbcf4e8dfc0000563f00c548ae0102ffe800015be8050b2af007339f201407e7c000289f803d245700a4685e00cca79c0001ab7805e1df3003513f800baade402ed21b80005a7b007556da007e77cc0288e5d8039b7eb000048ee00bab5cc031576d804b415d00002efa00da27b402ddb2780299cf30000a47e0152dabc0316c1780005c3f006d5ada01451c7c000093f0052479f000071de00baa9e802ddce7803aaeeb006639d6000160fc000285f8000346f00af3f9e00ec919c0001b77805c3aaf00af929e00dec7e4000212f8000336f0000b27e0128db3c000203e8000007f00003cf60137056c00030f78037b26b007a6f760000b1f40001a77805bb7db000034fa007e69d400e4dfc80341a6d00003bf6000176fc023ceed80004dfb00005ef6011ed13c024a06d8057d02f0000aa7e00015fbc020603c804840f3000096fa0144ccbc02be075805a503b008f48ae00ded9ac02be036801d9a79000067de00d8c7b40001bb78056173d000049ee0140d8bc02d608f80410dd7006552ce017869d401a0ef580001b7d]
  | 8 => [0x53600652bca8000236009c60019600616005f60035600436a41b0776c200a90b5b1000566c56c2c5b12003160007600796009a600446371358f1b13a37500146005a6001f600296005c6007860000600a100016653133008f600276009f6007a6b83f000556000088e131c53f1007e600806002060068200426005b60081400565001b600176c57320054600286002e500576009160052600be63f1b37a3f10074600876bc1b300976000d6000b600116007d6b59c4001e6008210041673135817a4002260037600896005d60000900a4000486b57a0004d6001d6008b6007525a3f3002560004600026975a500926004f600086b5704b5a8000b00736c200136563f500016a2130009d60034600c66753f200336003940093600bc65f3f3008e60012600bf6a110065102681b2003b400036006d2002163d3a4706c23b1b4000c60047600096003d65d3f40010600c06c5772007f600805006f400886bcb9000b76009969c5f400066000a6bc82100b8000326008d6341b5000f600186807a5af7a2002a600bd66f624002e600456ada800000a002b6008a600c160033500662009463d2e5008c6005060038600776ad97500007007b600c765f3d4b5ad000483003f600156000e6001c6331050034592483bcb5000b96007c639134002c6000560026600986009e600a2000906004e60082673702001a600af22d135735a500516004065a375661320060600466003e6005d4]
  | 9 => [0xa9169263760a61360460095a60361067763f60761b65560085f6976086bc6b967a60260070069c63d6]
  | 10 => [0x6]
  | _ => []

def C23_buckets : Nat → Nat
  | 5 => 1
  | 6 => 9
  | 7 => 39
  | 8 => 54
  | 9 => 7
  | 10 => 1
  | _ => 0

def C23_flag : Nat → Nat
  | 5 => 2
  | 6 => 0x400
  | 7 => 0x800
  | 8 => 0x400
  | 9 => 128
  | 10 => 2
  | _ => 0

def C23_seedBits : Nat → Nat
  | 5 => 2
  | 6 => 11
  | 7 => 12
  | 8 => 11
  | 9 => 8
  | 10 => 2
  | _ => 0

def C23_seeds : Nat → Nat
  | 5 => 2
  | 6 => 0xe15fa7620e00807e01000802
  | 7 => 0x1200203e0070261370770e20010b703b11261401a87c01c07e52b02e07886f00e00b0070f381205301000d00801604701600401800401b001035
  | 8 => 0x550280260500c0990024ecf708d00c014010011633412095400804463cac1e808c479b717a0540300e92c01c1d80c8f4010710138f2004010d305804c048b40520323380103b09007812
  | 9 => 0x1d350c071d806c
  | 10 => 2
  | _ => 0

def C23_S (s j : Nat) : List Nat :=
  qDirectStatePattern C23_initial (C23_countBits s) (C23_patternBits s) C23_patterns 15 8 (C23_slots s) C23_values
    (fld ((C23_records s).getD (j / 256) 0) (C23_recordBits s) (j % 256))

def C23_idx : Nat → List Nat → Nat :=
  qIndex C23_N C23_buckets C23_flag C23_seedBits C23_seeds

def C23_routeCodes : Nat := 0x1050000003100000000e000000000000000000000000000000000000001000000050000000000000000000000000000000000000000000000000000000000000000000000000
def C23_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C23_rankPool : List Nat := [6576760, 6491598, 2177927, 5328540, 1076651, 2112649, 4202173, 5532311, 6375546, 2182523, 5381241]

def C23_rows : List Nat := [28, 34, 49, 52, 65, 74, 76, 3, 5, 9, 6, 18, 40, 80, 96]
def C23_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C23_rows)
def C23_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C23_ori : List Nat → List Nat := qCompactOrient 2 C23_routeCodes
def C23_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 8) (compactCover 7 8) C23_S C23_N C23_idx C23_ori
    C23_coords 4 C23_rankPool s
def C23_F : Nat → Bool := certAt C23_Z C23_N 11
def C24_initial : List Nat := [0xe49, 0x1292, 0x1524, 0x29b0, 0xe007, 0x14038, 0x181c0]

def C24_values : Nat := 0xf4fc7a6c3c38fe1c0f01ff80e3c00fe000e0fc707038071c000d4f86a7035361a1c0caf26570327a593c0c8e063f27178189c0c3e060f02f77569b8b41c580e2bdf757beaa1c54aeaa0714838a11c50002536115248949439260000fedf7ddbbdeddea4ef407794bbc81de00eefff7727ba81dd36ee8077303b881cd360529227248ffec7f6c3db41ed80f49077643bb01cd80ca485ff22fb017248b6c0576029b214d88a0c0500020000fff87db43db61e490e9206a482f6c17240b4905000276412b2094d04a58252612900908048082400109008080400820000ed9073c839641c960e00050002240106008080400820000c000290010800820040402010100006c0016000380018000480020000600018000800020000

def C24_patterns : Nat := 0x56555595559555554554555055155154555

def C24_N : Nat → Nat
  | 5 => 2
  | 6 => 27
  | 7 => 82
  | 8 => 118
  | 9 => 18
  | 10 => 1
  | _ => 0

def C24_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C24_patternBits : Nat → Nat
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | _ => 0

def C24_slots : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C24_recordBits : Nat → Nat
  | 5 => 23
  | 6 => 31
  | 7 => 31
  | 8 => 20
  | 9 => 12
  | 10 => 4
  | _ => 0

def C24_records : Nat → List Nat
  | 5 => [0x20df83803e8f]
  | 6 => [0x5631e00211f87803ba1b3007e764e00fcf23c01f9e87bf3e2d8e524542c2e0c45c640001e4f803ba6a77e7c5e0e00eed05c01d4c19bf3e2e8b7e78690e0104fe3c01f92a3b829172900735556003c33e001cd90da9201761003b22e2007a3dc40155131803f3e0f]
  | 7 => [0x13778036b09f006b3a6e006219f000b48bca0170f71000025fa00a48bac00c863e00001d77004b3ace00ea84dc01f977580160f7900461ef200da9abc00ec7b98000383f00804aae0000eafc000205f803a89b70070623e00965bac00012f78036983b00003dee008a45e40001fb7803f2fcf000022fa00a463b800013378036b4b7007b4a6e005c3de5f9f1687c1403e0f0070406e000081dc01a537380171179004122ea00009fbc01f9f0f8038913d000041ee00a4819c01dcd9b80001b7700006d7e00006fdc000093e8035a5af000000fea45c3da400ac33c800038bf006b603e00a645b400784bc8000373f45421ee20000f6fdc0b879c803f3e2f0075673e000033f80209e8f8000296f000053de0000eefc01f9e17803f3e0f004d30d600fcbd9c00008fe8038292f004d36ce0000d6fc0001b1f803596bb]
  | 8 => [0x39600466003e60007600750001666d13000066003260022500216001d62e1e37e5a1005168280100009005c600176001265654100656003a62d0c4001864d131006a6545016b0c0004b10063600136000b6001a6001b6005763513200666003c600026004d10000800362002e6006d000386000f6000e600496827c04542200526002c60028600546000a60029600096005210031600206423e22e1e46942200007701e00000669132001e674720401e20005633225007b04b0c1006b0786f00047600156004268278000106001f6301340036600402001c600046320c5000363a0c2003f6003a20027600586000c6726f01e0c5521e1000d6504e1000160070000226004060034600086005060026650362007e100116451e40059600486002a600146002f6]
  | 9 => [0x5460660c60061361e62e60860083e6036506026636326426009007]
  | 10 => [0x6]
  | _ => []

def C24_buckets : Nat → Nat
  | 5 => 1
  | 6 => 7
  | 7 => 21
  | 8 => 30
  | 9 => 5
  | 10 => 1
  | _ => 0

def C24_flag : Nat → Nat
  | 5 => 4
  | 6 => 0x2000
  | 7 => 0x2000
  | 8 => 0x4000
  | 9 => 512
  | 10 => 2
  | _ => 0

def C24_seedBits : Nat → Nat
  | 5 => 3
  | 6 => 14
  | 7 => 14
  | 8 => 15
  | 9 => 10
  | 10 => 2
  | _ => 0

def C24_seeds : Nat → Nat
  | 5 => 2
  | 6 => 0x201b02dc00c00094710074001
  | 7 => 0x2046000de65015001701f400201cc01100320410400004005a03605c003202b004b001201b
  | 8 => 0x11a7801402ea00c004b800500bc00040130005000a0008021008902a00a080228001004c001001400e0014b012603b0012004400280450002
  | 9 => 0xb8480506938
  | 10 => 2
  | _ => 0

def C24_S (s j : Nat) : List Nat :=
  qDirectStatePattern C24_initial (C24_countBits s) (C24_patternBits s) C24_patterns 17 8 (C24_slots s) C24_values
    (fld ((C24_records s).getD (j / 256) 0) (C24_recordBits s) (j % 256))

def C24_idx : Nat → List Nat → Nat :=
  qIndex C24_N C24_buckets C24_flag C24_seedBits C24_seeds

def C24_routeCodes : Nat := 0x440000222000000f02000100100000010000010000000001000000002000000040000000540001333200000f02000400400000040000040000000004000001112000004040000040400000221200000f08000100100000010000010000000001000000000000000054000040000000222200010e04001000000000100000100000000100000000000000004000000044040000022200000104000000100000000000000000000001000000000000000404000001140000030200000800000000800000000000000000000008000000020000000104000041400000001000000208000000200000000000000000000002000000000000000140000000000000000000000000000000000000000000000000000000000000000000000000
def C24_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C24_rankPool : List Nat := [241447241, 201441743, 134264107, 135512494, 272738604, 67252586, 206650832, 134330733, 270744941, 275982636, 206585296]

def C24_rows : List Nat := [17, 18, 20, 33, 42, 44, 65, 74, 76, 3, 5, 9, 6, 24, 48, 80, 96]
def C24_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C24_rows)
def C24_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C24_ori : List Nat → List Nat := qCompactOrient 8 C24_routeCodes
def C24_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 9 8) (compactCover 9 8) C24_S C24_N C24_idx C24_ori
    C24_coords 5 C24_rankPool s
def C24_F : Nat → Bool := certAt C24_Z C24_N 11
def C25_initial : List Nat := [0x3a2, 0x4d9, 0x915, 0x120d, 0x2868, 0x5070, 0x6406]

def C25_values : Nat := 0x1efebc3c7870ec1fd81ba3b7470e80dc1c37dbed17da0db1bb60367ffcf4d9c1b3036586ca0d937f26ce486b2eb65c2c3854f9a9e15366a3853f2a6e14bc293ed270a41b48028f85170a1e0fbf5df7bb7d74dae9a1d06affb5bfab3e56742c6857feafa9534297d52d0a455474280047447f74ddf9b1d361a6834c8a96dd2db25a34986928d1ffe37746ec8d1519b22edc5d10b15132a25d44ae8955126a247448b891112202414482090010222020402880410001fec3ec87a20bb2137426d8489090010001f503e207560ea81d383a607000c000c001200222044008281040204040006400a001120208040005900920064006800c001200200030005000800080008000

def C25_patterns : Nat := 0x55955595559555554554554554554554555

def C25_N : Nat → Nat
  | 6 => 19
  | 7 => 84
  | 8 => 131
  | 9 => 20
  | 10 => 1
  | _ => 0

def C25_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | _ => 0

def C25_patternBits : Nat → Nat
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | _ => 0

def C25_slots : Nat → Nat
  | 6 => 3
  | 7 => 3
  | 8 => 2
  | 9 => 1
  | _ => 0

def C25_recordBits : Nat → Nat
  | 6 => 31
  | 7 => 31
  | 8 => 20
  | 9 => 12
  | 10 => 4
  | _ => 0

def C25_records : Nat → List Nat
  | 6 => [0x112bd1e11c524a8043a4350083319601087acc021da4b8040263300875f4e00f8ecf401f8a1c803ab81d005128d20112fc3c00019eb802d23e5006e45aa00b28b9401c11ea8042379d]
  | 7 => [0x7024ba000001fc0001e1f8000325f0078287a00fc96dc0108c7c803f1f3e006546ae0000d97c01914a7800039df000028fa00a863ac0001e5f8000375f000034f6010251e400010be800012fd00844d6e00a227ac01c902e803998db008a843e0114979c01b96678000335f006e43ba0000d77c0149173803d349f0084713e0000e17c016cc758000197b004c31e600010b7c01f84dd800034df00832c9e00006bec01f06ff004224b700724bae000067ec000226f804518eb006d68ae00f0ca7c02215b3802314755b432cd200fce47c01b83ae802a146d000024fa00eac87c01650f680003dbf000072be00eab6f40000c7d8000403f0075456e00ea48f40194a2e80003abf887c577c000039f8020d5e7803c2337000040fa00a88d9c0000abe803222d7007e407a0000fcfc0200c5d80161479007e515e0001077c0195527800032df]
  | 8 => [0x246002e6007507c770000d66d6a1003d6003865b435003a6002060011688576000078a7410028600566001e6008b64613300606001b66513100831000160017600616005c600066746d12c134000c6002f600436004d60010600216722c1781300036600146001260019657314000f6001d6716d100626817c0640e18a6d100405000a600586000b6002850000800166003e600156002767c4d6002b60037686711750e000651002d681134000e6432b500086004f67e2c00072100136003060063628135006e1817f0000267143500006002960055600396004167c2450007600780003c6005360031400316230e5004e68a8615b2c2007d67c606007e0003b6004068a2c200226006415b0e5005060009600056001f6007c6005d600046002c60057600826402c5001a6006910044600009003f600186004a6002455413200036450e300266]
  | 9 => [0x2c65767c63f66060760460074d60360560860065560080092b61364360e6]
  | 10 => [0x6]
  | _ => []

def C25_buckets : Nat → Nat
  | 6 => 5
  | 7 => 21
  | 8 => 33
  | 9 => 5
  | 10 => 1
  | _ => 0

def C25_flag : Nat → Nat
  | 6 => 0x1000
  | 7 => 0x800
  | 8 => 0x2000
  | 9 => 0x4000
  | 10 => 2
  | _ => 0

def C25_seedBits : Nat → Nat
  | 6 => 13
  | 7 => 12
  | 8 => 14
  | 9 => 15
  | 10 => 2
  | _ => 0

def C25_seeds : Nat → Nat
  | 6 => 0xd8a809c0381b4004
  | 7 => 0x820c00071cf83600c05c21200100101000248a0080210160020050e3047812
  | 8 => 0x4008300018128040007405301cd005002c1020004002002c006302c00500081000170001000c11c820c00300040b201bc001003403000dc06c
  | 9 => 0x34e0008006137c8004
  | 10 => 2
  | _ => 0

def C25_S (s j : Nat) : List Nat :=
  qDirectStatePattern C25_initial (C25_countBits s) (C25_patternBits s) C25_patterns 15 8 (C25_slots s) C25_values
    (fld ((C25_records s).getD (j / 256) 0) (C25_recordBits s) (j % 256))

def C25_idx : Nat → List Nat → Nat :=
  qIndex C25_N C25_buckets C25_flag C25_seedBits C25_seeds

def C25_routeCodes : Nat := 0x4100000111100000f05000000800000000000000000000008000000000000000410000054140000023100000b0d000000200000000000000000000002000000022000005400000011100000302000000808000000000000000000000000000000000000202000001010000000000000000000000000000000000000000000000000000000000000000000000000
def C25_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C25_rankPool : List Nat := [5532536, 5381788, 3279789, 5515927, 5389774, 3284363, 2121338, 5459081, 5467257, 4328622, 5450375, 4349306]

def C25_rows : List Nat := [14, 17, 28, 42, 70, 97, 98, 3, 5, 9, 18, 36, 72, 48, 80]
def C25_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C25_rows)
def C25_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def C25_ori : List Nat → List Nat := qCompactOrient 4 C25_routeCodes
def C25_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 8) (compactCover 7 8) C25_S C25_N C25_idx C25_ori
    C25_coords 4 C25_rankPool s
def C25_F : Nat → Bool := certAt C25_Z C25_N 11
def C26_initial : List Nat := [0x7e01, 0x82aa, 0x8554, 0x10866, 0x11198, 0x2201e, 0x241e0]

def C26_values : Nat := 0xffbffebfef2fbbc9e6f0783affeeb5fbaafee2bbb7fe1dfe677e01de7fb7998dce6371fedc7e371e0dc66369fed678353e0d47e351e0d46635000d2f9b49e6d278341e0ce67b381ecc67b3198cc07b287eca07b2800c807b2000c46631000c219b0800c061b0078c0002fff5bff86ff5fbfaaefe01b9ffae5feb9552e3feb8faae2beb8aaae1feb8782c9e0b1ffac7f4b1f82c5f4b1782c3eab0f82c2aab0782c000a9ffaa55ea9552a41ea8afaa21ea807a8554a0aaa80009fffe7fe19f87e7e019c7826be09a78267e09978263fe98f82621e9880261fe98782607e9819a601e9800259e094f8251e093f824de092f8249e091f8245e090f8242009079a41e29050240008c07a2a1e8a07a261e8907a221e7fffdff777fbbdfe677f805aaee67ff99dfe66ff997fe6577195986555193ba64e61919863ff98f7663bb98d7662ff98afe62bb98a666219987fe6155182ee60ab982aa6033180005fe657e675f80571985a19939984ce6131984a1991b98467f9199846199179845661139844679119a440010e66431990a664211108004080100003fffcff553fafcfeaf3faacfe0b3f804aaaa275509aaa255508ffe23d508eaa235508aee22ab88aaa22910880021ff8875421af886aa21800855e21558840020ff882fe20af882ae208a8820a208088200202a88036200a8800a200188002200007e1f1f83c7e071f80c2a00040000e00028380a0002000061e01800040000aa8022a00850020a0081802020080001fe006000088001f80078000d8001e00060000e000280006000080000

def C26_patterns : Nat := 0x16555665595564558155a5565558555d5569559556155755595555551552554555055255455511542550554054555145445501515545151154155051405500515545450554150559155855515505511540545151054115005051154454114444511041580554154054414505040550150015

def C26_N : Nat → Nat
  | 4 => 1
  | 5 => 27
  | 6 => 137
  | 7 => 334
  | 8 => 400
  | 9 => 158
  | 10 => 9
  | 11 => 1
  | _ => 0

def C26_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | _ => 0

def C26_patternBits : Nat → Nat
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | 10 => 7
  | _ => 0

def C26_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | _ => 0

def C26_recordBits : Nat → Nat
  | 4 => 25
  | 5 => 34
  | 6 => 43
  | 7 => 43
  | 8 => 34
  | 9 => 25
  | 10 => 16
  | 11 => 7
  | _ => 0

def C26_records : Nat → List Nat
  | 4 => [0xf57a06]
  | 5 => [0x1c6642222003cd5639d8e1320665aac526198ab1118003c95639d0ab2f067aba9ba19b0ab3106003d5e23800ec7087003b1b81ddcca558a749907c8800f46907003a9b61c00ee558e7aa84b819c6da2203003a5b81dd2dc320676368c81800f16a87003b9ac1dd0b6558a74b787c0ddcb1558a]
  | 6 => [0x1ecf1558e00001385f1e00002ad447800e55597c7000009811390038d18641c000030052e400ab5098c73a9c0b1558a00001aea11e00003a5bc3c007c278a7080180461138003a5b4641c0075381ac1c00e96f19070017eab14b800001feab3c0071b68b81c00e36d1f8380000ec322e0024c8c297000002f852e400bc2c0a5480156a02f8e00391c0dc0e0055a84527000e36d0f89801cae06987003a168ab1c0000001447c007d2788b080000a7113900001d2da1e0078b615638009444888c801d4ab2f8e00001dc9c1e006c32556380000759917000009c318f003c1565f1c005e220526400004b8a5c801d4da558e00001569c3c0049a20526400cb55888d001d0dd558e00254c83e64005d2c82c6400932c0a5480156a12f8e0000126297200719907cc800ba23059c0017489111955a847022300000331567800be5a838c80000ea6c8f0037d56a11c00002acc13800be3b9195000000073af00000009c3e0055a84ee39c6da361701801c6da2d0700361569d1c000025044e400f15599870017aab2f8e75395b46c0600772ad423800004a0a5c801a4a12e0700001b09c1e00003a4c8b800ea702ac700000c011395fad1562230000031d567800ea6eb483801dcab4e0e0036156a11c004a11844e000e96f1c0380000ef322e0000156a13c00003c5a43c000055a74f00000ab2fce003095622700075369ac1c000055a78f3a9cada3206002ad425b1c00742ad3a3800802688b080000c9559e00001eaea5c005d16444a5c6da321703001c8dc2e070000156a33c0074b78b41c009343888c80000ee558e000014c297200002ad3e7800005598d700000ff559f000019aa13c006c2ad383800ab5095c7001dad8558e6c2c556a11400003b9563c00e96f1e85801e0df558e002f88c0e70000037d383c00005598670017c4614b80024cae2252004a16444a400e47137038017c7b232a000018aab3c004ca30c83800ed6c358380000ab529e003a9cadc0e00003195679c6da3e1cc1801d4df558e]
  | 7 => [0x1642b3600002504440000050118a801743811100028070222000000012458000074b80680000220b2900001569c0e0000264b634000036889480000ba2d8d001cc8c0e50bf5e918443c00007195c680124381110003a9c664180055a84701800001b089480000ba2b8d00118701650003f934447974b21c088180000007e160038cf264180000190769800000030cb001c6e0320c00001409d0e00003a5bc080000500a4a0008c3511280024d1022080000280ae3400005e2cc3800009b2d8d0000000295e00002a8be3400004b888900000a4438700001c6771a000000104c400641c0894000008e159400000620e5200001d452a400ae55a8430000092129400000002a5e0071b81580800003a08948017ebd111000001fcab2a005faf45240000071918a80000931490002ad42010c00002ad405400005597cc8017e92111000118441650005e0e0524000d855a84080126351110000009e294a005a2ad421800461c039400000ab4915003a9c0ab02bf5eac8440c0000490a4a00000922b8d0000100225200002ad2054000023045700000fb11290000000a92c00002f0f0340000498a4a00000fe5596002b1405f04005ead15618000000280b000004614ae00001c65b1a0055aad4218f87026888e800003714a95d11870221e0071b68f20800ab508383000009a2b8d5faf4ee221200230e044a000005d21c380174761110002b1569d0c00002e8be3400e9331946000009223150024c8c222200002ad421800002b895100000411129002ad42480c0055a85421800ea7035810017873149000001c6b20e00002b0be6800001c0a5480000220ba90000132571a00002b53a1c00461c0a540017ebc149000001b45f340074b78ca080076230894000c85c039f00001d4d41a000000058bc000057a843801744607130000192ab2a000038db034000043894d8017878148b0000126870e00002550e1c000055a70300000ab4e86000008c165600499c0444000ea56990600000ac301a0024c9629200000251121c00461b8394001b0d65082002f16e292000000d044a40046188a5400000a04387002e91022085c268e04474000074990680000992f8d00000702252005ba48444000005d2aca80192ab5086002fd68ab0c00002fc56a400001a05948017477230c000012822240000285381c00ea70358000000e32a8d00000ec295200002f0525000c15e0a480017ebd129000000009c0e005e0dc524000be23088880178461493002e8b022140071b68b8080073230a540012431071000000c8295c005fac0444000005d1dc680000ba4e87000000000640060a48444000461b8a5400000be11120030974222000490dc52400000498a49000003414a900000802952005d118524c000000244b00000a8308d00001185f3400002f5565400e56eb60100124872b820000158613400003a9a43400001a039480000e56f8d00001565f3400719e4d82974771c088480000220da900001569d0e0055a84061800ba59118300000952f8d75395c0dd0000491181c4c0000000ad780000004a1600001569d2a005d2c8ee0800ab508883000005214a900001645f34007bba8c83000bc598a42800005c2720000012a2928005d0882c400000230ad70008c34112800001cad81a004ca30cc0800461c00d400000540ca000000521652000038cbe34000018845480184ad1110003a9ca64180075395b4080000001198ba9c0ad56010000000b92c00230c41ca000000029cb000003114a900255145b0400003a4cc340000438acd80000e96f0d0039568ab0e0071b68b800000029889480000942c8d0000192ab0c00002f08c5400c956ab0300000962e8d00001405b1a0075381560800004995c68000000621600001589c0e00000013058000071958680000c95587, 0xba59038280000c25595000012a571a00672ad4218000055a3ca801c6e06d020000174292800002490e1c00bf55888880000351129002b558a10c0056ab13a18000055a84380000ab509500000009c2c00000d452a400004a96c680000bb559500248ae3714005f0c41c400094110588000003712a9001f09e223c0000001785800ba5c088800000ba231500000e629520064ad1561800001f889480000a611120000000ba2c00002ad3854000071a1c3800009d4e070000156912a00000c852a4000000258b001c6381110000008c0e5c0071990b83000005698c6800003314a9002547022200055a85381800003f8a5480000b3159b00254ca3e1c00002b5461c00003b089480174351110000012622240000001485800004b22c380160ab5086002507022200000140529400ad5617cc80156a1380700001f4295200002ad422000005d2c83801cab4558600001d2641800002548c5400003206530017ead149000001c629280055a84e01800001b8ad48012622071000000d8295200278e0449000007216c6800003e14a9003a4ca6418006c2ad420800ac55a8430012658110a]
  | 8 => [0x2e8025800000d32002e9641c00220caf00000e4c800d05d160000072c800001db20000004c8003814ac259201cb8008a019c002b54058000012b20024844580052112c0033c56bc00482331002e88c580035112c1c0880ea400bc1494000000ac9248707070000042c8005d0ca3000c844b0000011b2000ec1cbc006523310000020c8000037b2001cc52b000bf5e96000d444a524480714002f89058000021b20021452bc00ba5d162591852b8000025320019070c4b84d01a0002b51e58004614b1000014060004b243100280445800000b3200000cec8000003b2000001ac8ec7011290038c905800001bad002e95a5870221129001c052bdd4e5330d002809058000049160011852bc00fa112c002fd1e5800bd5596002640658006c112c5fab44448004808af002740670007314a90000000d800004a16002dd245974381110380e044a40000093200254705800001f2d258e052a400461c3100000e2c8000014b9002f5565400000a3200248905800ba50960025070595aac5087002f524580000123200230067000002632000008cc8003e072c002dc56bd7438111200000d4c80046072f000a406bc00c14916001a41cbc70381129000e044a800ba59160019452bc00e307160037524588c38112b000e052bc000015af3b0e044a400005d1700001c660006411315d1dc4434000015b2000006cc800ba07160038cd25800c85016002e9585800ab50965faf44448002914af5d118445400003a32000cc44b0006c072c5b9c044a400004032002c806708c381129001983ec4003814a9000e044f000002331001c04abc0000433200395b034007f112c0000000c8000022b2000006ac800e30196001b88cc400960c9600144329c000040b20012c2cb0004b15af0013052bc000050160008822bc98381129002b1405800001d321b8881ca52422071400254905800940b1600254765800ad4e87000005ec8003e112c240c41ca400001432000004ec800007c32000e04abc000042325bad04a6c00924387000004cc800bd12af002b54258004f11270000092c8f84d1121399c044a400fd5d1600000d0c974b21107000dc44b000001132000007ac800dd2332001cc52bc00ab5095000882cb0005c14af002b1245800ac2f9a3e1c044a48c3811280000012c800ad4e9600281405800a01c1600001246000ab5087328e044a400932416001d844a4000007b2002c84a7000e35a16000dc1cb17ebd11100000070c8000024323992c52a400a03816001bc52bc00951116000dc52bc00702331000a444bc00000bb20000078c80025072f002f57458008323310021c0670000016b20000052bc00fe56960013c1c9c00bf4916001181cb924370712002e88c5400a00096003457a58004614ae000003ec8006401b1002481c5800ba3816000007ec8000014b000001f6c95aac5095000881cbc00ba1116001cc44b0dc381129002e890580076112c002e96858003714ac0039524580029072f000012a6000da019c, 0x5fae84448702201a96e8e044a444150729002d140580095071600258e058003701ac000c41ca400ba1c160000200c800ad49165eab558540092381600399245800b812af00000e0c800000cb2003095a5800000432003157458903707290010806b0000049174915c1c34000007320024c4448000009b2000d41cbc00005e16002fc4ab0000034b20024ce05800b45216002f0525800000532002480658004611310000052f40087089c00000d6c8964814ae230881cb9742207140000040c88c29112e00285405800ac15af000882ca5784b149400001f2cc004814af00285245800005216000003cc800005d160000106c80093071600000d8b400931a960000000cc000008b2001181cc55aac508600280065800bf58162e134448000003235002d04abc00370b2c1c08802a400dd14af00194769c004b14af75395c03400ab50860038c445800dd233100001f2c8004601b10000006c8005728a3000a402bc00bd56961c0882ca400ea48162e0e044a400924916002d12458003e01ac00234225800922b8d00001405c003714a90038c7058000000b2752b4cc3400a549165d1cc44480031072f003255a5800001732002b520580031072c00150068c004600b1001201cbce622072900248025800bd5016002540658000014b20000174600038112c001901cc4000023351b8a41ca400650ca700248705800ba01961c0881ca400004b1600254b634e646112b0000082c8b84d0720000003ac8004f01a7000008ec8005b1da300000ecc8963714a9001b006b000381129001188cc400e55d1600000dac974b7111200001266000ba3b8d002801c58000018320000036c890381129]
  | 9 => [0x7064b738320600d908802c8ca0e641807322e00d90006ac95811644c1c322400d90008cc44422640014b200131900070cc003864bf5e966e839900000c8f870640039b60005991701cc800006e00073a001219000b8d800922c15073239921900044c8ca386400003b49038b12070c8007066703832001a5900108c8060364461132001219af55a58ec7064002332000a5795806c8e670641801b20180990e02cc8000e6cdd243200375b12044c86e0e640601b200095900000fcf203640e00b2003e5907006c8440e644d11320000df0381cc8440e5e000cb201805900006c800007070073232921900002c8dc22644d0732002e8b12c90c5c003647001b23801590e070c8e6225838112c001c1b12c90c8440364000033240397adc4ac8960e640016b20000e007c06c8a20e64001c361c01d9210e0c8000e660e01b256a84b2d0e0c89629643811327500d902c06c974222c38073200089f13406c8000e7c8424327c9c190001cc8ec38640001b600001a0e006c896295edd01b200195b1c070c8e60e642d01b226121917070c8002e646501b22308988003ec800226c48073238065900004c80803640000363300d900044cc003b6400243600280b37444c8e048645c11326e8e190dc1cb00076640001b33808990000ec800056465113200045912090c87022520025b6]
  | 10 => [0x38321c3224321132073201b2003300360032]
  | 11 => [0x7f]
  | _ => []

def C26_buckets : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 35
  | 7 => 84
  | 8 => 100
  | 9 => 40
  | 10 => 3
  | 11 => 1
  | _ => 0

def C26_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 0x800
  | 7 => 0x400
  | 8 => 0x2000
  | 9 => 0x1000
  | 10 => 128
  | 11 => 2
  | _ => 0

def C26_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 12
  | 7 => 11
  | 8 => 14
  | 9 => 13
  | 10 => 8
  | 11 => 2
  | _ => 0

def C26_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x46828051c8456e0c
  | 6 => 0x223240250016db0090900313198770040b704500305134b01904201109586000508083081d01601a02b016004012019009002004
  | 7 => 0x4e20d001003012dc07581b06e008010013b45200200c6f29927239e0120500683800533c021b61181483483f046a243180300801013487a9c51c1212c002038020302700f43a0070023481f903028074008090381880a006070014028090081c4040948e70a0188a9066164268040020100080a
  | 8 => 0x304815052c005001400703c401c050d25384b801b00040c4012801900040d8088401300640eb000800a00681c4843804d00780c402400080f0832601b400302f60ca045413700380bf000c0af00260bf007e0b9000401405c40598260008001805000c800802440080060026011402d014c0110054005000a08201c8058002000e002400300300080004036009400f004c062003800f81780210294005000400500060310004013014801500e802b
  | 9 => 0x3980904fa08600180a407a006002a83036e09d823838c06c0910338dd001600c00080fc0d6011008806447e060815c010016009001008804e0060098330006007
  | 10 => 0x14105
  | 11 => 2
  | _ => 0

def C26_S (s j : Nat) : List Nat :=
  qDirectStatePattern C26_initial (C26_countBits s) (C26_patternBits s) C26_patterns 18 9 (C26_slots s) C26_values
    (fld ((C26_records s).getD (j / 256) 0) (C26_recordBits s) (j % 256))

def C26_idx : Nat → List Nat → Nat :=
  qIndex C26_N C26_buckets C26_flag C26_seedBits C26_seeds

def C26_routeCodes : Nat := 0x15440000311000020d0c002000020000200000200000000200000000202000000110000154100001213000000f06000400400000040000040000000004000001011000014054000011400002132000080502008000080000800000800000000800000002022000001140000144440001200200040b0600400010000040000040000000040100000100300001444400001500000210100008050c008000020000800000800000000800000002002000010110000154540001213000000706000400400000040000040000000004000001011000005054000005040002132000080302008000080000800000800000000800000002122000011540000150000000320200000706000100100000010000010000000001000000103000004044000144540001031000040b06004000040000400000400000000400000001013000014410000011500002020200000f04000800800000080000080000000008000002020000001140000144440001021200040b0c004000100000400000400000000401000001002000014444000000100002003000080604008000000000800000800000000800000002001000000010000004100002111000080306008000040000800000800000000800000002113000011010000151140001220200040b0400400080000040000040000000040800000102000000454000000400000202120008070c00800010000080000080000000080100000200200001104400000054000202300008060400800000000080000080000000080000000210100001001000010110000201200008050c008000020000800000800000000800000002001000001500000054100001013000000e06000400400000040000040000000004000001011000014010000050540001011000040306004000040000400000400000000400000001213000015454000045500001020200040b0400400080000040000040000000040800000122000001510400004510000120000004010c00400002000040000040000000040000000100000000410000011410000200000008030200800010000080000080000000080100000200000001101000011400000213320008020a008000040000800000800000000800000002010000011044000114000002023200080304008000100000800000800000000801000002001000011044000040440001032000040902004000040000400000400000000400000001012000015000000110440000220200020d06002000100000200000200000000201000000203000000400000040440000321200000d0c000100100000010000010000000001000000102000015000000100440000323000020c0800200000000020000020000000020000000020200000000000011044000033320002080a00200004000020000020000000020000000021000001140000011044000022320002090400200010000020000020000000020100000020100001140000004044000032000000050e00010010000001000001000000000100000010000000400000010044000212000008040000800000000080000080000000080000000210000001000000015154000001200000080c000000020000000000000000000000000000001000004100000104540000133000000506000000400000000000000000000004000000011000001410000114100000031000000106000000040000000000000000000000000000113000000454000101140000130200000a0400000080000000000000000000000800000002000000010400001154000031000000080c00000002000000000000000000000000000020000000110000000454000012000000050200000010000000000000000000000100000010000000041000004444000023320000000a00000004000000000000000000000000000001000000444400000444000002320000010400000010000000000000000000000100000000100000044400015000000001200000080200000004000000000000000000000000000001200000400000015000000000020000090600000010000000000000000000000100000020300000400000014000000020120000090c00000010000000000000000000000100000000200000500000010000000030300000080800000000000000000000000000000000000020200000000000001000000031320000080a00000004000000000000000000000000000021000000100000001000000020320000090400000010000000000000000000000100000020100000100000004000000020000000010e000000100000000000000000000001000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000
def C26_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def C26_rankPool : List Nat := [134300012, 235158857, 134331818, 167822638, 268584270, 272644529, 170930544, 236988719, 67323341, 235061548, 168018219, 67256747, 67157354, 33735981, 33635657, 201409966, 134299980, 268648812, 100910477, 201506090, 167984585, 100941257, 100712812, 268680586, 33669419, 234997134, 134497741, 201605451, 134267308, 100810153, 234964334, 100844909, 33800651, 167855438, 100810121, 201475470, 67157418, 201409902, 268517804]

def C26_rows : List Nat := [1, 42, 44, 50, 52, 74, 76, 82, 84, 3, 5, 9, 17, 33, 65, 6, 24, 96]
def C26_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C26_rows)
def C26_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C26_ori : List Nat → List Nat := qCompactOrient 48 C26_routeCodes
def C26_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 9 9) (compactCover 9 9) C26_S C26_N C26_idx C26_ori
    C26_coords 5 C26_rankPool s
def C26_F : Nat → Bool := certAt C26_Z C26_N 12
def C27_initial : List Nat := [0xf24, 0x12d8, 0x7103, 0x8449, 0x8892, 0x1201c, 0x140e0]

def C27_values : Nat := 0x7fdffebd7f55ffaa5fc78fe23ff103f7fefb3ffd125e4fdf274f9127c1f9e0e0eb7cf53a7a5f1d0e0e7fb73f9399f7ccf2e670723cb91c1c892e40071ba78bd3c4e9e2707112785c1c1e0e070700037ffbbedfdd6f6db7765b9afffd7df6bdf75e79acdfd62eeb073513da892d40e699774abba4ddd22fe91774839a01ccb6ce4b631edb8cdbc4496200308b3844dc224e014300017ffcbff3dfcfefe4f7f24baf1dd47eea0773fbb9f1dcf6ee7b1731fb981dcbf2e5f172e0b96e5cb62e3ff71e3b8f05c47ee2397103b8805c3f2e1c1701cb8005bff2dfc96f3cb792593f2c9c162fcb170587f2c3c1611cb080583f2c1c160dcb06c58172c091603cb01258072c0015ffcaff257c92adf154e0a9fc54f82a7b152f8a97054b62a40151e0a870540029fc94f24a7705378299c14ae0a4f0523828fc146e0a2f051382880143e0a1705080283c14100a07c503a281c940e1a010500027ff936dc996e4cb626439311c980e4bcf25e492c1c940e498724a39241c918e488724401211c900ec806240112004900044b6224010f248200408e2040100007fffbff6dff6eff6f7f93bf76dfb26fd4b7e81bef6df326f9037bedbdd2debb6f55b7aa7bd52dea06f3db7981bc52de216f1037449391259124b6d95a24acb615edaacdb54492952548b2a44d5225a91254014a0004fffa7ff93ffa9ffc4fb6a7b6d3db49ed94f6c2736d35b49ad84d4926649312497d94b6ea5b6d2db296d84b24a552529b294594a25a512527b092d9496c248012094900047ffa3ff51f6c8f7d47b7a3db51ed88f2c4792a3c911db68e924724a376d1b248d49466fa336d19b28c92462ca313518968c49460022e4915248992446d22269112c8893440021d250db28690432ca19350c92854d42a5a15250a0484db426ca11b508ba845b422ca113508968448420a2102508108401420020801020080584024a012100308009400420011000280003fff9fcfcfe5e7f273f819f40cf20677db3b819d40ce7b67303396c1c52ce236710b38839bc90a5b04f2420000fff07e4837d81b6c0cf6065b0320018000bcf05e582f25179209420480a2400100007ff43ff81fd80fb607cf03e4a1f240f6c06b602fb016dc0b6c85b602c0216000aa40500027b213d8098004b7025b612d9092c049202430120809000440020901018080003ff01ef80f6d07b603cf01e5a0f2c079383c941e000e0006800336018300c0406018300010000700030c018100c00050402800124008b80449022401090083004100204810200808040202008100006920304018000b6004b0024c01240089004300208010200804040001180086804200206010100800036c01b000c000480020000b000500024000e00038001b000c800600020000a000480020000a000400018000800020000

def C27_patterns : Nat := 0x25556655956655595165159156055695595565159156155755599565959556455855599565557555a556555755595555551552554555055255465515544550554054655165455514544551054155045405495515945551514515141445511144151014195059415505141150154045005156455515145151444505115415504540545951564556155455115405451510541145451414445051154451111444410544111014185055815505441490518145051014104540550114015

def C27_N : Nat → Nat
  | 4 => 1
  | 5 => 41
  | 6 => 315
  | 7 => 947
  | 8 => 0x528
  | 9 => 481
  | 10 => 18
  | 11 => 1
  | _ => 0

def C27_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | _ => 0

def C27_patternBits : Nat → Nat
  | 7 => 7
  | 8 => 7
  | 9 => 7
  | 10 => 7
  | _ => 0

def C27_slots : Nat → Nat
  | 4 => 2
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | _ => 0

def C27_recordBits : Nat → Nat
  | 4 => 25
  | 5 => 43
  | 6 => 43
  | 7 => 43
  | 8 => 34
  | 9 => 25
  | 10 => 16
  | 11 => 7
  | _ => 0

def C27_records : Nat → List Nat
  | 4 => [0x195c798]
  | 5 => [0xc01b004259e68c000de694d0140000e4461180001c8d787006f34a8f06000061f02640000c662cc8000118786100255206ec00000606f06801d6c3e044800017c45190075b03781581b7b3d8e080000e0461180001186e610075ba78106000065702680187c0de0c0030327419800606b7363000c5e057c240187c0c94c000018ec0990071a2a6342008ab3cc7800181ad9d0c000010e78610071b58630a00d061f02240181bc49cc000018fbe19006f2126842005c230dd8000008c39708034181bc0a0000212f0c200e36b1160c00008ab97080001bc8c23]
  | 6 => [0x5492a8f4600c0dbe002c015d94224c8038b81b38b00606debd1600005f912e40000c0d79c8000181b69b00001708cc60076b3c57900109771a74003036f750b00003037c3600002551f8c0000aca25c8030378b79a0060600749400c5e043c640181b349cc8038d1576a90056270be1a0000455dba40000c0dc4d800017e5f2d00001408fc600e36b0561c0000b340078000166840f004619e95c40000224d3e00000ae231c803418bc08b0046a1ce5c2000061f02640000c0da4d800009536e50061f036f3200de695821c01c5dfe0518000181b39bc0dbe4f253000c0dbd9e6801819f9d0d0030367939900001e095ca0000632de6c0000c0dacd8000187b31d00425e6dcc200005725e740181b74ecc80000c047e30000230cfc600e36b1821f036f63a541801b8cf1fe4006b7036f160000604f76401a0c0d6d48022d0e72e10000303733600003c141940181ab4d8d0029f3450070071b58ed1a008aae0c78401bcd2a2c98038d1567aa000018063ca00de2551e8c01c68ab991803ad81b30b006f34ac70e0000425dba4019ab7b1c3e83035d9e09de695b8c70a000071b583c00ed5c22f0803037b929a00003037f3600005717cb40181b7a80980000903778006f23709460000604f56401c6d64545801b89547e100606babe53a0c0d5a6e2801bc84b1d18000000b31f007021cc746000061f026c0000c09d2d0022aed15e10061f03663200006f22aac015c9d3b0680379a5798700606de543200006b6cc3c0000c0ddcd8000188c09b00001808bc600c0d58e8680000c2e08d8031f8bc09900606bb3634000000388bf4181b7c9450038d1515a30000001703fbcd2c258e0c0181adc95c00296b831a5007034cc70e00ac2f912a40109678ff16f212ee732100002bb2e3a0084b3cc7c00181b7a0cd00303007dc30000303637400c0d58f46400b8370eb2000018caeb900606de883200a9254d0940000c0decd8000000ad3d00425b8c7c200c5e05cc640181b71d0d00341813a4a006f2123f4600ae4e912640000b7c98e802b0ea44a9000018068cb81aecf24a6000ea6fa2708021cf272e10000302887200c0ded22680000c0dc0d803036f840b0062b027a3200e32e1168c0181ae9d0d002a5354a8700002b8ec5a00004612b8c00004a9a328021295346100003027eb40069a30ddc00196c0decd0000095236600606cf2534000056118e40181ae9e8c80341813d49005711269700000606d46c0185bea28c8030366929a0062f03273200de45a1e8c01c5c0d6d480001d9b79b0046e12dcc200c0dee4e640181adca0c80379a51f8700003036f360084bb9cd840181ab4dcd683036f9389006f212636200c0dbd8a2c00005c0f7300000b845e300003035b720084b707f840000005f0f802b92f44990000303793600c0c00f52401c6d643c38000181ba9b000012a90c6000057d12e40000873031803036f6e1900561126971bc84b718e840181aececc800015c9d1d002551c63c2007639113840000c0a0dd00317814519006f212c14600c3e064264015897af868038dac7307000017063ca00c0db8f46400008ab734800008c34f80000212c0c600c0dba6c680181bd4d8d000015c44b900561dca04a00c0de2cc68000076a8328022d0f6e6100425b8c1c2008b43dcb84015c7622548034181b30bc0d5a6f273000c0d6e6e64015879a5528000199c09b00439dce5c2008ab3d41880181b7af858034181b78b0056270893200e3455828c0000ac2f968000166939d00003256f37a0ce606de0c01c08b43918000181aaba000014068ca000071a2aac0000c0db0d803035baab8de45a1edc42000074b026c00008c3031803036f939900606de7434000059a76740181b7c94d003036f2e9900521126970000061f027400cf4598f80000187c0b9, 0xc0de8e8680181aac9dc0022aed60e100606df3b3200d0606ce2c010e72b1f0803036e800b00606de7a3200d0606f62c010e7739b0803036f31990062f03253400c0c8510640181b7cd8d003036f349a006f212f34600e045a1e8c018ac0cecc80296b845a30056212ee53bcd2bb9cc14015897a24c80212ee6fe1000030366360000461418c0000c0df4d800018b911d006067e7a32000067ede3c0095479a30803035d9799004559e2bc4004a9b88b9001bc4a9a12802b8be44a90075b036f160000606f0e80000d059878000181b41b00702350e4600e32e0c6940000c0de0d00379a58d8700606bb3c32000056112e40000c4a25c80303273a58000017066ca000062f026c0000eb5987ef34b168783002e11663c20000455418c018b90a24c8000181bc1b006f22acf5400005657cb401bcd298ca8030321419a]
  | 7 => [0x606df370c00c1e06aa640181aec94c802b8892a1800459b8916981b7c9e421001a7c0dbc300000c750300000296be26008b43db8ac01bc63a5478000181bd8a00522788930000031d2ac0014f9a35810019ec715af004599e2b5e00e0699400c0000698f61000012745c700000dc45980000606549c000090a0c50000000b71d0000290bd26000049d131c0000c0d6cd0000158141c000015e8b7e00003a8b2e0014b5c0ac780000ec37380000234a06000005fa70280000a418ce000000050c3000014054820000520a87001489e4bc4800016e2e9c00606df0f0c00002f912d8000062a81800001529a8a0000342956000002e05ec00181b7a4430000000344d000029acd271677244dccc0181c0dbc3002b0ee4a920000296ea26000056eaa700000449a63803036fb7868b43db89556000045940c000c54aa2d68030781ad9800001165d8e00ac4bc3c240000a32f49f1f8316878d00002b0593800c2e0cf4940000001f2680001092ec7000028ca02e000049e131c0181b7c8430018a9531ae00425dce6680000455acd80000006064803037bb78600002b93a1400c0dbc2c180000449a6300001486e1c00606df27080067b1c04bc000062a858003790915940000001523a0000284a90400ee678ad7801a6c545ad0000378c526008b254c6b80000c0d18d00000002a4d0000000669a00de25516500000c0cee3800015c761300002b1273800c0d5a4e6378ee73254700001098036000035d156c00005417a4c000000744e8000148459a000028c8b3400002551ed80000b7280b80001569d9c0000001473a00002bccd0401489e2f8900001c0629300003408b6c0072b1d40b800000063248000181a21a000017e6e70000037cc70401a0c0ca110022d0e502d0000280563800c0d75cc600000ce18e08000148449a000011269900000001450c00007522db00000cd31b80000212a17e008b43db8d00000de280b800012845a7007018aa01e00005604870000000538e80000b831b8000022aed6c00449a43d180000c0a81f80000a145bf00002b0be26007737d2ab800c55022d680000fb31c100002b25d3800002fd12d80109771b9a000000081cd0052d2a8b2800b7c84c62401c087280a000010e72c700606dee60c00006f25e280000a4cc0500379166e12000025e56500000606dc680000006f0e8000158449a0031540635c008a244dd18018fc0dbc3002b0890f1800001a663820000530cc70000064a55800250c74aa100606df280c00002f940c00000de150e0000181a41a00606ac91320000230dd1c00c74aa3d68000181a29a0000176a060000043940fc00f34a9b97001e49531ae0000112568e0000520ba700000669b9c6f1b8c74a8e0000290be2600c0d7678100181b3c843001b8c74aae000022ea06000de45a1244000084af5b00000002b4d0000000619a0000606cc68000066255800236dc4aae00606ba1e3000004fcac70000060a5580031f81ae9800425b82b7a000060ecc280000a44f0e0030b83ad980000170635c00003cd2ac0011684b71a00000a531c10000380a02e00a5b4cc6540000a5b149802dcc74a8f00001702c6000aed5912600095340fd7001708b15ad0000292bf2600d0606de4400000023e480000b245bf000019e3a8400aed2112600000c0af5b0019ec70f2f004252a637a0000524ba7001a584b1d680000cb4ab00000378b92600000029a740000e36b8980000002ecd0000200637000002f512d8000063255800001ac8ab6002551c2b5a000025916fc0000348a26000015c9d090000270225000003c940c001c68ab4c8800015c721c0053d82951e00003b0d2e00181b7d983000016e62930031d2a685c00c0ca24e94000050225f80000b831c100001e29560000033518d80000a7ae8980000c15030, 0x4252a3f5a0067b1c7ebc010967a81f000000084c900001708b5a00002f916d80000602818001d8892a3400001809560000071b5808000080a55800000cf31c100002970026000052e4e7000004718e38030b5d5f1200001368b7e00ae4e8a824000075281800000b831b000001be8b7e007739540b80181ab494c8000181b38a006f34ac70000002bcc70401465e97490000095343800002dd2f1400004e8aca0000060a2df80000b845b6005225ebe0400d0606de080000459ea38000000005000606bb370c00e32e0563c0000de4c45001dca0372e004258e955a0067a2c56f800004c22df801a68b31bd00521126e300000224f31c0000ac4b4500237094aad00001f68b7e0084b052ab4000072a8a080001bc9c0a0000001533a0000606de20010e63a816801a6c531ae000038d15260000604c71c0000d0225b003036f9299006f34ac704000062f02180000c5e04d00212ee6e3400001125d8e00005498a4c0000c0c01b003036f93860031d2a8b5a0000424f51c01589c398480001bc5f130000000909200005be48280000c0d08d0000148849a005217c6e2400000037a740183b74001000008b3a48000030b67140000260c7040000a3224d000012831a8004398aa05b81aecf24210000000226480000ea44b6005198e951e00002c8c7040000ae3b090000158849a00000014b3a00b7c8612180000de45898000000b31d0057122893000006f2004c000084bb9b0034181ab110062f033c0c00a42f9124400f36e255700000002acd000019e388400003bd2ac001524a8fc7800014c459a000027c898e00000029474014b678acb0017c89373400001caa08200003b52ae00000de370e00379096391005be4f251200aed217c480000600fd8000010e62b600001d4637000c0d5a6e14011672a81700001bc319c000014e6382008733d40f8000000162680001adc0b600002b93a380072b1540b80000c09ea380000c74fb00000303284e00000028a740000ae150e00001095e360000381162600ac24514600000a3150e0000181a19a0052d1663300000002192401819dca12800011567b600002ad27380000606de3001bcd2b7048000069114c00673036f0c008da5522b612ee73255580212ee732b000019e2f840000371171c000000172680001c0729c0000178a0600062a2cc6d000009f9d050022c9545ad00683036f0200c0dbd2a180000c0ba9b00000ca50300000212ea6c00003151ed80000a44bc50000095463f000012a44611687b3d2ab000006e296080001bc849a0000001593a00007021c68014844950c002bb565f1200455dad368008b43d2ab4010e77281680001bc7513006f34b1604000068302d801bc84b70c0000158988a0061707670c00004594ac00000c5a263800015c449a0000001cd3a0000565cc70016f90a24300001bc5e930000379a026006e3052ab80000459a64000016fb30a000012a8f5a00ac1a43c6c0181b74a03001a6b831ae0000212a07e000030056c000954598de800008b31c7000029eea2600000008d3c0181b782c30000000d1cd0060f03670c0067a547ebedf2163a54000000d3463f0000290c5260000606569c00000043a4800012584c80000001661400de695dc080000a349ce000018bc08a00606df250a000031512d80000ac878e0000000b91d0034cdc3a80000053d16680000ae398e000008b2a4700002b08b340076ae056b8014863a54780000c53438000019e2b840000314c6e00000c09d130000000bf1d0000212638e00c0b1d2ab4011567a55a800008c31c70000112548e0000560c6700000001f66800014d998a0065b035632000056074700000b72f8980000bd31b800003792d140000562287001096e31da00001a5512400439caa07a005f224a8d00000a3370e00000005043, 0x6f34b090c00c0dbe4a18014b4a98ca8019e6315c000000d23a980000001cb3400006725580017cb244ad00002dd2c14000053d7c4c0000b722cd000011577360000001483a00003954b040000c09e9380000ee50b00000112638e000052d16680000b749ce00001bcb38a0000182638200ac2f83c480000ac078e000015c9e1c00002dc89340000605b91c0000a5cb4500296d345940045940915a00ae2243c60000067a2df801e4e5502e000018aa56185c1d7678100181b7b4c300000b815b00000302548e00c0dbc021800004495e380001a084b60000001583a00000014b0c0000c0d5cd000010045b6006f12a632a009e3cd2ab801bc4a8fc7800016f910a00002b0bd26000042576d80000006f8e8000181ad980052d8e951e00d05be4a080181bdcdc300378f34a8f000019466700000254cd040000c0ca53800016e988a00002127490000043942fc018b908784802b8ec2a12000012c638200003092ac00186c0dbc300000cd5030000029a8c34000025484c000004496e380000006e4d0000200896c00de3052a3c0000ac224c000014b2e9c005727491120000534c6700181b7808300000b8503000001127a8e0000606aa6400000037a68019ec705af006f34a2b06000071a2a440000de49ce0022ab815ad00002b0543800c0d7678180000de604d00303213a2600606df273000005703c70011687b3d6800009b31c1000014e8b7e0000606aa680185c1dbc3003035d9398000034b004600c2d7512600000c0d60d00001096e4700606df2712000053e004c0000c0dbc50000158591c000021cee6c0000002c2740000ac370e002b891451800001889560000052cc670000059231f8000181b29a006b703284400c0dbc0e180000c0d6ce0022d0f4c2d0031d2a545c00000028c7400009e48d4002bb21449800002972f1400eae06de1800ea34879bc25b8c74aab00002788c8e0063a54c6b800ee4a98d7000000031cd006f212cf3200e0459403c01a0c0d748802b1380f0900003788b34008d43940b40000c09763801228a34c6000023e9560000046d40c001096e33e3003b981b786de6958e950000005457c4c00cf638117800008f344700606ba8a3000004e0aca00000678d21000016e319c0000251094e00c5e06de18000063a5d80022d0f4dad000019e2c8400c0dbcdc1800c74aa256802ad37938900002dd381400003152cc00185c1d54c8030366908600002dd67140000002b874014b62a2c88000148968a000029ea02e000052e622801bc84b1c6803215d4498000030356340000003b324000094225380380ee500f0000297093400005ba12680000de2ec9800014f319c00003037b0c00de33c56580000e06985003419cb7820061706744c00c0dbc30180000c0d98300000be34b800000019292000066ade2800cf628ad7800014f5e93003b9cc965c000052d7a4c0000c0d74d0000134802300606bb280c0000002ae74012763a5570019eb815af00001b8898e0000606966800005f18dc000009522b0000030b5b380084b3d8eb40000a64c8500000c54c30000023695600000560ba7000008733e4000018167c800001405d82000025486c00000005d8e8017cb2372e84b3d8e955800a5cc4c624018bc2e0c3000017e731c0052d8aa01e000033c7ee74181b7c840800013a44c70000285273800001a43d3000009e2263802973162820000000a3860000561e67000000023248000152479a006067f280c000069944900000c0b15b00000c54db0000018e9e6000001a449300000b7370e00000951fb000002cf661400c5e0642180000500fd8002df214586003b9cc955dbc84b1d2a3400006999a0801706315ae0052d8a63240048a28dd180000e345898000146968a000014063820069ae116b40196c0dbc30000000a61d, 0x2e116fc0000de174e0000146319c00606dec70c00d067302b400006b1a1c00000006dcd0000302749000c0d6e4260014897a2430000181b79a004f1dca05c00a7cd12a080000ac088e00379168791000018a8b6c00d055a6e0800004a9a1761707569b8500002dd2d14008b43d40b40000d018dc45a1eee732b00003388b7e00aecf24a240091449a6300001599c8a003b9cca05c00de45a1e340000a5a80bf1f83aed38000606de1e0c00006f34a28014b98a2c3000016e9d9c0000298ca26000000380740000b94b45000018134c800002dc5438009e2f912d0000062a89800279097734000017aa06000001f83d300000c0dbc380000dc50410071b58d30400004e1131c00dc4aa2de80000bd45b60000302744e0000521405c0000a43a898000181b7860056270ea0400003cd40c00000c0af9b00001095f3600576501e1200003b112d800005c0e180000158731c00002912738000052db8738f568b24480012a8f1fad00002b0a02e00aed5a5e2400006b23db00001a05030000030b7114000053d8a4c0181909e928030781b78600425b8c75a000056eac700000a91a0e00000b95030000029289340000000db340000a6cf0e00001462e9c00002bb2238005f1a43cdc0181b7a28300000ca45b600000008b92000051a1268015c76244900000892e47de45a1e951a000049d410400008aa55b00380c7500f006f22c912200005f83c70014696af41002349545ad003a9be1e5c00006f11268000094281200000b81a30005225e6e1200c0dbc5618000080281800000ee50300051a5a5d12000028116fc00c74a97570000185be8a00606bb3c1200de425dc4400008abb5a00303569406000029f31140084b718eac000000550e801b8951fae000012a6382000034d16fc0000a4cf0e000010934c800606ad37320000606cc28000084b15b00001c6d61300224d2548c00002f8dce000004a9a180000131512400002b138140000224dd1c00004aa2df8000181b39a0045a1edc5a00c0d5a6e180000ae224c001dc9545ad00003037b3400aec943c6c0181bdc84300001092a47003719e2b8000a931d2a3c010977399680001813d2500701caa02a0000230a91c0000006ece803418193b40000303278e0000002e8740000c0d9c3000014b2a1c0000001843a00005617c4800004599a380000b81d30000012a4060004a99c56b801a58b43d68000158978a0000296893400ac31d2a3c00008b289800212f34aad006f236951e00c2e0ef61800008ca558003035d9e18004259e2b7c000000292740000b72f49800010967c800561d41e2400c0dbe78180185aecbc480290690f1b]
  | 8 => [0x5621e75a6c74ab00000091400000d8d0c2d75cc7001465e93000029874009545bf00002dc7400002cd0000019d40008e0149005b9a674018ab71d000011728008b05c9002f4dce8000072cd003703d340000065000520dc7400001dd000616f6740185ab1d00000ad340000ac200051a1e75b8c74aae0062c3d340000a91d00244bb340159371d001403d340158159d0033474e800d31d430052c30740000665000224a91c01a56e4d0031cd1340185a59d00370173400af0143a5b4c565c0000635072b5941040183c0c963b1d2ac0000067d00060cc73400000ed000002b074006303cd0034cc70400e64dc3000008f4001b45043b7c84162801a7a41d84a5456fe370f4ab00052dcc7401b8734d00635132400f34ab00053dcc7400ee31cd00458c73400000750005221e74006e0f4d00002dc780000365000001a540009515c30068016e8008b0f4900002154000a0374363a543cc000d61fba00000ad4000005f3c000018af001c0501700003032401464a9d0060eb07400c7504379b992ac001814549000029a74000031ce00719a674008b374900424dd25dce64ab0002551324013805a900001874000a005c30060cad3778c74a8f003152ae9dcdc4ab8000017cec00540f4d0057696740181ab1d003954104000019d000000014000007cd0a32f4304c00006cd0004b416a4000058d00045a1f240000a59e00001192400c74ab200244a934015da09d005fa787400004fd000150053400007dd0004252b240000b71f000012f4000b815b000616ca740185434900000094000000bd0000014d4001a04aba9bb1d2ac000007a50005321e7400002a4d006f2126800d850430052c02740000045000000cb40007a15cd0032870e800951a4300174053400d315c38b43d2ad801485f1300225132401283729003594b0c01c1a31d00001f54000004cd000001ab4122892a4700000dd4378951597aed583c70013c84c9004a12aa4008905c900518047400530f4d0034c690c016e059d000021f400181014900604172401c1a59d006f212740148979d0060e967400be44b6000002d4000631d4d005744534000011d0000003d40014b988a000007f4001bcae9d000036540000055d084bb92ad8008b4549000016940010e504300474a935b8c74ab800001a34001bc8b13000005b4000003250001e817340000a7a0005feb0740156a31d48a28a91c0181ae9d002e0570c000073d0006803ceb79a54a8a005195e74008f1fc900280050c008b0c490070e9074014b879d0018cc7362d0f6b36000035340012f44c90069d132400008cd000000eb4001814ac98b3b922d8013117290033c053c011e5043001a43d35e6c74ab0000012340013c31cd449403d1c000041d00046917240000753b005ba78740000d85000606de2800003550004f8453400d31643002f964e8013105a90055a4e7001004aba006f18e74015d104d000023f4000004d50004f1410c010f4dc3c2e0ede6800001ad000001c74000cf15cf, 0x570a874000062bb0031404e8000008d000003bf40013c734d00280310c00a003c300001177c010e5049ac1403c7000c74ab1001b8a93401a7b71d004a056a4014f039d005b9227400002ed0003cd370d8e9500b0000023940012505cf005768c74000088d0006064f1c008903c98b43d2cfc0146059d69a2c56fe906e0f1c002450d2401469e1d001443d3400b244c90052d2a74012145c9000018f4000be4abad2b1d2ac000f231cd0049c0534010f45c9000029080000070d000001132c00007350004f0513400ee50430053c56740000875000001894001cede1d0022cc7240000803cd745a1ed80100013a00520167400cf15c300616de7401a0c0b600616dc762cd648b6005b98e7401bc9e1d00001a140013c1d4d00001bb422c9515b00041816e8014b459a0031d40e800002ecd00001d4f2df210f0a00652967401a7a31d000020f4000e5504d003b92ce8018190c900001a94000dc03cdde31d2a4c01d0ab1d001b875340000125063a552ac1166315c700001411001213a29002380f24000020d06c31d2ac000c731cd00425cd24016e7d9d00245132401090f4900561cc7000bd57ba00000974001c2a31d003703136912f0f0a63a5408c001813749004c45ea58a6315b800001394000a148c3000013d4000e62a4d69b1456c000ea0f3a00002e47400006e5000001df4001a015ba006b9450f0b83942700001a74000dc6e4d006043d24010f4c4387a44dd2001580f1d000021340013103a9002f804e800ee45c900000df4000dc69cde3d5a2c4d8e9503b000000fd400148009d006061f25acc5503000680dce8014b699dc2e06509c00b2124300359172401cce09d002c8dd34000021d000479430c01380f4d00245172400c74dc300001594001bcd28ab7b1d2ac000e634cd000007b4000e646490056016740000d2500071e967400542a4d00001fb400063014d0000131400000344d7331d2ac0000025500043cbb34018103c90018c0334011569c900002927400c50f3a00524507401274acd0043940fc00001150001b84534011448c98b43ddcd8014c1c1d00000bd422d0f4aadc2e0ede2801589b9d00002132800ea4aba001483d3400007e5000459410c008e15c90000113280000545000001974000002a4e000037880013803a9000008b4000c115c300228c734006305cd004003ce80181b79a000006140014ba59d006f12274006e144d5f2243cd800be373a0034cc73401280129000007140018193c90000213958e951fb000000014401a75043003991724010905c9001b8bb3400006e4e005be9674000017d048a28dd200000bf1dc0d5a426800006450004bc16a400dc48cd0022c5924014b319c002e52ae801729b9d006730324012f112900001411400ed69cdb7c840428005415cd000028c7c016f31cd00752dc74000085d000000d340000024d000699410c0185ac1d002f52ae80148a41d0031d2ae8014b0f1d00400e8e800c5373a6998c57040156a41d0043d2d0c000012d0, 0x40016e800951fb0005183074000044c90018c573400005ebb0069d172401480c1d0060e13240000505e0069f032401b66e4d00370dd340146489d00002907c00c531cd000028c780000d350002450b258e95013000258570c012144c90069cbb3400bb4aba0069eb0740183a31d000015d400000d3d000001eb4001a0013a0043ccd3678c74ab0001a4573c018169c9006043124008b31cd00000c14001bc039d005200474007415cf005212a7401bc011da5a2c566800001bd0000012d40006715cd00562ac7400c72a4d0034d410c009531c10051a8c7401165030006067924013403a90051a5a28005d0c4d005bedc74010f6e4d002e032e800bd0f3a002451524016f5043003dd410e36c74ab0006ba967400df15c30000155400000d55000606ac6800be37380034cc70c01164aba00000594000002750005b8dc76df21370a6e31d2ac0013731cd00518ba7001deab1d9e2f83ce0015d929dc0d764268018148c900001d3400158699d0052e627400eb373a006f2ac7401a7a59d004fc10758a8b15b60000017429663159c005347474008a44c9005183c762cdc4ab8003ec570c00c515ba002450f24010f42490000085419ec74ab063a5430c000d317c300358c73400af1c43004f0453400e66e4d004f03d3778ee4a9384b712b1c018100c9000015340000086d0005612a7401096e47000016f41a6b815b000003036000ea373a63a5416c0019c15c39bc3d23200185b39d005227871b89515c1004dd132401bcd29d87a44a91c0000a5a000000e7400148591d00314c6e0012f03a90037137340000d15000000414000c5504300561227779094a9a0052cdc74005d144d63a5522c000c745c90000149400148699dc0c9e431c009545c90034d172401586f9d005603c70014b639d00706847400c531ba002fc50e800d32a4d48a28dd1c000078d00052278768d2d0c0a000014b0c000050c300174bb34013c594d00150593400008a5000000ed400148449a001a4173c008b31c700001294000007450002f83ce800af2ecd005be9074018345c900000134000001750004590b2400007fd00000117940156a09d0072aac74013c2ccd0022c712780d650170022d1724015dab1d0018c313400dc15cd005226e7401bc879d0055a4e740000a41d0033d410c008b014900000734000951d43006058f24000031d000616ce2800c74c43000017af00148039d00224dd2400f34aba006f26e76b8912a1c0057690740146639d00003787b036f909a000015f41dc9515b00031540c00158011d005beb0740158731d00001136000a048c30000075400185a19d001a43d31dcd65030aed203c700114374d000016540019345c9005bd17240089014900150173400004ed00046d232400000cd0a5b14564f0b83ab1a005de967400c75030000033542df21158a002e00ee8010900c90049da7340185a11d0000031400181c0c900435b934010f84c90051a6e740116503a005487e74014f609d003a4bb3401da84c9, 0x3700535dce64ab800359410c005403cd0052d227400005ad0004240f2401bc679d00315172612c74aad00281410c009531cd00000ff400000de1f0049cdd35acd315c2000019340013c44c7001b8b334010948c9004f1172400001550002e048e8011e87c9000000540010967c8004245724010f2a4d002803d0c000082d000000c7640000a41e003b92ae800e64b43002bc570c000093d9006168c7401250f4f000009b4000001b50005225e2a90890f1a00726967401bcc19d0031d2ac0007a0f4d00606de740198ae9d001a43d3c0100373a00519a674012f1029006f1a674016eb71d004f4c734008a374d005ce8c74011b4b43006f3787400631a4d005b92a74015c2a1c005be422c000003d000706b0740000ced0005ba1e740158009d0049c3d340146159d000018341dc95373800606512400892a49000023b4000bd05ba004a03ca4013c44c9aed59cc7000b8013a005baba7400005143449503d1f036f908600002054000890f4900002414001bc6e1c00234c73401dbde1d00560307400a000c30033c173c00f56e4d003a856e800ee50300000051400162a59d0000237400067014d00519cc7401835043006f0dc74010f48c9000004f400000de1d77358dce30b83ae9a00000f538010015ba003712b36df214a8a00002214001a584c90043cc7357c6e0f38000014190000000d0004b40ea4011b4aba0026c570f8fc18b1300000ef40005d03cd00150033400e42a4da41403c7000006fd084b3d2b200000d03b00518dc7401090149003b9cd34011c84c90062dcd3400f7734d00001c5400137504300000814001d2de1d003719f3400c51fbade3712a7000c101430049d8f340146009d00605cd24010f44c9005b804740175a41d00616907400d32ecd000024f3801b4514300000bf400183a41d000028c74000051500044d1324014b059d005828c740152639d000033d4000be15ba003052ac00000335000001176001a76e4d0071e82740148159d00359450d2a3e15b000254c70c0181ae9a0045930e80164ac1d0022c5724016eab1d63a5456c000893747773992ab8007405cf00254590e913c0f1c0000117240185c1c9006150924016e3a1d001e8053679371128003052ae800000d5000254710c008d45c9a5a54565c013c124d005180e74015dac1d0064290740000a59d00359430c01480f1d000011f24016e0f1d0000367400156a19d5f2c83cc00125014fa5cc45628014b9b9d004f83d3400cf15c20071f82740000334d003b8b334012715cd00001674000c747c900706dc74016e731d0031cbb34000052d00052c5674000049d000399132400a537430052c0474000053d0000014340008105cf003718f3400d31c43005b80e7400a715c3000028c80012131cd0063f032400630f4d0000053400000ac9d00000d140008a4249005618e7401164dba005ba6e7400000dd0004ddb93400e5504300459430c01589e1d0069e132400be05ba00003807400d345bf00706ac74000044e5, 0x6b31d40c00000dcd063a54dcc0000072508b35940c00000615000425b93400000350489b83d30013745c9d060642d801bcc29d006045724014f879d00560d274009517c3006f0027400c74ae3a42f83c4c008b03c900001f140012805a9004243126bb210f1c00002dc8001bc0c1d006b9410c01972b4da3174307000df014300562b07401ae45c900002132400b815ba0060edc74000031e600000e34000007b50004252d26789145470052d8a4c0000ae1d0031d1326bb569e1c004f9cd3400b21d4300707787400ee52c30000125400181b7c90069cc7358e950b30000014140000010d0002812b0c0000ce50001b8493400001950000001b4000006e4d0000340f0000084cb000016140008205cd000001f4000692a4d006f34e740000d0d00073eb074010969c9003ec050c00000e508b3b8dce0000089d0003713134016705a9002f456e800006bd0000030328000084d8005be13274ec74ab00000375400000005a0060d132401bc059d005218e74016fa31d003b9bf34013784c90045d2ae8006317cd00000894000002ece00003b1421cd6503f00425152400003a5084b1d2ad800951fba000036b40016e159d00002b07800002a5900244ad34016703a984b1d2ac00181b786006f1cc7400ea34ba0019871340000c0e500244c73400e64c43001a07f362ce64ab000001b140016fa09d00224572401372b4d00398dd3762c74ab000000014c00f3374d002c8050c013131cd00260570c00bd013a0052122740158371d00398c734010984c90053c04740191ab1d000016d418a9515b09e2243d1c000018d000001b540010963c9002c8570c00dc00cd00000e54001a503a9000036f4001833a29005b80274000031cd006064b2400c505ba00535cc7401819bc90070140770b5d0f1c00000c7830b5d9e1ce3f075c4c0069014f004dd450e1ec74ab0003a804e800004dd000230752401bc6e1d00254bb34017ab71d000003f4001c1a41d0046d2ac0014b039d00562702a78ee4ab800003032c014b319d0072f7874005d15cd449b83d1c00cf0f4f004361324005d0f4d8b43d2ac0015da11d00521cc7400004ad0001e03d340000803b004861324011643c900398bb35dce64dc10034d132401bc159d002245124000045cb002f12ae8008b00c90055a967706c74ab00000250a800001e50c2e0ede18011645c9005bd132401819427005600e7400007f50006150b24012515cfde4592a4c0000d4500031516d8000050438b25522d80000895000616ba7401ae31cd000020940019cab1d0055a887401bc0f1d000002540012705cd00399410f5d1648b6004fc16758aa015b0001d03d3c010967c90065b0324013c6e4d000021d240074014f67a5457080000705000250a93400af0cc30019c0f34005b0f4d003a816e800c5503a0052e7877032890a7006168874014f699d00000b54001bc4a9d00001b96401c7a19d003b940e801dcc0c948a28dd180000cdd000000bb640000ebd000000694000f752c3, 0x4d4000540c4d00425dcd801a505a90017403362d094ab600670050c016e0c1d00571227401a72a4d00254a93401a54c29004c517252a8b15bf002240324018bc29d0017417340000a59f00000d74000002650000005740010f504300002034000a015c3001b8c734000031500000357412a6315c100001cb40000027d000518ba74000056d000228d33401096e49006f2de74000079d00031d2d0c00890c4900000a9400000ac1f]
  | 9 => [0x5bed0000941a66ea09103d0d743e831c0f403c02a185c1c90a01e84585741222ba10f4ad00004a83580541ece6a0b901500006680012d40005d9ae61d500037283b92aea5e1ea10f63d00007a8000174c00a0a0910f502e862843c57426ee6a00087da730ae80ac17417607a0d363d00f02e834c0f424202a00005d19e39a800003412a0ba12c01504502e843d2340160ba1460c1d004f2880129402802a1834ad015862860d8f40561ea05d0c4d000ba8001ad689207a00053d0908ae869c25434e1ea02b15d05402e86cda7400181921e03d0489ba85741740005da13737500c062824523400007b4953750451ba6b1c7f4000e6a13c10506c31e822857426e2fa06e05d0d3a468001a744011ba0009bdad8e9e84580f41a61ea0ee15d00002ed47523403c01a13c3750002b280001d400007a3b77350001a6871f827628e6a0e648d0a202e80003d592a2b860000518b255d4dd8f42de6ea0954ad0e082e80001758006ea60090d17734e812c17421e1ea0030150b787a843cdd436fa7a000375ae381e8000179f0b6f3b1b87d00001e9a4431400018a18505d000246d0005744002bb5370f500031e89c05740c62b9ae64ad000476800307440002b4001650488b281b83d3400e6b4005450370d28000016b4e95a0c702507b34e869c0f40a002a00b00d08b43e80000143062ba0dc4ad0005b8ecde1f400091a60703d00069ed000dd4367a7a000a31d000034e16ac75220ba00048d00031e98002d4000c1a16f4ad00000ab0140542426ea13769d0a58ace800714000c7a0009e5a0052cecf017402002a00079d00022e4a280542901e3a1800d00500a80000f867802a00087d100002e8036f40dc02a185ae9d001528002b0740095ced301500016680003d4e6e2ba06e0f50006bad001b1402607a000d3d100062891c05400002ce8a14506382e80f80541cc07a1ae03d08b00a800131400024a06e15d06c34e84c457435c2ba0000450000a2869cdd41162ba02b00d07700a8399cd438fa7a000105003806804017400002a20025d0639ba8314574000afa0dc4acd1f01e831c31401602a1dd87d063a56834d23412a91a06e03d00037e8000014b4ed3a0e6374d, 0x9515d0005be8ef12a75228a920000550015268007540010fa60b03d07306280021f4000e6a70f05d07701e86bb4f400095b41505d0b78ae800803400007a00069d300520eabc3140c62ba00015e10025680003d9dccd3a03e15d00000311b831418e1ea1214ad0000629b1d8f4001099200c1da63a46860c11435c98a00000533802e869d8f41121e920015d39e0ae8228dd400000ae00005b6380a800378752a02a0008a509e07a68006940300ba00015e700003422c5725ccc7a13701502807a86b9cd400095a3c1ab1d8780a84843d421e18a00059500037269c005412a01a0912a4d371ba8000c734008aa20069d0d38628000dd9da62b873705d06982e834d2b412202a08605d06b34e8001ed421295a00005d00008a82001742de02a0d603d0001328250dd40019ca0009bd12802e80018f6b4f0fa0500f4d8b39a869c174001a7a0be0f3a4a24682243d41a6d3a13c63d0003ee869c05430602a0ee73501580a800001701407a0d30cd0c182e816405403007a00701509e34e85581742dec7a10f48c98db1e834c3140009ba000375187c3e83d8dd422c96a1371150006ce843dcd40001eb4008b5a6b2821c841741dc9ba0003a500000a80014d40000bd40073518b43e4a44a94001b1a0000161000ae80003169ac2ba0950c509e39a6a543d41dce69ad650500011e80007f400109a10f03d00100a84761f41641ea13c0f506385a839817403002a08a0f5067a5680783d405607a0d3125079b9a831c5740002bac6e07500f0628001dd6a1e38a13e3750c19ba8001a76a3ad3a1ae69d0002569b9805434fa7a1a54ad0628add0005f427895a1a773500012685bc1741cc1ea1374ad0d700a8000c7434e2ea10f69d063a55800113240000a9a715d08a43e86c58f4306d3a18190c9698ae80012345e6c7a00050434a81e8398dd418e95751669d00007a8c252b2401a7a6700f50c187a80019f42bb563a000153]
  | 10 => [0x500150735048d04ad00c5003d005d0005a005187d063d00f5015d0375069d00053d3d0]
  | 11 => [0x7f]
  | _ => []

def C27_buckets : Nat → Nat
  | 4 => 1
  | 5 => 11
  | 6 => 79
  | 7 => 237
  | 8 => 330
  | 9 => 121
  | 10 => 5
  | 11 => 1
  | _ => 0

def C27_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 0x800
  | 7 => 0x800
  | 8 => 0x2000
  | 9 => 0x1000
  | 10 => 0x800
  | 11 => 2
  | _ => 0

def C27_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 12
  | 7 => 12
  | 8 => 14
  | 9 => 13
  | 10 => 12
  | 11 => 2
  | _ => 0

def C27_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x10e02e86b947205848040203
  | 6 => 0x531f857459705c00605b9370121ce13b00500e02205946b02c00301f1b34650121262110f409d0928dd0370950031a90038c400f0b00150e60550010cb00100100102203010500401e00201600d00a09b8b20130020110248a801a01583503b00102000600d18505100500901506e00100e00611a020
  | 7 => 0xbaf0120e21ec07a31a00203e11b208ba021f5300c6005b4605208c002b4200e00b274b3f003b0602132750a01503c77a00d021bb300259510c2cf50900603b10b7dd07e0040020212280bc05500f43302812e04401100b07e01300e014ac219f01faba03e38d0a600401c0410100f203b00f001032bb350000e00e004044a95013007014008004a8d1e2a5e0b4a490140020cc158009a1e1160e600307302b05f02300d01f19c04706b99c97703e0080130130f800f01c00600104616c00a09f00804c0030720560010550bb0a608f0230450bb00202900c08600101f00e01f02b08f05301502e00500100400a00100302c00c00400106816a01397101100200d00103e0a528400190910f00100218600100e03902b0bd01f0df8e502a8df00800100700a0040600010070060a00330080cf00100b022017015001bb300107782c00301100282300a00100200608005203901300201400100101007b00300380a02000e
  | 8 => 0x74009000e528001800a001423124255161b940420180005002011294524df10b401209b011000f800100500050f6801616d013a1cec00705aa485004804516d44d300d418d00583890010154008645a00440350bae528003c196000401a00082c2045c01508380f21c8c04c0bc4028911806900040270008006000c0ac907007c003006d0840016033c02e94a0014002c0b1003800e8f4c33b0eb400400140190d9c2330eb8001019c001049014e002405100c40028ed4081026c003003801d073c11d02b403a004013100540990b6000d002007f002c3b5022c002003000b0354007014404600d001f073012b023c130001400d020c00104b808101280a48eb8285005407f00200010184053018400d00083f2011807e006000f002000c000400100640180004014115c3e9008008c00142e000263230006281000e24a00080010398001045c00f0a3c1d2003000204500068880047020808b005c031001000f0010091006400a001c05200ec005017c00194a007800061e0090001500040010014001003808f87080020038040031800194a00d886fc00401c007e004c002015400a86e400100101900208012002803e012e5280018008869c01f001001f01dc003003806d00d000d001800b013c057000401583d000d000408400140030018018001c01500c001802565280014014000400100580200490014000802c004410500f40070038001006a03f000a5280138024017800500a8006000809600b8040000402400900050004001000c026039000a001c027003803f01500268058004
  | 9 => 0x1c85ef804000a04302b006c00622c1210dec0020ef032c7255741160bd807c01602700584282c317143a82d411115401a801c0020a6009841817e008020818e3c21d905600100490ce023002c0190a901506a800203602180040d400600d002000805c0f6800404600a008811407704f09c8194004076042000801600100c83040080fd000807001d1e1000c11c01600400180ac0fc005001802c15005d0340024002171000c0400ac007010402c00403e000811801205b015000c06a0cb00300180a8007
  | 10 => 0x53801d00d001001
  | 11 => 2
  | _ => 0

def C27_S (s j : Nat) : List Nat :=
  qDirectStatePattern C27_initial (C27_countBits s) (C27_patternBits s) C27_patterns 17 9 (C27_slots s) C27_values
    (fld ((C27_records s).getD (j / 256) 0) (C27_recordBits s) (j % 256))

def C27_idx : Nat → List Nat → Nat :=
  qIndex C27_N C27_buckets C27_flag C27_seedBits C27_seeds

def C27_routeCodes : Nat := 0x54540000100200010e05001000000000100000100000000100000000100000005454000050540000100300010e09001000000000100000100000000100000000102000005400000054000000101300010e06001000000000100000100000000100000000103000005054000050000000101100010e0200100000000010000010000000010000000010000000500000004415000020100000000c00000000000000000000000000000000000000200000404000000451000000200000000800000000000000000000000000000000000000200000001000004054000020100000000c000000000000000000000000000000000000002000004000000000000000000000000000000000000000000000000000000000000000000000000000
def C27_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C27_rankPool : List Nat := [240336203, 102773001, 236077486, 137440591, 169062760, 203668778, 68338125, 201441678, 201401612, 136428843, 171064618, 203438512, 135512461, 67320136, 67219784, 203472138, 237023497, 67157258, 167854350, 236108076, 33631567, 169916848, 167983400, 134292748, 204487088, 68173067, 167884104, 100876749, 135446797, 236077454, 68301160, 240336171, 100876685]

def C27_rows : List Nat := [10, 18, 33, 44, 52, 65, 76, 84, 3, 5, 9, 17, 6, 34, 66, 24, 96]
def C27_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C27_rows)
def C27_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def C27_ori : List Nat → List Nat := qCompactOrient 8 C27_routeCodes
def C27_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 9) (compactCover 8 9) C27_S C27_N C27_idx C27_ori
    C27_coords 5 C27_rankPool s
def C27_F : Nat → Bool := certAt C27_Z C27_N 12
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
def C28_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C28_rankPool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505]

def C28_rows : List Nat := [10, 33, 44, 52, 65, 82, 84, 3, 5, 9, 17, 6, 34, 24, 72, 96]
def C28_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C28_rows)
def C28_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def C28_ori : List Nat → List Nat := qCompactOrient 2 C28_routeCodes
def C28_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 9) (compactCover 7 9) C28_S C28_N C28_idx C28_ori
    C28_coords 4 C28_rankPool s
def C28_F : Nat → Bool := certAt C28_Z C28_N 12
def C29_initial : List Nat := [0x394, 0xca2, 0x1541, 0x220b, 0x480d, 0x900e, 0xe070]

def C29_values : Nat := 0xfffbfff7fdf3fcfefbfffb9ffa7ffa0ff87ef870f80ff80ef7f5f771f5f1f571f570f541f470f3fef27ef20ef17ef170f0fef07ef070f00ef000efffeff6eefbeef2ecf2eca2ebffebfdebf4ea7fea7dea7bea70ea0fe87de870e80de7f4e67be670e570e470e3ffe3fde3fce3f5e3f4e3f0e370e2fbe2f0e27fe27be279e274e271e270e20be1f0e170e0f2e0f0e07be079e078e073e071e010e000dd4fdcafda0fd90fd80fd80ed80dd800d541d00ecca2c80dc000beafbcaeb80eb74fb74bb54fb541b40eb39eb30fb28fb20fb20eb20bb10eb08eb00eb000a20ba0009fbe9eae9def9de39dae9da29cae9ca29c0e9a0e988e980e97d5974f9741970e960e95cf95c1954f9541950e9500948e940e939e9394938e930e928e920e9200918e910e9100908e9080904e901e900f900a9004900290008ca28394804080007fdf7f4f7d4d7a0f774b75416fbf6eaf6ca26b9f6b9d6b0f6a8f6a4f6a1f6a0f6a0d6a0b680d639f6394624b622b621b620f620b620460406010600e600160005fdd5f4d5d4d5d415d0d580d55414d0d4caf4ca24c8d4c0d4b9d4b944b0d4a8d4a0d498d490d488d484d481d48044800439440003fff3feb3eab3de33d4137d537cb374b374135c13541330b320b2fbf2fb62fab2eeb2ebb2eaf2eab2ea22e0b2ce22cb22cab2caa2ca32ca22b9f2a8b2a2b2a0f2a0b28292800279f268b262b260b2421240023bf23b4239f239d23952394238b230b22ab22a0229b228f228b226b223b222b221f221b220f22092208220322022201220020922080206020402030202a2020201d2010200c200b200a20092008200420032002200120001ff71fe31fb61f411de31dc11da21d411ca21c0c17d517c1174115c11551154b1549154310000ff60fbf0fbe0fb70fb60f940ea20da20cb20caa0bb40b9d0b9c0b960b950b940a890a060a00080007b40795079406810600040003f403b603b4039f039d039c0397039503900384038003000290028a028402800232022002140210020d020c020b020902080205020402030201020001e00190018401830180010000c000940090008f008e008a008900820081008000700040003600300020001c0019001400110010000f000b000a000900080003000200010000

def C29_patterns : Nat := 0xd556595955a5559516515855595565156955959655591561557555965655585559555a5565557555955555515515541546551554155015165455514541545651554455055195455915545151154154595155855515145151154155

def C29_N : Nat → Nat
  | 6 => 74
  | 7 => 513
  | 8 => 0x3ef
  | 9 => 411
  | 10 => 16
  | 11 => 1
  | _ => 0

def C29_countBits : Nat → Nat
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | _ => 0

def C29_patternBits : Nat → Nat
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | 11 => 6
  | _ => 0

def C29_slots : Nat → Nat
  | 6 => 3
  | 7 => 4
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | _ => 0

def C29_recordBits : Nat → Nat
  | 6 => 34
  | 7 => 43
  | 8 => 33
  | 9 => 24
  | 10 => 15
  | 11 => 6
  | _ => 0

def C29_records : Nat → List Nat
  | 6 => [0x3b8d78c0185a40fa519ccd265f268cd1b8525b42c00008bdbadcc4c44daed4266898b34c50e5f19335100525b52f0b4a6d8b0064e943c01813153003b5778c00bb5471c6e05b62ee0ee3123004c4c54e92da6a4993466276001456d4b00003007e94db344987bacc50eb7353113004c4c74eb6ed312398bacc50c018bc09b0049a3366946a32c90053cc4ce8ada6a49b8525d81c00692b7800631b2af053631130062ef4e66abb57d1bdcee4e6400bb57f16d3518ba1d6b92ae198ae4ab45dc672ae19a49a334705268c99003acc58c013b935900646e03c00d93469adbb5768c0182a40fbdced60c401311bd60051a4d6662622ad1a1c64cd26b6eb31239abb5770c016f3163003ad778c018aa40f000028f3c018c8c1badaed5ec6e1495187004a23366e1455187004d4c54f05488c8b003acc78c00ed3163]
  | 7 => [0x294dad6000036173ac015b31155c8000122694f000017682e6009b43cc54c00006bb2b580001614137000019a87ce0000000c7ec006f31157880172a84af800000011ff6000046505cc00002a0cbe00232fe335900002df3bd6000033cc5ac00000043ef80000008c5f00000c454f20000428c36c00006ba0b9801b66a2b780000232cdd60000431736c0000c1185d8000156861f002e52a24e40000519a3ac015b879bcb80000ca30eb00001d8dad600004d5776c00008520ab800010d664f00002acb97600c6e0e903c0000a4b4678026d273153000019661d60093c64d5640000c1430f80001496dcf00002b1197600003b8939c00005c99bc80000001c7e0000172a8f2000046595ac0000c54d8f800013b98dbc6ded78b06200004c4555c013131092980000d230eb0060ee14a1e0000616187c015b5da09980001314157000021ecb9e0000002157c01655dabf88031aeb5e6300001aea8f2000050cc5ac00008ab2a780001016bf9000011c63e600000006ff8000086986d800014f2bbf0000307489e000018c6fe800007c3d7c800011565cf00002330cb60000002c8fc0000c1179d80000941bf60000000b9f600c1529b03c00008220eb8000122654f00002b61f7c0000465bcec00006918b580000612a7900000013bf6000056cc2ec00003399bc80214ca47470056e62242e0000515a53c010f3798a98026aed414700000013fbe0000608c4ec000066ae75802acca30ab0000244cd9e00002ed5fc400008cc2ed8000122315b000028acd9e00003b577ac00000043af8000149684f000021ecd9e00003b8c5cc018d9346ac80000c7416700000010dbe000055904dc0000ac43cf800015b313b00001aed1d60000002c2fc00009132e780000da68eb000017282e6000032973ac00003394bc80000933173002e56057e20000369a1ad78b03215f8000007531730000302d19e000050d73ac000033953c800013b8a5b00001dc63e60098ae55164000098b367802ad0a650f000022063b600003ad73ac000000187d8000131654f0000302db9e000034cc3ac0000a2b62780001468a5b0000176aff200005a904dc015b3798998000182a40f00002330fb6000035da5ac000091b2a780000823173000028aeb9e007235da9c40000adcd4f8000195c11f0043ddc62a60000525b5ac015b87a08b80000005ffb000027702b600adcd5045c000000476f80262eb1247c6dee4f1a3200a1c66052c0000308dfd00305361217000023254f2009b334c58c000096c66d801948e30e300002e10f3e000056e1e7c000076a0f3800013576cf00000e062e60000002497c01368a18a98000102315b000022a62b6000035ca9e400008cbaf580000ee1bf6000000062f6000053c48dc000076a1f3802b68231330055a1461360077344c58c0000ac2e5d800010c305b00002b6836e000000175ec0000c0892b801dccd3163000018c82ce0000002b6fc01828cc08d8000000437700000de62e600000030f7c00b937957880000d76a79002e560a8e2000000317ec01368a0cab000000042f70056e6c62660000562627c0000b8430f800015830bb000028b439e000060a32ec0000c14d0f800013130db0049e3301b200003b5778c00004198b980000632af900002c8377c0000514993c0000a3513c80000da6aeb0060a94d11e0000361afac00003898b980262b912530056d9a62560000378c5cc00005c193980000eb1567000023314b600005aa187c0000c6c62d80000008dfb000028ad19e0000515bb3c00006b99bc80000621bfa00002ad0f3e000046597ac0000b5189d800015b8cbb000028ab9b600002083fd8018d6f36d58000170989f000023305b600a1cbe338c00006518b5800010f30db0000262eb9e007736cc58c0000ab189d800015b861f, 0x24d19b200005aa1e7c0194b8528780262eb584700001a4b9d6000058e227c00003094fc80000eb30eb0000292da9e000000107dc00009718b98000182a44f00002d4b9760000390c5cc000081186d80001316c4f004662901b20000637027c00008cc0ad8000182831f000019662d60000002acfc0000378dfb00001496d4b00001d662e60000409736c00ed5da0b1800010f4157003b8ce24c60000455055c00008518ad80000eb12e7000021862b6000053e287e95276d9aa48000136317300495b66ab20098af0c94c000000442f80000db347900003174f7600004c4655c00eb5e193180001192af900002b30d3e000050cc3ac01438cc5258000111315b000021861b600001a4afe4017ba4b6a580000ce31eb00000011ebe0000455a53c0000ab185d800000084df00000d465f20000564c2ec00eb5c8931800010a654f0000305363e00004c4c54c0000659835800015b43b7003b8c455e20000465a5ac000065ae7580000ee25e7000021832bc000060a147c00008532e78000000a83f003b89824cc0000334c3ac00008b34e7800011981db00001ae55f20000489b13c01717718b18000145654f00000010bbf8dc1d29b62c0000c0bae78000119855b00002ad313e000035d97ac0000852e6d80000bb41f3000011c62e600c6e0a903c00d76a31b4800000043f7003b9b862c600b2bb5778c0000b8189d80000009adf00515aed4b2000000177ec013166892380000b92a79000021882ae000000073f800006bb23580000eb316b000026c63e600c6c9a336400006bb375802b735121700002d5313e00005c172ec0000004cef80000da6a7900001f0ebd6006d3518da400005ca0f98000000acbf0000304b97600b5455a43c00009a892b80001022f5b001a8c857f000002ecdfcc00000020bb800017b9dbb000032a62e600004c5a53c00bb57a0b880262eb5ccb0056ddc62660000584c6ec00cd3798b1800009d3173000000130be0000003037c000098896b80000009d5f00515aed1960000466276c01829b360780001121bde0050e4f199600a4466052c000092b4a7800008e1bf6000016e62e600003ac659c00008798ad80001224157000030b363e000050904dc0000b8209b80255278cd90000232a8f20000464cde4000087ae6d8021ecd314b00515b6d796000060a627c0000a2b6e78000000895f0056e1e6236000050e33ac00eb310931800014565cf00000010cbe0087988ab6400008ab367800011983db0000244b9b6005caa049c4018d5e2a388000146a1eb00002b70a3e00004c4495c00006c18758000145644f00001d662c60061190afe0000098ae6d80000d8316b00002b6bb760000002e6fc00005198b98000156851f000000000fe00004c6336c00006698b5800015b4137000018c62d60000002237c018da2b6e58000161881f00001d6d7d6000056d72ec010a651865800010f654f000028ac99e0000002d8fc0000a1b5f58000145315b0000232d8d600759bcc58c01314a892b000013165cf000031ad6d600c1529b63c00009898b98000131315b00001dcdad60000188abe40000a7cc4f801b4d46269000000132be000060a1e7c0000001afd8000158861f000028a82ae00004bcc5cc01839b18a980001817c5b0000305303e000024cc1cc00003b18b9800008230f300002b7313e000052233ac000066187580000b92af900002d7183e00000029efc015b87b3478000181a79f0000218ca9e000062978ec017b93c66c80000008cfb00002c662760000002637c0000ab465d80001155cdb00001f0d1d600001bcc7cc00009aa0ab8000110674f003ad78b9c600003ad0f9c0000003e3d801d6b95863004c4de62a6000019cabe400008cb53c8000158313b00001b4d4d60000390999c0000ac428f8026abb4153, 0x883173]
  | 8 => [0x3600c7801768244004512360087c3ca0055802200000467001153794004709130055a1400021e0628016a228800003c1c004c65c5000015f700170580800a11bc400002c22002146f280000889400c697570000132e00286063c010f0a140030851700000f2e4d8c4244400005cae00a6c50a000021450000090700195a7880087a60a879bc484002f95b1000001638000056dc0000232b800c21f5c00a3262600a1c50a000017314c5726f24017b98940000391c0000128e002b624129514688e00cd59440056c5c2000015a700183ab080075850f002e4deb802d40a1000ee12260065050f005f90498024f0f28015fad88005e189700184aeb802ac1b131b4a6d9c00000d1c0000184e0021801280000861400c6cc4a0064178b802320a5c011a8cae0000186f001a8c0b802fb651001839b14000006dc0034828780001452c014b86140000131c0013048d8018c0a3c00eb3a9e00001e1c0000130e0019a625d94610a1c00519bd30000215680000e871dc48121a005c805700001f2e0000167700165aa0800c1c6570000004e001d6b95c0119802e00a1ac0f002f0f6980000817000ca471e00001d1c004c5505635dcdb3800d403340000189800002fce002b6b01000e437a60065818f00308de9802045728010a5814006bb5160060ea220000037700000314e0068a093005a8de2001a2874c018d41a6003115d700188aab002d49810015b0088002b8c9b00002625803041410015877080000225c00584642002950c2800006bb0000018620046a1e5003040210000028380087ac0a00002fee0012a0a6c00d8011e006c050f0064a6250029531280156120800002b9c00432185002cb3528d4642bac006bac17004da145001aa824c015f879400c6ae57000005ee0022ad21c008e37a6000043cc0018c64b801a4573c000031ae0000035c0058560260ee34a1c0000cbb800bad6c400515b6380294625c01198a2f8dbdaf036bb5188b000c4625e33147f1200310517006666c50021e625c00ce581e00005b5c002e404b802ac610c0000443800a1850f002bd049802772e5f1b658d0600bc21d300001e8e0011c0a4c01198a1400b8cc4a00274489802ca1f6c010a771400ab15c400450c2b80000ee70010f011400378c930056eb6200001617295276d8e00b8d6c40015404d0000018731b655e0600ca891300001dee002b6ee1000000ab8009e2e57001d4489800006e70010a851400580ddb989bc48400305362800ce191e0000031c00560ae2002390a2800bc382600ab1857002c0c6b8013a6f4c00007c3800001bdc000017358026d312800d7322e0098890a0000146a0026d195c010a00940077189100000f6e00240625c00000438000055dc004e2185000005670014a8794000023dc00502625002f0824c0000033800b8ae57c6af0e08800001070d4642baa0075aa0f005c0de2002cb0f280000793800002094, 0x5591c200302de28013998940000558400002b6280000c0721ecd120e0041005300260c2b800000a731b1a811200adc3c0000903ed802326f5c00000e380000488c006361e50032a577000008a9600001c1c005580c20026c2a4c015b310600002b1c005ed72b80262142800001538008d1897004d5045000001170018d86140000239400328c27001720a5c008e30ae00000c1c0032cae7800004570016b2b8800610ddb00431305000014f10017143a600912c0a0043ddc500001727000eb381e00a7bb84000021f68026c254c01225194000037dc0046a1850000041700055033400c69797005582820000040700114841400000c9c00408e0500243195c00e4122600b2d44400002305334c42438000057b8006c15cf002c0f29800de2a4c003c12360087828a003ad60780000a670010a4c140065018f0000032e002631428011c30ae009e4c4a0046404bcda4e242000db629e00002adc00190c2b80000a3700061012e0000169c003b8549802b6625c010c011400369897000013ae55a14140001315cae0000011c003b90498026d2d28000061b8005818570043cae50012a246c00007bb80062189700455305000000971d6b0379a009b2e57005ee185000015b10011900ae009643ca003b8c2b800001770000079b80000281c0000048e002bf561000c6379e00a0c50a005c01420026206280165af88000054dc000021858000062bc01197f2e0000255c003b5049d6cde24080114193600bdd6c40000056e000005170000039b983a534470057e32b800ce0a5c015f85150f77090800516285001040a4c01655dae000020a6005c130200000a870000045b8006dae5700000e4e002b21f100062052e003809130063aac24da1e24200000133956650501003e1dcb8000016700156851400ad8284004da1e5000002570008e192600ab1bc4000005ae0000031700119032e008cac17003ac0478023514280000ba38003798970000122e002b10c00005403340000488b0049e185001166f4c00a3052600bda0930045172b80178754c00fb5cae003519173798848880001797000001e380000575c0055aac20021e622400c60d9e000020d3004553a500178b95c015f312f655da0910036cc0b80160754c015b8794000010dc000028a6003070f28010c7714bc5c9bd1000007ae00232ff5c006f30ae00afcc4a000006ae00000ea7001224c14005c8517000003ee000003e70012226140085008a00002ace0031b5610018686140085328700656285000007f70014a4126009b420a004be28543cc4242400007e38000002dc00002c4e002b10c2801020a155b77090200334047800d4625c01438c9c00ac0504000009ae001ae6f5c01822b890a650507006367cb800008d7000004ea80066818f0043048556cc4240c010f1394005da097003b85c9d58c2140c0000b50c008d2e5700001c6e000015910010a0514006a009a, 0x338e000019670006130ae003217d700000eae000010f28013e8a140000571c0015028d000c2015c00000046008cc089000021a500000bb5c0000aa380077130f001bc4a9d6e1e2400013177158d5e1bd1000023313b8c4244400004638004409130000148e001a4063c01275cae00afa09300370c4b802944c3c000030d600bdd9440000000e0026d0c2800eb031e004215d30019828d002d4241001318d14008c15ca002610498020402280000003a00b828c40046632b802851428018383140080819a00455605000010a2c008203260065008f6523828680000207001148514000026dc0015464d0021806280145688e000015dc0000052e002acee1001829b0000c820d300001f0b8006c146c018330ae00004c4a0060d72b802cb195c009d052600b8a093004c5d63801dc324c00d2581e00c6bf17002e448b8000170180119812e0065ac0f0052972b80000e6700000af380085090a000012ee000016a1400ca2b9edb3515d60019804d00313362800005a38006f09130000050e49db66a580137851400c12c040048848500001667000a803340026029b0018804b8021857280165861400001b1c00002a4e0029d1428015f30ae0000466f0019c48baf0de644400d7052e00ad9bc4002503e9d6d04240800e40526005c9c17004ee6cb8024f07280000513800652c0f00558042000000170011a8514004705930032c047800010cb4010c5814007f189700001c4e3b9a22a34011a302e00ad8184000029ee000010f2c01319895438cbf8ec1d29b63801aed1380156580800000fdc0059504980104244c0136312e00378913005c09823ad726f3800ee312e000013dc0057e1850019a143c01585808000029dc002e4aeb801d6244c0195c194b9581bd100002636802140628013158140033931798bacde3801501468010a2b94000009dc0048814500001153000001db800c6af17005c4c4b80000b27000c6121e00005a5c0014c28d0019a6238010a309365afa08200634beb8018a0a6c000054b8000000303115448b2f130644400005cde0080809a00428c2b802141428000033b000001ddc0000104e00000f17000005ab80000209300190c4b8018a246c00d62b9e008a828a000005ce00220322801198a13365e191100344c4b800004b70000058b800c71857001884ab8026d142800004b38005818970052a285003070c28011a30ae006695cf004d504400000376c01658514000021dc005321e50025714280000bb380098a60a004548a500150026b1b1a8a12008a430a004da0e5002b6021000008cd60098804a003f8c2b8000135280119322e006a98975e2c0c8880160824c0098312e004120930063632b80232985c011487957bb2a082004080c500000b070018d85140000229c002f0c8b80000628b1b835e060000239c00635bc2001046f4c00002db800b2a1d30000034e000015b18006603358d812f09, 0xe1700000722800a2b90a000015ae00232145c01450514006c2c0f00560042002b682100165ab080000305c004c4484002ac0a10000030af8d8cc08900002dce0019a253c0000553800ada0820057d72bc28c2142401315c92000055850056d0498000058700162ab080000555c0000105700180b95c000024b8007709530000142e637071a0c016a580800002d9c00000c55800004a7000b94c2e0000085c00430de5000c4015c00003e380066ac0f004c404500104574ddcbc32220000201c0000046e001a4023c014a83940000271c002f972b802626f2800006bc4009b18919b450484002180a28015b0a08008a890a0000276b802e0241262b03790000021d3002f4c2b80000e07000ee5cae00005a1c0000066e00001561b1adb689c00a29bca0015004d002d49d1000db412600003f5c0000124e001d6b9380183312e00b2cc4a0000026e002ca625c00004f38b937891100002eee0021e6f2800b038260051891300208049802b0061001839894008a189700190bcb80000e970000023b80000565c002f0c2b801f0de5c00450536005caa1600002205002620a280114831400ab2604005c6185000009f70013d8cae006b89170049e28500286573c00007d3800c6989700002cae00172a85c00000738009b0c9300594c2b802cb5b1000b94aae00c2428a00441605000010c3000eb2b9e00b4a093005ecc4b802410f2800cd151e00c443ca004be32b8021e2428006a1bb60000165c0015428d00000b96001312b9400c79897002c0de980172b05c013630ae0000428c0035028d000c20a5c0000bc380086050a004a618500232245c00000eb8000018970000044e60e6c242000008cb0003109170000106e000c2245ecb278a1400bdc3ca0046a0e500172065c00b95cae0000379c5caa0deb000019b700000cab8006119170000028e52a4ed11c00b9322f8d6db54e00612ac200000a57001451214007f2e570000088e00000ec700182770800a2ac0a001840cb80232ee5c018d30ae008687ca0060e145000009a70009d22a6006d9897bdc6a28500001987000d74c2e005e1817b2cd504400232bc5c000002b8006d9757001880cb801884c3c0182030800002cdc004291c5596b6820800b93f2e0000604a0050c047802b69810016541a600a2a60a00190bab80196143c0127312e00b8c3ca4a9bc4890000131300000b80a00911bca8cc09fc480202146800003eb8004aa09300001cee002b65710000072b80096c68a004282c50025d142800003d380000545c00000c2c0031b1a5c01655cae000031900043c025000de62440000273800c0bb8a00208289800003a7001314a94b02b8c99c6e0e6c0000016070010f668e008c95d7]
  | 9 => [0x36e39b019c77091c005e1c00391c7a3b9ca8809c00091f0a051c05009c62029c003b9d0015e37f15dc00255cbda61c32009c0015ec37829c7709dc12005c35191777379c03015c0022dc5e019c5e1917001be300051c0001ac379bdc00551c24091c7f009c0057dc005963581edc9b15dc4c059c00002300001c77019cb2819c772c1c68ac1c9b051c93c50a32095c000fdc00052cc1851c58051c582c1caf809c6a9bdc8d019c0000a30056c40a005c64029c77051c0015dc00275cc6bb9cb4a61cbdd7dc0002a3b295dc2b809caf851c001bddaf9bdc000e9c0002b005029cc1809c00029f581bd36a829c5c9bd7b8d7dc03809c8a15dcb4d95c2b829c580c9c0035639b3b9c8a059c9695dc37819c03819c85050a000530bdac1c0000a135091cc6809c759bdc001bf000002a7f019c005ee365050f00009d83009c0015f0004c4a0000b000019c00428abb3b9c00002900011c00041ca0ac1c0009dc09009c37809c77091312009c62091c9b450a21029c0028dc8cbf9737891c58029c4c091c4c1e5cb2829c001b9c00009c6d9bdc4c1bdc005c63003f1c688a9cc1ac1c35029c002093b2891cafac1cb29bdc77009c2b891c005edd00095c6a821cb8a61c01009c00261d00209cad89041d009c8d15dc00597000655c00001eb2ac1c002c1c005f9c001edc0026306a891cc6c6970057f06d829c01809c5e009c03009c01005c0009308d051c00002000003358261c58019c66891c6da61c0a019c2b819c58091cbf15dc310917a51bdc3507dc2b851c7f051c689bdc9b2c1c0a009c00002407829c0000ac58009c612c1c29829cad891cbb57dc002c1d4c051c68829c5b261c0015dda5261cafa61c5815dcc69c1c0034630026230018574c009c00015c77261c001be8af829c0055848d009c0001b02b841c773b9c00003000595d003ba30052a337851c12019c003bb0c1bb9cbeac1c8a051ccabb9caf8b9c44829c581bdc6aa61ca5091caf819cb8891c00311daa019c0007dc000523c6af1700059c00545cb2a09300029d03005cb8829c00019d87890a4c029cb2d7dc5e15dc, 0x56dc00092300031c7a261cc6ac1c001897b2bb9c000f1c00005c002c3035011c000032bf595c47051c001a9d621bdc005a5c8a009c00309caf891c0000310036dd00430a05005c6d891c000f5c00595c68a61c5b15dc9b009c541bdc0001a35e051c0057dda5029cbd86dc5e2c1c00221cb2d95c001e5c000025bd9bdcafbb9c3215dcb8831c0005211e819c00091c00379c00239c003b9cb2a61c00559c00091d32019c000a9cb2a09c6dac1c00115c4c261cc1819c002e5724029c005c5d0001a1771bdc3795dcafd7dc7b2c1c12091cb8ac1c001d5cbdd944c6851c8d450a77029cab051c000b9c12051cb89d5c4a9bdc2e051cbdd95c93ac1c001bdc002a1c308517bd829c2a891c00021cbd891cb2851c00355d03019c0a029c0002a800529d2b95dc4c15dc0043ca002d9c002c2300029c00001d0f009c378913989bca09019c30851c0f051cab0504b89bdc4c019c00092885051c7e3b9cb2809c0f019c12029ca52c1c00465700261ca5450ac6819cc195dc3715dc7715dc001c1c68891c37805c8a019cb4d7dc0057e3a5021c000c9cb2d7c40006dc00345d5b2c1c005d9cbc595c00051d2f019c83019c05019c2e009cc695dc32051caf95dcbed7dc2e019c003d1c00131c00225cc1cd8a]
  | 10 => [0x60577028e009c003a008c14e57dcb2b8067160e001c4c38ee70dee091c]
  | 11 => [0x1c]
  | _ => []

def C29_buckets : Nat → Nat
  | 6 => 19
  | 7 => 129
  | 8 => 252
  | 9 => 103
  | 10 => 4
  | 11 => 1
  | _ => 0

def C29_flag : Nat → Nat
  | 6 => 0x400
  | 7 => 0x1000
  | 8 => 0x2000
  | 9 => 0x2000
  | 10 => 64
  | 11 => 2
  | _ => 0

def C29_seedBits : Nat → Nat
  | 6 => 11
  | 7 => 13
  | 8 => 14
  | 9 => 14
  | 10 => 7
  | 11 => 2
  | _ => 0

def C29_seeds : Nat → Nat
  | 6 => 0x6d8038071929601887b0050a80381208b09c0383084000c58027
  | 7 => 0x15c00080cc21c58f8f3903c0066c30040a2c01a020228827928a5309009430004716025c76405a02600700040300230049da40fc04b2c8800800404e024011a4020050aa00043440b60e1000c0fe01102b00b808c1c100748040ae4a3010881810a0190008008008004000801000a00500202cc00200a031806406e02400080040d8125001001819c096015800c03e055087c80404000200d014631003100080c800200200d800408a089001006622e00400080080020750150008002036000813c072001888800404000a001807a09402a
  | 8 => 0x8fb0021007c03202088118ef63b90015b5c00f8052040c0fd02fc8f60064005000c06c03442e0056802b169449600100080eb4001004e3b40a3c1500004006005e3ef0724086028c07a0040108007012c00e49d311c40bc0e6639a09902d1002c03d0008004017c031008023c8d1806d00180ff00200c00d6a3ef023800d000401400f41b50176345003400401ec0180058005018000402c003a0a4418d8ca4008000800a8b7e2ad0010028000404b0018001001400a88600031460049007800b00800e6011003803a0004020c00d08c803d00041bb000c003006400100ac018008c009036001b00a802100a001e009400e00381a500e800986f40ec03e010f0450007006801d86b800d0478004003408900080010068004007403401b402a000400901100030110139002406303ba17f000a10f03ea0ee02040010074153000e0eb003007d0034009008e0e8002402c0004001013c037000816501640150528005003400e007403f003c011018400700ac00400d806600a4002001c0398300002000a3ef001c00c00480dc00180010010005006001c000800100080310034001000800982b400a00940080010002000801e004604780d0002
  | 9 => 0xf500104d2858d19d03b401601b0096001055218a400100d0400849a116170c0030a0001400940fd016400100182fe01241c700ac00684440190e2c01600086ee01580100204014009001800b407b0088003000405700080c60004064866c16b0ebc02200a4007000e19b000401000a80d8813c041002c006015800301580f8003a03b040002c0004032001007701cc0f800f800100f0048006800d003400700a8001005c00500040b9006000d0008017003000d
  | 10 => 0xc84985
  | 11 => 2
  | _ => 0

def C29_S (s j : Nat) : List Nat :=
  qDirectStatePattern C29_initial (C29_countBits s) (C29_patternBits s) C29_patterns 16 9 (C29_slots s) C29_values
    (fld ((C29_records s).getD (j / 256) 0) (C29_recordBits s) (j % 256))

def C29_idx : Nat → List Nat → Nat :=
  qIndex C29_N C29_buckets C29_flag C29_seedBits C29_seeds

def C29_routeCodes : Nat := 0x54000000101100000a00000000800000000000000000000008000000000000005400000051150000131200000a00000000800000000000000000000008000000000000001404000010510000322100000c00000000400000000000000000000004000000210000005040000040140000230200000000000000000000000000000000000000000000000000004004000050410000212000000c00000000400000000000000000000004000000210000001040000000000000000000000000000000000000000000000000000000000000000000000000
def C29_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C29_rankPool : List Nat := [2112664, 2182779, 5532295, 5250494, 5311951, 6637690, 6381484, 2117516, 5451421, 5258426, 3304841, 6576760, 2186617, 6426319, 2177943, 5447614, 5271211, 1064122, 4403101, 2125193]

def C29_rows : List Nat := [28, 42, 49, 56, 65, 66, 68, 3, 5, 9, 6, 18, 36, 72, 80, 96]
def C29_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C29_rows)
def C29_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def C29_ori : List Nat → List Nat := qCompactOrient 6 C29_routeCodes
def C29_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 7 9) (compactCover 7 9) C29_S C29_N C29_idx C29_ori
    C29_coords 4 C29_rankPool s
def C29_F : Nat → Bool := certAt C29_Z C29_N 12
def C30_initial : List Nat := [0x744, 0xa92, 0x1929, 0x6403, 0x90c2, 0x140e0, 0x1a01c]

def C30_values : Nat := 0xffdfffdfffa7ffbfffcfefe4f7e9c7f4c3fa617d07fe807f0fcf8717c383e1bdf0c2f80e7ba7fd83fea9ef47e7a073cff9e75cf3a27987fca3fe4fcf271f9383c83fe41cf201f9003c5f9e21cf0fe78473c1f9e0e0f01e78073c001dff6eff7f6fefb5e5d9ebecf4f638bafcdd4e2e9717478ba1c5d0e0e8617400395e5c8e0e3f27138385c1c1e0e0707000b8001bfffdfef6fdf77a7bbbffdddfeecf775bdba9edcffee6ff737bb93fdc9eee47371bdb81cdbef6dd7369bdb41cd96f6c87363bdb11cd86f6c30b6039b000d7ef6bd735d3dac1cd5cf6aa7b5439a91cd40e69d734e89a71cd30e694734839a31cd10e6847341b9a09ed04e681734079a01ed00ee800335a599ebcc94e630b21859000c54961d1300017ffbbff7df7aefa5779e9ba71dd00ee1c16ff7b779dba4ed9c76c03b5795a382cfc96747b3a259b8ecc0765e3b281d938ec9c16483b211d900ec80162e0b0f058382c0015fffaff6d77a6b7f75be9ad7956b82b3f359edacf5d67a6b3c15929ac7055f92a9c152e0a8f054382a0014ff6a7f253bca99c14bf2a57d52bce95e54ae0a5495280293c148e0a40051f928fc14744a3705178289c14404a20050f8285c14200a0f05040281e140e8a0725038a81c340c0a04050102804140009c94caa4a40011f6d8dddc67a6335319698c9cc64b632530fd6856942aca15350a968549422221061080083a240001fff6ffef7febbfb4dfbd6fd2b7e61bdf1ded86f5c37a61bd309e806f0c27749bb00dce8ee6037281b900db5a4d9eb6c6135f19ad84d4c269613430975a4b9eb5c94ae3096f8cb4c259612c7096184b000554929d114880a0004fffa7fbd3fac9fc64fb6a7b493bd69dc24e6126fed37d69bd24ddda6bc935b49ad64d69a6b4935849a924cfda67bd33d699e94ce1266ad32d299394c96a64ad325298e24c6926329318698c24c08260012fcc97d64be725f1d2f8c97c24ba225b092b8494c34a6125001278492d2496324b09240091e248e524719238691c248822440121c490da486b24349219690ca48632430d2180908248402410920809002480023f5915a48a9a454b22a491114880043a22030101048040400120000fffe7fbb3fb79fcacfd267deb3ed59f5acfa767d2f3e959f4a4fa067c033c949dd1cec0675033a619d20ce88674233a059d00cdfae6f9337a39bb4cdd666e9b374b9ba4cdd246e0336819b20cd8466c1336059b00cd52467c733ab99d3cce8e674433819980cca0664c332419910cc846641332059901cbeda5d292ddd967a4b35259692c95964a4a1825022280013f589d244ad2255912a4c952448812411120008f88476423a311d148e88468021211080080003f6d1e948eeec7272392d1c958e4a46014300017eb0ba4855342a9615498aa485022280a140009d504e98274613a289d104c202508110308800420a2100100007ffc3fde1fed0feb07eec3efa1f6f0fb687d103e521d690e96874ac3a521bfb0ddf86eec37561ba90dc906da436721b2d0d9586ca435a41ab20d4d06a4c35241a400cf5867a4337619b90cd5866a432da196b0cb4864f4327619390c96864ac324019080c8086400318018200c0406008300218000be305f102ec8174c0ba305d142e8815020a20850002704120008e00448022101101088004308218010a2084d0420c210410800830041302084104008140408420401010080484020200810020800840001fec0fde07eb83f581f8c0fc407c903d901ea80f4c07a303d141e880ed2074b03a4c1d240e0106810300017a40bb205cd02e5817260b92057902b5815a40aba055982ac8153c0a9b054d02a5815260a90054102a0014c00a1205080283014040a0004e10270012400914048402404120008e2046002248112008830441022001080082804108208010240810040482020100808020400820000fc807d603ea01f180f88076c03b281d900eb8075603aa01d340e98074703a301d140e800704038001a080c8006040300015000a0805000261012080900041602080103408100403020101004080003a001a000c6006080303018000b0805800292014800a0805000244012100900044002120108008200408020201008080003c001c000c1006000288014300a0004a00242012000880042402100104008100404020000d6006100300017000a30051002480120008a00440021801060082004080200008400400018000880040001c000d800600028001200088004000140009000400018000a000400018000800020000

def C30_patterns : Nat := 0x2565956655695565519456155656595665559516455755599565959596555945615565959555d55695599565558555d5569559555d5565555554554955155415495519545551154154955195459515545151154154655165456515545151154154955165456515645551514515115415465515945591558555154454514544550554115

def C30_N : Nat → Nat
  | 5 => 6
  | 6 => 222
  | 7 => 0x595
  | 8 => 0xa5e
  | 9 => 970
  | 10 => 28
  | 11 => 1
  | _ => 0

def C30_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 1
  | _ => 0

def C30_patternBits : Nat → Nat
  | 8 => 7
  | 9 => 7
  | 10 => 7
  | _ => 0

def C30_slots : Nat → Nat
  | 5 => 3
  | 6 => 3
  | 7 => 4
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | _ => 0

def C30_recordBits : Nat → Nat
  | 5 => 37
  | 6 => 37
  | 7 => 47
  | 8 => 37
  | 9 => 27
  | 10 => 17
  | 11 => 7
  | _ => 0

def C30_records : Nat → List Nat
  | 5 => [0x2df2f705b46d06b82da3e82801745c05800bdaf50e005f17087]
  | 6 => [0x2da98d980f6bcc70816001fb36b35af6448036d7a0a141b6bcc70a15002e0b5cb801013719a3856cb7a9705b54015002c039e58014c2d2d6d798d422a005c16c97002e03eb28011d2b95ad798d3a2d20ad25754b22639461dc16d3741dd37195bc348464e08db02a23e86801013a396e0b6a84260059128cbb5e639449d5b023008c00b86662e002b870f1a8a4b7ec3bf6e99ff86d7b28fa1b51404e8a5a0a638e63001601f536a292e020f31c730d52b22638e630000058f3ed7b225116004c71cd6b5e6352c9d0531a751ac0a41d31b652e69d46001c157328016bcc65e907edd34a0047ab4d50024b80a38017ad023c009497ea7603f66d467edc63eb0daf31be61ee0b6a820f48382ada5b82da74c380164c051c007495bcb6bcc71c96b5e674289800fd9cf8ec9809c68728300b5d18c9c156e28016c5043ec9809b88d013a2e361002f1b5c78014d2d2d6d7a0a630e00593510f905693fe8dc333a8c56ad5f50762005b131978f55b2baa00156c049ed7a0a1a17705b45d87a69d25a5280131abb580038460f133aa2a351002eab80bd80fd9f51400abd7e66005c14b3600000a857ccea8a754adaa128216004046d66002af7315801702755ac05ccda8c0000131570026c98eb5af4128434007305cd8fda0e70e19417d41e880164d5a3e3256caea8004ca9d56002f3a8878016c9f535fb745c6c37052f1d96002c95ce3daf31c805641749698b514046d2699df554618016bcc85c007f5d3ca003f6e8e592dfb3ea2801705b45ee0a5dba4d705b53f9698e1a4ea9001322755a4b7ecda8d31be6a5c3a69693fd8d5ac02d6c6d7a094b1731a969d52b5e63868980101aff8c00abe523770cce9d16b26a27185daf644c61e9858cff62000011fddb2602746280170d903ec074d5b8a0054b0127b2aa252c5d3520ba43400b8ee22e005ed5127b02a25cc3ba4ad9ff8400b5e821f31ca31cd2749693ff080170c069ea2809c646005f57097b5e672a8a801011f595c158cffc370ccea89398e5190288016d5023c00b8239ad6bd90a58b001cc56f2d95022a30c0074969ca0052aae360015b39f8800e0ad3940090569ab513f66d26001fb4132800738b9e2c05ccfa8a005af3297001c1183600170cce5c005fd6ae34d482b495001fb3eb2daf6428436987055b4b31a96a1518f5692baa5c333bea1e3d7055b8a005c06d66b5eca5cc3cc6f9a751ae1b2a040f6d4c6e313002e0b58b80164ba334007055bcb64d450107002c93ea6d311eab656a2809b84c005c3410f002c9a947b82ad9ff86ca5cd4b86005450127a623d3fccc7ab19ff46c041ce193513f67d2594204602180170cc65ec9a89d11a004c69d56002e1988b8016bd463ec9a89730e005af640f0029a904e801785943ead941073364d447d0da6a413fcc800005ac7ea2808fa4a00590a5cb]
  | 7 => [0x7ed93ea0000170ccedc0000298869d80149368852b000008d9a99e00001259f574000028fa097801652e67d6500000b66873e00000cc2b59c00000ff183d000004a31cdb00000a095bce0000147c6c7c0000298719d8000000135770000056860ec005c16d5945c00001d224f680000524ad3700000a0a4b9e00001199437400002ca522780000460a5db00000809b8cc00001514be7c000029a5a5b80000544a5bb00000b6a7e3e00000005b6fc00002d7805780000530d7af002fab8ada2e0000147ac6dc00002908d8f800005c16d5700000b00a1ba0000115a976c00001c10e768000054b022f00000a60ff760000131b27d400a4a36428d800002fa87f6000008515bea00000ad297cc008c9af3fe5801481fe46b900000b86046e00000004c17c0000225236e801191fe46d900000b5db45e000015134cbc00b29ba52e580000000fe770026390225aa00001489feec00001af56f3800005052fcf0000056ca1ea00000005aefc00002257eeb80000525181f000008c94bb60000147c7a7c000024b6be7800004c728f30000071963e60000164ba33400002a480b3801513f65da7000008c21ab60000147a5eec00a89985cd38000051ecc2f002908c9d33a000011b2a36c0000000a51f80000404dc7600000904ffb600544b99f4d4000023d52ed800004beaa57000007edd3ce000007f8e7e400002928c8f8011eab639d5002e0b6a7e2e00595512e69c0000000243e800005ae7fbb0000098e2cae00000ad9ffcc000015b387a80000510f52f00000a41fb6e00001644733c0000000a55f8000000074fb00000809d1ca0000164c055c00000aa183e000002b64075000008d963ae000005b8c1f0008d9b42aa6801483821bad00000a89636e00001605307c00b8ada99cb800002f8b5f30028f6a55a4e0000164b753c008c95b1cea8000058046dd00000a89b45e00000fdb759c00002828ca7800003f66d6700000a123bb6003f6e9ad794000014b237c800003f6f5670000098e39ae000006811be400001c10df6800000011d5f00000568aeec00000e9129b4000015b4ebb00000520b9b7002d7b29423a00520ad8e6d400002916c978000046e855b000007ecface000011eb8d6c00002c04bed8000035eb1e7000006bc94da0000131c29d4000024c6a6780000368ad670000094640ba000016cb753c008f4ff1cec800004a473db00000ac2a35e00000ada4fd400002638a2b800004647fdb002c07ed93aa00001493e6bc000015b237a80151496b997000008f5c19e00001493f6dc0092dfb2ee3800ad9fe46f100000a89af5e0000151352bc00002a27a578014916e1bbc00000a49af5e00000000c1f8007edd371b1800002c64c75000007eccece00000b9a4fd400001632aba8000046ca5db00000808bbce000011e9557653909805ae8800005450127000008c95aae000016bcce7c0000000573b801654767d4d002d7b294b36005b531b165c000028256b3800005807d5d0000098caeec00000fdb839c00002367aa780000404cc670024b62d738e00001602976c00002d7b20780000460d7cfb2ab0a9253160000125a857400002a28c8f8000047a49dd000008e0aaba00001701779c0000251902d80000496f9cf00000b259a9e00000e92d39c00002a397e780151408c0270000056c9eea000011ead774000028f7a9780000520483d00000001a7de000016bcfc7c000026397eb800005b2f54f00000b01c6b6000000035dbc000010f0dfe00000526db2f00000a414b7600001484967c00002c06ea780000460555d000007cd63ce0000131c5d5c000025f806780000464b9d790a3b5ad5ea800530b195cd8000024124ee8000053446bd002045ccfaca000011ec297400000008cef8016bcce27170000098deace00001183313c00002c042add614bb00af3200000001d2de00000bca09d400001633b798000046050dd002c05ccbb8e00000e09cfac00001d3573a80000535209f002928d9b41e00001153e73c00002ca5f2d800005930167000008c9c6b6000012591b74000024c5e6b801715b53197001c158d07ca00000ad215cc0000000aa5f800005af319f, 0x89558ae00595522972eb0a9204601180000581481f00000a093a9e00000cc11bb40000263707380133b009d560000098d42ea00001494c6dc00002926d17800d79fe46e90000040873f200000b1943d4000023d64ee8000000175bfb2a53811808600000b9a97cc00002a298db80000530b9b7000008d95bae00000004c7dc00a41af3fd5800005c14167001fb74d07ca00001193f75c00002872ed7800000011c5f0023274d5baa000012fbe73c006016b38788000046449dd002908c8b73a000000046f7c00002307aa780000545181f000008f527ba000011b2b55c00002e0a03a8016bccec01700000b01a99e00000003bbbc00001734bf98000051ed4af001d37395bca00000da11bb400a8a4b8107800004c725d7002988f5c11e00001644773c00002634eab00000000ee6f002a292d8b1e0000131a5fcc000024b81278000051e853b002e298e39ac000016cbe16c00001a956b3800004a1024f00000b2263ce0000125b3d3c000015b23ba80131c76af56000000019bde00001259437400002e18d8f800005451b1f002326bd5b8e00001491feec00002906d17800004c7207500000002c9be0000156b82bc00002322aae800003f67d7500000baa63ae00000ad23fd800a42321cce800d7ab67fe300000001ccde00000b191dd40000000b75f800b195c1bf4000001cc60f800000d4ae79c008c9c10de680000214307a0000098d98ce00000fd955d400001632bbb000001fe3cf9000002b842f800000bc9b5d8008117336b3000005aead3700000a0a369e0051f183523c00001d223b6800004c6e37300000b86ca3e000014c330bc00000006df7800003c42e7c001af56cb7ca0000125c356c00002667b6780000000b4f7002caa8a531e003f66d17798000023286ad80000001285f002985ad636a000016bc7a7c00002145cfa800001fe40790000098db4ce000012fb5f3c00b00fa2ee68016d5050d4b0000057060ec000011b3313c007edba64f2800004c716d7002e2a8a044e00497023011c0092e045ce380000580b1d700000a615a6e00000004efdc0000292a097800004beb9d7002da98e1aa6000015125eec00002e0b02b800005c14273002675ad3aad58536c02d6c40000000237e8000047a7d5d0000043873f2000011f3993c00002d7a09780000594bee70029056cb76a00000004997c0000263795b80000580cc4f002eab8a672e00544e3330ac00001a95e73800005212f9f002906bd5b4e00000fdbc59c000019356ba8000051f31b70000056d2fe60000131b539c0000290a097800003f662e700000b5daf5e000013f4be7c0000232236e80000428ad7500000b24bb9e00000e0afb9c00002828b2780133be6a5cb0000056caeea0000151c773c008f56b58ea800005451e9f0023d704379a0000151404dc000015b52f98014d482881d000008d848bc0000149352bc000023d3fed80000460765b0000056d0ee6000016bd043c00002a2429d8011b16e1bdc000003fc7ff200001282fb5c00002638cab80000580add7001c13fc37d200000ad1c3cc00a61c10dd680171408f3b600000b26a23e00001021cfac0000086173e000004c711f5ac29b94e42320000000520fc00b6ab0a0878000047afdd700000002927e000016bb82bc00002ea9f8f8000000157bf00000ab6503e00000b99ffcc00002a292cf800005806d4f0000097c8dba005051dc352c0000000247e80000580684f00000b22519e00592e33312c00002828ee78000046093dd000008955aae004c712c2954000015b1bbb000fdba61be5002a2811734e0000131a755c00002ad66178014d1fe46b90020474d5bca0000151382bc000029858db800005aef52f00000002c0be005b5655443c000021a5cf98000047a855b000005552fe6005311ea0e74000024b4bed80165408a5cb0000058cdaec0000000544fc00001fb66738000038cadf300000002917e00000f12b7d400b6ab098cb8014c300b5b500230568a1aa0000151330bc00a6a41234e80000544ceaf000008c08dba00000004a57c0000290569b8000015c1cfc0000043860f400000b99f5d400002e299ab80000330b1e7, 0x6688dda00000003f1bc0000294439d8000052eae7600000a3df35e003a6e306fa400b86678ecb80000580d04f002dab29738e000011c21d6c00000008caf801209fe46d9000006d15bce000014c46c7c000029a3fdd80000000ad77000008c8a1ba0000131c535c0074d900df6000003e6ad67000008c1b49e000014c120f400a0a638963800000010177000008c92fb600593583a33400705805af28000047af54f00000b26a49e000012faab5c00002a281178000015c2e7c0000092da99e00000fdbe1cc000029270578000047aa15d000000025fbe0000147b5ebc00002518eed80000528dbaf000008c1fbae00000c9ac7d4008f5632bab000002b639f500000a54607c0000112ac75c00002d78c8f800005051ecf00000b823bae000016bd947c00002a398f38000052131b7000008f55bae0000131c695c000000092af800002b47673000008f96bba000016bcc65c00001fb66338014a16e2e3c002d7b29ba1e000014c3d4bc00a8a4b3e8e8000046493dd000005ccaaea000005a86ff000000007f7b801481fe39b9000008c897ba000011f143740000000936f801654967d4d000000022fbe00001605096c00002918ccf80000581414f0000058d42ea000014c11af4000029297cf800002e6a17500000a225f3e00001652976c00001fb49fa8000000147bf002982b83778000014c4967c00809d1663280000332b9e700000a41af5e00000e0879b400a616b579a80000580da4f000008c8faba000016050e7c000018058ba80000580f54f00000b89e66e005c533c7358000016349fa800005805dcf000008c9989e00520e9ab6d400002daafcf8016d5053f0f0000092dea9e001fe5706fe000001fb7cf380000531181f00000b25d19e000011dab9d800809c66631800003d446ed000002dc5cf80000164d453c00002ad601d801715af3397001c13fc73d20000125b313c0098e3b852a800003f646f5002b0a92024e00001192c75c0000000a75f80000408a8f30023d58d07aa003825706fb0000017336bb0000059528db00000a612f760000131c6d5c008118036b30000047ad4cf00000b5df35e00000dc8c1b8000029856db80151316b9a700000a899a5e0000131c4b5c000024b706780000368b1e700000001b9de00001512b6dc00000e70dfc800002b4337600000a515b6e000007f90de400b5e6383cb80000402c06700000568a1ea0047ab186f5400002daa8e7800003f6f4750000090569ea0000151404bc006bcff1cf48000000118df00000b00bd9e00001282d7740098e518969800000012bdf002f7a8a044e002b67f8e7c400002d97eeb8000047ab9d7001fb64cbbca002d25711bd000001c12536800002d239f5001af2b837d800000004d1dc00b01fb71a9800004a0e0cf0000058c9bea005af653a63c00001633eba80000482b5dd001693fc8de2000011b3693c00002d78acf80000524cc2f000008c10ab600000d491bb4000025f56ab800003f6857300000a8a825e00000b49ffcc000028f92cf800d4ab450e5001d25a510ca00000c9ae7d400a6dfb74f280000522ae370000056c97ea00000003ffdc00001692dfa800001fe2cfa001632b88de800000004e3dc00002366be780131c4b0d5300000a899e5e00000b991bd400002e0b68f801715b5640f00000a412f7600464ad9ff4c00002827ef3800002a893f50000056cdaec00521192b65c00002425a7a800005c16d1700000b6ac89e00000e311be400001ea553380000368b9e700000b82da6e004a0839c364008f5c141e6800002c697f3002d799d4b3600001192857400000b4183e00000530d4af000007cd5bce0000120ad37400001634ebb000003e646ed00000a3e303e000011b2e75c00001d356fa80000404e8f50000098df3ce005b531c21580000236286e80000000bef7000007eccace0000128c856c00a69d22356800fdba6c9e5000008c95bae000014c4647c00001c11236800005c333d70029a5a48d6a00001259ff6c00002c07ce7800005b5414f000007cd73ce000011d0c178000029292cf8000047a4c5d000008e1b79e00460d494334000026389ab80000460e35b, 0x2e2b66042e000011dc496c00b2a535ce380000434adf3000003fc90f2005205706ef000b5eca2ec7800004bef54f000008f5f39e000012fb8d6c000023671ad800005aeb1b70000074837da0000125a156c00002927b5780000496fdd7000007cd56ce000007f8ebe4000025f58eb8000051eb9b70000056c7fea000000033bbc000024b56eb800004c67d750000066090da005b53f3a63c00002c9812780000460b1d70023d2b837b800001174356c000017347fb00000594b9e700000a4a363e00580e33752c000015b1e7a800003d4ade7001633fc73e200000ad8ebd400000009bef800e91fe46e9002b0a8a024e00001601f53400000005ebb8000058062cf000006d95ace000012f9ff6c0090569236a800004bf0d5b000008b21ab600594b99b59800002b08fad800005331f1f000005686bec00000e0887b4000028f6d1780000544b9b70000099e35ae000011bb6d3c00002caa89780000000f66f00000a408d7a0000131a97cc00a3d5a285a800e9b74ade5000008d9f39e00001652953c00001fb3ff9800002b6347600000000e7f600000bf1cfcc00a8a02661380000000007f0028298e1ac6003f6e31778c0000000a61f800ad95c1bf40000000095fa000014dad3d400001c156f280000531412f0000092caaba000014c4be7c00002c03ea78000015c1e7c00000568aaea00382ad86f9400002987cd78000000149bf001fb71998c600594e9ab794000023d25ae800002b685730000090569aa000016bcbc7c0000250602d80147c60509d00000001f4de000016d4c75c00b8adaa087801655451d8f00000a2a636e000000037fbc000029852dd80000524f52f0000064d5bea00000004ed7c00000008d2f80151496cc0f000007488dda005c5021b59800002c03867800002d0577600000a4d5a6e00595514963c00428b70dfc0014835e39ad0000058d1fec00000d4ab79c000015b50ba80000524853b00000a88ff7600000e0ab59c000016923ba800005af601f00000b26029e000015111af4000028aa09780000482b4d700000b00ce9e000014c47a7c00002c9a88780000000adf70000000246be00580fdba71c00002908c0f8000000049fd0000000236be00581511763c00b8ad798cb80000382ade7000007ecdaec00594f9a972c0000168287a8000000171df001d25a48dca0000147ab6dc00001a65cf38000044aadd70000038448f20000131a15cc00801fb74f2800002f2887300000a65686e0000119b653c00a89071cdc80000000ce6f0000073168ce0000152af2dc00002ca39f5800003f650f500000b00aabb29c76c02bd48000026349fa800004c71cd600000a1dfb6e000014d2d2d400002c0a48f80148464d78f00000a52383e00000fdb5f9c00b8a674eab000003981bed000008cd5cae000013191bd400001fb68338000046ce0cf002d799df31e000011ec356c00002d7235e80000001275f000000008efa00000ac297cc00001c65cf98000047aad5700000000eaf60000112ae75c00002ca5e7380000496a5db0000074c60f800001483d4bc00002633ff98000000030fe00000a3e5f3e005b53f1763c00001732bbb00000525331f00000a6969ea00000e08b9b4000025f4bed800001fe49f900000b5e5f3e00000004cd7c00000005a3b80000520adb70000092dc6b6000005906ff0000021a56b98000051e46bd0000070442da00001193d53c000019058fb000003f65ee70024b810fa9a00000fd9a19c00bcad7b2878000055abeb7000005f4faea0000131955d4000023d662780000382b1e700000809d3ce00000fda85d4000015c2dfa8000035e46ed00000a6a413a005c5644a32c00002af39dd800003f6d4e7002d798e252e00580e9b8d2c006dcb71736000002e68573001c158caecc000015110cec00a5e638eeb00131c770d5300000001f6de00593584051c000010a237c800004bed4cf0000056927ea0000152b52bc00819d356f280000142307c00000bead73e005b5651f53400002a2a0578011b368854b002da98e14aa000016bc6c7c00002987edb800003a4b4e500000b22539e00001193833c008f56b57aa800001fe4779, 0x2928d8aa3a000017052edc000015a237a8000015c21fc000007a973ce004645706f7000001b756f38000000130df000008688df200594a59772c00b01c62ee5801603f6dd470028298e3b8e0000152b30bc00002d7559b8000059128cb00000b2251b600000fdb479c00001fb71b9801191fe39d9000001d460f80000125b693c00001af5cf380136cc71dd6b8a9799e3b2c00001412c79c00002e2b64f800005b5439f00000a61b45e00000d49cfac000029256db8000051f191f0000064173ec000011b25f6c00002636bf38014c382b1a7001c158c37ca00000cc2b79c000015a3ff98000046d0d5b000007a963ce00000002f3dc0000000b0af800005251e9f00000b5d5b6e000012fb693c00002d76a57800004667fdb0029056cff6600001182b75c00002e074f38000047ad7cf00000b25989e000016c9773c00002664d2d8016bd95020f00000b00ca9e000011b3eb3c00002e27b73800005af259f000006bd5ace000008711be40056cb7173a000000016cdf001fb71993e20000000507bc00001a958f3800001fe46f9000008d8ffb6000016bcc6dc00001d35a7a80000464da4f00000a8a02ce00001755053c00b5eca7cc780165496b9c70000098e5eae0000147b82bc00000007077800005aecc2f00000a65cc5e000011bab55c00001d25a7a800005aeb9b7000005cca1ea000007691be4000015b2aba800005af5f1f002c07ecbb8e0000125b2774000024c412e80000521191f002d7b2aa41e000011f2d15c00001fb2ef3801192b65bd5000008c9a99e000016bd90bc00002c05ceb80000460b9d700000a3d5a6e00000b9a75d8000025f5f2d80000464f9cf0000058c8dea00001492c6dc000000018bf00101370cc66001d36bd5bca000016bcc75c00002c074e7800001422e7c00000001a9de00000ad96fd40000000a69f80000592dc4f002e2810faca0000120ba53c000019a243680000464d7cf00000809b8ce000014847a7c008f5c15ae6800005f5512f00000570ffe6003a47f86fa6e2b6aca8103800005271b9f002c9a88bb1e000011b15574000000058fb80000382b9e70024b5ccfaaa0000164ba374000024b67e7801654a67d4d0000000173ee0000143cc6dc00002b05a398014c2c61bb500000a41c15e00000fd9f5940000298429d8000047a50dd0000097dc19e000016bab0dc00002c0a3cf80000420b1f600000001efde0000151332bc0000000b83b801653a6a5cb00000002e17e0000156c08bc000023856eb8000000125df00000a0a2d9e00000005837c00002925cdb8017152ef6a7001d36e85cd8000016033d3c005f50738788000047a97db00000a0a63ce00000fd9c39c00002027473800002b850f50024b5ccdaac000015138cec0062d733eb280000520cc2f00000b2951b6000016bc547c0000293429d800005af411f00000a89fb6e000016bbf6dc00002307067800e9ab67ff1000008d90ab600000ad95dd800b8ad7b20780000000cc6f0015b3fcb7e20000164b8d6c00b01c66625800004be855b002c9ac2a21e00544b99b4d800a615b1cda8000000162df00000809bace00001192156c000028f3fdd80120ba446cd0000066173ce000016bd913c000025f892d8014c1fe39b900000002997e00001604c75c00001c156fa800fdb167d6500000a088dda00001183533c00002638f6b8016d41efd970000092d27ba00000b495dd800002a2569b800003f6577600000002c3be005311ead67400001ea56b380164c04cc4700000a68907a005c525c091c00002907cd7800004a07d5d000005692fe6003a6c5ab79400002c07eeb80000000f5ef002c9a89981e003f67d1779400a3e30568b800e0ab639e50000089556ae00521191fe6c00b01d30de6800d7ab639e500000b85f55e0059131c4b1c000025f286e80000580d1cf002c064cbb9a00408c01f594000024b5ceb8011eb82b1c700000568b4ea00000ad90dd400002828ba7800001ce21f900000a41636e005311eac65c0000292121f0000053131b7001fb719bac6000000054efc00002d974e7800000011edf000008f4edb600001182b55c00a0a638532800003f66d66, 0x534e92f0019841c73d2005b5424fc6c00002caa957800005c112d7000008ee1ab6000016555abc00000008faf8000054b261f001fb640bbcc0000129c817400b25d1662680000404e3730000097d5bae00001414613c00001cc39f5800004c650f5001c15ad63ca00561013a3940090569442a8000038246ed00000932049e005b53f3743c00000007efb8000046cfdd7000000017eee00000ae0e7d4000012f237c8017ad95510f000007ed2fe6004bef525f2c00002c0706780000496ad57000007195ae6004705b8b9700000000906f80000530e0af00000b81bace0000000333bc007056b57b280000520853b001692b873e80000125ac75c000026389eb80000592e9cf00000002ad7e000010d3f7cc000019821b5800002b68ff6000005a48dea000000057d7c0000000bc1f8000047ab1d7002daa0a638e00001481feec00002c0a88f80000428b1f500000000e8f600000b19ffcc00002e199cf800003522e6e0000056942ea00534b4a20d400001ea5573800002b47d7500204600e1c6000011eb693c00000008c2f800004607d5d00000001b6de000000035fbc00b2a3b5ce3800005807fdb000002b848f800000004797c00000006d3780164d61520f002e2a5e662e00001412e79c000000097af80000404cce70000097d4bb60000164b3d3c000016342b980000000d9ef002c07ed90ac0000147bf6dc00000006cb78000046c46dd0000098e1ae600000ad9f5d400001b257338016bcceb59700000b015aae0021c5b8b9e00000241236e8000050f2f9f00000a1e3b3e00000b495dd400002c06be7800003f6da670000058d4be77152f023749800a616341da8000015c1bfc00000b021ab600000ab285d4000023d236e80118352ad47000008dcb4ba00000ad8c1d800002a27cd7800004c7127300000a899f5e000000054afc008c8ff2dec801514045da70023d6016baa004c71dc21580000292235e800005af641f0000023459f8000007f929e400002d78c0f80000580f14f00000b26028e004c70d429c400002638c2b800ad95c39f4002b0809b8cc000010a3f7d400002307ce7800005af414f00000b82876e000011825f6c000025f7eeb8000059501670000098e3bae0000164d44bc00001fb52f980000544f52f00000b86672e00000ad1b5d80000000253e80000520d4af000008c0ffb6000012fb313c00a623d0dce80000434b1f3]
  | 8 => [0x811732eca001411765c007182648004967d0e000fa02d400046806a00092c081e004ce46a8000003d15b00af2206c00000025600000c8ab00198064b800004b0ac006a4372e005aedd06002ca2f0b80176dae1800ac1982e00000a6ab0000030d58016d51e18003148d500035e39970019306540014bd1e180074d5b3c003e613170027b8ec7800938e6a00092c021e005aee70600000ac558012f96e3c0064037540020e3fa80000067d580093804a000284735000000882b002a46bcb8014800218008d98b1e001fe39a4002d790830014c1761800001825600000d42b0023200878014948418006e9a12e005374c06ac180578d800e73685e321cc371c002bc46a8000007ed0001712b0780098c4e3c00580398f0023d0dc7800e9b525c008ed633c005314c060021a00d2408dd30050009223d1e004c6881e0000084558007f8329000aea920cad142131c00000a40380147b521800b2e301e002b4399e0000085d5800e9874a000000f156004c71d9e0029b8c078000026aac00a49070d1d96e1ba70024f92c7800c02c67a9b6016b380054a68060024c6e878000016eac00002981200460508e0015b41cf0016518a5c009095b3c00580e30f000006f15801705947800002661e000006fab000006e9580000138ac008f4081e005a5298f002eca603000b182e78006a4a12e002e67d1e000ae2354001491761800002ad0c004966d0f0019a440b8000025aac00002755771408e994000008dc78000051e28000002d56000015e2b002dc8c078015c3305c00a0a3b1e00000e09a001071e5400000092ac00719ba2e00580e30d001d2234b800003f684001384854005b2f28f0010a2ed2001213f678000017c56000011e8f002a56e830008811ca000002095600460018f0000077958011eb743c00739a92ec02202ca3001982ecb8011eb823c000008b5600000b2ab0029b2354001714087ab0a6dce0800464dd0f0000097e2001022b47800b8a8b0c00408a99e000003bd5800ad20e780052c2648004086d1700000748b80165544080098e533c00000d798002362dc7ac6570e67400a61d30c000012f90a49b41381000e08105c006402654005ae5b86000680dd500173ab6780094e2e1e000013e2b0029b92c78014837418004409450004a0e98f0015a284e000c02b67800001733c00000d4990023600478011dc6c3c0098e223c000015107000b70f14000af2b478000013856005450202002a24403000b99787800000aa5200520e706002428c878011920e3c007044e2e0015439a80021a2dd20011e96e3c00ac2ac0c00000d917002a8a4030011b3003c006015e3c002e0b19e0023262c7800cc2205c00a88030c000011810909805ace000004604c008ee141e00544040600282098b8015c52e18001982654004be018f000002f55800c9806a00099e3d1e002b40b9e000000d158017147a3c00000085600000e9ab0000013958014c2c678008c8421e003a62428000002ad5800004663c000027956005c4b19e001ea098b8016d4603c000004856002d63da8000a109940010d06e900096a3b1e0000131bfb6aca74c5801513741800440935000000252b0008d0214001524c6780098e2518005ccad1e000fa00d400000430ac002b80254005222406, 0x1c10dd4001183523c00b5df304005492f8f002828ec58000013eac005cd733c00580fd8f0000092c800147c603c00beae23d58300b59b00000a485000fd8067800000d756003d48397b8a04794180000120a000705c12e0051f18010018b5ccf001214543c00a688d0c002c63a1e00000a6830000036c5c00a88260c00332c01700000bf55800c984ca000001d056001b41baa002902dc3001032b67800bf9992e002f6b99e001c1600b801524963c000015f5600000ce97001c158cb800004b4ac008f56b1c001a039a4002da98c6000005046000749102e0048f1b0f002928ec3000001c0ac00b6ad70c002b41b9e0000074958011dc5c3c0098e253c0031c5d9700163020f0000039caee2a5e040600000e7ab0000062158011939c3c00ab9c12e0000091ab001a9568a00055006a0000000456000002fab002538c07801182d63c0094e361e00464d78b000003dd5801651c25c000023e1e004a6cc170014b2ed200103b00780086819480000009ab0000025140011b0323c00a41af0c002b42c9e0000050d58000035aac007ec173c0052f4406001a9600b800e8b305c00001c156005954806002c4b007800cc04c5c0000010560000122ab00225034780133ae67800a3c080c00530af060000090158014939c18000007456005311e81002a25cc300000200ac007ec193c0000046ab0016358cf000f52d65c0092e421e00316ad1e000000bd5c7ae08e62c00909a92e002e67d1c000005dd5800002daac00a08022ed49421316001c600920000004cac006e9733c0000109ab001af0fcbbf6e9b165000850375000000222b000004695801481fe18006bc392e00580af0f002e292c7c76b5abc7400000be560043439a48c8ff0dc680000272ac00ac28b0c004bf020f00179340f5c56d4ce01af2dc372c005614786002c064c78011c0b83c0099e5f1e005300586000b710d400125b163c006bd6b2e0000040ab00204550f0011935e3c0099d553d193a61b8e0014b00d200000566ac00b66041f29b00b59b0016b1fd40017146c3e4b62cbb16005374586002ca58cf0016004c3eb041c7344000001f2b00163064f000004651000809982800310b59e00000b4958014c0e61800a92361e00496058f0020a74cb80131b0078000014e5600000fdbf000005ccf800000f8ac0094da92e0035ed79700000704c0006d04ca800000b85600000cc1a000004dd5800b996e7800568263c000012f91002da98cf000850e690007ccb72e0000051ab000aa0654001693745c00a915a3c003680197000002e95800e9b745c0097d071e003a62e28002d16e8b801180603c00b9a8f0c0011a00a80023d13878000027eac0074db42e005c9600f002306e878000005cac00b36361e00580010f000008915800b986e7800b28fa2e005d57106000005a15800005046400428aa48002c6571d002da9f87d614bb3008007ed8c3c003300117002c062c780000360ac006bc372e004be8f8f0000058d08000058048008c96b1e005952f8f0000058cf800f9ad65c007ec083c0000079ab0000071930015851a18000004f560013639a80011f00d50017ddae1800b5eca02005371e8f000008c8880000166ac009e1733c000008a2b00000a483000dd2f278006d0732e002b6041e, 0x29756cf000dd2b478007ed8b3c00000452b002daa603000a1004a00092d071e000006eab440ff23510011b1763c00b5cbb0c004b846a80025f064780133c5a3c0098e3b1e000002b2b92e042ec5800001c6ac000003056005b5338f56c730dce00088120a000000ae56000010a29002982b8300174dae1800704372c005201d0600198138b800b1a0e7800a48730c002c61b9e0024b3147800b5ab678008c95b1e003f6c81e0019d41cb8009d016a8001fc375000464af0f0000001958011f16e3c000004b560014205a8001f300cb800001fe980000254560025e39a4000006295800002b51400001d456000011b44b6acaa905800005c218000021f56000e62e28002304407801603f67800b96920c000009d2b000000695d951d9762c000014b4c0052f4486002e2a3c300000600ac00002900c00408d497000008c89c64d786e2c008f4011e0011a0ba80017d384f0000033aac006bd5b3c0057648280015b00cf0014b920a0005ac8650003e68397002a292c7d3729c843800b6a321e00000d7ab000001bd58004006ea0000021456005ef5106002674e8780000142ac00001c05600000502b000007ecf800ad9767800002321e000013d2b00263008f5205b86e1400b28ce2e001fe39a20012700d40000011aa4009095a3d4dad6af1c7ed9362ce5b5654fc04008c9101e002d6ad1e00000b00780000162ac000008056000016b88000002354460d484c2c00002302400520ad836016b440d801715803c00000e556005800b8f0000069558000024eac00a92301e002d6b19eb6aca2ec58016d5241800a40260c003ca5d97000007655d95584a63400a40080c004851e8f000730e54001184603c0041c8d50000016c8f002ca2f4b8014806e1800000165600580c00f002fea5c3001318e67800b29af2f654a6c00d002c0a907800f50325c00b895b3c00484cc1700163440f00000292ac004408d5000000e0970029081030000019aac003fc034800000f8ab002ca568f0016553018000008d7200000e4ab0000056dc00000134ac00001be56004960b8f000005d55800a1032a000b29ba2e000000c2b001ba68cb801673a65c00ac2890c005c56d06000004f15800550a0a00076dba2e00000ad38a4a3613808011dae678000001756000000cab000000d558014dab478006d00b2f29c08c01b0000072d58012fcbe3c00a62040c00496008f002ca2ecb800e72c67800001255600001490800282600b800e30e690000010b56002d6ab9e002308107800c98e6a0008f5801e002b40c9e0023d00c780000242ac00b8a673c0051ead0300000181500102b525c00601733c001422428002981e430011b2bc3c00000d656003f6c01e002678c87800cc0025c000015a7e0000020ab000003195dc56d4ce3000b89fb3c002960124002ca4e878000032aae538ed801a0000014ab001ba56cf0015bd2018002dc39500052083860025f7a878012fabc3c00b6a880c005ae1306002d76003000002ccac003fc0b48005d5650f002da7ecf000dd3265c00b8a900c004a71d8f002b08d87800b18ea780098c013c00530e0860015a02cf0011804c3c00810bf2e003b4d797b2aa22ec10016b80418000021e56005d5338f002da98c79fe3986e88000004356004280128, 0x2c02ecb800000eaae8298e0f28003d43997000da06550009d06ea800002b556003f6009e001af2dcb801021c25c0000050560036eb5970000076158000044a41d36bc372c0041ead9e7ed8b2eca000002fa7a9a4408d0a004d7190f002aba88300000126a0008f63b1e0013039a8002822dcb8005b8b89d694408d39484641b8100163578f0011ec083c00000d856005200106002ca8c878000057aac007edd33c00592cc0f002b0a6c3000da3685c000016370004c70a1c00204558f000004c678008115b3c003c6e997002635acf0000011b1800001c64a00560ce97000002395801525201a985ac730a0000026ab0000069158014db5e5c000004056004960c8f000004d158012596e3c00b5c030c000010d250022500c78014835e0800810fa2e0046d020f00171568f0005d90c90005695a3c00000d4ab002b0a8030003986ea0000000e560014201a8001b7170b800b99b47acaa92531725ae65d8c002d741c30005b91aa0009d23b1e00000d62bac2a473820016bd2e180000208560011a0ca80023062c78010d0049000a60010c005240106002ca7ecf00125ae63000001e15600330c0170000086d5c6c8509c34007ede53d29c84c00d002ca5cca000ad81678000025f24c02d65b9c002c0a5c7800b5aa87800a42320c8820e46a2001980dcb80000224ac000020b56004b1258f00000660b800002b47c000028557715b565010011f02d5000001b4ac0098e043c00000732b002900643484b5abc70001643754002e66d1d002d700430009d04ca800a08732e00000ad20002982dc3000c02b07800ac15b3c00464058f0000097c780057006aaa25ccbb06003300b970028f6e8300039886a000284375000001510600000b4d5800002ceac0098c263c004281328002ad3843001261a03c0041c8050005344685001a9340b800b9832780000082560020e302a001f31ccb800b5abc78004bc0b480021c2e2400169440f0016b8e61800b000b1e001541ba80000071158007d032a000571073c00000b82b0026302cf0013ccbe3c00b69733c0030cb99e0025f1cc7800fd8e67800001aa560000005ab00263840f000d78325c00b695b3c000007d290025b8d8780122c603c00002c088004345da4001a9568f0000032cac001d437511e8e61b8e6016b1cce000e72b6780074dc12e0036424170025f4bc68011b0103c0099d533d47b521302000007ccc00125b743c00000c0560000082ab0023d1cc7800af2aa78000019456004641f8f002c0020780000056ac0098e143c005214806001c6660b8014916e19c158c732800520b5860029870410007f9769000b02041e00000c02b000004895800001b2ae9056c37074bad6af1d0000068958014c4761800660032e0053129866bd5b0dca000003f6e00084026540021405a40015b3fcdd9529ba62c000017342004e12f8f002302dc7801021a05c0090a361e005af5206000008d8935e7f86e5400ac08d500000131a1002f592c78011b0e63c008ca321e0016e2e2a000a1009447ab18e63000002b85600300ad1e002d75083000af11ca0005cd103c000015d2b002066bcbcc71dc1e3000001b42e0047a880f0025f02c7800002e4ac005082650000b8132a001ea0dcb801603743ee2a5e6706005445f86, 0x1e1704b800002e6e000909af2e0052f4806000001dd58000030eac008500b5000000adbf001c62dd2000fdb8c7800718bb4800000fd9e002901cc3530b18e60c00001f0560054846a800263064f0014c0061800001df56005251b0f0015a440f0011b3683c00a88fa0c005951b0f001af00cbd95524762eca92cbb1600595510600204338b800004be4c00aed982e00524550600000add5d1f1804c04007a91f2e00000a42b0026398cf00000000c8000016340002d6a99e000008c07ba48811a58007cc192e000008b2b0015b3fcf0000038cac00001b256003820117b8a638946000004047800b8a8e0c000003c2b5acb717138011d926a00058c4e3c0039cd797001270994001522c6780000230887f96e1ba2000004a558015116e18007cc372e0000098ab0000071d5800003c4ac00739733c003680b97001e239d2000001eaac000026370005a51d8f001731ccf001604ce3c000010a4a003520c970000009d5800d48105c00a08032e002e65e9e0023d5787800e08065c007884350005c551060015b440f000001a0ac007395a3c0046cb58f002b06d0b80133c5c3c00811733c005612f8f0000092c9800fdb2670006d1072f31c4b078c002698c07801604763c00002d7140039c4a28002dca3c3000c9816a000b2da92e00000212b001732ecf000004f6ac005080b50000017fab000002358800000e2ae638520f38005ae04060025f738780129b5e5c006d1102e003828817000ae0dd500057016a800b6a890c004c6019e0026e97c780000196ac00b8a970c0000069ab002a202c3000000c6ac00001738a0051e1486b01d362c5800004baac008c15e1e00000b9a00024b00c7800e09765e8f568260600000652b0000007558013182e7800000e25600560ad1e0025392c7800000e6ac00002638a003f6e9940000080158014bc6c3c003680254003e65d97000000895801192b67800801fb3c003f6131e001ce6e8b801410165c0000000580052f1e8f00204600f000000a2ac00704b72e00382af170015a008f001651a05c0000174560047a0b8f000aa0094000004963c0094e491e00000442b001d367cb800000caac006401954000011811001a9008b80000176ac00b8a633c002e6019e0029b704b8009783290000016956005e56b86002b0a483000003dcae305682618fdb8cc59b0027398cf00000294ad5b2dc3738000011b100017302cf001495241800b029b1e005374b8694e425ac70014bac67800a61c12e00000c2ab00173578f00000206ac00a6d733c00000a129002302847d9502300500099d543c00497020b0000056cf00129c563c006600b2e0035e7f970000006d5800000b6ac00002515600504881700000339580000384aeb08099828e9b742196002dab00780151496040052c0b480000054ab0013a0655000b195c780042859480000036ab002e28c87800ad83278007ecbb2e003a6ad9c002ca23542205b86e9c00b2a2c1e003a6e7170000023d58007f8e6a00097e421e00000b1bf0022502c780131ba67800a62970c0035e05970021a09920017d4763c004bc37480000125c40000061158014c39c180056c733c002b639a80024b4407800cc0f25c000025556003a6cc17002ca5ccf00149b001800001975600496c00f, 0x2fe810f000cc3305c000028f0e003a61ba8002305686000da1765c00a92980c001f439a8001a902cb80000508aeb0a9180080039cd19700230738780000302ac003fc2648003528397001c1200b801023465c00000f25600530b5860000030558014c010180056d5b3c0047a3d8f001c6065200133ab47800001ab56004085d970016b181500000038ac00810c52e0047ae70f0015b05cf000001f8ac00001b431023005e940025f440780129c583c008c8bb1f4c47a3981ac2538ec6800f50165dd3738372c003a6b99e00173098f000c48eaa0008f4191e00536ad9e0028f8c030014c2c61800000145600000782b002321cc780156ba618007a9102e00000db2b0029200430011e95c3c00a3e420c000001cab001803852001392c678003680354003a61ca8000001155c08e986e580000101560052ead1e001af10cb800003d4680056c4e3c0055d4c06000860dd4000cc2d65c000016456000011b11002301cc78007f8049000b7a900c0025e5da4001b42dcb800da0025c005ac8050000f21ba8000008d878017e5943c00568083c00374cc17002945ac3000001c2ac00a3d6b0ce9b00b59c002140654316b997650000025b56005aea58600107385200147b520800a45070c00580e70f0020b600f00168c763c00000a65600520ad860028f74c3000e08e65eb0a6d8008e9ad6af1c002a206430015251e180097d8b1e0051e1506002366d05d303986e169074c370a002d2469e000003d958000028aac0074ce7480046c850d0028f2dc30012f8043c0074c435000460058f000005cdf800dd3685c00ad6a20c0044a0c8f000008693000cc0105c00a3c0b0c000009dab002a25cc1800da1545ee299e3b180051ee70600000001d00125ae678005ad563c0046c130f0029805c3000f9a745eb08118036005041b97000003fd28007d004a000a0a6328004961b8f002ca68cbc645b86e3800000205600477180fb2a53338580000208ac00b3e3d1e00000eb2b0018b56cf001604a63c004405954000004eab000004255800d48e65c0097d271e0000129ab0020f58cf001022aa780000248560052eb99e00253235400000250ac008c8011e0000042abb2a04440b80131c7630008cd071e0000043ab002901383001319767800000535600548e0970029b7ecf001583f678008c0171e005212106002a86bcbd614dca610004bcb748004640b8f002d0b0078015106e1ab0a89980400504b59700263738f00000014ac00ac2633c00460d48b000005b15800ad8b87800811af2e00580838f000007a158015852e18000012e560000089ab0020a6e8b801259763c00258735000000a92b0015b004f0014f5241800002b656005240b86000000955801213685c0099e3b1f4c3823982000b71094001653a65c006d0022e005241b86b8ada99c0800005804c00b5d100c0035288170015b008f000000feac00a89d30c0000063ab002b0704b800005804000001793c00560b19e0025f0047d4525976040000124560000111ab2b8730dd3801514961800b02c01e00001072b002979987800af2ac780077db42e00300302a0000023942b67f86e6c00000a15200000982b002c074c58007f91aa0005cc173c003c646a8001b45acb80000210ac006400354005454b86, 0xc55801510e6180094dfb3c00560cc97002e25ccf001180323c009ad5b3c00594d497002300047801654a63c00000bf56005f3319e00230568f0014786e180098e1a36e9b741b96002678d878016d4963c00b01fb18002d646a800000465580108006a8000016e5600000fd2b000006f558012fb003c005a48d380000006ab001805acf000b981078000023d200023e0caa0000017558000015aac00001b75600000d79a001d3568f0016d5943c00b7a321e00000872b002364407c6c5509c38000016b560056043240024258cf001193003e972dc374e0000046c0002a4a203001023f6780092c261e00001488600000568f000001ceac000022156000006a2b00000a8850014bc643c00000f856003f65b9e0018823540000042cac000005756005e92f8f0000064d5801182b43c006a56b2e003f6271e0000032158000024cac00b31af2e00476ad1eb8ada99c18011d91aa0000023220004cf180f000005e558013947a3c0097c4e1e003d49797002428b478009d004a80074daf2e0035eaf170028f94c3001653825c00660292e005240186001a9138b80000128ac0056c373c00464e98f0012702d4408c02206eca94e04160047a5d8f002042354000002d278006008e5000000f92b0000013158011ec7a3c0052c374965476dd0b0000046d58000007eac000017656002841ba8000004bd280134ab4780000198560056d58060023200c78015154418005ac77500025e13240007310940012f9763c008f4021e000008fab001b4428b801479761800a3e8f0c0012e1ba88c95b0dc6001712b27800a4a040c0000064ab001fb64cf000003b4ac009ea633c00000bc2b001a62ecb800000aaac002dc5c500052e242a001631ccf0000047b100097e3b1e005aeaf060023d74c780000288ac00b45d32e00000862b002e28c078016545c3c00a40030c0057646a8b26b066058000020eac00a3c020c003682817002a4a2830014bcbe3c008d84e1e000011e9300000875580000258ac00a48080c004bedd0f98e1a83cd800da0105c00000cc560033083970029074c3001674a63c0061d5b3c00548ad9e00000a3c3000e0ad65c002dc3750004c7079e0029b98cf000c02ae78000021c56000e61e280018c2ecb8004684ca000001405600000b1c5002046e8b8000021aac00000075600000ccab000000cd5801183a63c00b5dd30c004a6ad1e001af004b800da04c5c000015b3e5b89c1ba75ccfa2ece000fda0e78003b02648001fe46a4000bb23540014bc963c00b01901e000011c0f000000a9580000266aec07ed8b180052f4906601102351001603a63c00909c12e0000073a40028f13830015100218008f56b1e00000b19e002e7a403000002b6800041c86500013c1ba8002981dc300039890a000a49ba0c00000512b002b0a8830014bd141800000ee56005ae05860000007958014903218000014b5600000192b000e10dd40000054a1800a490a0c00001260f94d80578d80000376ac00002125600000592b002251cc7800002c2ac007a8bb2e00580270f000001b95800fdbf67ac07198b1a0038c1ba400232810780125b9c3e903fc3708002e6009e002b0241400167b825da95682628000003b2b001af440b801654543c00b895a3c002d0431e, 0x23600c7ba6ad86e7000b2a3b1e003520197000003f958005b890a0000000f5600595319e000004ad5801714be3c0097dea1600000422b00000b5558000019eac00a89980c002b4509e0000051958009d006a8000026341479421305002b0a903000d78845c00a5e8d0c004a6ad9e0000025958000051e24000029810000005b2b00000ac158011dbf6780064c02500000010ab001b40dcb8011eac63c00a88020c00544af06001c141cb800000d2ac000009756002c6019e0029ca3c30015851c1a414408d1d6d595020b002a45ccf000b58e6a000634bb2e0047ab19e001c102cb80103ba65c00234375160374c58b0023060078014c06e1800739c12e00000e099000007e55800005442400b00bb1e005b446a8b8aa4810a000004964400bdd733c00537480600000a483801584643c00a40170c001ce5ba400000570f000c411ca2b094e421a0000023ab001421cd40005a0b2a0000027d56004cefd9e0028f8ec3000005301800a604e0c004640c8f00000ad1580102ab478008da361e002b65b9c0028f5783001482b678002a826500000088ab0024b8107800002149800000d156002e6b59e000000dd5800e711aa0007a9272e0042005aa002c00647800c02a678000024256000002cab000000d95800e301690000028234002b45d9e000a106540008f86ea800000995600000edab002ca2fcb80104bf6780097d2f1e0044a1b8f001692354382838e6580000079560036cc0170025f05c7a20838e68800001935200382b19e0023202078011b20e3c006bc262e00482468f001c10dcbac63986e72366d04e160035ec017002978c0780000298ae0474d8028003c4e7170010a0992000003985c007cc0b2e00352af17b6a6383c60005090ca00062c8d5000000582b001b6164b8014847618000007d5600000d1abac2976002000dd35e5c006255e3c0036483970029002c30017753018000001156000008aab0024b5ac78016533e5c00894091e00594a58f000004795801523f6780058cbb3c00000d797000001695801043825c0097e531e005af4d860014200d4000a583290000014b4a004601b8f0000091d5801712ae7800b5e040c003e6a117000002495801600023c0058cb73c003261ba8000008555800001f2ac000020a560051e0b860015b2dcf000f9a205c000006c5600000b9ab002a66a4b800000f4ac0074d7d3c003520b9700000b5c3800c011aa0000004656000016a2b0015a09cf0012f86e3eb0a6d9804004b9210f0016302cf0017ad4419c11cc372c003f6059e002b08c078014c47a3c00000ff56000004c2b001981ccb801723f678000013e56004a6b19e002362a87001654603d6b57873380023e132a002323fc6800978069000ac2900c00000b02b0023d1fc78016bca61800001275200000a8ab00000225580120a203c007ed103c001b405aa002d7ac03000000a8ac005a0b73c00549190f000005bd58011809c3c00b01ba160046c0b8f002ca8b47800003f71400001af320000000ab002a4a8830005706ea000001f332000012e2b00000664b8008509e900099e2c1e0047ac58f001071cd4000c5ac67800001d756003f65d94001ba25140014946c040067cbb2e004c65b9e0027892c78000033060008c0081e005aef986, 0x7155ad6af16e7000a49b40c003e6c017001ba67cb8000050cac000007256004ceb19e000004a95800e610c5c0099d5b3cfdb74c594002538f478011b0043c00a3d5a0c005212986002921383000d48025c00b8a8c0c001c21324002d705c30008500490007047f2e00001480a0015b1cce000e08ea5c008ee2b1e003a646a8002da8a87801481fe10000017b5600000902b0023642878011c2d63c006e8e748001f41ba8000ff121200000386aee2811ba280037446a80008d13d4001492141000a3c730d652e65d94000aa02d4001651b45c00a89ce0ce99fe1ba2000008355d9529b742c0092cc21e0000119120023d704b800000d4ac00a61100c004086517002c6b007801258e63ea2660bb04005311e86a898b2ec1000004823c00b5c370c000dc1baa000000ed58014dd1e18000006856001fe46a2001e20dd40011b06e3c00001a92e000004dab001ce660b8000021eaea481180280035e83970000060d5801600063c007edba3c005b54806001d30f14000fdb745000b259816005b5410f0020458cf001493a61800b5e3b0c005805d8b000003555d45021760800a403c0c00000b41e0029b8c87800fdb8c6c00000a7560000160110019002d5000b58eaa00049c195000000a0ab002b0a303000c02aa7800ac1af2e00536b19e002a2a6c3000e084c5c00b02b01e004851d8f001ea600b80000168ac00000af56b1a0e399c002c06347800e09c25c00001f756000011b13ac2a48101000004a03c007ed5e3c0051e5086002d74e83001414c678000021a560024e1ba8002924403000001bcadd362c372c00496e98f002a6a3c3000ef3685c0047c02540044a130f0008d02d40011b1543c008f5631800466240f0015e560f00000572ac006e9633c0022068240000094158011b0163c00001a93400496b98f000003495800004b2ac00000aa56003165d970020858cf000e08025c00a89800c0051e0c860015b098f0014120e5c006e1982f65476e98b000ff0dd20000039aac00a6e8a0c00000f02b001a92dcb8016bdae1800894021e005440b860000009158014a0b81800b5e67020053446a8000007555b5e3986e5800b8ad70c00580b58f001ba17150016d5042c008c84e1e005452986001071d54000fd86e7800a6e920c00382b194002a48f47801013307800000e45600561011e000006dcb800005ae18000006457492142704000002315801214603c0094c935000520c0060000000d58016d46c3c00001e4560000103ab0023d7045800f1928a2ca8ee0417715950214000004bd3000001d6ac00001025600000cc190024123474967d17638000006656000003dab000006d0d0016b83218007ecbb3c00368c017000006d1580000312ac000015e5600000adc5001d310940014db525c009088d500054521060020f5ccf00108004a8008ee1a1e00000b8ab0026798cf0015120e18006d04e2e00460010f0028f41c30007d04ca0000005256000010cab000001ad5dc533c4a300082dba2e00330af17000007a8c001583525c008c0bb1e005f45d97000008f49000b98047800b00b71e005813f0f000000017001498b21800a88da0c8397639a28f56b1cc7000e911aa00092e3b1e00000542b001a90c0b80131c3478008d9ba1e003b2d497, 0x2da8f478015233e5c00001a157023005d9400297a303000cc16e5c0098d5e3c000002c2b00163098f0013186e78000009e560052efd9e000003715dc512c083000b69633c005040c97000005f5580147a20180090a2c1e00000b12b000006a4c001192b6300045c8d50000001c2b0025f0207801318107800a49b404001542e28002e09f8f000005321800a6d9d2e005372f8f002d75ac30000052618000015056002b45b9e0023b56cf000005ae240083dfb3c00460838f002908c878000054420008680b48005371b0f00237600780000058ac000006056005348806002fa6e8b801191fe3c00a89733c003f6e71e002e18ec3000d78105c00601723c00594a58d000007315b00b58ea70000029814000002f2b0024b138780148176180000000560046ce98f002ee58cf00000390ac004bc0248005325b86001c1064b80000018ac00001b556003a6d097001ea008b800000b8ae30284261c0035e5d97002d7b283000f9a965c0000292136556152020028f004300171530180052cb748000007dab000002f15801512d618002b81954005b5158f0028f8103001712ac7800b02421e005af650f001d2234b00000370ac00b29732e004641b8f0008d23540011d890a8009fa3b1e004cf258f00000241580000214ac008401954005300106000004195dc502176500094e321e00496af0f002986e831fe4686e880042803491ea0e398e002a2810300000172ac0098dba3c00000c92b000000f5580000078ac008ee321e0031e5d97002e58d87800001f4aeb0a919804002e6271e001af05cb80000126ac00000a456004201baa001891cd4000d7ab6500094dc12e00000ad210021400d40012e126a000b2a4b1e0047c430f00000a50300000486ac0098e423c0038c01a4001b4578b80129b685c008ee1a1a0046ce70f5ccda2ece80000012ac00be9d32e005324306002daa8830011e84c3c00000ec5600570ce970015a004f595299762c00b888d50004fc5d97002ca9707801413745c005684e3c001fe5ba40006b09950014c0321800001b43200000ada1000004755b82b58e6580098d073c003f6b59e0028f568f000f50065e9841c730a005208806000007a8c8015a3305c000023d220048246a80015e550f0016006e3edab29ba16002b8241e0000098cf800a58e69000a6e880c000000fab0015e56cf0010217a5c0000070560047a838f002598c878014846404008ee2d1e0042839a8a41af0dc100000576ac00704ae2e002e6839e002b0a6030016b89c180097dd31e005611e8f0024b3387800c8004a8007cc022e00530c0060029fa6030008506e9000705ba2e0011a0128b29d30dcb0016bcce3c002347350005d91e8f00000509580000492ac005ac7950000006dab0000051d58016d4be3c0058c023c005554906000001f95801021845c00b018f1e000008bab000ae099500000520240058c013c003fcfd9e0000092c95c56d4080c000024456004a0708f000003b558014c4841800000ac56004a6b99e0029841c30016d2b47800a88bb0c00000992b0023716478005706e9c004281948000014c070023b8a878000051e22c062cbb16003a6e317002c9ac0780177d2e1800a4a530cb5ac6399c002e2a483000002b8ae901cc370a00001102b, 0x11c56002145ba40026362cf00000184ac00001ca56005951e8f002caa483000005923c00a495e0c000014808002cab0078016551e1800b8a8a0c003525d97002b092c78004689ca0008c8b71e00001592b002da9f8080000050ac0083d5a3c00000f99a002980983000002c6ac00601593c00000622b001a96a4b8011e8163e976015e3a005442706001af008b800ad8727800000fd5600000e8ab002ca328b80000362ac000013d56005451d860028f098300000074ac00624605400497258f002320987801523525c00001e3560000097ab0029798cf0014904c18006bc4e2e00560b99e001ea2dcb800fd8047800b01101e002b4019e000002955801482bc1800a480b0c00000432b002972354001652b6780092cfa1f21476b58e0028f6003000000ceac00beada1e0000041ab001cc2dcb800dd3525c00704172e003521317000003155800004acac0094e421e005774d86000006195801525241800002e03c004be130f0025f5ac7801478061800a616306000005aab0029260030011805a3c006d0192e004db319e002925ac3000e9ac678003b4734800544cc02002cc8c8780000418ac000014f5600484b99e]
  | 9 => [0x4d8195639832ac731395801522e41c265600016ac00704b82e00abad2b056dd1a0aeda99c7dc5339e000197411804ac0041d59d601ab00110595c20ead80578f5b5650fbbd6b56005c4c8190215db41bab94c37565d86eadce1cd5cce012b0020a575203eac008c87801582c60037560006eb000a6d740eaf2b74dce2f65176aeca5ad581601ab0016b654d8e6ae0b5ad580079ab4601956b584cac000255800c02e8ed075613006ad6b1d15cf6c02b810735688032ae5394d5b74012b000007d212bcae3b0b55801319e0023b652104cad1013d58003fab74c3f5600000ec000dd7001258f0006456000e6ac001dd5b10882b002537546832ac00139d00001ab2ec2657214763dba00d5800272c000da5604004ad101cd5ba6e72b002980c27006ae042f15800682b74c26565d96eaee20355d600bab0dc08572120ead6b5795800af2e74c195758300ac0049d5ae65dab002675929ad6ac260055801692b064015601004ac0002e3db401ab58c73565b816ae971cd5800133a2ec0b571da20aeda0095c1e012ba916b5600484e8001cd922046abb2907575839cae970dd584601ab00002820003cad80021580121326e8175721048ad5e0e55800003400204655816ead0701158000b2b0011756c00b2add30095d6ce9ab45d07573396eac002ed580004324401757580f2aea402d5ca605abac008564b004ac001ad5801582b000ec56e7374adce00d58e61ba8000ca565b806ac002ddd000b5ba0009e5721016ae9760158e601ab62cbb575804cac0074d9000f12b002b857653745e9744158000cc11382656e982eac001bd5800b5abbf980574d816ac1700d5c641bab000f756f1374aee2b683000042e62c035729b9caeb47395c76b5ab6256b5634016ac00b896000e9ac62c195600000f1100dd58001d2b1900356b5832ac00b0078014bae000038e0047a3c000c15c08dd2b2ecbb5600300b1805acf47601ab2dcb7572107eae9b0995801212e909ba577106ead1744158e639ab00000900054418006e96016042b57819567f86eac730995b005bab00066574b804adce2dd596e0bab001b456000e8ac0044195600cab9087356e99c2ac0026d5800072b4404e5600130ae042ecbd10012b0011f56c02bcac0002db00016ab83c195639804ae536e95cce39abac1982f24c84ac004415abc012b7398056003a6b80003d5cce0cab, 0x94c17574db74ac0000161760bab00c03565b8e6aea400d5ba6dd1783c0b56af06eaee24415a0e01ab002495721484ae981cd5b823997002a464838e6a0006e95dc439ab6e910571d884aea40655c84882b2dc19560041eb2b8ac1581001aba5c2a574dca6aeb01cd584c0cab0011074000a0ac4e05d59e80cab000036ce9b74ac00139920e5bab00017574d86eae9700d582401ab000005e00048ac002ee38007fab001ba651b09c3cbb06558005bab0004856c009caeb0a6c32d65baba6c775600010e9360dd5a205dab002675c8804cacaa1395cce01ab000007400178ac00009d142132b002d70d4b976ae8f0983000e0ab001ce64af016ad100215a0e242ba6d6b561302eacb7141580075ab94c7356b5804ac006d0bc54012b5780857582bcad5e13958012d2ba90bf5751176187302d5db45dab9725356e986ea29b73958014bb28100b566d176ad88601596e122b738025600008aeda0655800432b789d357653a65d8b0dd5abc132bab1ba569b006ad6b02d58016d2c44002577104cacb71395abc83ab9d16b56000e6b1071cd597639ab440c556ad86eac003d15d60dd2b6e8bb5717016ac002dd90002cab2ec03560020ee8000655c76132bb29ce56c4b00ac001397594132b0023b5d71012ac00811720e272b002920c00594b0150095d60882b000fa572496eac660215d361d2b62cb75702006ae92138306e012b6e98056000e6ea420dd5d951d8f4411056c00eaac00a3c356083abac16b5605804ac00ac194ce1babac00356000051c00a5d64965dab00253570206eaced02d5a2083ab76dd356001e0aeb0a5c3000002e000175915806ac1705d5d9cdd2b0008d571d8e6ac00aed5cce132b000175c00006c9360095b68272ba6d07574b96eaee20655d6014ab92cbb1e00004d9800095c1e39ab74c08560006ed80000dd460132bb8a043c5d804ad6b1cd5c84b5ab6d04e2e8811aa00009965940cab81019560009cac0078d5a2001ab0025364002bcac00099b06e1bab020085752300ac370655b9ce72b138015729a20ac00ac1d20e05aba6cbb560004cb80009d5d36012b578275765004ac00b29748401ab7396b568c04cac009095ca7212b000378f1d816ac000099000c9ab000006400000b6046015b00b5ab0640256b997678009ed5b9c182b6e907561b802ac0097c780600ab0000d5600416addb41d5800af3a, 0x45cb75600536c9af0dd589c1bab578b756000eaac002b95d2eb5ab70473575206eada10215b74042b4d826560039cb800b29902e042b94d5e5771006ae040095b74282bbf253561b84cadd357958003cab000035d4d806acb709958320cab829805611816ae9b6015800004a000c556000d0aeb02ed5ad61bab94dd356e9a20ac005c95ad6882b41cbb561b806ae8f099580005ac000ce56e996eac006615800852b82dd35751176adba6e95ad6af1e0140256c59765da9098b800d7979690756cf804ae97099580014abaeeb056dd016ac0002dd35e1b976e81956002e678000015ca6c02b6e95e5752220ade37395da329ab2dc375000000cdd31cd5c84042b00204587982eac3705d5d941bab098265600560b95e2ed581605ab020015683832ac00a916000ad1e81107574806eac0000d652e1e2b5ac4e574d832ae530215d2e83abb28c256005b4b800001a80046a86007356af2bcac00ad95b0001ab74d07572139cac0050958000fab94c4e560016eb000660bbf6c59e000008483810ac005ad609c272b0012f56e706eac001ce0d60272b5c96b572102ead5e44158000cb2000738e0004d1c001cd731283ab6e837565d89cae422dd5db40f2b001ce58000f6ac12009589c012b5ac1756003b6ac006215b4605ab0018064e9ad6aea40995c84272b000377400434ac002015cce05ab8f4731ec42bcadce6e8b800c5ac0000b5d29c843c0058d594213288ecb7560004d04000dd5800882e00002591d832ac0062d70000cac58c733c00296ad6b5ad5801212c1cc015600300e80b0055dc405ab601105765006ac0057994085bab73826574b816ac008d8795c39ab002535c00352aeca94c796e042b600bb56002b678002a95800e9ba41c025600568ac00259580005b25601956c58e6ac00a6d620e0bab7380b5627016ae4274d5800dd2e90802576516eadba5ad58004babb88bb572996eae3b2ed58012e2b000176521176aeca441580083b2001af568c006aed29095800042b94cce5600032b8ff0dd25c4012b0013a576d016aea47395bc6dd2bb280b56e709cae970655b52132b000b78e00001267b94d5d36882b7380856c5804ae678ec7d4839ab000015683994ac0002165405bab94c305729832ac0041d74a683ab0003c56dd086aec062c7c08b5ab5540b5600000c2a4009580005c105c0b56b58b8aeb09095d615206, 0x2a42ed5806012b000c256dd0e6ad3602d5b005eab3e8bb570204cac4e0215ca601ab0003956edb9caeca1cd58001fab74d8056e989cac0074d58001bb274c37570539cac00579639c0baba6e970c00000ddce41d5800d0ab8111056e9816ac00739d561582bb49d357210f6ae0f00d580031abaed10568c004ae5c4415ae4af2b60026574dba6ad102dd580021ab0010758c5816ac020055d201b860006e563986eaee22dd596e012b8f47356005c4bada1cd5d60e9ab8c0261e8509cad6b2ed5ab4131e98e0f3c002d6b90703d5800c4ab2ec01560016eb8230655800b9ab78d10560a806add32ed5800012ba2403560c806adce0115800e32b62c2656002c6780000218005eab000bb6400032dab06615800012e56c373d5220eac000de0ad6042b00207560039cac0067d5dc483abb29d35600374e800001ed60012bb682656af006ad722dd5a3005ab7391056c0032ade22dd5d6005ab94cbb5683a0eac9802158005dae0023b5903b74adce579589c0cab0980256003525c0068d5c1e132b5ad07560017eae04600f000133206417563982ead8002d58dc0bab000ed565b81cae538ec7a2005aba60730c5d810ac00a4032bc39abb68b75721300ad6b1cd40e6042b05c025600007056b00d5b9c0cab0640b570786eadce2ed58005dac9081956c0300aee2a5c356129ab6e84e568386eac00b6995485bab000198f1906e3c002855d601bab0980b572d484ad5a0995800212b6010756af02cac260215c085dab001fb3c00300add300d58005dba8ac1956af02eac630095cb529ab94c265768b9cae3b0095ca6012bb29ba56001c2ac008515d365bab1bc1956dd16eaeca2ecbc761bab74dd3560009eadce201596e1bab6001756004603c001715800152ba91ba57298feacb721958000bbab298057023745eda41d582405ab6e826561b816ac0094d6000132b]
  | 10 => [0x1906eac1756e9ab6015800e95e57212b0215a0ead6b5639ab441584caeb05729ab0017176ac4e56012b6e95816acb7560cab0016006adce56002b]
  | 11 => [0x7f]
  | _ => []

def C30_buckets : Nat → Nat
  | 5 => 2
  | 6 => 56
  | 7 => 358
  | 8 => 664
  | 9 => 243
  | 10 => 7
  | 11 => 1
  | _ => 0

def C30_flag : Nat → Nat
  | 5 => 8
  | 6 => 0x1000
  | 7 => 0x1000
  | 8 => 0x8000
  | 9 => 0x1000
  | 10 => 256
  | 11 => 2
  | _ => 0

def C30_seedBits : Nat → Nat
  | 5 => 4
  | 6 => 13
  | 7 => 13
  | 8 => 16
  | 9 => 13
  | 10 => 9
  | 11 => 2
  | _ => 0

def C30_seeds : Nat → Nat
  | 5 => 33
  | 6 => 0x2b8948f160171e4002000c00209f801c0300d900e803c01000c01282c5a52003010803c038001003044c08a13405c827c056001082822e10a00d00380fc0040290018048002098004000802200200c804c026012808000800205f
  | 7 => 0xd1e2d709230f800224d007008814600812ad32c022006070870812a0070c0805004a146006013c17e0020bd531c1f602105c05f400200d00b8f5cd0679d0018040bce05118b878294601d32780f1e2a033009d1b0a4000d12801ac18a00605d80827b40ac9ec05c818a05d9dc81c815600f0ba8004156104002003009410a01e00c03332e8064800803600100a4a04aec07203c00200e002f10300064ec07c06204c800200a012801400600106e021832e04d0ab81f831e002001807c0e204c00780040ee0060b000604a801600e08985d4031006003400c00f2c38010042058aca801012a004006815c026009933565405800d000800c00200102580ec00400f055825a3be01302ec62433407d004001807917800091d41f814700105d400404900a804c06e0b4004802814f16d01e001801315e01d886eb2a02c06d000808606301e80040200020098080002006060803c00402288e047c046020000800407404c00700180bc09b00181300f000206e80201310f400580b800209000100082f611500f8064014002100565400201c000801c0230c785882281900fc090d6540740300020740132206855803c003595080001c00e034001801401e003001827a10001c0108188002001aca803c00e145007000416003401e007c01203d005803001402d023005c072008002023c00e01182d813000c01301f838000201100b006404e004001c12003206303cc050256041001002000800102600c008500d001001800200e012000404601101380c806c005011808004802d01e83c41d2027033801400c001
  | 8 => 0x18a1323ef0022022800280507003800070009000100261426000302dd00270241024c000305cc000a00d7000d00b20005006000070a0b00d6000303a8001589b800030231044100bb89ad012a488b00bc006b0064000200060002001c032e05ca0230000102090bcf008d007689a8897c00a6024300030002003105880581000c001300f4000a002800500067005a0004017c00060686010000ce00438954060804120005000a021d13db0398001a0001001600bd042700a4000500020019000101b50003010600020009016b019f016c0545000a000288c900470014001888c6000c02fe03e5005d063a0255005d0002004f010a0001889806fa00e300d5001c013c0001000300ae02de00a601c000190001001b035000d2000c005c001a00ea8822056a8815001b002502fa0023008e000187c487b003718a5e006500bd067201f90094000700070002015f00c6010e03f801020005011c0023015400110044002a0744004d029d00510003005c0007006b003600800011003d0004001400250024003b000600e600030001005d003d0013000301040032003a001401d2000700180015001e009d00340002014400120013000a879300460006010c004e873c004a00010045017d000200010001000f0001009f0162003c02ce86e40001005d00010029007e8a5e056601b0867800040306001985fe00e2001285e6009c85e2000a0008003700148a5e00180004001c8575000600fd0182010000040001000903f7075c0098000e02b3000c00060002000b8554000a001a005c02720004001084f700a90002011584c384020002004d000183d70023009100af003d000105630007001a010d00410003026e00ea0144003c00160011004583ca0161007000610011003c000d000c012b00040053012f83750002000a000a004800690015005400090001006100070037000b00c201df00740007030b831c0283003b00400021000d001802a98a5e0009000101700027830f8a5e01550003000300020035000d00ca005e830d009b00010001000800140065009d00010024001900340012004201070001000200a700ca009e000d8a5e000f00050001004700010001002b000a0002014d001101660003001000410001000c000682ae0002826201f5000300070001007a0005000d00ac002700da0001000500500132001b018f0001000d00090010000c005d00a4825800070001000a00020001003c0002002600210001001300ef002600158a5e00220110003e81d500280007002a000381c901290002007d00560059018d0003000c0006001b0045000400be01250003002800010017000400020002017a000900810001004200f3000b000100310064002a00820003000b014800420041001f0004000100c1005d001c000200a90004005c003a0008000d0011005e000300880317001b00040003009f005800230233000181c1002300028a5e00630001018381b1816e01080121000a000100100002004b002c013300140002816200110007000600070048001400a400190096000f0010001e0010008001de00610001003a0007002500020018002a00ab0006001a0002019d0007000c000281180016001700020009000700050012000880ed000100050010000e005d003e0002003d000100030008000a013d0244001d0006003f0002809700080150001a0012000100070004000200078094006b00c000070003001400020024807e00b8001b001500340019000200010027000200840073000d00080003000a005c00660003000f0010007400080005004d8026003d00890006005600030112001c000f00080005000c000a008c000e
  | 9 => 0x50278c06207133c023e00416880dc66c02221b8249ed85740f807d414a35107900d04400020b201981233c536700902793ca07701a002007f055826823c02b228a0da73a01410301000260500f404ec04401d004000806c22700185e672e02f04a80ac00801818e847c08c002092007400802d0064d5c00800d99c80a801a18700f05580040e3015064c0bc01e01200140020300e20014036007005031c0b33220f682a000428500d002c31612f048855802e013001000401407a0274c7812731d000800804405d98d001c30400e003800800200400081e411a004004804c0080120008006618001038051000e036001000c1ae01400100b4026026001800c00d204007816400200d00681500a400700600401ba02d029800800a02405c00201da02e00f43c679402c00f806001601c0238008026021001001000623300801f401a02a873428405a08901a005002c027021803c0120e000080b801e003005000c046006004004803c00500400267940a8092802001e0bc803800401c037003002009800a0008076794002
  | 10 => 0x852d1510902836
  | 11 => 2
  | _ => 0

def C30_S (s j : Nat) : List Nat :=
  qDirectStatePattern C30_initial (C30_countBits s) (C30_patternBits s) C30_patterns 17 10 (C30_slots s) C30_values
    (fld ((C30_records s).getD (j / 256) 0) (C30_recordBits s) (j % 256))

def C30_idx : Nat → List Nat → Nat :=
  qIndex C30_N C30_buckets C30_flag C30_seedBits C30_seeds

def C30_routeCodes : Nat := 0x151500002202100000302000800000000080000080000000000000002102000010040000000000000000000000000000000000000000000000000000000000000000000000000
def C30_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C30_rankPool : List Nat := [239122864, 201370952, 204553484, 241347849, 202619178, 167887278, 238235947, 68338063, 202386697, 134292747, 135511501, 67220746, 204614952, 202457422, 235028910, 135478605, 238207375, 171981232, 201567528, 235027820, 101725583, 201505034, 170110248, 67289549, 100843981, 68302122, 204517704]

def C30_rows : List Nat := [10, 28, 33, 34, 36, 66, 81, 84, 3, 5, 9, 6, 18, 40, 72, 48, 96]
def C30_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C30_rows)
def C30_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def C30_ori : List Nat → List Nat := qCompactOrient 2 C30_routeCodes
def C30_Z (s : Nat) : Nat → Bool :=
  barFastOrbit (compactGoal 8 9) (compactCover 8 9) C30_S C30_N C30_idx C30_ori
    C30_coords 5 C30_rankPool s
def C30_F : Nat → Bool := certAt C30_Z C30_N 12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_enc_goal : encL C0_f C0_rows = compactGoal 8 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_proper : ∀ zs ∈ C0_xs.sublists, zs ≠ C0_xs → compactCover 8 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_initial_perm : C0_xs.Perm (C0_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_good : qCompactGood (compactGoal 8 7) 8 C0_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_b0 : span C0_F 161 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C1_enc_goal : encL C1_f C1_rows = compactGoal 10 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C1_proper : ∀ zs ∈ C1_xs.sublists, zs ≠ C1_xs → compactCover 10 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C1_initial_perm : C1_xs.Perm (C1_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C1_good : qCompactGood (compactGoal 10 7) 16 C1_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C1_b0 : span C1_F 85 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C2_enc_goal : encL C2_f C2_rows = compactGoal 9 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C2_proper : ∀ zs ∈ C2_xs.sublists, zs ≠ C2_xs → compactCover 9 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C2_initial_perm : C2_xs.Perm (C2_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C2_good : qCompactGood (compactGoal 9 7) 4 C2_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C2_b0 : span C2_F 106 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C3_enc_goal : encL C3_f C3_rows = compactGoal 8 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C3_proper : ∀ zs ∈ C3_xs.sublists, zs ≠ C3_xs → compactCover 8 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C3_initial_perm : C3_xs.Perm (C3_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C3_good : qCompactGood (compactGoal 8 7) 2 C3_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C3_b0 : span C3_F 110 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_enc_goal : encL C4_f C4_rows = compactGoal 8 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_proper : ∀ zs ∈ C4_xs.sublists, zs ≠ C4_xs → compactCover 8 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_initial_perm : C4_xs.Perm (C4_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_good : qCompactGood (compactGoal 8 7) 2 C4_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_b0 : span C4_F 195 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C5_enc_goal : encL C5_f C5_rows = compactGoal 8 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C5_proper : ∀ zs ∈ C5_xs.sublists, zs ≠ C5_xs → compactCover 8 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C5_initial_perm : C5_xs.Perm (C5_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C5_good : qCompactGood (compactGoal 8 7) 2 C5_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C5_b0 : span C5_F 122 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C6_enc_goal : encL C6_f C6_rows = compactGoal 9 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C6_proper : ∀ zs ∈ C6_xs.sublists, zs ≠ C6_xs → compactCover 9 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C6_initial_perm : C6_xs.Perm (C6_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C6_good : qCompactGood (compactGoal 9 7) 12 C6_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C6_b0 : span C6_F 72 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C7_enc_goal : encL C7_f C7_rows = compactGoal 8 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C7_proper : ∀ zs ∈ C7_xs.sublists, zs ≠ C7_xs → compactCover 8 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C7_initial_perm : C7_xs.Perm (C7_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C7_good : qCompactGood (compactGoal 8 7) 2 C7_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C7_b0 : span C7_F 89 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C8_enc_goal : encL C8_f C8_rows = compactGoal 7 7 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C8_proper : ∀ zs ∈ C8_xs.sublists, zs ≠ C8_xs → compactCover 7 7 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C8_initial_perm : C8_xs.Perm (C8_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C8_good : qCompactGood (compactGoal 7 7) 14 C8_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C8_b0 : span C8_F 14 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C9_enc_goal : encL C9_f C9_rows = compactGoal 5 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C9_proper : ∀ zs ∈ C9_xs.sublists, zs ≠ C9_xs → compactCover 5 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C9_initial_perm : C9_xs.Perm (C9_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C9_good : qCompactGood (compactGoal 5 8) 16 C9_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C9_b0 : span C9_F 122 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_enc_goal : encL C10_f C10_rows = compactGoal 5 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_proper : ∀ zs ∈ C10_xs.sublists, zs ≠ C10_xs → compactCover 5 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_initial_perm : C10_xs.Perm (C10_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_good : qCompactGood (compactGoal 5 8) 2 C10_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_b0 : span C10_F 228 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_enc_goal : encL C11_f C11_rows = compactGoal 9 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_proper : ∀ zs ∈ C11_xs.sublists, zs ≠ C11_xs → compactCover 9 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_initial_perm : C11_xs.Perm (C11_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_good : qCompactGood (compactGoal 9 8) 8 C11_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b0 : span C11_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b1 : span C11_F 68 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_enc_goal : encL C12_f C12_rows = compactGoal 5 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_proper : ∀ zs ∈ C12_xs.sublists, zs ≠ C12_xs → compactCover 5 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_initial_perm : C12_xs.Perm (C12_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_good : qCompactGood (compactGoal 5 8) 4 C12_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_b0 : span C12_F 209 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_enc_goal : encL C13_f C13_rows = compactGoal 7 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_proper : ∀ zs ∈ C13_xs.sublists, zs ≠ C13_xs → compactCover 7 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_initial_perm : C13_xs.Perm (C13_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_good : qCompactGood (compactGoal 7 8) 4 C13_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b0 : span C13_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b1 : span C13_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b2 : span C13_F 78 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C14_enc_goal : encL C14_f C14_rows = compactGoal 5 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C14_proper : ∀ zs ∈ C14_xs.sublists, zs ≠ C14_xs → compactCover 5 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C14_initial_perm : C14_xs.Perm (C14_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C14_good : qCompactGood (compactGoal 5 8) 2 C14_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C14_b0 : span C14_F 115 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_enc_goal : encL C15_f C15_rows = compactGoal 8 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_proper : ∀ zs ∈ C15_xs.sublists, zs ≠ C15_xs → compactCover 8 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_initial_perm : C15_xs.Perm (C15_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_good : qCompactGood (compactGoal 8 8) 2 C15_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b0 : span C15_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b1 : span C15_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b2 : span C15_F 175 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_enc_goal : encL C16_f C16_rows = compactGoal 6 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_proper : ∀ zs ∈ C16_xs.sublists, zs ≠ C16_xs → compactCover 6 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_initial_perm : C16_xs.Perm (C16_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_good : qCompactGood (compactGoal 6 8) 1 C16_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_b0 : span C16_F 154 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_enc_goal : encL C17_f C17_rows = compactGoal 8 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_proper : ∀ zs ∈ C17_xs.sublists, zs ≠ C17_xs → compactCover 8 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_initial_perm : C17_xs.Perm (C17_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_good : qCompactGood (compactGoal 8 8) 4 C17_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b0 : span C17_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b1 : span C17_F 471 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_enc_goal : encL C18_f C18_rows = compactGoal 8 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_proper : ∀ zs ∈ C18_xs.sublists, zs ≠ C18_xs → compactCover 8 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_initial_perm : C18_xs.Perm (C18_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_good : qCompactGood (compactGoal 8 8) 4 C18_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_b0 : span C18_F 391 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_enc_goal : encL C19_f C19_rows = compactGoal 7 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_proper : ∀ zs ∈ C19_xs.sublists, zs ≠ C19_xs → compactCover 7 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_initial_perm : C19_xs.Perm (C19_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_good : qCompactGood (compactGoal 7 8) 2 C19_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b0 : span C19_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b1 : span C19_F 286 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_enc_goal : encL C20_f C20_rows = compactGoal 7 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_proper : ∀ zs ∈ C20_xs.sublists, zs ≠ C20_xs → compactCover 7 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_initial_perm : C20_xs.Perm (C20_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_good : qCompactGood (compactGoal 7 8) 1 C20_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b0 : span C20_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b1 : span C20_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b2 : span C20_F 475 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_enc_goal : encL C21_f C21_rows = compactGoal 8 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_proper : ∀ zs ∈ C21_xs.sublists, zs ≠ C21_xs → compactCover 8 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_initial_perm : C21_xs.Perm (C21_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_good : qCompactGood (compactGoal 8 8) 2 C21_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b0 : span C21_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b1 : span C21_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b2 : span C21_F 142 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C22_enc_goal : encL C22_f C22_rows = compactGoal 6 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C22_proper : ∀ zs ∈ C22_xs.sublists, zs ≠ C22_xs → compactCover 6 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C22_initial_perm : C22_xs.Perm (C22_S 9 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C22_good : qCompactGood (compactGoal 6 8) 2 C22_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C22_b0 : span C22_F 85 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_enc_goal : encL C23_f C23_rows = compactGoal 7 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_proper : ∀ zs ∈ C23_xs.sublists, zs ≠ C23_xs → compactCover 7 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_initial_perm : C23_xs.Perm (C23_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_good : qCompactGood (compactGoal 7 8) 2 C23_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_b0 : span C23_F 430 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_enc_goal : encL C24_f C24_rows = compactGoal 9 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_proper : ∀ zs ∈ C24_xs.sublists, zs ≠ C24_xs → compactCover 9 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_initial_perm : C24_xs.Perm (C24_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_good : qCompactGood (compactGoal 9 8) 8 C24_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_b0 : span C24_F 248 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_enc_goal : encL C25_f C25_rows = compactGoal 7 8 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_proper : ∀ zs ∈ C25_xs.sublists, zs ≠ C25_xs → compactCover 7 8 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_initial_perm : C25_xs.Perm (C25_S 10 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_good : qCompactGood (compactGoal 7 8) 4 C25_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_b0 : span C25_F 255 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_enc_goal : encL C26_f C26_rows = compactGoal 9 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_proper : ∀ zs ∈ C26_xs.sublists, zs ≠ C26_xs → compactCover 9 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_initial_perm : C26_xs.Perm (C26_S 11 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_good : qCompactGood (compactGoal 9 9) 48 C26_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b0 : span C26_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b1 : span C26_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b2 : span C26_F 43 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_enc_goal : encL C27_f C27_rows = compactGoal 8 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_proper : ∀ zs ∈ C27_xs.sublists, zs ≠ C27_xs → compactCover 8 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_initial_perm : C27_xs.Perm (C27_S 11 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_good : qCompactGood (compactGoal 8 9) 8 C27_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b0 : span C27_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b1 : span C27_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b2 : span C27_F 512 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b3 : span C27_F 512 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b4 : span C27_F 512 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b5 : span C27_F 512 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b6 : span C27_F 52 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_enc_goal : encL C28_f C28_rows = compactGoal 7 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_proper : ∀ zs ∈ C28_xs.sublists, zs ≠ C28_xs → compactCover 7 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_initial_perm : C28_xs.Perm (C28_S 11 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_good : qCompactGood (compactGoal 7 9) 2 C28_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b0 : span C28_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b1 : span C28_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b2 : span C28_F 512 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b3 : span C28_F 512 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b4 : span C28_F 512 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b5 : span C28_F 512 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b6 : span C28_F 512 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b7 : span C28_F 512 3584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b8 : span C28_F 512 4096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b9 : span C28_F 512 4608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b10 : span C28_F 512 5120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b11 : span C28_F 110 5632 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_enc_goal : encL C29_f C29_rows = compactGoal 7 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_proper : ∀ zs ∈ C29_xs.sublists, zs ≠ C29_xs → compactCover 7 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_initial_perm : C29_xs.Perm (C29_S 11 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_good : qCompactGood (compactGoal 7 9) 6 C29_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b0 : span C29_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b1 : span C29_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b2 : span C29_F 512 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b3 : span C29_F 486 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_enc_goal : encL C30_f C30_rows = compactGoal 8 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_proper : ∀ zs ∈ C30_xs.sublists, zs ≠ C30_xs → compactCover 8 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_initial_perm : C30_xs.Perm (C30_S 11 0) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_good : qCompactGood (compactGoal 8 9) 2 C30_routeCodes := by
  unfold qCompactGood
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b0 : span C30_F 512 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b1 : span C30_F 512 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b2 : span C30_F 512 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b3 : span C30_F 512 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b4 : span C30_F 512 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b5 : span C30_F 512 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b6 : span C30_F 512 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b7 : span C30_F 512 3584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b8 : span C30_F 512 4096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b9 : span C30_F 512 4608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b10 : span C30_F 190 5120 = true := by decide +kernel
theorem C0_nonconstant : ∃ x y : Fin 6 → Bool, C0_f x ≠ C0_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C0_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C0_ori ws) := qCompactOrient_run h C0_good
theorem C0_checked : ∀ s ≤ 9, ∀ j < C0_N s, C0_Z s j = true := by
  apply certFlat_sound
  change span C0_F 161 0 = true
  exact C0_b0
theorem C0_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C0_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C0_S) (N := C0_N) (idx := C0_idx) (ori := C0_ori)
    (coords := C0_coords) (bw := 4) (pool := C0_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C0_ori_run C0_checked
    (by decide) (by decide) C0_initial_perm
theorem C0_no_small : ¬ HasMonoSize 6 C0_f 9 :=
  encoded_compact_exclusion C0_f C0_nonconstant 9 C0_rows C0_xs 8 7
    rfl C0_enc_goal C0_proper C0_no_run
theorem C0_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = C0_f x) :
    10 ≤ C.size := mono_lower C0_f 9 C0_no_small C hmono hev
theorem C1_nonconstant : ∃ x y : Fin 7 → Bool, C1_f x ≠ C1_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C1_ori_run {s ws} (h : MonRun (compactGoal 10 7) s ws) :
    MonRun (compactGoal 10 7) s (C1_ori ws) := qCompactOrient_run h C1_good
theorem C1_checked : ∀ s ≤ 9, ∀ j < C1_N s, C1_Z s j = true := by
  apply certFlat_sound
  change span C1_F 85 0 = true
  exact C1_b0
theorem C1_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 10 7) s C1_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 10 7) (cover := compactCover 10 7)
    (S := C1_S) (N := C1_N) (idx := C1_idx) (ori := C1_ori)
    (coords := C1_coords) (bw := 4) (pool := C1_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C1_ori_run C1_checked
    (by decide) (by decide) C1_initial_perm
theorem C1_no_small : ¬ HasMonoSize 7 C1_f 9 :=
  encoded_compact_exclusion C1_f C1_nonconstant 9 C1_rows C1_xs 10 7
    rfl C1_enc_goal C1_proper C1_no_run
theorem C1_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C1_f x) :
    10 ≤ C.size := mono_lower C1_f 9 C1_no_small C hmono hev
theorem C2_nonconstant : ∃ x y : Fin 7 → Bool, C2_f x ≠ C2_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C2_ori_run {s ws} (h : MonRun (compactGoal 9 7) s ws) :
    MonRun (compactGoal 9 7) s (C2_ori ws) := qCompactOrient_run h C2_good
theorem C2_checked : ∀ s ≤ 9, ∀ j < C2_N s, C2_Z s j = true := by
  apply certFlat_sound
  change span C2_F 106 0 = true
  exact C2_b0
theorem C2_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 9 7) s C2_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 9 7) (cover := compactCover 9 7)
    (S := C2_S) (N := C2_N) (idx := C2_idx) (ori := C2_ori)
    (coords := C2_coords) (bw := 4) (pool := C2_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C2_ori_run C2_checked
    (by decide) (by decide) C2_initial_perm
theorem C2_no_small : ¬ HasMonoSize 7 C2_f 9 :=
  encoded_compact_exclusion C2_f C2_nonconstant 9 C2_rows C2_xs 9 7
    rfl C2_enc_goal C2_proper C2_no_run
theorem C2_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C2_f x) :
    10 ≤ C.size := mono_lower C2_f 9 C2_no_small C hmono hev
theorem C3_nonconstant : ∃ x y : Fin 7 → Bool, C3_f x ≠ C3_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C3_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C3_ori ws) := qCompactOrient_run h C3_good
theorem C3_checked : ∀ s ≤ 9, ∀ j < C3_N s, C3_Z s j = true := by
  apply certFlat_sound
  change span C3_F 110 0 = true
  exact C3_b0
theorem C3_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C3_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C3_S) (N := C3_N) (idx := C3_idx) (ori := C3_ori)
    (coords := C3_coords) (bw := 4) (pool := C3_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C3_ori_run C3_checked
    (by decide) (by decide) C3_initial_perm
theorem C3_no_small : ¬ HasMonoSize 7 C3_f 9 :=
  encoded_compact_exclusion C3_f C3_nonconstant 9 C3_rows C3_xs 8 7
    rfl C3_enc_goal C3_proper C3_no_run
theorem C3_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C3_f x) :
    10 ≤ C.size := mono_lower C3_f 9 C3_no_small C hmono hev
theorem C4_nonconstant : ∃ x y : Fin 7 → Bool, C4_f x ≠ C4_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C4_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C4_ori ws) := qCompactOrient_run h C4_good
theorem C4_checked : ∀ s ≤ 9, ∀ j < C4_N s, C4_Z s j = true := by
  apply certFlat_sound
  change span C4_F 195 0 = true
  exact C4_b0
theorem C4_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C4_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C4_S) (N := C4_N) (idx := C4_idx) (ori := C4_ori)
    (coords := C4_coords) (bw := 4) (pool := C4_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C4_ori_run C4_checked
    (by decide) (by decide) C4_initial_perm
theorem C4_no_small : ¬ HasMonoSize 7 C4_f 9 :=
  encoded_compact_exclusion C4_f C4_nonconstant 9 C4_rows C4_xs 8 7
    rfl C4_enc_goal C4_proper C4_no_run
theorem C4_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C4_f x) :
    10 ≤ C.size := mono_lower C4_f 9 C4_no_small C hmono hev
theorem C5_nonconstant : ∃ x y : Fin 7 → Bool, C5_f x ≠ C5_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C5_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C5_ori ws) := qCompactOrient_run h C5_good
theorem C5_checked : ∀ s ≤ 9, ∀ j < C5_N s, C5_Z s j = true := by
  apply certFlat_sound
  change span C5_F 122 0 = true
  exact C5_b0
theorem C5_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C5_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C5_S) (N := C5_N) (idx := C5_idx) (ori := C5_ori)
    (coords := C5_coords) (bw := 4) (pool := C5_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C5_ori_run C5_checked
    (by decide) (by decide) C5_initial_perm
theorem C5_no_small : ¬ HasMonoSize 7 C5_f 9 :=
  encoded_compact_exclusion C5_f C5_nonconstant 9 C5_rows C5_xs 8 7
    rfl C5_enc_goal C5_proper C5_no_run
theorem C5_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C5_f x) :
    10 ≤ C.size := mono_lower C5_f 9 C5_no_small C hmono hev
theorem C6_nonconstant : ∃ x y : Fin 7 → Bool, C6_f x ≠ C6_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C6_ori_run {s ws} (h : MonRun (compactGoal 9 7) s ws) :
    MonRun (compactGoal 9 7) s (C6_ori ws) := qCompactOrient_run h C6_good
theorem C6_checked : ∀ s ≤ 9, ∀ j < C6_N s, C6_Z s j = true := by
  apply certFlat_sound
  change span C6_F 72 0 = true
  exact C6_b0
theorem C6_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 9 7) s C6_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 9 7) (cover := compactCover 9 7)
    (S := C6_S) (N := C6_N) (idx := C6_idx) (ori := C6_ori)
    (coords := C6_coords) (bw := 4) (pool := C6_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C6_ori_run C6_checked
    (by decide) (by decide) C6_initial_perm
theorem C6_no_small : ¬ HasMonoSize 7 C6_f 9 :=
  encoded_compact_exclusion C6_f C6_nonconstant 9 C6_rows C6_xs 9 7
    rfl C6_enc_goal C6_proper C6_no_run
theorem C6_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C6_f x) :
    10 ≤ C.size := mono_lower C6_f 9 C6_no_small C hmono hev
theorem C7_nonconstant : ∃ x y : Fin 7 → Bool, C7_f x ≠ C7_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C7_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C7_ori ws) := qCompactOrient_run h C7_good
theorem C7_checked : ∀ s ≤ 9, ∀ j < C7_N s, C7_Z s j = true := by
  apply certFlat_sound
  change span C7_F 89 0 = true
  exact C7_b0
theorem C7_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C7_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C7_S) (N := C7_N) (idx := C7_idx) (ori := C7_ori)
    (coords := C7_coords) (bw := 4) (pool := C7_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C7_ori_run C7_checked
    (by decide) (by decide) C7_initial_perm
theorem C7_no_small : ¬ HasMonoSize 7 C7_f 9 :=
  encoded_compact_exclusion C7_f C7_nonconstant 9 C7_rows C7_xs 8 7
    rfl C7_enc_goal C7_proper C7_no_run
theorem C7_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C7_f x) :
    10 ≤ C.size := mono_lower C7_f 9 C7_no_small C hmono hev
theorem C8_nonconstant : ∃ x y : Fin 7 → Bool, C8_f x ≠ C8_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C8_ori_run {s ws} (h : MonRun (compactGoal 7 7) s ws) :
    MonRun (compactGoal 7 7) s (C8_ori ws) := qCompactOrient_run h C8_good
theorem C8_checked : ∀ s ≤ 9, ∀ j < C8_N s, C8_Z s j = true := by
  apply certFlat_sound
  change span C8_F 14 0 = true
  exact C8_b0
theorem C8_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 7 7) s C8_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 7) (cover := compactCover 7 7)
    (S := C8_S) (N := C8_N) (idx := C8_idx) (ori := C8_ori)
    (coords := C8_coords) (bw := 4) (pool := C8_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C8_ori_run C8_checked
    (by decide) (by decide) C8_initial_perm
theorem C8_no_small : ¬ HasMonoSize 7 C8_f 9 :=
  encoded_compact_exclusion C8_f C8_nonconstant 9 C8_rows C8_xs 7 7
    rfl C8_enc_goal C8_proper C8_no_run
theorem C8_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C8_f x) :
    10 ≤ C.size := mono_lower C8_f 9 C8_no_small C hmono hev
theorem C9_nonconstant : ∃ x y : Fin 7 → Bool, C9_f x ≠ C9_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C9_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C9_ori ws) := qCompactOrient_run h C9_good
theorem C9_checked : ∀ s ≤ 9, ∀ j < C9_N s, C9_Z s j = true := by
  apply certFlat_sound
  change span C9_F 122 0 = true
  exact C9_b0
theorem C9_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C9_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C9_S) (N := C9_N) (idx := C9_idx) (ori := C9_ori)
    (coords := C9_coords) (bw := 4) (pool := C9_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C9_ori_run C9_checked
    (by decide) (by decide) C9_initial_perm
theorem C9_no_small : ¬ HasMonoSize 7 C9_f 9 :=
  encoded_compact_exclusion C9_f C9_nonconstant 9 C9_rows C9_xs 5 8
    rfl C9_enc_goal C9_proper C9_no_run
theorem C9_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C9_f x) :
    10 ≤ C.size := mono_lower C9_f 9 C9_no_small C hmono hev
theorem C10_nonconstant : ∃ x y : Fin 7 → Bool, C10_f x ≠ C10_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C10_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C10_ori ws) := qCompactOrient_run h C10_good
theorem C10_checked : ∀ s ≤ 9, ∀ j < C10_N s, C10_Z s j = true := by
  apply certFlat_sound
  change span C10_F 228 0 = true
  exact C10_b0
theorem C10_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C10_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C10_S) (N := C10_N) (idx := C10_idx) (ori := C10_ori)
    (coords := C10_coords) (bw := 4) (pool := C10_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C10_ori_run C10_checked
    (by decide) (by decide) C10_initial_perm
theorem C10_no_small : ¬ HasMonoSize 7 C10_f 9 :=
  encoded_compact_exclusion C10_f C10_nonconstant 9 C10_rows C10_xs 5 8
    rfl C10_enc_goal C10_proper C10_no_run
theorem C10_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C10_f x) :
    10 ≤ C.size := mono_lower C10_f 9 C10_no_small C hmono hev
theorem C11_nonconstant : ∃ x y : Fin 7 → Bool, C11_f x ≠ C11_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C11_ori_run {s ws} (h : MonRun (compactGoal 9 8) s ws) :
    MonRun (compactGoal 9 8) s (C11_ori ws) := qCompactOrient_run h C11_good
theorem C11_j0 : span C11_F 580 0 = true :=
  span_join C11_b0 C11_b1
theorem C11_checked : ∀ s ≤ 10, ∀ j < C11_N s, C11_Z s j = true := by
  apply certFlat_sound
  change span C11_F 580 0 = true
  exact C11_j0
theorem C11_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 9 8) s C11_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 9 8) (cover := compactCover 9 8)
    (S := C11_S) (N := C11_N) (idx := C11_idx) (ori := C11_ori)
    (coords := C11_coords) (bw := 5) (pool := C11_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C11_ori_run C11_checked
    (by decide) (by decide) C11_initial_perm
theorem C11_no_small : ¬ HasMonoSize 7 C11_f 10 :=
  encoded_compact_exclusion C11_f C11_nonconstant 10 C11_rows C11_xs 9 8
    rfl C11_enc_goal C11_proper C11_no_run
theorem C11_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C11_f x) :
    11 ≤ C.size := mono_lower C11_f 10 C11_no_small C hmono hev
theorem C12_nonconstant : ∃ x y : Fin 7 → Bool, C12_f x ≠ C12_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C12_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C12_ori ws) := qCompactOrient_run h C12_good
theorem C12_checked : ∀ s ≤ 9, ∀ j < C12_N s, C12_Z s j = true := by
  apply certFlat_sound
  change span C12_F 209 0 = true
  exact C12_b0
theorem C12_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C12_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C12_S) (N := C12_N) (idx := C12_idx) (ori := C12_ori)
    (coords := C12_coords) (bw := 4) (pool := C12_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C12_ori_run C12_checked
    (by decide) (by decide) C12_initial_perm
theorem C12_no_small : ¬ HasMonoSize 7 C12_f 9 :=
  encoded_compact_exclusion C12_f C12_nonconstant 9 C12_rows C12_xs 5 8
    rfl C12_enc_goal C12_proper C12_no_run
theorem C12_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C12_f x) :
    10 ≤ C.size := mono_lower C12_f 9 C12_no_small C hmono hev
theorem C13_nonconstant : ∃ x y : Fin 7 → Bool, C13_f x ≠ C13_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C13_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C13_ori ws) := qCompactOrient_run h C13_good
theorem C13_j0 : span C13_F 590 512 = true :=
  span_join C13_b1 C13_b2
theorem C13_j1 : span C13_F 1102 0 = true :=
  span_join C13_b0 C13_j0
theorem C13_checked : ∀ s ≤ 10, ∀ j < C13_N s, C13_Z s j = true := by
  apply certFlat_sound
  change span C13_F 1102 0 = true
  exact C13_j1
theorem C13_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C13_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C13_S) (N := C13_N) (idx := C13_idx) (ori := C13_ori)
    (coords := C13_coords) (bw := 4) (pool := C13_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C13_ori_run C13_checked
    (by decide) (by decide) C13_initial_perm
theorem C13_no_small : ¬ HasMonoSize 7 C13_f 10 :=
  encoded_compact_exclusion C13_f C13_nonconstant 10 C13_rows C13_xs 7 8
    rfl C13_enc_goal C13_proper C13_no_run
theorem C13_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C13_f x) :
    11 ≤ C.size := mono_lower C13_f 10 C13_no_small C hmono hev
theorem C14_nonconstant : ∃ x y : Fin 7 → Bool, C14_f x ≠ C14_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C14_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C14_ori ws) := qCompactOrient_run h C14_good
theorem C14_checked : ∀ s ≤ 9, ∀ j < C14_N s, C14_Z s j = true := by
  apply certFlat_sound
  change span C14_F 115 0 = true
  exact C14_b0
theorem C14_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C14_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C14_S) (N := C14_N) (idx := C14_idx) (ori := C14_ori)
    (coords := C14_coords) (bw := 4) (pool := C14_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C14_ori_run C14_checked
    (by decide) (by decide) C14_initial_perm
theorem C14_no_small : ¬ HasMonoSize 7 C14_f 9 :=
  encoded_compact_exclusion C14_f C14_nonconstant 9 C14_rows C14_xs 5 8
    rfl C14_enc_goal C14_proper C14_no_run
theorem C14_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C14_f x) :
    10 ≤ C.size := mono_lower C14_f 9 C14_no_small C hmono hev
theorem C15_nonconstant : ∃ x y : Fin 7 → Bool, C15_f x ≠ C15_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C15_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C15_ori ws) := qCompactOrient_run h C15_good
theorem C15_j0 : span C15_F 687 512 = true :=
  span_join C15_b1 C15_b2
theorem C15_j1 : span C15_F 1199 0 = true :=
  span_join C15_b0 C15_j0
theorem C15_checked : ∀ s ≤ 10, ∀ j < C15_N s, C15_Z s j = true := by
  apply certFlat_sound
  change span C15_F 1199 0 = true
  exact C15_j1
theorem C15_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C15_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C15_S) (N := C15_N) (idx := C15_idx) (ori := C15_ori)
    (coords := C15_coords) (bw := 4) (pool := C15_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C15_ori_run C15_checked
    (by decide) (by decide) C15_initial_perm
theorem C15_no_small : ¬ HasMonoSize 7 C15_f 10 :=
  encoded_compact_exclusion C15_f C15_nonconstant 10 C15_rows C15_xs 8 8
    rfl C15_enc_goal C15_proper C15_no_run
theorem C15_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C15_f x) :
    11 ≤ C.size := mono_lower C15_f 10 C15_no_small C hmono hev
theorem C16_nonconstant : ∃ x y : Fin 7 → Bool, C16_f x ≠ C16_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C16_ori_run {s ws} (h : MonRun (compactGoal 6 8) s ws) :
    MonRun (compactGoal 6 8) s (C16_ori ws) := qCompactOrient_run h C16_good
theorem C16_checked : ∀ s ≤ 9, ∀ j < C16_N s, C16_Z s j = true := by
  apply certFlat_sound
  change span C16_F 154 0 = true
  exact C16_b0
theorem C16_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 6 8) s C16_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 6 8) (cover := compactCover 6 8)
    (S := C16_S) (N := C16_N) (idx := C16_idx) (ori := C16_ori)
    (coords := C16_coords) (bw := 4) (pool := C16_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C16_ori_run C16_checked
    (by decide) (by decide) C16_initial_perm
theorem C16_no_small : ¬ HasMonoSize 7 C16_f 9 :=
  encoded_compact_exclusion C16_f C16_nonconstant 9 C16_rows C16_xs 6 8
    rfl C16_enc_goal C16_proper C16_no_run
theorem C16_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C16_f x) :
    10 ≤ C.size := mono_lower C16_f 9 C16_no_small C hmono hev
theorem C17_nonconstant : ∃ x y : Fin 7 → Bool, C17_f x ≠ C17_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C17_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C17_ori ws) := qCompactOrient_run h C17_good
theorem C17_j0 : span C17_F 983 0 = true :=
  span_join C17_b0 C17_b1
theorem C17_checked : ∀ s ≤ 10, ∀ j < C17_N s, C17_Z s j = true := by
  apply certFlat_sound
  change span C17_F 983 0 = true
  exact C17_j0
theorem C17_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C17_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C17_S) (N := C17_N) (idx := C17_idx) (ori := C17_ori)
    (coords := C17_coords) (bw := 4) (pool := C17_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C17_ori_run C17_checked
    (by decide) (by decide) C17_initial_perm
theorem C17_no_small : ¬ HasMonoSize 7 C17_f 10 :=
  encoded_compact_exclusion C17_f C17_nonconstant 10 C17_rows C17_xs 8 8
    rfl C17_enc_goal C17_proper C17_no_run
theorem C17_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C17_f x) :
    11 ≤ C.size := mono_lower C17_f 10 C17_no_small C hmono hev
theorem C18_nonconstant : ∃ x y : Fin 7 → Bool, C18_f x ≠ C18_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C18_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C18_ori ws) := qCompactOrient_run h C18_good
theorem C18_checked : ∀ s ≤ 10, ∀ j < C18_N s, C18_Z s j = true := by
  apply certFlat_sound
  change span C18_F 391 0 = true
  exact C18_b0
theorem C18_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C18_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C18_S) (N := C18_N) (idx := C18_idx) (ori := C18_ori)
    (coords := C18_coords) (bw := 4) (pool := C18_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C18_ori_run C18_checked
    (by decide) (by decide) C18_initial_perm
theorem C18_no_small : ¬ HasMonoSize 7 C18_f 10 :=
  encoded_compact_exclusion C18_f C18_nonconstant 10 C18_rows C18_xs 8 8
    rfl C18_enc_goal C18_proper C18_no_run
theorem C18_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C18_f x) :
    11 ≤ C.size := mono_lower C18_f 10 C18_no_small C hmono hev
theorem C19_nonconstant : ∃ x y : Fin 7 → Bool, C19_f x ≠ C19_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C19_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C19_ori ws) := qCompactOrient_run h C19_good
theorem C19_j0 : span C19_F 798 0 = true :=
  span_join C19_b0 C19_b1
theorem C19_checked : ∀ s ≤ 10, ∀ j < C19_N s, C19_Z s j = true := by
  apply certFlat_sound
  change span C19_F 798 0 = true
  exact C19_j0
theorem C19_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C19_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C19_S) (N := C19_N) (idx := C19_idx) (ori := C19_ori)
    (coords := C19_coords) (bw := 4) (pool := C19_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C19_ori_run C19_checked
    (by decide) (by decide) C19_initial_perm
theorem C19_no_small : ¬ HasMonoSize 7 C19_f 10 :=
  encoded_compact_exclusion C19_f C19_nonconstant 10 C19_rows C19_xs 7 8
    rfl C19_enc_goal C19_proper C19_no_run
theorem C19_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C19_f x) :
    11 ≤ C.size := mono_lower C19_f 10 C19_no_small C hmono hev
theorem C20_nonconstant : ∃ x y : Fin 7 → Bool, C20_f x ≠ C20_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C20_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C20_ori ws) := qCompactOrient_run h C20_good
theorem C20_j0 : span C20_F 987 512 = true :=
  span_join C20_b1 C20_b2
theorem C20_j1 : span C20_F 1499 0 = true :=
  span_join C20_b0 C20_j0
theorem C20_checked : ∀ s ≤ 10, ∀ j < C20_N s, C20_Z s j = true := by
  apply certFlat_sound
  change span C20_F 1499 0 = true
  exact C20_j1
theorem C20_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C20_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C20_S) (N := C20_N) (idx := C20_idx) (ori := C20_ori)
    (coords := C20_coords) (bw := 4) (pool := C20_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C20_ori_run C20_checked
    (by decide) (by decide) C20_initial_perm
theorem C20_no_small : ¬ HasMonoSize 7 C20_f 10 :=
  encoded_compact_exclusion C20_f C20_nonconstant 10 C20_rows C20_xs 7 8
    rfl C20_enc_goal C20_proper C20_no_run
theorem C20_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C20_f x) :
    11 ≤ C.size := mono_lower C20_f 10 C20_no_small C hmono hev
theorem C21_nonconstant : ∃ x y : Fin 7 → Bool, C21_f x ≠ C21_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C21_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C21_ori ws) := qCompactOrient_run h C21_good
theorem C21_j0 : span C21_F 654 512 = true :=
  span_join C21_b1 C21_b2
theorem C21_j1 : span C21_F 1166 0 = true :=
  span_join C21_b0 C21_j0
theorem C21_checked : ∀ s ≤ 10, ∀ j < C21_N s, C21_Z s j = true := by
  apply certFlat_sound
  change span C21_F 1166 0 = true
  exact C21_j1
theorem C21_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C21_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C21_S) (N := C21_N) (idx := C21_idx) (ori := C21_ori)
    (coords := C21_coords) (bw := 4) (pool := C21_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C21_ori_run C21_checked
    (by decide) (by decide) C21_initial_perm
theorem C21_no_small : ¬ HasMonoSize 7 C21_f 10 :=
  encoded_compact_exclusion C21_f C21_nonconstant 10 C21_rows C21_xs 8 8
    rfl C21_enc_goal C21_proper C21_no_run
theorem C21_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C21_f x) :
    11 ≤ C.size := mono_lower C21_f 10 C21_no_small C hmono hev
theorem C22_nonconstant : ∃ x y : Fin 7 → Bool, C22_f x ≠ C22_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C22_ori_run {s ws} (h : MonRun (compactGoal 6 8) s ws) :
    MonRun (compactGoal 6 8) s (C22_ori ws) := qCompactOrient_run h C22_good
theorem C22_checked : ∀ s ≤ 9, ∀ j < C22_N s, C22_Z s j = true := by
  apply certFlat_sound
  change span C22_F 85 0 = true
  exact C22_b0
theorem C22_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 6 8) s C22_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 6 8) (cover := compactCover 6 8)
    (S := C22_S) (N := C22_N) (idx := C22_idx) (ori := C22_ori)
    (coords := C22_coords) (bw := 4) (pool := C22_rankPool) (cap := 9) (i := 0)
    (fun h => compactCover_ok h) C22_ori_run C22_checked
    (by decide) (by decide) C22_initial_perm
theorem C22_no_small : ¬ HasMonoSize 7 C22_f 9 :=
  encoded_compact_exclusion C22_f C22_nonconstant 9 C22_rows C22_xs 6 8
    rfl C22_enc_goal C22_proper C22_no_run
theorem C22_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C22_f x) :
    10 ≤ C.size := mono_lower C22_f 9 C22_no_small C hmono hev
theorem C23_nonconstant : ∃ x y : Fin 7 → Bool, C23_f x ≠ C23_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C23_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C23_ori ws) := qCompactOrient_run h C23_good
theorem C23_checked : ∀ s ≤ 10, ∀ j < C23_N s, C23_Z s j = true := by
  apply certFlat_sound
  change span C23_F 430 0 = true
  exact C23_b0
theorem C23_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C23_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C23_S) (N := C23_N) (idx := C23_idx) (ori := C23_ori)
    (coords := C23_coords) (bw := 4) (pool := C23_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C23_ori_run C23_checked
    (by decide) (by decide) C23_initial_perm
theorem C23_no_small : ¬ HasMonoSize 7 C23_f 10 :=
  encoded_compact_exclusion C23_f C23_nonconstant 10 C23_rows C23_xs 7 8
    rfl C23_enc_goal C23_proper C23_no_run
theorem C23_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C23_f x) :
    11 ≤ C.size := mono_lower C23_f 10 C23_no_small C hmono hev
theorem C24_nonconstant : ∃ x y : Fin 7 → Bool, C24_f x ≠ C24_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C24_ori_run {s ws} (h : MonRun (compactGoal 9 8) s ws) :
    MonRun (compactGoal 9 8) s (C24_ori ws) := qCompactOrient_run h C24_good
theorem C24_checked : ∀ s ≤ 10, ∀ j < C24_N s, C24_Z s j = true := by
  apply certFlat_sound
  change span C24_F 248 0 = true
  exact C24_b0
theorem C24_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 9 8) s C24_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 9 8) (cover := compactCover 9 8)
    (S := C24_S) (N := C24_N) (idx := C24_idx) (ori := C24_ori)
    (coords := C24_coords) (bw := 5) (pool := C24_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C24_ori_run C24_checked
    (by decide) (by decide) C24_initial_perm
theorem C24_no_small : ¬ HasMonoSize 7 C24_f 10 :=
  encoded_compact_exclusion C24_f C24_nonconstant 10 C24_rows C24_xs 9 8
    rfl C24_enc_goal C24_proper C24_no_run
theorem C24_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C24_f x) :
    11 ≤ C.size := mono_lower C24_f 10 C24_no_small C hmono hev
theorem C25_nonconstant : ∃ x y : Fin 7 → Bool, C25_f x ≠ C25_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C25_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C25_ori ws) := qCompactOrient_run h C25_good
theorem C25_checked : ∀ s ≤ 10, ∀ j < C25_N s, C25_Z s j = true := by
  apply certFlat_sound
  change span C25_F 255 0 = true
  exact C25_b0
theorem C25_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C25_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C25_S) (N := C25_N) (idx := C25_idx) (ori := C25_ori)
    (coords := C25_coords) (bw := 4) (pool := C25_rankPool) (cap := 10) (i := 0)
    (fun h => compactCover_ok h) C25_ori_run C25_checked
    (by decide) (by decide) C25_initial_perm
theorem C25_no_small : ¬ HasMonoSize 7 C25_f 10 :=
  encoded_compact_exclusion C25_f C25_nonconstant 10 C25_rows C25_xs 7 8
    rfl C25_enc_goal C25_proper C25_no_run
theorem C25_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C25_f x) :
    11 ≤ C.size := mono_lower C25_f 10 C25_no_small C hmono hev
theorem C26_nonconstant : ∃ x y : Fin 7 → Bool, C26_f x ≠ C26_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C26_ori_run {s ws} (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_ori ws) := qCompactOrient_run h C26_good
theorem C26_j0 : span C26_F 555 512 = true :=
  span_join C26_b1 C26_b2
theorem C26_j1 : span C26_F 1067 0 = true :=
  span_join C26_b0 C26_j0
theorem C26_checked : ∀ s ≤ 11, ∀ j < C26_N s, C26_Z s j = true := by
  apply certFlat_sound
  change span C26_F 1067 0 = true
  exact C26_j1
theorem C26_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 9 9) s C26_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 9 9) (cover := compactCover 9 9)
    (S := C26_S) (N := C26_N) (idx := C26_idx) (ori := C26_ori)
    (coords := C26_coords) (bw := 5) (pool := C26_rankPool) (cap := 11) (i := 0)
    (fun h => compactCover_ok h) C26_ori_run C26_checked
    (by decide) (by decide) C26_initial_perm
theorem C26_no_small : ¬ HasMonoSize 7 C26_f 11 :=
  encoded_compact_exclusion C26_f C26_nonconstant 11 C26_rows C26_xs 9 9
    rfl C26_enc_goal C26_proper C26_no_run
theorem C26_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C26_f x) :
    12 ≤ C.size := mono_lower C26_f 11 C26_no_small C hmono hev
theorem C27_nonconstant : ∃ x y : Fin 7 → Bool, C27_f x ≠ C27_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C27_ori_run {s ws} (h : MonRun (compactGoal 8 9) s ws) :
    MonRun (compactGoal 8 9) s (C27_ori ws) := qCompactOrient_run h C27_good
theorem C27_j0 : span C27_F 1024 512 = true :=
  span_join C27_b1 C27_b2
theorem C27_j1 : span C27_F 1536 0 = true :=
  span_join C27_b0 C27_j0
theorem C27_j2 : span C27_F 1024 1536 = true :=
  span_join C27_b3 C27_b4
theorem C27_j3 : span C27_F 564 2560 = true :=
  span_join C27_b5 C27_b6
theorem C27_j4 : span C27_F 1588 1536 = true :=
  span_join C27_j2 C27_j3
theorem C27_j5 : span C27_F 3124 0 = true :=
  span_join C27_j1 C27_j4
theorem C27_checked : ∀ s ≤ 11, ∀ j < C27_N s, C27_Z s j = true := by
  apply certFlat_sound
  change span C27_F 3124 0 = true
  exact C27_j5
theorem C27_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 8 9) s C27_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 9) (cover := compactCover 8 9)
    (S := C27_S) (N := C27_N) (idx := C27_idx) (ori := C27_ori)
    (coords := C27_coords) (bw := 5) (pool := C27_rankPool) (cap := 11) (i := 0)
    (fun h => compactCover_ok h) C27_ori_run C27_checked
    (by decide) (by decide) C27_initial_perm
theorem C27_no_small : ¬ HasMonoSize 7 C27_f 11 :=
  encoded_compact_exclusion C27_f C27_nonconstant 11 C27_rows C27_xs 8 9
    rfl C27_enc_goal C27_proper C27_no_run
theorem C27_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C27_f x) :
    12 ≤ C.size := mono_lower C27_f 11 C27_no_small C hmono hev
theorem C28_nonconstant : ∃ x y : Fin 7 → Bool, C28_f x ≠ C28_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C28_ori_run {s ws} (h : MonRun (compactGoal 7 9) s ws) :
    MonRun (compactGoal 7 9) s (C28_ori ws) := qCompactOrient_run h C28_good
theorem C28_j0 : span C28_F 1024 512 = true :=
  span_join C28_b1 C28_b2
theorem C28_j1 : span C28_F 1536 0 = true :=
  span_join C28_b0 C28_j0
theorem C28_j2 : span C28_F 1024 2048 = true :=
  span_join C28_b4 C28_b5
theorem C28_j3 : span C28_F 1536 1536 = true :=
  span_join C28_b3 C28_j2
theorem C28_j4 : span C28_F 3072 0 = true :=
  span_join C28_j1 C28_j3
theorem C28_j5 : span C28_F 1024 3584 = true :=
  span_join C28_b7 C28_b8
theorem C28_j6 : span C28_F 1536 3072 = true :=
  span_join C28_b6 C28_j5
theorem C28_j7 : span C28_F 622 5120 = true :=
  span_join C28_b10 C28_b11
theorem C28_j8 : span C28_F 1134 4608 = true :=
  span_join C28_b9 C28_j7
theorem C28_j9 : span C28_F 2670 3072 = true :=
  span_join C28_j6 C28_j8
theorem C28_j10 : span C28_F 5742 0 = true :=
  span_join C28_j4 C28_j9
theorem C28_checked : ∀ s ≤ 11, ∀ j < C28_N s, C28_Z s j = true := by
  apply certFlat_sound
  change span C28_F 5742 0 = true
  exact C28_j10
theorem C28_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 7 9) s C28_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 9) (cover := compactCover 7 9)
    (S := C28_S) (N := C28_N) (idx := C28_idx) (ori := C28_ori)
    (coords := C28_coords) (bw := 4) (pool := C28_rankPool) (cap := 11) (i := 0)
    (fun h => compactCover_ok h) C28_ori_run C28_checked
    (by decide) (by decide) C28_initial_perm
theorem C28_no_small : ¬ HasMonoSize 7 C28_f 11 :=
  encoded_compact_exclusion C28_f C28_nonconstant 11 C28_rows C28_xs 7 9
    rfl C28_enc_goal C28_proper C28_no_run
theorem C28_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C28_f x) :
    12 ≤ C.size := mono_lower C28_f 11 C28_no_small C hmono hev
theorem C29_nonconstant : ∃ x y : Fin 7 → Bool, C29_f x ≠ C29_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C29_ori_run {s ws} (h : MonRun (compactGoal 7 9) s ws) :
    MonRun (compactGoal 7 9) s (C29_ori ws) := qCompactOrient_run h C29_good
theorem C29_j0 : span C29_F 1024 0 = true :=
  span_join C29_b0 C29_b1
theorem C29_j1 : span C29_F 998 1024 = true :=
  span_join C29_b2 C29_b3
theorem C29_j2 : span C29_F 2022 0 = true :=
  span_join C29_j0 C29_j1
theorem C29_checked : ∀ s ≤ 11, ∀ j < C29_N s, C29_Z s j = true := by
  apply certFlat_sound
  change span C29_F 2022 0 = true
  exact C29_j2
theorem C29_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 7 9) s C29_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 7 9) (cover := compactCover 7 9)
    (S := C29_S) (N := C29_N) (idx := C29_idx) (ori := C29_ori)
    (coords := C29_coords) (bw := 4) (pool := C29_rankPool) (cap := 11) (i := 0)
    (fun h => compactCover_ok h) C29_ori_run C29_checked
    (by decide) (by decide) C29_initial_perm
theorem C29_no_small : ¬ HasMonoSize 7 C29_f 11 :=
  encoded_compact_exclusion C29_f C29_nonconstant 11 C29_rows C29_xs 7 9
    rfl C29_enc_goal C29_proper C29_no_run
theorem C29_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C29_f x) :
    12 ≤ C.size := mono_lower C29_f 11 C29_no_small C hmono hev
theorem C30_nonconstant : ∃ x y : Fin 7 → Bool, C30_f x ≠ C30_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C30_ori_run {s ws} (h : MonRun (compactGoal 8 9) s ws) :
    MonRun (compactGoal 8 9) s (C30_ori ws) := qCompactOrient_run h C30_good
theorem C30_j0 : span C30_F 1024 0 = true :=
  span_join C30_b0 C30_b1
theorem C30_j1 : span C30_F 1024 1536 = true :=
  span_join C30_b3 C30_b4
theorem C30_j2 : span C30_F 1536 1024 = true :=
  span_join C30_b2 C30_j1
theorem C30_j3 : span C30_F 2560 0 = true :=
  span_join C30_j0 C30_j2
theorem C30_j4 : span C30_F 1024 3072 = true :=
  span_join C30_b6 C30_b7
theorem C30_j5 : span C30_F 1536 2560 = true :=
  span_join C30_b5 C30_j4
theorem C30_j6 : span C30_F 702 4608 = true :=
  span_join C30_b9 C30_b10
theorem C30_j7 : span C30_F 1214 4096 = true :=
  span_join C30_b8 C30_j6
theorem C30_j8 : span C30_F 2750 2560 = true :=
  span_join C30_j5 C30_j7
theorem C30_j9 : span C30_F 5310 0 = true :=
  span_join C30_j3 C30_j8
theorem C30_checked : ∀ s ≤ 11, ∀ j < C30_N s, C30_Z s j = true := by
  apply certFlat_sound
  change span C30_F 5310 0 = true
  exact C30_j9
theorem C30_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 8 9) s C30_xs := by
  exact noRun_from_barFastOrbit (y := compactGoal 8 9) (cover := compactCover 8 9)
    (S := C30_S) (N := C30_N) (idx := C30_idx) (ori := C30_ori)
    (coords := C30_coords) (bw := 5) (pool := C30_rankPool) (cap := 11) (i := 0)
    (fun h => compactCover_ok h) C30_ori_run C30_checked
    (by decide) (by decide) C30_initial_perm
theorem C30_no_small : ¬ HasMonoSize 7 C30_f 11 :=
  encoded_compact_exclusion C30_f C30_nonconstant 11 C30_rows C30_xs 8 9
    rfl C30_enc_goal C30_proper C30_no_run
theorem C30_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C30_f x) :
    12 ≤ C.size := mono_lower C30_f 11 C30_no_small C hmono hev
end PEqualNP.Outside.L_meta_984.Cert

theorem PEqualNP.Outside.L_meta_984 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact ⟨PEqualNP.Outside.L_meta_984.Cert.C0_lower, PEqualNP.Outside.L_meta_984.Cert.C1_lower, PEqualNP.Outside.L_meta_984.Cert.C2_lower, PEqualNP.Outside.L_meta_984.Cert.C3_lower, PEqualNP.Outside.L_meta_984.Cert.C4_lower, PEqualNP.Outside.L_meta_984.Cert.C5_lower, PEqualNP.Outside.L_meta_984.Cert.C6_lower, PEqualNP.Outside.L_meta_984.Cert.C7_lower, PEqualNP.Outside.L_meta_984.Cert.C8_lower, PEqualNP.Outside.L_meta_984.Cert.C9_lower, PEqualNP.Outside.L_meta_984.Cert.C10_lower, PEqualNP.Outside.L_meta_984.Cert.C11_lower, PEqualNP.Outside.L_meta_984.Cert.C12_lower, PEqualNP.Outside.L_meta_984.Cert.C13_lower, PEqualNP.Outside.L_meta_984.Cert.C14_lower, PEqualNP.Outside.L_meta_984.Cert.C15_lower, PEqualNP.Outside.L_meta_984.Cert.C16_lower, PEqualNP.Outside.L_meta_984.Cert.C17_lower, PEqualNP.Outside.L_meta_984.Cert.C18_lower, PEqualNP.Outside.L_meta_984.Cert.C19_lower, PEqualNP.Outside.L_meta_984.Cert.C20_lower, PEqualNP.Outside.L_meta_984.Cert.C21_lower, PEqualNP.Outside.L_meta_984.Cert.C22_lower, PEqualNP.Outside.L_meta_984.Cert.C23_lower, PEqualNP.Outside.L_meta_984.Cert.C24_lower, PEqualNP.Outside.L_meta_984.Cert.C25_lower, PEqualNP.Outside.L_meta_984.Cert.C26_lower, PEqualNP.Outside.L_meta_984.Cert.C27_lower, PEqualNP.Outside.L_meta_984.Cert.C28_lower, PEqualNP.Outside.L_meta_984.Cert.C29_lower, PEqualNP.Outside.L_meta_984.Cert.C30_lower⟩
