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

def barWithScore (y : Nat) (cover : List Nat → Bool)
    (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (score : Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (s+2-ws.length) ws fun zs => cover zs &&
      !(score s (ori zs)) && !(found S N idx s (ori zs)))

theorem barWithScore_eq {y cover S N idx ori score coords bw pool}
    (heq : ∀ s ws, score s ws = fastScr y s coords bw pool ws) (s i : Nat) :
    barWithScore y cover S N idx ori score s i =
      barFastOrbit y cover S N idx ori coords bw pool s i := by
  cases s <;> simp only [barWithScore,barFastOrbit,heq]

def barEarlyScore (y : Nat) (cover : List Nat → Bool)
    (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (early score : Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (s+2-ws.length) ws fun zs => cover zs && !(early s zs) &&
      !(score s (ori zs)) && !(found S N idx s (ori zs)))

theorem barEarlyScore_sound {y cover S N idx ori early score} {s i : Nat}
    (hb : barEarlyScore y cover S N idx ori early score s i = true)
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (hearly : ∀ {u ys}, MonRun y u ys → early u ys = false)
    (hscore : ∀ {u ys}, MonRun y u ys → score u ys = false)
    (hr : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (h : MonRun y s (S s i)) :
    ∃ q < s, ∃ j < N q, MonRun y q (S q j) := by
  cases s with
  | zero => simp [barEarlyScore, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := cover zs && !(early s zs) &&
      !(score s (ori zs)) && !(found S N idx s (ori zs))
    have hF (zs) (hz : MonRun y s zs) : F zs = true := by
      simp only [F, hcover hz, hearly hz, hscore (hr hz),
        Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barEarlyScore_all {y cover S N idx ori early score} {cap : Nat}
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (hearly : ∀ {u ys}, MonRun y u ys → early u ys = false)
    (hscore : ∀ {u ys}, MonRun y u ys → score u ys = false)
    (hr : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s,
      barEarlyScore y cover S N idx ori early score s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ MonRun y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ :=
      barEarlyScore_sound (hc s hs i hi) hcover hearly hscore hr hh
    exact ih q hq (by omega) j hj h

theorem noRun_from_barEarlyScore {y cover S N idx ori early score cap i xs}
    (hcover : ∀ {u ys}, MonRun y u ys → cover ys = true)
    (hearly : ∀ {u ys}, MonRun y u ys → early u ys = false)
    (hscore : ∀ {u ys}, MonRun y u ys → score u ys = false)
    (preserved : ∀ {u ys}, MonRun y u ys → MonRun y u (ori ys))
    (checked : ∀ s ≤ cap, ∀ j < N s,
      barEarlyScore y cover S N idx ori early score s j = true)
    (hi : i < N cap) (hne : xs ≠ []) (hinit : xs.Perm (S cap i)) :
    ∀ s ≤ cap, ¬ MonRun y s xs := by
  intro s hs hrun
  cases xs with
  | nil => exact hne rfl
  | cons a r =>
    exact barEarlyScore_all hcover hearly hscore preserved checked cap (Nat.le_refl _) i hi
      (Run.perm hinit (extend_run hrun hs))

theorem score_no_of_fastScr_eq {y bw : Nat} {score : Nat → List Nat → Bool}
    {coords pool : List Nat}
    (heq : ∀ s ws, score s ws = fastScr y s coords bw pool ws)
    {u ys} (h : MonRun y u ys) : score u ys = false := by
  rw [heq u ys]
  exact fastScr_no coords bw pool h

def literalRoutesGood (y : Nat) (routes : List (List (Nat × Nat))) : Bool :=
  routes.all fun r => validStages r && (routeStages r y == y)

def literalRouteOrient (routes : List (List (Nat × Nat))) : List Nat → List Nat :=
  orbitActions qPrefer (routes.map routeStages)

theorem literalRouteOrient_run {y s : Nat} {ws : List Nat}
    (h : MonRun y s ws) (routes : List (List (Nat × Nat)))
    (hg : literalRoutesGood y routes = true) :
    MonRun y s (literalRouteOrient routes ws) := by
  unfold literalRouteOrient
  unfold literalRoutesGood at hg
  apply orbitActions_run h qPrefer
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨r,hr,rfl⟩
  have hrgood := (List.all_eq_true.1 hg) r hr
  simp only [Bool.and_eq_true,beq_iff_eq] at hrgood
  exact routeStages_run hz r hrgood.1 hrgood.2

def qGrayGood (y : Nat) (routes : List (List (Nat × Nat))) : Bool :=
  routes.all fun ps => validStages ps && (routeStages ps y == y)

theorem qInsert_perm (a : Nat) (xs : List Nat) : (a :: xs).Perm (qInsert a xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons b xs ih =>
    simp only [qInsert]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.swap _ _ _).trans (List.Perm.cons b ih)

theorem qNorm_perm (xs : List Nat) : xs.Perm (qNorm xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons a xs ih =>
    exact (List.Perm.cons a ih).trans (qInsert_perm a (qNorm xs))

def orbitNormWalk (actions : List (Nat → Nat)) (current best : List Nat) : List Nat :=
  match actions with
  | [] => best
  | action :: rest =>
    let candidate := current.map action
    let normalized := qNorm candidate
    orbitNormWalk rest candidate (if qLex normalized best then normalized else best)

theorem orbitNormWalk_run {y : Nat} (actions : List (Nat → Nat))
    (preserved : ∀ action ∈ actions, ∀ {u zs},
      MonRun y u zs → MonRun y u (zs.map action)) :
    ∀ {s current best}, MonRun y s current → MonRun y s best →
      MonRun y s (orbitNormWalk actions current best) := by
  induction actions with
  | nil =>
    intro s current best hcurrent hbest
    exact hbest
  | cons action rest ih =>
    intro s current best hcurrent hbest
    have hnext := preserved action (by simp) hcurrent
    have hnorm := Run.perm (qNorm_perm (current.map action)) hnext
    have htail := ih (fun p hp => preserved p (by simp [hp]))
    change MonRun y s (orbitNormWalk rest (current.map action)
      (if qLex (qNorm (current.map action)) best then qNorm (current.map action) else best))
    split
    · exact htail hnext hnorm
    · exact htail hnext hbest

def qGrayNormOrbit (routes : List (List (Nat × Nat))) (ws : List Nat) : List Nat :=
  orbitNormWalk (routes.map routeStages) ws (qNorm ws)

theorem qGrayNormOrbit_run {y s : Nat} {ws : List Nat}
    {routes : List (List (Nat × Nat))}
    (h : MonRun y s ws) (hgood : qGrayGood y routes = true) :
    MonRun y s (qGrayNormOrbit routes ws) := by
  apply orbitNormWalk_run (routes.map routeStages) ?_ h (Run.perm (qNorm_perm ws) h)
  intro action ha u zs hz
  rcases List.mem_map.1 ha with ⟨ps,hps,rfl⟩
  have hp := List.all_eq_true.1 hgood ps hps
  have hv := (Bool.and_eq_true.1 hp).1
  have hy : routeStages ps y = y := by
    simpa only [beq_iff_eq] using (Bool.and_eq_true.1 hp).2
  exact routeStages_run hz ps hv hy

def C26_initial : List Nat := [0x7e01, 0x82aa, 0x8554, 0x10866, 0x11198, 0x2201e, 0x241e0]

def C26_values : Nat := 0xffbffebfef2fbbc9e6f0783affeeb5fbaafee2bbb7fe1dfe677e01de7fb7998dce6371fedc7e371e0dc66369fed678353e0d47e351e0d46635000d2f9b49e6d278341e0ce67b381ecc67b3198cc07b287eca07b2800c807b2000c46631000c219b0800c061b0078c0002fff5bff86ff5fbfaaefe01b9ffae5feb9552e3feb8faae2beb8aaae1feb8782c9e0b1ffac7f4b1f82c5f4b1782c3eab0f82c2aab0782c000a9ffaa55ea9552a41ea8afaa21ea807a8554a0aaa80009fffe7fe19f87e7e019c7826be09a78267e09978263fe98f82621e9880261fe98782607e9819a601e9800259e094f8251e093f824de092f8249e091f8245e090f8242009079a41e29050240008c07a2a1e8a07a261e8907a221e7fffdff777fbbdfe677f805aaee67ff99dfe66ff997fe6577195986555193ba64e61919863ff98f7663bb98d7662ff98afe62bb98a666219987fe6155182ee60ab982aa6033180005fe657e675f80571985a19939984ce6131984a1991b98467f9199846199179845661139844679119a440010e66431990a664211108004080100003fffcff553fafcfeaf3faacfe0b3f804aaaa275509aaa255508ffe23d508eaa235508aee22ab88aaa22910880021ff8875421af886aa21800855e21558840020ff882fe20af882ae208a8820a208088200202a88036200a8800a200188002200007e1f1f83c7e071f80c2a00040000e00028380a0002000061e01800040000aa8022a00850020a0081802020080001fe006000088001f80078000d8001e00060000e000280006000080000

def C26_patterns : Nat := 0x16555665595564558155a5565558555d5569559556155755595555551552554555055255455511542550551554515115155451505515545450554150559155855515505511514541115445405601550550055

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

def C26_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x1000b000000
  | 6 => 0x904e02f003000
  | 7 => 0xa0810ab017001
  | 8 => 0x430e006a003
  | 9 => 0x61035008
  | 10 => 0x6003
  | 11 => 1
  | _ => 0

def C26_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x501281000000
  | 6 => 0x401601501219000
  | 7 => 0x40160159a499119
  | 8 => 0x50171a69a31a
  | 9 => 0x59959a31a
  | 10 => 0x21931a
  | 11 => 281
  | _ => 0

def C26_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0, 0x0]
  | 5 => [0x0, 0x0, 0x6069, 0x190078219a, 0x0]
  | 6 => [0x0, 0x5, 0x47d9d16869010240bc070062f0641d, 0x6983406902d6cd00104c04d04902702882f00e01507b00d00700b010004, 0x40253]
  | 7 => [0x2, 0x11cea0601c0802, 0x140bcab01e1008f0072eca38098a727416c3c00206600c128f42880040b82400202c190140bb0b8020480060400e0130020040203e1f011003025, 0x87e00100936a1a700200e00969406f0b20b500100201a10c01202c04a0030040080e600f04388113601512b0f18810310c8, 0x561305]
  | 8 => [0x12, 0x1e4006399670805207e00800c80041ac1288350190098001003015c09204f80880d4020001004005811400d, 0x1e14002009009f031403350020a91280002005822103400c208f8042007011d1f40002000800200940090004001010000b0ea800300180058128016003403c0004056001804c013c0030bf8008013e03c000400d00040070038026000400f0084002, 0x280181b299a6028032719816801004668643413c1a, 0x0]
  | 9 => [0x396, 0x5c250020100341e03a0660922e38800402826, 0x60080480295d0240a595abb01a02226001002104040a6886008008654201c40b81d, 0x0, 0x0]
  | 10 => [0x12, 0x11, 0x0, 0x0, 0x0]
  | 11 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C26_records : Nat → List (List Nat)
  | 4 => [[], [], [0xf57a06], [], []]
  | 5 => [[], [], [0x3b95639e6ab1cf5788e74b703bc5aa1ddcd60ef469077536c3bb1c21de4ab1cec6e07], [0x773295629d0ab2f0665aac5261c6da2203749907c89d0b6558a7aa84b819dcb1558a76384c819c66422226c2acc419eaea6e8676368c81998ab111874b70c819d2de1f03], []]
  | 6 => [[], [0x9c0944139c5], [0x3a5bc3d7c2972ff559e530a5cbc5a43d282272c7559e632acf2ad3a79262972ab4f9e7faacfa9c44e5b09c1ecc559e600a5cb5d423d56a13cab511e55a94f3bcc8b98aab3cc011397619173acc8b9569e3c9c2f8f772707a5052e592ab3cab519e772ac7aacc339569c3cab2fce4e18c7ba9b23d56609ce9322e5598d73d5d4b9302272df4e0f772ac73a5b43d2e2972cd509e], [0x5faac52e1e0df558e75375a41d56a1318e5f2d41c65d2de38074991852e1748911193e93c4585d4e56e07753695639745911294a11844e1d2de3d0b71b68b41dd4df558e6c2ad4239d4e0558e743755639b0ab4e8e40134458556a12d8e72370b81d265814a95e2205265dcab508e782acbe39c6da3f075e16052a5b0ab4e0e4a9907cc9c8e06e074a16444a5d2de320e5f1181ce18046113875369ac1dd4ab2f8e74b78b41dc8e26e0771b68b81d74460b384a2244465d0ab4e8e6faad42397c4614b878aaccc3956a12f8e5eaacbe39dcab4e0e76b615639caab2f8e69284b81d7c7b232a7b3c55639cae0698749a1c44657c77232a71b687c4de2d8558e5d2c82c6584ab113865aac4469328c320e71a30c83956a12b8e75381ac1dd2da320e55a84ee39d0b4558e4995c44a5b0c9558e55a845271dad86b0755a80be38f84f14e149a205265c6641f32], [0x38db47c398375395b4640cea702c55629c6da361701ba9cada36036c2c556a114ab508e04461c6da3217032fd68ab1118]]
  | 7 => [[0x20], [0xb929225290a5014fc292450a5d5e1496295250a9d5d14c3298852702413e942856ea60a4e14a7288cf8b1d], [0x55a8495617ce1b8a574b88871c0a575015c55e11894988873f8a57198a57290a575d274255a4895011895e0a484a97c572b60543894f5d21c255a4092b895255a841208897500a484ea70255a70957a8421f88974d15c51106d75627025698c54a95c54aa1c27195454617ce56a742278a5455a749491189498a46360a575418453206551b08971485974a96c51a03977535055daac923039c5e1e0555a809612ac9753485200a57470ac82305995d0a48718a485221c256184e7d88973688971c08974b22c255a4494a08867191897216c550a702320a5c55a7425d11894995c53b08975597ce438acf74b8057195c549a1c27499855917ce71a1c274b78556180e4a8a482e139164aac14c96c55d2ac91b89572a06513a08974d96c54921c272b7c55eaac9188397719dc55016c564aac91a8a5755a8425f8ad74a08871a089755a8437195854915c555a7025f088756a8c21105d7400897190a576d17ce230adc490a484909485d15c57f2aca1b8ad7598acf590acf2988971f0a577d0a5711059764aac25d1dc574b780498a4855a3c95d16c57197c51a8897320ed5280a5423045c230a5c55a7017499045d2c827f2ac94a22425597cd4b1745188a573b0a574a91894c97c55e2cc218845771b60571ac82498a475d17c54c95c55021c25308877196c57499055517c51a05973a8a5755a7411a0a574a1645502742398a57], [0x156a1019e230e007e1d4e0558f75381ac3dcadd6c0f5ba4844e556a11c1e6c2ad423d56a1381f5d0d444e55aac2fce5d2c8ee3d56a1381e490dc52e5262207395e1e052b556a1111e4a0882ce5c6da2e0f74994c8b97eab113a5e11852f1328c330f60af052e52646113a5fab452e5c6642e2e55a853878c85c03e64915c6ead7477232e3991853e192b4559e612e844e52438113956280be3d5aac4e9e5faf052e5c63811396c359423d2a8a2d8f71b68b81d56a1071e5faf44ae57eb4559e719e4d8add26632ae5d1181cf158ab4e9e55a8402797ebd14b972ad1567d744614bc399181de0c83811785d2c88c797458112b5faf444e49e381171562ad4279d4e56d0f572ad427924872b8f582ad4279d4e06b07752b4c8b97476113955a85427974b811395f0c41ce556a1241e3f934458d2446073c5fa4844e48c34117849a20446c8c380b7871b80c8b97c46113a4992c52e5eeea322e71b81b43d2a381139230dc1de192ad561e3b11845e174220b395ead1567978b3149d490c41ce48c3114f85e0e052e57488111b230882de1829211395fac044e5d4e0558e230d445e12838113975394c8b88c3107785e0dc52e48c3714f872ad1567978b714b95a2ad42788c3811785e1cc52e52658112b64aad4279c6e0560f74b78ca3d263511396c2ad42392a651f33672ad4279c679322e5d2c81c755aac509e230e01de1d4e3322e3e13c458dc6da3c8f5d0e044e540381139230e053e156ab509e499c044e584ad1139], [0xb84d1c08b0afd7a46113875395c0dd0ebf5e9dc44a574771c0894ba9c0ad560e5d1187022707c3813445857ebd59088cae964381119]]
  | 8 => [[0x20921], [0x1c6605e04240467c56e8be052144980910402043403980d8d89a018404181f1003e001c076812660a6735c02d8015008e03a402b808d1ae8a02c00e801100da04a1407803f00ea050180980270248c174083808f0042037c0258035008207dc0a0283d0086049141280db007604b14ba30c919ca0501614812a61a201f3667808d008a014ba3d80050116012406981f3089e0254028806b02f0a7cc07080370248b1bb629797459c6021c019805358fe008c081805300e201e404c8003005a006c08080d500ee0], [0x3f889a5900d023039d560add718e0a5e0a48428a5d4b1c0a4b064a5eae8a148a5d1883971105971a839d328ed61f039a49088a7d089a5d1c0a52a48a32919f230a5d491c0a56a74a29089a4e80d05d2d0a14889d50088a4a920a11065d2886561b859a258add5eaaca38095d56248a1d839d5d120a490e0a41919f5d284a3b0897719a4a71888a1c095d55a84268af4a72a48a2e0a5d56a48a6e8a5d71920a5ea48a2780d66e919f2b945349838a32089f64ab4a1c0a5a18839d49120a5fac0a258a5d1c089a320e1f380a5d11059a5ba48a678add12839d50038a23039c5a290a24045d59095019089a5d2e8a5d2b4a3200df11045d230e1f5f895a4900ca7f2b4a43845038119f36089a5a248a34839d1480dd5fa48a18839a1c08974500d04915c52a00d35d118a378a5d2300df230a5c24119f5d088a75240a1b8a5a501c0a55a8411b80da4a0e0a4a058a6e91a039889a1c08aa1c0a57328a5d62ae8a5d0e0a1f089a260a5d73248a500e0a612b4a5faf4a49038a5d2c8a7eae8a2d8ed31b8a5d50004a23039f32865672ae8a5e895d499c0a64280a72b60556a3ca5617ce4a8e0a682e8a14805d25859a56a84a55a8496d00d04c80ca49248a398a5d11039d32039f4a888a50a80a3307df7180ca5a280a240a5d56a74227839656280a23089f5000ca56a40a5fa3ca3600da1b839a5d118971ad0a5c095d398a5723119f46844a5a095d50120a5d038a55a84a36039a5ea80a19889a498d4a5eaac94600d04a8eca24039d398a5a1c08983b089a49004a14839d4921c250280a1c0a5d5d004a5d1dc55f120a56a80a5d2c825e0a4a5b8add1b8a5737119f4380d0230a5f5eab4a71838a1b889a4a96c55d2b0a4a80ca1f00da1a889749888750a48a4a838a49920a25921f5d00ca23005f2e86531a889a60a48a2100da2788966ea48a], [0xe646117a3e1c045e55aac50be2e0e045e4963814f91c08807e574b2111f3b1c045e5743811395d0e044ecec381179258dc53e5d4ad332f2591853f070220b79490dc1cece6701179110541de56e70117956ab1427ce64b14f9259201df0964814fc5d11844f89031077975394ccbc70220779230e045e17ead113b4915c1cbd2448073d5faf444ec702203f9398881de4b84d01e7240dc1de5d4e5702f490881cf5ba381179370e045e5784b14bd5d1cc44ecb84d07674921c1c7c8c22077c5faf444e4e03811791b8a41de57477112f240e045e55aac509e230e045e8702200f91c0e045e4f84d116b2e134459c6e220779230a445f17aad563e1c08845e48c3811795d0881cf4ca3811795fae844ed6eb412dd260e045e574b7113b], []]
  | 9 => [[0x9ad8298658a4], [0xe0114829800720e200cc001807108b6017400ea00770460114076804560d600fc092288cf80ec24405c90e10be6025c84680cb21c2050140580e12096011424c801d09ce45d1448841d00e2407580e91bb200e11dc0489109005a034c007800500a5d], [0x1c03a00a83a023089f3300e03280e049038a0180a06e8e203288a00600e0240e201c01e02b00e00300e00200e01680e03800e02612200e00e0380e201b83a00700603e1c202e03a0260e206e80e01c089a2683a02400e06e88a03801600c03a024122024039d2688a02680e038066011039d5b9c202592201c05a05a1c200580e01100e0258a606e922056a84a1108a01100600180e02883a05faf4a3808a00700e03b1c207c9c205d088a2583a03c80e07000e01b839a2e0e2032922038122039922039889a421c201c00e03b0e203283a00180602403a06e83a05eab4a328e2025921f1c08a0421220399c202308a07500e01103a01c08970703a0258a5d2e00e00f80e05604605b89603803a01c0e202408a02e08a03983a00c00e03708a0381c20], [], []]
  | 10 => [[0x20921], [0xe1008a024400e8071000e0], [], [], []]
  | 11 => [[0x20], [], [], [], []]
  | _ => []

def C26_S (s j : Nat) : List Nat :=
  qGroupedState C26_initial 5 18 9 C26_patterns C26_values (C26_counts s) (C26_specs s) (C26_records s) j

def C26_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C26_initial (C26_counts s) (C26_specs s) (C26_seeds s) ws

def C26_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x100,4),(0x10,8),(0x10e,4),(0x2000,2),(0x4000,1)],[(0x1000,1),(0x2010,2),(0x100,4),(0x10,8),(0x904,4),(0x2032,2),(0x1000,1)],[(0x1000,1),(0x2100,2),(0x4,8),(0x80a,4),(0x3132,2),(0x1000,1)],[(0x2020,2),(0x808,4),(0x3030,2),(0x10000,1)],[(0x5000,1),(0x20,2),(0x100,4),(0x10,8),(0x90c,4),(0x2012,2),(0x14000,1)],[(0x4000,1),(0x2030,2),(0x100,4),(0x10,8),(0x906,4),(0x2,2),(0x15000,1)],[(0x4000,1),(0x120,2),(0x4,8),(0x802,4),(0x120,2),(0x15000,1)],[(0x444,1),(0x10,2),(0x100,4),(0x10,8),(0x104,4),(0x232,2),(0x444,1)],[(0x4444,1),(0x100,2),(0x4,8),(0xa,4),(0x2332,2),(0x4444,1)],[(0x410,1),(0x1000,2),(0x100,4),(0x10,8),(0x502,4),(0x1200,2),(0x454,1)],[(0x1100,1),(0x2000,2),(0x2,8),(0x80c,4),(0x3100,2),(0x1154,1)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0xa04,4),(0x1302,2),(0x10114,1)],[(0x454,1),(0x1130,2),(0x4,8),(0x106,4),(0x310,2),(0x11410,1)],[(0x1410,1),(0x110,2),(0x400,4),(0x40,8),(0x506,4),(0x1330,2),(0x10454,1)],[(0x4100,1),(0x10,2),(0x2,8),(0x80c,4),(0x120,2),(0x15154,1)],[(0x10000,1),(0x21000,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80400,4),(0x21200,2),(0x10044,1)],[(0x4000,1),(0x1000,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0x50e,4),(0x3200,2),(0x4044,1)],[(0x11400,1),(0x2010,2),(0x20100,4),(0x200000,8),(0x2000,16),(0x200010,8),(0x20904,4),(0x2232,2),(0x11044,1)],[(0x11400,1),(0x2100,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200004,8),(0x2080a,4),(0x3332,2),(0x11044,1)],[(0x2020,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200000,8),(0x20c08,4),(0x3230,2),(0x10044,1)],[(0x15000,1),(0x1020,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xd0c,4),(0x3212,2),(0x4044,1)],[(0x400,1),(0x2030,2),(0x20100,4),(0x200000,8),(0x2000,16),(0x200010,8),(0x20d06,4),(0x2202,2),(0x11044,1)],[(0x15000,1),(0x10120,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40902,4),(0x10320,2),(0x4044,1)],[(0x11044,1),(0x20010,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x80304,4),(0x20232,2),(0x11400,1)],[(0x11044,1),(0x20100,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800004,8),(0x8020a,4),(0x21332,2),(0x11400,1)],[(0x11010,1),(0x20000,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x80302,4),(0x20000,2),(0x11410,1)],[(0x4100,1),(0x10000,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400002,8),(0x4010c,4),(0x12000,2),(0x4510,1)],[(0x15104,1),(0x12200,2),(0x40800,4),(0x400000,8),(0x4000,16),(0x400080,8),(0x40b04,4),(0x10202,2),(0x4550,1)],[(0x15454,1),(0x12130,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40306,4),(0x10110,2),(0x5054,1)],[(0x14010,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xe06,4),(0x10130,2),(0x5410,1)],[(0x1500,1),(0x20010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800002,8),(0x8050c,4),(0x20120,2),(0x10110,1)],[(0x10010,1),(0x21010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80604,4),(0x20230,2),(0x54,1)],[(0x11044,1),(0x20020,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x8070c,4),(0x20212,2),(0x400,1)],[(0x4540,1),(0x10200,2),(0x40800,4),(0x400000,8),(0x4000,16),(0x400080,8),(0x40b04,4),(0x12202,2),(0x15114,1)],[(0x11010,1),(0x21130,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800004,8),(0x80306,4),(0x21110,2),(0x410,1)],[(0x10,1),(0x20010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80604,4),(0x20030,2),(0x10,1)],[(0x14444,1),(0x10020,2),(0x40100,4),(0x400000,8),(0x4000,16),(0x400010,8),(0x40b0c,4),(0x10212,2),(0x14444,1)],[(0x1140,1),(0x20200,2),(0x800,4),(0x80000,8),(0x800,16),(0x80080,8),(0xf04,4),(0x20202,2),(0x1150,1)],[(0x14410,1),(0x10130,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40b06,4),(0x10310,2),(0x14454,1)],[(0x4044,1),(0x1030,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0x706,4),(0x3202,2),(0x15000,1)],[(0x11540,1),(0x21220,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800008,8),(0x80302,4),(0x21320,2),(0x504,1)],[(0x5054,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0x706,4),(0x12130,2),(0x15454,1)],[(0x10110,1),(0x20020,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800002,8),(0x8050c,4),(0x21010,2),(0x1500,1)],[(0x14444,1),(0x10030,2),(0x40100,4),(0x400000,8),(0x4000,16),(0x400010,8),(0x40b06,4),(0x12002,2),(0x14444,1)],[(0x1140,1),(0x20220,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800008,8),(0x80502,4),(0x21320,2),(0x1140,1)],[(0x14054,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xf06,4),(0x12130,2),(0x15410,1)],[(0x110,1),(0x2020,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200002,8),(0x20d0c,4),(0x3110,2),(0x1544,1)]]

def C26_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def C26_rankPool : List Nat := [272644529, 100712812, 201506090, 170930544, 167855438, 100910477, 236988719, 67256747, 235158857, 234997134, 134299980, 33735981, 268648812, 168018219, 268680586, 167822638, 67323341, 134331818, 235061548, 201605451, 134300012, 268584270, 67157354, 33635657, 201409966, 167984585, 100941257, 33669419, 134497741, 134267308, 100810153, 234964334, 100844909, 33800651, 100810121, 201475470, 67157418, 201409902, 268517804]

def C26_grayRoute8 : List (Nat × Nat) := [(0x2aa,1)]
def C26_grayRoute2 : List (Nat × Nat) := [(0x800,1),(0x66,2)]
def C26_grayRoute1 : List (Nat × Nat) := [(0x2000,1),(0x1e,4)]
def C26_grayRoute16 : List (Nat × Nat) := [(0x8044,1),(0x600,2)]
def C26_grayRoute4 : List (Nat × Nat) := [(0x10000,1),(0x1818,2)]
def C26_grayWalk : List (List (Nat × Nat)) :=
  [C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute4,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute4,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8]
theorem C26_grayGood : qGrayGood (compactGoal 9 9) C26_grayWalk = true := by decide +kernel
def C26_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17] => (sum6 r17 r13 r14 r0 r4 r8 < 3) || ((sum6 r12 r11 r16 r1 r0 r3 < 3) || ((sum6 r10 r9 r15 r5 r0 r6 < 3) || ((sum6 r16 r11 r12 r0 r3 r5 < 3) || ((sum6 r14 r10 r17 r2 r0 r5 < 3) || ((sum6 r13 r12 r17 r7 r0 r3 < 3) || ((sum6 r15 r9 r10 r0 r2 r7 < 3) || ((sum6 r11 r13 r16 r4 r0 r2 < 3) || ((sum6 r9 r10 r15 r8 r0 r7 < 3) || ((sum6 r14 r12 r17 r3 r0 r7 < 3) || ((sum6 r12 r10 r16 r2 r0 r4 < 3) || ((sum6 r13 r9 r17 r5 r0 r1 < 3) || ((sum6 r12 r11 r16 r6 r0 r8 < 3) || ((sum6 r11 r9 r16 r7 r0 r5 < 3) || ((sum6 r10 r12 r15 r7 r0 r8 < 3) || ((sum6 r14 r9 r17 r1 r0 r5 < 3) || ((sum6 r13 r14 r17 r6 r0 r2 < 3) || ((sum6 r10 r13 r15 r3 r0 r4 < 3) || ((sum6 r12 r9 r16 r5 r0 r7 < 3) || ((sum6 r11 r10 r16 r8 r0 r6 < 3) || ((sum6 r12 r11 r16 r2 r0 r4 < 3) || ((sum6 r14 r10 r17 r4 r0 r8 < 3) || ((sum6 r10 r11 r15 r1 r0 r2 < 3) || ((sum6 r9 r10 r15 r2 r0 r1 < 3) || ((sum6 r14 r13 r17 r2 r0 r6 < 3) || ((sum6 r9 r14 r15 r6 r0 r5 < 3) || ((sum6 r9 r14 r15 r8 r0 r3 < 3) || ((sum6 r11 r9 r16 r3 r0 r1 < 3) || ((sum6 r13 r14 r17 r8 r0 r4 < 3) || ((sum6 r12 r13 r16 r1 r0 r4 < 3) || ((sum6 r9 r13 r15 r4 r0 r3 < 3) || ((sum6 r14 r11 r17 r2 r0 r7 < 3) || ((sum6 r13 r11 r17 r5 r0 r3 < 3) || ((sum6 r11 r14 r16 r7 r0 r1 < 3) || ((sum6 r9 r12 r15 r4 r0 r3 < 3) || ((sum6 r14 r12 r17 r4 r0 r6 < 3) || ((sum6 r10 r13 r15 r1 r0 r2 < 3) || ((sum6 r14 r11 r17 r2 r0 r6 < 3) || ((sum6 r12 r13 r16 r2 r0 r8 < 3) || (false)))))))))))))))))))))))))))))))))))))))
  | masks => C26_rankPool.any (fastEntry (compactGoal 9 9) 5 C26_coords masks)
theorem C26_patternScore_eq (masks : List Nat) :
    C26_patternScore masks = C26_rankPool.any (fastEntry (compactGoal 9 9) 5 C26_coords masks) := by
  unfold C26_patternScore
  split <;> rfl
def C26_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C26_patternScore (C26_coords.map fun j => row ws (fun w => w.testBit j))
  else false
theorem C26_patternScr_eq (s : Nat) (ws : List Nat) :
    C26_patternScr s ws = fastScr (compactGoal 9 9) s C26_coords 5 C26_rankPool ws := by
  unfold C26_patternScr fastScr
  split
  · rw [C26_patternScore_eq]
  · rfl
def C26_rows : List Nat := [1, 42, 44, 50, 52, 74, 76, 82, 84, 3, 5, 9, 17, 33, 65, 6, 24, 96]
def C26_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C26_rows)
def C26_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
theorem C26_nonconstant : ∃ x y : Fin 7 → Bool, C26_f x ≠ C26_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_enc_goal : encL C26_f C26_rows = compactGoal 9 9 := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_proper : ∀ zs ∈ C26_xs.sublists, zs ≠ C26_xs → compactCover 9 9 zs = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_initial_perm : C26_xs.Perm (C26_S 11 0) := by decide +kernel
def C26_ori : List Nat → List Nat := qGrayNormOrbit C26_grayWalk
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_good : literalRoutesGood (compactGoal 9 9) C26_literalRoutes = true := by decide +kernel
theorem C26_ori_run {s ws} (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_ori ws) := qGrayNormOrbit_run h C26_grayGood
def C26_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 9) (compactCover 9 9) C26_S C26_N C26_idx C26_ori
    C26_patternScr C26_patternScr s
def C26_F : Nat → Bool := certAt C26_Z C26_N 12
theorem C26_decoder_diagnostic : qNorm (C26_S 10 0) = [0x7e01, 0x7e01, 0x82aa, 0x8554, 0x10866, 0x11198, 0x2201e, 0x241e0] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_gray_one_state : span (C26_Z 8) 1 0 = true := by decide +kernel

end PEqualNP.Outside.L_meta_984.Cert
