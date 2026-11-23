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

def C0_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x600d001000
  | 6 => 0x501f011001
  | 7 => 0x14030003
  | 8 => 0xa003
  | 9 => 1
  | _ => 0

def C0_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x481301101000
  | 6 => 0x20180150110d
  | 7 => 0x60d58d18e
  | 8 => 0x28d18e
  | 9 => 269
  | _ => 0

def C0_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x44234d, 0x1ea09]
  | 6 => [0x2, 0x14f0185801802, 0x55c80007000501cf0004000200050026, 0x14]
  | 7 => [0x1, 0x44e0593d00984b08c0c01217009800803, 0x18130af7e7001, 0x0]
  | 8 => [0x1, 0xe03, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C0_records : Nat → List (List Nat)
  | 4 => [[], [0x1387], [0xa93c6], []]
  | 5 => [[], [0x128f], [0x9f2c7243f8a74079e966363b890b939f3479f28790f0b9f0d6524b150571ab3c7], [0x27c4723455eb518ae8f131559e467cd6a1cf9acc6]]
  | 6 => [[0x5], [0x9f78af96f47fd31f2feabde0bf3f72beacde03efdf84fa9de33f49f], [0x3c579443bc3a5794e7735e579242f99f3479ed7356876624b99eda77e9d78abdb421fc8aad7a72cf9f357361f958575504b37edcf9f34f8281b384b93c4b9508f382e0f9f1177e75b8c55d8ae8f], [0x2f5a4b18a789333e6b21e9d19a3ab3c4b1]]
  | 7 => [[0x1ee], [0xb6282b0255747505485635f5274fd4341d235855655535435175f89e56d3d4cd494ad4e52d775a5981357b40d8206d1144d154a50f49531515194e5], [0x82304f6469cd126384e1c9e248f1274e205aa8a20f15922743b5eb4a32b179274e897e1c4524090791e20], []]
  | 8 => [[0x1ee], [0x3d555194150f495454255b5dd], [], []]
  | 9 => [[0x5], [], [], []]
  | _ => []

def C0_S (s j : Nat) : List Nat :=
  qGroupedState C0_initial 4 15 7 C0_patterns C0_values (C0_counts s) (C0_specs s) (C0_records s) j

def C0_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C0_initial (C0_counts s) (C0_specs s) (C0_seeds s) ws

def C0_literalRoutes : List (List (Nat × Nat)) := [[(0x20,2),(0xc,4),(0x10,2),(0x1054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x40,1),(0x20,2),(0xc,4),(0x10,2),(0x1115,1)],[(0x4000,1),(0xb02,4),(0x11,2),(0x4000,1)],[(0x4054,1),(0x30,2),(0xb06,4),(0x13,2),(0x4100,1)],[(0x4000,1),(0x20,2),(0xb09,4),(0x3,2),(0x5054,1)],[(0x4054,1),(0xb05,4),(0x2,2),(0x5154,1)]]

def C0_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C0_rankPool : List Nat := [4401547, 7609806, 5275034, 6626216, 7425741, 3174108, 7670697, 5520265, 2112650, 6454168, 2182298, 6303405, 5340570, 7559563, 6650776, 5270922]

def C0_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r11 r8 r9 r2 r3 r4 < 3) || ((sum6 r14 r12 r13 r1 r4 r7 < 3) || ((sum6 r10 r9 r13 r7 r0 r5 < 3) || ((sum6 r8 r10 r11 r1 r5 r6 < 3) || ((sum6 r13 r12 r14 r4 r1 r7 < 3) || ((sum6 r12 r13 r14 r6 r0 r3 < 3) || ((sum6 r9 r10 r11 r0 r5 r7 < 3) || ((sum6 r9 r8 r11 r3 r4 r5 < 3) || ((sum6 r10 r8 r12 r3 r0 r2 < 3) || ((sum6 r8 r9 r11 r7 r2 r6 < 3) || ((sum6 r10 r9 r12 r4 r1 r2 < 3) || ((sum6 r13 r10 r14 r2 r0 r6 < 3) || ((sum6 r10 r9 r13 r7 r1 r5 < 3) || ((sum6 r11 r8 r9 r5 r3 r7 < 3) || ((sum6 r8 r9 r11 r7 r5 r6 < 3) || ((sum6 r10 r8 r13 r6 r0 r5 < 3) || (false))))))))))))))))
  | masks => C0_rankPool.any (fastEntry (compactGoal 8 7) 4 C0_coords masks)
def C0_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C0_patternScore (C0_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C0_rows : List Nat := [10, 12, 17, 18, 20, 33, 34, 36, 3, 5, 9, 6, 24, 40, 48]
def C0_xs : List Nat :=
  (List.ofFn fun (i : Fin 6) => (fun x : Fin 6 → Bool => x i)).map
    (fun a => encL a C0_rows)
def C0_f (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def C0_ori : List Nat → List Nat := literalRouteOrient C0_literalRoutes
def C0_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 7) (compactCover 8 7) C0_S C0_N C0_idx C0_ori
    C0_patternScr C0_patternScr s
def C0_F : Nat → Bool := certAt C0_Z C0_N 10
def C1_initial : List Nat := [0x3c21, 0x454a, 0x4a94, 0x90c6, 0xa318, 0x1001f, 0x103e0]

def C1_values : Nat := 0x1a318d0006431b00014a94a2afd152a87c140009e1fcf0860fc1040081ffc001a00030000718c357397842b3de598c29c60fad67c2127ef110008000040000210001800020000

def C1_patterns : Nat := 0x655555955595555551551515515515541590558155

def C1_N : Nat → Nat
  | 5 => 8
  | 6 => 22
  | 7 => 36
  | 8 => 18
  | 9 => 1
  | _ => 0

def C1_counts : Nat → Nat
  | 5 => 0x4003001000
  | 6 => 0x400f003000
  | 7 => 0x1400f001
  | 8 => 0xe004
  | 9 => 1
  | _ => 0

def C1_specs : Nat → Nat
  | 5 => 0x201181101000
  | 6 => 0x201501191000
  | 7 => 0x401412111
  | 8 => 0x591212
  | 9 => 273
  | _ => 0

def C1_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x2, 0x7]
  | 6 => [0x0, 0x3, 0x6440303002, 0x3]
  | 7 => [0x2, 0x4014201, 0x3c0601662d, 0x0]
  | 8 => [0x4, 0x1080400827, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C1_records : Nat → List (List Nat)
  | 5 => [[], [0x100f], [0x10ae39e343c2f87], [0x44e34342eae2a17d70d0bee83]]
  | 6 => [[], [0x15064110], [0x10ae3e15c742f874493d0a23d744f2239d44c1f0be3e17d39c6e68575c8a03db5cf2258f], [0x85744742ea22d1206330be887]]
  | 7 => [[0x8], [0x1122d577444c54d215490764416325d1368d05], [0x6113f0a23d444fa209f4513e8887d114fae8be6d13e40de5128fa241f5d13c89e7d118fb889f8515eba27d10cfa211f], []]
  | 8 => [[0x9ba8], [0x3e06844058460882a1880e148121c844c28], [], []]
  | 9 => [[0x8], [], [], []]
  | _ => []

def C1_S (s j : Nat) : List Nat :=
  qGroupedState C1_initial 4 17 6 C1_patterns C1_values (C1_counts s) (C1_specs s) (C1_records s) j

def C1_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C1_initial (C1_counts s) (C1_specs s) (C1_seeds s) ws

def C1_literalRoutes : List (List (Nat × Nat)) := [[(0x200,2),(0x100,4),(0x18,8),(0x10f,4),(0x221,2),(0x155,1)],[(0x210,2),(0x900,4),(0x90,8),(0x904,4),(0x212,2),(0x1000,1)],[(0x130,2),(0x6,8),(0x9,4),(0x103,2),(0x1155,1)],[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x544,1)],[(0x140,1),(0x200,2),(0x100,4),(0x18,8),(0x10f,4),(0x221,2),(0x415,1)],[(0x10,1),(0x300,2),(0xc00,4),(0xc0,8),(0xc02,4),(0x300,2),(0x1554,1)],[(0x140,1),(0x130,2),(0x6,8),(0x9,4),(0x103,2),(0x1415,1)],[(0x100,1),(0x1200,2),(0x800,4),(0x80,8),(0xe00,4),(0x1200,2),(0x4104,1)],[(0x4,1),(0x1200,2),(0x100,4),(0x18,8),(0x70f,4),(0x1221,2),(0x4151,1)],[(0x100,1),(0x1210,2),(0x800,4),(0x80,8),(0xe04,4),(0x1212,2),(0x4444,1)],[(0x4,1),(0x1200,2),(0x100,4),(0x18,8),(0x707,4),(0x1220,2),(0x4411,1)],[(0x104,1),(0x3010,2),(0x100,4),(0x10,8),(0xd04,4),(0x3012,2),(0x5040,1)],[(0x144,1),(0x2110,2),(0x6,8),(0x90b,4),(0x2100,2),(0x5151,1)],[(0x110,1),(0x2100,2),(0x400,4),(0x40,8),(0xd02,4),(0x2100,2),(0x5510,1)],[(0x144,1),(0x2130,2),(0x6,8),(0x909,4),(0x2103,2),(0x5411,1)]]

def C1_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C1_rankPool : List Nat := [7708636, 3165914, 6445998, 8417229, 8478159, 2125483, 6651594, 9473755, 6328284, 4227021, 5414844]

def C1_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r12 r13 r15 r9 r5 r7 < 3) || ((sum6 r10 r13 r14 r4 r0 r3 < 3) || ((sum6 r14 r10 r11 r5 r2 r6 < 3) || ((sum6 r13 r12 r15 r6 r0 r8 < 3) || ((sum6 r15 r12 r13 r5 r1 r8 < 3) || ((sum6 r11 r10 r14 r6 r0 r2 < 3) || ((sum6 r10 r12 r14 r7 r5 r6 < 3) || ((sum6 r11 r13 r14 r8 r0 r9 < 3) || ((sum6 r12 r13 r15 r8 r0 r6 < 3) || ((sum6 r13 r12 r15 r7 r0 r4 < 3) || ((sum6 r12 r11 r15 r9 r2 r5 < 3) || (false)))))))))))
  | masks => C1_rankPool.any (fastEntry (compactGoal 10 7) 4 C1_coords masks)
def C1_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C1_patternScore (C1_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C1_rows : List Nat := [33, 42, 44, 50, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 6, 24, 96]
def C1_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C1_rows)
def C1_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C1_ori : List Nat → List Nat := literalRouteOrient C1_literalRoutes
def C1_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 10 7) (compactCover 10 7) C1_S C1_N C1_idx C1_ori
    C1_patternScr C1_patternScr s
def C1_F : Nat → Bool := certAt C1_Z C1_N 10
def C2_initial : List Nat := [0x1e40, 0x2295, 0x252a, 0x41cc, 0x4833, 0x81f0, 0x900f]

def C2_values : Nat := 0xdff0de40d83fd833d80fd800d00fd000c9f3c9f0c833c1fcc1f0c000b52ab29fb295b00fa52aa295a1f09ff09e4f9e40980f920f91f0900089f083f080006ab7652a63dd5fcc5e735e4049ff480041c040844040400c40003ed53e402d2a27bf272a220020000800020001c000840040000c00050003

def C2_patterns : Nat := 0x0

def C2_N : Nat → Nat
  | 4 => 2
  | 5 => 10
  | 6 => 25
  | 7 => 41
  | 8 => 27
  | 9 => 1
  | _ => 0

def C2_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x1007002000
  | 6 => 0x1015003000
  | 7 => 0xd01b001
  | 8 => 0x16005
  | 9 => 1
  | _ => 0

def C2_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x101481181000
  | 6 => 0x101401201000
  | 7 => 0x581501101
  | 8 => 0x501282
  | 9 => 257
  | _ => 0

def C2_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x1, 0x11a02, 0x2]
  | 6 => [0x0, 0x4, 0x2d940d499202, 0x2]
  | 7 => [0x2, 0x1272c1b0455e00445, 0x60a4d000807, 0x0]
  | 8 => [0x161, 0x14084d4016e017, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C2_records : Nat → List (List Nat)
  | 4 => [[], [0x1b07], [0x75c86], []]
  | 5 => [[], [0x3aada17], [0x16c86a456340a87b6b33c483b7c83f3707], [0x1cc8806]]
  | 6 => [[], [0x407e4bd757], [0x76bd638cf30205d0371c6827bd7adcc87b8807ccbd6d6f2f92b1e442b5921ea68b2719e2d80de324e9203d6487e992d4cac7], [0x1cba807]]
  | 7 => [[0x7f], [0x54fd3ef0df5ff15f4eff7df7efbd7d0ef1bf9ef9bee4bea7789f97ed1eedfb4bbc07e0bf25e577cd7f57e77e], [0x388675d0edaa0ddd42bcd2de408ceda1cef42bcc857999ae613e6680ff2867], []]
  | 8 => [[0x155656555595955555], [0x18ff87f0bf93fc5fe87fcff89fc6fe47f33f87fdafeb7f43bf3fdcfecff3ff83fe6be3ff], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C2_S (s j : Nat) : List Nat :=
  qGroupedState C2_initial 4 16 6 C2_patterns C2_values (C2_counts s) (C2_specs s) (C2_records s) j

def C2_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C2_initial (C2_counts s) (C2_specs s) (C2_seeds s) ws

def C2_literalRoutes : List (List (Nat × Nat)) := [[(0x1000,1),(0x2030,2),(0x80c,4),(0x2030,2),(0x5000,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x300,2),(0x115,1)],[(0x1100,1),(0x2030,2),(0x200,4),(0x20,8),(0xa0c,4),(0x2130,2),(0x5115,1)]]

def C2_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C2_rankPool : List Nat := [8813978, 6524844, 6303387, 2189981, 6655659, 6442940, 6438345, 6577593, 6381500, 6455196, 6586011]

def C2_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r10 r9 r13 r7 r6 r8 < 3) || ((sum6 r12 r10 r15 r8 r3 r6 < 3) || ((sum6 r11 r9 r14 r2 r0 r6 < 3) || ((sum6 r13 r9 r10 r6 r1 r2 < 3) || ((sum6 r11 r10 r14 r8 r5 r6 < 3) || ((sum6 r12 r11 r15 r4 r2 r6 < 3) || ((sum6 r9 r12 r13 r3 r2 r6 < 3) || ((sum6 r9 r11 r13 r5 r4 r6 < 3) || ((sum6 r12 r11 r15 r5 r1 r6 < 3) || ((sum6 r12 r9 r15 r7 r2 r6 < 3) || ((sum6 r11 r9 r14 r7 r4 r6 < 3) || (false)))))))))))
  | masks => C2_rankPool.any (fastEntry (compactGoal 9 7) 4 C2_coords masks)
def C2_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C2_patternScore (C2_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C2_rows : List Nat := [26, 28, 50, 52, 74, 76, 97, 98, 100, 3, 5, 9, 17, 6, 40, 80]
def C2_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C2_rows)
def C2_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)
def C2_ori : List Nat → List Nat := literalRouteOrient C2_literalRoutes
def C2_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 7) (compactCover 9 7) C2_S C2_N C2_idx C2_ori
    C2_patternScr C2_patternScr s
def C2_F : Nat → Bool := certAt C2_Z C2_N 10
def C3_initial : List Nat := [0x722, 0xa95, 0x1948, 0x20e6, 0x2419, 0x40f8, 0x5007]

def C3_values : Nat := 0x3a0ff419e80fd003803f000c9f393e320ce0fec1f1839b0005a97b52b67e2ca7d948b00f5c9eb915407a40f441e87c5000952b23e239144f885f107e20003d597a90e7b9ca42e9d5d2aabdd54aa7e64e769c8927fa40041c082110202022400c8000fb51d4836903edc74a8b9514001000100010001c002100110020000c00140010001

def C3_patterns : Nat := 0x0

def C3_N : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 23
  | 7 => 45
  | 8 => 31
  | 9 => 1
  | _ => 0

def C3_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x8001000
  | 6 => 0x14003000
  | 7 => 0xd01f001
  | 8 => 0x1a005
  | 9 => 1
  | _ => 0

def C3_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x381101000
  | 6 => 0x481181000
  | 7 => 0x381481101
  | 8 => 0x501202
  | 9 => 257
  | _ => 0

def C3_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x1501]
  | 6 => [0x0, 0x1, 0xd0108401001]
  | 7 => [0x2, 0x289cc090500ae81613, 0x8c5ceae]
  | 8 => [0x33, 0x3490020900a04c05, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C3_records : Nat → List (List Nat)
  | 4 => [[], [0x2187], []]
  | 5 => [[], [0x2097], [0x48830c47e1d6990ed4dd270d4cc4488dab234d4cc3]]
  | 6 => [[], [0x169f6b6dd57], [0x6ab4dad265da93a6fccc726471b85a75cb5364c76548671a23dc613c2edccc76aaad35666df3596d4ed376d69c244cdaacb31568f]]
  | 7 => [[0x7f], [0x87b84fcf7d537dadb4f7d69f45ec77d2dddadf60fc8fb5d7d45f797cc7768fc67d6f7dafb5efd8bf29dc9f733bc6fd577d6df2bdcbf7], [0xdd69f784ebb54d6c98bceddb5b3c4fac226dd113e6dced76e4eba6275d293ce849e7]]
  | 8 => [[0x165556555565565555], [0x1ffc57f81fc97f0bfc17f43fc9f78dfc1ff27fc37f3ffc47f6f7cd7f3bfd2ff0ffc4ff03fce7f09fd1ff17fdeff], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C3_S (s j : Nat) : List Nat :=
  qGroupedState C3_initial 3 15 7 C3_patterns C3_values (C3_counts s) (C3_specs s) (C3_records s) j

def C3_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C3_initial (C3_counts s) (C3_specs s) (C3_seeds s) ws

def C3_literalRoutes : List (List (Nat × Nat)) := [[(0x4040,1),(0x1010,2),(0x404,4),(0x3232,2),(0x4040,1)]]

def C3_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C3_rankPool : List Nat := [7695241, 3165884, 1060250, 5442728, 6576523, 3235468, 3239306, 6650776]

def C3_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r9 r8 r11 r6 r5 r7 < 3) || ((sum6 r12 r11 r14 r4 r0 r3 < 3) || ((sum6 r10 r9 r13 r2 r0 r1 < 3) || ((sum6 r8 r10 r12 r0 r3 r5 < 3) || ((sum6 r11 r8 r9 r5 r4 r6 < 3) || ((sum6 r12 r8 r14 r5 r1 r3 < 3) || ((sum6 r10 r8 r13 r6 r1 r3 < 3) || ((sum6 r8 r9 r11 r7 r5 r6 < 3) || (false))))))))
  | masks => C3_rankPool.any (fastEntry (compactGoal 8 7) 4 C3_coords masks)
def C3_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C3_patternScore (C3_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C3_rows : List Nat := [28, 49, 52, 74, 76, 97, 98, 100, 3, 5, 9, 6, 18, 40, 80]
def C3_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C3_rows)
def C3_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def C3_ori : List Nat → List Nat := literalRouteOrient C3_literalRoutes
def C3_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 7) (compactCover 8 7) C3_S C3_N C3_idx C3_ori
    C3_patternScr C3_patternScr s
def C3_F : Nat → Bool := certAt C3_Z C3_N 10
def C4_initial : List Nat := [0x721, 0x94a, 0xa94, 0x20e7, 0x3418, 0x40f8, 0x5007]

def C4_values : Nat := 0xefcfdc87a7c741fe831d01fa0070e7e1c1c01f80060ffc1f1839f0005a94b29f652ac03d727ae43501e883d0ffa1f1400254a49fa929523e23fcc72189f107e20704048804100620003d5a7830dce5b90b51869fed001873b0005528a7bd4a528e74fce9c85273a40043ce83810212021400e8000d4a172120003dac7908e9417bc2e5048008000800040007000480084008401000180010001c0010001

def C4_patterns : Nat := 0x0

def C4_N : Nat → Nat
  | 4 => 2
  | 5 => 18
  | 6 => 51
  | 7 => 79
  | 8 => 44
  | 9 => 1
  | _ => 0

def C4_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x400d001000
  | 6 => 0x4026009000
  | 7 => 0x1a034001
  | 8 => 0x25007
  | 9 => 1
  | _ => 0

def C4_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x301301101000
  | 6 => 0x201581401000
  | 7 => 0x601501101
  | 8 => 0x481302
  | 9 => 257
  | _ => 0

def C4_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0xb5504e, 0x10]
  | 6 => [0x0, 0x887802, 0x2130150220108027100eb7824819, 0x1]
  | 7 => [0x2, 0x3d78a2f0f1e706c0116c6a01c0400442, 0x81a07e027004001402014, 0x0]
  | 8 => [0x4c3, 0x18e0f0d0044c3392a980433, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C4_records : Nat → List (List Nat)
  | 4 => [[], [0x2707], [0x14e806], []]
  | 5 => [[], [0x2517], [0x140fc6a9403bb3a1e84a0f4200e8b00d2e545a84d0f42587767cb529e1d7270f16199], [0x9ae9a929ae9c11a135a86a135d03]]
  | 6 => [[], [0x2357a13d576995cff696ddd9f4f9e7b7], [0x1d35b4e9c59a11e3d23b1d222e340bc78aecdbb405e84d4f2d2335c94bd09b1d21fe542697907eb50823d7262f426879aecbbb365e91fad2cfb6a0ea5c0767aa2e2f4104796b8bcd5e5e6ae2f41ace9720bae3f5a84d1eb8a9e2443c52965dd972f41d8f], [0x9ad57169ae9713a135707a546687]]
  | 7 => [[0x7f], [0x4dde85f7efdbdf917cd77777d85f49ed4efa1bda5fa9ddafe41dd8df3bdddbf677e5f72bfa95f5f7de5f9bdd95f767d66f3fde3f723ecf773fda5bf96dc7fb4bdcc7733de84f37ddf3f2decffe25f877d39dd75f75ecbf743de13f], [0xf97ed48dd7a5467d05d3dd2eb73571f9ababcb2edd5a0ed357376abaf529b5d217e71d7572037cd19add720aeb8bd75c50fc15c7e6b2af48bd79ab8bc82f5e93b3f49057], []]
  | 8 => [[0x2555555559559555596555556], [0x17f1bfe6f7a5fc1ffa57d0777bfc47f29fe6ff47fc87f83fc0ff89fc9ff17fe8ff93fdb7f13fc37f41fd5ff15fcbf75dfd6ff73fc3ff5d7d47f2ffc27f0bfc67f], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C4_S (s j : Nat) : List Nat :=
  qGroupedState C4_initial 4 15 7 C4_patterns C4_values (C4_counts s) (C4_specs s) (C4_records s) j

def C4_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C4_initial (C4_counts s) (C4_specs s) (C4_seeds s) ws

def C4_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C4_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C4_rankPool : List Nat := [7756171, 4205722, 3239644, 2112425, 5467530, 3165096, 4357852, 3153034, 5537178]

def C4_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r11 r8 r9 r5 r6 r7 < 3) || ((sum6 r10 r9 r12 r2 r0 r4 < 3) || ((sum6 r12 r13 r14 r6 r1 r3 < 3) || ((sum6 r9 r10 r11 r3 r0 r2 < 3) || ((sum6 r10 r8 r13 r6 r3 r5 < 3) || ((sum6 r8 r10 r11 r4 r0 r3 < 3) || ((sum6 r12 r13 r14 r7 r2 r4 < 3) || ((sum6 r10 r8 r12 r1 r0 r3 < 3) || ((sum6 r10 r9 r13 r7 r4 r5 < 3) || (false)))))))))
  | masks => C4_rankPool.any (fastEntry (compactGoal 8 7) 4 C4_coords masks)
def C4_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C4_patternScore (C4_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C4_rows : List Nat := [49, 50, 52, 74, 76, 97, 98, 100, 3, 5, 9, 6, 24, 40, 80]
def C4_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C4_rows)
def C4_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)
def C4_ori : List Nat → List Nat := literalRouteOrient C4_literalRoutes
def C4_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 7) (compactCover 8 7) C4_S C4_N C4_idx C4_ori
    C4_patternScr C4_patternScr s
def C4_F : Nat → Bool := certAt C4_Z C4_N 10
def C5_initial : List Nat := [0x721, 0x94a, 0xa94, 0x141e, 0x30e0, 0x40f8, 0x6007]

def C5_values : Nat := 0xe83fd07ba0070f8e1cfc383803f000d529a53f4a56807ce4f9c87203e107c1ff83e300054fea83d43e254a49fa929523e23fcc72189f107e207040488041006200039ea71c0df85a7f34e0683cc7818002a944e428000eaf1c1e35285cfcb90951e280040007b58f211d282f785ca09001000100008000e0009001000100018001400180010001

def C5_patterns : Nat := 0x0

def C5_N : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 21
  | 7 => 52
  | 8 => 40
  | 9 => 1
  | _ => 0

def C5_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x6001000
  | 6 => 0x13002000
  | 7 => 0xb028001
  | 8 => 0x21007
  | 9 => 1
  | _ => 0

def C5_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x401101000
  | 6 => 0x481181000
  | 7 => 0x281481101
  | 8 => 0x501482
  | 9 => 257
  | _ => 0

def C5_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x5e01]
  | 6 => [0x0, 0x1, 0x16599340a0f]
  | 7 => [0x2, 0xb11e330040c0a72b0c367b, 0x2425]
  | 8 => [0x10202, 0x205006012134600581c15, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C5_records : Nat → List (List Nat)
  | 4 => [[], [0x2307], []]
  | 5 => [[], [0x208f], [0x203e331dd966c58747861db140f01d9a]]
  | 6 => [[], [0x6c7e1cf], [0x325b6931e1f0db0f8a5a7476c5d930b30d6ce223fc406c6e4431ed918f86d23c5291da2dad1610f6c4c7a6405ddb63d0d94b]]
  | 7 => [[0x7f], [0x677cfef29dc8fe577d65f2bddcbf87bd4df6cfd077877d35f6f7cefb6d7d97b84fd55f21ee1cf517c6fd3dbd0ef1ded6fe69dcb7e8b7debf33dd7df6c7dd3f4f7ce7e49bcc7b], [0xf19e5926b71624f5a9af434d3e2b63f2131f8a8e7a6367da26af149cf]]
  | 8 => [[0x1655555655565555565565595], [0x137f47fdfff0ffc17f15fc67f89fe47f07fe2ff5dfc27f4d7c37f79fdc7f03fe2df45fc7ff4bfd8ff0bfcdff27fc4ff6bfcd7f11fc97f2ffc5ff], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C5_S (s j : Nat) : List Nat :=
  qGroupedState C5_initial 3 15 7 C5_patterns C5_values (C5_counts s) (C5_specs s) (C5_records s) j

def C5_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C5_initial (C5_counts s) (C5_specs s) (C5_seeds s) ws

def C5_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C5_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C5_rankPool : List Nat := [7695241, 1059752, 5258957, 7409068, 5336202, 5405850, 4413835]

def C5_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r9 r8 r11 r6 r5 r7 < 3) || ((sum6 r8 r10 r11 r2 r0 r1 < 3) || ((sum6 r13 r12 r14 r3 r0 r5 < 3) || ((sum6 r12 r10 r13 r0 r1 r7 < 3) || ((sum6 r10 r8 r12 r6 r1 r5 < 3) || ((sum6 r10 r9 r12 r7 r2 r5 < 3) || ((sum6 r11 r8 r9 r5 r3 r4 < 3) || (false)))))))
  | masks => C5_rankPool.any (fastEntry (compactGoal 8 7) 4 C5_coords masks)
def C5_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C5_patternScore (C5_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C5_rows : List Nat := [33, 42, 44, 74, 76, 81, 82, 84, 3, 5, 9, 6, 24, 48, 96]
def C5_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C5_rows)
def C5_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)
def C5_ori : List Nat → List Nat := literalRouteOrient C5_literalRoutes
def C5_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 7) (compactCover 8 7) C5_S C5_N C5_idx C5_ori
    C5_patternScr C5_patternScr s
def C5_F : Nat → Bool := certAt C5_Z C5_N 10
def C6_initial : List Nat := [0x9b6, 0xe49, 0x1292, 0x1524, 0x6007, 0xa038, 0xc1c0]

def C6_values : Nat := 0xe1f8e1c0e03fe007e000d1c0c9c0c3c0c000a83872976e4f69b7600035242e4929b620001fb61f6d1f241edb1e921e491e001db61d241bb61a9219b617b617241400120010000fff0e000bb60a0008920806080002000092000600020001

def C6_patterns : Nat := 0x0

def C6_N : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 29
  | 8 => 23
  | 9 => 1
  | _ => 0

def C6_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x4001000
  | 6 => 0xa003000
  | 7 => 0x6016001
  | 8 => 0x12005
  | 9 => 1
  | _ => 0

def C6_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x281101000
  | 6 => 0x301301000
  | 7 => 0x301681101
  | 8 => 0x481202
  | 9 => 257
  | _ => 0

def C6_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0xb]
  | 6 => [0x0, 0x10, 0x14086]
  | 7 => [0x2, 0x10fc021002000c532001, 0x45e]
  | 8 => [0xa2, 0xe1008320411, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C6_records : Nat → List (List Nat)
  | 4 => [[], [0xbf0], []]
  | 5 => [[], [0x158f], [0x34be0eb1c1c6781e4f0]]
  | 6 => [[], [0x2bd8bf8df6], [0x18478d2ab6689f0e9bc963b930b74bec1eaa7ca7787d331e]]
  | 7 => [[0x7f], [0x2a7e4fe43babdae7ec7d83e9deddfcffe1bf43dd3fc97ea1f8ff8afd16f53f52fc8fcaf7], [0x151bb38b7658ded48cf91379daf4f]]
  | 8 => [[0x155555955565565655], [0x2fe6ff53f23fc5fe1ff07fdbfc4fe37e1bfcbfccfea7f8ffbdfe4fed7f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C6_S (s j : Nat) : List Nat :=
  qGroupedState C6_initial 3 16 6 C6_patterns C6_values (C6_counts s) (C6_specs s) (C6_records s) j

def C6_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C6_initial (C6_counts s) (C6_specs s) (C6_seeds s) ws

def C6_literalRoutes : List (List (Nat × Nat)) := [[(0x4140,1),(0x200,4),(0x20,8),(0x208,4),(0x2010,2),(0x4140,1)],[(0x10,2),(0x6,4),(0x13,2),(0x4015,1)],[(0x4100,1),(0x200,4),(0x20,8),(0x20e,4),(0x2013,2),(0x154,1)],[(0x100,2),(0x4,8),(0x7,4),(0x2132,2),(0x4015,1)],[(0x130,2),(0x4,8),(0x3,4),(0x2130,2)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x302,2),(0x114,1)],[(0x4404,1),(0x100,4),(0x10,8),(0x104,4),(0x2222,2),(0x4404,1)],[(0x110,1),(0x210,2),(0x800,4),(0x80,8),(0x806,4),(0x313,2),(0x4105,1)],[(0x4110,1),(0x200,4),(0x20,8),(0x20e,4),(0x2111,2),(0x144,1)],[(0x144,1),(0x2,8),(0xb,4),(0x2111,2),(0x4110,1)],[(0x104,1),(0x10,2),(0x2,8),(0x9,4),(0x2110,2),(0x114,1)]]

def C6_coords : List Nat := [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15]
def C6_rankPool : List Nat := [5258684, 2103945, 5339800, 4353483]

def C6_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13] => (sum6 r12 r11 r13 r3 r0 r5 < 3) || ((sum6 r9 r8 r10 r1 r0 r2 < 3) || ((sum6 r8 r9 r10 r7 r1 r5 < 3) || ((sum6 r11 r12 r13 r6 r2 r4 < 3) || (false))))
  | masks => C6_rankPool.any (fastEntry (compactGoal 9 7) 4 C6_coords masks)
def C6_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C6_patternScore (C6_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C6_rows : List Nat := [17, 26, 28, 33, 42, 44, 65, 74, 76, 3, 5, 9, 6, 48, 80, 96]
def C6_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C6_rows)
def C6_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C6_ori : List Nat → List Nat := literalRouteOrient C6_literalRoutes
def C6_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 7) (compactCover 9 7) C6_S C6_N C6_idx C6_ori
    C6_patternScr C6_patternScr s
def C6_F : Nat → Bool := certAt C6_Z C6_N 10
def C7_initial : List Nat := [0x750, 0x98d, 0x122b, 0x20f8, 0x2407, 0x4832, 0x50c4]

def C7_values : Nat := 0xe989c31361bec32d1f5a0cb203e0f8b39b63dac6254c4a58948ae8e24f72937f20023a840006c56c8ad6c7ac0753faa3e13fc27574ea0941d27fa4f8480087e1028203040508000dd79a2b2c564cac7ee8f5012002000200010000a000c00140022002000240018002

def C7_patterns : Nat := 0x0

def C7_N : Nat → Nat
  | 5 => 3
  | 6 => 11
  | 7 => 40
  | 8 => 34
  | 9 => 1
  | _ => 0

def C7_counts : Nat → Nat
  | 5 => 0x3000000
  | 6 => 0x9002000
  | 7 => 0x7020001
  | 8 => 0x1c006
  | 9 => 1
  | _ => 0

def C7_specs : Nat → Nat
  | 5 => 0x201000000
  | 6 => 0x281181000
  | 7 => 0x381501101
  | 8 => 0x601302
  | 9 => 257
  | _ => 0

def C7_seeds : Nat → List Nat
  | 5 => [0x0, 0x0, 0x7]
  | 6 => [0x0, 0x1, 0x38a2]
  | 7 => [0x2, 0x2e03804802618010a028, 0x3a5]
  | 8 => [0x7c2, 0x40a80e00780600200221a, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C7_records : Nat → List (List Nat)
  | 5 => [[], [], [0x12398b8911f1a87]]
  | 6 => [[], [0x1cecc67], [0x44e66ddc6dbc6cf8613ef997918c71b9c93431b8c66]]
  | 7 => [[0x7f], [0x43ddcfe7bfbbf47db1dd4ef53f7bb99f53ef8f79bf39ded7eff773f2ddec7e7fb37f2bde3f6defcb7d7ed9eec67877b9d97eec6f], [0x1ba6dd32b3bcef68d3e6f319e24f3b89f6]]
  | 8 => [[0x555959565556555565555], [0x7f95fcbfe27fbff8dfdafe17f4bf8bfe0fe9f74ffcbfdefe77f1ffc5ff4ffb7f77fd1fdeee1ff27fd3ff0fe47f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C7_S (s j : Nat) : List Nat :=
  qGroupedState C7_initial 3 15 6 C7_patterns C7_values (C7_counts s) (C7_specs s) (C7_records s) j

def C7_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C7_initial (C7_counts s) (C7_specs s) (C7_seeds s) ws

def C7_literalRoutes : List (List (Nat × Nat)) := [[(0x1004,1),(0x2000,2),(0x800,4),(0x2032,2),(0x1104,1)]]

def C7_coords : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C7_rankPool : List Nat := [5401464, 3235194, 4275595, 5262473, 6507143, 1059757, 3239033]

def C7_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13] => (sum6 r8 r7 r11 r6 r2 r5 < 3) || ((sum6 r10 r7 r13 r5 r1 r3 < 3) || ((sum6 r11 r8 r13 r3 r1 r4 < 3) || ((sum6 r9 r8 r12 r4 r0 r5 < 3) || ((sum6 r7 r8 r10 r4 r3 r6 < 3) || ((sum6 r13 r10 r11 r2 r0 r1 < 3) || ((sum6 r9 r7 r12 r6 r1 r3 < 3) || (false)))))))
  | masks => C7_rankPool.any (fastEntry (compactGoal 8 7) 4 C7_coords masks)
def C7_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C7_patternScore (C7_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C7_rows : List Nat := [14, 28, 42, 70, 81, 84, 97, 98, 3, 5, 9, 18, 36, 72, 48]
def C7_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C7_rows)
def C7_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def C7_ori : List Nat → List Nat := literalRouteOrient C7_literalRoutes
def C7_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 7) (compactCover 8 7) C7_S C7_N C7_idx C7_ori
    C7_patternScr C7_patternScr s
def C7_F : Nat → Bool := certAt C7_Z C7_N 10
def C8_initial : List Nat := [0x1a5, 0x29a, 0x552, 0xa61, 0x140d, 0x280e, 0x3070]

def C8_values : Nat := 0xd1c3170c3c0f731f683bf06000800014001

def C8_patterns : Nat := 0x5559555

def C8_N : Nat → Nat
  | 7 => 5
  | 8 => 8
  | 9 => 1
  | _ => 0

def C8_counts : Nat → Nat
  | 7 => 0x4001
  | 8 => 0x6002
  | 9 => 1
  | _ => 0

def C8_specs : Nat → Nat
  | 7 => 0x281105
  | 8 => 0x305206
  | 9 => 261
  | _ => 0

def C8_seeds : Nat → List Nat
  | 7 => [0x2, 0x9]
  | 8 => [0x6, 0x463]
  | 9 => [0x2, 0x0]
  | _ => []

def C8_records : Nat → List (List Nat)
  | 7 => [[0x0], [0x87e9fa9fcbf]]
  | 8 => [[0x1], [0x4c329c4]]
  | 9 => [[0x0], []]
  | _ => []

def C8_S (s j : Nat) : List Nat :=
  qGroupedState C8_initial 2 14 4 C8_patterns C8_values (C8_counts s) (C8_specs s) (C8_records s) j

def C8_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C8_initial (C8_counts s) (C8_specs s) (C8_seeds s) ws

def C8_literalRoutes : List (List (Nat × Nat)) := [[(0x450,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x1210,2),(0x450,1)],[(0x1515,1)],[(0x450,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x1210,2),(0x1145,1)],[(0x410,1),(0x2020,2),(0x200,4),(0x20,8),(0xa0d,4),(0x2120,2),(0x1105,1)],[(0x144,1),(0x2000,2),(0x400,4),(0x40,8),(0xd01,4),(0x2022,2),(0x144,1)],[(0x410,1),(0x2020,2),(0x200,4),(0x20,8),(0xa0d,4),(0x2120,2),(0x410,1)],[(0x144,1),(0x2000,2),(0x400,4),(0x40,8),(0xd01,4),(0x2022,2),(0x1451,1)],[(0x104,1),(0x1000,2),(0x800,4),(0x80,8),(0xe02,4),(0x1011,2),(0x1411,1)],[(0x40,1),(0x1000,2),(0x40,8),(0x20a,4),(0x1123,2),(0x40,1)],[(0x104,1),(0x1000,2),(0x800,4),(0x80,8),(0xe02,4),(0x1011,2),(0x104,1)],[(0x40,1),(0x1000,2),(0x40,8),(0x20a,4),(0x1123,2),(0x1555,1)],[(0x2000,2),(0x80,8),(0x105,4),(0x2213,2),(0x1515,1)],[(0x2000,2),(0x80,8),(0x105,4),(0x2213,2)]]

def C8_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def C8_rankPool : List Nat := [5532039, 4398508, 6376859, 6306424, 5377213, 1072266, 6564729]

def C8_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13] => (sum6 r7 r8 r9 r6 r4 r5 < 3) || ((sum6 r12 r10 r13 r1 r3 r4 < 3) || ((sum6 r11 r9 r13 r4 r1 r6 < 3) || ((sum6 r8 r7 r10 r3 r0 r6 < 3) || ((sum6 r13 r11 r12 r0 r2 r5 < 3) || ((sum6 r10 r8 r12 r5 r0 r1 < 3) || ((sum6 r9 r7 r11 r2 r4 r6 < 3) || (false)))))))
  | masks => C8_rankPool.any (fastEntry (compactGoal 7 7) 4 C8_coords masks)
def C8_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C8_patternScore (C8_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C8_rows : List Nat := [25, 38, 49, 50, 70, 73, 76, 3, 5, 10, 20, 40, 80, 96]
def C8_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C8_rows)
def C8_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C8_ori : List Nat → List Nat := literalRouteOrient C8_literalRoutes
def C8_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 7) (compactCover 7 7) C8_S C8_N C8_idx C8_ori
    C8_patternScr C8_patternScr s
def C8_F : Nat → Bool := certAt C8_Z C8_N 10
def C9_initial : List Nat := [0x21e, 0x41e, 0x7e1, 0x82a, 0x854, 0x1086, 0x1118]

def C9_values : Nat := 0x7afb97d918c575fe6fc379ebcc5ce2e3d718b43567ab31538a8f546293d48698c4a7a50d19e8cc44e1fd6fe173f3979ca8e3e71538798fcc5e62a30f9854c1e52a28f90fc8204001ffcc7c62030f1818c0043e210100040c200010007800c002

def C9_patterns : Nat := 0x1595564156555815565555554554555055155151554551

def C9_N : Nat → Nat
  | 4 => 1
  | 5 => 13
  | 6 => 38
  | 7 => 49
  | 8 => 20
  | 9 => 1
  | _ => 0

def C9_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x2008003000
  | 6 => 0x201500f000
  | 7 => 0x18018001
  | 8 => 0x10004
  | 9 => 1
  | _ => 0

def C9_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x181301201000
  | 6 => 0x181501481000
  | 7 => 0x701592111
  | 8 => 0x491312
  | 9 => 273
  | _ => 0

def C9_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x5, 0x504, 0x3]
  | 6 => [0x0, 0x14a7a1e0e, 0xb4095a00c0e001, 0x1]
  | 7 => [0x2, 0x10101300201205808, 0x56dc00400640248060002, 0x0]
  | 8 => [0x1e, 0x4c0180509, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C9_records : Nat → List (List Nat)
  | 4 => [[], [], [0x6da98], []]
  | 5 => [[], [0x68f33798bc], [0xad459021936c9c5731cc5e58fa3931c0e6d799], [0x36b2731b4a618]]
  | 6 => [[], [0x3bf2e7ae7cb5eb7f2b7a57cc5ec1f0cf877cefe1bf0bf98bc], [0x573bcad85b198f3931e3486584cf1be4f3129e328e5a0c7958af32a1e4863cb28795a6f2ba4ea2674dac73b4a6f131e3e86c], [0x194d0c8920664]]
  | 7 => [[0x7], [0x59466e94a525575324c4ac085316819063175613e45d4290cb1591269555], [0xe0cf8619f174fe1857c74cf89219cc0fe4467c653f860bf1333e502be3ccf8605f0c13e3286ddec7a38bf0c07e2467ca93f8ea7f1033e2e2fc], []]
  | 8 => [[0x7a8c], [0x15cc45d4270dd0749c473dc56e1d3705cc789cc5], [], []]
  | 9 => [[0x7], [], [], []]
  | _ => []

def C9_S (s j : Nat) : List Nat :=
  qGroupedState C9_initial 4 13 6 C9_patterns C9_values (C9_counts s) (C9_specs s) (C9_records s) j

def C9_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C9_initial (C9_counts s) (C9_specs s) (C9_seeds s) ws

def C9_literalRoutes : List (List (Nat × Nat)) := [[(0x400,1),(0x200,2),(0x400,1)],[(0x100,1),(0x210,2),(0x800,4),(0x80,8),(0x804,4),(0x212,2),(0x100,1)],[(0x100,1),(0x210,2),(0x800,4),(0x80,8),(0x804,4),(0x312,2),(0x100,1)],[(0x44,1),(0x10,2),(0x4,4),(0x32,2),(0x44,1)],[(0x444,1),(0x10,2),(0x4,4),(0x232,2),(0x444,1)],[(0x110,1),(0x200,2),(0x800,4),(0x80,8),(0x802,4),(0x210,2),(0x114,1)],[(0x110,1),(0x200,2),(0x800,4),(0x80,8),(0x802,4),(0x310,2),(0x114,1)],[(0x1000,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2120,2),(0x1004,1)],[(0x400,1),(0x100,2),(0x400,4),(0x40,8),(0x500,4),(0x320,2),(0x404,1)],[(0x1140,1),(0x210,2),(0x800,4),(0x80,8),(0xa04,4),(0x232,2),(0x1104,1)],[(0x1140,1),(0x210,2),(0x800,4),(0x80,8),(0xa04,4),(0x332,2),(0x1104,1)],[(0x1104,1),(0x2010,2),(0x200,4),(0x20,8),(0xa04,4),(0x2032,2),(0x1140,1)],[(0x1104,1),(0x2010,2),(0x200,4),(0x20,8),(0xa04,4),(0x2132,2),(0x1140,1)],[(0x1010,1),(0x2000,2),(0x100,4),(0x10,8),(0x902,4),(0x2000,2),(0x1050,1)],[(0x410,1),(0x1000,2),(0x100,4),(0x10,8),(0x502,4),(0x1200,2),(0x450,1)]]

def C9_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def C9_rankPool : List Nat := [1059685, 3153016, 4209574, 3278972, 2104214, 4205736, 1064087, 3165061, 2116743, 4392539, 1064103, 4201334, 4205672, 2112599]

def C9_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12] => (sum6 r5 r6 r11 r2 r0 r1 < 3) || ((sum6 r8 r7 r12 r1 r0 r3 < 3) || ((sum6 r6 r10 r11 r3 r0 r4 < 3) || ((sum6 r12 r7 r8 r0 r2 r3 < 3) || ((sum6 r6 r9 r11 r1 r0 r2 < 3) || ((sum6 r8 r10 r12 r2 r0 r4 < 3) || ((sum6 r7 r9 r12 r3 r0 r1 < 3) || ((sum6 r5 r8 r11 r4 r0 r3 < 3) || ((sum6 r7 r8 r12 r4 r0 r2 < 3) || ((sum6 r11 r5 r6 r0 r3 r4 < 3) || ((sum6 r7 r10 r12 r3 r0 r1 < 3) || ((sum6 r6 r7 r11 r1 r0 r4 < 3) || ((sum6 r8 r6 r12 r2 r0 r4 < 3) || ((sum6 r7 r5 r12 r3 r0 r2 < 3) || (false))))))))))))))
  | masks => C9_rankPool.any (fastEntry (compactGoal 5 8) 4 C9_coords masks)
def C9_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C9_patternScore (C9_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C9_rows : List Nat := [1, 106, 108, 114, 116, 3, 5, 9, 17, 33, 65, 6, 24]
def C9_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C9_rows)
def C9_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)
def C9_ori : List Nat → List Nat := literalRouteOrient C9_literalRoutes
def C9_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 5 8) (compactCover 5 8) C9_S C9_N C9_idx C9_ori
    C9_patternScr C9_patternScr s
def C9_F : Nat → Bool := certAt C9_Z C9_N 10
def C10_initial : List Nat := [0x21b, 0x3e4, 0x458, 0x81c, 0xc23, 0x1089, 0x1112]

def C10_values : Nat := 0x1ebbe55f08f22589dc44e072db7512a6cd1627ed3ed9f24e6e7253529994c6e62529b944c86e3371928a944ca1010007fe3f9dfc8ea373db9e1cc6e5c72db961c76e23651b1ed8f0c6362e316187ec2060e30017f8be451c287d438a1b50022710b883c41020610108044001ff0fc86d833c196ccb061b26c11e08804001ff8a6c50025b12008ec440218104880c40008002000800300090040010006001

def C10_patterns : Nat := 0x0

def C10_N : Nat → Nat
  | 4 => 1
  | 5 => 15
  | 6 => 67
  | 7 => 101
  | 8 => 43
  | 9 => 1
  | _ => 0

def C10_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0xd002000
  | 6 => 0x1031011000
  | 7 => 0x23041001
  | 8 => 0x24007
  | 9 => 1
  | _ => 0

def C10_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x501181000
  | 6 => 0x101581301000
  | 7 => 0x501681101
  | 8 => 0x501282
  | 9 => 257
  | _ => 0

def C10_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x1, 0x6aa0901802, 0x0]
  | 6 => [0x0, 0x102273c1, 0x9200402c0abb40540521082706c0445401e, 0x2]
  | 7 => [0x2, 0x11622800405a0dc00d408000600f00782b00260120008060018019, 0x4201532118040dc0a06a1f, 0x0]
  | 8 => [0x1f6, 0x10a28c06054242a80d0d00a, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C10_records : Nat → List (List Nat)
  | 4 => [[], [], [0x10a060], []]
  | 5 => [[], [0x7fc9df2], [0xe59e2846f8426f8613ac9396b480bf13e698989bc55299c5a6b84e66ca8b464e56e4], []]
  | 6 => [[], [0x1ceea0fa73e5bd58e76dcd9f3a4f94767db967639ea0ee35ea1753bea8be], [0x15251d684394d67c9e9ae4e50669cd1b4d5bd29c53ce99f272bb33c67caf3366ccdf29ca9b4069caf2d6b527bc726b53353c9cb4ccd5a633c6fc4868cdd2fccb8d725a2ba39559998ae538d3a606f92d53d2f5c2ecd6f1686f93a5bd101ae4bcdf29cb9b375f8d51ae539cae686b94e40da21be4d08f2b4d392d37d274c3d3e31e], [0x86e9764]]
  | 7 => [[0x7f], [0x2f3fb5f88fe47debfb35ea6fe2fed77792fc97e8d7ecbf1bf96f56bbd17773fadf737fa9fe9cf85fe1df9cef75f87fe35f8b7b19f96f73df63bf31ee07e53f887ec3f9a7733fa43f55de5fe49de2774ddd6fd41de73f5fdd0f767cd9f761dea7d35eefef67ec57e4bde67e27f9cee4fddc6f], [0x4d5dd9a1be680df6542bb1f37eac34e7790379a83b1a15e99a0e73e2be686fd4a8a7e6b4ece91f6402bb4e14f9d20ece9a76722b7569ef9bb4e6a5076682bb3a5dd9a1becb8df63657d4375ba1aeeab50755c2bb3437c9a08e6b86f6], []]
  | 8 => [[0x1555595595556555565565565], [0x65fc57f09fc3ff15f907757fcaff6ffc1ffabfc47f5ddda7741ff07f5dfc2ff8bfc4ff9bf8dff37fa6ffb1fda7fbbfc17f29fdd7e95fc37f75fc0ff87fcfff], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C10_S (s j : Nat) : List Nat :=
  qGroupedState C10_initial 4 13 7 C10_patterns C10_values (C10_counts s) (C10_specs s) (C10_records s) j

def C10_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C10_initial (C10_counts s) (C10_specs s) (C10_seeds s) ws

def C10_literalRoutes : List (List (Nat × Nat)) := [[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)]]

def C10_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12]
def C10_rankPool : List Nat := [4340328, 2181477, 2103943, 4204121, 3221626, 2165336, 2111861, 3279222, 3295879, 4331862]

def C10_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10] => (sum6 r8 r6 r10 r3 r2 r4 < 3) || ((sum6 r5 r6 r9 r4 r1 r2 < 3) || ((sum6 r7 r8 r10 r1 r0 r2 < 3) || ((sum6 r9 r5 r6 r2 r0 r4 < 3) || ((sum6 r10 r7 r8 r2 r1 r3 < 3) || ((sum6 r8 r5 r10 r0 r1 r2 < 3) || ((sum6 r5 r7 r9 r3 r0 r2 < 3) || ((sum6 r6 r7 r9 r0 r2 r3 < 3) || ((sum6 r7 r8 r10 r4 r2 r3 < 3) || ((sum6 r6 r5 r9 r1 r2 r4 < 3) || (false))))))))))
  | masks => C10_rankPool.any (fastEntry (compactGoal 5 8) 4 C10_coords masks)
def C10_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C10_patternScore (C10_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C10_rows : List Nat := [42, 50, 65, 108, 116, 3, 5, 9, 17, 33, 6, 66, 24]
def C10_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C10_rows)
def C10_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)
def C10_ori : List Nat → List Nat := literalRouteOrient C10_literalRoutes
def C10_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 5 8) (compactCover 5 8) C10_S C10_N C10_idx C10_ori
    C10_patternScr C10_patternScr s
def C10_F : Nat → Bool := certAt C10_Z C10_N 10
def C11_initial : List Nat := [0x3e10, 0x42a5, 0x454a, 0x8863, 0x918c, 0x101f0, 0x1200f]

def C11_values : Nat := 0x7abbf97efbff0dfce6f84373dfb98cdc07ece33631fb18cd807ec00350dfa863d007e800323f991f0c8c66400313e78863c400607c300017ff5bff85fafefd6b7e10b3f7d953eca9563ffb157d8a96c41f600fb00051ffe8bf5454aa1fad0fc2854b41f0a0004fffe7fe13e709f0fcf842601f2a0f9407c983e481f23f091504883e440121ff90f8481be405f201f9001c800217e109f083f840fc2040101f380f8c0782030100e0803840182004100108001c0001fdeedd4a6df7b5739ab18d3ad69c6346319fdecd6b6631b2b9d90c6c54a6152afe717ce6be105cc62ce316318a8634dc6267bd331898634c0025e312b18938c45319fffcfeb47eb53f0819528c54a4d4a255291fbc8e9446a5220010f9485ce42e5215a90abc854e42a0211090814840040a020109001480003e701f188f84c44002010100188000140006000150008840420020501000078001c0007000318018400c000230010800800020000f00038000c00020000

def C11_patterns : Nat := 0x2555855615465555595559555555155151551594561156455515415541590558155

def C11_N : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 110
  | 7 => 227
  | 8 => 193
  | 9 => 23
  | 10 => 1
  | _ => 0

def C11_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0xc00c001000
  | 6 => 0x2d03a007000
  | 7 => 0x1b093034001
  | 8 => 0x4e06e005
  | 9 => 0x12005
  | 10 => 1
  | _ => 0

def C11_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x581581101000
  | 6 => 0x581601481000
  | 7 => 0x401581596115
  | 8 => 0x501596216
  | 9 => 0x415216
  | 10 => 277
  | _ => 0

def C11_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0xcdc05002, 0xea403401]
  | 6 => [0x0, 0x10a03, 0x383a08500550b02d01401126200183a04602601a02a, 0xe9a00b00206e0fc2f80201800406050]
  | 7 => [0x2, 0x67e29e61583c00e010552718360340c801, 0x47d8ac048560fb22c0500209401a17c8a0023361ca288d70020c0488330068682806b00200c1a01f88f0cc0200c15c04c0e82c, 0x7050c4d03012c]
  | 8 => [0x47, 0x44b10c4a0fc02d0d80546e09e2ecbc9a70a40087f02905f054020190e0268090088dc0d403409, 0x10001150010f00431c039286302c1e00408245cb0080b16247, 0x0]
  | 9 => [0x47, 0x7d03010358, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C11_records : Nat → List (List Nat)
  | 4 => [[], [], [0x53d306], []]
  | 5 => [[], [0x4f8f], [0xa2940f4d241e85dc750ca879b3f0f433a1e95dc75222a6a73f8d4f443a8ddc72aa2e2], [0xa195770d4314ee2a61dccc550cebb86a19d8a07312a660e8605dc533a29f868c771e314cae8a1a61dd04345bb9118]]
  | 6 => [[], [0xce7cf33c21f979edc7e36f3bde], [0x114ff350b38fab773e8a7b9a31dcf42bb9ea645cceede79d915751490f98671ea469aa85dc7b3929da1775d433a9d51173b91139776a3cee4572addcf504c8fa19d8e763da59cf87aa22e677683ca4998d5d107bb9cce67421eae843e62563c91fc7674f1ece723d9cd0f50bbce77429d42ee3914f3343bb9ea1571f433a3ddd9cf1d11694531e510ee795d0c7bba7ce776b3ceedc7a86743bb9f4e731e7330ef399c88ed022ae], [0x54a29fc6a29e930ef48a7f1a6256061a7a517e1a18a6717388a7e9aa289dc74f4c4a87a19d7a0f433ace1e615d043d14f22a69895880f16ae44659cbc78caba1208798573317312a2e1e8a69dc7514d4a87772f1eb1268a7f1a85dd5c74c40bbca9895778d4530ee3a895d14750bd3c0e9e98771ca69a91852514ff1513ba38e8c571e32ae84662e85dd9c74e499f879877671cae8a7f1a61dc5c73baba10e8b771e353110ee3a85e9dc729a6a2e2]]
  | 7 => [[0xc], [0x792b38dc0b0c364292a9dd6ce2245428da06e637f2af95b0acc56329a2ddcaea3394a824894b65444be1568aee7a14a124f929e977811a970a769592c815f4aae5670bd150d2ee4622cc25c4a8096f1b38174ace5], [0x8c63ce61de744339fa25b3f448bb93d2b3aba14f8077bd10eef99c04fbba5df7717bca28bbd408b6c3113d7a399ef46979e896ebba5de7759bcce5e7ddd9cf9711797e77bd1cef7a617a7b3841f7d34bc84839e85ea7bd1f4f4233d6ae4574e87b5bbb3be80673f0a9ebe315cf9c976b3422f8ee217a21dcf3b80de7767bd30ef3e62567bd339f4f34dce87cbe61df71791796a573f10ee7e459cfab8d1f7706bcae647cb47bcbd115d57173f10ef799c5cfb3819f57183f10ae7ead5cfaba7cf57421ea28bb91cf73bd3bde6f573e3c2be55d097bb9ade78673f3d30bd14ff3b90f3b671e3ea293ad9c50fb79caf85573f0af47ddcbef50b3af6b573eeedb79d91d7bb845e7b673ef49f3e625a7978f797a683eca7d3ddc2af42be9f771ebceeaf78d043e3d0ddea1679e8a7f995ce67a29fee7d4f9f30af3d9cd4fcc4ae77703bcf4853e8a4e7b19ccf77673d312b1e40d2f459179670a3edec67d9c18fab9a5e7a78bd10b27de1def43b39fa1671f183de5dddef33881f674b3ecece7e61ea7bd379f67573e5821e5b19cfab9f4f6d673f3103adfc8aec29a3e4d22f29c3de4e4e33b6214f], [0x110f4f07a62555e3cc40abcba298571f4534ae3e7a615c7bd3bb39e8877573cae5e3d65e9e19cf3bab8b9e7d2f1eb2f45e3d662d5c78da3a31fe6852f1e7317103ce5dd9d5cf4c442b8fa17a671f30ae2e3d3cbc7b4aba10b8f9877579d44ae8e3d4d447b49a178f78]]
  | 8 => [[0xd931ee], [0xd16ae857306b185896d9160331e90eec1063395dcb0a31460131bc6f6c4f49a30318c6c20613b02d872977234b20d8ae54249831e8a26c67644b1818f4c6328ab0dd8af159601b0bd84cc2250431e1808c6a614b039832c6f605323d8d8c2a636b06180ac1e60e31ea2b65aa615b0c98b253e4bd18258ce34e625b059910c1f64c247581ec17642b0b5822c6c2b5b085850c7e60db00586ac6704031f58aec5b655b231834c7d289301d844c4862b31618eeb], [0x1e9e2fd123ef5710bef4f1f8b843dc42b9f3622faf46b7e21e1fbd0f5f341efcf45f7cbc7bd978f797757bef4cf7d451f7c8bd5f7a03beae077de99cfab8b9f6f107e8e7fbdedeafc5c43f851e7eae977e796ef9b1afe570abef4cefe615f7d14d6f6c17be7221bcd443eab97df8b1ef6f4f1795c5dfb1885f5708bef4117e615e7bf2bdf8857bf10f57c7843ebbabde7a6dbeae2f7e215dfbd2bdf7d1ebef4157de15efb6abdf5735bef4217e0a02fab835f7a17bf00f57de166fababdf4f1edef4297d4d477a10bef5701beeeaffa015efbd25df4d1ef6f4f57de81afab8f5f], []]
  | 9 => [[0xd931ee], [0x12d8dac0364031e8a5ec356043019814c572c430418f0c7a60bb0798aec], [], []]
  | 10 => [[0xc], [], [], []]
  | _ => []

def C11_S (s j : Nat) : List Nat :=
  qGroupedState C11_initial 4 17 8 C11_patterns C11_values (C11_counts s) (C11_specs s) (C11_records s) j

def C11_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C11_initial (C11_counts s) (C11_specs s) (C11_seeds s) ws

def C11_literalRoutes : List (List (Nat × Nat)) := [[(0x1000,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2123,2),(0x1000,1)],[(0x440,1),(0x100,2),(0x400,4),(0x40,8),(0x400,4),(0x320,2),(0x445,1)],[(0x1100,1),(0x2000,2),(0x200,4),(0x20,8),(0xa00,4),(0x2103,2),(0x1145,1)],[(0x4,1),(0x1000,2),(0x400,4),(0x1202,2),(0x4044,1)],[(0x1404,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2322,2),(0x5041,1)],[(0x1044,1),(0x100,2),(0x400,4),(0x40,8),(0x600,4),(0x321,2),(0x5401,1)],[(0x104,1),(0x200,4),(0x20,8),(0x300,4),(0x1,2),(0x4504,1)]]

def C11_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C11_rankPool : List Nat := [239352137, 272842092, 134398253, 206711086, 136330604, 205798731, 235024751, 272710026, 135281066, 172177769, 137642381, 135479629, 134299051, 136561037, 205764970, 135380395, 272809260, 136560941, 205699370, 205765002, 239254828, 272873866, 172211595, 136593741, 170013007, 241315118, 235023695, 206713166]

def C11_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16] => (sum6 r9 r10 r14 r8 r4 r7 < 3) || ((sum6 r12 r11 r15 r6 r4 r8 < 3) || ((sum6 r13 r9 r16 r5 r0 r4 < 3) || ((sum6 r14 r9 r10 r4 r5 r6 < 3) || ((sum6 r12 r11 r15 r0 r2 r4 < 3) || ((sum6 r11 r10 r15 r8 r4 r6 < 3) || ((sum6 r15 r11 r12 r4 r0 r7 < 3) || ((sum6 r10 r12 r14 r2 r4 r8 < 3) || ((sum6 r10 r13 r14 r0 r1 r4 < 3) || ((sum6 r9 r11 r14 r6 r4 r5 < 3) || ((sum6 r13 r12 r16 r8 r3 r4 < 3) || ((sum6 r13 r10 r16 r6 r1 r4 < 3) || ((sum6 r11 r13 r15 r2 r0 r4 < 3) || ((sum6 r13 r12 r16 r7 r2 r4 < 3) || ((sum6 r10 r11 r14 r7 r4 r6 < 3) || ((sum6 r11 r13 r15 r3 r1 r4 < 3) || ((sum6 r12 r9 r15 r5 r4 r8 < 3) || ((sum6 r13 r9 r16 r7 r2 r4 < 3) || ((sum6 r10 r9 r14 r5 r4 r6 < 3) || ((sum6 r10 r12 r14 r7 r4 r6 < 3) || ((sum6 r12 r9 r15 r5 r4 r7 < 3) || ((sum6 r10 r12 r14 r7 r4 r8 < 3) || ((sum6 r11 r12 r15 r7 r4 r5 < 3) || ((sum6 r13 r10 r16 r8 r2 r4 < 3) || ((sum6 r15 r10 r12 r4 r2 r5 < 3) || ((sum6 r14 r9 r11 r4 r6 r7 < 3) || ((sum6 r15 r10 r11 r4 r0 r7 < 3) || ((sum6 r14 r10 r12 r4 r5 r6 < 3) || (false))))))))))))))))))))))))))))
  | masks => C11_rankPool.any (fastEntry (compactGoal 9 8) 5 C11_coords masks)
def C11_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C11_patternScore (C11_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C11_rows : List Nat := [42, 44, 50, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 33, 6, 24, 96]
def C11_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C11_rows)
def C11_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C11_ori : List Nat → List Nat := literalRouteOrient C11_literalRoutes
def C11_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 8) (compactCover 9 8) C11_S C11_N C11_idx C11_ori
    C11_patternScr C11_patternScr s
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

def C12_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x1008005000
  | 6 => 0x102a019000
  | 7 => 0x2b02f001
  | 8 => 0x1c006
  | 9 => 1
  | _ => 0

def C12_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x101501281000
  | 6 => 0x101681381000
  | 7 => 0x515516115
  | 8 => 0x515296
  | 9 => 277
  | _ => 0

def C12_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x115, 0x4fc01, 0x2]
  | 6 => [0x0, 0xc8282122aa94, 0x2c800060dc000800a02e0060c14058014065, 0x2]
  | 7 => [0x2, 0x43c340b8481081516c2402c020b805, 0x7828021f921004fd0981425c04, 0x0]
  | 8 => [0x1a5, 0x21182c3d078040358c, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C12_records : Nat → List (List Nat)
  | 4 => [[], [], [0xe9c60], []]
  | 5 => [[], [0x1a71658dd726fc5772], [0xa0b992027c284e26e1861a0d18b66b8603562d1770], [0x8709492]]
  | 6 => [[], [0x11f669cd07559cd57345d54f35dd9a7539d93f363cd47379cd77257cd8739bcd3735dcd2f35fcdaf35bcda71], [0x1495e3310353a4f936538d793e5154f180a59cc38d9725e4d4af170d78c66bc64a967454e3522f8ae53ca1a9e4fd4b38708f2029c5093e5325978ea59b453c60216aa4671523794152cdb21cae54e3403f8b50fc5f29a6d12f1383f93b5fc9493e5414b342578d04acd48ae280e74], [0x84f5493]]
  | 7 => [[0x10], [0x2ae5e51ed3893ca52a6aa4a582214e3aa7e280234a22d40a1af16e5348ae20d32a30a5273ea5ea92240872426f42a18e36a48a94a38a6c4a245257c35366a54aa8e286f24d526], [0xe10a22292d25255224ad4b15c292a90455214a5c7957a92a90255220aa47154a52a128576a4abca161292c85255250a547ae48f0931ec421d0cd4954a92a92c5423ca84b15aa929d1e5523caecea54862a90653a50b190a27a92bd52584f40a42163292a90e5], []]
  | 8 => [[0x2b3bc650], [0x9101ed0502d06708d00301305250705300900d01d08908502900f03aa1100b01f042a7107b077052aa50], [], []]
  | 9 => [[0x10], [], [], []]
  | _ => []

def C12_S (s j : Nat) : List Nat :=
  qGroupedState C12_initial 4 13 7 C12_patterns C12_values (C12_counts s) (C12_specs s) (C12_records s) j

def C12_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C12_initial (C12_counts s) (C12_specs s) (C12_seeds s) ws

def C12_literalRoutes : List (List (Nat × Nat)) := [[(0x400,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x511,1)]]

def C12_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12]
def C12_rankPool : List Nat := [4340344, 2181509, 3155545, 3279222, 2103895, 3295879, 2111861, 4331910, 4204666, 2165368]

def C12_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10] => (sum6 r8 r7 r10 r3 r2 r4 < 3) || ((sum6 r5 r8 r9 r4 r1 r2 < 3) || ((sum6 r9 r5 r6 r2 r0 r3 < 3) || ((sum6 r6 r7 r9 r0 r2 r3 < 3) || ((sum6 r7 r5 r10 r1 r0 r2 < 3) || ((sum6 r7 r8 r10 r4 r2 r3 < 3) || ((sum6 r5 r7 r9 r3 r0 r2 < 3) || ((sum6 r6 r8 r9 r1 r2 r4 < 3) || ((sum6 r10 r7 r8 r2 r0 r4 < 3) || ((sum6 r8 r7 r10 r0 r1 r2 < 3) || (false))))))))))
  | masks => C12_rankPool.any (fastEntry (compactGoal 5 8) 4 C12_coords masks)
def C12_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C12_patternScore (C12_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C12_rows : List Nat := [10, 18, 97, 108, 116, 3, 5, 9, 17, 6, 34, 66, 24]
def C12_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C12_rows)
def C12_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)
def C12_ori : List Nat → List Nat := literalRouteOrient C12_literalRoutes
def C12_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 5 8) (compactCover 5 8) C12_S C12_N C12_idx C12_ori
    C12_patternScr C12_patternScr s
def C12_F : Nat → Bool := certAt C12_Z C12_N 10
def C13_initial : List Nat := [0x790, 0x1073, 0x188c, 0x207c, 0x2903, 0x4225, 0x444a]

def C13_values : Nat := 0x1eebfd7efaadf1f9e233a25727fe44bbc0f6a5ed4ada07b12b593eb25d607a897481e7fdcff99ed73c8654ac8fd91f32256400c64b89f713e6225c0f98002fdedf9cbddf733ae465c4ab5ff6ab6c4657f7acff532aa3dd44aa4ef4896839ccca989528963ffc7da8f6b1e42365466f8c95189630045ca8a95132a20042a584eb099e11ac22784490886100c200804300060003ffc7fe6ffc1fcfbf9c7f20ebf1d4639ff73f8e63dcc639837300e5cdc91b9037200e3fdc7e38f07158e271c46388070f8e1cdc3838006ffedff1bf9b79061f8c20183fb07c60e6c1c180830005ffebff17c9af905e06ae0d581a98352fea5f1491a90051f8a24143e282450009ff13f827b44f389e4133e237c46488bf113e220043f886310be2170420083f104020704048804100620003ffe7e70fc81a8c331863fcc7e18ad31586270c47988d310061ccc0017f32fe05e4cbc81273230645cc87990f0210041fc83b907120e0418c818902320424080809901020184010801900120003e404400803100220003f807b10f261e443000280044208401008200030002400460084010001cc038807000c600c40128023004200800098010000a000c0008000

def C13_patterns : Nat := 0x65559516455914641565158556145815591559556155655565555554554955155155255491519546151654555145445509541950551554154554555

def C13_N : Nat → Nat
  | 4 => 3
  | 5 => 46
  | 6 => 236
  | 7 => 466
  | 8 => 322
  | 9 => 28
  | 10 => 1
  | _ => 0

def C13_counts : Nat → Nat
  | 4 => 0x2001000
  | 5 => 0xf01c003000
  | 6 => 0x45092015000
  | 7 => 0x3013e063001
  | 8 => 0xa9094005
  | 9 => 0x17005
  | 10 => 1
  | _ => 0

def C13_specs : Nat → Nat
  | 4 => 0x181101000
  | 5 => 0x381501181000
  | 6 => 0x501601401000
  | 7 => 0x60168159a119
  | 8 => 0x68159a39a
  | 9 => 0x61939a
  | 10 => 281
  | _ => 0

def C13_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x1, 0x0]
  | 5 => [0x0, 0x1, 0x3004420107686d23, 0x6ad888f]
  | 6 => [0x0, 0x70302512c21, 0x20802257906786b00a00b2b60068591c202408001f04b1a905f1f10010c500300302803a03d00e00100200e004003001008006033001001, 0x64e2d8ac01105e41101a03c040741b83011060711340f]
  | 7 => [0x2, 0x1b833c0780326400c0680e8081f80040580207a5ac168010101603581685606802c15, 0x28bd4004259000801e25613c043c47227c00a06cb9d6204032028004c002174000827197400203281002b8112000872a27c00112800dc0a415907e800410400501c804009c018023005802203400080fc00509000380d002106d028002c00e0b904b80980040010098b5c09c02809a800804a01803b8048068079004000800905a, 0x290060015290e90070a400282a005014032]
  | 8 => [0x5a0, 0x4695360ad7413b1022900cc4916602c030d40132500d8031840d00bc25014004062160461500180120d04c020232bc0685c050, 0x40a00140029ad021a9aa842031c08805b002008000232e01200a01282130030164014008008807607204607e0140024010040021e02c07b001800c00600400800900cc005, 0x0]
  | 9 => [0x5a0, 0x4d480100a03907b001, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C13_records : Nat → List (List Nat)
  | 4 => [[], [0x4861], [0x2624f04c48e0], []]
  | 5 => [[], [0xfbd263a4665], [0xd6b12cd2698787743c8c561e6e42b24e38a20eb84743619381c3230b85c50384dc9e1e1714dc7663af5f5a46bee47134e1311b9218eb849c4e1e67d69230d8676470c6b8e48d86c32475c1a4eb249c161], [0x1a59a7452fe28e986ae84785bd863a6126c87582fe46290e966c685b3b1862526e261824dc49305ec6c321d2863a611b0c7582b23e190c8c51d60]]
  | 6 => [[], [0x40f5e7e6edd65b9bef47decf7d5f7ab4e792e737d5d7ae8b75fed13d60bab8f6ae3fadd9dfac373], [0x3697f3431a71de71cf58c89e28d38eac933925fe524d38f2ec4bd5afb68d7fcb231586cebcf2f93745f30e90cdb8ef5d5aefc333993de90c59c628eba692fb6713de991667aceb8f46c3636948c70c7bc58cefa321d74e1694f27058f557db48be65695fcd3a75d37dc5b2f9a748a4ae8fa49d2357f348c563865fe50c75c219a71c318716a5fcda59a5eb17db49c1615f2ce91471c635e72d64333863ae532fdd17d23946c365866ec70c6fc57cdfa5ec3339272c71049c6189b8c6c2659d34e2d261957cdba4314f18d81cbc1a69d91231d82fb66929cb2449c6ae199d84333863ae3c18cadf0eba5eafb67124e8f275d2e2199c22574753ae9bce39a462b2b21a719d4ae90c7dc676372e646e57130e970bed998d38c9c1655f39e8be75d1a48f3661d748623e5bfb65f82cd73e9d74c25fe4dabf9a18db8afa4f25423cd1b0d874a199b72fe6aa6e1faba05ece1b950c3539371ccd249964a3f2b31d74863ae8e2d39a79c07d0afd68d8acb0c7fc58ceba3ebaf45f29e966dd3a18e78c33563923de2fe75d235d72b49ee55f24e9ccead619c79452071b3b13db50d8e18938c947e3], [0x6ab931a68d8a3ac90c7449c24628d30b4a59ee4b3b1632d2714e38b4b357cb59d8921cc38a3ae1b567623a3628430e9669e95d2cd782bbd1f0d8635fceb246c31261864b3de16763145e28e8d386d61588bb3b18a2d271475c2724e2b0c6af9264e2deb31dc5bd842f497c91a69432fb2d28624637b1b14964e3e2b0c9c54161c38a3ae37ac674d362cec4b64d9d89e865f24e1571448c629b4930c9c541e1d2863d636763267af618918c93931e2b3b14b3d26c86186764dcb146b19d64daccb10f7b771456f5e4e9a7161d99ebd5f2469a59a4856fe28d18c8c51ee1b19e86277b1474d235e4eb258cf2f96938f86c3330c7bc2f635e52f16f6607936424c39967625b4b36189debf9d34]]
  | 7 => [[0x13], [0x16895525589ab021095924a906909a0961255097f256c986773896d0db832542f40821f1405726089244100fb3498892641a4966264848d0dac9b2017cb7325bc371257c82b41c485e26c00d824c505f79609a106b402d41f095f26749da0d4896426185234a44365268c130421c979261994a4b7038619d493a49d472c422896026e405327a09882730986117cd2e40a502f425c99226e0099258c9cb265096726fc05c25c035d268815f6a189], [0xb88a6ebe7bda3e2bac51f75a163aef27bd68492ee659f68d10db716e7d7c37b49c573935fece4bfda4e1b9bf9d768a71ed8f66fa28d7ad9d0de6e63cebea9db797fbc6846d8672e758acde10fbab92a673a02f8ac49d618079de9d3e8d26db8f427f4a199a99b756326eb68bfd94093ab1a4733e10f27421f2f17fb1d14fcb0247b0c21cdc98fb271275bd8a6f0cf5cd8cebb5a374fb0636f3a49d7357fb2f9274861fe7d30dcd8cdfaf46173bd636fb58ebdc593b331275de5fecdc49b70d7fbb19275b315bcc861d64d933eab1b78d79cb0c49e628c3ab19b756d24dac669d5b54f3ce9875b38aef1469cf6b333b1a4f3a463ae9049e6ecb2ead24f37323edb449b629bb3ab2473b363ed3a53d6ce2bb1211794f24ea4847f228c7ae7aff66323ed2891cd8ca7a9d127c663deb5714dd7c07b55d49f9d93e7b5159eac91ecba4f38a41e7bcc99f497dbcf4373d2cd2f56a6de362b2c7c3758a23ec8849e62a0bac6c567633aeb690dce18179af92758608e6f261d6f6ecfd9a5fe3a08f93cdd3e18579c6816d3a03f90c7bc57c0bb3f2ff6df646f42977d7d7fb4931f3b8247b5f3c7d7c0fb4312758a36eb147bd6f5e5bd50a9f632ceb1473d73093aceb9765f24ed0c05ce661b9c31ef39254e6dcb59f0893cc51d767c3deba514de35e73c513758678e767627b62cfb59927c631ced630dcd389baad1275b393fd70ccdeb18dbc32ff6793aecf253d6c678fe92fb6b5af3f3915d7698f3e66173d5546fb9433f3a86be145738d3add0c49cf4b35bb4a5e78a29eb1485cda58f3bc2ff6b08a6ec67bd619939af88767c34eb1475d62a0fae6c3736c5feca849d6198f9c7aff6b15fed3cbfd990f7abf9d757524eb147fd628dfac524f3d2636f43155f26cff5ec6af9e1a3ef275d219e3ac32ff28686e756dabd507f3bf9d74dab3ddbd0dcec169bebaff6860de76762f94493aafa5f6b0a13f43277e340f6b19cf56623ed7046fa358f3b31ff58a3ceb1469c6f21b9e1c373b3b13f3ad39db58f3c6926d, 0x17c23b319875865fe786bfdb4b3dbc534e7864be756c6dd9093abc9d754924f2fe49d5b9275e65d75ac8a6f1459d58c6fb2f8ff6df8a6f5848f674f7ac323f3863deb1475d2297fb45c373cf86e714f1d6180f9f16637bd247b0cd9cf4891ec7aa674d24eabe49f18ceba644f1f5f15edb585ae18938d8d09f7a5feda50cde29239ccaff65f47ecf249d6ea2bad8372f635fecb473d63e1b9af82f65324eb14db9ee18dbc512758a34eb987bd62a1b9e131f3], [0x634b3de9271f15864e3e2b2c69d126c8d7924cb7a7448f23628932bf9d1274793a24e999633c5f8b0e78fc9c51871e2de9e1f67633c79c98d53349b931e6bd79246b633c487628f4d38c9b925ea938a24e3147449d2f634916c9c53263938f8ac77a9a48d6358c932c6a69265bd63246b7b1448d64e28f78cea59ef4dab19e1ec67449d2c67a4cfd8cf45178a2410e3633cc65e4e289b8b9319274c38a24e32714e58ef6ec90ea69d1274b5b4b13dbce4c79a292cf7a58cf259f]]
  | 8 => [[0x17853515], [0x5f22c00074c813274e6939f4d093414eed3c04d2132445589c24c213454db83134c3d3234a993124c393a104e92304ce93294c853636d8ca464e289af4e184034c713364cb13094d1d38a7e8138d0c7d31d4c293ca4d8ce954cfd3a54f213324ce531e4d8c9864fad32c40f93b800353234e2d3434e189a84e7492462dd32482f13bd002d3154ca138a28593054d8cc9c4d8df264eac0642628e2640613174ea530c4ec53804e9d34b4c6d38a6fa93014ed13494e28c54253136d0c1131a4de495a24cd3a14f0d3784f309194f113ba4c91c104f95329417c953264d3224cf536627053b64c913da0c916444c1939e4c0933042293144c4537a4c910b34ecd2344cdd3], [0x4504778a15eeb42bde562bb918ffebd247f148fdf7a2bbc5187d938fdf993dddb093eb192758a02ef14d9dec62bbc9b96f8f24fb1449d4f40bec509f7b424fb140bded6c5fb1aa77d4cfef6897fce893eb70aef4d24eac621dcf40fe92127dc79e7ec60bdd2ca7eb925fe6302efbc49f6d22bbc9c5775310ef14f5deec93ed5883f6324fb6b69fa3e2bac501f7e2c3ff264df62993b92047d9e24fb1449f63c43ec7817d4b3dfd143fde7856fb1a5f7b5a1bf7849f62893bcf31f73d18fb3a97dd340bbbc927db0157ee449f6c679fc9927d6324ee7a21f4900fee1967d9d63ef1715dec52ffbd127dc38aeec67bd6792ffc781fdcf8aee9a11dd8c7fbb18af78f8aef7915def491ec7b1f7bc63ef6327fdb18fbdc0fbfb124fa9a49df79cb7f16f6f8a8aeec6c7de2837bd8cf1f7263ed673dfad24ffcf4577b163ef8649f62843ba688772402fa7a49f6d056fb19ef78063ef3b15de28c3bbc92757463ef8f6afe3493ecf49ff3a24f926c7de28f7ab931f7cf24fa482bf76a7b79202fd8a72ee9649f5b4437b30ff74d03ee7a11f70d8fb9200fdc7be7ec625dd8d1fbc6926dde63ef1a49bc907fe9206fdea8aef1e11f6292fbbd31f72410fb14c7de4e2b9b186f74724fb147bdf8b1dfb184773610fac607dce893f451875b463efb2c7df3d8fbbc9277], []]
  | 9 => [[0x17853515], [0xf53154c093054ed13104de93034c9104b4e2891f4ef13934c213b14f0d38a4d8c9474e793244c353], [], []]
  | 10 => [[0x13], [], [], []]
  | _ => []

def C13_S (s j : Nat) : List Nat :=
  qGroupedState C13_initial 4 15 8 C13_patterns C13_values (C13_counts s) (C13_specs s) (C13_records s) j

def C13_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C13_initial (C13_counts s) (C13_specs s) (C13_seeds s) ws

def C13_literalRoutes : List (List (Nat × Nat)) := [[(0x440,1),(0x220,2),(0x445,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x203,2),(0x1100,1)],[(0x440,1),(0x100,2),(0x400,4),(0x40,8),(0x400,4),(0x323,2),(0x1445,1)]]

def C13_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C13_rankPool : List Nat := [6577818, 2115707, 4287912, 4341369, 1067678, 4402810, 2121163, 4418727, 4349079, 4263562, 4202121, 4205464, 3239371, 5458590, 4328327, 4397991, 4218264, 3295902, 4275064, 4397959, 4205432]

def C13_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r10 r9 r14 r5 r4 r6 < 3) || ((sum6 r11 r7 r8 r4 r0 r2 < 3) || ((sum6 r8 r10 r13 r6 r1 r4 < 3) || ((sum6 r9 r7 r14 r3 r2 r4 < 3) || ((sum6 r14 r9 r10 r4 r0 r1 < 3) || ((sum6 r10 r7 r14 r2 r3 r4 < 3) || ((sum6 r11 r12 r13 r5 r0 r2 < 3) || ((sum6 r7 r10 r12 r6 r3 r4 < 3) || ((sum6 r7 r9 r12 r5 r2 r4 < 3) || ((sum6 r10 r8 r14 r0 r1 r4 < 3) || ((sum6 r9 r8 r14 r1 r0 r4 < 3) || ((sum6 r8 r9 r11 r2 r0 r4 < 3) || ((sum6 r11 r12 r13 r6 r1 r3 < 3) || ((sum6 r14 r9 r10 r4 r3 r5 < 3) || ((sum6 r7 r8 r11 r0 r2 r4 < 3) || ((sum6 r7 r10 r11 r1 r3 r4 < 3) || ((sum6 r8 r9 r13 r5 r0 r4 < 3) || ((sum6 r14 r9 r10 r4 r2 r3 < 3) || ((sum6 r8 r7 r11 r3 r1 r4 < 3) || ((sum6 r7 r8 r11 r1 r3 r4 < 3) || ((sum6 r8 r7 r11 r2 r0 r4 < 3) || (false)))))))))))))))))))))
  | masks => C13_rankPool.any (fastEntry (compactGoal 7 8) 4 C13_coords masks)
def C13_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C13_patternScore (C13_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C13_rows : List Nat := [44, 52, 74, 82, 97, 104, 112, 3, 5, 9, 17, 6, 34, 68, 24]
def C13_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C13_rows)
def C13_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def C13_ori : List Nat → List Nat := literalRouteOrient C13_literalRoutes
def C13_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 8) (compactCover 7 8) C13_S C13_N C13_idx C13_ori
    C13_patternScr C13_patternScr s
def C13_F : Nat → Bool := certAt C13_Z C13_N 11
def C14_initial : List Nat := [0x1e8, 0x252, 0x41a, 0x625, 0x914, 0x101c, 0x1883]

def C14_values : Nat := 0x1ea7e41ea0f3f99ebcf4665f329983c8e64531878a3c40607300163db12d7f2bd141ea0e506a80125290e47f23d111c84e42020b903c8003cd5a3cd145ab2c5132895449a1fb4e4a67732d1948c7e5fa2f4106082441020410088003fa1f40d4848020002000800300120080020004001

def C14_patterns : Nat := 0x0

def C14_N : Nat → Nat
  | 5 => 4
  | 6 => 27
  | 7 => 53
  | 8 => 30
  | 9 => 1
  | _ => 0

def C14_counts : Nat → Nat
  | 5 => 0x3001000
  | 6 => 0x1014006000
  | 7 => 0x10024001
  | 8 => 0x19005
  | 9 => 1
  | _ => 0

def C14_specs : Nat → Nat
  | 5 => 0x201101000
  | 6 => 0x101581401000
  | 7 => 0x481481101
  | 8 => 0x401282
  | 9 => 257
  | _ => 0

def C14_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x4, 0x0]
  | 6 => [0x0, 0x8549, 0x20062260a3dc, 0x2]
  | 7 => [0x2, 0x9303c75f626030440236, 0xd005ce1f, 0x0]
  | 8 => [0x101, 0x12150a0794846a, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C14_records : Nat → List (List Nat)
  | 5 => [[], [0x195a], [0x407e39d9792eca4a], []]
  | 6 => [[], [0x8179c1f773df4f5d6d55e], [0x6052d2129a9e0b9aec74b76be5b32969daa9d110ab76565bb5b3550eb51181b76d23bb312de1a8efdb0f68aab3d783de14b4aca5a], [0x7880c49]]
  | 7 => [[0x7f], [0x86fe15f3bbce6f4d7d5df5579e5f1dedb5f77bc87b6f7debf597ddcf777c9fb617d2df29f9d3f23ed0ef15f467e557cf6f517d3df3fbc7fb72fc97b537e23f], [0x76927bc473e0abbcfde4f563adc41cede0eb65077a7862dbc413de15b69075b423b5b01d6d595b660479], []]
  | 8 => [[0x155556555595595556], [0xff797c1ff1bfd17f2bfe2ff2dfd5df63fd1ff05fdaff31fc4ff0ffc27f1dec2ff1dfcdff41fccff11fc37f], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C14_S (s j : Nat) : List Nat :=
  qGroupedState C14_initial 4 13 7 C14_patterns C14_values (C14_counts s) (C14_specs s) (C14_records s) j

def C14_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C14_initial (C14_counts s) (C14_specs s) (C14_seeds s) ws

def C14_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x100,2),(0x400,4),(0x40,8),(0x500,4),(0x322,2),(0x4,1)]]

def C14_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
def C14_rankPool : List Nat := [3295589, 3230567, 2111611, 1063529, 3279704, 4397928, 3157079, 4401494, 3152229, 3213654]

def C14_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12] => (sum6 r5 r6 r9 r4 r2 r3 < 3) || ((sum6 r7 r6 r11 r4 r1 r3 < 3) || ((sum6 r11 r7 r8 r3 r0 r2 < 3) || ((sum6 r9 r6 r10 r3 r0 r1 < 3) || ((sum6 r8 r5 r11 r0 r2 r3 < 3) || ((sum6 r8 r6 r11 r1 r3 r4 < 3) || ((sum6 r7 r5 r12 r2 r0 r3 < 3) || ((sum6 r6 r5 r9 r2 r3 r4 < 3) || ((sum6 r5 r6 r9 r1 r0 r3 < 3) || ((sum6 r6 r5 r9 r0 r1 r3 < 3) || (false))))))))))
  | masks => C14_rankPool.any (fastEntry (compactGoal 5 8) 4 C14_coords masks)
def C14_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C14_patternScore (C14_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C14_rows : List Nat := [10, 44, 82, 97, 116, 3, 5, 9, 17, 6, 34, 24, 72]
def C14_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C14_rows)
def C14_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)
def C14_ori : List Nat → List Nat := literalRouteOrient C14_literalRoutes
def C14_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 5 8) (compactCover 5 8) C14_S C14_N C14_idx C14_ori
    C14_patternScr C14_patternScr s
def C14_F : Nat → Bool := certAt C14_Z C14_N 10
def C15_initial : List Nat := [0xf09, 0x12a6, 0x3150, 0x4432, 0x48c4, 0x80f8, 0xa007]

def C15_values : Nat := 0xf6b7f5faf577f572f1f8f150ef3fecf7e8c7e8c4e807e800e4ffe437e432e407e007e000d6fecffbccfec8fcc8f8c8c4c800c4fac4f8c432c0f8c000bff9bfafbf5fbf59bf09b5f8b550b3feb3f8b3f7b3f6b3a6b350b2ffb2a7b2a6b207b200b1ffb1f8b1f0b170b158b157b150b107b100b0f8b0a0b007b000afffaf0faf09ac07a607a507a407a400a307a207a200a1f8a108a107a100a0ffa0f8a0a7a057a037a030a027a017a00fa006a002a001a0009fff92fe92f892a6920091f890f890008ff98f098cf886f885f884f8840083f882f8820081f8810080fe80fa80f980f080c080b080a880a08070805880508038803080208010800880068002800180007f7b7df67d5079d4795078c477f675727550715069c468c464325fbf5ef65ea65ae65ac45aa659c458c456b656a65632543252a64fff4fcd4f3b4f094ec44dc44cf64cc44c324c004bc44ac449c448004632453244f244b644b24472443a4436443344304422441044024400403040224010400240003fff3f593f093d503750355033f633a6335032a631f0317231703158315631523151310030002f0921002050201020062002200120001faf1f091ea617a616a613a612f612b612ae12a712a0122212061200110010a0105010221010100610000fa90f590f390f2b0f190f0f0f0b0c00060005000430042204100408040204010400030002a0022202080206020102000150011001080101010000f000b000a800a600a200a00070005800500038003200300026002200200012001000090008000700060003000200010000

def C15_patterns : Nat := 0x255585561456555595559555955595555551551551551551551954615165456515645551494519145155419505941590558155

def C15_N : Nat → Nat
  | 4 => 1
  | 5 => 40
  | 6 => 222
  | 7 => 488
  | 8 => 406
  | 9 => 41
  | 10 => 1
  | _ => 0

def C15_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x15010003000
  | 6 => 0x5607b00d000
  | 7 => 0x30141076001
  | 8 => 0xa30ec007
  | 9 => 0x22007
  | 10 => 1
  | _ => 0

def C15_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x501601181000
  | 6 => 0x701681381000
  | 7 => 0x581681596115
  | 8 => 0x581716316
  | 9 => 0x495316
  | 10 => 277
  | _ => 0

def C15_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x4a2003017003, 0x5f8100640d00410]
  | 6 => [0x0, 0x4208742, 0xc01107b2ce88920de90e01181c801a00201a073411c00600200340f607604a800400e00800ec1ec0860510040018006004, 0x36404c004803e7b8800100dc0f00094085001400c052800100240070004003006c020815800c]
  | 7 => [0x2, 0x11878ea0344c9748de0d0260530380040e80300446167801048010208910051d80880900607401007, 0x3017220c05e01801100d00bf0e3028803c0161b8016001c20023c016803411c1bc00e800c03400185402d2126009037819400400a00081bc03401a024834c00e0020018a140f80060048078035080033000400202c00680bc08803003d808404203e000802a0dc00b82a00140060ba042804c044006801000806e065000804c02c09a, 0x3aa90812c2d1080340c40402c0100c807]
  | 8 => [0x401, 0xa03205d00019609037c1e3096c04e00040030008057001000100042760204007016004c0048001019800133ec00d000407c0038001023001a065c028002805f00ac038005004b01760820064010004c003001015400080100006011002c002003001902e0018, 0x318568100a047a0ae00404a6e86803c1a84c0600241481e0060681f80f0740a000c080020342784700500c1d0070200f80102d01400401808, 0x0]
  | 9 => [0x401, 0x1b0301cbd200a86e3e87, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C15_records : Nat → List (List Nat)
  | 4 => [[], [], [0x1007d18], []]
  | 5 => [[], [0x799d751b8b8f], [0x7c3d8cc01d869f2ec32f5601c8cc503a490991f4e63319718e7abb0cbb1c669eae338e630194fa13142dc639c6c639114087], [0x1eaec601865211021a16c02e8c8cc51ea16331471868cbb1c62a1707298676318a66217072e8576300ba61d88440c251190c06216ec718a7638d8c6232f5718c85bd5d825946025188cbd5d825eaec71988cc51d80decec3e09]]
  | 6 => [[], [0x8edb62dd854f7f5b7c5b6d9f6f1f731f6b9f3f67651f765b889f], [0x3b1c67a310c1e843fe64ea135465d92dd8c0b46724e57638cd3d5c67994413b198a4778bacdbb11165eae33b0b650f65300f328f83d3a8fd2a0426676334dc51c679e8905aca1e9b4211fa465c73a33141eec3dcb7ab8de3291075d8e374ca239d650f8ebd5d8e5eaec3af5761965260db8d4479d8df36e72f397aa88eb288c7633144ef5719c7b2e0ec15031d0881cd0b764b651ec7b28d85deaec36f4639d76398dbb1946dce7c5aec4b4b8cb8c7a88c879d8cc370b604e3d11f297895e1eae3b88f426c8cc503bb08d65d8e436f6761b652347c613aad44553690256c7635cdb8d9479d8dc370b83c7761b29bb10969944a3c7c256c32183c449d86dd8c6b2ec404b76360dc65c6b9d88d96ec1f596520079e8c38dd8d436ec255a652587bb1a06dd8e3b503761b7632cdb28a679e85e72a22e9d421fb33b1ce6d208aca6731e3761f25b28ba7544533cca2f1b8cb8c7319817194843cec23d97638cdc65943deaecb2f5651d76176cbb0a769d8ce36a22f9d65318eb28c26d2684cc8430f2], [0x7638d446a249840a35121103194496298e7630098698cc0261c85a88a63944964a877b288f835e2ed719a7abc5da65d8e3651a85c1d8d15445d299c7b3b0c0661707260785a88ba3616ec650b76288a669eaf1719c723198271e2e7301963288a671ecec461976329806a248440a685b198131d8a22e998cbd59435d8e4609a7b3b03e6616f6600e85bb18d2632f1718e7abb1946632ec650b78980956216c0260e723198071ecec601a4f269118616e4600e4c2210385eae3651c7b3218071d88133c376390ca69d8e4631985c1d8119eaec51194c2451985eaf1761985c1dd90dd8e4601a763298c6616ec720b85bd9d82e16ec604a763189866170772078cc51941e249e4d23442110392331478874c2110389ecec6319651806e65ecc6601c80bb1c86a16e4608e4f2690989f4f6761983211031944962e8d763198161228c426485c1dec1e32e3650e78a110319eca22f1978bb1c66944602a1965204ce1decec641989419021d80a22e9c]]
  | 7 => [[0x14], [0x2ac51af54a5fe92048dd077a5e857094bb261a5d88650d74966956c9473d84945c933178260c965052cf766996530c55896ca588929cd20f51248328f255497424e102f454c924488d275957c97619c45413d7295ba55a96510d90254dd2953a55693dbd5c95fa5112761dc7365247d2650194278a616f424cdb06e9570965157a95425dc97ac938f7394c713ebdbe5891632f23c9a294bbdf896349649324d789604e10966147f2314500f70155e982a4bf25da5b496e1560924c9aa9763506f63a5d8937c0f8f6c15d918995311], [0x76303d42e0f1d2284dc4a1f7c7ab28ebb18de58cc0f915651f5117ada889a7e24847cf1605e3e17b5b915c7e42ca3eb73dcf83262db61447dbe477aa24c5b78b34fbc4a779d811b6c346cf89418faf08f75e83e7af1365778986da88bb75d826b6f1635d64302f204cf9d94a23eec0a5b5125a7bd8bde616c09d14651f51148fb19817a16c6da962eed76206dbd9567e16c09eec01db65320fbb1ad6de2dc3e9629ee7b3b1d99cc3cda8a23e863fe776302dbc5013deca23ef5651f4220731787de5be6176f1255e51150fb28127de23ebab7235d72319eb39447d448d9f0836573f99f3bc5b07de28d9ee4549f65098fa2109f1d8e4b6ec515b7619edbb1576dbebc3e7a13675114cf3283e7e16b19f0b514f4999f3b1c7d75727c9ec6605d789ee7a88ba7d1a8cdaca0d1f63306ebb0136dc8ca3ee7303d65268fa10d9d944809ef65cdd65130fb281c7c941ff8ec02db76bb2da00d99de2cc3ec6515d73b0cfc4930edfaca3eec03db85b067b70f8bdd8c1b6ec635b8fbb2da35139dce1f7af5655d65050fb7d00bdd8cab6ca019f7612edbc5db6d444e3ef6761f85bb35a7911b54447bac0515e76216da888d754484bcca461f4220773d980fa24a23ef6651f4612be30c957a24f13ea2255e3e0df6b71727de241badf511f511ee7bd9d96dd81fb706425e4b2573b28967dd8c8b6ec605a3391faa78d99d0061d6ec721f899b1bb28387de4ca3f0b84cf78a62db616e7d0a61e6f12edd480fb6bc50979daca3ef1739f7631acb29027d4461b6ca039f51222ebc4b16de2cb3f19652f7626adb71447e16f19f09651f72288fb552d3e32ca1e6123f95e186da88d95dd84cb6ec653b789f27a80cf9e1707ceec305b65008fbb0cb6dd837b65e25f97b298f99c5f9de2ca3e602a79489b33b9d18f5e288bb0b764f8cbc67bc52d3db85e7706445d3012be4493cbde2df3ef123dd81a88fc2d81b9c6ca3cec015b65328fbb1196d4453bd07605e459b3aa88a6f9acca3e9e426e76328db28227de246bad0511f65004fb195d75445d7af171de7b1f36bd594f5326ce6e7511f6c1ed7bb01d6de2ecb6ca1b9f76302f329827d94673ee3651f7606adb014d79e256b6ec723b, 0x98447976328fb8d94f9ce4a7cec065b650f0f9ecf19e32ca9ea22e9d5113cfae4bd6dc8ab3efa765b80bb2db55947e17079e98427a409b33b198171ce8d5f07765b7895edc4910f612c0bd04651f65030fb608cf50047db09765b8f262db290a7dd8c6baf6761b7abc6eb28ca7cf646daec721b76006daf1013dfe61b6a2299f6a94ef455d96d3091d6f12f5b3e1e73c2dd92d0a47ea8413766a976ec2dc8bde23db6ca029f763b2d9f097b5447c9eca301f7e17ada3495b8bc37f2a21f5d2e94fe211039dc6cabca2261f], [0x7b321447616c6514d85bb1452d448133c74c204cf8de2ec651b723014479eaf1651d4f268cf8e16c0514e7b2891875088133e685c1d451d8ca2261d7b3014479108133e572288ca7a32f1650f85b91443d4453261e78b8d9479445d261d85bd9443dd8c0515a89204ce9dd8a2261b85a88983cca6025f876391446dc8c6511d76329446d228c33e57b2883e75e2ed651b83204cf1dd8c65159602889879ecf1769b7b3b1446de2ed721b51258983dc8c1511e789806f65eca2301d78a04cf1d8cc0515c432150399ecc6511d]]
  | 8 => [[0x62d7ad33c], [0x67d05143e3c6d46c51c942bd178929cc47442d143478b0ed44449bf43cd1b94516dd890dd07546f9527435d18d414d08f44c45cf4512643423520f490514b43dbd8d222514c90fd10945e518745ad015427502b41ed15343c51b852650574512d41481516941ad20d476d20c904d0a5416d06348915ce5761809401d1ad42dd144c1851a9487d00d439518143a504349151e34465181317d0bd4685209465255d44dd07d41bd1ab478b900f5cd0674655073406d04146515a541dd01142b523748b5149453502545ba59d426d0e7438d11af335144a2ed22140a512cf34502748e509f42a5213413d225472d049451d0174015087460d0ff48ad1e2b7645aa929d02d4165039430d01944a521d440d02142f450f46452074650033413508d222d1f7478ed529155186930c5ed464d172912d0d34254c6545bd1b0500d1e291a50a3407d02f4424dd943551a740c51ef455a4b340750cb444d1e540ed071402d15744ad11142550b9423c95c933d05d459d023430507d225d03d45150eb485bde2a0d50ef41150b544d513142ec9fb45138a14365079403d08542c50d90], [0x39183fa12f1bef1465f78b22fb9c6efe2ae47e4b0ffd86c26fbc4cf7d3465f6f676bf6328bebc4297d440cbe9133ef4612febb5c8fd8ca2baf101df78bb6f9844dede2ca3ec31bdf8d27b79783fecc037faf176db7881efa88c17cba4cfac1515f78832fa60cfede21cbea233df3012fea881d7e12a2be86367778a8afc85e37dd8a2be96266f823c6fa88997c6e1ffabc135f84b06fa88037dc8a23e7b0d6f510def9286ff990c1bea2515f85a8b7a7923bdaa4cbe6713777b07fea88357deca27ef10fdf51131fa450dbd80a2fca242df793c6fadc357daca2bf1554df460dfebc46f7d228cfadf133f76a8afa89357cf81fdef678df2306be9947df5e281bef132df4f21b7a880f7cca4bfc8433fe4419fea190bf90267def1265f468df7bd9447db81f7ef6647d7628bdbc4797de2edf6f6467d78846fc6a1bbd4403bea232df7b28afb6034fde20ebee4515f6028af11c4df5444bbf0633df7b2bafbc5957dc8a27ea2261f7628ada89197de21abee432fe78826fbc50b7d0267cea204df7ebc6fa880b7de2c1bef125df4f19f7a88057de260be8513775109afbc5c97de2f1bf1578df51052fc48cefde29abef6307d7229afbc40b7ddaabbf07515f85a8a7bc5ad7d8ca2bec8515f5c87efa1903bdece47e9e4d7b78b29fc6a2afde202bea20fdf29933f2004dbd80a2bea240df32983dc55457de226bea208df], []]
  | 9 => [[0x62d7ad33c], [0x1bd14494d50cb4265145404d1ad401522b40a50974725183406510b402d103433d0c1408d191407521340fd1ed44651e2901d1e340d500f41351db4], [], []]
  | 10 => [[0x14], [], [], []]
  | _ => []

def C15_S (s j : Nat) : List Nat :=
  qGroupedState C15_initial 4 16 9 C15_patterns C15_values (C15_counts s) (C15_specs s) (C15_records s) j

def C15_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C15_initial (C15_counts s) (C15_specs s) (C15_seeds s) ws

def C15_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x32,2),(0x404,1)]]

def C15_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C15_rankPool : List Nat := [2165678, 6519960, 1068169, 4284365, 2104987, 6622620, 4419210, 1060538, 4210573, 6455245, 7367817, 6311563, 4201624, 4340654, 7556265, 7616908, 4414616]

def C15_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r14 r10 r11 r0 r1 r2 < 3) || ((sum6 r8 r9 r12 r7 r3 r6 < 3) || ((sum6 r9 r8 r12 r4 r0 r1 < 3) || ((sum6 r13 r12 r15 r5 r1 r4 < 3) || ((sum6 r11 r9 r14 r1 r0 r2 < 3) || ((sum6 r12 r9 r13 r0 r5 r6 < 3) || ((sum6 r10 r8 r14 r6 r3 r4 < 3) || ((sum6 r10 r11 r14 r2 r0 r1 < 3) || ((sum6 r13 r8 r15 r3 r0 r4 < 3) || ((sum6 r13 r12 r15 r7 r2 r6 < 3) || ((sum6 r9 r8 r12 r6 r0 r7 < 3) || ((sum6 r11 r8 r14 r4 r0 r6 < 3) || ((sum6 r8 r9 r12 r1 r0 r4 < 3) || ((sum6 r14 r10 r11 r3 r2 r4 < 3) || ((sum6 r9 r10 r12 r4 r3 r7 < 3) || ((sum6 r12 r8 r9 r3 r4 r7 < 3) || ((sum6 r8 r9 r12 r5 r3 r4 < 3) || (false)))))))))))))))))
  | masks => C15_rankPool.any (fastEntry (compactGoal 8 8) 4 C15_coords masks)
def C15_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C15_patternScore (C15_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C15_rows : List Nat := [33, 44, 52, 65, 74, 76, 82, 84, 3, 5, 9, 17, 6, 34, 24, 96]
def C15_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C15_rows)
def C15_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)
def C15_ori : List Nat → List Nat := literalRouteOrient C15_literalRoutes
def C15_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 8) (compactCover 8 8) C15_S C15_N C15_idx C15_ori
    C15_patternScr C15_patternScr s
def C15_F : Nat → Bool := certAt C15_Z C15_N 11
def C16_initial : List Nat := [0x235, 0x3ca, 0x4a4, 0xc51, 0x1105, 0x2806, 0x3038]

def C16_values : Nat := 0xf1e7907e0fb838e01b4bcd0e33fac8f7238c4f7138c4170b8c1e3000b29ac57b146c06af3aa37a81a906a21a846a0024a48f2a2358001f757555c5164157b5569550552913cf4f293854d153354c15235461514544010003f6cf513bd4ed139d4e513544cf53344ca42f28a3520007ee1f287a41b906b51a9063516904e412004000ffc3350c002b50a002750900230089021108142040800100020004000c00240080011004000800140040008001

def C16_patterns : Nat := 0x0

def C16_N : Nat → Nat
  | 6 => 24
  | 7 => 78
  | 8 => 51
  | 9 => 1
  | _ => 0

def C16_counts : Nat → Nat
  | 6 => 0xf009000
  | 7 => 0xc041001
  | 8 => 0x2b008
  | 9 => 1
  | _ => 0

def C16_specs : Nat → Nat
  | 6 => 0x701401000
  | 7 => 0x401601101
  | 8 => 0x681382
  | 9 => 257
  | _ => 0

def C16_seeds : Nat → List Nat
  | 6 => [0x0, 0x24504, 0x49900810004006]
  | 7 => [0x2, 0x6420010010670273fd03f00a01801b03000a00183d05d010004, 0x430207]
  | 8 => [0x2bc, 0x270814400e02c805800c001803801c04c011, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C16_records : Nat → List (List Nat)
  | 6 => [[], [0x107a45e9dee47e9d6e5fd98f671b96f6], [0x2d41ca7389d3905aaae57385b9a72dad81cce4887c5b70badce3d6d6b6b681d3c73b28a1b4e106a]]
  | 7 => [[0x7f], [0x15777fbc97e4ff887ea5dd4fb61f947dbcfd07a5df927d73fabbfc17e55faafeb3f83fa47d59dd6fe7dec7fe71bcb7e93ee5df85bdc7e3ffa1f72bf8efb8bf8a7e33f96f743fa65f6ff907b2ff96f69b7daef23f9e7db2fe75f31fb0bf8ff907eb6fe8df69bdc6e39eec6f1df9b6f3dec9fe], [0x72cf73d73bb1b9dc8077ab639f381db92a1f5510fa64bbb4e1d7968eec84dfa]]
  | 8 => [[0x6555559595655555555955595556], [0x5ff0bfd2ff07fe9ff67ff1ff5dfeeff65fe37f57fc17fc5fee7f03fc37f43ff27f13fe07f1bfe7ffa9fcdff73fc47fbffed7f19fcd7f5df9cfe09fd37f0ffd0fe1dfc57f7bfc77e89fe87f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C16_S (s j : Nat) : List Nat :=
  qGroupedState C16_initial 3 14 7 C16_patterns C16_values (C16_counts s) (C16_specs s) (C16_records s) j

def C16_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C16_initial (C16_counts s) (C16_specs s) (C16_seeds s) ws

def C16_literalRoutes : List (List (Nat × Nat)) := []

def C16_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13]
def C16_rankPool : List Nat := [5376940, 4413814, 3284107, 5458279, 5511017]

def C16_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12] => (sum6 r12 r10 r11 r0 r2 r5 < 3) || ((sum6 r6 r7 r9 r5 r3 r4 < 3) || ((sum6 r11 r8 r12 r1 r2 r3 < 3) || ((sum6 r7 r6 r9 r4 r3 r5 < 3) || ((sum6 r9 r6 r7 r1 r4 r5 < 3) || (false)))))
  | masks => C16_rankPool.any (fastEntry (compactGoal 6 8) 4 C16_coords masks)
def C16_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C16_patternScore (C16_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C16_rows : List Nat := [26, 33, 60, 65, 82, 84, 3, 5, 9, 17, 6, 34, 72, 96]
def C16_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C16_rows)
def C16_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C16_ori : List Nat → List Nat := literalRouteOrient C16_literalRoutes
def C16_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 6 8) (compactCover 6 8) C16_S C16_N C16_idx C16_ori
    C16_patternScr C16_patternScr s
def C16_F : Nat → Bool := certAt C16_Z C16_N 10
def C17_initial : List Nat := [0x8db, 0xf24, 0x1149, 0x1292, 0x6403, 0xa01c, 0xc0e0]

def C17_values : Nat := 0xf55ff1fdeffcef3fef24ecdfecdbec1fec03e8ffe4ffe4e3e4e0e41fe41ce403e400e0fce0e0e01ce000d2f2d2e0d292d1e9d1e0d149d0e0cfe4cf24cce0cae0c9e0c8fbc8e0c8dbc800c5e0c4e0c3e0c2e0c1e0c000bf7dba9eb9dfb3dfb29eb292b21cb15db01cafffaf3caf24ac1ca91ca8dfa8dba81ca41ca11ca0dca05da05ca03ca01fa01da018a008a004a0009adb9a9299db929291498f2488db880080188008800480007fdb7f6f7f037edb7e937e037ddb7d4b7cdb7c0377db770376937603754b7503740372926fff6f276f246f036e036ddb6d036cdb6c4b6c1b6c0368db670366036503644b641b640b6407640060003adb3a9239db3692329231492f242cdb2c1828db280024002018200820042003200120001fff1fb61f921f6d1f491f241f001edb1e921ddb1d491bdb1b921b491b001adb1a921a0019db19921959194b194918db180017921692154913db1392134913001296120011db1159114d114b11081101110010491008100110000fff0f6d0f3c0f2c0f270f250f000ddb0d000cdb0c490c000bdb0b0009db09180903090008df08d80859084b0849081b0818080808040803080108000500040404030401040003000149010801040101010000db00d80059004b004900480024001c001b0018000c000900080004000300010000

def C17_patterns : Nat := 0x6555954645185459556545851565559155955615565555554554554554915185455514519145851554544554555

def C17_N : Nat → Nat
  | 4 => 3
  | 5 => 30
  | 6 => 167
  | 7 => 412
  | 8 => 337
  | 9 => 33
  | 10 => 1
  | _ => 0

def C17_counts : Nat → Nat
  | 4 => 0x2001000
  | 5 => 0xc010002000
  | 6 => 0x34063010000
  | 7 => 0x2310d06b001
  | 8 => 0x9c0af006
  | 9 => 0x1b006
  | 10 => 1
  | _ => 0

def C17_specs : Nat → Nat
  | 4 => 0x181101000
  | 5 => 0x481401181000
  | 6 => 0x701601481000
  | 7 => 0x781581596115
  | 8 => 0x601616216
  | 9 => 0x515216
  | 10 => 277
  | _ => 0

def C17_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x1, 0x0]
  | 5 => [0x0, 0x2, 0x1879020a, 0x23c2403]
  | 6 => [0x0, 0x578940802, 0x67105b00307802c03a1af01216e02800105f00800900981f00100300100b03e00100d001001, 0x1f788c0050a2800b0290002000801002e80030004145]
  | 7 => [0x2, 0xe52a8030a000c1987682b1ac05c6b4c61e8018492ac008460190080040301801239403409, 0x2a049ac4f9002084a813e004ff45c85b2b73e0438a009003466009420cfe6d4cc0581401080195f20c0e4800cf198110080645200302c0740101d86a0160040082e004030008270020040084300200c00b93858018030020080b44a00a, 0x2608000200600ed013c00180044004800c]
  | 8 => [0x31, 0x46200a08b0bb00908589b0020013182670020020280080620060cf18d00200a14087903c0091320e90060770050c500b8af00900a00400883a05200802b01d011002, 0x60e40038788540e900c02f2138520ed00e5fc00478300501989c00110982800615c82201326506900126003d89c07900300209f00b36a05d194, 0x0]
  | 9 => [0x31, 0x20b4f0f10083b00411, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C17_records : Nat → List (List Nat)
  | 4 => [[], [0x30f0], [0x2798b078770c], []]
  | 5 => [[], [0x3907acf2], [0x625ce1d9c63a818b81d9a706259e114c592558b0b12d706663e1c10e3a6d8b277700e8b3bc5e1ca3628ff1231970], [0x84624bc102c4ab824d8957072f1ab8690625cc1b382b84a86321c66543b98cd9625c61bd26aa8b66417116f61aa92]]
  | 6 => [[], [0xecdd17bb41f32f634f911b9239f01f57ecadd96fb2ff684dcf1da5f755f6], [0x1bbaed588a7c312bf4d7d179cae737395db6cc22e624be3caaf9970ff9312e74a17b1ee6afd13d2f9442de64629e594dc3d89738c2316c6258e952a3cb597db3219785c3be4c491c55d279231672e3a53cbebbca04ff1f2f00f844dcd14cd9b2d5db6a2db6573fe4c4b9c95d3396a442e844acd4eafd2598b8c51de6ad57ad02af99996b950c61d8c87d9bd269e117f31d96f2d9576dad08ba4d8b2e7422e5751e5cbaeb7cb947c11de3e5e11f5b0938ecbb9482be6ddda6753099b315db452be6843fd4eaa3ca11cf6695c9e6256e8c459e189278eb5e9e8057cd4f09b16cff96aabb6cb845d02c59729ccef4f30fa03be5a4aedb52f0f6f6197d2845cb07fc989738712bb65b51e5c508ba74ff9422be68475cd3ac5d168ef972f18f], [0x81553bc5b2c4b0d3978c747312825f0e5d8bf1bc753504d89615786ce0ac16e3a9a72ba508ae9a4170ef172f1d48762583fe1a573083b67052c9ecc82c26d2b9572db6b07ec98970ef87772f18ed8bfa639d3c30e3a861de87692ba8b2d95c3b64c4aa97c189604b872f1d38d625c4be1c74f4c732a1da0773c3b9cc845751c5cbc70e3a41896326cb125b1946255e1c743083b8e855cb4a49316187624be0c4b8abc24560ff16cc825a3e5e3a61d20c4978762fea4ab1258ef0e5e3551db329248e112cef133322e70]]
  | 7 => [[0xd], [0x312e95852c8412ab13d8a6c881ad9f34118b306423244708357bd49c8585ac1e63d8d79930c821ea00998ea75163bb10559c0901ccb2159b2086669017ceec7ad0e7808d8b4c2462a30b9912c6f619b36c109671653ac899ca33265707580a0c2f65f2e21954ca6674009d8b8c574ad9a108ae82b62bcd38e54caf0b93388140ccb0251e204ae64050fb21d906c80192b2e9858c4d3c79fb98e0cb0098b210abe69a639acfd58871d62eb15cea4c], [0xe2707d98aafb3935bd6c3de5701ed7d5b76eab6f1f8efa571ded52b1dae55fb6743be7558ecc8afd954fbd2c1df6cb2c7db30efbb613750abf6e3a13eb8afd95d479b10979bf84dd28c5d55c63b2894fad2576f10abba1213743bd6e5105f594d07f969f6c2346e5112f502abbb62b4fc09de7e9e13eea3bd98137b73b74f9d66ed00959e100f765c3beeee5dcaa9bda00b3743b9fc5c3be5534fd685ceef3abf6621df9203bb9712bb28927ace557dc4e6f73875f43a576624be7530fdac21ef2c26f6cbb73eae09da50ff9c3b17cd2517cb0afdaa557b3ab876a7a6f908af9b50a5f65aabe7975ecaa7feb9dceeecaabea9a6edcbc67d70fbd6c54b7d2845f76afda58ef9f0d09f7370f908abba100773ab9f59d3bec967fcd892f8b2167ad9946f0f01bb58bdf568ede842fdcaeafdb8e137489feba91dec762fce0077772d4e73b29f54e3bf2515fb2e1df6574beda4aafb6589ea30973b984dcb6abdb12b6bc414eeaca9ecc4b1d2415772b81768402ddc50efb4a1df42096e4d1decaeabd95c0fb398efc5b29eda508b960ffb2ba8f28d87ddcbc63f96b67f2ec2f8464dd84afd95c17b332bf64d31ec9459da10eb7332c76583ff50ebfdaa6a39c21dee4b3be7a5727f5a1df402aee9257ecb095db95a27ab86f66255f92509b960ff9f1abf65751ecae25db66417cc486ecb4a6e943bdb8955f420feee5e35fa8aafb8eb4fe95dbec557ed9d707d28ff9dc915e8166cfa43afa4143765c02f8451dda508f954f7d713ab78784dcc4b1dafd5fb2f97f66857ecc4b1d66613748316d6250f8aa95db969b7658ebed91d7d210fb91893b2b9df6d2b97d0ef9b970ef9aa9e7ae784dd4f0ff2115f3f9509fce317d0897ba1d37b2c23f6583fe51b09bb495db439ffac857edb14cf95c23b332e763b2cf4a21beb8875f72aaee8404ddc55a7f961f7420c6e623ff3b67eee1d5fb2b9d767355f94eabf1d557b43baf6e51ddd1aafda6a37761426e8980dd08afd9440bd4206eed9507cc853ea101776ce09f, 0x249df3ad55bccc93cd35339c20eee8408dd38afdaee1373aba73624beb4309ba85e8fe95c9e], [0x10e9677c9412cef96ca59db3d8bfa13ba5083ab999912f8f4f3f18f624b3be2aea23bc98960efa73c3b44ee3a1873cb0aa77ca115c77371d08e9e90583bcd2924778efe361f62e2a9df266583fe5c753425e5154ef9695c8e9ee3a1553c96763bc9552cef9692b8eb6d9583b6cb07625cb8e9e84eb3322c745c4b3be5cbc7423f8e9a84f48259de3]]
  | 8 => [[0x2b06cb2e], [0x9379da3b4086a83235a2ed456dfb601b527c06cd347585ed116c3e1f9a08d186c00f1da2ad31643c4e1aced55a4fb4f5b5a1066e58081a34d0968e3685a48df36bfb4e5b8cd841423511a78d036c233a9b0f4296ab986db0ec966f0b429ae0d5567a347dbc6d626d3adf1bca34d3f8b64070ef4b68fb0fd462d696a1b689a44c36686b4e9ad4dbb6b83075e0ada3687b6d5a50d3f6dc355702cd026f7b5cd684dce00ec562320d3e68eb6a1bcad516f937480a2cc16dbb5563c40646923249b4ed1dc2b9db5aaad496bd3709aaaf4a380b4ddae6d5c605b441a0ed3b6d330b19b2029617b3adad8d146c3b725adcdad689b431aa0da46873699b083b46dcb6cda32d6b6beb6c5b34c3569136d9ae8db26ae35d4e58d8e6b43589698d], [0x1d04fd083bfb7361ff4d6dfbb87fca077fb7f71f8e8c7ec755fdce3bfa1c37f4943fe1d08fd1b0fb97157f320efed8d37f7e3bf954eff43b6fe6658ecaa75f9712ff43827e6658eeaa25faed57f46c3febf22fcaa05fa85a2fd0aafe874bfd9624fd604bf3ab4776655fdcf0ffa6a4bf1d897b5508fd5343df4875f69ddfe6455fdced17d284bba59df35529fcaa3bfa1077732127e8702fd2925be519bbc3847eef87fd0ed1fa004b7f1d09fa11dfcb077df4875f8e8efe511dfc743bfb8d57f5350febf8dfb1b0fbd3463bac1df6c287fd9c30fe3a1ff0e82fe6412f7b142fefe1ff4381fe9a55fd430ffaec77f2a86fe8d1ffcd03bf9600bf71d0bf6755fd0ec9fb1557f2a827e903bdeccc9f7a761fca2afe8755fc3a25fafd57f718efe5805fd350ffa3557f0e80fe5855fd251bbe4957f62ca778705fcd0abf92cefbc20eefa7a1fbc70ff9c1a3f2c1f7ee5a1df0f0ff96037f74f3ef1d02fccc97df64edfaaaafe873afcae3bdb9d57f6fe2f7623bfaaa0bf9552ff71343fc255fc963bfa1c63f610efe8d1dfd0e25fa1c77f490efed8bffacc7fee1ceff2b8ef73b1dfc5825fa1cbff2a8c7ee9e37ee6d1f6e477f2a81fe943bee3a07f8c463f0e86fe], []]
  | 9 => [[0x2b06cb2e], [0xeb1a1a06d086d0b78da24d3a6a5b79db24d3b6e1361da3ad646823461b76d056aab435b7ed8762ab009b1ad], [], []]
  | 10 => [[0xd], [], [], []]
  | _ => []

def C17_S (s j : Nat) : List Nat :=
  qGroupedState C17_initial 4 16 8 C17_patterns C17_values (C17_counts s) (C17_specs s) (C17_records s) j

def C17_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C17_initial (C17_counts s) (C17_specs s) (C17_seeds s) ws

def C17_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4115,1)]]

def C17_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C17_rankPool : List Nat := [6491871, 6651032, 2112954, 7547276, 7695545, 5255086, 5271178, 2195437, 4340873, 2182554, 7426014, 2187181, 5340826, 3296408, 5250216]

def C17_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r15 r13 r14 r0 r3 r6 < 3) || ((sum6 r8 r9 r12 r7 r5 r6 < 3) || ((sum6 r10 r11 r13 r3 r0 r2 < 3) || ((sum6 r12 r8 r9 r2 r3 r7 < 3) || ((sum6 r9 r11 r12 r6 r5 r7 < 3) || ((sum6 r14 r10 r15 r2 r0 r5 < 3) || ((sum6 r10 r8 r14 r6 r0 r5 < 3) || ((sum6 r13 r14 r15 r7 r1 r2 < 3) || ((sum6 r9 r8 r12 r3 r2 r4 < 3) || ((sum6 r10 r9 r13 r4 r1 r2 < 3) || ((sum6 r14 r13 r15 r4 r1 r7 < 3) || ((sum6 r13 r10 r15 r5 r1 r2 < 3) || ((sum6 r10 r9 r14 r7 r1 r5 < 3) || ((sum6 r8 r9 r12 r4 r2 r3 < 3) || ((sum6 r8 r10 r12 r1 r0 r5 < 3) || (false)))))))))))))))
  | masks => C17_rankPool.any (fastEntry (compactGoal 8 8) 4 C17_coords masks)
def C17_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C17_patternScore (C17_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C17_rows : List Nat := [26, 28, 33, 50, 52, 65, 82, 84, 3, 5, 9, 17, 6, 40, 72, 96]
def C17_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C17_rows)
def C17_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C17_ori : List Nat → List Nat := literalRouteOrient C17_literalRoutes
def C17_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 8) (compactCover 8 8) C17_S C17_N C17_idx C17_ori
    C17_patternScr C17_patternScr s
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

def C18_counts : Nat → Nat
  | 5 => 0x1002001000
  | 6 => 0xb01d003000
  | 7 => 0x705602c001
  | 8 => 0x3207d005
  | 9 => 0x14005
  | 10 => 1
  | _ => 0

def C18_specs : Nat → Nat
  | 5 => 0x101181101000
  | 6 => 0x501401181000
  | 7 => 0x201601591111
  | 8 => 0x691591212
  | 9 => 0x591212
  | 10 => 273
  | _ => 0

def C18_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x1, 0x2]
  | 6 => [0x0, 0x1, 0x8b21275703030336, 0x250c06]
  | 7 => [0x2, 0x249058a80386e00800181a00802943, 0x4c90100f70031b200202d0450c203a00701a0af08300601e83e00406381780c003, 0x44]
  | 8 => [0x13, 0x4f1343c8031382cd7483f01e054cd90606c00826c190f40bc0200600b1f4038018fa4c80480206e14804410, 0x95c00940a800e0010020dcc00401f24f0380002060, 0x0]
  | 9 => [0x13, 0x10070385b2ce, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C18_records : Nat → List (List Nat)
  | 5 => [[], [0x528f], [0x279983b11a68], [0x45332486]]
  | 6 => [[], [0x13c7e3d79679], [0x4524275134f1147e5d952735018b35424d2685be240fe3ce2fab9f488f372aea9d825aa1a6a9b987344ca9d7cd351a17f89c84374d403cd0b3c302ee9a7911f4cff3a412672a90e995905d149279816353818d3], [0x150cc93196cd0bf44bb0af29975b2f532f045e665a01bcd45331c07615e34d12d21003a5cd0bdc51cfb307]]
  | 7 => [[0x8], [0x413315a627215c25523355626f54c52566d72468b03f39903477f7266711a004974f5970423403572930642a207018e06529022e58d05325b29108c0325940855731], [0xd8b7cc83e675121f2bcb1ba8125f4836ee7f70bcf6636e096e7c5332f653fcf402ade8e7cf9a17f95b4dcededbe958e33d3384f90809ea843acb893cd0381f6f6ef26261e629797c5a9af6658dc927fda8cc79c837eb9f5e9f2e68faa126f2e126d5024f2a069ea15c2dc1285b6449dd14707da526f4b37bba0645f2114bea0febcc923d693fae5a43e56cd374fb34f5347cf1af67d3127d4698bb97823e6849f0d0bfc2625f92f21f320713e35597d11fb796703e5e49e65a417958879342ff4ac63ad3cff9aa1b6b532ed6f6ad3c8453c9a087ca848ce7063cea2457d0263b975b5f16f47d91335bd29cf7015aef67f5e2cb9daf2d6b], [0x12e5e42e6a198e23ad9790e9342f21f0c2bc43a65a01a4f1b1a97f8]]
  | 8 => [[0x9cba8], [0x7e83a81386d71087682d8518701198218a382782f80589108384b81d86982463f36b80b80286685b2a480e8638ab8898ad88786e82383471a8758688228a008880682888b00481c87483882080886f56c84d8448128ac82e53781e85628d01488283984581b87881786a80783e86787980c8778a985282987a88084783b84a84984970180a82a8a187c87d83d81683084383c88184c51187b86d83f81884889f89706420985329024e81f83151587084683480f8358038aa80d8248], [0x38153a838190692a85e250365561526638353102363574e3836f69536246a3153a892297210665925021596690351065b2126d6972f21496920a8662803f38b100a3a103115596807615e22f215362f5a370169381493874c3855e592a3960643829d865a03809a9609d9a0211063421786505804a77b1512e1058d150], []]
  | 9 => [[0x9cba8], [0x38158358108698838a187d80680484a88080586683882f84e8098a38218], [], []]
  | 10 => [[0x8], [], [], []]
  | _ => []

def C18_S (s j : Nat) : List Nat :=
  qGroupedState C18_initial 4 16 8 C18_patterns C18_values (C18_counts s) (C18_specs s) (C18_records s) j

def C18_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C18_initial (C18_counts s) (C18_specs s) (C18_seeds s) ws

def C18_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4454,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4515,1)]]

def C18_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C18_rankPool : List Nat := [3296408, 6491871, 7695529, 2195115, 7756172, 5320638, 5520569, 4284333, 6438282, 6454424, 2125451, 7687610]

def C18_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r8 r9 r12 r4 r2 r3 < 3) || ((sum6 r15 r13 r14 r0 r3 r6 < 3) || ((sum6 r9 r10 r12 r6 r5 r7 < 3) || ((sum6 r11 r10 r14 r7 r1 r2 < 3) || ((sum6 r12 r8 r9 r5 r6 r7 < 3) || ((sum6 r14 r11 r15 r2 r1 r5 < 3) || ((sum6 r9 r11 r12 r3 r4 r5 < 3) || ((sum6 r13 r10 r15 r5 r1 r4 < 3) || ((sum6 r10 r8 r13 r3 r2 r6 < 3) || ((sum6 r8 r9 r12 r7 r2 r6 < 3) || ((sum6 r11 r8 r14 r6 r0 r2 < 3) || ((sum6 r10 r11 r13 r4 r5 r7 < 3) || (false))))))))))))
  | masks => C18_rankPool.any (fastEntry (compactGoal 8 8) 4 C18_coords masks)
def C18_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C18_patternScore (C18_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C18_rows : List Nat := [26, 28, 33, 50, 52, 65, 74, 76, 3, 5, 9, 17, 6, 40, 80, 96]
def C18_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C18_rows)
def C18_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C18_ori : List Nat → List Nat := literalRouteOrient C18_literalRoutes
def C18_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 8) (compactCover 8 8) C18_S C18_N C18_idx C18_ori
    C18_patternScr C18_patternScr s
def C18_F : Nat → Bool := certAt C18_Z C18_N 11
def C19_initial : List Nat := [0x3a4, 0xcc2, 0x106e, 0x1511, 0x220b, 0x480d, 0x6070]

def C19_values : Nat := 0x3f8ffcf2f4dfdfd7bbdf57feae3d5c3a88f470e7fdc9ff8b8707ee0e1c1bb8006ff6d9e5b30b5feebafd4ffa83f506ea00d0fba1c3406e800cae191c31ffe3f4c7498dc3178627bc4e1882f0f86170c1e181eb03ce072c0e381830106010c0017476e88dd0db9dd733ee615c0db7df6436c37d86eb01b6002a88d06e9a1b333e6614c8d981b2eb65d24b0d951b28364c6c90d911b20020003fdb7ddefb2de773cc26f7eddfdb8db7116c16d4459f7b3ee6616c9bd937320b60dcc0017f7aecb5d84b309505a60b475e8e91185a28b44d6892d117a22b4436883d105220944048805100206040808081008200a40128009000a0003fee7fb8ff31eee3d8477b8ee99dc23b227444e771cc238186fb8bff97ee2f6a5e90bc897112b2255fcab8956e2a6a54c4a8d95192a265400a0013ee27cc4f909d713ac27484db898512ee24dc48008f711c222dc4580886110021dc420083f106f20d441988311060208440b8816102420404040807100a2010400880090001fcc3f087610dc219a4330c5d207a40a000f981f203b4075c0eb41d603a6074a0e0018002800448088010502090408080810082000300049009001100208040408000a401400208040007000d401980310060006000b8016002400400044008000e001600280048008000600080008000

def C19_patterns : Nat := 0x2555951654165159415955645590559556155815595556555555455455465515542550551554154554554555

def C19_N : Nat → Nat
  | 5 => 4
  | 6 => 92
  | 7 => 337
  | 8 => 330
  | 9 => 34
  | 10 => 1
  | _ => 0

def C19_counts : Nat → Nat
  | 5 => 0x3001000
  | 6 => 0xc047009000
  | 7 => 0xb0df066001
  | 8 => 0x8a0ba006
  | 9 => 0x1c006
  | 10 => 1
  | _ => 0

def C19_specs : Nat → Nat
  | 5 => 0x181101000
  | 6 => 0x381701281000
  | 7 => 0x481601596115
  | 8 => 0x681716296
  | 9 => 0x515296
  | 10 => 277
  | _ => 0

def C19_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x3, 0x0]
  | 6 => [0x0, 0x603, 0x5114193002caaf001c005009c08e0200068002c001003c34a0060015004c008, 0x121d9a]
  | 7 => [0x2, 0x3083c15a058230ff06a75a258bd47c5cc0286d0040101680c0340045301c0070640a802, 0x84b00280420020032d91be06100300a5aa0060340028d006506703e0090412200058c700100705d03a00500f00101f00901005e8b20028af08f8a902e0020f406e00289a00f01307c02211704100b035849113, 0x4282682]
  | 8 => [0x28c, 0x99067601582e86e6000810700bdb9400d051d0040004073844c02700020234019068000201c0045007002600040040004001014004a016a0ba0154001001c0020098026000816a0024007001c00382e8005, 0x1502c600207b005403600f01c00450fa0150f900d000a00401a417000c001051820c04600100500080c0004059004407205200080d00fe01d, 0x0]
  | 9 => [0x28c, 0x20d0287f6c01a00896, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C19_records : Nat → List (List Nat)
  | 5 => [[], [0x748f], [0x1e4dfc1f6cd26cd3cd1], []]
  | 6 => [[], [0x3cf956f93af9729f31f33e79793b61db6579], [0x38ceae54275d2e636c75f25de29cebc5f27572c73cd94d1d74b9ceae5dee078be2e787cb24daf0a34d5075d2953ae977b98e9e4e1c4f25cf0ce62d3599d6c9d4cbc5f4f366d01d2d7a310dad0eb64ea35f0cd31d359a287a58eba4c639e2c23af13a98f8ad4eb659cbeaabc3ad9681d5cb40da9dd4dc1ee63ad93a9b78b70eae51475d2b73ad96c1d5c9e8e9c54879d2783b716c9d5cbd8f2e58875b2db3ae94c9d74af97571529ccaf43ab97b31cd9dcebc5d49c9a621cf15f2296a6cb9e19275b2cf3cf13a973c3987535f4ef6a751b78752a63becc6ccf263e2753671], [0x7a311422cf27030f0783993a35c2be5d9c7829d3a95e8c43a997a1d4b8e0fe7a3870649e8ed45e8a13aa962284eb2588752e58]]
  | 7 => [[0xb], [0x221cbc76004fe777a4c076f80c67501d1c25a051426d0096763851823f1cac75b056e17200a67511ceae1d25f443ad88271f9c729231dec05f24ae76e00eb437117816900d276c008474588c643a95e80279ce675e84da4799d38954914a71da4b672c9c9472e1dcc115a88a73a99a204da4a4768007a73c948076c811a26f00a87289cde77504ba7249cb47318ceb12a9d8813aa570136113e7389c8e7309da602c1d5c75c849875a859212f9d4e43ca4a07], [0x17043e8c23af2d0679f3a973cad0c36d8e61b6c42e5b450f759d405e5e8c436d930bb3f1d7c97007e94e9beaf450bb579d7cbd1896cea0df2811d6d73985d9d4c3e5b2397adb30eb7e1d7c98453e984beeac43af97a171d9d873e56e6daecf5f5d79b41db10eb74ea1af2b3409f6e1b5bb99553cb81af4a730f360afbcb4042bdb23d766c30f3782297a84eba57c61f2cf60db1e8ebc9e8ede5a0bb3e750579679d7cb98c36d6a54b6753af9509d7c9d47be5a03d76f424bb5a0f6d98473e57c817a3d1a737829db9d403e5686caeb51edb6e0f5daa5159dccd03ebb3af9611879b10eb65448ad69530eb521875b18ebe5883db6e653d7759b73adcc36d026dce7535f9809d7cbd4ebe53075f29a30eb3a887c98835cd5475f27b1cf93b1d7cad52d3d3a75f2b23af9471875b2cebe4ea11f2d830bb4c9875bd8a2ecea07f2e15f3d3614399fcf5e5b6beda75067959986d8f473e5eac4b6d95a9f78398fbc0ebe56850b6f4621f5a2567a28c3add48a9e813af94b187596075e4ea48f29b1ef97327679b47bccea16f2fa68372e01fd3acebe57c76f2f630bb5097359d871e4b80cf4e13af977b41eb98433db050766c1ef35e0f6da9d41cce051e6752e7c7a1d5cb4078fd6a39ba9b4bfc6e185d9e8ebe5a0707e7501f95a986dbd146edb25476a428eb3a973c1947bcde861767d1d796c1b1baf96775b0b43ee64ddd5e186db10c36cea06f2a13aed7a0f5d9d479e5388ada7930f96e2dcfafcebe4f251f2ae4df95026fca6cc3e4c661e6f43abd5526f6b607aecec3af2753179368eba9b4b1cca839f2e330bb68185db987b6dd075f2f43af94b15359701be9d6e73ea33af96e161db8d787d84bbae7730f3758eb6b99416cda61e6be5ddd6e0e9eb74ebe54261d6961ced63946dadcb16d98bef2b71d5d509075b3ca3ccc63ce6761bf9538f79af87be56e3db69b3b796228679fcc7cdb88a5e753879], [0xea5c1ef87a1d47ae588751ed9679e8edc4f47631713d1c079d142751ee97827502b5e8c41e9b622847b2cf4763871]]
  | 8 => [[0x313831ab], [0x132cccb4eaca8b09ad20b182d42b30a1e801aad2eb309c8ab6e0050b092cd6b47ade8b0b2d4cb10ac58b4c2d88126ac0cb072d3cb4b2cea551ad04b172c36b502c6cb6c807b76c0066b281d0eb2e2c32b6dacfe7422c44b7bac7a72a1cc2b6e2cdab802cb0778ada8b282c92b0d2dfcb3aa51420fac54b249dc2b41ac62b08acc8b1f2c06b539014b30c87a8289daab11adb0b2e1df0b00ac8a76bacd0b6b2ce4b3611b2b42ace0b49ad34b32ac4eb402c2ab2c2c0eb1eac82b272c04b452d6a1812c64b7ead22b582c3ab58ac30b14aca2b4a2d681352ddcb0e2dbab4dac2eb4da40ab36910cb21ad7c930d502b209c28b5b847b217adf8b4cadcc1362deab552c48b3b2158b1a2d2ab12ac5ab1e2c12b06add6b1ca510b762c16b44ac10b76ac08b6800ceb492cfeb30bc1eb53ac3cb30dd56b062c40b1d2420b5e047af501dfeb682dc4b], [0x14e81ee960d6f78205fb107b7c7a03f6cf635f4e987db85bafde09dfa751efd3082bdb107b6ce03df69b40fd5a86af9e8ede57661f6f030fb1e8f7db3cc3ecc20df6e130fb3a8f7c8f40decc206f6f551fb59205fa0443bcc211f6f830fb7e385fba0c3ec7a02f6760d7b3b187d9d807ed4661f6eb10ef73206fb3d777cec19f6f530fb6c059f95035ed0261f63d067b38117d98405ede83d7eaa20fb30947d9402dedd670fef51efb30887da98c3ede0bffa7030fb63187db747becb83df69d40ef408f7dbf093edb21a7e9830fb75b41f984c3ecec0df6390d7d3081fdb20c3ed6816beaa38775f2cbe9e8c3ede83d76e11efb1e847dbf1eafde0e17eb710df358f7d9b02ddc7a1af661137b3f987d98407ed6461f6dd30fb5f987d8f415ecf470eee1456f308f3db3d7f7d303df6fc30fb758f3fbf155dcf43cfafc1efb55187dbad9f7d4081f6610b7b758f7dbacc3ec7a07f63d00fb39187d9e8edf47421faeb745f5520778f443ecb021f6611efb518f7dbd07becc20cf6aa1efb508f7db7042fcec21f63d06fb4e8f7d98435ecd661f66d10f73b033d8f479ec7a16f6eb5ddf4e8f3eafd777cfe3cf67603fb], []]
  | 9 => [[0x313831ab], [0x70add6b10adeab30ad3ab032d54b03ace0b1e9c06b052d30b40ac78b0b2c22b062c34b6eadf8b06acc2751acd6b1eac04b], [], []]
  | 10 => [[0xb], [], [], []]
  | _ => []

def C19_S (s j : Nat) : List Nat :=
  qGroupedState C19_initial 4 15 9 C19_patterns C19_values (C19_counts s) (C19_specs s) (C19_records s) j

def C19_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C19_initial (C19_counts s) (C19_specs s) (C19_seeds s) ws

def C19_literalRoutes : List (List (Nat × Nat)) := [[(0x4044,1),(0x2322,2),(0x4044,1)]]

def C19_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C19_rankPool : List Nat := [5336441, 1059722, 5532280, 4206237, 6446715, 4283514, 6311595, 1064122, 2112664, 5447102, 6638215, 6576250, 2117001, 6634391]

def C19_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r9 r7 r13 r6 r1 r5 < 3) || ((sum6 r10 r8 r11 r2 r0 r1 < 3) || ((sum6 r8 r7 r10 r6 r4 r5 < 3) || ((sum6 r13 r9 r14 r2 r0 r4 < 3) || ((sum6 r11 r7 r14 r5 r2 r6 < 3) || ((sum6 r10 r7 r12 r5 r1 r4 < 3) || ((sum6 r11 r10 r14 r4 r0 r6 < 3) || ((sum6 r10 r11 r12 r3 r0 r1 < 3) || ((sum6 r8 r9 r12 r3 r0 r2 < 3) || ((sum6 r14 r11 r13 r1 r3 r5 < 3) || ((sum6 r7 r8 r10 r4 r5 r6 < 3) || ((sum6 r10 r7 r8 r5 r4 r6 < 3) || ((sum6 r9 r8 r13 r4 r0 r2 < 3) || ((sum6 r7 r9 r11 r3 r5 r6 < 3) || (false))))))))))))))
  | masks => C19_rankPool.any (fastEntry (compactGoal 7 8) 4 C19_coords masks)
def C19_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C19_patternScore (C19_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C19_rows : List Nat := [28, 42, 49, 56, 68, 97, 98, 3, 5, 9, 6, 18, 36, 72, 80]
def C19_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C19_rows)
def C19_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def C19_ori : List Nat → List Nat := literalRouteOrient C19_literalRoutes
def C19_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 8) (compactCover 7 8) C19_S C19_N C19_idx C19_ori
    C19_patternScr C19_patternScr s
def C19_F : Nat → Bool := certAt C19_Z C19_N 11
def C20_initial : List Nat := [0x394, 0x54a, 0xca1, 0x207c, 0x3203, 0x480e, 0x5070]

def C20_values : Nat := 0x1fd3ff79feaff9fbf3c7dcffa7ff41fe83bd01fa00f0fde1f3c38780ef001ddefabf757ae8f9d1c39fe73f7e7e9ce53978727fe4f9c9cf9387203e401c5f38b870fce1e1c1f383c7074e0e1c0338006d7ed9ffaffb5cf6a0ed0fda1f34076800c7f98e5303e6000bfeb77eeebf5cffb9e37286e385bfeb41d63c2c3f5870b01d6002bff557aaae1552aa785470a7e94e529b852f0a4e147c28b850f0a0f941ea83c5074a0e541c68205020a02140027ef4fbf9bdf353a6a54d0e995f32866474c0e973d2e525874a8e941d263a487488e90fd213a417481e901f20324054804900520022a5439480e1010201040108019002a00240028000ffadfdbbeff7d46fa85f01bca17506e80dbefb77f6e96dd29b81b6836c06d5299ffb3fc672ece519c1b3036506c9fd93e32736496c90d911b2176426c83d905b2076400c1f182430206028c0017feafb55d42b7fd67eaca158f8aff15ca28fc50f8a0013ff27fc4fbc9e513a5257e4af8952928024fc48f890011fe23f447b88ed11ce239446f88d2117e22a044f889c1106220043f885f108020fc410081f903ea07840e881c1034205c4098812102020344058808100e2014402080310042004400480050001ea139425d28aa51394240041c082010202020400880090001ffe3ed47d08f941d4237ac6e50da11a9433c46748ce1196a32c46568cab194a328c6400c0017282200410080c10142010401080110001f783e507940e9417282bd056a0abc15682a7054b0a90150028505020a001200224044008401028201040108000fd01ee03d407680e781ce0396072a0e001800280042808401020202040208000c0014802800450088010a0208040808000a0012802400420081010001f003c007400e001a0030005c00a0013002500480084010001a003000580084010001c00280040007000c001400200030004000600080008000

def C20_patterns : Nat := 0x95565159451955645591459556155851595559555955595555551551551552554915195461516545551451554154554915185455514945191458515

def C20_N : Nat → Nat
  | 4 => 1
  | 5 => 21
  | 6 => 199
  | 7 => 651
  | 8 => 575
  | 9 => 51
  | 10 => 1
  | _ => 0

def C20_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x800b002000
  | 6 => 0x21095011000
  | 7 => 0x1d1bd0b0001
  | 8 => 0xfa13d008
  | 9 => 0x2b008
  | 10 => 1
  | _ => 0

def C20_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x381501181000
  | 6 => 0x501681401000
  | 7 => 0x58160181a119
  | 8 => 0x50169a49a
  | 9 => 0x61949a
  | 10 => 281
  | _ => 0

def C20_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0, 0x0]
  | 5 => [0x0, 0x2, 0x26f806, 0x1f01]
  | 6 => [0x0, 0x900e590f01, 0x47e200b811158c22000300a41a4126006014c00309504a80360da005001082c0ee0be0ad800402c03503a001400a02104f805810000b006846401e036, 0x1c4024011f1100052a01871]
  | 7 => [0x2, 0x411902ef00030979002e0073008f00a0000400a780b000d380b0003b000180b003a6008400c5000f003d00aa00440005000e006e00010017000b000e017b00010006001400120015000701860040014280a900030021000b, 0x5949ae00b17e05f0481d300b03598d0340020972fa0781511c759c00c00313f0060ec05e0010013d00db00100193424e0da09604f9190070020060600b027f0a80d506f00403d01e05b1990241050ac00b0279000ce01c05106c00100704f01b26b0041f58b50d001c89a12e00400a00105e00400d01500400606d00600284500200600201607307204005c00100300208d00c02700100100f04c00601701604501b060038005830, 0x5650560980100610601804]
  | 8 => [0x14406, 0x49f4e22206a003875400235c0a80ae000601200380b52780980020bb400415406a0ad06de239025005006a002001809009a187065802408403701e44140cc00400c804c07414100d818407a0b7013004003a01f001007e16e00500200c60be00200681500d4013001803c008096001800c020002008003416400200083dc0aa01a, 0x13a02002ba582b951945877010043901804c011701105c1d06c060f00e09406010ad0d8030048eb3024304a7be82206007aac302c89793efa02c0b01a16835a201005479fa020010c84610c030980f, 0x0]
  | 9 => [0x14406, 0x80d00d3d000100400309042700100a010, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C20_records : Nat → List (List Nat)
  | 4 => [[], [0xb287], [], []]
  | 5 => [[], [0xa827b017], [0x3ddae5acf520f0b6bb2abd4533dd901dbed7c966b187b3b9e1c2d908dcedfc2e76be2], [0x9a3a1ae8a970e8591a5c3a0e52a34b3006b352e0e1a970b8392a8d2cd816cd4b8705]]
  | 6 => [[], [0xa437959f5d769ed79df6b137a93759f6a637adb76bf6a337a7376467ab37577552f6], [0x1487b3572b6f8a94a7d258a5ad4872b399c9dcd6a16cea26c9ac05971859f5d586905e5aa56d0b83da7b297a54646baa2609d1d52b67bb1cbb714b9ab5514f486bb699cb0dc954ada907d6d2052b66b2ab344d4ada906d66af52f47bb0cbd21949e912c2f0e85d982296b294a9d2672375489f17a5be0bba1af9a90d54f13301ea4408bd9a7f1d4a80e4c33863b352d39c4dfe24f2378bd52f26db5fa354abb290606d0152d69f296b3b1909da8a5cd4b99b3a42bdaa94fdd2cd0e9b526033a41f9ad22025ea4c84f4b85b385b0d9b9d918e126db30b52f2b3b223d69ee5ea4b26b5152e6a4155b44d3a9deea5acf73e9ea4151ab0ca995aec8cd487ab6943796b014bc94a70e50252d6962763b78abb14a6de4bd57f18f295b546909e12d59b0952d69f2f699b4abe1cad7e568a927a43dcbd054b5a91042f4885b3a42f59bb1aed8e457f14864276fb232c2d8ece1a6db352a097a0b029d21b89dd071f5616bd6a42019d494ad9bcb0cac83ee66aa973481909ecd2d1ec852e68741ee5468c9e91092f4871a77435f3d2090d668d76d486db5b0b969d9a0f3aa34b4f4852b652923a52dee5d64a5e928869d9a3213b8d4b9a1ade9ae06be6529b3a520d8d690536b637b97899b0eb294b9a907067486a27], [0x296ec3615a8d2dec9696ec3016a8d2e168e913e5e93551b4afc27cbd52d2a5bd9ead2a34b7aa692421ec7268e861a3a8d2cb01e970b7ab29242e106a90bd52b2a8c92103a90af52b49f2f55f46913e5795a5c2dee4d7aaf52f0b352dee1e970e7b95a8d2e1e1e913e5296a8d2e101e970f8593a5c1dee5a970b7b31a42f55ec5aaaa2be4a5c2e104e7caf52d4]]
  | 7 => [[0x14], [0x4f964b48dc9244b7b24e626083d2052424c72e583b011529a534a668d2026316a57eb85abd2908952115a5aa8b7d0ebb2d1a5a50b850e8e2d505c0c745171d10da89f53a400714dac4a1cb3f24d52570598914596852e603b48b4c971f12903298b40a2e544a8945045297582d345ac929788c822a85be0752b3234d905b7895216822ea4012525196a12e8e5a18b4022a5711e5adcba4064c4aa45c3926196c52e9e59fd272135125305b2097b8edc261a3a6cb5c96e325ae52c0b2aa72212823d20b9c96952e7e5ce8b5e17061d125d68b6216a72e4a2270b51170b46123d24b93a4564a785cc842525051d7a8bec7b312dd262c2294f90087245525a40b4616a52a26236d26b969e2e0e9b64b9f0eac2d4a9aacba51726116a5a48b810f1510c09d204808f1e10d894a043823632e9a58dd36a132d12965a80b7c8f48053a5bd53b08e882d265b5d3], [0x70297b5a290de90d36f485ef3551f7b29411daa34bced93ef692b717c91ee7e967eeb0b3abb5ea9794f97b6e04aaaeac2af67b20baca54bdaa3089e823873602ab9d204cde3d023f25563785c22dcb1055e1ef5bd0937dd5eaab9d614bdaa33acf5352f6a8aab3b8159d66713774b76b7a4015bd2e095d54a5ed405ef3923d9ec8104dd5480e74b57f557a97ac9504de90086edb61f555133ac76027e68c36f667bcf5283bb52080de90e86f51a5afad54dbd2012de02d49ebb307652903b280e1cd4a20ed3f7bd752963b52de8dd4a9ded51922f9f2f79a08dbce270f3ea501f689960fa80a9d5c6aacf4852f6a42f59d2e16edc055f89b36f3a5b233a9405da913e2f5185eba5c79bd44b13e97486f1d4cb760a97b4b1016e7cbda72c3ede761f5f4e9edd690bd76f741576e15775214afab4ec6f09705d58123ad2e5ade97346ed52bed5ea97d569919dc6b8ce823ef6411b3aae0d9d58e80e704385ba8c4d7aa871d98e7eea822a75a5bdcbcb1555dd0a5ed4b90378eb517d221edd64aaeb024dd75f2bfad493adea2f6dad4416758a97b4b570ded060bd4b36f3a5c5dbd4e96de913e6f6852f636903cd215ede90826f3463b75289bb294ebdab4d8ed4b52f655183b52d7bce58c7ae571b7c6a2673d2038dd7060ecdc5567412039d2290de587ebb13841f529cfb425555e96f6ea803efa642ab3d2252de47137d202a3da4361baf55fe640a06f4252f6602779cf94b5cde61f34b2af6a5bc9bcd2587e91246f4852b6a5c06bc7936de1682e6702a796a14f6a945fda12dc9eaf52f641183b405555e0282af2789bda9d21bcf9555e7cafbb487637901c1dd8e5add7aa5ed485537a5cb2baf517cd3253eb1e36bba415dbcb504de3caa6e8229f5a42bded20eade9653eb044157a0aaabb55059e96fbaf3e5ed7a5b8f3d2e4ade970b674b6e675282fb2bd05d69b1d6f4b7af6550bbb4d14bda9702af25849fa4005bda25a7d4a82ed042a5da40bdbd217cdec2c3af092adea4431bd2cc1d9a6a5ecf5557672b0f9abd4bf1aaaace55137ca5cfabc214bda490b76be52f6a4055bb614bd90455ed51a5b79f2fabc7554ddb0aaed4870375ea979d461f3e912e6f6ba437, 0xec52f69644cfc3e176e046db655247ca42f5bbd955d5b882cf4b78b7a400dba9419da5a607d4f8f37ae495bda13b9e04d59f3e52d6b752dbbdd555daa6dd70129dda5953ab7891b6971d6f25703da41cdba942bd94a01ed4052f68ea09bc7904de913eaebd57f5a402dbd201cde7ca5bd4b6df597297b54954dd007ef34858b79f20abcb5ee7ebb486f48013737957e425595daa40db4b3873ac521b9b4afe54a05ed4b7637a41bdbc3cdbe55470e6a52bf6822aabbd9ebf1aa9bcf0b7afa96b8d7af55fc5047ccf4b247552827b3b186de3d0f7b4b72f3551b79c21ed75aec3ecaa3675719b36ba0c3ee96f73f4b6bf6a44d1bc4d54ddb8accf517aee6a2ab3c2dede6829daf0e7bdd969b1eaf563ce1a48bb4b85b74e9d73ac93bd616aae6ec305e3f1f7e20891d54a6fed4b3675a4295bc4d0edd7aafe74b79b7b0d2ebd9290de9709af4b6ae7b41b2ea954bda18a5ecec365d71983752e26de908b6f4884379d42f9d45059e90206eaa3f757aa0bb2bd4bd27c87af2555377430f3bdcea7d8e7deca509f6a42bfaa9439da97186f4809b75514fad2d01ce48c8cf252abe57a3faca090f55439ed205537a44f8fc11415d68a5ed0f6aeda42bdad46969e3cd55f4b85f35a957b52018ddd8c76f482c37618bf3d2126de7ca5ed2d553789a09ba9513da91406f02415757aabab81879e96f76f3a7af6a59f7b482087cd860f8e34167a5bdebaa8abda687d7d1d29bd55123ac1def7a78f5ed094157b42e2bc914bd97a82e74b6a67aa481bd2186de0299af5a9a3736923ca08fdd61ea5ecca416785bdedaa8a9d6687e7b09135d], [0x290bd4133a5bd5d8da97347433a5c21d85e96f67635a5bb0b05ce66f2bf85515c4dd2970f7617a5cd1ee5e90af4135a5cd218ce96e870679f2f5054e7caf4155a429504da4908761e843a0e7e9d0d85566a5c2dd8cdc0d8556657a9505d17aaf4171a8d2dd89e7ca54156b43a0e7ad7aa54172a44f9045ed153a5a7]]
  | 8 => [[0x5d66d45587a1], [0x89a85e51125a0119028015084a1ad416296d5090919d427286651165c9545ea84551a6a280b68a86c4a18a0114a59cb6518e5835417a87852b2a52cc15a8ce51ee3d4549c28fe51d0a4d948228ed52dca4804a42935517a8a08e7b2855513a5d2e07fa8ac2e90045d485a29750eea52ddaaa92e5234a1d9410a93a5104ebb945520c95032a22d4a2a93e1c60a1d140a28705062a401411a851517ca40872928e050a8a3694b4a94b5014a0a541228f051545cb145c284350da8a09a2c283b5090a208b41186f5224a2094a2293751faa520452a92510b4a20906a131950a8952d06128554c38a0d5428282a5262a00948da828508ca42d471a8d551705aa9a9228f649a8a21cb0aa88f2c6ca00d41c28aa80baa5b1496a839527ca10143e28f75066a26d49d161d521ea1e94302709504ca47443ea67e5020a38942e28605154a5449a1a83e5024a1b1461a92d11e6a0f54551910523c21cd452a64752d0a195458a8a05158a039465a8595074a21d43da90850faa17d419289b2daa4d20b10291e52dea385452961a5252a3b1438227e4882a0894898879507ea361409a94052965bd5304a80c5016a1b54ad165b51dea019426a8a529865879474a8cc502ca20147528932df8a0454342857504ea21140428f15154e86144b288f51b848f14, 0x1914414083503ea57944ca86151325abd416a9645088a06d4792918500aa38c9ad282551d6a57d466a88952083c454a5b4635126a33d495290250d4a47549a280f5154731d46e29091e583a7547a28af4a02385d43aa83450a6a54d429a42e52d4a329434a901517ea13d468291c51eaa01d4], [0x14a82ef64a5f7b43a37d2cafdda6aaeeaa0477a5cd1fd2c13dd541ceeaa20776a89b7da2a7be1082eebd41779f20abb80aff60426bf3a7677a5883ba805fddd08beeaa4ef741103bd2104fe9082eea541765ea0b9b8155dd540eef4b05f7a9aabbaa82bdd84aaef0417df37903ec3dd1fe18aaef34973fa5823bad955de962fee8239f7552abbd2cebde8082ef29923f52a0bf2085fdd5409ef4841378620bbd2e69dea74b7f0f865f879bfeaa905dca620fb4b6c773795fed2e97de9602ef4b9777961d6fab081ded12ebeec2c5fa5ca7ba0803ddd0aaef1e133f4102fba00ebed5426ef6889bfa9a0bbd2c07ddc040fa7e3afda9c91fc32117e6882ef4b7637a5cd1b9f4ebfa1073fd246c7e96961f9ccaff8d858fa823af78e881fabd05dd0403ee57137d762abba0813ddc658df0f5577743837da155de7c82eeaa05f79a3a3dac505de96e8ef24847e380bfdbd5d9fad073ff3e415fa9d2fbd2dd9dd5420ef5ea5f77b3b3ed2c4dded10fbedc206fad52fbd6a49dd7a82f74b927794aabbcd252fca82ffaaf417d3689bdcd1ef7dc0b1fb4b0e777620bbda105dd3220eeaa17f755017bd2ce7dd62aaee40137da5857bc21d1fe9605ee602c7e6a08379cc91f5d0bef6ec3abf6c2abb20805de9682ee55207ea5b4fbd45d9bd0457ef4b2c77900bdfaa819de80aaef43557794c3fed2dd8fe5caaef343abfa583bba0839de96c3ef25203f55163baa8ebdd0413eeaa16f7743637a08b1de1e82ef4b06779a491fd2c27dd7058ef4b58f7741cfdc2dd9eed94beebe41774103bba0841dd0408eec73af757a0bab6955de0220bf4b2077a59bfbb6113ded108bf2441774120bba080bdd7cb1ef0f845f551bfbc3c4df57caaef4b87f75500fbca5c1f61240bf4b70776c2abf3811fddc082ef6843f7a9a4fbd2de1de10aaee820677399bfdda2817d5473ef24557769a0bbcd219eeab4beed855775504fba084dde68aaee9b1377a5c23bb81b1bdb082ef405f7755097bd2e19de5282ef4b5577a5d03bc3dc1f696beeeaa2bf787bb2fc91d8fe10ecbf682c5f7420bbd6955de5c82eeaa0177411bfbd4e96dd0415ef68a5f7], []]
  | 9 => [[0x5d66d45587a1], [0x14b51d0a49145f292e5154580d409a86f505ea021441280250aea2a943aa90c5016a071469a8b1504ca101404a8822e10a081402a87350b0a4a547028d852d0a54d487a80c5280a52cb072934502aa3b14], [], []]
  | 10 => [[0x14], [], [], []]
  | _ => []

def C20_S (s j : Nat) : List Nat :=
  qGroupedState C20_initial 4 15 9 C20_patterns C20_values (C20_counts s) (C20_specs s) (C20_records s) j

def C20_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C20_initial (C20_counts s) (C20_specs s) (C20_seeds s) ws

def C20_literalRoutes : List (List (Nat × Nat)) := []

def C20_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C20_rankPool : List Nat := [6637690, 6368924, 2104215, 4262552, 2178441, 5311678, 2121081, 3156874, 6445688, 5336747, 5532295, 5394043, 6373084, 4414072]

def C20_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r10 r7 r8 r4 r5 r6 < 3) || ((sum6 r12 r9 r14 r2 r1 r6 < 3) || ((sum6 r7 r9 r11 r1 r0 r2 < 3) || ((sum6 r8 r9 r10 r0 r1 r4 < 3) || ((sum6 r9 r8 r13 r3 r1 r2 < 3) || ((sum6 r14 r11 r12 r0 r1 r5 < 3) || ((sum6 r9 r7 r13 r5 r0 r2 < 3) || ((sum6 r10 r8 r11 r2 r0 r3 < 3) || ((sum6 r8 r7 r10 r5 r2 r6 < 3) || ((sum6 r11 r10 r14 r6 r1 r5 < 3) || ((sum6 r7 r8 r10 r6 r4 r5 < 3) || ((sum6 r11 r7 r14 r4 r2 r5 < 3) || ((sum6 r12 r13 r14 r3 r1 r6 < 3) || ((sum6 r8 r7 r10 r5 r3 r4 < 3) || (false))))))))))))))
  | masks => C20_rankPool.any (fastEntry (compactGoal 7 8) 4 C20_coords masks)
def C20_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C20_patternScore (C20_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C20_rows : List Nat := [10, 28, 81, 84, 97, 98, 100, 3, 5, 9, 6, 18, 40, 72, 48]
def C20_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C20_rows)
def C20_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def C20_ori : List Nat → List Nat := literalRouteOrient C20_literalRoutes
def C20_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 8) (compactCover 7 8) C20_S C20_N C20_idx C20_ori
    C20_patternScr C20_patternScr s
def C20_F : Nat → Bool := certAt C20_Z C20_N 11
def C21_initial : List Nat := [0x748, 0xa92, 0x10da, 0x1925, 0x6403, 0xa01c, 0xc0e0]

def C21_values : Nat := 0xfd3ff9fdf4dff0feee9feafee7fce75fe748e4ffe4e3e4e0e41fe41ce403e400e0fce0e0e01ce000d9e5d9e0d925d8e0d1e0d0fad0e0d0dad000caf2cae0ca92c9e0c8e0c7e8c748c6e0c5e0c4e0c3e0c2e0c1e0c000bf7dbbbfbadeba9eb9ffb93db925b91cb81cb7deb75cb11cb0deb0dab01cafdeaa9eaa92aa1ca81ca75ca748a41ca21ca11ca0dca09ea09ca05ca03ca01ea01da018a010a008a004a0009ada9a92992597da974890da90008a928748801880108008800480007fb77f6f7f037edb7e937dff7d277d037c03792577db774b750374db740370da6fdb6e936e036d036c036a92674b67486703660365036493644b641b6413640b6407640060003d253ada3a92392537da374834da30da30002e922a922748240020182010200820042002200120001fff1fda1f921f6d1f481f251f001eda1e921d251bff1bda1bb71b921b251b001ada1a9a1a921a481a0019ff19da19b7196d193d1935192d1927190018da18181802180017da1758174a174816da15da150214da140013da139212da120011da1118110010de10db10d8109a10921058104a1048101a10181010100810041002100110000fda0f920f480e920b920ada0a9a0a960a930a100a020a00090008920810080408020801080007da0758074c074a07490700060005000448040804020401040003000292024802100208020202000148010801040101010000da00d8009a009200900058004a00480024001c001a0018001400120010000c0008000500040003000200010000

def C21_patterns : Nat := 0x655594565119415955645591164156555855611581559555955595555551551552554855195455511542550551554154554554555

def C21_N : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 176
  | 7 => 488
  | 8 => 432
  | 9 => 41
  | 10 => 1
  | _ => 0

def C21_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x7011002000
  | 6 => 0x2507d00e000
  | 7 => 0x1e14a07f001
  | 8 => 0xbe0eb007
  | 9 => 0x22007
  | 10 => 1
  | _ => 0

def C21_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x301401181000
  | 6 => 0x501601301000
  | 7 => 0x601601696115
  | 8 => 0x601616216
  | 9 => 0x515216
  | 10 => 277
  | _ => 0

def C21_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x1, 0x6b0b080183, 0x641]
  | 6 => [0x0, 0x550047, 0x8c03952884c2d201502887d0290050190038390090010080410040018332920180bc0180050bf8161e704a0020cc02b, 0x107e4f009894020fc1f2be1d]
  | 7 => [0x2, 0x4ac1ec00201283f96000020da08a02d401a08c00300d402401c66583d834c00f001800c03413c83f800401600101280f8004001, 0x28b9116e90030a40101b203501d00105d0230162261a900107d01f94a26800202d4e100837a8f401000307a1cb00602c0530e78f200c8f00200080020800388c902b83382a23f0018131f506500101001700909e0020040060150b000304b00311b02802700f19200700301002a00c0780e504100700900700d001027, 0x1847a0010a0813020001022]
  | 8 => [0x33, 0x8d600a0b409f44800126400b0cd01900b12401503a06488009400912887a0010430f50e301000103587604204409200104a35603385905407100100201705184d0d500f0248eb84900b16a82200100100400200400d01917e, 0x304be09c00d01f03206e3248a689104100b0de0050060170071c100888903800600100900a13f00102500100e00408e85005404c80400e00100210002c07903a00f0d18be019058, 0x0]
  | 9 => [0x33, 0x90480c01c176501c87806, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C21_records : Nat → List (List Nat)
  | 4 => [[], [0x3ff0], [0xba40e0], []]
  | 5 => [[], [0x3b71858f], [0x6415f05e20781a055c16a81c512860e409e3828cd1860ae826813b7041a0b821101c10277e0a4326151a0744156a8d5481d0813cf0], [0x2190a300a81b9cf2456cab40e081ad0f28606813cb086428e62568813ce0]]
  | 6 => [[], [0x307a64f941f938f9637a3ef94bf9839f347339f93c797f3b4a7a40fa], [0xfb7bbc789cdca58c1c8f873e268117161983c308e7e1e87372f0471e409e792d103a8e641f0823c7180181d15083c8d060e50340ba3b9d789e0c1e20478727330788642879ccd1c6290c1f047fb3812c15c11eed95060d4a239e9421df8a38e7e10279e10339b92a0e38aa883b1f8dd3aa2326334107920087d1e47372813cf878981d400e6e5f8aa5aae39e93b99389907fc56078d303739b3b907a3c11a3d0279e2773072884347c311d38c038f10a621b5b207923cc1e1e46074822ef2340778c24c0ea18f75ccb305a81390da0471e16a68c70c39e980384dc08c0ea19071e8139f84018f91dccfc54664d2c83072511835204f3d0d03fe2a43ae9409a39258e7c4ea2bf0810ef83c9cb8c30c1a9f26074f939b97a181d40d68ad5475d2803af1641cf89e4d1c54684d2601ff8519cf49e0d1c619081f0534333c99389dce7c6127372a839e9802b95af54a797a9b1f047db55198352c0c1a96873d2bc327130103c2b8c1a8f860e4a333e9659ceca1055e0c823e2ab40f85190761dce3c54675d2ab3471], [0x2190a3a8b409e4c9c214c86195819e4c8c618f86d8e58208c7895c73306842208f3c2190a610e7c36d9059047831f0803855c2d02793af05b2acc98568793261802b8e6a614bd301a86428882de4773ab1853218459e4d83a99852f4e666190a318b802b8c0a9e4a33aa980384c068f26018f03c91083c2190a628b801ccc0e200e1399986429901d46773ae18530d8471f0db619c86429863614c86293]]
  | 7 => [[0xe], [0x9a862219c13e10d0862a130856a0ca83411904306d9816134a283c1502d422098849a11ec39c89c84b118e87b0136230a154261b0b8823212a828219612031bcc47350274c9212039b092851099a11fb0c0d213072c6520be82f209483c31ea0304cfc839a12283c214ec31a15225188c4839d902824214ad2220cc83a20b282d20e664831502678524815b4ae874920407a01f2030215c22aa21828001602301de207980ce827a1c481d30e487900b081c30e7a3b921e02ea1682340ce65305cf4825a14823aa0ac8302a0607e00de820b4b684011f402a21b4d5990c88], [0x431cfc9e87fe4c002f4b02a6b7a1d5db6ce7e4ee43eb0c64677cb70f9e4c9cd2c8feb0c226b5718373c5ae7cce41f4ae236b3e18f9a611fe618c3db00303e471d7d30889e95e60f4f4223b6530fc9800be8c62af4f933bb300c7d28cebe6004476441c797caa17c01c27d4677cf0947bd7928d7bd0f8de1863d6843cf986428fa04c9e95075d7094b37518c76c30ebacc043f4a831eb7c98dda103be52c8eec60307a571cfcb0c89e58ac3f30a39f980384d9f081d57073f303323b3c983d19c3be6128e7c4c1c797c9d5dc08c6ee1c73f30039bd761cfcc391b3dbe60f4b63273519d76a10d1cd8463f47c22735818f5b20c7cdf0c86ef26c1f7e0e1e9f0ebcce603f2bc3af9399cfc9d441e54644d6b6307a55907e1dcb1cd0473f2753473719cfc9cc3be5e256770071bb42107d394c1e9b4cbbc822a73208e3e3c10c7cee31ea793af95198f5ba8c1e9e444770c852f80181da8c87b4e060f4962273571cf5a8ceba61460f4ae306a3b9139a58c7cde85c767932793b9d79a8889ade23f7ac7617a3001fd1d447e5f0cb3ef131bb5e9cfc9903be5248ff300572f30077d1cc03e6067576e3307a31983d298c1e8a831e6a8226b789d5d9cc87e55c60f4730a7930033d400eaed0460f4600c7a80181d1cc19e621083eb639f930133d18013e97a9a3e84417a801cdca98e7e55438db0c850f519635b0cc7e586c2f90a659f43183d18007e8c63ff2f955bd5e983d2ace7e54456d6af39f9849d5dbe488ee1c8ebc8f477c398c7ca887fb4e624f2750f7930007d3d080f54463d6f231bb3c993a9a087ccea3bf2f1512f58983d42488ed5067d6750ef96f32ee9dcebc5e4776eae226b7c905f2acc9e5c4cbb709659f791d5d9ccc1e50873f30a5e9f5599fc98021e94475d68e31fa6598edbd1b27cea73f2a820ee39863ca3cc7e48837e6df39f97092adc3185b8e610f2751c792e103c9dcc7cc883ff2e965d739983e1cc9fe6006376ae39e93c907e3c8b0ecf054f3085e9f7c30deb2c896e18c5d67520fa3991bcbd0c6ecf273f28f3af9751cfcb2187d600e1767304f9519d75a10c1e8c818e6602a7a87183d11081e4e607f2773af939983d320ebccea2af27933f9, 0xe670f3145e9f6431799587fe56875d70039bb4118fd4310d3cf85ce660227a802bddc08a8ed8ac2f463167a39983c384e7e4ee75ea75117939913cb84c1e91e44f2751ff94923bd2b8c1ad5c63d67331f931907d36cc1e9c2aed6751e79571cf6b0cebe618cb9e6831f34aa3bd1e0c7e618f85e631c79559d7c90c55f15660f4752079409d7d2d0c9ae00ae7696497322107d308ebe8fc40f309493b4208bcb2185d8e605f2733279571d7598c81e5c6aed700572b318bbd1cc05e59044e675307a4b1d79bc488ed5684f2600a7a20877e23889e8ee38eabd475e659d6dc24c6ecc024f4793271], [0x80384886d6cab3ae95b208c7ca00ae222b571cc89a614c35e9d801cc88e4ee750ef1411e4c7ca210e850f864297a3cf24418f14118c71e1e4750eb98018088e95c60226a519d43ba5047921f455a98eba614bd221b411e4ebc614bd319b853217a5df0db5e9e3c9d4c9c4e66022784118ca9ca14c25e9e853157a6e14bd3a9b]]
  | 8 => [[0x45cf866bd], [0x17ce2b2068e0bb878e2c215ce3220ebc5cb90ce50b83ce89b8e6c2c3886e4d3950e31a4d6e03387ae3020ea935380ee0a38a6e45b9ace7c80e654239961233840e203222e06b96ee1f395ee43b83ae6bb812e14388982938dae31ad1ce2e20e6e44b814e46385ae04392c4788042e443846e4fb9a4e492064e4939d6e12b9e4007b8c7c57081ce13b888961b094e34b808e1c300ae6db9dce1638ea83ab8c688c38e0e3ad104e453822e64108ee1ab8eee56394628d38f2e6c3956e1bb984d0db84ce31b860e5108888227212005ba2ae1238a886fb9a8e3e1140e61b9b2e70b854e31e12ce22b85ce8a38d8e0939b8e113946e5db866e64395021c391ec3e3838e09b91cd68b8eb8613a2ce8cb90ae00ba10e17b8cee20b90881fb0c0e46b8eab7039cce0d3980e323a1ce800018e3b908c862a032e62b888b2e3898886082ce0fb852e2520a8e0ab8ce86ab9c6e8bb8c741db8c07083882d76b89e839a182e8639dee30356ce4e38894513806e7a00ace1fb9d4e26397ee1b3996e20393ae8539a6e37389ee0c3978e5939a0e18b93ce5eb91ee223804e5338f6e], [0x17a44f660227a338c7d9d40bed6c44f7067ebf5b18fdab889bcf275fa7504fb518777aa063bc8801f6b6536f751d7dc421dbe1c75f670227b80b8fdbc83afce644fa60227e3a913d9d487ed5644f6310efd3a893d98c31ed5675f26303fb3c9d7cab889ad0463f67518fb5b20bbba889ee20cbbea20c6f1f863ea590ddcc626f6db31fb3a843da0887f8ea1df6863afb22033db6d4df97275f6fd7c3f31913da1087ed6463f6e33afb3c9d7dc317bbd0479ee823afb2c077da08c7e91e86fb0a31fb21877e9cc89ed4c75f6c85ef73818fd9f049de1475f6ea31fb3c8c7e9dc3bde0cf87e75387b7c36ff2f4c7ec8818f663117b8721afb7c89ecea14f6bd3afb3180fdc38c7ecea21f68431fb421d7da14c7ecc631f644127b769d7dbc430fc8844f6b63afb7512bd98c29ed5e75f6632a7b22077dc3889ed1c86fc750c7b3a877cbe17afd5e63f6a6227b41113daac87f4c044f66321fb55a9b791007edbe63f6db227b61af7eaac63f48814f6fd6ffd852f4faacc7ecc624f70a227b5318fd98c19ec8809f6e3227b22017dc0088ee12867f00223f559d7eb7cebed6cabde5c127b3a833d98c21ecac18f6e331fb3c93fdbd048fe20f87e7322793198fd9100fecea1dfa86227b22043d90463f8c61df6b657ef220c7d98c0bee0d017e7531fb3c98fd91005edc244f675327b62af7dab889edbeabfaab3afb833abbc4214fd5e44f66304fb2210fdb6cebee14bd7ef918bf20093e9e489ecea02f68631fb7318fdaf50d7d0438fab6237b3a9d7db8d5fecf243faea5b7741133d9ecebecea03f663017b4921bda08c7f8ea07f6c25efe], []]
  | 9 => [[0x45cf866bd], [0x3cb904e013862e31b8e0e0eb818e57b812e6db8c6855b830e873a14e01b828e3ab9d4e5eb848e02b90ce5b380ee2239bee53388883aa020e21b9c6e], [], []]
  | 10 => [[0xe], [], [], []]
  | _ => []

def C21_S (s j : Nat) : List Nat :=
  qGroupedState C21_initial 4 16 9 C21_patterns C21_values (C21_counts s) (C21_specs s) (C21_records s) j

def C21_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C21_initial (C21_counts s) (C21_specs s) (C21_seeds s) ws

def C21_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)]]

def C21_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C21_rankPool : List Nat := [6389402, 4340107, 7610079, 7756681, 6298792, 5255134, 6315658, 3157386, 3231130, 4288429, 3296152, 7367051, 6651032, 6373294]

def C21_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r10 r9 r14 r7 r1 r6 < 3) || ((sum6 r11 r8 r9 r3 r2 r4 < 3) || ((sum6 r15 r13 r14 r1 r4 r7 < 3) || ((sum6 r9 r8 r11 r5 r6 r7 < 3) || ((sum6 r8 r10 r12 r1 r0 r6 < 3) || ((sum6 r14 r13 r15 r2 r0 r5 < 3) || ((sum6 r10 r8 r14 r5 r0 r6 < 3) || ((sum6 r10 r8 r13 r2 r0 r3 < 3) || ((sum6 r10 r9 r13 r4 r1 r3 < 3) || ((sum6 r13 r10 r15 r6 r1 r4 < 3) || ((sum6 r8 r9 r11 r4 r2 r3 < 3) || ((sum6 r11 r8 r9 r6 r0 r7 < 3) || ((sum6 r8 r9 r12 r7 r5 r6 < 3) || ((sum6 r14 r10 r15 r3 r1 r6 < 3) || (false))))))))))))))
  | masks => C21_rankPool.any (fastEntry (compactGoal 8 8) 4 C21_coords masks)
def C21_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C21_patternScore (C21_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C21_rows : List Nat := [10, 28, 34, 49, 52, 66, 81, 84, 3, 5, 9, 6, 18, 40, 72, 96]
def C21_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C21_rows)
def C21_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)
def C21_ori : List Nat → List Nat := literalRouteOrient C21_literalRoutes
def C21_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 8) (compactCover 8 8) C21_S C21_N C21_idx C21_ori
    C21_patternScr C21_patternScr s
def C21_F : Nat → Bool := certAt C21_Z C21_N 11
def C22_initial : List Nat := [0x1d1, 0x2a4, 0x64a, 0x928, 0x1430, 0x2038, 0x3807]

def C22_values : Nat := 0x3d38f0dfc30f01faa7e75f92fe41f887e11f83fe003438d0c2938a4a2838a00264a8af22a487e61d184e20b881e202880820088001d3870c16b4592963057c553052c14703da8e4a2eb0aa427e490020007db1d286ca0fd43a40b902800400080010002800800080010001

def C22_patterns : Nat := 0x0

def C22_N : Nat → Nat
  | 6 => 12
  | 7 => 41
  | 8 => 31
  | 9 => 1
  | _ => 0

def C22_counts : Nat → Nat
  | 6 => 0x9003000
  | 7 => 0x7021001
  | 8 => 0x19006
  | 9 => 1
  | _ => 0

def C22_specs : Nat → Nat
  | 6 => 0x401181000
  | 7 => 0x301481101
  | 8 => 0x581302
  | 9 => 257
  | _ => 0

def C22_seeds : Nat → List Nat
  | 6 => [0x0, 0x1, 0x750a02]
  | 7 => [0x2, 0x285825201e058115e14, 0x4c3]
  | 8 => [0x503, 0x5411a470060d802804, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C22_records : Nat → List (List Nat)
  | 6 => [[], [0x613fb9f91f], [0x5e753ae7b5853370ba3d74d9c2b97d623eeae9de5d5]]
  | 7 => [[0x7f], [0x184f6f7e1bf67e8f78afd3f61bf35fbefbdbe4bec6f82ffb7cdf65fdbafdb7f57f65f57dd7ecafb2df3bd93f63becef73dafbd3fba3f], [0x17915e982ee2ecfc5a9fe633f0827d705b]]
  | 8 => [[0x955555665555595655555], [0x67fe7fdf7c3fefff23fc17effe2ff3fff1fe8feb7f53fa1ff7fe0ff83fe7fc4ff57f4bf8ffc2fe37f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C22_S (s j : Nat) : List Nat :=
  qGroupedState C22_initial 3 14 6 C22_patterns C22_values (C22_counts s) (C22_specs s) (C22_records s) j

def C22_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C22_initial (C22_counts s) (C22_specs s) (C22_seeds s) ws

def C22_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x200,4),(0x20,8),(0xa08,4),(0x2120,2),(0x1011,1)]]

def C22_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def C22_rankPool : List Nat := [4413814, 5393547, 5389740, 2103655, 5458553]

def C22_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13] => (sum6 r6 r7 r9 r5 r3 r4 < 3) || ((sum6 r11 r8 r12 r4 r2 r5 < 3) || ((sum6 r12 r10 r13 r3 r2 r5 < 3) || ((sum6 r7 r6 r9 r1 r0 r2 < 3) || ((sum6 r9 r7 r10 r4 r3 r5 < 3) || (false)))))
  | masks => C22_rankPool.any (fastEntry (compactGoal 6 8) 4 C22_coords masks)
def C22_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C22_patternScore (C22_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C22_rows : List Nat := [33, 34, 36, 74, 81, 92, 3, 5, 9, 6, 18, 40, 48, 96]
def C22_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C22_rows)
def C22_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)
def C22_ori : List Nat → List Nat := literalRouteOrient C22_literalRoutes
def C22_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 6 8) (compactCover 6 8) C22_S C22_N C22_idx C22_ori
    C22_patternScr C22_patternScr s
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

def C23_counts : Nat → Nat
  | 5 => 0x1000
  | 6 => 0x1f002000
  | 7 => 0x105f039001
  | 8 => 0x3b095005
  | 9 => 0x17005
  | 10 => 1
  | _ => 0

def C23_specs : Nat → Nat
  | 5 => 0x101000
  | 6 => 0x501181000
  | 7 => 0x101681601111
  | 8 => 0x691691212
  | 9 => 0x511212
  | 10 => 273
  | _ => 0

def C23_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x0, 0x0]
  | 6 => [0x0, 0x1, 0x418103b44c2c81687c03, 0x0]
  | 7 => [0x2, 0x341600707656c00900a0f30010080530d700300e002, 0x801106a00d00080ec11a2c904d80140040cb00c890c03800900202680020030ee017003105c, 0x2]
  | 8 => [0xd6, 0x14d09584a847187402027e000409305503a42540960060fa006c0b200400d01d00c2011828007000203800a80340c2014044c10007a00703a407c0ae003, 0x10a076c2200c0009b6028108c000c010019001800401402e, 0x0]
  | 9 => [0xd6, 0x831848100100c01, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C23_records : Nat → List (List Nat)
  | 5 => [[], [0x610f], [], []]
  | 6 => [[], [0x2d8fd72f], [0x104de6dd97b1da53bab4af57046955c9bf4af2c716f6bd4da73a4f0dfc564a9dc39b976956e5c4e74d024176d53cb88e536e0ed9b8ace5906f6789603eed799dc1a35823ba75e911eead19d638ad3935f1372d66edd93e1dc0f], []]
  | 7 => [[0x6], [0x563f65df0b7d33bb6efa37e93dcefdb8ef86bed1bd7bdb3ef80fb52fdab7d53f76df60fcf3dda7b6edeebbd9b7a57739f6bbecdbe927eb87f44fda77a5f79bf703ef0f7b7fb96fb077cc3eac7d2ffb5fbe85fddbfa47f097cd3ed9bf33fa5df695fc15fa67e91dd5bed93f], [0x170baed79239c7a457b5823f42cabd994f3b6ad6dafa05eeaadb681cd7d2342f736fd66a27f2be433ca36cf8180f36940eed601eb41deba96d5ef4915cecd3cc71cdb8f689f8ab99e3ceedbb24679682bb5f01b689997d79fcf9081e6da27b5c4bb6c0bffa6c63da7e77ceddb27e1c14fbc3be6ded9af1522bbaaeebc5b05edec9ae516aed1471fb76fb67e69d6e06dbdc411f9b82b6bab5ce80fcfa99bf5755fcecc73ade9bdde2aedb6552ce725de5cce7cd2479faf929f4472edbd8fcc79a5d5d56f2726fe64a06daeaa7a8d659eca67b6be075d0362fbcb73f6b5ebee159ed6173da18d3f4266f54ce79ba37f3bb486f4868f6086ebde37bbb8755e6e47f16123ab41a6db7739f1ccd3ef0d3ad21dbb], [0x1e9d1bf8]]
  | 8 => [[0x697a8], [0xe61269867460568b67f62363364064861a63948a6096266565046be6476446af20864830b69962c68141e67d66623568962266522e61067b61c63b49063358c63d6926186796c161b65069f68f61d6786bc69d60263263862a6296b768768260160665d62169765c63f64f65167c65463460a68864361965b66064268215769e61460c6286682156806256276a20a900f6076c668d65665a6456916c76752616b807e6a104e6176b001365d49364162e5bd65368e64d6556206b965263166f44665f67767a69469a63761663451f63e6bf66d2c060360d68052b69c6116a40], [0xb5a802d135a2130bc1b3975a5bcb90bca80b5ad0753f2c53f15a37539134c5732661329c5f4bcb50341b53d3a46f624681b23b1b4b5704b57a0af7a237135736c273135ad97553133817a4b59c4924833f1b37a3f1a41b0706c2b5b10735a55f3d4563f565102bc821a11005d3f48f1b1b83f0c56c23d2e53a375ada80c5b125f3f3776c2c577273702807a55a3f3331058e131], []]
  | 9 => [[0x697a8], [0x863d6926036556b969c6076136776026bc61b63f60a65a60467a69765f6916376106], [], []]
  | 10 => [[0x6], [], [], []]
  | _ => []

def C23_S (s j : Nat) : List Nat :=
  qGroupedState C23_initial 4 15 8 C23_patterns C23_values (C23_counts s) (C23_specs s) (C23_records s) j

def C23_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C23_initial (C23_counts s) (C23_specs s) (C23_seeds s) ws

def C23_literalRoutes : List (List (Nat × Nat)) := [[(0x50,1),(0x10,2),(0xe,4),(0x310,2),(0x1050,1)]]

def C23_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C23_rankPool : List Nat := [6576760, 6491598, 2177927, 5328540, 1076651, 2112649, 4202173, 5532311, 6375546, 2182523, 5381241]

def C23_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r8 r7 r10 r5 r4 r6 < 3) || ((sum6 r14 r12 r13 r0 r3 r6 < 3) || ((sum6 r7 r8 r11 r3 r1 r2 < 3) || ((sum6 r12 r9 r14 r4 r1 r5 < 3) || ((sum6 r11 r10 r13 r6 r0 r1 < 3) || ((sum6 r9 r8 r12 r3 r0 r2 < 3) || ((sum6 r13 r11 r14 r1 r0 r4 < 3) || ((sum6 r7 r9 r10 r6 r4 r5 < 3) || ((sum6 r10 r7 r8 r4 r1 r6 < 3) || ((sum6 r11 r7 r13 r4 r1 r2 < 3) || ((sum6 r9 r7 r12 r1 r2 r5 < 3) || (false)))))))))))
  | masks => C23_rankPool.any (fastEntry (compactGoal 7 8) 4 C23_coords masks)
def C23_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C23_patternScore (C23_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C23_rows : List Nat := [28, 34, 49, 52, 65, 74, 76, 3, 5, 9, 6, 18, 40, 80, 96]
def C23_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C23_rows)
def C23_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C23_ori : List Nat → List Nat := literalRouteOrient C23_literalRoutes
def C23_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 8) (compactCover 7 8) C23_S C23_N C23_idx C23_ori
    C23_patternScr C23_patternScr s
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

def C24_counts : Nat → Nat
  | 5 => 0x1001000
  | 6 => 0x8012001000
  | 7 => 0x602f01c001
  | 8 => 0x20052004
  | 9 => 0xe004
  | 10 => 1
  | _ => 0

def C24_specs : Nat → Nat
  | 5 => 0x101101000
  | 6 => 0x281601101000
  | 7 => 0x201601401111
  | 8 => 0x491611212
  | 9 => 0x391212
  | 10 => 273
  | _ => 0

def C24_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x2, 0x0]
  | 6 => [0x0, 0x2, 0x812064005416001, 0x63]
  | 7 => [0x2, 0xa011765174d36, 0x40302104403505104200106d01d00901c828, 0x26]
  | 8 => [0x4, 0x83726a02105203905200a44007f03085200600f0048130130230030010eb065, 0x2b84c04085ec50a43c, 0x0]
  | 9 => [0x4, 0x8a08a27, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C24_records : Nat → List (List Nat)
  | 5 => [[], [0x3e8f], [0x41bf07], []]
  | 6 => [[], [0x3c9f], [0x209fc7ba98337e7c1eee86cd55131b9aaab7e791ee6c86df9d93bbb417847e1efcf43cec8b8bf25471e19f07a3dc4ac63c3ba6a7], [0x524542c2fcf0d21d4900bb0b831171970522e52fcf8b639f9f1745bf3e2f07]]
  | 7 => [[0x6], [0x6d7e9bbdd5fa0776b7e33f8ebbbbbf4bde45f5fb7b83f23fb02fd3f7927d53de7bdc97ea66f6c7e6ddcdfbbdbf6e7ea5bdc5fa0f7], [0xf694ddf9e179586791e12f2fcf83d34c35a30f7975426e8245d548c773f3e2f827a3ea645b4b48bcb4a6e75245d6fcbf3dd44db970f794d36ce6431f1ad80f97117977366efcf87df97b3b6983b4522f2e0a4bdd59cfb8913d804aae763dcd2ceb3b8311f7e5dd66219f12cb75b5a5af5240cedac27db5a5bb820376b3a6eda9abdacb5d960f79], [0x1f9f1687c1403e0f702e1e72a45c3da515087b8a0170f71]]
  | 8 => [[0x7698], [0x1a63862160565865215260a61262762250965162c64663c65067506562660f62966d04260e66a61f64863166362a60363460d61c61761360764963964060660466b07b00865c63662e61661463e60c64021061b63621162f60265963261e63f65764762261864b15466667002860b60163a24d11d61563a67e1206], [0x6d130521e1504e14d131694223a0c282780454223322550362827c01e0c5351326b0c02e1e47e5a1301342e1e3545014b0c1726f02d0c4701e074720320c5423e26913282801786f0451e4401e256541], []]
  | 9 => [[0x7698], [0x6365061361e60860c64260263e62e6546036326066], [], []]
  | 10 => [[0x6], [], [], []]
  | _ => []

def C24_S (s j : Nat) : List Nat :=
  qGroupedState C24_initial 4 17 8 C24_patterns C24_values (C24_counts s) (C24_specs s) (C24_records s) j

def C24_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C24_initial (C24_counts s) (C24_specs s) (C24_seeds s) ws

def C24_literalRoutes : List (List (Nat × Nat)) := [[(0x140,1),(0x200,4),(0x20,8),(0x208,4),(0x10,2),(0x4140,1)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x302,2),(0x114,1)],[(0x404,1),(0x100,4),(0x10,8),(0x104,4),(0x222,2),(0x4404,1)],[(0x4000,1),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e04,4),(0x2222,2),(0x4000,1)],[(0x54,1),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xf08,4),(0x2212,2),(0x4040,1)],[(0x4040,1),(0x11120,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xf02,4),(0x13332,2),(0x54,1)],[(0x40,1),(0x20,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xf02,4),(0x2220,2),(0x44,1)]]

def C24_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C24_rankPool : List Nat := [241447241, 201441743, 134264107, 135512494, 272738604, 67252586, 206650832, 134330733, 270744941, 275982636, 206585296]

def C24_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16] => (sum6 r9 r10 r12 r8 r6 r7 < 3) || ((sum6 r15 r14 r16 r3 r0 r6 < 3) || ((sum6 r11 r9 r13 r1 r0 r4 < 3) || ((sum6 r14 r13 r16 r7 r1 r4 < 3) || ((sum6 r12 r9 r10 r3 r4 r8 < 3) || ((sum6 r10 r11 r12 r4 r0 r2 < 3) || ((sum6 r16 r14 r15 r2 r5 r6 < 3) || ((sum6 r13 r11 r14 r3 r0 r4 < 3) || ((sum6 r13 r11 r15 r6 r2 r8 < 3) || ((sum6 r12 r9 r10 r6 r7 r8 < 3) || ((sum6 r16 r14 r15 r0 r5 r6 < 3) || (false)))))))))))
  | masks => C24_rankPool.any (fastEntry (compactGoal 9 8) 5 C24_coords masks)
def C24_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C24_patternScore (C24_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C24_rows : List Nat := [17, 18, 20, 33, 42, 44, 65, 74, 76, 3, 5, 9, 6, 24, 48, 80, 96]
def C24_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C24_rows)
def C24_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def C24_ori : List Nat → List Nat := literalRouteOrient C24_literalRoutes
def C24_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 8) (compactCover 9 8) C24_S C24_N C24_idx C24_ori
    C24_patternScr C24_patternScr s
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

def C25_counts : Nat → Nat
  | 6 => 0x1011001000
  | 7 => 0x203201f001
  | 8 => 0x2305c004
  | 9 => 0x10004
  | 10 => 1
  | _ => 0

def C25_specs : Nat → Nat
  | 6 => 0x101501101000
  | 7 => 0x181601481111
  | 8 => 0x591591212
  | 9 => 0x491212
  | 10 => 273
  | _ => 0

def C25_seeds : Nat → List Nat
  | 6 => [0x0, 0x2, 0x14d8460700c11, 0x2]
  | 7 => [0x2, 0x306e1281028242013, 0x40758322a000105402a04b46e001007009061, 0x1]
  | 8 => [0x4, 0x588f480100e3e95200e00806ce08990421f01800288e02001064012008038d5, 0x166040046401901c0e4030bf, 0x0]
  | 9 => [0x4, 0x790601013, 0x0, 0x0]
  | 10 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C25_records : Nat → List (List Nat)
  | 6 => [[], [0x33d7], [0x43afa77c767b0e90d611bcea89469895e8f06632e25f87b823d5843d66fc50e5691f2c026335945cadc8b55d5c0ec3b497], [0x4238a495]]
  | 7 => [[0x6], [0xe77dbaf957d757e63ed0bec2df40fa67edf9f927d6cbe6bee26fb4df32f6f6fcd3db85f83bf00fc73f32df66be4bf4a3eb95f797ef0fdaefb25f], [0x1f84ddaa146d8a4bcf15087d444f5c224b74628eadcb33dd56dea618f3844d6e5851e5f9c8fbc143d75456edc1d75e9a4faca1ed4231f2dad15e0cb27aa23675b31d6dc8775d491ebf28af803176eac87d49173b2294f7e4b6eca5175f06ff2a18eb6546aee6636df901ebc329f7e3e7ce4975e11c4fb8125d83579ecaa93e04a3cc518eb7240bac88b5e215b3bc2337], [0x221f15df2da19669]]
  | 8 => [[0x9867], [0x165561262862456262f61d60862d62b68260c62462765760967210363a64d67c66361167e01a64464060e61565d61b64163964e65c66e13d61763b63143667805666515363862266412e63164366911f61861062854051461960d60b64a60463c67502064f63765868311360f62963e67d60a61e60260560765068b60662c62163f6306606166266616], [0x402c58a86178130640e1230e57c606541325b0e5450e38a6d17c4d68a2c228135722c146133746d17e2c065131811347c7705b4355b2c26d6a1817c0573147143586711750e02c13488576432b5716d18a741817f07c245], []]
  | 9 => [[0x9867], [0x1362c65760e67c64d62b66060560760364360463f6086556], [], []]
  | 10 => [[0x6], [], [], []]
  | _ => []

def C25_S (s j : Nat) : List Nat :=
  qGroupedState C25_initial 4 15 8 C25_patterns C25_values (C25_counts s) (C25_specs s) (C25_records s) j

def C25_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C25_initial (C25_counts s) (C25_specs s) (C25_seeds s) ws

def C25_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x808,4),(0x3020,2),(0x1110,1)],[(0x5400,1),(0x220,2),(0x200,4),(0x20,8),(0xb0d,4),(0x231,2),(0x5414,1)],[(0x410,1),(0x800,4),(0x80,8),(0xf05,4),(0x1111,2),(0x410,1)]]

def C25_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C25_rankPool : List Nat := [5532536, 5381788, 3279789, 5515927, 5389774, 3284363, 2121338, 5459081, 5467257, 4328622, 5450375, 4349306]

def C25_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14] => (sum6 r8 r7 r11 r6 r4 r5 < 3) || ((sum6 r12 r9 r14 r1 r2 r5 < 3) || ((sum6 r13 r10 r11 r0 r2 r3 < 3) || ((sum6 r7 r9 r10 r2 r4 r5 < 3) || ((sum6 r14 r12 r13 r3 r2 r5 < 3) || ((sum6 r11 r8 r13 r1 r2 r3 < 3) || ((sum6 r10 r7 r14 r5 r0 r2 < 3) || ((sum6 r9 r8 r12 r4 r3 r5 < 3) || ((sum6 r9 r7 r12 r6 r3 r5 < 3) || ((sum6 r14 r10 r12 r0 r2 r4 < 3) || ((sum6 r7 r8 r10 r2 r3 r5 < 3) || ((sum6 r10 r7 r13 r5 r2 r4 < 3) || (false))))))))))))
  | masks => C25_rankPool.any (fastEntry (compactGoal 7 8) 4 C25_coords masks)
def C25_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C25_patternScore (C25_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C25_rows : List Nat := [14, 17, 28, 42, 70, 97, 98, 3, 5, 9, 18, 36, 72, 48, 80]
def C25_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C25_rows)
def C25_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def C25_ori : List Nat → List Nat := literalRouteOrient C25_literalRoutes
def C25_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 8) (compactCover 7 8) C25_S C25_N C25_idx C25_ori
    C25_patternScr C25_patternScr s
def C25_F : Nat → Bool := certAt C25_Z C25_N 11
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
def C26_rankPool : List Nat := [134300012, 235158857, 134331818, 167822638, 268584270, 272644529, 170930544, 236988719, 67323341, 235061548, 168018219, 67256747, 67157354, 33735981, 33635657, 201409966, 134299980, 268648812, 100910477, 201506090, 167984585, 100941257, 100712812, 268680586, 33669419, 234997134, 134497741, 201605451, 134267308, 100810153, 234964334, 100844909, 33800651, 167855438, 100810121, 201475470, 67157418, 201409902, 268517804]

def C26_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17] => (sum6 r12 r11 r16 r2 r0 r4 < 3) || ((sum6 r9 r10 r15 r8 r0 r7 < 3) || ((sum6 r10 r13 r15 r3 r0 r4 < 3) || ((sum6 r14 r9 r17 r1 r0 r5 < 3) || ((sum6 r14 r10 r17 r4 r0 r8 < 3) || ((sum6 r17 r13 r14 r0 r4 r8 < 3) || ((sum6 r16 r11 r12 r0 r3 r5 < 3) || ((sum6 r15 r9 r10 r0 r2 r7 < 3) || ((sum6 r13 r14 r17 r6 r0 r2 < 3) || ((sum6 r12 r9 r16 r5 r0 r7 < 3) || ((sum6 r11 r9 r16 r7 r0 r5 < 3) || ((sum6 r11 r13 r16 r4 r0 r2 < 3) || ((sum6 r10 r11 r15 r1 r0 r2 < 3) || ((sum6 r13 r9 r17 r5 r0 r1 < 3) || ((sum6 r9 r10 r15 r2 r0 r1 < 3) || ((sum6 r14 r13 r17 r2 r0 r6 < 3) || ((sum6 r12 r10 r16 r2 r0 r4 < 3) || ((sum6 r12 r11 r16 r6 r0 r8 < 3) || ((sum6 r13 r12 r17 r7 r0 r3 < 3) || ((sum6 r10 r9 r15 r5 r0 r6 < 3) || ((sum6 r9 r14 r15 r6 r0 r5 < 3) || ((sum6 r9 r14 r15 r8 r0 r3 < 3) || ((sum6 r12 r11 r16 r1 r0 r3 < 3) || ((sum6 r10 r12 r15 r7 r0 r8 < 3) || ((sum6 r11 r9 r16 r3 r0 r1 < 3) || ((sum6 r14 r12 r17 r3 r0 r7 < 3) || ((sum6 r13 r14 r17 r8 r0 r4 < 3) || ((sum6 r11 r10 r16 r8 r0 r6 < 3) || ((sum6 r12 r13 r16 r1 r0 r4 < 3) || ((sum6 r9 r13 r15 r4 r0 r3 < 3) || ((sum6 r14 r11 r17 r2 r0 r7 < 3) || ((sum6 r13 r11 r17 r5 r0 r3 < 3) || ((sum6 r11 r14 r16 r7 r0 r1 < 3) || ((sum6 r14 r10 r17 r2 r0 r5 < 3) || ((sum6 r9 r12 r15 r4 r0 r3 < 3) || ((sum6 r14 r12 r17 r4 r0 r6 < 3) || ((sum6 r10 r13 r15 r1 r0 r2 < 3) || ((sum6 r14 r11 r17 r2 r0 r6 < 3) || ((sum6 r12 r13 r16 r2 r0 r8 < 3) || (false)))))))))))))))))))))))))))))))))))))))
  | masks => C26_rankPool.any (fastEntry (compactGoal 9 9) 5 C26_coords masks)
def C26_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C26_patternScore (C26_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C26_rows : List Nat := [1, 42, 44, 50, 52, 74, 76, 82, 84, 3, 5, 9, 17, 33, 65, 6, 24, 96]
def C26_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C26_rows)
def C26_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def C26_ori : List Nat → List Nat := literalRouteOrient C26_literalRoutes
def C26_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 9 9) (compactCover 9 9) C26_S C26_N C26_idx C26_ori
    C26_patternScr C26_patternScr s
def C26_F : Nat → Bool := certAt C26_Z C26_N 12
def C27_initial : List Nat := [0xf24, 0x12d8, 0x7103, 0x8449, 0x8892, 0x1201c, 0x140e0]

def C27_values : Nat := 0x7fdffebd7f55ffaa5fc78fe23ff103f7fefb3ffd125e4fdf274f9127c1f9e0e0eb7cf53a7a5f1d0e0e7fb73f9399f7ccf2e670723cb91c1c892e40071ba78bd3c4e9e2707112785c1c1e0e070700037ffbbedfdd6f6db7765b9afffd7df6bdf75e79acdfd62eeb073513da892d40e699774abba4ddd22fe91774839a01ccb6ce4b631edb8cdbc4496200308b3844dc224e014300017ffcbff3dfcfefe4f7f24baf1dd47eea0773fbb9f1dcf6ee7b1731fb981dcbf2e5f172e0b96e5cb62e3ff71e3b8f05c47ee2397103b8805c3f2e1c1701cb8005bff2dfc96f3cb792593f2c9c162fcb170587f2c3c1611cb080583f2c1c160dcb06c58172c091603cb01258072c0015ffcaff257c92adf154e0a9fc54f82a7b152f8a97054b62a40151e0a870540029fc94f24a7705378299c14ae0a4f0523828fc146e0a2f051382880143e0a1705080283c14100a07c503a281c940e1a010500027ff936dc996e4cb626439311c980e4bcf25e492c1c940e498724a39241c918e488724401211c900ec806240112004900044b6224010f248200408e2040100007fffbff6dff6eff6f7f93bf76dfb26fd4b7e81bef6df326f9037bedbdd2debb6f55b7aa7bd52dea06f3db7981bc52de216f1037449391259124b6d95a24acb615edaacdb54492952548b2a44d5225a91254014a0004fffa7ff93ffa9ffc4fb6a7b6d3db49ed94f6c2736d35b49ad84d4926649312497d94b6ea5b6d2db296d84b24a552529b294594a25a512527b092d9496c248012094900047ffa3ff51f6c8f7d47b7a3db51ed88f2c4792a3c911db68e924724a376d1b248d49466fa336d19b28c92462ca313518968c49460022e4915248992446d22269112c8893440021d250db28690432ca19350c92854d42a5a15250a0484db426ca11b508ba845b422ca113508968448420a2102508108401420020801020080584024a012100308009400420011000280003fff9fcfcfe5e7f273f819f40cf20677db3b819d40ce7b67303396c1c52ce236710b38839bc90a5b04f2420000fff07e4837d81b6c0cf6065b0320018000bcf05e582f25179209420480a2400100007ff43ff81fd80fb607cf03e4a1f240f6c06b602fb016dc0b6c85b602c0216000aa40500027b213d8098004b7025b612d9092c049202430120809000440020901018080003ff01ef80f6d07b603cf01e5a0f2c079383c941e000e0006800336018300c0406018300010000700030c018100c00050402800124008b80449022401090083004100204810200808040202008100006920304018000b6004b0024c01240089004300208010200804040001180086804200206010100800036c01b000c000480020000b000500024000e00038001b000c800600020000a000480020000a000400018000800020000

def C27_patterns : Nat := 0x25556655956655595165159156055695595565159156155755599565959556455855599565557555a556555755595555551552554555055255465515544550554054655165455514544550552554565155454514544551054195059415504540545591554545145451114144550551654559155855515445451510541145445511444450614156055415105241460514055

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

def C27_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0x1016011001000
  | 6 => 0x100bb06b005000
  | 7 => 0x1514f208046001
  | 8 => 0xa233414e004
  | 9 => 0x13909a00e
  | 10 => 0xe004
  | 11 => 1
  | _ => 0

def C27_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x101401381101000
  | 6 => 0x601601681201000
  | 7 => 0x48168169e601101
  | 8 => 0x68179e69e21e
  | 9 => 0x60169e49e
  | 10 => 0x38121e
  | 11 => 257
  | _ => 0

def C27_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0, 0x0]
  | 5 => [0x0, 0x2, 0x444cce01, 0x810805630412, 0x2]
  | 6 => [0x0, 0x81, 0x46dc7200301a802c05400f00a412024600201a020c00c00c0e980101ef026004402c002004010800c1fe03b, 0x114e50050d902d02300305c19146401700100106212406f8a000335900504d01307405e03203802b0eb85205180100703b0ce00a00200800100102201001902a04600f001004, 0x7fd02b003002]
  | 7 => [0x2, 0xaf00203b01951601e00800603c0028320ad00500304a02328400d, 0x139a003139464c1d40163088b2c00481c8bc05dc03a12b8b7811c2d212908c80243a00071af43b000c06b02d80b8004020028037ca6a02f031010027e25b030853800b0e20018e400424c9003804047801e002806401b0ab00e023006800c00b00240901040a0800806400100180540e019585001740041040eb005807e02a02b005e41001800f818000a0b60018064008168001801001709003e80340120bb00541fc326015000800804c011002009400307c000824000304900c40f400408c001802400200100402041a60ee00a82980b8001, 0x31806a26c02b151802800c07c073000400b1060ba008d6e424300543fc03800101300084f23ad8a7813801e117001003c008003004002000244a003007000c3530a4000400601c871000c00206a13801b007a012006003c01200b110435c02603a0750004002432089018c2ba00104f80f000201400281e800210283580d80ba0098240004006031, 0x1101c3e0040204]
  | 8 => [0x6, 0x19005c02641806b817c0030f7010800c10c0b6008834c0420046d982388d109805307f4002040002833c00a01382a809c10c0c304b01b001200100c002007207d005819000802800e00040ae00a00304f400304d017801401800600241240403d6819c07400414300101d002000102e000800200b05180b00900170368eb400c004007800a29c0c9, 0x14035400b00200012019894a410f80ea02510c3031c81ca00070cd000e801800da002401d00010508000c01f001706270bc40220003000a01ec0038008858a058806b804c00690cd0156811f021623c6143803c00040010014007c07ab098c11a00050028000c000800200d403d407a819400160268042046d004a00880b680a8000e0010000806784bd07fc000826301760014007002d00d0028800d8066000201f000780588266009a07c000f00880054037000201de0004004804c0004003800380ca055000280118569000601e6063003000860084009407300040010002010700a8001e02900050010008400b000100ae0024100403d01b2004010e800d028001c4090008d008e0004020000901e4000400e000100120090005000b006a00340040030001203b0009806f002900c4032800800080010070011d00020014004809a001e00b400200030054002402b802a804d002400101380008007c0038026002c016001300010034019e19a000100e40084045000d007200300060038, 0x108f0148496144003174000a0ce8382d0050803003a1d286b402806f06380a60be25602e800400e07600c428800800206f865c01c18a001800e14401200e00040f30a2, 0x0]
  | 9 => [0x350113602, 0x7dbea23b00885115ea21b0a404ac00615e00202bc00e03a02181e00080010518006134034029000400802b005800c016016001002c00600b001c18400309a, 0x91800293914600490634f16c00f0090191d500904c0050940244168e30c900105a00d8da1640191122f705789f0020a200408300105409000601000e89200104803f00414493987d13002b00b00300301901300300705400f0c801301c00300126100105f05608814200e81b0600cd00f01104e03600b, 0x0, 0x0]
  | 10 => [0x6, 0x9288a8, 0x0, 0x0, 0x0]
  | 11 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C27_records : Nat → List (List Nat)
  | 4 => [[], [], [0x195c798], [], []]
  | 5 => [[], [0xc01b], [0x18cc599c7604cf02308f1f7c33c8d787de4611f22308e30dcc3097861873c30e06f06af88a33187861c3e04cc55cb872b81351872e1], [0xe36b1160f0f819298de694d017add3c083e36b0c61717815f09eb606f02b0f81bc185c230dd8379a54783c0c9d0663037893984aa40dd83035b9b18e3454c6874181bc0a8ab3cc7834187c089eb61f022779093421c0d6ce86212cf3460], [0x606decf6382]]
  | 6 => [[], [0xad3dbe1fe22fb31fb81f], [0x56512e7128973813a5ac0de0d5617cb70378375c463984bb74b01178f037b368c34f8c0dc0de06fe6fb36f37bc8aabc0da8de06bce7196f3766939d449a7c2e1178d808fc781be1bae4bced765c752a90c69536e576a832a80d1962adcd2b83365cfdbc7bc14197256f371576e9c0d55d75acc3ebe897381b79bc3e05ce06cc6f0375375c9d1d4a91b3606f0eb0283755c762dd6d987b00d195708cc781bb9bb34207df912e5408fc69547e34a9a32d9a76762aa0c7186063c0de4de82cc3eb889737e5f2dc5e04dae07b9ab2be5bc68aabc0dccdf4b026f11813766800fc3e04de06d26f036375096063cce04ddbe4c757063cb81b41bc0db4da40dde30f813381b59bc0d6dcb00c795e095cb5844b9c2e08de06d86f0f813b5c5f2dc5c88ee04f76703713787b31de36b07c612b8eb08c73813f5ac0df4de0510e630cfc781b39b8c2831c39818f195d73813d59], [0x3036f9b1ac0d58f46612953461c0dee4e672d81bd9ade4559eaa12cf31f0ac4bd12670378b79ae2e06ce2e12f36e61cd5bd8e1f1f8bc099e34559eab17214499de4247e8eb92f4499c0c85106630cf4ae2ac3cd2a97036e800bc0dbe7666b1384499c0dbd8a2e12cf1fe284bb9bf86a49547a3c0dee4a6b036e9b1a8dc25b987035d3d19d0606de2f8d1560a3c0dea6c6b0367929ade45a1e8f79a56387c0db8e86b15813d194a9b88b92b0ee5025a5ae1168f790979a3a94d52a1ea49534258abb583870378b31a76b3c5792bb284499c0c9ce9638dac768dac2f912a7790931b1e04398e8f036f5013c0dbdb8662acf5062ac3a912a62d0f6e61e36b1821f8dac7307c5e064e66b88934b8de695e61f033f3d19c0dbd9e69b89547e1c0dbe102f8cb845a3c5e043c678bbfc0a3c0cfce86b036f2a198b43dcb862acf15e2e06998e1f035d9799c0d6e6e674181b38be045a1e8f036f5f0b84bb8d3a296b831a5c2df51466b109772984b7183878d157323c0dbce86b0f81b319e3455daa61ce563e1c0dbcf4661cf272e1c5e05cc6741813a4ac0d74e869dab845e1c0c00f52703569b1ac560676670f81b799c0c01f70f035593b8de695821f8dac8a8bc0d58e86ab12f5f0d84bb9cd87036f419a8d439cb87035d9e196e33c7f938dac8787c0d5a6e6b79a51f87ac4e17c362ab831e1ae4e9d8374181b30b5c1b87593036f2e99d0606b6a7035b92b8c5e064a6b036f5e8bae2f912a7036e9d99e36b0561fad81b78b84b718f87036e3d19ae4e91267036f9399c0dbe002e12dc1fe1de254d0969f345007c0dbcd26b811a8723c0dbe4a6a2aed15e1de694c6575b81b78bc0c85066b037b489aa4224d2e34181bd8beb606cc2da68c3770c0d6eaae3791b84a3c0d6e50661cee72e1c0d9e4e6779a54593873b9cd870366929ae3454568f79a58d87c0c00e92b789547a3c0d766c6b036f750bc5e051465708b31e1ac224d2e22d0e72e1c0d9a4e652a8f3461c0de8e86b81168723d062f022d2a8e31e1e32e0c6970f819099c0dbd1066b8ec44a967a2cc7c3035d9d99c0dbcc667790960a3c0d757ca7790963a3d0604f525d8e444e1e2e06b6a5d4df44e1], [0xde425dce643bc84b718e87791687b710e06ad379398de695dce60b81b7b1d2a0f79a58b43c1e06bb3c9298d0673036f07a0c0d5a6e2b4181b7c9c4e06df279298d0606bb3c13bcd2b718e1779a584b1c1e83036f928a]]
  | 7 => [[0x7f], [0x877b2b7d6f7d2e7d84fba5bf867bb73fa9bf50f7487bacbfc97ba2bfecfb52f781fdc23fb33fd1fdddbfa63f44fb31fd2a7de6bfa33fb31fac3f467b237e72fd30fdb93faa3fa93f6e7d3e7d47fbe03fe8bf337db0bf6dfdbf3fc0fb2afda3bfbb3f347d36fdc67ba6bfae3fa73f3efdde3f51f72c7da4bfa53f5177debfabbfba3fa43f45fbdf3f50772efd], [0x69a2d4224a8bf4b002981a18ede3a85561402e972d0b194a9e600acf3bd2a7916665fa0c0a25c280f2c8c6a516545e9645a88da80f531942a90dc1f81ad8fde31452fcdc8d126e5fa084a2ac2f84af4c68e9e8b1c95201eae2247571123296bd15580f0fa5a247424d2c250a02af3501e4aa3ce606f63a2ca23d67b305a32805d217c29e4a03d097722c0ba91455da859e2b5516501e5fa251604e86236953d284598e0314552d8a2a00a03dc0d305de1747d62621612be4581b381c098d7ba8c68f78a0178bc085c0d6c6224babd9e8b50e552a95e280f254d0754e6353093d2fc09e8b224f2bf02545f58448c8abb51401128a90bd14c54d9e5c18ceabd16a1406352dc5029a431452c916a15e635327502960280f34ccca7036f034b2a0f8018d1ae0c67a9acd15465e8a62a3d13252a7b78b915813a304a910f294c6a57c6346c53423a4afc5562123a91271f2745afa798c7b1512898aa53cbe501e62254f566721612a1516e9c05c0d9c2ae0c68e2ea03c9631a9a931456058a898ea03d58448e34891a3714aa6dca01758458ec0dec2d2e6217792d0b315115b74bc2e06b63b0269608934afc2dc42becc6a7037b0381b78ea923c7526783d98953d489e0f8abb91616b63f388b50a12a29761a51e06903b8d1511154aa2678fd255a4e3eb25d1f4c458e4da2d4681407b42953d4b9785849517d62701651093146448e5c18d4b3c58a99e3a554b458e8731512f540794e8b51ac8aa25022d4616fa159aa03d6e2e8fac0907e059ec2dc891d590f0f4aa2d4606ca3a792332c04a9e678e156f302397c6946c74b9ec0dbc1ce04464d21e692744afb94b42e2f0239dca13d1a501eac2c87b3c5ea98a983c8c31afc0cacc4f118bd2a8f45bc5f0a9418ccb7d16a22ad645bc848ea418c7e06cc05d4a03d5c2a0f751651cbcac67356f0a953423449a58315447a125d5eea45a2c0d982ef3402a1ce55e9831a9c0d5c76f1123adc541fbc2a0fa34247606cc398a6346c1501e78a54f22cbabd76a03d569d8f62a2d1425b8be96a0172584b090a0c2eba2a89ac8f4546938f84c01153e6214fc1e6942938fac0e87d1a5a15948b454b938f5ca80f6f17a2adcbe148931af, 0x4a90cf425d48a6900296e9605c0af515624e3e8cdc1ed331a94a98d4e0676bf03004581b782de2ec56064ebcd228691567a237115a560443f03581d585e8ac09e97a8112a2745632ec3723c0ca4c5625e15828b51582a0fd02251500ac3d803f3d81ab0ec0b717ba9128b02a051586e0f77280f3b52a8d9c953dbc6e0f94224c230dcbe7056334b800a9c2257b34dc8dd88945462a0fac3cc7a24b8bd2a453dbc8b0ae04387254d0792a423c691d34ac1747d2cba3d8aa03d7e0f0fde6942f1b58017a89455d910f449a5737cc6a67c895f5896856b1a11e70c6a58c953ce55029d6e05171b5c2b03671d815f22a5ba85562283f03441c954628add587d60c63e9b3c1f5c0f0fac3987f1a2a2ab0be15c0728fb74b42cfcac3e9ea017bc9785c2d9c2f022c2a96dc1f6e458ea44bc2e065462df660ab845a8501514e2f02069f001581a58e479a17b152c7ab8ec135c9d0f4496d7d3d7c2b406346a02ea9678d15565cc3d36635381b70ec09757e065061a63d550e50a85c0e0f39544a702742ecf31a9b7c902d21d42a9eea14a01f9e592314522123adc631f093a30c09e8c31d3e7a9ebd14b8179ede22c762d12be9eba157e730f5c0b0f6f0c63db8895e69113493c257d72741303551ccb4a9eb72f45521402e9ec5153a44af449597e994455428b5181aa8dc0dbc2a2cf4bd8e953d5c760a4a9994ae068797c8b44ca332362a84f335188994a03cbd45a2b74ec7d727416b93c1fbc98855f1b91c24c6bedf220adc45af79a54f6068a3b03461d81a10ebf4e02d417a2916635f6e848e6098d4d2116398e9e3d4d318fa94d42b4d18a21ca051499805e345852e1168a912d0b492e8fae3987c39dc8918545f83b3055c0e8f5ba621696be153c44af579994d25123b8dac156eb3854495d7f01402df68b514c330fd022d14052a7a12bd45462e8fa42247519163a96631e951f9ede4e02db9b83eb8e41f52340f8022d12f9128a12bb450967b061254f4258a8a7e740acd31a3de59c2d36661690541fbc938f459a584399ec2a2be15582c8fa41747db98a291c635eb8159eadd547ef20029308b514b848e84a8142e11673035d1c893d2f60a54f22ce8c22ca53da55115, 0xa64c82d35183ab0281f46318fb749c7c7d2a7b036f0f095e22], [0x84b719fe3036f699baed5a5e77032893d977254c79696c545abac31d2a9f036f009bc0d5a6e6e2ce55065ae3b0a8b7419cc0e3a5cc4c676b93a489dc0dbe1e6f2d81ab3a63a54d196349545e363a54bb972d81b79bd0606de2e968b31b96e25517c6913c979d84b718f8edf21849bb7c85166e12cf5072b7c9e4a75228a34f8ae24512e612ee3769de6962c3f1781b79ba92547e9e90892a39c7e06de6de6dc4ae58b439418f0b5d5f2dac4e03c77036f939bc0d6e42e6df21319dc0dbc2c6f0b5d44b9c5e06426f4181aeabb7c85126d9ec71fe6c0d764ae97c892a697733c57999ec70166a44f112e5a6b845e3ac2243ce6a4c74aa7c0e06de6dcac55065c0dbe506ebb4844b9c0dbe4a699e8b15f26e2547f962d0f4c6393b1d2b96b8ec48ad5c18c5796912f371da42f8dcb71785c19ba4224dce70b83b39b69b15178e50c74ac77739541962cdc48e9a5b15409e12ee7363c0dbede6e78f34ae5de4258eaf78f34aa7c0d766e6f0b83aaba8dc252b8e96d345b35c22c578e2c9545e3d0606512f036f939984b718fa62d0f6e69de31d2a9f4b0963e3c2e0ede6f4b1687e3c0dbe4aeb036f4a9b7737d2b97036f939da7cd1ac3e350e5063a5cc58a3f037bb79b8b43d378e90c74aa767ae0579b035d941bc5e06786d7c690f6cc0d743ce5a6c531e56798c57d30d81b79bab4de4e770b5d979dc0dbc306f036f489bc0d5a6ee98e9544e38b254c79779166e2dde25516cf79a5638fc0dbdcc6f215d44b95f224dda779a51597ac3a83cb69f344a8fc7e06bae52a6715e5e039540d62d096e69873b9418dd8892a69d0606acaedcc74aa78b43d2b8d7cb244e369ae0c79778cf15b6a41a43cf1228a377884b052b8f81a6501784bb9b9a70781adb9c0dbcdc6e12951fe363a54c7952a681fe5ac2f83cb612dc15f172b1d4197037b909b9e425dda5d4df0f6579a54dd970781b79bde42456cf03569b9ac0d9e426f076e800fe0315409f036fb31baec943cf3b981b79ba42f912addc9545e3c0dbc0e6f78c14aa7c5c843c76b8914539e031d409e2acf4aea751a43db302c74ae3c1e06ce6e12c74ae3ac24514e7036f451b8b281238ebb2144b9c0d7678762d0f67e3c2e0ce96ab8892a3967b1c3d9a12ee7361a44f17cb5dce64b658aae0578d8a8b31e9c0d5922e99ec70266aed217cb741569b8fc0dbe426ddab815e5c0d76786512690f78d0672de3f791b4aa7a5cc5166f035d9e1b67a547f9b8d1569aba32f4bab62ccf15e684a54c7c6bb3c929dac4e1d43d2a8e15e37739941958e9547e3a5ae0569eb0690f3cac4bc3c7781165027d0606de3eb0ee4aadc0dbc566f79a5849b84bb9cda61ccf5072c0dbc166e96d331b5de4259eeb037b9b9b79254c795e4e55065a5b3c56da8d2d5e8f8a244dde278ee5065c2e0eb6e5b8cf15f4aeca03c77810e5033ae4e8a87780ee5027de254c6d6369548e36e3052b970b83bd9b8731d418d9ec715e6c0dbe6e6d8aa045e377280dd97791684aba44bd126d8aa031e5, 0x3036f93b9de45a1e8e969531b5d0606deaf036f0f1b8b43d418e969545b3d3e06de6f033b9459a5b14c6b70781aabad6e06512f035693b9c0dbd8e6d7cb237658abb5a7a779a5638763a54a995a68b31f1de45a1eaf418193e9e36b1a63d8a9545e384bcd2b8e1ce55071de695dc3f036f011bd05be4a3d9ec515e6de425dcaddce64ae5c0dba506e2d0f6e61aed597cb7035d7339a34b4ba75228934f8c0d9a426f036f929bc0d5a4aea2d0f6e638db712b97035d93b9699b875d12a8f1fe39e2f913a6b138731d4aa2cc7c69ec14aa784b718f86912f5f0fa331d2a9f03213a5a63a55178f78951fa7c0d7678e7033f941b62a54c7970b833d59de695b87703213d596e31d2b959ec705e6eae06de6e12cf15f2c0dbe786f790963a3ae2243ce612cf63e3ce606de6f035d4539449a4a9e30356941b87315418f8cb815a7a5b1d2a9ebb5644b9de45922af79096e39], [0x606df2790998b43d9e95c5c7e0ebb4e1f791687a551e06bb3c9099e3f062d0f4785c1d7678670b83ab4dcd45a1edc4ae184bb9cc95c36f90b1d2a1f790963a551c259ec74ae2e3d5a2c91551677244dda378dc63a552c5a1eee736184b718e95c3a0c0dbe422f78ee732552ef34ac74a87]]
  | 8 => [[0x70e5dc2], [0x4d3835386938d438d33820b8ebb8de10b7116eb81d38a59333380c38d4b84db87eb861b8504c34382b38ac10ae104f38023856b81fb80cb8d538de134fb8d1385ea645cd463182388db86c3831b60138a41216b83fb817b8303848b88838363862a6dab8893825b86e38a5912f38813812b866385ab855b8d8b8a69007b82eb54ab82638a79339b86a38752713388a3803b8d9b8a41344cdd5b81a38dd3844c086b823b8573887b8ce38173873382a410338c0cd32385b388e382a3622b86ab8093831ce88b87b3847b167b851386bb82a384c382cb8903884b34b38213819386fb804b827b8cd3824384cb8e01072b57ab835b82238313854b86e367c38633808b81ab8941b57b8043879b865b8393853b8873193b65ea70f380d3863b8802712381b38dcb821b8d026333515b864b845c7dbb8a41111b83b3883b8ceb84bb8a910d0275038d2386738d938ac1341b8073826b8b7120db81db85a381838c0b2493844b2c0b377b814b868b8d0b8b91062a76e4152ab1cb815381038a592502c2eb650ab93c12b3570383d3687385f27502d7d3853386238504611382eb874b8143813b880b87e3845b373b85438683884cd84b81638613834b874388eb8a313ac1159381c382ec132b819b869b845b138b87f387fb83bb8a310203806b82d3844b331c1c0b15f26563859b8de1271b81eb88cb86e350b38253884b10e380fb8, 0x18b858b837b84e3805b849b844b150b8cf38a490de1145b200b8343589b87cb81bb8ac120eb8c0c0d8386cb83738b713bf10ac906d38b710502b063884c0853831b87a383ab824b831b5523831c8553852b845c0713860b8efb85bb884b2a6103a38a590583864383f38273878b8ec3882b82a350bb81e38723810b88fb82fb870b8d3b8a3114a38512b72b875264eb87db88026a410a31285b8cdb8], [0xac398856270169663213e0f358798dac25ccc6286e6b31171a8f2815d192a42ad271ec50f256e005ae9e9042b0df21489b909781cd37130d68c5d1ee645b16298d2c259ec2910f21c1a3103718dad768c4378c7215d1035449518b9930ae900721526390d3e058d2d2a41d46e4b832b358b43d8e0404c7874820a0372b8da458d35cc422ca04a8b05b16e371abb916c5120b62c115ab9e2c9ab14569576954a95162b6b2955cc4c6d74e636b85bd90a5cf083147e96b01e1f9345b18da552af4dc9696012167059aa60e081403cd4dc226bd4b71048a298b5916c779bc20c747b1c0c858b7c04ad12076291433187975ae5b02c696e62116502bde398822cdcc7b98162c74a9eac34c825468ae4ed36ba7b7106398daa24dcc7076e210963b1de424818c74d5146e6af773355c0092c59407ade896383a4109e371aa0816d52a636b85b71063a615c3d30af0a85626915b7d281cd5216442b137205415b56b0fd2ca03c6abb4820cf0137c0861898c5ed6783a6ba584b15f0ad29d016df70e66ac14aa59e2258a803caca41e6ab815ab7ab71aaf43c95b89b6acf502b6e01dad1a1e435d4b214b0390d3d2c852da641820256d32a35b743c84000497067434e550353c079acd00e6b8f4321819bb176b4dae9cbad5a6a057372b35448ad8dde9640d2026f0977228002d2a3074c5d42b4b4b628aa781c86f03040e81e6f466990a7c3c82c804ad4a6e57c7e0906998dad18304379a720ee733537091ac3e12c5b81e6a7a15b5732815c5d2a951484629815ab48951adfa7843400b4b5da090c082d8af83c96dcd3215d929062a80f4bd12c6701e6ae55029d282cd606de164e956b31059a2a009ae2dccd61ca0632737359ba895ef00e4379091d83a31097888d15002d6b891209515aba4244831d4096b01820dc48b58b22d8c2514c58a954af752aba68e882f8dc951a8b63164aa52a02dac3cccd63696576eab1037151a9b8b2d7836e21a015a54b0ad5c252cc7032562d331ab4a8e95e0d16c67e0820b94aa5c0dbc72f81694c6186b460110a44bc2950a8d4d2546b5d1135800ad2b151689a63857c1de1063a6d5d1816430758206315b5451a5adb830421201629142b1, 0xb051886f22c29362b576e0f10a452084f140ae0c0b4bc9a59072151ab9918c68cc7213c73352e81da98cc6d70b462190a410c0dbc0c2456c7854621a7502bab5048314169702d36385b2903482dbdfeb043074b20c7502b772552a5470ae9ec1212505b79f399ae06de425a073585ae9050a455b14dc95cc636b67039a6e255adbeb041162c634801105f8a129a43cd6de636ad32eb5a34dc8662ba430b6f21569390a5b1c823804c6f56e2128011ac198daf014042990f216e1590a58608616864383562181ab10578e15e061ec57a024a8b31afa5a448646ac42dc0b21bc37106e061ad92b04212dc6a5d00b5a7b4c85227841646e6adc0135de24484bc406add6e207a05b5de6942c2416c4cc386b580590a324486168441702b3d31039a7718daeb8c6d6b8541f6e00904a8bd5c252ac5e69b572705b59f089a9b850d6b01e2181ab0eac3987f338242912f218384b16e0adad18dc43022b63c7a09073175ab98d2d6b26e2148059062a815c9456df9f5821d2de10a48a0835942af4e89634b37108f43d8b5944add4024b5815905001d5b5940af834b21deab10de57485768442b85420890c3169a258cdd40af68a057465e8ada289598c0ed57a2b4b2d059aa307884dd16c70b670b813731b757486064ec706a05728371aa4078852c1641120263caab10ac1b8820416dd12286358ab10de2548521a643033c634b9885a42f8543db8d61e96568b31b534879a60650c6b13c20ea05a5449517c003c97021e631344b1edef0843d22c64e026b0d84b1a40ac869ca8d70b58208a44b1e0d0881a07ed4c61e6a8b01315c0652b3c3cdd9a3a4ad331a945a2d8d60044379a520912b35909d0d43d36afa156205d14352d879a9743cd5b0a056b244b1752552c590ec74edc6b8193af448798d3dcc41dc596a631a358da54f5600242b10f20ee502b5eabd2af4169778d320f34aa5ac01c84f112bda63457586390c0d7483992cad2a3f3da56e354518dac3d16c4dc1e6ba001259f82c86d9b8d7793c20c72a3579a54f6f21e40c6026adc3735a3518822c30c5225d6a541635a5808839540ae8c012148639086b71aa50a8d4dc3a6b854331d3a2d8d2e1e40a61e6bc66990, 0x458ad8f3b78422c9b4bbcb7907d8095ef1b840c60b6b85c1b18481d89e804d77802212131b54a98d5cde12c7382b56d317abd3d188314c6d70b6720c7501ea33988224dcbedc9121972b3563975adbedc42e74621250137a32bc84f116c6dea056e92eb569a2d46f2ac41cc9b57729b90a90fc8522783f782b21460390698b15c259ec6c54b208b00b1d722d8b14049690891d56a19084b717cf212c4f41e6ba0372563a565d5a8c424e2b6ac74a9f2e861ae7004ae700735da84b1ab51086f26e41be2b57bc00905c01d2ba8d2970b5620a0502b500055abcbad6dcfb21096e31de0788576ac41a62b573145b1de33c84943cdf036f630f44b1d02552bacdc951201627415b79e0a1ac7212c51638636e0110ab52c85be964302e662dc05b5500ad5c6916c678226b8d44b14898dab4d16c5ac636a952a35590e95e0522c6006e4abe0125aed60817456d5e66e6abe3723e5ef085be9042126e62e66e35d72815af9128ab069211e50ab639a1a9d004dd2a5d6a8b0f31d32815d76964290e6210948b160a54f22cc6c55e1957c0500b848798e9eb04303283156a410d2a60d24512c58e8b63bcc290a4004829c56ad168a63483710c1e058c55a6c678596ba00f25500615cc45e68ba026a9545a831805ac3d08c6b095206715b5478fd8b1d2a96b09120670135590ad5c3940ae9e0220ca1c25a587884dd12c578954b8163b187951ad2c5643294b206703b5b7d04862adc417a954b6e3a10a5a2c745122c5cc89639cab10b701c825512c678246b0984b173151a97416d69095208944b163a5505bd16c61202630f502b7918dad1a5a162c984b4b9b90ac56082f964974f09632763b5a598c7abc56ae428b62690f37c2d2082812aae502b34b815a563a595bb94096700b35462e9090c258ba83c969e2b20f7502b5000959b8bad5b8c76a8d31b594254d4012a97020163270f35b7254834c74ae974b21c1a410c5e1481500ed5409156cf15aaa406085d69040a81e6acf15ab4581d8db8dc428d3c213c0f35c2a118b1516c51c0763a0c0a25f2552a8016ae2c636aee52aba30ac8425a6c78f4b2181c0b1c0d7476f01641dc964b3731b57d8ad5ac848ae1ca0519cc0b1, 0xc081d8bb940798e89631d2a354a8fd2974bad59e2b6ecf05b74a98d4e3f02c6df0963090c3190a258a4516c5b8d36ac55025e0d6084ddb8d5cc6e6aaf012b28879a95030d70b4b216e9e10b74dc86f1b83d1c2b63ae512bb739886052ac600744b1642b19402cd2450ec678636b1650abc0a298e2c3cd77983212f059a6298d1ae04895dcdf6b6e6390b7c84360d12c70b4420dc67b54aa2d8d2e62427a636b6fa310], [0xd745a1faf4ac74ae78b3712bb678c74ae763a543d9e129515f3c2d75ccf5dcdc4aedb7c84047f0b83aebb8b43d2b8e78be0f6d63b1d2b9d126e0f79449403de58e9500e78db1d2b9f032890dba41b83cf5b0c74ae769a2c57cf036f909b84b1d2b9d2a8b15f3b7c84dc7d8e9505e7b7b1d2b9f78ee4aaf48a28dde98e954ae7d3b1d2b9dcad65075a34b4307f0b83b79baed583cf5dce64ae784b3d2beab0500f3d67b1d2b9d22892a79c2e0edeed7c6e0f6d62a2c57ad8e9548e7e3f075cbde6c74ae769b14579d8e950b678b3992b9f035690bb6e31d2bb52a6315f58b254579e2d0f4b73a5b1456be6ec74ae77739937d6969515b7b7c852a7e12c74ae3c2e06516f78c74aaf48a28dde7789515b7a598c56f779164aaf6b31d419f032790f948a28dde2bb480f3d8735941cf0b5d9e3d69ae0579edf21159fa44f03cf61ec74ae75f2c83d9e96d315b76b315419e2cee376d87a44ddea12ee4aebe3f062cbddce64ae579b992b9d8e95026763a547f9f06c74ae7b7c843c7d8e95016762a54579f79094abb6e31d2b9e912f0f1f9e4dc45762c9548eb84b712be5acd315f6aed59ccf778dc4abd8b4252bad8e9537679bc3d23ea90500f3d87a44a9e62cee48eb63a54579e968b15bb6298c57b70b5d0f3d8b43d2b9f0b83ab3baed5a78f5166315f9a5cc4567d8e950c676e25457d6df21059f489b83df112540f79a42f83cbe78890f794a8f8579e2cd650677331d2b9ddcd6376da317430f7035d90bb5f2243dae7891457963a540f9e8cbd0c2f8b43d2baf8f568b2f77359419f418190ebc2e0ede7e2d0f6b6b84b1d2bad8aa015e7a42243cee78ee4aed8dc3d2b9eb8912a3de035940debb210f3d8b35923af79a54a9f6e31d2b95a66315f5d745923ad9e9515f6c2e0e516ddc95376d48a28a9e5dce64aed77254579f78c74aa7d8b1d2b9f036f90bb69b1d2b9e2d0f776b], []]
  | 9 => [[0x283d8ae2551731213a7eee1bc], [0x13853386e3569b9014f6e3863b902383738543884b887b8503805be23b826384ab96c3815be014956380c380c390b382eb863bb03bbd3bb4abba59087c2c1b94c388eb82a3548b90c4224b801420cb83a384539b7b931b88b4204389e397db84db8013e67b8013b1c382eb534b8013979b89e4205d273396fb857b81fb8a41005cf1a388a3825b887bb373915b848b81d384acf0f3b11389bc210380f3e373b0c3b4b38ce38374f48c20f42073884b100b803b948bb05bb733815cfac1090b96b4205b9d3b93742733bb7102a3815b9b7c24ab84ac27742143869bb69b8d3c253b8d74245b115c2d3b817b803c27342dbb803c97b384a3887b905c20f3815bb0f39502b44b1d8b80938de10a310173812388db860b8c0b103b863c205b89bb931b516380f4f2cb8c1c263b815c969c2d9b85938], [0xd3a47fc5a1fff5d0fff214aff5d81ffb1457bc0e01ff4405ff7302ff9c057fd228af68005ff0a01ffb1d2bbd222bfec7017f8ea47fcbc3dfd142bfed6507f0f063fb1c31fddc95df1b87ff1f00bfebb4ffd2a6eff3c737fb787bfcdc05fd0c0bffb369ff63813fcddcdff4e2bfed650779b88bf8ac3dff4e95ff2105ff6387bf84017fede02fe9103ffd739bf9b817fda602fe912a7f8b0affc51cdfd141efe8b15ff878aff84c0fff8fc17e14017fc1823f91c05fe5802ffb1d3ff879bbfc84ddff78957f1603ff878e3fa443dfe2d0ff716017f9e00bfc3d23fe6e2bffa7737f84a57feddcdfc3c0bfe6e377f84a57db9831fc2002ff8305ff730affe9e1ffda62befa763ff6987bf81405ff4e07fec703ff63a573cdd2bfd9e95ffc703ff87863fd2c56fe78d3ffa7017f8781ffcdd8fff0321f70f737f87a57fb4c0fff0602fe1803ff7307bf82c17ff0a0bffa7d3ffd700bfcdda7ff4e6effa70c7f9e083f9b80ffc5607ff1b63ffd38bbfb1457fd162bf6e6377f69b1ff86005fdac02fed315ff2800bff1f4ffe6f0ffe500f7f9e07bfd1830febb567f370f7f4a80bfc521ffc0602fed863ff87b1ffe0c3dfe786efe0a03ffc2d59fdbc17fc3c02fe950c7f638afff0417fd226efed34aff9b9bbfb4c33ff0b6f7e950f7fc1b1ffbd9a7fce00bfe912a7d4a1bbf8780ffc1607fe1800ff451bbf9b857fdcc02ffc1ab3f4880bfa4523ff062bff16737f9e257f9c005fd1402fee61d7f69893fc3c3dfdb895ffb3d3ffd7263fb1d23fc7c2bffb163ff318afea540ffd121efee669ff4a807fcdc17fda6d3fe07017f3807bfc843dfc3c1eff3c0f7d4aa47f97431f4b202ffae69ff6c34ffbb857fc560bfe8a05ff63a57fcf057fdcce6fea805ff6b0aff87803fd2a2beec71fff8782ff9b83dfe3ad3ff83377f79b9bfb1d8ffdcc91ff3c05ffb7a57f86031ff0b83f60b00ff8b34ff82805fd2218ff0f48fb37063f81c0ffddce6fee663ff15863fe9da7fdac07fef6737fab02ffb59a7fe7c6efe9515ff699bbfe16bafe6e2ffe2b00ffd387bfd203cfeba0bfe0200ff4a247fe0da7fe1f0ffe890f7b73257f9403df4ba18feee03ff87b4ff9b83df5a618ff0f017f, 0x4b05ff450a3f98c57fc7c07feb9017f731bbeb4c17fd2a95feb20f7f5f07b7a4417fcdc0efe91167f6e257e82c05fc0402feee737d3700bfeb80fff4e0bff1d87ff7700bfcf18ffc2a0bfeee69ffb78affc592dfd8e6eff3115ffc1a57fabc31fcdc34ff3c737db7b1ffbb937fd8e0bfe1805ffd384bfedf4ffca00bfe4903ff6385bfb980fffbb0fff2115ffd2a57fb4d23fe2c95de9505ffb79bbf8ac05fd146efbae15ff7b1bbf8ac57fde6c7ff21017f], [], []]
  | 10 => [[0x70e5dc2], [0xf7f0c7f017f69ff4aff48ff63ff03ffd3ff737f15ff87ff05ff377f], [], [], []]
  | 11 => [[0x7f], [], [], [], []]
  | _ => []

def C27_S (s j : Nat) : List Nat :=
  qGroupedState C27_initial 5 17 9 C27_patterns C27_values (C27_counts s) (C27_specs s) (C27_records s) j

def C27_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C27_initial (C27_counts s) (C27_specs s) (C27_seeds s) ws

def C27_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x451,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4415,1)],[(0x5000,1),(0x1000,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e02,4),(0x1011,2),(0x5000,1)],[(0x5054,1),(0x1030,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e06,4),(0x1013,2),(0x5400,1)],[(0x5400,1),(0x1020,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e09,4),(0x1003,2),(0x5054,1)],[(0x5454,1),(0x1000,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e05,4),(0x1002,2),(0x5454,1)]]

def C27_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C27_rankPool : List Nat := [240336203, 102773001, 236077486, 137440591, 169062760, 203668778, 68338125, 201441678, 201401612, 136428843, 171064618, 203438512, 135512461, 67320136, 67219784, 203472138, 237023497, 67157258, 167854350, 236108076, 33631567, 169916848, 167983400, 134292748, 204487088, 68173067, 167884104, 100876749, 135446797, 236077454, 68301160, 240336171, 100876685]

def C27_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16] => (sum6 r11 r10 r15 r6 r5 r7 < 3) || ((sum6 r9 r8 r12 r0 r2 r3 < 3) || ((sum6 r14 r13 r16 r4 r1 r7 < 3) || ((sum6 r15 r10 r11 r2 r3 r4 < 3) || ((sum6 r8 r11 r12 r7 r1 r5 < 3) || ((sum6 r10 r9 r15 r7 r2 r6 < 3) || ((sum6 r13 r14 r16 r5 r1 r2 < 3) || ((sum6 r14 r12 r16 r3 r0 r6 < 3) || ((sum6 r12 r8 r9 r2 r0 r6 < 3) || ((sum6 r11 r9 r15 r3 r2 r4 < 3) || ((sum6 r10 r9 r15 r4 r3 r5 < 3) || ((sum6 r16 r13 r14 r0 r2 r6 < 3) || ((sum6 r13 r12 r16 r7 r1 r4 < 3) || ((sum6 r8 r10 r14 r6 r0 r2 < 3) || ((sum6 r8 r10 r12 r3 r0 r2 < 3) || ((sum6 r10 r8 r15 r1 r2 r6 < 3) || ((sum6 r9 r8 r12 r1 r2 r7 < 3) || ((sum6 r10 r8 r15 r1 r0 r2 < 3) || ((sum6 r14 r8 r16 r2 r0 r5 < 3) || ((sum6 r12 r9 r14 r5 r1 r7 < 3) || ((sum6 r15 r10 r11 r2 r0 r1 < 3) || ((sum6 r16 r13 r14 r1 r2 r5 < 3) || ((sum6 r8 r9 r14 r6 r0 r5 < 3) || ((sum6 r12 r8 r9 r2 r0 r4 < 3) || ((sum6 r16 r13 r14 r0 r3 r6 < 3) || ((sum6 r11 r8 r15 r0 r1 r2 < 3) || ((sum6 r8 r10 r13 r3 r0 r5 < 3) || ((sum6 r13 r14 r16 r6 r0 r3 < 3) || ((sum6 r13 r8 r16 r5 r1 r4 < 3) || ((sum6 r14 r12 r16 r4 r1 r7 < 3) || ((sum6 r8 r11 r12 r4 r1 r2 < 3) || ((sum6 r11 r9 r15 r6 r5 r7 < 3) || ((sum6 r13 r12 r16 r6 r0 r3 < 3) || (false)))))))))))))))))))))))))))))))))
  | masks => C27_rankPool.any (fastEntry (compactGoal 8 9) 5 C27_coords masks)
def C27_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C27_patternScore (C27_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C27_rows : List Nat := [10, 18, 33, 44, 52, 65, 76, 84, 3, 5, 9, 17, 6, 34, 66, 24, 96]
def C27_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C27_rows)
def C27_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def C27_ori : List Nat → List Nat := literalRouteOrient C27_literalRoutes
def C27_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 9) (compactCover 8 9) C27_S C27_N C27_idx C27_ori
    C27_patternScr C27_patternScr s
def C27_F : Nat → Bool := certAt C27_Z C27_N 12
def C28_initial : List Nat := [0x792, 0x94c, 0x18a1, 0x2468, 0x6205, 0x900e, 0xc070]

def C28_values : Nat := 0xffdfffbffdfdfd7efcf9fbfdfbeffb7ffb4ffafffaf5faaffaa5fa0ff8f1f79ff66ff60ff47ef478f46ef468f30ff28ff275f20ff20ef205f200f07ef070f00ef000ed7cec78eb7deb4dea75ea05e97ce870e7fae7f7e7f2e797e792e67de678e675e670e66de668e605e578e4f8e478e470e468e400e375e305e2f5e2f0e285e275e270e205e200e170e0f0e070e000dfffdffedff3dcf1daf1d9ffd9fdd9f1d97ed97cd94ed8ffd8fdd8f9d8f5d8f3d8f1d8f0d8afd8a1d87ed870d800d7fed7f2d79ed792d47ed470d27ed270d20ed17ed170d0fed0f0d080d07fd07ed070d06ed04ed02ed01ed00fd00ed001d000cffecff2cd7ccd70cc70cb7cca70c9fcc97cc970c94cc8f0c870c800c7f2c792c770c6f0c670c5f0c570c4f0c470c400c3f0c370c2f0c270c200c1f0c170c100c0f0c080c07cc078c074c072c071c060c040c020c010c000bfffbffebdefbd6ebcefbce9bc6ebc68b94eb8afb7feb79eb66eb56eb4eeb47eb46fb46eb468b40eb400b20eb06eb04eb02eb00fb00ead6cac68a7faa668a568a4e8a468a4009fff9fde9fbf9fb39f9e9d4e9caf9ca19b4e9aaf99ef99ed99ce99af996e995e994f994e994c990e98ef98e198bf98b198af98ad98a998a598a398a1988e984e9840982e980f980e97fe97de97be979f979e9792960e950e948e946e944e942e941e940e9400930e928e921e920f920e918e914e911e910e90ae909e9090908f908e907e906e9060905e904e903e902f902e901e900f900c900a900890069004900290008fde8f92896c895c894e894c882c8800879e879a87968792846284008142811c810080a28080806c8060804880408028802580208010800e800c800a8008800680048002800180007fff7fed7fb77eed7ea57ea17ce97bed7ba57b4d7aed7aad7aa77aa57a857a0578a17797766d760574687305728572056fdf6f976f6d6f4d6f4c6e6d6e056d6c6c686bcd6b4d6b056a856a05694c67fa679767926785676d6768670566ed66e86685666d6668660d66056600656864e86468641064006385630562856265624d624562256215620d6207620060005fb35aa159ed58e158b158a558a1579250245000494c4792420040604040402040003fff3ffb3fb33ee93ea13ded3de93da13d6c3cf93ced3ceb3ce93ce83ca13c683aa139ed38e938e138a938a538a137fa37923668356834e8346c346a3469346834003024300930002ffe2ffa2fde2f922f6c2f682e682dec2de82d6e2d6d2d6c2d682d4c2d002ce82c682c002b4c296c294d294c28492824280027fa27e82792276826e82668260025e82568250024e824802478246c246a24692420240020001fff1ffb1ff31fde1fbf1fbb1fb71fb31f921ea11ded1da11ce91ce11cb11ca91ca31ca11bed1ba11ab11aa51aa31aa119fd19ef19ed19e919e119cc19b119ad19a519a319a1196c194e194d194c190218f118ed18e918e518e118b318b118af18ad18ab18a918a718a518a318a0188118801848182018041801180017b2179e179a179617931792148814221400128412031200118c110010a010811080106c10681060104810401032102110201010100e100d100c100a1008100610041002100110000ffe0fdf0fde0fda0fd20fb20f9e0f960f930f920f4c0dcc0d6c0d5c0d4e0d4c0d200cc80c000bcc0b5c0b4e0b4d0b4c0b010a840a0009ec09dc09ce09cd09cc097c096d096c095e095c094e094d0948094409400930090c09080904090008d008a0088e0881088008680860084c084808440840082c082108200810080d080c0808080408020801080007de07da07ba079e079a07970796079307800580050c05020500040003800310030c0302030002820280020001e801e0019001850182018001780160014c014a014801440140012001120110010c01080106010401020101010000f000e000c800c000aa00a100a000920090008c008800870084008200810080006d006c0060005e004c004a004900480040002d002c002800240020001c0018001400120010000e000d000c000a000900080006000500040003000200010000

def C28_patterns : Nat := 0xa5565659566555955255194564558555d5565959596559955655195164558555995659595565459456155665595564557555a55665595564558555d55695595561557555955555515525545549551552554655165455465516545651551654565156455495515945591558555

def C28_N : Nat → Nat
  | 5 => 25
  | 6 => 341
  | 7 => 0x66c
  | 8 => 0xaaf
  | 9 => 968
  | 10 => 28
  | 11 => 1
  | _ => 0

def C28_counts : Nat → Nat
  | 5 => 0xc00c001000
  | 6 => 0x60cd07a008000
  | 7 => 0xe1ad42b085001
  | 8 => 0xf46f52c1005
  | 9 => 0x28a129015
  | 10 => 0x17005
  | 11 => 1
  | _ => 0

def C28_specs : Nat → Nat
  | 5 => 0x601381101000
  | 6 => 0x381781681381000
  | 7 => 0x381701701581119
  | 8 => 0x68168169a21a
  | 9 => 0x71971a49a
  | 10 => 0x39921a
  | 11 => 281
  | _ => 0

def C28_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x119c6, 0x5e5001003, 0x0]
  | 6 => [0x0, 0x322, 0x860ea002002811815000356c872401e30d02780181ca001018817802303d052000603d01d00081080040d3011c1e8168009, 0x96001c01102a901388abcf2d0007000800040058001005801e800880790208004c0ac80020dfc00580b580da0006001803000b5001401280e940cd0004000400380180012016c02f80e6000600740338003010c00140248002003a0114007000f, 0x1585]
  | 7 => [0x2, 0x328448e80100480908c0053c8030120747d00209c6f40d8720de0280b44702e61c07002876128060011263dc02040, 0x18d008006d00b400651ec00908c02ea112c0ce1050043000402102341182720812081e3d901c637700200511ff80d730a0547000801a031c01d01bc3328afc17b00900390004024000420a002008f03104da01f406347dc0db0de801b045800104d4041200409a000c4ca000400106e626800ec00b899c0020004166020c00302fc3db0114193000800202e000f001800500042040118013005405c885c29c002c00201a4001011242b01001050004002000a42b0068089001c42b026c03b038c23d00a01ed025400300da42b00280b90114073000c082009c00700c0009883c00100080040030040009c1cf01e006600ae42b04680b402180031b5800a016c008000801c009c092001000300841028814193000802200380020020029000400602340170004010003404905ec0e4001413001180010064006002000c003800600400030150001016400100700020008002001400400140090018001000402d000c0010078004000a1d9010c00d0084003002c01d0044038000c00d87580280008001001028f09dc24b874c04c019002a0054008025000790ae1c4000800c001000100b0002003c0c7000405d003005e002410b031c00103ec001001c0048338025006e0690014047007c001009c05c8064038, 0x202c6000c4fe06a40010025e8e04c408b002c21224f01f206500010e34004001400c00900c7015c02f12205b10178029004c0180064127000800e00180070108047003004b028c19508b80270014115001401a00061ad02440b1005000a00880fe86a40fd838c070000801d00042fc0018005026209200040a6025c0020264001000a076000c004001405b003400b000a062003002c064c02f004808400a0013000c009006400180c000a002601b0088004001404e000c11705c8001, 0x3280b9]
  | 8 => [0x49, 0xc015802c01412a02695ee43a00200595d8a5c00a1368b080a600212807ea26002163184310e4b4888880a40860b203b008c04c1fb87c80b003406a04c001885e00208a0170b84028013cb040c201c114866800800209a844e5820ea003001813400800382dc1b92c1003002417814e00f0080392035001000461804d12700082a800d00386001e609402885100d8022868894c0140288538028036098001801612410f010000406202d003800c01e02902784080040090a488b007c0280e6800417003600e00080a003c000cb0401e02600208cc008008092801c2a803702d0030012002033003401403703580302a00340df005000801284700b800200603f806400200a8128064002009000817c02001e02d8008014001002801000e015, 0x2db47f7003161ada02b81c1804820847100c00041676f50d9801dd5e1f9000900032200400ad9fc0b23b661157ec03c716aed001400200b03781dab90001028818409e24c45b85980a4008006165000802302880341e205200a001809819c002001411e22b028800c07a03d00080e83e0012000803077400400083303e000503e800c07602a00300a001201500b0e2000614d08280040040025aed6602520060238508c0a0fc11f1e5805e35a071819003a018006011c0662e000680283d2006003267018203200086f40020420038470046003ac9192c06000a0068060002008008802028c004a9d804c0c14ef001800461a0a524a801092425a1e08014c8603f09803b4004492006003800c0aa00100241c4108a6a006698001c00110b4073470034000c01201400381405340900bbd16685603f16580580140bb0d583cc18400e01d000c06c00405f80a40996f500207cc02a01d043002c05600123980080496f5022805001a6080ef800e85421004d017400a001014810000400b01500b81a209406100140a40110ea81141aa201001020000e01003180e004d426a0b5bd403a04f09e8212dea01b02b001a7aa057002800829606f0088f4c010001001003800202702480880720c3000800804220002300040ba01101f001402404802400e4004024072800412400301681926e40af001811029000100103cc02000b03d007001d323007821402200302180ec28a6620008028004005002001803e003000802c00531e007005c0e814501280140b603401b0100082041925c73c00607807201d00216f501300ec1b224d030801c07c0440120458002014002000adea17408e46f40fa00a009800c062001000dbd409605602e816c00c002007816003e00c00100400071ad0334334142004001800c08f0c700881100030b901780060f6017001001400600f001800c004038001000400a00700980c005b077001807c048013002016400411900500060da007001000607c003, 0x150020ff8144857006003809306400c07940040081e80010002008059c3d14d40010b6001000801b003801454611482f000483a1d00c380ec0ba00800104ce05e17300c80e405c00101d00147c200e016874806b007007030e1e800300082e0032006, 0x0]
  | 9 => [0x2954e40c3002, 0x122281a800208b8183000c4ba235000a0804010001c00e005406504c41950134001007800603180080a9400d0110015012a129007001601b400c0130003015407e818009b02040010130033005c02501580210024004006c029001805900800140148003000402984a401f013000f0050041014c02100040080008007002c0020070001, 0x900f007d008cc6700104d300300260012253140021b0efe23b000c21c001851b07e6231049c24901661fe000423e052c020017228a0004032017c01902f80024c10435000800e01cc0c501640c600140db01bc011012002006361e304601298a28028872409606ce17c00ac02d00600018a288ba85320da01f4026001c34900a00070250004024004c0b2c0140044075043c1c9000c00383280010038010018000e00a00118298001006c00f0014014002002202320a502500080034006040c00901a01df0004001071c00407f801309300040004033005c002006c01000f802d009c01a03d8003014e09b00040100498006002402102400bb000801a005c00e00600540038009000c004010c003007c04b037000682400060004004, 0x0, 0x0]
  | 10 => [0x49, 0x2ba33a04502, 0x0, 0x0, 0x0]
  | 11 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C28_records : Nat → List (List Nat)
  | 5 => [[], [0x1668f], [0xac1f92cc830792d47e4b5795ba6ac2872d6a50e5ac95ec3b4ec1e2b3a871d53d0e3ad4b383d0f1996], [0xac262378a40afcae84ab0a9cde0b67466ad06b3a628cc340ac1af68ace7e5740d67560fc86b3ab08402d61473f24ab0a9cc10ce8b06bd86], []]
  | 6 => [[], [0xabdbcfa7e8b3f532f8c6baef9d22eb391f], [0x262744f59d312ea9cfc9d58a46d6b17c4bcc51236a8d784f51a46d646330daf88ae6aca1b676a3a25d79457359d390fa9ccc97519f2cda960f34e4fc9e45493e9394665dad578f3a2bd17ac2722e8a92fd115263a3048be6745742f5851ccd50457959d3f0f59cf3c75bd449ea7989755079b359898caa322bc98351b92f08ae6454f9e558af09e055d19d4679b3a8d7f4f6726b1d24267a5ad670fb3a338e8a9e7cab85e13b06bde662524cac1af59a3251a9d50bc27b3a7a1f675123d894832c48fcd6a9cc19d51926d6726547d60e8974b525e9472e8ce463f0f562a33364983cd15a8d4ecfaa07d6102b3a8c976acf1f9a9874932a564cf4ac57f4f54126d6724d4bd6153a7ac4f36743ce47abca9d759d5827a8d7c4f512f69d153ef95464c35ac1c56d58af89ece7e675613136ac4936a94133d2ce30672ce49e560cf3e558c645d663ef1d64f817a419e5719bf35a725d0bd9d460f51cfce4bfa2b99835df348c609e60c93e902af4cd4d457956d53a767947c7391827aa77e675467db3a1dd13d5ad649ea79c87b06bc66a8d794f6a4e45d243f3a546a333], [0xc3306bde4b3ab28d03d4f3d1823aa74d4de8b474c4519a61d242672448e29bd52b2714f36553cc502aaa9e05306556153b9696b0a3a742751be2bc07b3a338161d46f89e64eb0989fa2d5938a49b47c51524ea22a79927c2b15e0f346d6b06bda68157b5991d1d231826ab098dfa2d15af08ac65e146457156153c0a8ea35e1154d15a7c49d181574569959d3d26a1ea798cc11d51a4a4cb498e247e8b546bc23696ce8cd550f67564fc8e61d2038b0c0ae8ae84eb0a9e740f51c5679937c57845632f08a92792ce9e9f91d593a27993ac2a7a391d46bc126958948099c953c486f45b3a7a8145d6153cce96337e5552d51af079a3a8d464559561474224d874f925c3674c6fc8eac5785191c56a322b49f1454f3a519ba2ad16ac26228cb56553be21eb2a9cf3475848c6f15a8d784f91d65539823aa79d2621cc4a484ce4b419f3f2554679926c6745ed158d51a7c49b18c978456356519bf25a325e14687674f51987ac246304b561473f44e464d4c12d5940abc23ac267989a59d3d1823ab09d2622cc530692e48ad1524ea59ce8ae81eb0a3a62655854ee2a68c9464569546c3a4a966549099696b466fc965e1153cf14d092132d2b15191564ffa484cd4aca347e4b59d594661ece91a330f53d1d312a96df1454b4b6bc22a9ab098a112d5851ce893a9e637e8759d44bf2392438899e134312922596d1524da562bc12696b27c5c52cc4a487161aca057c49ba2bdacc1ed067d458719c0afcd2aca0524d8d9d313a23a464d4de2b593a2bc07a9e055d11d4f314223ab18c94627593a24995a8e2b5e03d4f444c4399f60d48c56533ea44391995304733aa424b86ce919f91c901c44cf0b3a637e872fe8b941929160d7b4d65306bdc68ad784fa1c0ae2ae8cab2a9c934b674c71987ac63248cac8ccaa6a1d9c60d7bc49f24a4cf0ac2a77e83d4f121831ab17c5780efcba2ba16ac9c55e134f519bf25a5b454f36565338bdc3a26337e4b3a2ba2be4e465ed154d07b1292455e13e457151d3a2e84e74815742751a2a49b498e337e8b44902ab4caa78915a4d58af08aa6ac57848d2c1e9213352a37c4932b53cc4fd0eac2a728c3c4902bf34aa7715744d58c648a96a8d835ed354e9a983193e45493e167560e887b5ace8cc3b3aa29d5861181574275851131166b574378ad63192f01ecaa8d7b0f67466fcc6a9e89304735aba1825a2b454f3a4e8ae8ad167fd704822d4f231823aa7988a31d51bfe9295ac2a78443ae090133919f60d25cd53cc5122698e337e4b59d19c2116057e9742768518cf8b67d8a5170d6153cc49aa3454f36551c564995], [0x2a798e247e8354f31c0afd0a98e247e9cb2931c4902bf44ab2a9e114942d6508b8a9294]]
  | 7 => [[0x16], [0x161ef44fbafbde723ea3f7975fcaafd0ceec677999fd56fe547f28bf9b5fca4fd7aef35bfaab7b05be647ecc77aa1fd6bbd1feec077a15fce4fe5e7e3cfd9e9faf1bc99fd2bbf97dfabdf90eeecbef443b8f5f570df303f5bf7ba37eaddf2b3f4d3bb2bbd89de9577483bb2dbd0fee60fe985fa6bdd9ede9d77a41fcfcfd12ee9277a01fba57e25ee9cf76237a77dd87de90f74b7f4b4fe5b7eceef893bca6fe657ee7feac3bd82fd99de2afe45bb9f9f98edf53efb2dfc4fdccdf7676f5f37d48fccef72cbf9b9fcb0fd7fde3bfd8cfbca0fd72ef1f77756fbad7e687eea5f717f2e3bc7bfa667b5d7bd18fea57eebdf517bd06fc76fa86f74f3f4b8feb17e88f7a8dfc4ddd14eebb775d3bba77e23ee3a7d7e7f453dea27e3afd], [0x7c5709ebc22b9d2120faa8c91f36b5746f53c233d4648faa48717351925e690133da245e33b8a89769e9126e92133d4991efe2e849f5b4145af232debd874fb5af09067ac8f9e7159837aa796d7c4876f3ac5236e768e9e6a35d1bd4660be4d4f3e6c4a4994e21efca20717392d746eb7983bace7e6756154b75bd20cf3a21f5ea757f5b8a90764808beb674f53e24457b27c60faac2636ef8a255d0f187abe2ba5762474db48af4de055d19bf089579a0797a88107d5e21d2eccabc2f8ac99bd2b0e8f6466557ca2f11f5e166ceff86f76243cf9cb6893771570dd2b32abc990efe3a24cdea9cc1bd192f13d5f4839a2e79f367d45e72a3d47e565d1bbfe18dd57c99f5685187dd15d2bd4e60cf4f912e76b3a27d0f18fabeebfcf5ed15ec7e199e92020fad4f272f9456f5f2bbdc7eb27debd4f2aaf56920ed263a27dc55d3b54e534fa9d12ceff98379743cf9cf4c3af45493ea9a9c5ceb2263ac0a60fa891d5af3a26b5e5b6557c0aba37aca627d02ae9ce6883cfc56b84f94de23f5854e9e24717b36460de5e135cf2dae8dea79897b8abc6ea9c74db2314a7d781d36b0eba6736099f532a1adc9910be4b712375c0c1dd298f2f65d5fd7d6479f37ad0daef8a6b5dea442bc48c3e74e4c1ec710dfe6b0989bd4f313eb00f3e6dbae8ddeb266f3d660de8ad959f2e2f8bd9e3335ca286b7a8cf3e6a2225cd4645793ce3a5d5c061daec26b5e5c435bd6491f55c0e2d758494ddcb4d7abec86d745c98eb51af6dd7842f3bc4ba57aca32af2b2f4dd9630774ad1237951106f3d3e27db4306f24a8af69e9955ec528bd6a3788fd46bc2f44883eaa422bd8ed307d27c4cfa9e9356f123b35d7457f9a40717394c997c859e7cea77c67ca287b797d126ec39dbad0f20fad9cfcee5d16fcf122df9e46435bcf4e2be7c5789f58a46d6ce9e97a483cf54550aed2d982fa535d1bd46bc6726434f929b2abe6374cfca2f59f78899bcffa1f5ce2307d22e4bf5330c1f4868e9d62b5d2ba2a8976ac9c46e891c5ce0f1deed464cbe9d074bb3d3a67d7838b5ae090676a515ece8af13dff1d2ecb6bc2f7fd74af2b2e0bd061d3aba4e2de961146f53bcf3e33746bca6f39f6bcc1bcba27dcea78ae7ca63a3d5ed73ce90127d65361d7ba2ba375d167cf5912fd6a3449ba403a756553ed7539dbad35307b48c893781099bd231547d953cf599818f9, 0xb3a7b9ef3adf3d071d7ab5a60dea31d13f1232b9df143ebc0890d79962b3ebc2e99ece8175b1090e78ad12af32adebdeb5be7ccc90b75c135ce869dbcd1323faca6b7af8d146e68a9e7d9093cf9af086e7448fbe6e2adfbaa74fb5d61313e49099e8fc2f13e919d0fca24cbe8915aecf89837a7a7acfc8c60de89074eaaf8e9e57437bad50893759d25ceba183daa7a897d4e60ceac2a75f5954ebd241d3aba2cacf64966cf02a25cdad570fb2a87e7788c1bd2db8af96f44f3cd09237919206ee8a1f5e5b788fd4e87e743c7eea90183d9f1436bd94a4578150de6ffb2b3ea77ea7d4f3a4f61c75db32ba27e51305f3a29057a8dff3f32a40de0f6267ce8b84f8ad20ae4c8f3f0e21dfcd64e2beb01d13f53cc6bece7ea7b0e3a6db3a33af2db0ebd6744b3cf519b79e90d6eb81e7aed0306f4f4b7afac6322f59386ddff482bafe7ceb61c99dd288e8f57438b993225fca9e62dcce9f9bab0a399b0e60ee78912af078e975894933cf4e91f4f935e73d182fa53481b9e23a797ad12af58492dde2436bb06bdf69d120aea7a2bd9874d739321efc9e9d13ef130f3e465d1ba0e3a754d499ed29ae0be56744faf08af6b4135af53bb33df16567da09cd7946246e710f3e5393f79cd3313e94d356ee2a6bda575bd7d23313eac6326e880bdd5203cf9c8c87b733099f519bf35e681d1ebd6bc4fac2466e87983d9e24e6bcacbc2fa30fc7d15a115d8738b5d4f1267514fced652e95deb61e7af6b3e74550ced28ae8ddad3f2f54e52cf9ea246ef121f5e0f492bb8a3a7c959e23e8b9f7ccf31d3c9c435f9918997cbc22f9d74457b27273f55e111cee2b0fba46304fc64a3535bd0dceff86975e26567ae031ed5f10dcf539bd3e2479ebd62a333b3a7a1ec1a4bd9955d33d18ceaf5c510cf54290dd95307754e86e7918a83f19bf55e8c7fcfbce3bdd57d0fe6cb2739cfc0c7e59cfccf79d20af33132fab0989b3a237db4505eea710bde65744dbae03aed8cdf9ec879e7cdff3f2f48c60bea8df13f2b30ebdeb482bcac9ab7434e2e70793379143c79d4f2b2f9d0c1bcc1a91d90f17baa908df5ac9d33ec922bda5b4d5ba1e34f5995e73e869adce245c33d612437932246f51926d6a7989721a4cf6789789e4c8e9f2a3481bacc79f37e5d1bcb80bdb63251b9b6cba375d170cebc21f9eb0a3b99b03a79995f13f3d3ae7ece98d7a1a60f6, 0x6c0c1bcffa1b5d675233d46a7b759912cf32932f95f4379cf4ff9f891cbea891dbcd123cf9cc6e89f5e115cd123d75eb1521bd47123794d126ec49c5ae24307b40a9af383c31bb23448dd24267b5631a37a9dd39f51bce7e7a760fda119d796d0d6ef3b0f3d7026772e83a759950f6f53c90bd5b4d7abc4b7cf5c10fceca8e9b6a35a57a2a79f28908beb1928d5e2420fac08665b6b4ccb6e88f376a35e1bc66ead7939c57d28a24de7461e7ca2b82f7150dec8a927d2a79457b2c7eeb5c06bda87927d55f44b9bfec3cf4550fed3d132fa7a5c17bcebc4f60d7bdd48ae8dea3421bcb6e89fb39d39eb7a259e5b425bd6153e77ad959e71133ea5b79cfba2ba174f90fe6ca933b9ff5be7bfe8957a8da96f6748cbea33cd9ccaf59f3e474f2caa1b9eb251b9b3ec1eea25d13f32982f99d5235d64f8d77456f9eff897766561d7d4eeecf7b96f9f412f55e746567d4686b79e8747b51ba27d701a76ae84cf6ac632ae92a31d5e76567d4f262f4d4ede733cc4f96f31f5a8c8af35c114ce8a9e7cd6f35b5c9ce89f5ed66cf593a47de75d2bd9d19cf94dc57d3d4e87e4661d7ca6f89f65535cebe22f9df743ebca6bc2f434f3e73135af8e817bccb69037a9e655f28af0be585c17d5092b745493ec8aa1bda2446faa7c3a7961d12cf51a90dd6624faa2460f6a31456e900f9d6465e17d4f24af5d15aecc39b1ae7a1bddd64bfe7ac893eb28ba27e63754fcb63a3d48115ed33310bea79297a482f75994747af5ae95e2b1d2ec8c639f9d2723f58522dd444979af084e7a9de29f34312bd1724fac56b7cf945206f3dce67e046227ce4519f7a9719ef5ae13e2b522bd62bc373c45ef2899dbce2457f9d62bdb7a8c516e79983ea7a8acfc6708755bc74db681996e745d2bc4902f35d0ede6f58e9754848facbafb9fb02a75f2dae0bd4537bac6702f3745879f2b38af9835ef35a13f1f57cc1f529ba27e0548399981bf931c42f2fcba5798926773ce86d7ac8fbe7539513ea726773ce4cde8ad35af5854edec05e33bce9ad74f90ae6bc2259de75c27d9d084fb39d19e901dbcd703c75d4f232f995c57d233a27e8e9d0fa1a41f56555fd6f5a6b5d701bf6b2a716b5c4e2d768289aea728e7bd687d74508beaf3a255e90331da1a63f3890deeb2b21addff1deece8bc4fa9cb69f5835adeb09d2bd46f59f7c56f9f539e7aea35c17c0a87f3, 0x5bc99dc4c86ff0e21d7cb52b367ac9f97d54cc4f9ad5e9bd46e2be67125e6890e9d6a7a8d7d4eba675e964e731c66de6375cfca2e2be748c1bd2b2debe24267b4ca3cbd9e9f97d23182795a43fb3a43a5d43c74eb31c48dd7117b6ba2b84f9e9746e8a8e9f2b148facbebc2f5e099dd29a1add2546baab49af6959206e86917d4e21a7cba23a5d67174e6e90f3757f45f3d4f23af7fcccb72d932f93546fac5687d7654edd732ae8dd874833c4849f56f1746f2a2e2bd7f17b6a483df5760c1bd3a4495eb25f33d4f02eb918b63f539553df161e7ccb1237995ff3e79933e9d1716f4487173a8d875eba117d6461d1ecb0f79f7fc99bc8aa11d9f142ebcf487b738874f2ba107d6ce28e7d4649f59f9e23f53ca6bde743ebc5686d748d15ec900f7d4b6267d4a2f39f4d493eb5398f3cf917bcb06ba76b40fcbd2b182fa654d5ba2e7cf34f920e758a8dcd17153b4ba87b7918a63f3d3c47e30522bd463a3d43c7deaf72275dff10aec8cb82f94d0f6ecfb07bea77fe7cd04cbeb3a119e9f24bcd21267b3e24cdea9dd19effa6b5dff516baf060eeac262ecb80e9b653891ba1e717394cc17cf11996e514d5bce8895751917e64c863f1e7306f54679b761d0fcf2da1eddd14d6bbfebc4fa8d6f5e4c8ebf232522bb06bde79f8c17cdd2e8dd8a60f716c3a795c112ce878dfd64628cfba286d7ac5256f32ae0be247febd4e716b8ae24ae9a9bdd515447b2fe87e7995e23ef126b5d3520fac8c9ab75bd35ce9a917d656265f21e76f3a9cc1dd123c55e7e6597af4b3e7959126effae13e2b5e27ca2caaf57d35e6caa419def452bce8b7cf5c0edd6a322bd90f3e79ce84cde44899ed3a21b5d2037bad4ee2eeb3a349f51b2abeb27e2bd62a337a9e219eb42259e7a79cfab43a7cac9f6aeff877759544b3d4e9ae7a46723f58af19e7a754fc0a4cfa62099dd53cf4be565a17c66fcd69f9d13ec3a1b9ea3495b9c431f95211eeabc2e59c991dfe3fececf5bd0fcf6533f3e0f1d6ea2a28f67fc3dbb51b24de4a891bd64bc67a8c936f231bc7ced267d448f8d75bcedd6bd2b5da7a481bd62bc27ac28e6eb821b9cc11d3e3e290574811beb60127d65643dbba289578ad879f51a14de4a5d1bc0818dd71595dca3999cdd1306f4cacaaf4d474eaf12415e65449bb3aa2e76245edb51a6addf11d2ecfc9cb77150fec87917d5e25c27a1e4cf6, 0xeaa6b5e72744fb123aedb3a338e9aa2bd9873cf5cf4bc2f96d6f5f542f6dd0f1afac60895781474f353bd73e247eabab486f6ac5785eb79c5ae244fb9a48507543c7bea9f21bcea35e13d9d592f56912ecf132d3ce2187cd4687b77bd709f68550bd1543bb4a6f59f99a043efb2f93e8e989f4a2c3af891d1aee9b2b3ea74833d9d19e73f074f8c22f59eb2744fd60fd57], [0x891c5555b48c9a9465ea35ed3e6708b8a18dc6249917b6564bc127962b520fda75935a609eae6b25e13bfea424b56a7989ad5ca92908af2ac2a79193d64e8a4a5ea3521156d594c649b5891ad306b4a6710bce5845e115cd07a487ed5ac9f16b4bcf4d698279ad5d0a32f31bf4e89e67d48457957b53cc6bab2a9e244f53cc702ab521153f7954f029472eb2845c53d592f079e35c10f17b2cb6f8af03e24714a3ad53c8ce2aeb3a637447d652d9e6ced0918c13d5935a79b3655353073564d6af09e46844313b53c48e2e6388990c7c308bda2f99873885ed33d3a2ca8f490e21d38d65549e6cea7815c5d531c0afd1eb42a9306759d3d1463ea3494a06b5952279b399520265b546a427ccec06117bcd53bf4e2ce9e8ea179cbceb821f1ce22645ef0c93088be6ac9c5495b29092933d2535c10f4f29a1e2f3561d203ab2c64c228d4dff38831b3593a2bd97a9e629197466e8aaa5d845ed15cd1235aad36995ff480bb0e4c8e9b1704805ecb342483a35995701796da13d26a5d0f38874e353cc712277fce217accb6bc22e9ea791a111f31b5a609e4d4de307a3f49c9fbcaa798dfa1f31c48fd36acaa75ed3d94bdacd1e517896f1f53c22e2ce9950f179aca64c862f2657fc993cb81322f6cadeb2a9d3d22cfae8cd8445c93e951c569297ac9d1520bd4f31c223ed1b427a1f31bf4d81e5d15f56b9562c22f69d242645ee931bf4e59eb427a67c7cf4ca982b9ad5d15f675930e92e5b42b0a399bf4d6ae85e0f26474b96740ae8cb49520267a2487e933d2a34f92566f8a2e79d36b53537aaa487e941d2637e5d13d6826a60d674574554bd4f121471e535c05e5aa29d463f1a3a4628cdd64c1af79ace7e5d19d53ce9230f9d17457e9d4708a4ad6915d15f66901323a74aca633cd9b0ea424b96b2a78f366c1af6b366aca9124dad9d3d3a23de726431b929ae0712b9e9d1304f4a2b7a1a9e63891faad15a7c92d3b427a304f546bdacc9e637e9b43cffa1e2f558cdf9746b2e0879c58d2026431e948ce8ba1796d1724daa909298fc6a791a244effb0e4cceaca917c4bd6531af09ea34945e6affa4018d5a8d483f59b3eb324b9d8748099cc901d44cf4b42b0aa53da0cf9833ab2a9dc55d02ae8aab3aca408159b0e92a419653388747358b08a333a8d845ed3d9d593a23e7a7e5d13d48ba2ba17b42a94d63a7c928bdc6b296c936b2dbe28b97a8d25455b54715a905eb27c4f3a7682f68ae645cf324f8b124c8e9b2b0918a32ef3ae0714b5213e45793ce879c54de25bd0d8ec22f08be698a4628cf5a12326a5deb448eda7594c6f89783d241d2ac4908b8b5a63891fa2f591e649f1aca5b5e13c22d6ae85df145c93ab53bf47eceb3a919e87c67083a355a961117cd67466e8c7a9e7a28c79d4608bde2d0ac2a74f3d3a29a978ad484fa9bfec3863358445cf3e53441e3a1daca34715b40ad6ae8ce5b45cf366d6af6b32798e2472dacf519ba25eb09d2462ed6a6a60d6994990c5e4c6c22f59acea46338f5854ed6a7624e21d34c4902b8bc9e743c5eab12396e2f49a1891d16d64f8af11ea76b4c19d341c43a39ac925267a4caffb0e3e51434836a879322f749958726574e8ba2b55aa38ad7b2eff9323a5ca8d4846daca6879c4ce2b52115ad15a4a8ad6, 0xe89d42f59625243f72ca6ff86276b2a9e05569f24a8af298dfa6b4f448d69bd56b0919fa2ec228c8bf2a457b5993bfec3a411eb27c493aad6ae8ad36acaa77e87cc6fd36479c56b5746cfd32c7eea83ce21d2ccca710bce62484605a753c4908c7a9d3528e3af6aaa2b997038874d353cc6fd2e959eb448bd4f1240b8de73885eb331c66e8977c57845e3d4f122aa9eb27157b6d15af68ad661d0f17b2af08b92796b28157b66c393218ecb42a998975a154cf43ed68cdd12effa404cd6acaa728c7c56a423756b27e5d13d32b0e18ad6b55a28cf5a0caa6b1e7a6b5951f1240ae8d349517267a4a2f121a5d7026431d8f3ae02f4daca248159c48fd1fb5a0f38831b36832a60ce995874813d46bda2ada2b67d48a753cc6518fa9dc528e756554be25d3e494a0e31240afd5343c990c7a456bda7d4d7b4f915e53d26a6f35a9e110c66c8c609467ace919d11f3a48cba179e9954d53a484c8e9d2b2815486744bf2e89e625241d32d4e60947398451915e4c530e9065a460a5d19d614748ccea798dfa9d53c48e5e545ca0147a3c48690755254545ee9684f4ca8facaa95e13af08b9e78ea76b5744f51b3ea433919fa3f4f5a151af69ea798dc55ccfb149065ac632610bd6554926d5ff43c31ab123f4e2d643ce217b8b1490133d2b2a45784eff93218dc9d1ad5d0bda0cfa6b1d954d4decb67522fccea9e637e875613148cdab26b4936b53c8c518f9e935305b30e9006396a7891fa8f29bceb80f6b5954d63b38bdacd8e918cdf9acd6b2a60ce98e247e8b2de8690796896b4c13d1240aaab383d891d26d651a40acea7919fa1f29bce8797480e217b8d6553a909ea7815d19758b08bc274bd25267a4a6f38bc76915d15a6d59448e2b67fd7017a6da09a9bd56b28d1d12f6854f312e8ce057469bfeb806336b2815256751a4a8db5815ad306d40ae29476ad067cc79731c48e2b6a9e6361174ac891dacd9f59948c731c4902b3aca33744bc8cca9463d703885ed2711323a7879ce21d2cbfe901d5566826474795954f1a27994991d1e42302863658a61120cb685613136995ff0c4ed652dbe25ecea467b1f5938aa436acaa74953d6553c223eb091a112f31c48c236], [0x263891fa6b4b56508b5a9295aca638d1fa2d1a3f4a41fb499f6114845f15a1595531a07b41fa67cfd95685233db3e2ea798dfa6b47290929fa5070aca636117b4d68468cfa910ed0aa6637e8733ec529092e1]]
  | 8 => [[0x1fc1a597], [0xa8c479d66f56266f76d605d63059a3d67c4803d65756595699411f963816879627d66b968cd6b9d646d636964c96005681161bd65c091356a2162d563d161fd6305e6cd605562bd6869650565c0b9e83185615160a5674851d1d23d60e560d1674961ad6671691160b969440329632563dd617d61d1380164490305699440f961d2730d616561d169d16ba5679565bccb9169cd684167816465634961dd304565bca2b96a5961ed30a16998079967ac78456a300295601d675c5958496c4b8565fc9440d50162659861677564559909669168d963bd67f96819649d665491d564f92025670563e9635565f0914969e841b167316a69694c294418656994348d65d109d96a9caac401d5314564e160716225665897556448f85d695c04cd68b562e567ad6482674d66ed63d9615960ed66d560dd672164810091638560f16a61661f6744780d63a167b96885630797545715987167ac89e5626d63f967d167e560d9643e6289626798dd6359632d637962656315677165bc954967156271626965e0b7296a9cb399657d283962c167d562f56970085168937a316815671965456b89612d6480ea756715e3c964377b6d696c31256105604160a9690d67656994271d6169677d608d67ed61916482d99404e4d829634d6509647567cd69fd61796255678d6958296c11e53745685561896a2961e5683d6480d8d56a4961c962e96, 0x299624d675d69f803116a9cc7c473196654c43d017163ad676965d0d2e165bf67b16215600964d663c566bd6901622d6199606961f564b961e1674469d083f164096701643661c1687d68e5619560896624935167e16805668d66ad61816a8c3a9ec011679168816585641165c496fd661cc8f5622968e96b3895d3770966c96231643ce84964e560bd61a163a9611d6259654d65c0cac0d031679c778566e56480fa4560f561a563c162dd6761694427c960196716f8b164796434e6c1605965c0a7f567bd61d3894c091827448029658969e8158d64c162356175615d608168ed64dd67c568e1643cf2f162c5649969183b756395640d651967b566b565bcb9e16331153d61116514d73569d071156085694443fd6a8c1a81607d6a356211628160c1659168910389244ad94c30e162cd64d9653167d964d5613962c964c564d4e6956a5d652168d1643ed3d565e2c5d0f944382166576a7962fd6035657d6890f5d2661ca78883b9602164f9651564d4d389694c1434f34163e16365697c005167a1695009a00551609569d567fc7741685963456434d2396654b9e800b16889600d694c433d679c8a0565e0ca9f68c966a967f1696c24956265e2ad68ad61b5628562d965e8d24162496075609d62056a55671558ac71d2e7a9613d69056a39661cb4f568b969f9601565716b8165e0a9ed65d0e1f167256331678875256, 0x96008f1616d648373e5620163916656c6d161a963cd652d6a7d67a561cd6266827968ac846168ccd74750e96119681d62a16265561c94d500ad661ec20d678962d1635d63b565c3643f72a9630682916a8c27fc88bd65c2c448d5699ba1638d6779619d667d610d65d2d21d6450d3ed6a656a9c9892d68963f15681628d637d6890e1dd62b560fd62f96654a0b563f5624561d140c56b8d643501ed69e821296aa007dd64d4f1b96405695812196958031d60d563216739636d6251658164d6d1c561096890d72d6685643cd8356a8c0490d436da4d640161d2381526c56306f361646965396a6d60c96101684d696c0448e674944a65e099f163b527445065602d662092ed63a56a856a5162b164a56958320960996b996a7163b1682d614d63cd27e9639d65bec825606d625d69156831629d64fd644cd1316484db79652966e16221697406f969dd627568096892630552a5616165e367e5526167fd644b774c50cd63016049630968c164d7747166b1650d68a96371618d6375651168fd68756], [0x8d135ee50069f6345bf79d434fd6a875faf10077c83023e92605fdaa67a7f53c69bd0f17bac8c10bf7e9afbf2b3d6fe4600dfa2a10fe7c431be79863ee96746fb8a51feb7187df72cc6fe8194dfae0716f31c31fabda2bdd4842bbc6912774f831f728c68feb2907bd649af798dcb7e3a011f624067ba58897720c0bfa87877dd7b457b22e4cfe440eaef28854fea77ea7ca22f3fb95d5beda1477d5b087ea2624f7480eaeee580bf6a300dfb089af7a4520eeba011de653f5fa4018f7ac987deff86375fa5c37b22bc6f4545efd5ccb6fe2b3f6fb5acaef9e935eecab2bbd700c778bc18fd7fca3bebda1fdc99023f4f6e8df7e9b0bf51a36fd74563bca218bf98dad7e4c8e9f6df98dfa6a60f649515ed08b5f7cf3283dabe02fb52125ef23290fe6343fb8e802fd5ed0bee750e9f535497bbd62f5f5d003eefd2e9dd845e37b4ac26faca7a7ef10bd7eb2715f53529bf7fc21beba147dcde17becc6e89f79c05bef59fb7eb2893bd22caef945ad7e8b8f7f66361f7cf6b86f5e117cf052e1bd7017b7ab401feaa574ee83069de116d2fbfe18fda4574ee50077f656021fda086f761574ef68449de11333db3eca6f65548de89141deb26bdfda063df9c2657f2300afe5b00dfb5a9af788074fa9a9fbde341d3ea1a50779e8037ef89277d84307f4143a7d5ec74fb48983f9ff18ef9e225fb9e995df5848ddc8b17bec84a4775e00bdef59d57e5b829fca2fd3f9945e7eb324bddff31efcf402bfaa569debc24bbd6f17b7b8a10fe7c45ebf31ca6fe7e2d9f9d437fd65584df594acfe8c31dfb3ecaefae912ef121fbdd041d3ed4e506f37808fb12007de40893bd8e9077654a3de920e9dd8d5d3bbfe02df814a3f734ca6fd783f77a5286f7a9cfddec3af7bcfc31ff316b7ef84570df12397d6a717b7a1a51f74bd20ef29bcefe51788fc4818f784545ef59225de7a0c5faaa897762935eeff9417ea3a45fc144cfe9e8a07f15a377ea79197a2a01fe61074fb3a0177e7b1d3ed64c977b16a7de9f24bced094dfda060df788a3bf2b35afde7522fd52b86fb6178de87947de51495fccb053f5f148dee5843f4a3267f59ce8cf66cc1fc6c0bded950877b123a7d994997ec22d3bd8a44bbb2ac56f5ed74ee908dfde24717ba1a18f7b7dd1becf98feca01d3eda6b86f44801ee7e983fa5b495fcd92b3f7d948bf3d35afed02dafc48fd57, 0x52135eee280bf9eb28ef93218fc18431fa9f141ed5a017f24a3a7d918a3bf3d183fa34267f2f02f6f98c79fafd273de7b5bf7cf5053f4342aee92a1fde9b75ef98e10fb38805f7594b6fd950c77d64b7ef98e4d7e710bdeeb2437bb5a60df96c027e8b8e9f4ea1afeccb31bfac9d5beb8005bed0995fb9601fda8d256e90005de110c7eb3e61ff37803fa4c863fad7523ba9090777fc08bf021417d0f00bbd4f127761120ef593a37d8700b7d2237fba465b7f6814d7deb086fca2f13f6485efb6818378831bfebae755f7ac05be92a11de63893bbd68957844c1fd3a1477df15e279825b7e84499fcf50857d3500fbade116f43ce2e702ba37e53065fcc6fd7e5e0eadeaaa1fde65199fca6013f38831f753c499dfa72efabe2f7b43c0bef34af1be210dfeae8aaf767c74fae88bd7e9f1d3ec68b86f61c99de41885f53e087dcc62bfe788a0be79817eed02bafa3618fd55520ee76863ede23f6fcf47ebf89184eebc22fdeba959fa2a02fe78805beb7843bd20007bb3eb86f745d1bf0538bf97e5bf7adeb7ef43403ee86907d4fd16bf522c3ef744eabefcba3fa7e7e9fcb6f8bf844fcfc89225dd9f62b7a6a10f7aa587df31cb6fcde017eca6cfbf890a0ef53b3fbe3843fba487ef762920eec38c3bd6f00f7c8c05bf6b50fef12375deb2995fb1437fd20c03fb34a6bde110e3ed6548bf9d174ef53cf7beb27c7bcb649bfac9d13f08af1bea95bf7cac2f3faa64c7f31983fa2b523baf000ef67d13eee8b3f7e5b5e37cc69af761c19dee838bf92019bbbd6505f4345eeebda1bdea772f7ba201df7c4a3bf591e7cdcb717f2e8ad77b7eb27f10863f5c56b7f2e850776110fef53a4bbd4f1afeae087e79940b7f592f7dd5a087f5c2cfef6b56fde76917ee563f5fd6f53ef5d157ef53b61bedf74efcf534bfa9ca3df32bf4fe2482bbcc64cfe918317ef10437ec0a45fd4f31bf79c5ebef51d57d4846fbcad053f67c75fb48cf6fea3a8dfc8c519fafeb27ecfae9dd2002fbcca4cbe5ed17ee9a947deb2497bc0a2f7ba9c05de7e8eff5060c7bb0e01efac9d17f29c68fd2518feae0756f43c19eed1b2bbe5b015fd64bc6f996117e50133f98a5e37cd29077a8c017ea40e9f56f5237ca286f77fc61beb82e1bdad28efb2a506f9a64b7e76807ee24717b2e805f752115ed15449de2428fbae02f7d5210beec9309bd845ef79d42f7d, 0xab16fdee2807fa7a67dfb3eb66f7e920ef31b64fe5b5e17d4e10ef94e0a7f08ae9de0a483ba1e717743c08ee50063f663891ba6a5077959126f31ae9dea78477b082cfe22c03fabc291bd9b6577a4051f74d402ef53a91bc7400beb96047d61170df05183f9870177a36047d1d021fa71007ed8a1a7eb8a047e71548fcba2b7de9f74af9fa3afd82995df120bddd9f307f456755f654a6deff9337eb26b5fbce01dfa8ca37f594a6fdcb0c7ea0c05f757c21f708b8bf97043fbc14897761c0bdebc00bbd4531fbd8092f7434fdeeba2addd2045fbcd2b86f3f47bfac22e9dea77177998507b3f4b6f6b7811be7a305f54ec56f3cc93f6af947ee5b085fa0c10f74bc99fcc22d7be683f5fb543a7d5bcfddf54ccafe7b307f2404cf64805eef592e9deb2483bca6fd3f8456fdefd199ede2436bcd03a3d8106fbee88437d5b0c7eae875776945efa92983fa05017d9da2f7b3b405f754ad1bea70677a7a9af7b5935ee3f063f45e0f7ea6a60f7944ea7f572e1bea700f7bfe05df9e8087e928d3f65b021fc229af7958037efd3657dff61e7bb051df891adeecfa1bdd173cfbca6d6bf4f803f63a017f65b67dfb2a00ef94cea7eca983fab292dfc66e8d794c0b7f078e9f6a998dfca692bf9d008bf61546fc5e0dfea4250775ecc1fcfd2f1bd551d3ea1e10f71783bfa4c817f9954d77c488bf74946ffad698f7d700877ae8b37746c5efb602f7de05717f2e8ba77a9e0ade5007bf57457fbd64d83f89148eec48e9bd8a453b9c43a7b9d148bf08a41ddfa15bf3ce87d746c0bfaca9fbbe3442fbd6460fe7c4a0be9f011ee899e9fa904cfe82987df3d290fd9502f7d223a7d2645efcc50bdf4c1087f4ac013f714a0fd5a21fdde22dafb2a02ef944837f2d9d4fd1724fabceb84f79c21bf1a3a37c5e0d3eb1487f77fc99fd5921fddd367efb5a5b5f98d0deee88517d3545fba908df59e8de7f3da1bde463f5fccac3ef8919fef48adfbd7828f7b4cba779e8197f3a1fb7cfd173f2e2216f9460a7ead8bdf59517b7cd24cfe89001ef1fa41dced283dccaff9fb9525eeb8017be345d3bbce755f4d4deef48ba57e5b065fa2e28f767d84deaf811eeb224facc6b7ef62861fac3947bd8f483bb0e00ef6b499fccfaf1bd8761f7b54c56fa468a7f59546fdad29afd4692bf83cfdbe60805fad01d3ec491277b496fdf6830fbe110f7ecd332bf, 0x44803ee8a817fa5b96dfda153efa9e05d689117de24847bd4e756f83c74bebd2b3dd1202fbb10506f54c74fb1da91dea3085fd4ee2ee891cbeef89e77dc500bf33eb4ef82974eed91477e0502fda989af7944217e878bdf58717b7da15877a8c317f54ba77de70cefb5a545f1d031fb3dc49de7a3a9fb2a6f6f41807ee4c8e9f2919e9fcac92bf26402fcf59db7c7417beb5a86f7654a4deb7a1b9e51845fc48de77a464e7e90241dce2087dade016facaa97f592e1be56015fae8a47726431fb34a25de63745fa2e79f36b512ef28816fe9e96dfcf410bf9e8ae7e60817f8830c7eb08b7ef22c05fb32940fe65481bbfe905796ca37ef10637e24017bd644cfe304c1fd31ca2fd5f0c7dba2505f5ed78df109fbfaa398dfa6a6f751d003fb634c6fe70267f22e2bfe38842f751816fd6f0077a6a0477950ea7f28adebebb98dfbfe7edfa9e24df681557dfa1d3ea1a02f744805eed694b7ed05d3ba1a05f794cfd7ec9b0fbea3829fc22217da627a7f31ba37d353abbd64a477a9ca39f48a6bddf9746fc6886f77e935ef31cacfd0f3abbbc4a45f26405fcb89d5be53021fa2a047e67d12ee4c803fa7a28dfbd605dfa8d486eb81c5ad8f61f7d64a7f761ca0df5932bbc8017be9d463fb9d003bebda13de657fdf98251fe24c21facf983fe7a009fc6860fe6116ddf19ba37e917e7f4d528bf43c3def2b140fcc1283f52319f7994057f48ce8fde2022f9fa3cfda45d7be890bddd700237d6728bf5210deecfa6bde2b086fcba92bf9e9955eaf807ee567e9fdcae8df64917ef34b0fbea9959fd9ce8ef61d20de76947ec99267f4c63a7d8ad48bee2a4bf9e220efccb1a3fa7dd1bebf8a3bd7b59b3bd645df7e996df53bf5be6393dfcb71a3f56808fd32806fce217be8fa18fd8459ddf46422fe247ebb9820cfe7e9c5fd673a37e5b7e9fd80d6bf81421f692933f9785e37c8c043f8ac08beb7941be2b0c6fa9087f741805ef3da41ded16577d529af7aca42eee2b8bfa0a5e37bf486f748099fcff9337883017e9c43a7d974517ed6983fa636c1fa1a0cf79a56fdf6cd65ddd1022fd4734bf7fc5ebf2b062fe919a5fd1b32bf6286bfa3e0bdf525427b96c2f7b4d40beee88637ce228fdd3b2b3f5bc83ded22e1be51005fc8c523f5d125ef23140fe111d3eccc503fb6ea37f4dba37e5644bbd88c3efb416bdee29fbf97b5bf7ccac3af, 0x6b520ee89005dea76b77b4a30fdb7ed0df32b3efd780c77aaa4cfe84437fb2b468fe65021fd528977b2148ef51940fe246cbba6a02f774469bf684a2fd2517fec68caef4806beef39477d93267f5a087f7b4099fd54cb6fd870c77af6b46f3a863fb54a1fddfa746fc48757722c4bfaba003de5b3f5fda0b56f9a5d7beb79d5beb7893b94a3a7d26419fcc3811bdd1066fc4805f7b12657f48c9afea9267f3f47efead2537f28940fc5e147ed22e8df5c019df681477e7a746fb14b46fac90aef48ae1bcf3023dba205dfb4170dea8a25de653a9faf00cef944087f1a225de3461f7d651a775bca3df519d4fd0600fbcb8a43f6a584de6b043eecca8dfb5a555f48021eea4261dd48307f54e18ef98d12ef6ed4fbdff3aafd23127794c017f34a1fdeb224fbb2a016f995257e86a1bdd35067baf6b56f41822ef51c22fdd128efc48dbf76296adec20ebf4fd267f1401bfd67d0fef6aae9ddc53abf4f725bf7e899fcba2b5d874007eb962f7d54d25ef51b5afd7012f7ccb32bfb5a7a7eb7a4bbea700b7ade02ef9a574ef29a1ede691d3ec4801779e80b7f5949afd874977b0e90679ea637f51810fe51009fab4507e5bc31df682d9bd1742bbd46fd3fb4120eea7a2fdd7000f7a7c2f7b98e057e891dbde65521fae01a6f28056fd02941ee745d2bd2289775ed12ee4c807f9873ab7cf6c3ef7e96fdee2817faa35edbb34caef9e9357f5caf1bdef12efd6502bf62874fb3a0bd7e46179fa2e84777880bbf684b6fe530c5fafc86f78290fef31c9cfea9437bc0a18fb9ea7a7ebc005bd0d00bbbce7edf950427ebc141bea9746fbc4b7ef7ad12eec50c7f57445fbc20e8df4d4a8eef3a1fde5328dfda0b76f9599f7ef58637e7b5d3bb5e51df81403f6ca833bd703f77cf460bf3f4a0fc891d5deb2931fa404cf7959487f5953efde25be7cc62cfe654eadec221bde65085fbf2e8de24c5efa50085f69f9a5fa2a18fe49074ea6080bf9954d73c3ee2fe9a64c7e80983f94831fdb50bc6f5c125df682f1bdad61f794637fb98c5afc8a097de5b6b5f9bc05fd98d7aeec39fbbe5b179fd22ba379e8017eb8291beb21d3eab605fd67d6fdf63ccafd392dbbcdf2dbf24c08fb48af1bd3e497ba2e86f796cf37e891dbcea75ef7a9c87f79a595df48ca6fe84959fcf51a3f4f4c1fc60807f88b0c7eb0287f73a899fd6826bded7a45fca6b86f, 0x94c387ebfa4bbd9500f7d64bc67b419fdea78bdf50f0c7bb0e2fef79c31be92a1bdd783cf7cf69af7994317f28adfbe743aafd53127748005ef53d4fbd25187ebf43bfdaa4c1fd32946fd8a19becac00bf24c03fb2dc22fd5a17bf56553efa8d487f23146fe5b005f9fa3a7d9d0a0bebdae1be8696dfbc4755f43483ee87807dec0aa5f9e651fb17842fa89063de513f5fd473dbf715affcaf941eed0746fc221dfd9ed0fef682dfbe7b96dfcad08bfa8c5e7f1a211dea3523b98218fe4d4aeee37863f67b6577d6479f7939ad7eaaa1bdd0f147bb08b76fb0148ef08897f6d06577d224cfe37821fa87803de0a1dfeca251bf1a431fa418bdf57824f7ccc37bf61112ee9f147ed531efecac05bfb40c1fd052dfbc93017ecc6caef7159ffcc5183f974017bda13d3fafaa37f592f1de7f945fda0897789205ef574a6fe635e37aaa9af7aa6a7df29a90fd0f17bba247ef7958217eba0bddd8a5af7c221a7da9e635f48a1bdd8a5d3ba4a907738808f6e28bdf912087bcca013f945487f1a21fddf1086fd2327bf94d705f08ba37e740c6fcd03a7daa6a37ed6ae9dde70defd46cfbfaa6537f1a291dcf317bdd46013f5bd0def59a1bddad5c37ce8afdfa8d3e7f44983fada67f7d7b53ef4950beeba033dd1b00febaaa45f2804bfb298bcfe5b02dfd6484f744819ef158177dc50c7f4f6e2fea45c5fd34ca2fe919c5fab6047d59948ee8ba1fdec8a45fc562f5faa6517e900d3dd8a61f7cac45bf9a65b7f08b2bbc5e12fec6e86f760570deba005dd7b483bcf64cfe94c217f3daf1bd2544bb8e80cfd9a6567f54c9cfd845b37ae02f6da45d5bf158077ea96577cb6a43f9e9257f078e976116cafa1a10f7ac9c57e45843f634717f54602bf56831fcfd32bbe1143fba4a2f7d568a3fd5954efecea477d4e046f9ee567eba063dd1010bbcf49ab7b42567ef38177d20023ba6a60fe5e008df2b4acfe2462bbc403bfd61d84dec5309be1e267f2b601fd74405bf519fafd87267f5a06f5f74525be9a803de69746fb2a92ef6557bdf4fbf5fa24023bbce045fa9e119f72c69de65267f3a27edf624fddf29ca6fe5167dfade0cef829d1beba1fbde3944bbcc725bf748fdbefd3697d1228fbaf001ef96ca07ef8af1bcfd15ff38a0cfe5bc0bdefd21fdc8b02fea3602fda8e2b7f3d3a27ed04d6bca6503f7c4eabf12043de651a5f9c42f79, 0x35a6f5fa450fef34a1bde11437bcac0cbf944057eca811be463a9f93210fe9a624ef32b5afd700077b3e4cfe74401bef3ae1bdff00efab405fe62970df299c4fcea187e9822f7e44808eebd933f9f1022fda0545f94c057f51af7dea728efa7c02fb5e021df3da25de2b522bcf508bf5ed35ef48cacfe9198dfcf728bf52115eee8a917d0f283bb1486f7304a5fd68553bd8a267f55928bfa8c197e90007dc741d3eca61dbf5d021ef590a3dea76137be202df8d178df1580b7e99a45fc22c3ef884ccf7594a2fd9f483bc5651dfa4479fb0521bdd06023ba4a35fd18c31fb2635afdc5007f3c486f767d87def39417d9a4d7bcca0cbf5ed66ef1a241de69307f564f8d728c74fb5848cdd25457bae051ef3cc03f768546fea798f7bf460fe24c31fb2d862fe7b94dfbe201df3cc21f6b8141bced023dc4902f39e9d17f2c096fea9483ba908bf75c005deaf817ed350c7bb5a60de480fdeeb7893be635c37d4e00ef6c0a3be7980bec991bff3f4c3efa46657f19ba3dced02fdbd601df7fc31be920e9f5ff483bb5a3a7d745adbf51c68fd0f43fbd3731bf48019ef53c8dbe7a179fd523a7d67d6adf2b892fe636d1fcac753f946517f28a1add354d7bca601bf944197ea4213dd8752379323a7ea9c0bde6f063f69174efab602fd98dd2bf340e8fd8726773c411df7fd48bf59211dd481efed2328bf9d005be8b927de5379cfb2a9af794d0fef54af1bd870877cca9077388a0f68ba25dd1b087eca2143f6a517ee41843f65100dfcd331bf7c40bbef39c57e7b995fd4f34ef22c08fa86811dd4844bba1a00f78ad3ebe60811f984267f33eb6ef958a37e92a2fde245efbd6531bf9d021bf5954ebdeb022f9fa2cfe81408f635863f5891d36ae8aff37e912ee90141ded19e9fa1e02f798d20eed6af1bd87483b9da10fb7c548bef89fb7eb26a7b9c405fb7ad48bee88057de70d2fcca00bf7fd87df159417cc1007f35aba37958ed7f6826b7ea7a477d4f02ef3a8c1fc869d5dec898dfd23263fa8d25eecfad1bd95307744892f7654c1df3dcf4fe24557bd233a1f845b0bec52dfbd0f3f7bc5112776206fdf29c22fe7a7e9f9c43a79a7c79fa9f017ecde307f33a63efb40a5be830bddd962db7caecfbf72c0bfa9a8bdde0a4d7bc228977], [0x4950517bad6531a4adeb2715ad7d685533dcfb429167f5d64d6a4adeb267d25ef59522a437b42b0919bc22b8063b65379c313ee2b5a51de43ca00c7ada154c8cbeb2aa6346f683f47ede8460a0c6ea6a60947d8fd3a85ef359522e89f845fa0c6ed4f02b5bae917e5d1bd48cc6e89f624fd1d36d9d48ba33ed0918a33f5952292b76289917be3c4b78433d6f43421ce710e818f95212517bad4ee2b5bbab24945eeb685531a4f94d0f0c5bccac50bcf60a7e8fdbd34cc6fd3e6112545fb2de41843b61179c31bb53c22d6cfaca246b5bda148cf67ea7891adce901322f7662948497aca62f062f66561c5e5e879c418f3b419f3f759322f063f2652645e7d5933ec56f3885e0c7cbce710636eb2a46346eb80bc18ed61c9917b74c6c5309ba1152125ead6ae8aab794483085ec68fd2915eb298d486ed6aaa519f521251afab0e2f063b59f6285edacfb14a46b83cfd1d2eda153c8cbe53280317b08bf41bddaa6637e9f4c6fd35a7e1138831f27114018f9acaa9521bb14c20bdb6683f4747b48cf4e89fb4234522bb14c38bdb6b25ed66ceff8bc18dd845fa3f6f4a671062eed07e99f9f684f6cfcf5c0e20c75c68fd1fb79874945edaff9322f5eaca635edb9fa750e9e6116b431baa41fa3a79b42b28d2bccaff8bc7dad304a3bca41fa507a3f4ea283d5a11a33f3dff4945eba929322f7c9e93528dbd6553b5abd8452117ed3d18251be79d700c679d4518bde6056b4a3b6cfa908bf34951717babce2f06376a7919ad5f6826a51d7b419f29a7b08bda2f9ab27e9ad3ec52402f7552125283ada0cfa91ae654805e6ef121a10d799525179ed2331bf4fa2472dadeb59422d69faca346f1b9fa50063f1e728031ba878bc18f5aca11497ac68a41fbce913a85ef3592907ef3b42a98467c2287863d4ea2645ef8ffb142f5d5d15a557b4c6fd35a7ab2aa5256f48b14c26f61cea17b6da13d1467ed0aa4a39f29c2218bd8d19f5239bc441843757028031db3a2e8aad7994ea179ec48e2b5bd99f3f474f331bf4d6bea9e636b57cc6cfb09b9ff4805eaec22f68be7b419f28e7da154cc6be919a5d13ed6a6a51d761d2017b3ca2f10427d9f62861dacf9fa507aac925283acc6d69467d845ed17ed3d32a51af9e9ad28cf9fa4c8e9f1243f474ea4c8e82f7caca347eaba40750bdd57043c31cf31bf4d7de79d0f0c6bca2b7842bd48494fde7594c71a37a4574555ba4a900bdd651434216eba2beaaf3891ad555bd6531bf4f9fa6b4fdbccfb087eeb98e246b5bb5aca9473eb26b5486f5935a519fa4633746bc48d69475ea77e9ad9f68552fd4f49517283a9fa500e9f2636117bdd123f4d6d798d9f62b7d64cfa91cd2017831eb59552bdb743483087ad233dba27e24815ade759522bdb7a9dad28e7da12333ebe6967d84df5935abdb77e8fd2dbd3fe750bd75fa3f474f912422d6d76553528f3cc6cfb09bdff61c5e9f68422cfcf67d484979cf4e89467cfd38874f36832a51cfb40c128ef5651a35aded084431bb31b8ad6beac9845ef3b3ec51fbad4845cfde729ae018af654c128f74ca2f062f6d0acaa95e9a9bc51f5], []]
  | 9 => [[0x176216b0cbb7ebd1ccfcf656e25a0c6a], [0x82b07e9a023a351620d652171d166b5a00e9448d0c5fa45a480d9a5f029634960c695edf065a0156a65679d602248d30087a1f5698f00c7a283a67d63a9628d60870085f281fb856179601963f567616555a3ab0a457a9c93a9729969a7014564116611a1a5608569eda1256065782961d13789615d68d1a179700da958069563aba33d6369600fa26569ef07e963f5717a46bd602e41f168816629f845f109694c007169056829f2a960c6428fa28df065622d698df12d608d649700ed65c0931d657d600d728da1f966549009717d60c57015f4957aa5a890d6b7002df3796a4709096845a88566b5f71557eb0ac9f6b564f9602d7015a8ad6745676963b5635963f705edaacb028e99ed70096179a1696829a8d17085a0a96b41f28f0023061c9171602d600f0016467f001d67c56495aa29602fab41a96c00f5608699edf199608968d1f0cd63f5a84700c5aa45f03d645da7816009a6c9646d69a5a281720166d160dd602299ed674450d16017a523a26553f5f3a9f016984576c1617ba76560a1667da0217021a24d618d68297021617a9aa707e9728291ad6a7d649563896629a434d77562b96179f281a00d68456055667df305543cd52300c56521a00567ad6021f1bd63416994072d6159600df03562956b43028d75d0d3a9a0e166a96305698da5e0954d65bc93cd6a6d6a456185602da0157085736168d167fd6, 0x2f000e42d9628308616aa5f52160c70065f16563f7aac9a53d602e99e8094402a16715617b0a5964d4da8c06b57b796611f9d16815667d7017000b02916495f7e9f06704c16009f8ed6521f281608644d56], [0x654a325fa02d68d0215aa902d60641959170f5653d485a6902d6410fd58ea0216a460a5948065690925599f281698c08594800d6a445e59ad00d68620a5920179614021580b0156494025a348d16378a3582102d602c0b59043a9679c3116919ec067c4958310c563a80559170296acaa901ad0856934055a1100969442100fd0c567e8fd5905015612008592500d6628055a7b28d6520ea5a0a5216628fd5a7b9ed63a80b5a9128d63f4195a530c565206b59ad3f562800b59ad28c590a345a9fa4569a63459250c5698cea58a001569ecae59aa3f5661c5e269f3f56628ea590d08565540859484956844314cfd3a968281559ad6b5645c085ab23a966b40159fa00967e85e5a7b02d67e8a359ff17968d20a58500156b7a0a585e02d6846115a246b4d43c31340b00d6494055a7b6b56520085a916b5602c085a96a456a4419597b01564942158590216064035ae552161f0025a690216a45485a342b9667d84251700d6280195a7b8d169ec3158e20c5161021585e17965214859fa5216b9691591701563f4a35a696d16b799f59700c4967c6158a01bd6a667b5ab2494d52117350900d69ed2559fa6b5662821581300d6495255a1117965540358c128d53a8a059ad67d68459f5a7b3a965ed173634520db40315a0a0c56a4663015528d6b4005599f06566b40b59253f566a54858a300d6628315ab2281653cea5a8a7e960c42159700c563a802580500965ec1c5a0a281667d4858a00096610345a7b021628c215a7b0856178315a631796414215ab25216b69fa594800963f4fd5a346b560c419597b0c5602c025a530c405205e59a53a969ec1c5ad78d16715ad5a6900d63a8aa58e20c563f4744ed0a456b40ea5ae184563a80658d202164945e58a301565eca058a0179645c21599f0096020025ad002168d0035a7b0156a5a7b5a651780b414859482a166105e5a18845698daf59533f5604c05598a17965200b5a1128166b4ea59ad0156610a35ad02916844215a910a160200858fd29563a82158fd17966285e4c7d00d628c0b5a3467d69a4ea592545cd554a05a118296178314e637e963a8425a630ed69ee0a5aa90216520215a0a3a969a4a358a02816610ea5a20829662984269b3a968ee34585600966b4a05ab28d0d28c5e58a30656, 0x3a8315a6328165bc2125fa0156b6634598a02163f4035ab26c9620c214e7b67d69a45e5a6919969c4a05a0a4956884a058ea28d68440858d402d628c08599f08567fc5e158a28d60842158a00856828025a913f564c1255a110156178015a6308561680b58a00c538443359fa7e96844a3581e0216ac8a359cb6b56628a05a6302d6844fd5a917e969a4fd599528d6a4669028a9ed69edfa5a21845693c0b585000d6aa403599f3f56828035a203f56828235a91a45667c5e599f0216715ad55535216844315ad008563a85e58fd02164140359ad52163a8195a344956494a05a3401561400b59843f567e808581e01568d019582100d6520a059fa06565545e58fd01569ecfd5a9174561202158fd1d1615c0558210096844035a0a3f561781958fd0096828195a418d16aca9100a30056a9dad264c00d69a4a0591728166100858c128d6aca0a5a7b06568d00b5ab202d606405592502d6844ea598402d68280559050c562645e54a3009608419594f4956b40fd597b02d69060a5848015698c315adfa456a440358210156ac8315ab298c0a459f58050056064025a343f560200158a00c56520fd597b3a968282158a30c569e8a301e208569a421599f3a968280b5a7b845667ca65a690e1667d255a7b0096b40a314ea00d6aa45e58180156885fa59ad0656520315a637e9593808580300d698ca35a345216b41fa5ab27e960c4035a0a82966b408599f01565ec03596902d667d8a269128164d4a3585e085608408583102d6aa5b05a0a6b567e8ea58ea17934946659302816ac94836340c56b40035ab25ecd014035a0a7e965ec2159840c567e8375a347e96aca115a65179628ca3581902163f4215a636b406b5255a116b566b45e58d0015694421585c06566a99f598400d698d4858da0656178085ad002d6520a358fd281600c0258500216774195aa97e96b419f25a567d64805e35550c564945e4dfa2d9645c3158310156a4611585e00d6b40a0598a17d65eca35ad08d16ac8085a34179667c0b597b021667c31580300567e8fd55845ec96b431595501566b4025a1131d698c2a585e009661022583100567e8035a6301565a00358fd28150640b5819005606008589917968d0a05aa93a96b42a925253a969a66301d80096aa42159e70c56, 0x200559fa28168d0a35a690c56280035ad084569a40559170a968d00859042816a4402598401d6a45d116115216828635a0a0196078035a1102d6008025a0a67d6ac8035a9984568d0ea590f0c56b40a35a340716905485a183a9678821140800d64d4a336918d169ed485aa93f5628ca05a697e96aa663019f67d69ec03598a00d6a44085a7b28160c402598a12d684419594801567e8215aa9521645c0b5ab23f569a60a5aa928169ec0f5a0a28d6845fa599f00d6a44315948494d0c40859fa0c56494195a11495602c0159fa67d6414085a056b56140315a348456a452559ad28d6aa4a358830856629485a910856aa4315a7b17963f40b592528d6610a05a911a56a44055a6300d68edfa598a02d69a5485ab217969a611585e0156a467b58a00216014055ab201564280b5a340096a440b5a0a1796038035925021649451590d084db405e581e02d6084015ab26b407e9255a207e96aa4055ad08296120035802005661005591717965ec5e58cf00d6a6e91590a01565bc215aa982962800d5a4284565540b5a9682964145e584802d65a408581800d6554215a913a96828085987179667ca3599428164140b58ea3a969e8a35974554dac8215a633f56], [], []]
  | 10 => [[0x1fc1a597], [0x856a456829628d68d16065602163f569ed600d66b56281602d601564956179684563a960c5667d6009652167e96], [], [], []]
  | 11 => [[0x16], [], [], [], []]
  | _ => []

def C28_S (s j : Nat) : List Nat :=
  qGroupedState C28_initial 5 16 10 C28_patterns C28_values (C28_counts s) (C28_specs s) (C28_records s) j

def C28_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C28_initial (C28_counts s) (C28_specs s) (C28_seeds s) ws

def C28_literalRoutes : List (List (Nat × Nat)) := [[(0x5550,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x3210,2),(0x5550,1)]]

def C28_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C28_rankPool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505]

def C28_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r9 r10 r13 r3 r1 r2 < 3) || ((sum6 r15 r12 r14 r0 r2 r6 < 3) || ((sum6 r11 r7 r8 r4 r5 r6 < 3) || ((sum6 r10 r7 r13 r0 r1 r5 < 3) || ((sum6 r8 r10 r11 r5 r4 r6 < 3) || ((sum6 r7 r8 r11 r6 r4 r5 < 3) || ((sum6 r8 r9 r11 r0 r2 r4 < 3) || ((sum6 r7 r9 r12 r2 r0 r1 < 3) || ((sum6 r14 r9 r15 r1 r2 r4 < 3) || ((sum6 r12 r11 r15 r6 r3 r5 < 3) || ((sum6 r13 r10 r14 r4 r2 r3 < 3) || ((sum6 r14 r13 r15 r3 r0 r6 < 3) || ((sum6 r13 r9 r10 r1 r0 r3 < 3) || ((sum6 r12 r7 r15 r4 r1 r5 < 3) || ((sum6 r9 r7 r14 r5 r0 r1 < 3) || ((sum6 r10 r9 r13 r2 r1 r3 < 3) || ((sum6 r13 r9 r10 r1 r2 r3 < 3) || ((sum6 r15 r12 r14 r0 r1 r4 < 3) || ((sum6 r7 r9 r11 r2 r0 r4 < 3) || ((sum6 r10 r7 r11 r0 r4 r6 < 3) || ((sum6 r8 r9 r13 r0 r1 r6 < 3) || ((sum6 r9 r7 r13 r5 r0 r1 < 3) || (false))))))))))))))))))))))
  | masks => C28_rankPool.any (fastEntry (compactGoal 7 9) 4 C28_coords masks)
def C28_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C28_patternScore (C28_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C28_rows : List Nat := [10, 33, 44, 52, 65, 82, 84, 3, 5, 9, 17, 6, 34, 24, 72, 96]
def C28_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C28_rows)
def C28_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def C28_ori : List Nat → List Nat := literalRouteOrient C28_literalRoutes
def C28_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 9) (compactCover 7 9) C28_S C28_N C28_idx C28_ori
    C28_patternScr C28_patternScr s
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

def C29_counts : Nat → Nat
  | 6 => 0x27020003000
  | 7 => 0x506c159036001
  | 8 => 0x51273127004
  | 9 => 0x10808600d
  | 10 => 0xc004
  | 11 => 1
  | _ => 0

def C29_specs : Nat → Nat
  | 6 => 0x601501219000
  | 7 => 0x301681701599119
  | 8 => 0x69969959a29a
  | 9 => 0x61971a39a
  | 10 => 0x51929a
  | 11 => 281
  | _ => 0

def C29_seeds : Nat → List Nat
  | 6 => [0x0, 0x5, 0x4d8f384610080800808, 0x80847f40020128270b50010020d9, 0x0]
  | 7 => [0x2, 0x13a1748e3b05b80e01709e0581f00c05400802, 0x40015ab700288d30a68f19008433c83b4275834c58a032824c03d2159025805900040070038085002c03001f400a00080290068005036c0030098381001010400c00050018001015800409e000f021c014856422585640a3003615982bc167856400305d810400d80010008011023002301400610004001000c0018564008025c001004c167001c02f000c0a50030005051203500f0072, 0x220c00832a00d106c02007202d000401d01f0008004006120050800409e00a004048002100904d019c0f0059, 0x403]
  | 8 => [0xa, 0x4752702b434020711300ec13822004008e80669820c4008121165dc009d50120080e80396f49c4a91c1020380083f00217406007090050018183503440201606004555cb301f1ec4f01304a13c0081c070018028070021bc0080301c0cc0280280699409039, 0xcf604001c249e759939802801809d01c00146b40b19260b3c00202490710e469e0068df8114054001007037806e0a30021f0009c00500081f451632a8dc801408400607c00f80b51a88d2019428a001000818c01400a8b7c3a0174002116016c90a001009c2cc00406e93984a401402d01680aa12015401f00980ce088017008c00205106a04b000a007814001816203a0148134002226001804002e010035005c23c19802402480a200106c001400602503980480940ca036800c014044006824001602c00080a802200100380a407800500081c4032001812c9cc05802b00a00040a201500d80b403a082000801403c02e003007801602f00c0104012002, 0x6030800403a00763904b00d200901800241c805600280a4126016000803000a01a, 0x0]
  | 9 => [0x8805502, 0x14009a50080040004015000c30e1394060005403e000801b009801a019801e0004026002000200340060034001001800100e802400080020004022, 0xf1b800100406d01266938b46405c01e0011bd0ca60200f0620aa11e00400300610701604103a02400e90803202506d8fe01400100208800100a00700a0249081ce1e50048a400a00100100700202b00e063865074003002165005053043059005828, 0x0, 0x0]
  | 10 => [0xa, 0x1a802001, 0x0, 0x0, 0x0]
  | 11 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C29_records : Nat → List (List Nat)
  | 6 => [[], [0x117268e3e000], [0x9a98a9aed5fc718d95793a50f93466ccc4c54f178137288cd99dc9ace16903f05481f311bd6a349ace46e03dd662c76f3163a2b6a5e2a903dda62c6bb5471a79899bb8d78e6263a6d93469a4b6a5e04c54cd256f0eb5de37598f1e2ef4e5dabbc78c8c1b], [0x31b816d8bb8515461db4d462e8a536cd125dc672ae198bacc50eb73131139aaed5f461eeb3143a2b69a92705268c99adbb4c48e62622ad1b8525b42e69268cd1c14d8c44ee1495187a1c64cd265f193351c1522322eb6eb3123a4b69a92662b92ad198b34c50eb6ed5da3a519ccd26e0ee3123adcd4c44e6aed5dc36bb5099a2946a32c975ae4ab86f73b939997c9a33464d1989d8c2d29b62ef73b5831adaed5ec6e1497607], []]
  | 7 => [[0x1c], [0x2c82430a5caf122a1c518d743a6386f16b98979daf312976bc7d75d2e376e6654c0aab091e2a32bc2caa80959121e54c8a8514615e225424ac094f85e9e22193c3956112d820e5b9a951829049c74a92150d2a20556c4b988bf5e74521539f94834e36b9ad7], [0xac430fc54c56ddc63e6d72a79310dfd4d5776f04627756879f890def24cc5cee1313f313153758ab3cee056e6225af614137a2b227d15b73daecad6cf316b8aa0abdc2187e8a82af8d8c5b66ae75da904dd2837ed5b41378ab2e7e0972ee86d7d6ca30eb988aaba74c5ce6232af5b5dbbc1418fb90999f1b813f5b313bac2e5dc05afe5c862e6bb37f38aae6dd6e32ee32d8d71031db9120abd60c4eead0c3e713173ac4c4fc660b6cde37ecde31739798b9c419d3eb6836f45694f8cbaf5b48c5ae8ac99e612a79a7891bd0d73addcdad73631f3c1465dbe1a3ad1c62e715654fa198b5c6505cf05343f705cbb6318b5d5a147d2660e70c5cdb6598b5c28c56e1eca9f81a79fb5c60fc66276e1461b759869f76a1f3dee76ee62b9b6692bf93094fcb5da9e6b66177313173318dfd495a53f02db9ed7696bc0be2dc08c56dd8dad7859b1fa19875be1ebe5dc49cf31694f8cc3edbb86fda2ad29eda68ebb7cef5e0a6c7f14bc76a33173a7cc4fa0cc5cd7266f3588cbb4418b9b69abae44ca9f0230db75ae75bad0f9eb7353ece31ebb54c4fd6e187f050f3f3165cfa4b6b5d58c2ed6e62e75b851fad87df444c56e4462b74668eb8cc52dd621e7e6224af82851f6518b5b34c3af0b0c3f45a1cf98b627a08c5ceac826f46a1ebc54d8fd25b52eb261770f66cf6d353c9846fea8aeb9f4f2bbf7712f3d5a32ecce55f382981fb1989dc66176ee0826e7631735ca0b9c30c56d7254f30a654f8cc32dd25b73dd662c71966eb86b327b5d91acce54f2cb30eb8c953cc6597aead313eeb316b852e6dcc4c36f174f775b879fb8189ddaa187cc655f33166cfa44675c89736e045eb6ed5deb4718f9d15953cc454f2cd43e7b843cfcee296e4d19b2d741733394bcb30c3adae55f2eb6beb6b99bcbe1d7ad72a8f35b5cbbb543cfc3d736ce062e76a5cbb913627c30c16e94dad7641bbe692e75c59a73e92da9f0c654fc15227b6cd1e72a62e78d6b6b76aef1c30657b0224af4241373a98b9c09736f02d19f4565cf8cb4b5c3d055daea8f383a44f35197cd14993e8a62b6d765ebc1179dcc6336e8ad89eeb30ebb5189dae0c9cd9660d795c11f98b2a7d15a33e3255f382861f, 0x18175cf8cb79dbac4b9ec263770f30db5da0b9c559b3e330ab782a40f6bb475cd4495d8c82cf0a41578532e7cb6336dd662e756313b5dabfcc660f6e1882aeda6a6bac185dc65a9e5b061d6cb5ceb9dcc6dcb8c5cdb0b9d7438cebc14c4fd6e627db0d7d6d330eba3513ccc5d73d0461e70c30db7718b99bcc7cd041fecda686b8220ebd5972ed9a62d749684f9abb67c6595ae44cd9f314157a2ae6dbac659ec7113f0f315b86986dc8d953ec3103f4968cf8c99bccc4c56e3303b6bb41f36bb375a386fd976afe2d230eb3399bcb1d059d7255f2d8316ba3452d9bcc5cca832f94f8a1f76a0f3c66056cc455f319547987b2e7d62147e8acd9f3631739132e7ae507cd94b9d75b43b7c1185dcd5055e44d29f456ecf], [0xc6c9a3565d6621263989bcc54e4f1980d9b5455a43dd66f31636d3518da6b70f379787bb8c54e1e622ad977344c58f054a688f98ae551671b268cd975af0c98e8ad76a596bb518da6e2ee316377130499a6d0f31535cac0afc70770a50f61190afe2f7496d4bc14d8485eb682313375af1738f1b456dcba2b5da32e32fe3359adbb8c4cf1abc54715caa12be287198a4ba1c9e332eb736313398bad611eb6bb4133c6bad798f0519811b5cac151c614ca30cbadc3d045e62eb5ccb9abb5051ddccd3163ab429943ddc622af1a1cbe338f1ade6dab9b49cc54cde622af1adc3cc46ead0a309b76aed058f1b82a40f98af0c94ddcdc31639549e3366acca30aba1c66052f05366c0fb2aed5fc66d1431539b334c58eb66f31335caa049c66d141956adcc4485e62621253c1529b03eb7354117669bcc58d76af41719aaed054e62eb1247adcd4485f1b83a40f98a544959d6b95863ca5c2943f054a6d8f5c9bcabc662cd1247c1cd8c54e9119814b92b6cd56662b9125365238c38eb70f668f6d9a8ade1c8d76a71a2b6daf2e4f193559b2bb5778ef7278cd95ca5449cab6622ab98cc5203661ecd314b853291d1cd4642bf87719c498eb6cd312b879bcc54ddcdb31636d35189a5d6b91263], [0x52a4edb35495e2c0c857e18dc1d29b62f1b7b5e2c18e36f7278d19]]
  | 8 => [[0x7708dc], [0x4939797080e3e5c314e11716ae16dc19b84d7128e35d807385a7330e3e1756b8b95c96e269c773826713aa0a1cce38a37082e565c4ab8af700ae1c9caf39452c98e599cabb87f7162e575c193804721969f1c2cb8b9bcc6bbe1c28389b721568b1cafb862bdc8a285c56390fb548e20ae14b96a1af0e571c03388d7056e53dc9daf95702ee0edc3c380d7028e5b5c6fb8197078e075c8614087030e2d1cb0895170e8e1c1c8516ef70b0e29dcb438f470dce2a1c0d38824d00e465770397f70c4c119c74b80c71c4e0c5c30d6ec7002e301c315634714ce229c91186760c2c5b9c30ae917112e5a5c72b8b372cee2e6b4f3809705ee56dc75397e7146a20d3aa38aa709ce35e243b8e870dee241c3144437130e041c24b897722a5c66b4139967164e111c18395671f8e2adc1bb76170a2e0f5c4b3970191ee46624e388171e6e399c22b84a72b6220941539657036e0fdc8694625dc6e5d1c60b8c6432ee2ed71bb9812a6a5071c7eb95616337c3ccb1382772b2220dc45b95b1aaae55867d390f2eeee009c47388e521461edc9898357144e27dc3cb94f10fae43ca70b875704ae2e5898db3128e6e1b1c10b96a143ee11dc73b87771c8e3c1c0b382370c37b09ca93915310e9a0a652b80b716ce569c1239196132e430b0538157222566dc, 0xa9705ae0e9c1f385772625d58450395370f4e56c5bb3822722053c9c1038b072145488bb939607230530dc78b8618918e514c5cc4f771bce275c2b3970149ee430c09b888705ce2b9c], [0xc2428aafc28aada6043217574e91535e1d53c6c30a31051786004a3218574109139c430ab51bc43217d775818f8d450a5c8297c14d8029851aab26049b0953c1ae57bf20935cac17ab2c04310297369897ad9897ac4300b828c4cac50a8e428ac6af178a9bca4c189793c30ab2d444bda093afa093ab15c451829363028fa7bb84611bd385260aa04c4a6915cf9b4657b2cd4a2a809a75ae57b2d584ab23845e9857a195cfc6cf974a07d3cad3c48cc017a1c64e87c3caad80848c9917c4cd8abe56c46bb44e8d430a9e2e5791260ac443ca8d43cab595c4b527447c379780809aab0044a29bca9b41ca81050a5c95d775aa0fad850498828ab2d6c49b430a9f450a9b428aac87c43217976a009a459bd3310097ab00846515cfa643cac82f17863b8ac6d58487b347bdd6c48c95d765184e5c8057772e5798ac0a8c80979643cab2ae57b826048cbf9787a60ab8c30a62130f3087d798cb8a54051a853287b298576bb516a2b447720913b298975da0979018976aa0934a891bad9bc49ccc4a309857cd594465818fa5430a1b051b8798899b0a935da091811c0ab509044a829bafd584b8a1d39bc28a9b420a3109578cc5178a18979b18917c3b9737985775808f9b2e57c820d387808aa1ac0f33009aafc657b5114430819797c50a759d4fc10184471bd38515ca4409132a851a85090a32189797450a318c976306cf93ae5791090ab8028433051a81018a69018f6a9897770b933389174e8293b2a1d39dcb978e18574c209385185765850f6a051aa52e5786430ac6c697861bca4215d3c1008485018ac69797ca89138a1857b2cc4aa543ca7709133095d7b2a0d39b0c9358185785028a77209354019a7718574c185766850f4702936a019a77130f581d535e2e57a1818fc6c28a8a890a411bd3af98579043caa5c30a6695cf470913ab1bc4581897c1d444a5450a581c139b450acccd8a882c0aa2a60ab809045e1857a2890a8795cac12c04ac050498c50ab52c048a0c9b75ae4e378953672c0f692c0f9128cac13b8465808f8a2e576c008f9b43ca68a093ac0184770a93ab0504, 0x8a428a98850a6c018f30809763090f2a051abdcc4aca95dca6c50aa2ac0a3789133518975c85177f1897b2c28aa1450a853b8ac19897a541ca912c0ab8d6c4c6c6575189134705937595cfc14d8ac79897b2d7c4582093308517862c0a758913c1c28a7dae57adac045e1c13c0b78a8aac0a2a8c9a6da093c94c4ac6c3ca86018a8aa60a610ddb8789caab06c494c30a3109178cc097c6bf178d18976b82978a828ab8c3ca98aa0a41005397c657988908a54c4a470c93b2c30ab8ae57c7558485004ab8a093bc21d385050a9b4b4a66894f6d981793c3cac115c4bad6c44105136c2c0f87ac0a98808a65018fad98835cae5785008aadbb84ac2c0465238f989bca6b15cf86050aaf98979b1897880c8aab185722891bcae0ca5caa17a2b6c7ac15c447185787818ab2d50466818f2a019aa51897a0c50ab898978a418a9ec657c1cc4a378a9385058a62829bab4280c1d584c1985762891ba2c50ac697576dae5765008f602e57771897add6c48cc657bdc3ca2a819a350ddb5e18978c819738091398a54a86028a310057ad8b848615ca87bb8a720293bdc30aac430a6ba6178cc50aada0846b8917911bcabdd944c6ae5787828ac6cc4a4e8913852c0a90c657ad95c44aa0936b9bd78cc089669897b0ac0498890a5c8197c6a0d398bac73382978a914ab2a093ada082bed9448a420a412093a52093b287db33019a98ae5769050fa1c50a1207db96c68aab1843ac00848115ca8c8297a2b90a2b8c9b3393178d18173a89138c15caad8284afd6c4c1c3ca26029b670c8f8cac178d185766808f9dcd975e1ed3ad8184c6b784410093c105046b99179895ca75850fc0bb8a6c050f93989751931377095369008f378c939e4c4aab01845caa1622829bc697d7bd98976d98976e189798bb8a3118975e1917b2c3caa11bc465050f5ca61765ac0fad80449b4c4a581e535c9bd798cc4a91028a2a009a8ab4875e1817770c938c80573518175c9c176c15cf8cbb97c69857c1cd8aa1808f652c0f80819a8d41ca1e091bc71857adc3cab15584ab55848ca61798804ac25584308057b2aed7, 0xab3b84bc2093851849b08c84308917adc3c054009a5818d76db14f86260a6595cf75ac0fada093a1850fa2828a85428a721bd34e9bd33101976d9757879bca581bd395c50a9aa088a7450a7f2e57ad8904c1c30a8aa74aab090457a0939aa08aab0284308297ab428a6119175c89176218979b18578d4657b5260498a60a68a1d38c8917631bcfac3b843798918c8517c6989785238a8a43ca580ddb851bca8d2e57afc30ab4a0938a430a8d428aafcc4ab5028487804a7718918c9bd7c1c18a3519176f0913519bd38cc5093115d798c68ab81bc4759c0fc3430a5f2e575c809766988e26091bb82c0476a093bdae5793c50ab8130487850aafae575c9f9786008ab2c65766ac0fb8cc4a5ca557a5130f8caf1737989791130a879897668a8f3115568cbfd75c99174101934115d393c1ca68989798ae498687ca41029387890a98818a6bac17afc3ca80851a7f1857c1c65786090a81008a], [0x18d8cc0895caa0deb43d9a241f1aee6d9d8db2c683669884873b9a22a34c455122d0a65050787988484c28c21426f71a8a146a3215d598bacde3cda1e2422b70f12017bb2a0826d9a8aeb1bcc42446ac610a0765afa082a1c65fc760e94db1ddcbc32238d5e1c115815c64caf0de6444d4642bad8d8d4509b2cd5044636cabc0f1abc37a356650501c6b6da2763706bc0ead0a0a018d6db54e75ae4de72f1606446cb278a15655da091c6e0e341c3ddc242178b937a33137890893b6cd4b46628fe271b4a6d9d5b3109035cac0de8d2a4edb1d789832230f37890898ac0de463604bc270771a50f83a534476bb5188b4d8c424466d2712118d8d40895c9bc488d6cde240a9527688eee24090dc1cd84843ad606f366cbc32238dc1cd80adbb84814c5726f26b6821204ca47050d9b45048452a28d11ddc62122319813f8965184287254de244b1b7b5e0765ada082], []]
  | 9 => [[0x2aa5c7a5ca481dc338f1], [0xc4bbd1c61380ac232b9d5cbb3824a0f6e029f44b8957172b81a17e38827160e09304c60de7098e021c1fb8047262535632bbb5fc0d4edee30fb90c2814eac237738b67028e85234438e47048fd6c403460aa21450f1c12382570dee3bb001390f29049b6ddbdba028546e355d013b4a8c2908e9ca53a5771618595d0359957049181b038386f8c54e005c37d0578d311a39c623b717516e052c68ba14c2bee891d0db80a70af63b9d033b547130e82a37747718ecae1bf0a8b80c708ae00acab395610deeb4636dc6b074af800b030ae7972fce275c02b83d72b6e57e3b2e15f72f0e09dc17381672cb180a30a38067020e261c1938a872d2e1b9c], [0x771bdcb2a61c09019c689bdc01009c0f019c77379cbc595c773b9c93ac1caf851c83009c03819ca5091c8a019c37891c21029c2b891cbed7dc5b261c58261cc1819c64029c66891c5e1917bdac1c5c9bd79b3b9c68829cb2ac1c759bdc6d9bdcb8891cbdd95caf95dcb2819c2a891c62091c5e019c8a009c9b051c7f019c7709dcad891c85051c3507dc35091c9b450a5e009c77029c68891c310917bd829c05029c6d891c6a821cb2809c7709138a059cc69c1c4c091c7f15dcb2851c05019c58029c12051c5e051c12091c2b819c0f051cc1bb9c0a051c35029c4c1e5ca5021c581bdc77091c2b851c83019caf8b9c5b2c1cb29bdcb8829c4a9bdca8809c12019c8d051c24091c621bdc6a891cb2829c2f019c0a029c3715dc01809c05009c0a005cb2bb9c8d15dc01005c7a261c47051c2b809c62029c4c059cb4d7dc4c009c05005c32095cb4d95c379bdcc6ac1c989bcabf595c2e019c03015cc1cd8a2b95dc68ac1c7f009c37851c03009c32051cc6809c0f009ca5450a8d009c581edc688a9c09009c5e15dcc6af17b8ac1cb8d7dc12009c772c1cbd86dccabb9cb2d7c44c261ca51bdc5e2c1cb295dc35011cafbb9c612c1caf829c1e819c8a051c6da61ca5261c8d450a37819c7f051c32019c24029cb8831c32009c9695dc37809c3789137a3b9cb2a0938a15dc8cbf9758091c351917ab05043215dc6a829caf9bdcbd9bdc44829cb2891cb8a61caa019cbb57dcaf891c4c051c581bd37b2c1c03809cc195dc3795dc6aa61c30851cbd891c37805ca5029cc6819c85050a58019c37829c582c1c2b829c58051c93c50abf15dcafd7dc4c029c0a009cb2d95c541bdcbb3b9cb89bdc5b15dcbdd7dc9b2c1cbdd94487890a0a019c7715dcc6851cafac1c77261c4c019cc1ac1ca0ac1c12005c9b019caf819c2e009c29829c6dac1c6d829cad89049b009cb89d5cc695dcc6c697afa61cbeac1c65050fbda61c7e3b9c77019cab051c07829c9b15dc03019c8d019cc1851cc1809c1d009c4c15dc12029c2e051cb4a61cc6bb9c77009caf809c58009cb2a09c580c9c6a9bdc2b841c, 0x5815dcb2d7dc77051c4c1bdc68a61ca52c1c30851703005c], [], []]
  | 10 => [[0x7708dc], [0xb2b80270aee1bdc4c38147014e3b9c1238b0700ce57dc], [], [], []]
  | 11 => [[0x1c], [], [], [], []]
  | _ => []

def C29_S (s j : Nat) : List Nat :=
  qGroupedState C29_initial 5 16 9 C29_patterns C29_values (C29_counts s) (C29_specs s) (C29_records s) j

def C29_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C29_initial (C29_counts s) (C29_specs s) (C29_seeds s) ws

def C29_literalRoutes : List (List (Nat × Nat)) := [[(0x1040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2120,2),(0x5041,1)],[(0x4004,1),(0x2302,2),(0x4014,1)],[(0x5040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x3221,2),(0x1051,1)],[(0x1404,1),(0x800,4),(0x80,8),(0xa00,4),(0x1312,2),(0x5115,1)],[(0x5400,1),(0x800,4),(0x80,8),(0xa00,4),(0x1011,2),(0x5400,1)]]

def C29_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def C29_rankPool : List Nat := [2112664, 2182779, 5532295, 5250494, 5311951, 6637690, 6381484, 2117516, 5451421, 5258426, 3304841, 6576760, 2186617, 6426319, 2177943, 5447614, 5271211, 1064122, 4403101, 2125193]

def C29_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] => (sum6 r8 r9 r12 r3 r0 r2 < 3) || ((sum6 r11 r7 r14 r4 r1 r2 < 3) || ((sum6 r7 r8 r10 r6 r4 r5 < 3) || ((sum6 r14 r11 r13 r1 r0 r5 < 3) || ((sum6 r15 r12 r13 r0 r1 r5 < 3) || ((sum6 r10 r7 r8 r4 r5 r6 < 3) || ((sum6 r12 r10 r15 r5 r1 r6 < 3) || ((sum6 r12 r8 r15 r4 r0 r2 < 3) || ((sum6 r13 r9 r14 r2 r3 r5 < 3) || ((sum6 r10 r11 r12 r3 r0 r5 < 3) || ((sum6 r9 r8 r13 r6 r2 r3 < 3) || ((sum6 r8 r7 r10 r5 r4 r6 < 3) || ((sum6 r9 r7 r13 r5 r1 r2 < 3) || ((sum6 r15 r12 r14 r0 r2 r6 < 3) || ((sum6 r7 r9 r11 r3 r1 r2 < 3) || ((sum6 r14 r11 r15 r1 r3 r5 < 3) || ((sum6 r11 r10 r14 r6 r0 r5 < 3) || ((sum6 r10 r11 r12 r3 r0 r1 < 3) || ((sum6 r13 r9 r15 r2 r3 r4 < 3) || ((sum6 r9 r8 r13 r6 r0 r2 < 3) || (false))))))))))))))))))))
  | masks => C29_rankPool.any (fastEntry (compactGoal 7 9) 4 C29_coords masks)
def C29_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C29_patternScore (C29_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C29_rows : List Nat := [28, 42, 49, 56, 65, 66, 68, 3, 5, 9, 6, 18, 36, 72, 80, 96]
def C29_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C29_rows)
def C29_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def C29_ori : List Nat → List Nat := literalRouteOrient C29_literalRoutes
def C29_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 7 9) (compactCover 7 9) C29_S C29_N C29_idx C29_ori
    C29_patternScr C29_patternScr s
def C29_F : Nat → Bool := certAt C29_Z C29_N 12
def C30_initial : List Nat := [0x744, 0xa92, 0x1929, 0x6403, 0x90c2, 0x140e0, 0x1a01c]

def C30_values : Nat := 0xffdfffdfffa7ffbfffcfefe4f7e9c7f4c3fa617d07fe807f0fcf8717c383e1bdf0c2f80e7ba7fd83fea9ef47e7a073cff9e75cf3a27987fca3fe4fcf271f9383c83fe41cf201f9003c5f9e21cf0fe78473c1f9e0e0f01e78073c001dff6eff7f6fefb5e5d9ebecf4f638bafcdd4e2e9717478ba1c5d0e0e8617400395e5c8e0e3f27138385c1c1e0e0707000b8001bfffdfef6fdf77a7bbbffdddfeecf775bdba9edcffee6ff737bb93fdc9eee47371bdb81cdbef6dd7369bdb41cd96f6c87363bdb11cd86f6c30b6039b000d7ef6bd735d3dac1cd5cf6aa7b5439a91cd40e69d734e89a71cd30e694734839a31cd10e6847341b9a09ed04e681734079a01ed00ee800335a599ebcc94e630b21859000c54961d1300017ffbbff7df7aefa5779e9ba71dd00ee1c16ff7b779dba4ed9c76c03b5795a382cfc96747b3a259b8ecc0765e3b281d938ec9c16483b211d900ec80162e0b0f058382c0015fffaff6d77a6b7f75be9ad7956b82b3f359edacf5d67a6b3c15929ac7055f92a9c152e0a8f054382a0014ff6a7f253bca99c14bf2a57d52bce95e54ae0a5495280293c148e0a40051f928fc14744a3705178289c14404a20050f8285c14200a0f05040281e140e8a0725038a81c340c0a04050102804140009c94caa4a40011f6d8dddc67a6335319698c9cc64b632530fd6856942aca15350a968549422221061080083a240001fff6ffef7febbfb4dfbd6fd2b7e61bdf1ded86f5c37a61bd309e806f0c27749bb00dce8ee6037281b900db5a4d9eb6c6135f19ad84d4c269613430975a4b9eb5c94ae3096f8cb4c259612c7096184b000554929d114880a0004fffa7fbd3fac9fc64fb6a7b493bd69dc24e6126fed37d69bd24ddda6bc935b49ad64d69a6b4935849a924cfda67bd33d699e94ce1266ad32d299394c96a64ad325298e24c6926329318698c24c08260012fcc97d64be725f1d2f8c97c24ba225b092b8494c34a6125001278492d2496324b09240091e248e524719238691c248822440121c490da486b24349219690ca48632430d2180908248402410920809002480023f5915a48a9a454b22a491114880043a22030101048040400120000fffe7fbb3fb79fcacfd267deb3ed59f5acfa767d2f3e959f4a4fa067c033c949dd1cec0675033a619d20ce88674233a059d00cdfae6f9337a39bb4cdd666e9b374b9ba4cdd246e0336819b20cd8466c1336059b00cd52467c733ab99d3cce8e674433819980cca0664c332419910cc846641332059901cbeda5d292ddd967a4b35259692c95964a4a1825022280013f589d244ad2255912a4c952448812411120008f88476423a311d148e88468021211080080003f6d1e948eeec7272392d1c958e4a46014300017eb0ba4855342a9615498aa485022280a140009d504e98274613a289d104c202508110308800420a2100100007ffc3fde1fed0feb07eec3efa1f6f0fb687d103e521d690e96874ac3a521bfb0ddf86eec37561ba90dc906da436721b2d0d9586ca435a41ab20d4d06a4c35241a400cf5867a4337619b90cd5866a432da196b0cb4864f4327619390c96864ac324019080c8086400318018200c0406008300218000be305f102ec8174c0ba305d142e8815020a20850002704120008e00448022101101088004308218010a2084d0420c210410800830041302084104008140408420401010080484020200810020800840001fec0fde07eb83f581f8c0fc407c903d901ea80f4c07a303d141e880ed2074b03a4c1d240e0106810300017a40bb205cd02e5817260b92057902b5815a40aba055982ac8153c0a9b054d02a5815260a90054102a0014c00a1205080283014040a0004e10270012400914048402404120008e2046002248112008830441022001080082804108208010240810040482020100808020400820000fc807d603ea01f180f88076c03b281d900eb8075603aa01d340e98074703a301d140e800704038001a080c8006040300015000a0805000261012080900041602080103408100403020101004080003a001a000c6006080303018000b0805800292014800a0805000244012100900044002120108008200408020201008080003c001c000c1006000288014300a0004a00242012000880042402100104008100404020000d6006100300017000a30051002480120008a00440021801060082004080200008400400018000880040001c000d800600028001200088004000140009000400018000a000400018000800020000

def C30_patterns : Nat := 0x9596559955a55595465158555959655995565459155d55665596565659556515855596565557555a55665595561557555a55655575559555555155255455495519545549551954595155195459515945549551654565156455465515945591558555

def C30_N : Nat → Nat
  | 5 => 6
  | 6 => 222
  | 7 => 0x595
  | 8 => 0xa5e
  | 9 => 970
  | 10 => 28
  | 11 => 1
  | _ => 0

def C30_counts : Nat → Nat
  | 5 => 0x2003001000
  | 6 => 0x7f05a005000
  | 7 => 0xc1393d107e001
  | 8 => 0xcc6b22db005
  | 9 => 0x28912c015
  | 10 => 0x17005
  | 11 => 1
  | _ => 0

def C30_specs : Nat → Nat
  | 5 => 0x181281101000
  | 6 => 0x601681381000
  | 7 => 0x481781681619119
  | 8 => 0x70178169a29a
  | 9 => 0x69969a41a
  | 10 => 0x41929a
  | 11 => 281
  | _ => 0

def C30_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x9, 0x2, 0x0]
  | 6 => [0x0, 0x1145, 0x456a08b571008c0d00e200240e400200c03200380aa002001803c00801315a827800a002, 0x4c2467e509486b1bc12d00103b00187f00200901823e2000460340010120fa00e00487f04984a00a825822001009006, 0x0]
  | 7 => [0x2, 0xe92b103200102e05d3e103b05186a0021580980a35c800203b04000100600100400604603584e00d80719300100e001, 0xf807b801888c00100408ec03e0ed0770dec49a0140a1cf4400200200486240d738d2138050f0c0329c1a1f4830059012000401a42910f827c00606f9b100101ce002024804c79c0839b0000809400500a808c02c09c01089b402d33b03a05b80ab33a00a02e001870b000801c83200201605b06dc027085800415003405f4cc43e201e00201e404000502f002c22600400088b419e00900bcf44002002062cf4400202205c800804b309001801ca441a50fd4a927a203f061ca825041ce006802000200c001089c02004d000c91024600b08a80ac0b20311618108094014909022c00e04400480c27a200403000d80d80d2011801c00601002447d80b002207b818c370030045477c004030006800803200f014820c02000100280040051d2009800404400904400880ee00f8e3001000815e000800402007e0028348004002007001007400102c003826805900b0008002052004c1bc0ba008012800405403000d06f000203800a003a0b4002005809c00201300081641ac0a00158004002004034801a0ae01f01f802c02c1dc, 0xb118013800600e800940010ca60004071000100010016001804d86f1014212a40c701f5001201340050069002e00e43828087004000901fa808800b6003002e8007001204c8000c0e60006002c0830090000a000a09c8104002c00c401300ef001c000c00c800181c000080140043000a00140060001001e000403b804001bd0240048801e808e00440010013002e00040be0001, 0x3540b03]
  | 8 => [0x1a1, 0x4b6e57c016008023c02c52095c887825404702d80080e412b09591c471b2af4eb84607b610102700141f817e00a0004042003009987c370011005800a52600e05384301d41230f983541d000400186b800a01101f007c11a001018004000b233919000401000a8ed00063b0077012c6a409e001002014227201e2418c481185470a3833c0020240e683c41780100c481100ec04a026c4b0030003008800625400388e803429b2db03b001036e0a7059cb6c3a000700b001410204000200041f200d002000400f05a001002439201907703d40020010090004004014007802806a0020ed003400a07d033802c218003029006800200700e000c033050026001400a0e8000810808e014002800c0280d603b0a240440080008470002003005409c008032006005809c005, 0x3b704fc012c15a0f16045e0004063c61311d4001e2f18554024116b833212b31bba02fc20e808313360f6c0180040021a02262d5800100e4000808400d00002827400102360462047017a001e03b004762af80820048000c003800d0476001c030000d8aa8001800080318d6513e8011001389dc0354006004e07080088011832200740ff800b46b2010800040020001899403dc00d00010188005a24a00130030001c1ab833289100006229444d000219ac00a807b179c00e81260001012d1040001813301980f0c002912e878220383b6c38c870a1b8e1ac000408080118037000300ba00963590027043005240cf80040004032c001c33b02f400b00040093000601b0008803b06b50b0402f0001000400283110039097400b80448024011c00a409e823502680204120819702231ac8051800100061d4a157000513b60098017003c018000dc00c000b00030888039800c00040004010804f043c01cc00a0056001e00100038008005000140ed800d0030048003c82060014000c03e8032000c0074004421c01e60008005c6b200100010006804d83da01680070014000801f00580098001a001409a81010006001800200470198014c282006900200030003000e000208cc00b002a0002010c00081680002002e359005783bc014804f000a0006001801b801f00080080028000501d2000c0490016004a137401d8004005602f0047c19600ca018e0690012006e0028009807a000400680048002012001080008189001200e00584099000201700088035008400c004a0002010e00080ae806600d6000635901190330001c0108002000a015000580010804005000a00ad80ae005c019011f00500004050801501ca00140b700e3003c0004005002300831ac80008004000800580098083000200e400080090002007400080010390000400180f7005401e804c80e1003a004001100f701fc010c05c002c00b800140010001000a032400180980042000c02c810f0012000c094800200271ac80008003000a00100050027001f1ac80008022000400060148007000e00100050002000200240110001026e000c005c6b20004000803580010012004e012007f002200381020009, 0x3b02202c500f000d4ce00070200c9900e44ef8278072001001d00b802e0a24018019000800060780078069001c00103600180008078018c0670004039000400f000c009045c0010268178001002200b20cc01a00060004001, 0x0]
  | 9 => [0x210107041152, 0x20580ca51f08206f40820af0010036256631068001c16e1180fe812c01e01d87d016045c02703d436c1e30a000a8110024002003004024400c000801404800202a04420a405e0008004020204027801001406c00e807011c00605c805c02c00c000805425b12c001801c01600d80bc0362580170098018002008, 0x2000a47d9429584078004081c8f801f201070014844400300592a000800100301de3d91e000800ac01a0b3077032845719e00480c834c2fe0a68be83460f915d0004002003008814151c1bd00201f438413a01a80140ca005013002251203500400bc01405e887800400201200900103301bc860000617d0aa0008e7614a08100d801c08005a02085fc3b8016011000402e520002046402c07501808d80200cd00c803c0030779448220004010016802004e0cd007801e0c303a00480440b604f00f00a002400a069006c00302d009800405e00c002004800d007001001405c00a1db8004004074000ca2401602e009015403008400c801c0c200800f80b4008002045019c03a014, 0x0, 0x0]
  | 10 => [0x1a1, 0x2451703041f, 0x0, 0x0, 0x0]
  | 11 => [0x2, 0x0, 0x0, 0x0, 0x0]
  | _ => []

def C30_records : Nat → List (List Nat)
  | 5 => [[], [0x16f97], [0x17b5ea1ef8b843dd17016], [0x2e0b68fa0b705b46d06], []]
  | 6 => [[], [0x150afb1e7c7f76d63f3157], [0x2c95ce3ba4ade5bcea21f52c049ec97466dc16b97b5ec81f514049ed7a8c7cd931d6abdcc5770cce5e027472d93510f7edd1cb7027559c156f2ded5127b80facb57afcce95571b5b13197b26028f71dc45ee036b3593528f80d7fc764d5a3e525fa9c7ab4d5b82d62f011b59a644eab4c6aed6abe52374d2d2d6f5a047df57097b24fa9b6bcca5ef0b287dc3640f38460f0e62b795c15a72dc14b3698d3aad601cf2e9a904eafeb571809b8cd25c051e985a5ade36b8fab6024f601f536e198cbb82ae65b214b96fd9f596654eab5c16c977ece7c76c5043dc118364047d65b86622ead9cfc5d25a72bfae9e5570e1e36bcc65dcc1736482b4d5b5e642f6d5023ec89465dc11cd68e95cad6bd043dfb4132dc33317b86821efd9b59ae0b68bdb27d4dbaae02e738b9e2e180d3cc71cd6], [0x5af31c725a6352d42a2e92b67fe1ab5805ad8d45013709a9a904ff33705b54213b5e63508ab82b19ff8641749698b56c08c023b86674e8b5b531b8c4ea2808da4d6bcc72893905692baa594b9a7519c156cffc331c730d52b02a23e86daf651f436c9809c687602e67d45b5ec85086d311eab656d799d0a27705b541077edc63eb0d9131ca30ed799caa2b33aa2a351b2a045461daf642962e02745c6c36bd050d0b74dc656f0d3520ba435fb745c6c34d482b4957edd33ff0db5425042e907055b4b28300b5d1a0a638e634c728c8146d798e402b64c04e8c5b82da2ec3daf31be61ed798d4b276bd913187b26a27185dc3654081e3256caea964d44b987b5e8252c5dc16d4fe5ad798e142b513f66d269417d41e8d95512962e907edd34b60520e98db22638e635c333bea1e508118086fda0e70e18f55b2baa47ab19ff46c9a88fa1b70ccea893ab65041ccd93514041ec0a89730f19382adc5b5ec89445dc16d3a61e3d7055b8b4c382ada5b297352e1d311e9fe66c041ce193705b54015b01fb3ea2cc728c734aa292dfb0f51404e8a5a69d25a52d93513a236677d55187514047d25b82976e935c333a8c56c074d5b8b56afa83b1b82da6e83daf31a745ae0a5e3b2d1ead25754b5e825086cc70d2754ad7a0a141b513f67d25b5e638689daf64480369858cff6320ad27fd1a42327046d80b99b51a9a5a4ff635149701078e15b2dea4cea8a754ada98d980f31be6a5c3b5e63840b50531a751a4b7ecfa8b603f66d46749693ff0d93013711a6352d3aa531be69d46b5e8298c3daf652e61e4b7ecda8d51404e323], []]
  | 7 => [[0x18], [0x58ce7ece664a3a529a8eab40b8408cc539d2660a92858bc58e059c4e3a12b8c53a92a88066caa54018972395670a8d856d0aaf856b8aa7409dce24d51857b145b740a600568e2515978590459a0e93855e4ebc00704a8f8524559485a4c0748a8c85a500730a5e8e570e25556ccaa640a44094057aca808e91856dca770a56ceb24524156e4aa4809845674a7fce8d05a680980597c55a4eb80e23558e85aa408c058f456c8a7d8a5cce9bc5a0ca8f05a9c0a4007b0a5a0e98ce6d8a9345b08593059d855f8eb5c07e0aa3c06fca6a4a69cab6456bca774a1817b005bac08c4599858dc5abc0b6c0a94095c5b0c5b0457f4e7f0e7d0a92c57bca5f4e], [0xb85f55f1b2976eca5f73cc6f567941c19f011779ec03ea6c7ae0cfa3dea5f454c6ddfb68f3d45259f98c8deb4935ebee0a139b8cad738695ae74c3f6ddb45cf3d24adb797d73af754c75ed78c0fd92dd4fa9202cf514059ec07aa7cbeadd78d9f59f493f6de027473d207fbbbead73f705815e327ce7d28873b7a973cf703a79da958f3c28b1f574d5beb705b47e326d27d80ad573408df319155764b52edac685738f50ab731cbd5e2c86add36b4f5a65cc5f0d2c7cd5c183b505194fa4a5f3ee9129b59856f3ca7205d8c8ffb7183f75e6389abc70555da68907b25c356d5b1ffad25412fb6a7e3f7052ede415a6bb20b9f6b01989f212d3d63250aed1e853b7cd56ced4ab79e998f8fab45a7598e51e71938d6ec02f67b68b1e7b86673ead96fd50a183d47ab5ddb65fbaf1f2d776634eab526ad37b02a23efd98b9e8897cfc60e35b56d27ead4ab59ea26757ac69d76baa7e3e810e7e63d25aeca3215b3fc73f3259f574b20dfe2b68ff698d3aaeada1dcec098ebd81479f97dc19f2fb313e5f6be7d26853b8f542bb479feedfb3433ba6b4f5b823baeb1955d4ff243cd05184f98e30aed7929b6906617ae67d758c897baf52c79ee02ef3cbe7fdba89af5f4c382bc86173e544fdb72b83cf918143765f7ce7d451b1f568faeb25ac75e1a5cf9c4aad57999ed9ead0d7d95a36bb52eae7697d5aaee0891b63856ebc7ab1d78c15baee32c7ce8f8c8fad246f5a40907b4c368be8f569bab6577592dfbaeb195dda0439f5d810d5ba8e63cf47cc6de988d8fb82b1e797e1ab6ac297ce3d64eed0f2f9f8f54bb6e08b9b64c5e6bb5eb1e7a423d3ead285d6306be7d93014798caaeb652f96e9897cfd44cfaf3fc7ff2e61cfacb50dfe530adb7a608d7abe9f5d663896bdaf1b1fb223b9f4c214ede256fad20d7af92d9e9f70ccf5e6371b9c7a4c5d8c88dbb193533e638cab9ce1bf98d9c19f31a4fd55a237ad9128cba4a303f1e92776927cd79fe2cfaa60ff7751502be2558ebbf67d7599934b747b52bd5c1cfac28ad75a1dfb6ebe2d7cec074e7d0516cfa49636f605096d9a2436daf1e9f58c9beb494647e98719dc04e8e57055acef511bb6c03eaebf65de78f8a1bb0a2b7d63242adc6493dd7ed27eb64d447ea28c0fb72306e8c0fabaad8ebd5691cfac6c97db56c86eafda97ce926d17d1f2f9f92d2fb76c9773e366a67942307c, 0x92d989f705b55ea26997d80f14fa0a4b9f601c33dc656f9d44433b8ee1ab6ad8f3d6045479c6c50ddb5e2b3edbab79e9052ddd44cd2f56d3aed414773ed76bd7b8221ed98d42ea9791be5682bbb50f1d9f7ecdacf1b2b55d9a2376c34fdf3b25c6b6b191bd68f58dbc6ce35b8c893bab495dd6016033d31412f97c8dbad7ab59dd25a73c7a46dda892f7749214edd25a7abf67ff3a0a5f9f5138cee4b6a67d30f9afa41736ec02c5d6da98ebb8cb9f38cdb29f484647ec8946dd311e9f66090db47ab6de634bf9d34b4b798e39ad31c695d5b1a3b382ade7ac23eb76554abe907a97d80b1d7b5dfb6e570b9f17350bad25259f8c21ab72594375fb7ab3b82bee7b82876ed7ab79edaa1cfc6ead578c1f39ead8ddda9058dbdc3023792daf9f603473ea27a57d310d3ba0a63ceada5fce41236edb3439fb02873f192e75e5f42add0f31b7a62323e8786ff0ae123e38273eb5cd0ae6fdbe1ce9a7497cc68573b5e63af25bd53e4b67e7bf6cce76a579cf49b6cbea28c8fd04b9e7b5dea5f20ad776a27cd7dd5414f2845cf931c4f5d5b237ad2097bbab57d6f31c5b5eca5cf3a1c307a809d3cf6bc647e0271b9ab85bf556ce1eaaa24fd65f556bac697f3a6969eb47b68be1a56f9d80d4cf8f55aaf603693e3b573b5aeadb77eda0cf20ad3768f6bd7c6edb4f58cdaed4c120f68f235edaeb9b7b5e7e3f6bcbc7dea56f3ae69d7697d2fb731c29d625562bd2a303ea515b6f47c7a7dd3573ac64cc4f8d90ab72595575c12536d44b9b72dc5cf9412753e638a2bdb2f85b7ed42eb47ae6dd935cfac7cb45792d27bb6bd043e33286ec5d0d5b8f5fbaf181d96d692dfac60e0cfa41f35f51404bed798dbc60da4f809b8cd5133cbda65cf3ae6557566086d7713db9dfb6633db2dd4f8d848bd48504bec07eebd23199f8f4aabb58546bea2809bad27ff37eda9cf644c79e90569bd80654fb25d39ecc2c79ea27057d251e9f905d29f6018b3e63903ad3097bba8a3d3e7f929e5633ff9d31181f6d95acf082c7dad76d17c66ae57b25d19b153e73ee299abd80cf4fb5d586f705059d9856b3c6ccc4f56cffe6f52a99ea55e5bab64775b5dc15eb491dd6ca5227c60855b98e29aef9ab59e92235ed3446bda89995ecc2e79ee1b28fdaef9af64d5beb31c975dfb2f73d30b9b78ee24b657073f1fb42b9daf151f73037db20ad3d5fb2bbb504fde7, 0x52c8df3601f53e5f6a67ca0b5dda425f3f25b8d6e147efadc16d17a61ea5f2faf96ed7af8fdc31b1f809b8cefd9b5da638e6bdc0dd672a860f8c82c7da9056dbdb55f9fa895a6f47b82be906a57c04e8f5b00ffb764d443e3256abbf6f167b5ec89ead23fd95b203adc333b78c163aee9127b55a52f9c64d7cf6a45cdcccae79e323eaeb5eb9e764d63eaf10b9f2a2235ed1f1b1f7eccece5b8c1f24c412edaed4af5ccffe7183533c8d167e520fdb7b008dbb1b4356e946dd7cc6f2b7b01f39f6035f3e5f7eebd80add7b8280eae98c1f0ff203cc6e855bb2602af64b313dcc5a33c6cf54f7043cda3a8c1f28f92cfc70dbcfb5c8d7aad93dd55a183b581414fb2a51b6ad24fd5b456f3d24f52f7cd63cf47b30be678d6bac64775a8e3b9efdbe79ecaab57d25331fb8225af31a97ce145cfab82216d97d4bb7414593e986617ca31cdb7ede8eb31b539ec0a60fdc333976bc8ddab9a5fce913fddd1ef9afb02903f512c6ddea5573c7ae35b3fc75f3193d53e887a97ca07d5db5ec85f514be7e3d49eed1e97bb7edb4cf424776e362aaeafc73f398e5faf2fb693ed7569bd21259fa69696b4c4c6de303fedab650f5b01a09f182b55ec06ea7cc6d7e7b22519f31b839e255cebc04cce758d4be6ad143d6986bd7ac68ff6568aeed6025f6e828ba7bd4ad678f55baeda11bb6926a57d1f181fb25b89f56c08bed73fddc7ada4f8f4a1baad0cdda306627daf339f70439db48214ee366d27d94a5db97dea9f2faa95e302aaebe6b9e790569ab6bc02be3d3b6dc64a5dbb2951b6e911bb64b6d27c7af54f5ccaeed4c296eedaa0a7ca31ddb55942eab9a4fd579413ac96ad57b294a9ee92d395633ebabf67d67b5ec81f1c21d6ea26d17c7af9cfb5e632efd955d6c9a92795c1bfcb5e4b3f194356e3d6627ab497f38f5a99f6bd04be9298dbac650f5b2a02cf31b699e5f892ddc56c9fa6a413f52b52bd0e1cfcba41beda42303efdb8dccae10fe0e6307cb22539f25c093ed76617ca0c05b92dc19f705b4dda92376c6cd7cf6608ddb284093e9892cfc6cfdd75cca1eb1d0c17a2556ebd291c1f98df3cf31943d68fa097bf665677ec8deb513d4be3d852ebf66d66b5e829f282fb5cff24fccc71273a894b76fdba79dc6237cac6a17556caeed1eae75e4b5cebc6046ddb259e9f1b2a36edab227c7ce64f8c14bb6d49cfaead940fcc67ff3, 0x520e0afa3dfb6eb1931d6ad7057ab476735cd1fed602976e4c8127c4afdd77ece1cf25be73dfb4bf9daf641f94640b74cad0dd5b36bb5051b4f2b842f931c7b5dfb64fa9fe43798f52fb76baacdeca5e73d2131b7b6aa39f6cbd53d554bf9c96c9dd5ccdaecae143d6926617d92e8cf8c9c19f64ba3756349faca3205da890a77209ff6d7944399fe3cf990493bad92b99ec07067ab470f3b26029f31c47d6c071add22ae37948e7b752c987d0a237ccc717578f4ffb731c6d5dfb6eb3daeb1b78c173af4111bb5fb3eb2cbf00cf97dc6b74d1feed5b42b9d35209da408d7b6bd047dc12376c6497dbb5eca3f651cfacb4183e2b6a5f38ad4bb76014375fb6bf3d211b1fb0173af6bd807ea2a097d447fbbb5e5f3f7d544bd5b2abaac676f37488edaae1ffce872ed7c9646dda61636f644733e6364fa9fe307a7edc1cf64d44bea26a57c6cb1d798e2caf64b353ead601dad2577698e3baf52b30be636633d80855bb26a29ed4ae79dc10df6d81491f4388df3192b75cff237cc6cb9d77055beb713ccdd68287ad45022f97ca1bb12aad5d5b1cfabe6ade78f4fabb3195dda36236ed450127a095bcf1b2b75ec033a7be646ed8c9fbaf45504be923fddc98d4cfabce7771b96976d974e7ab48573ac168e6ad1ffcec03427ab455758688df348b64be25236eb68ad6764d5aeb649773ea26617c6cf9cfa8e5f9f56b30be3258ebab6a175a615a6f601b53ec02ee7c04dc76a49ed5f4147b3e026633c7b0d5ba8a636f25a8576928d8fb82b9e79fa5f3f49382be5f58ebd44adb7a41b45f183d53e363fedaf26d76b5e633f31c35cec98127d04b1e78f5af9e70891e6333fedc6450dd8c12fb74c352bec02aaed4b022fa49736f1824f755b25fabf650f598cfaeaad9f5d6c980b3c04dd675f50fed25ab75d73237ad04ad67b2aa25ead8c1da92569b9fe4779a4e373f259ff6d7352f9b82ade539c43f349090fa4b42ad9da46f9], [0x8f5c158e3bf66d1779ae2b6a632f4c2c65736b01c66ea5deb655443e4b5ccdaad6bd95520fb8ad9810bc60d4ab51ee2b6a672f1e9fe39d97edc66eb1d94dd2972e676013aad1eb821bcdb2aa452e5d44cc2e69eca8ed738f4c2d6af35a3e306a47c645706f72e0b6a7e2f4c47ae08f7056b58f2d20d78e6b64b811808f023007d65b6a8298e3d30b5ac6d63256cffa6e91fe1be9b26a26607d95259f535805ace1e3715af3397a623d5acedc16d5945ec9745989b31c770a55bdea28113d95299f536e2b225197715af3197ac2a28093ba6dd2b796ca5ccdacd513f65da78f5c15ae6d0531c4b1dfb6e993ca8716e2e787edc664f8d20ad9fecedab28fa9b1eb8283cdb8a0479db3f6e9b2795d362d5bcad7ab639e5a8a4b5ccbdaf33a966d692b88de970ccf1d97a61c10dd6d1f182b45e983fc737351408c0277056b57b2c7ac02d756007edd3cafdba683e5b8adab207b52ad14396c898e258f414c70a65809b86633382b195d9a928d8aa3b58404e8e5a8a4b6607d94e9ab796c9ac2a41ead9fe39f1819d356f2d95514963ed7b29ba1f31ca312d3b2aa28ec7c97022e71eda98e1aa6e0ac683e598e3b57ab594f9a972e906bcff574dbf6e9e56bcff2374db53f3743eda9f8bb1ee0ab61be58f5630dead051dc352eda98d8b2ee0ab639e58d9b42aa6d45011769e382dc5cb8ad95c39f458cae237a5b5424fc6e04600e1c7482b65bb5a0a6386b1dc5021b59ac07ecbb8ee9b9cade5b2a4b5ce3d0531c771e5041ce1b2fdba6b5e5b8a043eb2ba6d7ab79698705634f714ce9d56b6ab0a087c827f91b669856c736b31c770856a49b44295dc533c735ad798e252f482b639b5811d356f2d94e9a972e362dc37b8d795c1bec8f56341eabf6e9b8d8ecaa89734f65545298fbaae299cbbf6e31778d5b3fc8de3191fe5bd958cff1cf8a145b86fe2415a48dab47b52ad27a69d22356db5652e71e988f5073ae9b8c1be9b8a4b8123d61524049dd25a48dcb51497020fa61805adab16b99f596a241c737358404dc667ecfa2ef2ad27f91bc69798e3bad193821bcdb02a22ec7d30b186ed6daa0a1a97603f6e9c7749694432d21190e676a292d8b1f4d2d246b5beae2b68bb5e7f8e7a55b3fcb7e36d41efd97a89c66615c64ad8e756326bd5b8f4c2c683b5a40ff235cbf6e33318e638ee1aa71935e7fcbb01932ee6cc72044b55c158c37cb654a6b9c7b5e675acbdaf3389c5e908c9af1f4d1fe46b9b6a63842b5807d17736903fc73736bd94a59bb5e6383cbdc56d5043e988f5632f602e65dc7b26026623d80fdb215aca5ccfacb6d5053f0fb2a0452e5d93511763ec97199896e09fe39e9809d16632c64ad96f56e2a5e662f51404cc27661071cf4cceb5a755ac07199896fdb265de5b5e67600bba6dd0b9b1c12b837d925b16b9c7a8973369b520d7ab69ee2a5ded4f51316b9a73fcae0dfc408b99b59a045ccfacb4946c851bb01d30de6c7ab5ac7565f7a92f96e91fe46e9b6a63852ad1ead142d6c074dc69731c4b0a558c1a92866c7a5706f72415a510aafdb205de68f55b1ceadaf653e63ec07edba8f0138ccc6374d5b3ff8c97021f536982b83779182b450d5b6ab098cbd205706ef2908c9d33b31c350a71a48b70dde534b4a20d6e2b5ec81f64d61510f, 0x1512e67d3599df352e5d311e86e75af56cb7cb6bccef98fa41d356dac7ab195d5ad7b29423b4d482469d92d733eaac96fd9771e366d10a974946cda0fa8a4b3e8ed80e31772e3d5ad5eab715450227905d22366ac65706fd1c16016bcb36cc71dd67ed8b3eb2d45022e69ec9ac2028f64d60e8cdb6acaa887cc712c354d5b2dc5ce948464ad978c8ff236cc64e9ab7557d41ce1e3603f6c9d5b6a7e74c7ad2570e7d1c13fc37d2db96e2e6c74d900df6594a59772ee298e39ad6bd945d8f7edd30df2d1f1814276323fc73b3484645b9d8118036b35af653a63d5b2b837e96bd95020fb01fb71a9d3520a2075af56cffc7484647f9bbcad7b287d951d9f536942dc5c79483821bad], [0xb8adab2a040f7152f023749a428ed6b57aa5614dca72119b8a9799e3b2d58549023008e53909805ae8d9558549298b94e3b6015ea5654a7023010eb0a5d8057995614db00b5b1]]
  | 8 => [[0x196277db], [0x98ec3698975861d88cc528982d9834d818d8855812185a0e1d187ed0aed8660b1fd8021891d8429328d81558025832d82b582d18235872584798089805d87018a3c009d802d8660d34583f9860980e1892c71298a440911851985c184bd32e585cd062585e183fd454187e587ef26898221837986058305873d84e585f4e64d674d88c072618b840039848d86dca9e586c1871d866185c98875865188f857ccd2f184f582c581a98a8828dc523d80e9897c90e5828582a983658a3c10dd84558881876d86bcdad987c984418859807181f18279821181d98291858584a182c1864981e187a18091811588d886d588c315cce06d8941875182d589d5858ec39d85ad8755844d84598ac1827d87ed1741898e54a988c875cf2930586d85058b80e96d8a64019d87c580598a3c21ed85d587b98a680265859182b9859d8ad580c9811981bd8b5c32dd816989ed8b5c149d894d8495808180f18a5007818730a51d8b00790452e1827185d986d0a25d86158b4d88f46675810d81b5850981a58685882d86ed823561058a3c4901892c6ae585c58095813583d1857d88c055ccf56f25cec7ecf335811d84018569001d83dd8065878d8789852d84c984b982598249820185dd879185cd820982a9601183cd839581e9838d86f580a58a6003c1871934bd4660c40583e986a4a7dd8045807580a186a1818178c09589890d82a586118, 0x6f9835986b180d18568f58cf00981d588358a883674a44984ad8b49804d88f48998517d852d30d58429475d838989f5897f14f980a9839186c9841d88694a602a4818498a08d1a1871583f18069812d842182373a940a08c251556ce4fd836180b98add8079881d858d13e96099822585298629850963bd898cfa19869181b18a4848cb1285675986d1856e5a4c085d814988693801897c63ad800d82998b51817587ece58180858721814583258339870583758a881349864d87298301842587698ad18ac987e9832187a8b4b5818181f9823663b5829581c183d9858f260d85258785883989e98879813186a986c8a26d86bca70984c58731897181dd84698a40072d898f20cd8a1184d5884581c982c98a401545856d085167ccc6bd8745841583b9847d84dd85b985a18a3c33fd36a588298965831986bccb0098c08005820d85e582bd88c85af5852d47eec241565d8b64539d297c756ec821898d104182f986e9858ce15983fd831587618139848588658bf5870d81ad858d05ed88d892e9826987a8d24d55f181718239547187198451897c56198a6049558b5c256a5bfd8719484d83f58704c0bd833d892c954988e0503180518b0312298ae985bd87358571889183b1888d8569146d816d8894658d819986a4b511819186ad85b1842d8a8804898239887d850d86f184f180d980c58599821982ad8b5c07658b5c4, 0x73985a58660a779810986d0b29d864580ad85958a403235550188d8653985e4e6e188318399858e503d86d0d2518568e4cd813d85318329824183c58b0063ed831d843d8961856d10b180fd88db1704b275898ce5f5874981018035892f1b0088618311821d856acae188c8935d86d8a85182058a4805358355898d04d18a88465981cd8ac5834186a4d8f491c581b980b58acd8521807d89518af18a4044398a4834758b558570e235e1798165856cf869896988f47a08b1418959836d86218499890981e580f989405411856b28d8544581f58029835180f5837d88c064bd82ed830988258945816185cd12a183c984e18b245808e3e184658c01868d806189f184ed8b005215822d814d8151823188f454318111867d81958704a664a481887183718695849182f588f7177d812588c866dd85b587c187ccb6c582b18236d49d630d82cd84c186558579841987ee545d85158281815d8921840984b1860187a8ca6038d876bcb0c18a402435892c58c885a4e42984a5866586a4c6d9892c8a4822fd83e589258ab40a6016d0c0ed83d5871184e988858748a91585d1853d86b583858381824d8a15840d8704d5ce50198331897c8], [0x97c4ebeaf2b5dd730dfbab67ff774c37fb29b83bdfb64fb96e2e7c74dc1def9833bd07237eae60477b2ac0bebdae7dea22ddfdaf653fa688d7b58524fe6394fbbf65df762460fc838f3f5ce68f7c085def6a4bbdeb196fdeca6bf7bb2d4efa0a3b9f5211bf6362aaed2001bfa3cb77f21383be63896bc84d4efae2977f31ba7dec0ac2fd94656f49c02fb4104dbe981cdfb3a83ef74d7def190077d7058fbd80275f8c819bf1c0b97eda5cfbd2005bf52c26f627091fa5f022fb20017eb293abf52520feca6eb7d6b513fb8a30bf603177eca8baf92c39fd9095bee7f91be5632bbbb00aaf7a923dbf57383bdf350b7b6eb5ef71998de93817f66797efd04c06fb26b0bf33ab5ddc10237df331f72a837fa8506fed5b443bc7a39df8c910bf021c3be9b56fbad6aa77a6163ef584617d2f09bdad6adf7a0a63eee9873f6361cefc1efdf76a403dee086fb5a956b3d21193f85019fada221be982b9fa4e0cfd92dbabee991bf6a2009f95439fda40bb7f34c617e1000ff56145bf96a3bbead20fdd5b56fbb5205efb895aef2fa5f7e631cfbdf5717792c37bf35c657e538cafd6146bfb5ea47f1b0177d5a443bc7a1bdf2a826fb259777d5b09bbb8c017bac2a47f0d16fee3009afc8246fd90a30bf49154fdaf05f7a2049fd97c19bf31a0fdebb243edc56bbf8f63bbf47c607d981cf7a1439fb6bd6bdf4bc6d7e5f7aafb5e00ef98c4eef25c777eca52efca715df8ec93fb4bc617e32602fdc531f7a6dafdf259b57db40077ac601f76bc19df23c6d7ee6a3dfab439f74e837fce7129f6ca36b7ccf1ddf6e9a9dec7977be3600afd20d7bf7a8bbdf47ab5dcff00fda145bfbb8ac0beaf2b1dc6609bf300af778c9babecc017bec00defc98685fbd6a27f0218bbcda00bf36483efa623b7e7f833edaf00b7ad6ab77704e1df602217e63813bd80045f6d04edf49176fd3a00bf476fdf7b6a829f41221bd07387dd31023f8ee1ab6e0901be928d8fbe65bef6216bef600077d5b02fbcbf215fb863b7f6bd36fee2b69f95c05fe6c848df29ac7de1402fedb5443f8d9d3bf6f520fe63067ba3e01fea415b7f7bd44feb07efbc6cda4f6e95aeeb189ddc73173ed945fef8c0a1bb51536fe3b8bafae601778d826bf47832fd69237bd61473fb5d427f08033faa25cfbc341bfb99d53ef5233fbd2700fed24c03f74dafded484dbeda8c2fbe6136f, 0x41c7ffb25ba77ee2a39fb520cefa3d6b7f6ba96fde3237edb446fd2a85cfb5251efebba6dfa740cfe8c15ebf4bd1afea6a3dfa96017b92c02bf51484fdde6d37c601bdf70426dedd331bd986637dccad7758d5eef6052f7e428eef954017d70417df7d375beda97efcc65bf75cc4eeefdba79dfb05fbab40bf76e99fdf4a0b8fcff1cfcab601772b88dfab58fff5d356fb96e1e7dbeed77f6517bbd5c123bc1eb1f7a6d9ddee9ab7d690065fcce46fdb6a32be46807f4bb21bdb00abf73fc26f73d4c7dea2369fc9725df74db4de7f977eeb06d37b185defa61d37f6e4617de273b7ab60bf7b0193bead0b3dd1f067f316b1f76d017df73ab7de921cdfa8439fd2a80bfa50805f5fb2dfbd44133fac29b7ec3ab7ddd35cfbc9600df38426f6e911bbe323fefab450f7a49ce7f584c7dcb70dfedc5513fb8a927f6d4cf7e1a09bdbf61bf7a5e4bbf31c1fddd339fdc7ae0efa3c037f6bbe6be3256fba0e39fdbfa04ef7152efeda8aef95c137e4280bf7605377c680dff35e1cefa6e8a7ec011df68f005fc640bdf3e837faf11cfec970dfed21191f50803fb58383bd9813b7c1eadf797d07bf4dd10fcfa1cfed614c3f8f507bf5bd20fd7156bbdb54c3fb6604beb58c1fa630dfbc64b5df8ca04bf5847b7e5f57afc7ac5dfb89fbeead2b5dd5b13bbb5ed7efbd64bbf190857d984437bd41befb8a67ef51496fe4258fba965dfbac086f7514977d69237aa3e1bfe8f419bead96fd569443b91a0bfd60172ef6cbcb7e9a441fd2401bfb5c0b7ee9b8dbe3213afa84137da4c597ee0a21be5f97efb9cb9f78c1a99f1f10d7e9b98fbcbf025f97cbbbf7a4bf7dce56fbd4cd4ef2a803fb4c39cfec041efcc70a7574c3afada0a1beda8aafb8205ef8c95bbead04ddd9800b7c96045fa925fbedd343bec06ea7dd5713f6bd5bcf605817d6b56bb96e2e7dab5d37f49002fc730f3ebe69d6f3e80bfb77d2efeca6a77d494c3fa3e537f021f5beca8aafd952e5f74dbadf128337e322defc85155f7488dfb0a0e7f5d3173ed2e487da48267f4bae7de63853bd45513f2a819fae304dee366eafc08aaf7b288dfa9386ff6a205dfca725dfadab07e3706ff9a92df7d49493fa600b7f6bb74feaea61fc60275fa88737f4784cfc800dfec7a135fb5ecabee0b83bdaf57b7db5415f97dea9ed7817be535cfbdc8fdf77055edf31a21de36602fc7ab1d7, 0xa4a36bf673a7be92021fcc70d738f4aebeb9817deca7efbd451dbf58c75eef524fbe9b8c2fca71b5f2348dfb47b9cfdfb41fbc96b5df931babf1bb017d9000ff4771b5fa48027f1dc297ee2a29fc60c5df5ac75fac011bf58b56fbd2f47bf5cd10eee0977bdb40df7d25213f70419df384bf7e3d706fca0e9df34073f7022adde9b97efc6c885f41c86fb6bdaefe0858fbbe601ef7044edf602d77dba56fbd441bbf49c26fac411bf58056fbcbec05fbfa977f51374feca3eb7c4a135f4385cf74bccd7d982df7df51ddfac236bf02375be903fdfd305dbf8e16bbf602bd7d7336bb5ae013f47c0bfd48408fe9a235fb00a9f78d801bf5117efebb66379b4137ea423b7eb195ddacaa3dfd30013f8ed5aeecc06fbecf8f6fac61377a9263eeb9803deb05cfb9c21bfd44090fae0807be9b8f6fae65df756837ef7111bf64b5cebccf31f7b6a3dbeb1803de3b5cfbc66245f4bcbbf7654777ec02eefd44cc2fb5d6b7f5120efe6758fbbc6e9ef7a826df6bd60fe4b3eaeac65df790a2cbe50807f69ba5dfb9cdd6f7ed90ef0d007ee1002ff4c71dd73fc8df747ba6fe3b8aefc08adf75a0b7ef73d20fdc141f7c64e9dfa490a7f65177bca102fec64c5df6e198df2f8077d9002ff5b5605fa41af5f47b00fd8b237ed2529bf58d07ef04bf7de320defd2405bf58c0beee0805bd5a13bbd81215f70563cedd11bf690021f9fe39fb28437fb64b317c8d023edb53f5fa49ba7ecc2d7be8298f3d36d4efa3c177f58520fe3b237ece4b1f7a623dbf1dc557d4b02fdb00ac77ac15bef33c617e41442fccf16df2dc48fab18e7de8f0ddfad6af77704b7dee9879f6a2441fad6abf76d019df7d3a7bea45cfb91a1bfd7edc6e748484fdc12bb7d99195f7ecbbcf52353bdf3603798a46fd92e42be5b8b9f9c10077c4a06df66910df0d177ee3e2defab639f742803f71b2d77d865cfbdaf29bf5680bef1e8057dd3123ecc6017745c8dfb58353bd2f00bddc51b5f23473fb6b806fe2500afd2f31f78c802bedd129f64b30afcd2ad77b5e3b7f7647b7cda0dff4a6cc6fb3a53bead807dd73067bd30b1bfbcad77f190e77e3d022fd94686f8c107bee0ad7be678cafd68cc6f66026df3dc777ed7909fc6683dfb00bb9f032b7dcff02fdd30e0ef5ad53ef1805b7e6309bbdb51b5f97c73bf48002fdfb71bb95c1bfcb2a927e7604deddb6eb7da51ddf, 0x92d8bbe57007f96b1e7eba6217d2dc8dfb58121f6cc6bf7d9ee0ef5ccbceef520fbe30066fdc4ac7757107eeaf2b7de04237e95c1bfdb2a987ed789dbeb0a81f8ea1bfdb01babe2e04df9ba58fbd1e39bf52c37f6e9b31bee2567b95c0cfeac1afdf192b75e8f2edfbf6c07744094fb524977daf3ff7c7b025f36819fd410e7be981e5fdae1bbf83d73ef4b891fa536a77a4e39fd5ccfaef654977d7309bbad6407db25989edd2e7de3074efd2f453f66079df2147b7e982ddfae60bf77180bf74820efefcb2afc7ab5dfb5d077f603a77d1f00bf368856f4bc37f722c617d7357bbd1f023fb01d39f1b02f7e323fed942437d98e25ef48074fee2a31fc600bdf909b4dec9807f63d05efcfc5def98e10ef6ba20fd4b00fdce731f792c26bead177dd0a067ddd533df56802ef2599d7e5f94efc7a01dfac232bea1017f6300c2fc14dd6f8c1cebf2f84d7db41cf7daf023f1ac26fd7151efe0458fbd040cefb0017bf492bcfeb06677ca649fd8c073bec48ebf61400bed94e0ef56c01ef4c96efe828eef94239fd60173ef4d11bf5ea00f7d04b5efa6e987f6d520fdfb74fbbc421fd568a1eae7353bead385fda1605fb5dce7ee7369bd5b0e7bd3646fd5ac86fb2e4857e97a25fb82c06f9624bbeb1ac7dd2f00fdd48adf773963ef2f86f7d982ef7c7a275fa5c8dfb4bbf7deb0a3dfab45bf73fcb7f76b96efd1023bec6000df90998df29c7b7e326bef9ce5bfb66008df52383be906e9fb74d1ef82dbaded482fbcfa00bed97185f99d73ef33c6d7e922ddfd26c03f6bc03df51300fed77cdfc7a05df9095aef021a1bee28cafd2f1edf98c01eeed35fbe536bf7d94a5dbb0019beb997bddfb023bd49513fa60177ef2977bced1cfd9fe39fdb6963ee39885f5ce7077daf33dfa60017ef9a21be97a41fb52b5ef5ac7bfb3182fdcb710fed1e043fa0907df712b7ddb66037b5239ef9e173ee85005ee320fefd95483f7edbacf212e7de04553bda31ddfa89737efd805de7e8eefd45023f56803eee9887f68f009fca724df2340bfaa1005f6632efbd36b1f7730b7df2fba77ec009afddb6bbf52cb7f736cc7ddaf10b7c60ad57ba6d77eb9807de0a74f7b3083ef92cc5bf47b52feb0a25fbc64a7d6d180df49408fdea2df7ab4047770473df4c010fdaf09b7af2687741c80fa838c1fa3000afca070df638bbdf0d033eeb056bb9b405fe, 0x97d2fb6d78e7bec0602fce51edfa4a927efdb19de905adfc0aad77a516b7f31c35de6373bbd61563f28426fb2dc6d7e67553bd1e153fa6e36bf35ab7ded7005fd2eb1f756cb7ee4689ff63d58fbd61463f92d73bf4920efdfb00fbc6c5bdfa61807ed486fbdaf41f7d36fdf7a9163eeccb01be4b602fcbf1ddf3fc48f731c45de4b13afd2eadf7a40177ee9b53be8f6a57c77185f6a401df1b0117e02663bdae9d3fa45077f1ead776ca5cf7ab67ff38ed63eed4a21bed7065fd20133fac24bbf5109cfdba5e7bda2dd6f8da36bec984df6c094efb2639fdb8a907f1b1557e3000efc7a3fdfb6a927f25abd7dcc21b7ca71ddfb2a2cbf51002fe087077d60cc6f90a32bef0b83bd731cfbd30133f5f4e1ef1b2157e045cfbc60b5df89403bf6039d7e8f6e9fd70ceef62d5aef1920f7ea46bf7b742e7e66001dedd327be9074dfd7646fdb6a8f7f47abcfe42237ed440cbf74598dead811ddc16eb7d2f2fdf92e049f258e77e674eafcc6dd77a915aef1eabd7c590dff544043f5cd07ef6d4fc7d8058fbdfcccefa62977edb0b3be428dafabcaaf76d1b4de9d04df980387d9f401fd8c110be97833ee3b8b6fdb525df5cd6bef600037e5f49ef91a017d7a910df013319ec4b02fc605bdfa496b7ef9a97be32022fd94b9e792dcebf31811de92441fb300bef1cc37fb1e8037e6792efb68b5ef6d0aadf4c374fe9b56bbc645ddfa62427f712addcb710bed50d7ef440d0f6e0ac7dd0a167db8cdd6fb695aef6bba6fe9b8cafb68af6fbb2987f4809cfecaa89fd8133df8c008bec6977be8f569bb5ec06f97d6bbf6d512fe8200b7b260cfd6d0bbdf29c617eca5cfbb821befb8a04eefdbcbdee25cfbc6c1bdf8c9af9f6bb00fe3d1eefd9516dfb6a63bef5005be9ba2dfb261bfd7a980ded4805bd420dfeb5e1befa08bbdf484657eeab2afd49185f8d819bf7bae7de901cdfb52af6fb6aa27f651c3be988f5fd55493f90a2dbeff3f7de042f77c96b9f77ed93ea85155eec0a92fc60d4df8115aef2f8177cb70e7ebf639f7b0002bf4902efe8f8c2fc1ead7797093faad04fde8f02dfd30b5bfac2977f023f7dea22edfd2129bf7edfbeecf977be7997efc7a885f7047fdee9b9dbdce6bf7d80fddfb295aef1b2156e99219fccf165fa89987f523f7dee0b2bbbe683efa61c17f194657e7892efdae5dbfb018dbf6d5957ddf6d37d0405ef, 0xa6dc1df5d524fd5b0dfbc4a39dfa8a537f65347be8fa3dfc60c05f6d00bded796fbdb400f7a1427fbb4a53bf6d4c75dfb73bbc770d5fa62537f31b17ddd22376cb846fd99dfbef582c7de3d58efd9531f7811afdf712afde362eefdc52fdf5788efae7331bda62ef7daeaf3fb2da9df512e6dec07efbbc41bfda5d5aeef525fbed174f7d20af3fbba987f481feee1409bed44e9bf74d9fdf08005fa5f47ef9fe46fd1fc37fb1b2bd7e4f92efd44b5bf6255eef0d0e7eec09fafca646fd6d107df4816efc981cfed9529df3fc02f731817ddfb443bc281bfdb0204bf181777eee58fbad63bfd8d9cebf66c6d7e5390afdcb493f6016bef511f4fd732dfb8e621fd8ec48fca5833ee987057dc545bf84026fd2f96f7dc60dfd9f40cfd5ccfaeb2cc657e3600efdc51edf56d07ef49476fd9800f7c60dd5f94e2cbf4dae7dec6b02f9682cfdbe8bbdeb1833dea8a41fbf65def4e803fd48520fe6e97efd94adf750819faf9ad7be9056db97646fd6dc5cdefdad7de63603bc7a5bdf5788dfb2fa217ea28117dae133f815a9deb5ac7dea5341fad246fd62cbbde46833f63202efca6ad7766029ded7a21be91121fc0ec077b9636bf31ad7de4b442fb2605fd28448fb31c777ea4a21fca6da6f81dd3df4906efdf302f7bf600f799e2ebf65179bd3a02ff4bee75f6615edf4c20efe3d74ef95c017ea6e8f7f2447b7e6390bbba4886fb5c177f653a7bdea02f7b52046fa615e7ead003de92429ddaf4bbf7cc02df2fb177e0433b7c7ac05f7395aef71530fea48dafcceaaf76bc3fdf25a0f7e1400feb5e046fa9232bf1b3177d5b173bd94cfefa41107f6b89cfdf32ef7db56bbf98d5eeeb186fdeb86637b685bef97c01bf58405de30812fc64e75fb5eca3ee9ab5de4b812fbd40cef6a44ede9796fed631d3bcc731f770437faf986fbe2502efa202cfe27837fb1904d7ec08eefd1f213fb2a36bef523fbdc62dfdc60ad7771803f70335fbe98a61fd8039df810dadf213f7dea200dfb20137e6a430def98e7beda98fbd041bef8ee32bec806ff91f09bf2d0437756c19eed7887be41236ed20c03f1cc48fb51016fe042ff7dc9605f86802f6b182fde978cafc8246df7a873dec5ae7dc8d09bedae39bfa3e3b7f29bf7de9fa61fc9605dfb01fbaf128137d80567bb68136fa6e907f184617dc62efda0e3afda8a977f58544fe90739fdb947bf, 0x23d8f6fd80e35b6a507df33ab7deca33b7d951edf8c95ebf33c7b7e9ea49fac68877a728f7f1e9777dfb067bd300cbf811a3df4bd24fe30286fc6d025f58c02ee4689df6748eefc6cda5fa60377e5706ff9ce237eae66d77a61107f2f8057c9b1cfe9f4137d428bbf6d4b01bea2579fdae043f5ac73fb258077e37166fd805def7ec4eef52b74fec0642fc7add5fa09badf2fb757d891cfeab639f58f5cebf182b57e822df79420cfda48197f31c77defab6afb8c0cfb6015aeefdabddeca8cafd805bdf3fc37f76bcce7e8f8c1fac6047792cb7bf652c7dee09fbbca7175fa3c4e7ef52d7be4b066fc960bdf84037fd02195bed26eb7db4adf7a484e7eaf2adde8f285fc76adf7a5e887eda005be250defd1e883f56cbbef4c006fd98603790c1bfd56819ef4dd24fe8f41dfcc601f76a55aeec00c1fab06777ba6b1f7a3d5a7f003f7de9056fbd24da3fb018fbf6f4657dfb02fbdb4fdf71cc39fb5139cfee292efc6c275f909afdf55d44fe3d7067d2f463f810c2de46803f5a96a77b10477db2a30be3c86ff5c158f7b68046f8c00bbecc033bdba6d37d9462ef52c73f74dc977e90009fd30273f81153eed7ab7de32006fc08d4ef8680bf6c9805f65356fb9b401fe5cd73eedd1cfecaa143ed201bbf82d80ef493a6fe5f05efd49453f56c73fad49a1be981ddfbf6dd7774da1df654bf7dc61cfdd24da2f64019fcfdb17de4b3eafb74d7efa0803df47852feb0237ea5e05fbb01c6bf65544bd6b237ec6c83df7ec26eee08ebbe988f4fa2046fda403c7e8504dee04603bd45259f4bc73f6d7977bec002efd612fdfa61636ed4943bee258fbabcaa77], [0xb8ada99dbd80e9b173cae1cc37f8ad8e61bf5a61c11cd7d1f1804c7ecaac253b764d60cc4f7edd362f3d20d786ebdaf3fc37d7513305daf8f5631cebb82b18e79e321cc37bb654a6c05b94e046039c765b86ff25390980b758300af73a6d6b57bad60c02d7ce9858c736ec02d65bf55ad631cfaba6c586fb5af56c37cf484641b9fb8a67896b96e2706ff28298e0fcf31c7707d7a616b1cded951db753ee2b2a04cf193a61bdd92cfa2eeec64ad86f5e0460110e68397639f98c15a09abc7ab58e7751041c73f27f96e1bf9b29d30df6ad6af16fd6e2a5e676f31c2907f5a6910235ed9558548beb0a5d80768816e1bfcac2976617c08dd3019e428ed6bba8820e46f95ccfa2efad207f86eeee2b6a673f1b214275bb2a536ea7b00b5a21cee2811d3cf4bad6af76749102376d80dd3173dc11cc37db1eb8239cfb2a4b2ee7d95023019ee298e25aec02d63af5909805afaab67f86fcecaa88bb5e7f91a1bf9b6aca9f8fba6dd087b6638960faed796e1bed7edc662f9d44b9976de326bc379f47942133d74dce0df6dc512c095eca8ecbb9f31c3507f392e042ee7dc5021779e536016be74946c271fa490a139dd60838e7e6988f4733f6d595524fac29b94ddd36c02d7d6e2a9204cf49368272fb8a04795bac6570e7daa2810bb5ee9ab61bf57056b1cf6d95524a73e4b5ccbbaed4942136d7ed9362fadc56d5947e322dc37bb1b368274fb8a046eb3d45259767e536015ee7654a6674f5a510237ad614db30be3b5ad5eed65476e9cf62d732ef3db5654093e04600bdcead14213758f5071ceed95524773ee2b6a672ee9b00b5f574daf0df6d2ec02bdd98057910e758404cc67a6e5390aec7a3986f76538ed80b6e9ad6af759096b57bad6102301ceca94dd39f4c20e39bd8c0a109aead65b8b9f16b57873eab1a0e39f558c730dfad20e986ef5fb6e98bcf6d5945dcf811802ef3d80fdb175eb094e3bb758548e73b7ed8b2ef3d94b99779ea481180cf654a65dcf811d36033d6152300ee306a4269f58548cc2fa898b2ed7c647f86f6d73368bbecd78e61bed6a55a09b3dc533c775eca8ee049f25b165dcfb6aca74e7d9529c093ee2b6a67aec02d639f5705071cf6a207f91be6539096bbae99fe1bf93fc730dfcb008811be6ca81110df715b50237a3d5a099bb00880b3ea901cc377b4816e1bbdac2a26617d20ad86ede8f6a4265f4c0e61bbd8d8aa13aedb531c1f5ee2a5e046f6038cc5db56cb70dfadb5653753ec062cbb9f023a61bedac29b739dc828811b75d36e837db022e65de7a5cb70dfe56152408beb0a6d8077584a7215b], []]
  | 9 => [[0x2062775c8b66e9d6b9196a1ddfaafc28], [0x441f02d8685862db1cd809d8aed845d894d83b580e9825984e984418811900ae00b4099b441b3cd8661813d8a5d902f40398a40074d92ddf07d80fd809a70f1868d84298811b0ddb739800d8909b6d0a67d849d802e33b18067441db41d8ac196d182f180a985cd8660aa3c02df481d8b89f066e442794db2f5860195ad920183dd85cce1398341805db0ddf8c8544192edf73991ad810d856ce06675798009f021f0e582a986e9fa6df47d874dfb69b601874d88ed997c5909f02180258099802ee739fb2991d1806581cd91e58285852d809996a4a00a71658b0052ed93d18a6d902d92b9809a3909900580358a9198edf065f8518021b9ed814181bd8261825d82edb2ddb00dba91f00a33ad802e713996ea790a71a18a6db09b40918a88094dfad1858ce009818d86e980df4199830986258704a03d86e9b8d852fd80659b29fa5df90982ed81dd8235862d974e700ee568e3858a5db02dbb89b86988edba91b83d905e702271cf499d907980dd81d582ee782d809ae78d83c18b69936985799ac2796987898621800f498ce739b92c51cdf6e9999db066327986bd8b69f6bca76d800e3601b5ae74bd82de75ad805dfb29b74db1b98a6007ecead9857a7009b94e7121870580a586a5819183298971821980de7099f0de3ac1858d8b8998f4533981ed8579f1ceeae18059805d91cdb1fd800d90219109864d826d85098, 0x5adf41df9258601f2dd9065b0c180dd9a48002df73a71ce73e9813a7139b579b6027011841e73158139f8298b4980099b5c0ac1f41d95c982dd88c0500df0b5805d83fd894d97198811f0dee17182355ac1b2ef45adb00e7], [0xa4037016b021806401603705d86e803616b1398625076292138099c1962e2810e6015e60b70918a900361100658810bc62ca099874c1962745ad8b68b7610732984408d56b094d894c196236138562c0262ca1cd8b29d361d32ed8ad2b062678ec55c96b6242579894cce615e41d88ac19618b0998b891062420dd883c3761ba2dd85780362421ed8789d3615806580641762b02dd8810bb295e099890a3b15ba2ed808c0b62bbac184400862e299ce00c0262ce6e981cc0b61631cce05c0361d30dd52dc4e61070998ac2a401d302d890907615e09d8b296b629b00982dc8660f305d857873622b00d8b2a3b147300d894e42623d1cd808c0360b7039841c7356b04418ac03762da079874d0761805ad8a3c260037099899cb7603700588f47316ca74cab690761360998a5c0262d173986e85062a42dd82dcb7604e13988ecbb62b02ed873837616b02d88ec02618b02d8b28bb61802dd84410762b002d883c2661ba06585781762532ed878dba620a6018440bb620406588111062531cd88ec7361070dd8a5c3c629b0e986215e60b700d86e84e6180578e74ce1613602d81380160260218b28c2625341d874d806037009874c3761d30098810736118099819808615e0598ac026629b0dd894c0862a40dd89ed8062670098ac107610700986001760120098b687361d3099873907615a098e94c7f62ca7398a6e9702ca2eca7381760fa2ed8ac1982ada2ed86e83762d2909841c0b61ba60183fc37618b2ed841c04607305d81380860f406584d81961a909984400b62a22ec0a4037611000988118061806018739ce61d31cd86003760aa1398b298060bb00582ecbb61072ed8a6d6b623b1098578bb62b0a6c08c02662b0ac180540261631cd82ec7362b074d8a901f61d32dd8788b761d37398a5d0762b000d873826628f0998b465361805ace7391061d30fd86d04e29802ed81382661071398789ba61072dd8a9026600b02186e87362970658b8826606802d874c17601500d8a6c2660bb2dd874d1060b70dd860059604e0658ac19861800098a6c0b62a444186e96b62ca6e8a8100b61db41d896907604e009828426540800d8b887362e2a5c018c02625c94d890873616b1cd54d80262040dd82ec02607300587047362a46e98ac242618000d8, 0x5ccbb611741d882d6b618b00d805c0b629b2dd8b681960731cd81cc4e60b702d8ab1ba61ba6e9883c03629700d82dc19604e00d8924b7600b00d800802629b1cd82dc176189601862180627b94d8b680362040098ac18062a42fd82ec0b629b065805c086110315873880615a0998ac00262da02d85783962970dd85ad10615e0658b881961360dd881dba611009988116b61102dd862c19619f00985acbb61895ad876dce62ca02d860073629b00d845d10600500986a426298b1cd89098062538ec59080360030058b880d62421398441106180441894dd362530098ac04e62a441d890802623b5ad84408d61a302d899c2662ca6e98a9073629b2ed8ac01762ca00d899c37618006584404f60bb05d881026615b0dd80200262972dd856c37390a13986d04e616b2dd80dc37611005d86211060a1099862cbb282602d8b880362a473987384e62320dd80640b616b00d8b8802625a9098a607362b06e98738bb62320dc541c0860bb0dd894dce622e02d8a2403604e02d8ae1076297099806402622a00983b40b624202188ec2661ba44187395e623b06582dc26629702d826008623b41d844003620f1cd85780b602605d81cc3762671cd8a6dd3625390856e843616b1cd8909ba624990985ad5e39722dd806403610712180080162975ad874dba616b41d81cc0860080218a900261ba0998b88b761af0dcab6aca16b0a5c00dc1961d313981cc19601202d8a5c2a615502d881d5e600b00980480361180658811ba62ca41d809819616b0dd874dd3600b005841c0f606e05d894d6b6096009808c02610700d82ec4e618002188ec0b61172dd86bc3761732ece5ad6b60b71418739ba295e021890817615e57989711062d274d8a5d8061ba009894d5e60170058a5cbb6288009809803629b73988ecb7615e44184d803625302d8ad9d3618002d841d076242909841c7361d35ad890819615e2dd8ac008616b57985ac5c626702d8ac01960ae1cd83fc374a4274d8704732a8d06585c95e60bb02186840862420fd88ec0361d36e8a0641961e344184403760730dd57380b615e00982dc0861ce00987ed8b398b0dd8aed10620441d8811ba2a4b2ec57398061ba02d81383760bb0998a6c776253601809802611800d86e95e62531398bf980625394d8, 0x25a94d8a900b62530c18b8ada02e202d8ac073620f06586e907620f02d8810b760b70dd578dce6242441894d1060b71cd81381762a02dd86002662da099883c0260370218738b761ce065857837601705d8bbd6b62974418810bb600300d85ac2662fc94d86e808600800585ac74625305d89082461d3738ab281961ce00d85ac02623b0b58738736110139873808606f0658ac1ce626700d876dd362da99c59080b629b601874c03623b0dd80dc0360260998a6d1062b00a5882dd3606400d86007562b01e586e817620a7398ac15e6242099894cb7618b2dd8600bd62427398a6d0760da2ed808c1962422dd8b2837623b441892cbb61ce5ad84600b61801398a607302ca44184407362971cd8ac16b61d302184600262a42ed841c19629b94d8b680262c062c52ec0361ce0c1805c02601902181cc2662e20dd841c1762b8ac1894c37600b02d8811803aca009894dba603702d8b6837615e1398b8809602600585ac1762425ad83ac0361d357988c026156b06586e8d062a460188100362a45ad873804626383ceb2a53165309986010762422ed8ad1ce629b6e982ec1961ce6e982dc0260730098a9019625300d8b890762e22ed8b28b762a22ed8], [], []]
  | 10 => [[0x196277db], [0x1398601890985ad894d8099874d8065805d8441800d8009802d81cd86e9802180dd8ac182dd85798739841d82ed8], [], [], []]
  | 11 => [[0x18], [], [], [], []]
  | _ => []

def C30_S (s j : Nat) : List Nat :=
  qGroupedState C30_initial 5 17 10 C30_patterns C30_values (C30_counts s) (C30_specs s) (C30_records s) j

def C30_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C30_initial (C30_counts s) (C30_specs s) (C30_seeds s) ws

def C30_literalRoutes : List (List (Nat × Nat)) := [[(0x10040,1),(0x21020,2),(0x80000,8),(0x800,16),(0x80000,8),(0x302,4),(0x22021,2),(0x15150,1)]]

def C30_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def C30_rankPool : List Nat := [239122864, 201370952, 204553484, 241347849, 202619178, 167887278, 238235947, 68338063, 202386697, 134292747, 135511501, 67220746, 204614952, 202457422, 235028910, 135478605, 238207375, 171981232, 201567528, 235027820, 101725583, 201505034, 170110248, 67289549, 100843981, 68302122, 204517704]

def C30_patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16] => (sum6 r16 r13 r14 r1 r4 r7 < 3) || ((sum6 r8 r10 r11 r1 r0 r6 < 3) || ((sum6 r12 r8 r15 r2 r3 r6 < 3) || ((sum6 r9 r8 r11 r5 r6 r7 < 3) || ((sum6 r10 r9 r14 r7 r1 r6 < 3) || ((sum6 r14 r13 r16 r3 r0 r5 < 3) || ((sum6 r11 r9 r12 r6 r3 r7 < 3) || ((sum6 r15 r12 r16 r5 r1 r2 < 3) || ((sum6 r9 r8 r11 r0 r1 r6 < 3) || ((sum6 r11 r8 r9 r2 r0 r4 < 3) || ((sum6 r13 r14 r15 r7 r1 r4 < 3) || ((sum6 r10 r8 r13 r3 r0 r2 < 3) || ((sum6 r8 r9 r11 r4 r3 r6 < 3) || ((sum6 r14 r10 r16 r2 r1 r6 < 3) || ((sum6 r14 r13 r16 r4 r0 r7 < 3) || ((sum6 r13 r10 r15 r6 r1 r4 < 3) || ((sum6 r15 r12 r16 r5 r3 r7 < 3) || ((sum6 r16 r13 r14 r0 r4 r5 < 3) || ((sum6 r8 r9 r11 r7 r0 r6 < 3) || ((sum6 r12 r11 r15 r4 r0 r7 < 3) || ((sum6 r15 r12 r13 r0 r1 r3 < 3) || ((sum6 r10 r8 r14 r5 r0 r6 < 3) || ((sum6 r8 r9 r11 r7 r2 r5 < 3) || ((sum6 r13 r14 r16 r5 r0 r2 < 3) || ((sum6 r13 r14 r16 r5 r0 r3 < 3) || ((sum6 r10 r9 r13 r4 r1 r2 < 3) || ((sum6 r8 r10 r12 r1 r3 r6 < 3) || (false)))))))))))))))))))))))))))
  | masks => C30_rankPool.any (fastEntry (compactGoal 8 9) 5 C30_coords masks)
def C30_patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    C30_patternScore (C30_coords.map fun j => row ws (fun w => w.testBit j))
  else false
def C30_rows : List Nat := [10, 28, 33, 34, 36, 66, 81, 84, 3, 5, 9, 6, 18, 40, 72, 48, 96]
def C30_xs : List Nat :=
  (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map
    (fun a => encL a C30_rows)
def C30_f (x : Fin 7 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def C30_ori : List Nat → List Nat := literalRouteOrient C30_literalRoutes
def C30_Z (s : Nat) : Nat → Bool :=
  barEarlyScore (compactGoal 8 9) (compactCover 8 9) C30_S C30_N C30_idx C30_ori
    C30_patternScr C30_patternScr s
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
theorem C0_good : literalRoutesGood (compactGoal 8 7) C0_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_b0 : span C0_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C0_b1 : span C0_F 33 128 = true := by decide +kernel
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
theorem C1_good : literalRoutesGood (compactGoal 10 7) C1_literalRoutes = true := by decide +kernel
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
theorem C2_good : literalRoutesGood (compactGoal 9 7) C2_literalRoutes = true := by decide +kernel
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
theorem C3_good : literalRoutesGood (compactGoal 8 7) C3_literalRoutes = true := by decide +kernel
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
theorem C4_good : literalRoutesGood (compactGoal 8 7) C4_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_b0 : span C4_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C4_b1 : span C4_F 67 128 = true := by decide +kernel
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
theorem C5_good : literalRoutesGood (compactGoal 8 7) C5_literalRoutes = true := by decide +kernel
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
theorem C6_good : literalRoutesGood (compactGoal 9 7) C6_literalRoutes = true := by decide +kernel
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
theorem C7_good : literalRoutesGood (compactGoal 8 7) C7_literalRoutes = true := by decide +kernel
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
theorem C8_good : literalRoutesGood (compactGoal 7 7) C8_literalRoutes = true := by decide +kernel
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
theorem C9_good : literalRoutesGood (compactGoal 5 8) C9_literalRoutes = true := by decide +kernel
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
theorem C10_good : literalRoutesGood (compactGoal 5 8) C10_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_b0 : span C10_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C10_b1 : span C10_F 100 128 = true := by decide +kernel
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
theorem C11_good : literalRoutesGood (compactGoal 9 8) C11_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b0 : span C11_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b1 : span C11_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b2 : span C11_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b3 : span C11_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C11_b4 : span C11_F 68 512 = true := by decide +kernel
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
theorem C12_good : literalRoutesGood (compactGoal 5 8) C12_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_b0 : span C12_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C12_b1 : span C12_F 81 128 = true := by decide +kernel
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
theorem C13_good : literalRoutesGood (compactGoal 7 8) C13_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b0 : span C13_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b1 : span C13_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b2 : span C13_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b3 : span C13_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b4 : span C13_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b5 : span C13_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b6 : span C13_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b7 : span C13_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C13_b8 : span C13_F 78 1024 = true := by decide +kernel
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
theorem C14_good : literalRoutesGood (compactGoal 5 8) C14_literalRoutes = true := by decide +kernel
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
theorem C15_good : literalRoutesGood (compactGoal 8 8) C15_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b0 : span C15_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b1 : span C15_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b2 : span C15_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b3 : span C15_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b4 : span C15_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b5 : span C15_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b6 : span C15_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b7 : span C15_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b8 : span C15_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C15_b9 : span C15_F 47 1152 = true := by decide +kernel
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
theorem C16_good : literalRoutesGood (compactGoal 6 8) C16_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_b0 : span C16_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C16_b1 : span C16_F 26 128 = true := by decide +kernel
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
theorem C17_good : literalRoutesGood (compactGoal 8 8) C17_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b0 : span C17_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b1 : span C17_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b2 : span C17_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b3 : span C17_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b4 : span C17_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b5 : span C17_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b6 : span C17_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C17_b7 : span C17_F 87 896 = true := by decide +kernel
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
theorem C18_good : literalRoutesGood (compactGoal 8 8) C18_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_b0 : span C18_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_b1 : span C18_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_b2 : span C18_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C18_b3 : span C18_F 7 384 = true := by decide +kernel
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
theorem C19_good : literalRoutesGood (compactGoal 7 8) C19_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b0 : span C19_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b1 : span C19_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b2 : span C19_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b3 : span C19_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b4 : span C19_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b5 : span C19_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C19_b6 : span C19_F 30 768 = true := by decide +kernel
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
theorem C20_good : literalRoutesGood (compactGoal 7 8) C20_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b0 : span C20_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b1 : span C20_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b2 : span C20_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b3 : span C20_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b4 : span C20_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b5 : span C20_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b6 : span C20_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b7 : span C20_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b8 : span C20_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b9 : span C20_F 128 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b10 : span C20_F 128 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C20_b11 : span C20_F 91 1408 = true := by decide +kernel
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
theorem C21_good : literalRoutesGood (compactGoal 8 8) C21_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b0 : span C21_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b1 : span C21_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b2 : span C21_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b3 : span C21_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b4 : span C21_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b5 : span C21_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b6 : span C21_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b7 : span C21_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b8 : span C21_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C21_b9 : span C21_F 14 1152 = true := by decide +kernel
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
theorem C22_good : literalRoutesGood (compactGoal 6 8) C22_literalRoutes = true := by decide +kernel
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
theorem C23_good : literalRoutesGood (compactGoal 7 8) C23_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_b0 : span C23_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_b1 : span C23_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_b2 : span C23_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C23_b3 : span C23_F 46 384 = true := by decide +kernel
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
theorem C24_good : literalRoutesGood (compactGoal 9 8) C24_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_b0 : span C24_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C24_b1 : span C24_F 120 128 = true := by decide +kernel
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
theorem C25_good : literalRoutesGood (compactGoal 7 8) C25_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_b0 : span C25_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C25_b1 : span C25_F 127 128 = true := by decide +kernel
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
theorem C26_good : literalRoutesGood (compactGoal 9 9) C26_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b0 : span C26_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b1 : span C26_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b2 : span C26_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b3 : span C26_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b4 : span C26_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b5 : span C26_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b6 : span C26_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b7 : span C26_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C26_b8 : span C26_F 43 1024 = true := by decide +kernel
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
theorem C27_good : literalRoutesGood (compactGoal 8 9) C27_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b0 : span C27_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b1 : span C27_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b2 : span C27_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b3 : span C27_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b4 : span C27_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b5 : span C27_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b6 : span C27_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b7 : span C27_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b8 : span C27_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b9 : span C27_F 128 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b10 : span C27_F 128 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b11 : span C27_F 128 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b12 : span C27_F 128 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b13 : span C27_F 128 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b14 : span C27_F 128 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b15 : span C27_F 128 1920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b16 : span C27_F 128 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b17 : span C27_F 128 2176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b18 : span C27_F 128 2304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b19 : span C27_F 128 2432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b20 : span C27_F 128 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b21 : span C27_F 128 2688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b22 : span C27_F 128 2816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b23 : span C27_F 128 2944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C27_b24 : span C27_F 52 3072 = true := by decide +kernel
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
theorem C28_good : literalRoutesGood (compactGoal 7 9) C28_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b0 : span C28_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b1 : span C28_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b2 : span C28_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b3 : span C28_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b4 : span C28_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b5 : span C28_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b6 : span C28_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b7 : span C28_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b8 : span C28_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b9 : span C28_F 128 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b10 : span C28_F 128 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b11 : span C28_F 128 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b12 : span C28_F 128 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b13 : span C28_F 128 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b14 : span C28_F 128 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b15 : span C28_F 128 1920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b16 : span C28_F 128 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b17 : span C28_F 128 2176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b18 : span C28_F 128 2304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b19 : span C28_F 128 2432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b20 : span C28_F 128 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b21 : span C28_F 128 2688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b22 : span C28_F 128 2816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b23 : span C28_F 128 2944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b24 : span C28_F 128 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b25 : span C28_F 128 3200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b26 : span C28_F 128 3328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b27 : span C28_F 128 3456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b28 : span C28_F 128 3584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b29 : span C28_F 128 3712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b30 : span C28_F 128 3840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b31 : span C28_F 128 3968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b32 : span C28_F 128 4096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b33 : span C28_F 128 4224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b34 : span C28_F 128 4352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b35 : span C28_F 128 4480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b36 : span C28_F 128 4608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b37 : span C28_F 128 4736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b38 : span C28_F 128 4864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b39 : span C28_F 128 4992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b40 : span C28_F 128 5120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b41 : span C28_F 128 5248 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b42 : span C28_F 128 5376 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b43 : span C28_F 128 5504 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C28_b44 : span C28_F 110 5632 = true := by decide +kernel
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
theorem C29_good : literalRoutesGood (compactGoal 7 9) C29_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b0 : span C29_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b1 : span C29_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b2 : span C29_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b3 : span C29_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b4 : span C29_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b5 : span C29_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b6 : span C29_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b7 : span C29_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b8 : span C29_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b9 : span C29_F 128 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b10 : span C29_F 128 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b11 : span C29_F 128 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b12 : span C29_F 128 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b13 : span C29_F 128 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b14 : span C29_F 128 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C29_b15 : span C29_F 102 1920 = true := by decide +kernel
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
theorem C30_good : literalRoutesGood (compactGoal 8 9) C30_literalRoutes = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b0 : span C30_F 128 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b1 : span C30_F 128 128 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b2 : span C30_F 128 256 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b3 : span C30_F 128 384 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b4 : span C30_F 128 512 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b5 : span C30_F 128 640 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b6 : span C30_F 128 768 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b7 : span C30_F 128 896 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b8 : span C30_F 128 1024 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b9 : span C30_F 128 1152 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b10 : span C30_F 128 1280 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b11 : span C30_F 128 1408 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b12 : span C30_F 128 1536 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b13 : span C30_F 128 1664 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b14 : span C30_F 128 1792 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b15 : span C30_F 128 1920 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b16 : span C30_F 128 2048 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b17 : span C30_F 128 2176 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b18 : span C30_F 128 2304 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b19 : span C30_F 128 2432 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b20 : span C30_F 128 2560 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b21 : span C30_F 128 2688 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b22 : span C30_F 128 2816 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b23 : span C30_F 128 2944 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b24 : span C30_F 128 3072 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b25 : span C30_F 128 3200 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b26 : span C30_F 128 3328 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b27 : span C30_F 128 3456 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b28 : span C30_F 128 3584 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b29 : span C30_F 128 3712 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b30 : span C30_F 128 3840 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b31 : span C30_F 128 3968 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b32 : span C30_F 128 4096 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b33 : span C30_F 128 4224 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b34 : span C30_F 128 4352 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b35 : span C30_F 128 4480 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b36 : span C30_F 128 4608 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b37 : span C30_F 128 4736 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b38 : span C30_F 128 4864 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b39 : span C30_F 128 4992 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b40 : span C30_F 128 5120 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem C30_b41 : span C30_F 62 5248 = true := by decide +kernel
theorem C0_patternScore_eq (masks : List Nat) :
    C0_patternScore masks = C0_rankPool.any (fastEntry (compactGoal 8 7) 4 C0_coords masks) := by
  unfold C0_patternScore
  split <;> rfl
theorem C0_patternScr_eq (s : Nat) (ws : List Nat) :
    C0_patternScr s ws = fastScr (compactGoal 8 7) s C0_coords 4 C0_rankPool ws := by
  unfold C0_patternScr fastScr
  split
  · rw [C0_patternScore_eq]
  · rfl
theorem C0_nonconstant : ∃ x y : Fin 6 → Bool, C0_f x ≠ C0_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C0_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C0_ori ws) := literalRouteOrient_run h C0_literalRoutes C0_good
theorem C0_checked : ∀ s ≤ 9, ∀ j < C0_N s, C0_Z s j = true := by
  apply certFlat_sound
  change span C0_F 161 0 = true
  exact (span_join C0_b0 C0_b1)
theorem C0_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C0_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C0_S) (N := C0_N) (idx := C0_idx) (ori := C0_ori)
    (early := C0_patternScr) (score := C0_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C0_patternScr_eq) (score_no_of_fastScr_eq C0_patternScr_eq)
    C0_ori_run C0_checked (by decide) (by decide) C0_initial_perm
theorem C0_no_small : ¬ HasMonoSize 6 C0_f 9 :=
  encoded_compact_exclusion C0_f C0_nonconstant 9 C0_rows C0_xs 8 7
    rfl C0_enc_goal C0_proper C0_no_run
theorem C0_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = C0_f x) :
    10 ≤ C.size := mono_lower C0_f 9 C0_no_small C hmono hev
theorem C1_patternScore_eq (masks : List Nat) :
    C1_patternScore masks = C1_rankPool.any (fastEntry (compactGoal 10 7) 4 C1_coords masks) := by
  unfold C1_patternScore
  split <;> rfl
theorem C1_patternScr_eq (s : Nat) (ws : List Nat) :
    C1_patternScr s ws = fastScr (compactGoal 10 7) s C1_coords 4 C1_rankPool ws := by
  unfold C1_patternScr fastScr
  split
  · rw [C1_patternScore_eq]
  · rfl
theorem C1_nonconstant : ∃ x y : Fin 7 → Bool, C1_f x ≠ C1_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C1_ori_run {s ws} (h : MonRun (compactGoal 10 7) s ws) :
    MonRun (compactGoal 10 7) s (C1_ori ws) := literalRouteOrient_run h C1_literalRoutes C1_good
theorem C1_checked : ∀ s ≤ 9, ∀ j < C1_N s, C1_Z s j = true := by
  apply certFlat_sound
  change span C1_F 85 0 = true
  exact C1_b0
theorem C1_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 10 7) s C1_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 10 7) (cover := compactCover 10 7)
    (S := C1_S) (N := C1_N) (idx := C1_idx) (ori := C1_ori)
    (early := C1_patternScr) (score := C1_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C1_patternScr_eq) (score_no_of_fastScr_eq C1_patternScr_eq)
    C1_ori_run C1_checked (by decide) (by decide) C1_initial_perm
theorem C1_no_small : ¬ HasMonoSize 7 C1_f 9 :=
  encoded_compact_exclusion C1_f C1_nonconstant 9 C1_rows C1_xs 10 7
    rfl C1_enc_goal C1_proper C1_no_run
theorem C1_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C1_f x) :
    10 ≤ C.size := mono_lower C1_f 9 C1_no_small C hmono hev
theorem C2_patternScore_eq (masks : List Nat) :
    C2_patternScore masks = C2_rankPool.any (fastEntry (compactGoal 9 7) 4 C2_coords masks) := by
  unfold C2_patternScore
  split <;> rfl
theorem C2_patternScr_eq (s : Nat) (ws : List Nat) :
    C2_patternScr s ws = fastScr (compactGoal 9 7) s C2_coords 4 C2_rankPool ws := by
  unfold C2_patternScr fastScr
  split
  · rw [C2_patternScore_eq]
  · rfl
theorem C2_nonconstant : ∃ x y : Fin 7 → Bool, C2_f x ≠ C2_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C2_ori_run {s ws} (h : MonRun (compactGoal 9 7) s ws) :
    MonRun (compactGoal 9 7) s (C2_ori ws) := literalRouteOrient_run h C2_literalRoutes C2_good
theorem C2_checked : ∀ s ≤ 9, ∀ j < C2_N s, C2_Z s j = true := by
  apply certFlat_sound
  change span C2_F 106 0 = true
  exact C2_b0
theorem C2_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 9 7) s C2_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 9 7) (cover := compactCover 9 7)
    (S := C2_S) (N := C2_N) (idx := C2_idx) (ori := C2_ori)
    (early := C2_patternScr) (score := C2_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C2_patternScr_eq) (score_no_of_fastScr_eq C2_patternScr_eq)
    C2_ori_run C2_checked (by decide) (by decide) C2_initial_perm
theorem C2_no_small : ¬ HasMonoSize 7 C2_f 9 :=
  encoded_compact_exclusion C2_f C2_nonconstant 9 C2_rows C2_xs 9 7
    rfl C2_enc_goal C2_proper C2_no_run
theorem C2_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C2_f x) :
    10 ≤ C.size := mono_lower C2_f 9 C2_no_small C hmono hev
theorem C3_patternScore_eq (masks : List Nat) :
    C3_patternScore masks = C3_rankPool.any (fastEntry (compactGoal 8 7) 4 C3_coords masks) := by
  unfold C3_patternScore
  split <;> rfl
theorem C3_patternScr_eq (s : Nat) (ws : List Nat) :
    C3_patternScr s ws = fastScr (compactGoal 8 7) s C3_coords 4 C3_rankPool ws := by
  unfold C3_patternScr fastScr
  split
  · rw [C3_patternScore_eq]
  · rfl
theorem C3_nonconstant : ∃ x y : Fin 7 → Bool, C3_f x ≠ C3_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C3_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C3_ori ws) := literalRouteOrient_run h C3_literalRoutes C3_good
theorem C3_checked : ∀ s ≤ 9, ∀ j < C3_N s, C3_Z s j = true := by
  apply certFlat_sound
  change span C3_F 110 0 = true
  exact C3_b0
theorem C3_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C3_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C3_S) (N := C3_N) (idx := C3_idx) (ori := C3_ori)
    (early := C3_patternScr) (score := C3_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C3_patternScr_eq) (score_no_of_fastScr_eq C3_patternScr_eq)
    C3_ori_run C3_checked (by decide) (by decide) C3_initial_perm
theorem C3_no_small : ¬ HasMonoSize 7 C3_f 9 :=
  encoded_compact_exclusion C3_f C3_nonconstant 9 C3_rows C3_xs 8 7
    rfl C3_enc_goal C3_proper C3_no_run
theorem C3_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C3_f x) :
    10 ≤ C.size := mono_lower C3_f 9 C3_no_small C hmono hev
theorem C4_patternScore_eq (masks : List Nat) :
    C4_patternScore masks = C4_rankPool.any (fastEntry (compactGoal 8 7) 4 C4_coords masks) := by
  unfold C4_patternScore
  split <;> rfl
theorem C4_patternScr_eq (s : Nat) (ws : List Nat) :
    C4_patternScr s ws = fastScr (compactGoal 8 7) s C4_coords 4 C4_rankPool ws := by
  unfold C4_patternScr fastScr
  split
  · rw [C4_patternScore_eq]
  · rfl
theorem C4_nonconstant : ∃ x y : Fin 7 → Bool, C4_f x ≠ C4_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C4_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C4_ori ws) := literalRouteOrient_run h C4_literalRoutes C4_good
theorem C4_checked : ∀ s ≤ 9, ∀ j < C4_N s, C4_Z s j = true := by
  apply certFlat_sound
  change span C4_F 195 0 = true
  exact (span_join C4_b0 C4_b1)
theorem C4_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C4_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C4_S) (N := C4_N) (idx := C4_idx) (ori := C4_ori)
    (early := C4_patternScr) (score := C4_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C4_patternScr_eq) (score_no_of_fastScr_eq C4_patternScr_eq)
    C4_ori_run C4_checked (by decide) (by decide) C4_initial_perm
theorem C4_no_small : ¬ HasMonoSize 7 C4_f 9 :=
  encoded_compact_exclusion C4_f C4_nonconstant 9 C4_rows C4_xs 8 7
    rfl C4_enc_goal C4_proper C4_no_run
theorem C4_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C4_f x) :
    10 ≤ C.size := mono_lower C4_f 9 C4_no_small C hmono hev
theorem C5_patternScore_eq (masks : List Nat) :
    C5_patternScore masks = C5_rankPool.any (fastEntry (compactGoal 8 7) 4 C5_coords masks) := by
  unfold C5_patternScore
  split <;> rfl
theorem C5_patternScr_eq (s : Nat) (ws : List Nat) :
    C5_patternScr s ws = fastScr (compactGoal 8 7) s C5_coords 4 C5_rankPool ws := by
  unfold C5_patternScr fastScr
  split
  · rw [C5_patternScore_eq]
  · rfl
theorem C5_nonconstant : ∃ x y : Fin 7 → Bool, C5_f x ≠ C5_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C5_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C5_ori ws) := literalRouteOrient_run h C5_literalRoutes C5_good
theorem C5_checked : ∀ s ≤ 9, ∀ j < C5_N s, C5_Z s j = true := by
  apply certFlat_sound
  change span C5_F 122 0 = true
  exact C5_b0
theorem C5_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C5_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C5_S) (N := C5_N) (idx := C5_idx) (ori := C5_ori)
    (early := C5_patternScr) (score := C5_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C5_patternScr_eq) (score_no_of_fastScr_eq C5_patternScr_eq)
    C5_ori_run C5_checked (by decide) (by decide) C5_initial_perm
theorem C5_no_small : ¬ HasMonoSize 7 C5_f 9 :=
  encoded_compact_exclusion C5_f C5_nonconstant 9 C5_rows C5_xs 8 7
    rfl C5_enc_goal C5_proper C5_no_run
theorem C5_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C5_f x) :
    10 ≤ C.size := mono_lower C5_f 9 C5_no_small C hmono hev
theorem C6_patternScore_eq (masks : List Nat) :
    C6_patternScore masks = C6_rankPool.any (fastEntry (compactGoal 9 7) 4 C6_coords masks) := by
  unfold C6_patternScore
  split <;> rfl
theorem C6_patternScr_eq (s : Nat) (ws : List Nat) :
    C6_patternScr s ws = fastScr (compactGoal 9 7) s C6_coords 4 C6_rankPool ws := by
  unfold C6_patternScr fastScr
  split
  · rw [C6_patternScore_eq]
  · rfl
theorem C6_nonconstant : ∃ x y : Fin 7 → Bool, C6_f x ≠ C6_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C6_ori_run {s ws} (h : MonRun (compactGoal 9 7) s ws) :
    MonRun (compactGoal 9 7) s (C6_ori ws) := literalRouteOrient_run h C6_literalRoutes C6_good
theorem C6_checked : ∀ s ≤ 9, ∀ j < C6_N s, C6_Z s j = true := by
  apply certFlat_sound
  change span C6_F 72 0 = true
  exact C6_b0
theorem C6_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 9 7) s C6_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 9 7) (cover := compactCover 9 7)
    (S := C6_S) (N := C6_N) (idx := C6_idx) (ori := C6_ori)
    (early := C6_patternScr) (score := C6_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C6_patternScr_eq) (score_no_of_fastScr_eq C6_patternScr_eq)
    C6_ori_run C6_checked (by decide) (by decide) C6_initial_perm
theorem C6_no_small : ¬ HasMonoSize 7 C6_f 9 :=
  encoded_compact_exclusion C6_f C6_nonconstant 9 C6_rows C6_xs 9 7
    rfl C6_enc_goal C6_proper C6_no_run
theorem C6_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C6_f x) :
    10 ≤ C.size := mono_lower C6_f 9 C6_no_small C hmono hev
theorem C7_patternScore_eq (masks : List Nat) :
    C7_patternScore masks = C7_rankPool.any (fastEntry (compactGoal 8 7) 4 C7_coords masks) := by
  unfold C7_patternScore
  split <;> rfl
theorem C7_patternScr_eq (s : Nat) (ws : List Nat) :
    C7_patternScr s ws = fastScr (compactGoal 8 7) s C7_coords 4 C7_rankPool ws := by
  unfold C7_patternScr fastScr
  split
  · rw [C7_patternScore_eq]
  · rfl
theorem C7_nonconstant : ∃ x y : Fin 7 → Bool, C7_f x ≠ C7_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C7_ori_run {s ws} (h : MonRun (compactGoal 8 7) s ws) :
    MonRun (compactGoal 8 7) s (C7_ori ws) := literalRouteOrient_run h C7_literalRoutes C7_good
theorem C7_checked : ∀ s ≤ 9, ∀ j < C7_N s, C7_Z s j = true := by
  apply certFlat_sound
  change span C7_F 89 0 = true
  exact C7_b0
theorem C7_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 8 7) s C7_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 7) (cover := compactCover 8 7)
    (S := C7_S) (N := C7_N) (idx := C7_idx) (ori := C7_ori)
    (early := C7_patternScr) (score := C7_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C7_patternScr_eq) (score_no_of_fastScr_eq C7_patternScr_eq)
    C7_ori_run C7_checked (by decide) (by decide) C7_initial_perm
theorem C7_no_small : ¬ HasMonoSize 7 C7_f 9 :=
  encoded_compact_exclusion C7_f C7_nonconstant 9 C7_rows C7_xs 8 7
    rfl C7_enc_goal C7_proper C7_no_run
theorem C7_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C7_f x) :
    10 ≤ C.size := mono_lower C7_f 9 C7_no_small C hmono hev
theorem C8_patternScore_eq (masks : List Nat) :
    C8_patternScore masks = C8_rankPool.any (fastEntry (compactGoal 7 7) 4 C8_coords masks) := by
  unfold C8_patternScore
  split <;> rfl
theorem C8_patternScr_eq (s : Nat) (ws : List Nat) :
    C8_patternScr s ws = fastScr (compactGoal 7 7) s C8_coords 4 C8_rankPool ws := by
  unfold C8_patternScr fastScr
  split
  · rw [C8_patternScore_eq]
  · rfl
theorem C8_nonconstant : ∃ x y : Fin 7 → Bool, C8_f x ≠ C8_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C8_ori_run {s ws} (h : MonRun (compactGoal 7 7) s ws) :
    MonRun (compactGoal 7 7) s (C8_ori ws) := literalRouteOrient_run h C8_literalRoutes C8_good
theorem C8_checked : ∀ s ≤ 9, ∀ j < C8_N s, C8_Z s j = true := by
  apply certFlat_sound
  change span C8_F 14 0 = true
  exact C8_b0
theorem C8_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 7 7) s C8_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 7) (cover := compactCover 7 7)
    (S := C8_S) (N := C8_N) (idx := C8_idx) (ori := C8_ori)
    (early := C8_patternScr) (score := C8_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C8_patternScr_eq) (score_no_of_fastScr_eq C8_patternScr_eq)
    C8_ori_run C8_checked (by decide) (by decide) C8_initial_perm
theorem C8_no_small : ¬ HasMonoSize 7 C8_f 9 :=
  encoded_compact_exclusion C8_f C8_nonconstant 9 C8_rows C8_xs 7 7
    rfl C8_enc_goal C8_proper C8_no_run
theorem C8_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C8_f x) :
    10 ≤ C.size := mono_lower C8_f 9 C8_no_small C hmono hev
theorem C9_patternScore_eq (masks : List Nat) :
    C9_patternScore masks = C9_rankPool.any (fastEntry (compactGoal 5 8) 4 C9_coords masks) := by
  unfold C9_patternScore
  split <;> rfl
theorem C9_patternScr_eq (s : Nat) (ws : List Nat) :
    C9_patternScr s ws = fastScr (compactGoal 5 8) s C9_coords 4 C9_rankPool ws := by
  unfold C9_patternScr fastScr
  split
  · rw [C9_patternScore_eq]
  · rfl
theorem C9_nonconstant : ∃ x y : Fin 7 → Bool, C9_f x ≠ C9_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C9_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C9_ori ws) := literalRouteOrient_run h C9_literalRoutes C9_good
theorem C9_checked : ∀ s ≤ 9, ∀ j < C9_N s, C9_Z s j = true := by
  apply certFlat_sound
  change span C9_F 122 0 = true
  exact C9_b0
theorem C9_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C9_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C9_S) (N := C9_N) (idx := C9_idx) (ori := C9_ori)
    (early := C9_patternScr) (score := C9_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C9_patternScr_eq) (score_no_of_fastScr_eq C9_patternScr_eq)
    C9_ori_run C9_checked (by decide) (by decide) C9_initial_perm
theorem C9_no_small : ¬ HasMonoSize 7 C9_f 9 :=
  encoded_compact_exclusion C9_f C9_nonconstant 9 C9_rows C9_xs 5 8
    rfl C9_enc_goal C9_proper C9_no_run
theorem C9_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C9_f x) :
    10 ≤ C.size := mono_lower C9_f 9 C9_no_small C hmono hev
theorem C10_patternScore_eq (masks : List Nat) :
    C10_patternScore masks = C10_rankPool.any (fastEntry (compactGoal 5 8) 4 C10_coords masks) := by
  unfold C10_patternScore
  split <;> rfl
theorem C10_patternScr_eq (s : Nat) (ws : List Nat) :
    C10_patternScr s ws = fastScr (compactGoal 5 8) s C10_coords 4 C10_rankPool ws := by
  unfold C10_patternScr fastScr
  split
  · rw [C10_patternScore_eq]
  · rfl
theorem C10_nonconstant : ∃ x y : Fin 7 → Bool, C10_f x ≠ C10_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C10_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C10_ori ws) := literalRouteOrient_run h C10_literalRoutes C10_good
theorem C10_checked : ∀ s ≤ 9, ∀ j < C10_N s, C10_Z s j = true := by
  apply certFlat_sound
  change span C10_F 228 0 = true
  exact (span_join C10_b0 C10_b1)
theorem C10_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C10_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C10_S) (N := C10_N) (idx := C10_idx) (ori := C10_ori)
    (early := C10_patternScr) (score := C10_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C10_patternScr_eq) (score_no_of_fastScr_eq C10_patternScr_eq)
    C10_ori_run C10_checked (by decide) (by decide) C10_initial_perm
theorem C10_no_small : ¬ HasMonoSize 7 C10_f 9 :=
  encoded_compact_exclusion C10_f C10_nonconstant 9 C10_rows C10_xs 5 8
    rfl C10_enc_goal C10_proper C10_no_run
theorem C10_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C10_f x) :
    10 ≤ C.size := mono_lower C10_f 9 C10_no_small C hmono hev
theorem C11_patternScore_eq (masks : List Nat) :
    C11_patternScore masks = C11_rankPool.any (fastEntry (compactGoal 9 8) 5 C11_coords masks) := by
  unfold C11_patternScore
  split <;> rfl
theorem C11_patternScr_eq (s : Nat) (ws : List Nat) :
    C11_patternScr s ws = fastScr (compactGoal 9 8) s C11_coords 5 C11_rankPool ws := by
  unfold C11_patternScr fastScr
  split
  · rw [C11_patternScore_eq]
  · rfl
theorem C11_nonconstant : ∃ x y : Fin 7 → Bool, C11_f x ≠ C11_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C11_ori_run {s ws} (h : MonRun (compactGoal 9 8) s ws) :
    MonRun (compactGoal 9 8) s (C11_ori ws) := literalRouteOrient_run h C11_literalRoutes C11_good
theorem C11_checked : ∀ s ≤ 10, ∀ j < C11_N s, C11_Z s j = true := by
  apply certFlat_sound
  change span C11_F 580 0 = true
  exact (span_join (span_join C11_b0 C11_b1) (span_join C11_b2 (span_join C11_b3 C11_b4)))
theorem C11_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 9 8) s C11_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 9 8) (cover := compactCover 9 8)
    (S := C11_S) (N := C11_N) (idx := C11_idx) (ori := C11_ori)
    (early := C11_patternScr) (score := C11_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C11_patternScr_eq) (score_no_of_fastScr_eq C11_patternScr_eq)
    C11_ori_run C11_checked (by decide) (by decide) C11_initial_perm
theorem C11_no_small : ¬ HasMonoSize 7 C11_f 10 :=
  encoded_compact_exclusion C11_f C11_nonconstant 10 C11_rows C11_xs 9 8
    rfl C11_enc_goal C11_proper C11_no_run
theorem C11_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C11_f x) :
    11 ≤ C.size := mono_lower C11_f 10 C11_no_small C hmono hev
theorem C12_patternScore_eq (masks : List Nat) :
    C12_patternScore masks = C12_rankPool.any (fastEntry (compactGoal 5 8) 4 C12_coords masks) := by
  unfold C12_patternScore
  split <;> rfl
theorem C12_patternScr_eq (s : Nat) (ws : List Nat) :
    C12_patternScr s ws = fastScr (compactGoal 5 8) s C12_coords 4 C12_rankPool ws := by
  unfold C12_patternScr fastScr
  split
  · rw [C12_patternScore_eq]
  · rfl
theorem C12_nonconstant : ∃ x y : Fin 7 → Bool, C12_f x ≠ C12_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C12_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C12_ori ws) := literalRouteOrient_run h C12_literalRoutes C12_good
theorem C12_checked : ∀ s ≤ 9, ∀ j < C12_N s, C12_Z s j = true := by
  apply certFlat_sound
  change span C12_F 209 0 = true
  exact (span_join C12_b0 C12_b1)
theorem C12_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C12_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C12_S) (N := C12_N) (idx := C12_idx) (ori := C12_ori)
    (early := C12_patternScr) (score := C12_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C12_patternScr_eq) (score_no_of_fastScr_eq C12_patternScr_eq)
    C12_ori_run C12_checked (by decide) (by decide) C12_initial_perm
theorem C12_no_small : ¬ HasMonoSize 7 C12_f 9 :=
  encoded_compact_exclusion C12_f C12_nonconstant 9 C12_rows C12_xs 5 8
    rfl C12_enc_goal C12_proper C12_no_run
theorem C12_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C12_f x) :
    10 ≤ C.size := mono_lower C12_f 9 C12_no_small C hmono hev
theorem C13_patternScore_eq (masks : List Nat) :
    C13_patternScore masks = C13_rankPool.any (fastEntry (compactGoal 7 8) 4 C13_coords masks) := by
  unfold C13_patternScore
  split <;> rfl
theorem C13_patternScr_eq (s : Nat) (ws : List Nat) :
    C13_patternScr s ws = fastScr (compactGoal 7 8) s C13_coords 4 C13_rankPool ws := by
  unfold C13_patternScr fastScr
  split
  · rw [C13_patternScore_eq]
  · rfl
theorem C13_nonconstant : ∃ x y : Fin 7 → Bool, C13_f x ≠ C13_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C13_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C13_ori ws) := literalRouteOrient_run h C13_literalRoutes C13_good
theorem C13_checked : ∀ s ≤ 10, ∀ j < C13_N s, C13_Z s j = true := by
  apply certFlat_sound
  change span C13_F 1102 0 = true
  exact (span_join (span_join (span_join C13_b0 C13_b1) (span_join C13_b2 C13_b3)) (span_join (span_join C13_b4 C13_b5) (span_join C13_b6 (span_join C13_b7 C13_b8))))
theorem C13_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C13_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C13_S) (N := C13_N) (idx := C13_idx) (ori := C13_ori)
    (early := C13_patternScr) (score := C13_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C13_patternScr_eq) (score_no_of_fastScr_eq C13_patternScr_eq)
    C13_ori_run C13_checked (by decide) (by decide) C13_initial_perm
theorem C13_no_small : ¬ HasMonoSize 7 C13_f 10 :=
  encoded_compact_exclusion C13_f C13_nonconstant 10 C13_rows C13_xs 7 8
    rfl C13_enc_goal C13_proper C13_no_run
theorem C13_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C13_f x) :
    11 ≤ C.size := mono_lower C13_f 10 C13_no_small C hmono hev
theorem C14_patternScore_eq (masks : List Nat) :
    C14_patternScore masks = C14_rankPool.any (fastEntry (compactGoal 5 8) 4 C14_coords masks) := by
  unfold C14_patternScore
  split <;> rfl
theorem C14_patternScr_eq (s : Nat) (ws : List Nat) :
    C14_patternScr s ws = fastScr (compactGoal 5 8) s C14_coords 4 C14_rankPool ws := by
  unfold C14_patternScr fastScr
  split
  · rw [C14_patternScore_eq]
  · rfl
theorem C14_nonconstant : ∃ x y : Fin 7 → Bool, C14_f x ≠ C14_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C14_ori_run {s ws} (h : MonRun (compactGoal 5 8) s ws) :
    MonRun (compactGoal 5 8) s (C14_ori ws) := literalRouteOrient_run h C14_literalRoutes C14_good
theorem C14_checked : ∀ s ≤ 9, ∀ j < C14_N s, C14_Z s j = true := by
  apply certFlat_sound
  change span C14_F 115 0 = true
  exact C14_b0
theorem C14_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 5 8) s C14_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 5 8) (cover := compactCover 5 8)
    (S := C14_S) (N := C14_N) (idx := C14_idx) (ori := C14_ori)
    (early := C14_patternScr) (score := C14_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C14_patternScr_eq) (score_no_of_fastScr_eq C14_patternScr_eq)
    C14_ori_run C14_checked (by decide) (by decide) C14_initial_perm
theorem C14_no_small : ¬ HasMonoSize 7 C14_f 9 :=
  encoded_compact_exclusion C14_f C14_nonconstant 9 C14_rows C14_xs 5 8
    rfl C14_enc_goal C14_proper C14_no_run
theorem C14_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C14_f x) :
    10 ≤ C.size := mono_lower C14_f 9 C14_no_small C hmono hev
theorem C15_patternScore_eq (masks : List Nat) :
    C15_patternScore masks = C15_rankPool.any (fastEntry (compactGoal 8 8) 4 C15_coords masks) := by
  unfold C15_patternScore
  split <;> rfl
theorem C15_patternScr_eq (s : Nat) (ws : List Nat) :
    C15_patternScr s ws = fastScr (compactGoal 8 8) s C15_coords 4 C15_rankPool ws := by
  unfold C15_patternScr fastScr
  split
  · rw [C15_patternScore_eq]
  · rfl
theorem C15_nonconstant : ∃ x y : Fin 7 → Bool, C15_f x ≠ C15_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C15_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C15_ori ws) := literalRouteOrient_run h C15_literalRoutes C15_good
theorem C15_checked : ∀ s ≤ 10, ∀ j < C15_N s, C15_Z s j = true := by
  apply certFlat_sound
  change span C15_F 1199 0 = true
  exact (span_join (span_join (span_join C15_b0 C15_b1) (span_join C15_b2 (span_join C15_b3 C15_b4))) (span_join (span_join C15_b5 C15_b6) (span_join C15_b7 (span_join C15_b8 C15_b9))))
theorem C15_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C15_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C15_S) (N := C15_N) (idx := C15_idx) (ori := C15_ori)
    (early := C15_patternScr) (score := C15_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C15_patternScr_eq) (score_no_of_fastScr_eq C15_patternScr_eq)
    C15_ori_run C15_checked (by decide) (by decide) C15_initial_perm
theorem C15_no_small : ¬ HasMonoSize 7 C15_f 10 :=
  encoded_compact_exclusion C15_f C15_nonconstant 10 C15_rows C15_xs 8 8
    rfl C15_enc_goal C15_proper C15_no_run
theorem C15_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C15_f x) :
    11 ≤ C.size := mono_lower C15_f 10 C15_no_small C hmono hev
theorem C16_patternScore_eq (masks : List Nat) :
    C16_patternScore masks = C16_rankPool.any (fastEntry (compactGoal 6 8) 4 C16_coords masks) := by
  unfold C16_patternScore
  split <;> rfl
theorem C16_patternScr_eq (s : Nat) (ws : List Nat) :
    C16_patternScr s ws = fastScr (compactGoal 6 8) s C16_coords 4 C16_rankPool ws := by
  unfold C16_patternScr fastScr
  split
  · rw [C16_patternScore_eq]
  · rfl
theorem C16_nonconstant : ∃ x y : Fin 7 → Bool, C16_f x ≠ C16_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C16_ori_run {s ws} (h : MonRun (compactGoal 6 8) s ws) :
    MonRun (compactGoal 6 8) s (C16_ori ws) := literalRouteOrient_run h C16_literalRoutes C16_good
theorem C16_checked : ∀ s ≤ 9, ∀ j < C16_N s, C16_Z s j = true := by
  apply certFlat_sound
  change span C16_F 154 0 = true
  exact (span_join C16_b0 C16_b1)
theorem C16_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 6 8) s C16_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 6 8) (cover := compactCover 6 8)
    (S := C16_S) (N := C16_N) (idx := C16_idx) (ori := C16_ori)
    (early := C16_patternScr) (score := C16_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C16_patternScr_eq) (score_no_of_fastScr_eq C16_patternScr_eq)
    C16_ori_run C16_checked (by decide) (by decide) C16_initial_perm
theorem C16_no_small : ¬ HasMonoSize 7 C16_f 9 :=
  encoded_compact_exclusion C16_f C16_nonconstant 9 C16_rows C16_xs 6 8
    rfl C16_enc_goal C16_proper C16_no_run
theorem C16_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C16_f x) :
    10 ≤ C.size := mono_lower C16_f 9 C16_no_small C hmono hev
theorem C17_patternScore_eq (masks : List Nat) :
    C17_patternScore masks = C17_rankPool.any (fastEntry (compactGoal 8 8) 4 C17_coords masks) := by
  unfold C17_patternScore
  split <;> rfl
theorem C17_patternScr_eq (s : Nat) (ws : List Nat) :
    C17_patternScr s ws = fastScr (compactGoal 8 8) s C17_coords 4 C17_rankPool ws := by
  unfold C17_patternScr fastScr
  split
  · rw [C17_patternScore_eq]
  · rfl
theorem C17_nonconstant : ∃ x y : Fin 7 → Bool, C17_f x ≠ C17_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C17_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C17_ori ws) := literalRouteOrient_run h C17_literalRoutes C17_good
theorem C17_checked : ∀ s ≤ 10, ∀ j < C17_N s, C17_Z s j = true := by
  apply certFlat_sound
  change span C17_F 983 0 = true
  exact (span_join (span_join (span_join C17_b0 C17_b1) (span_join C17_b2 C17_b3)) (span_join (span_join C17_b4 C17_b5) (span_join C17_b6 C17_b7)))
theorem C17_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C17_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C17_S) (N := C17_N) (idx := C17_idx) (ori := C17_ori)
    (early := C17_patternScr) (score := C17_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C17_patternScr_eq) (score_no_of_fastScr_eq C17_patternScr_eq)
    C17_ori_run C17_checked (by decide) (by decide) C17_initial_perm
theorem C17_no_small : ¬ HasMonoSize 7 C17_f 10 :=
  encoded_compact_exclusion C17_f C17_nonconstant 10 C17_rows C17_xs 8 8
    rfl C17_enc_goal C17_proper C17_no_run
theorem C17_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C17_f x) :
    11 ≤ C.size := mono_lower C17_f 10 C17_no_small C hmono hev
theorem C18_patternScore_eq (masks : List Nat) :
    C18_patternScore masks = C18_rankPool.any (fastEntry (compactGoal 8 8) 4 C18_coords masks) := by
  unfold C18_patternScore
  split <;> rfl
theorem C18_patternScr_eq (s : Nat) (ws : List Nat) :
    C18_patternScr s ws = fastScr (compactGoal 8 8) s C18_coords 4 C18_rankPool ws := by
  unfold C18_patternScr fastScr
  split
  · rw [C18_patternScore_eq]
  · rfl
theorem C18_nonconstant : ∃ x y : Fin 7 → Bool, C18_f x ≠ C18_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C18_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C18_ori ws) := literalRouteOrient_run h C18_literalRoutes C18_good
theorem C18_checked : ∀ s ≤ 10, ∀ j < C18_N s, C18_Z s j = true := by
  apply certFlat_sound
  change span C18_F 391 0 = true
  exact (span_join (span_join C18_b0 C18_b1) (span_join C18_b2 C18_b3))
theorem C18_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C18_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C18_S) (N := C18_N) (idx := C18_idx) (ori := C18_ori)
    (early := C18_patternScr) (score := C18_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C18_patternScr_eq) (score_no_of_fastScr_eq C18_patternScr_eq)
    C18_ori_run C18_checked (by decide) (by decide) C18_initial_perm
theorem C18_no_small : ¬ HasMonoSize 7 C18_f 10 :=
  encoded_compact_exclusion C18_f C18_nonconstant 10 C18_rows C18_xs 8 8
    rfl C18_enc_goal C18_proper C18_no_run
theorem C18_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C18_f x) :
    11 ≤ C.size := mono_lower C18_f 10 C18_no_small C hmono hev
theorem C19_patternScore_eq (masks : List Nat) :
    C19_patternScore masks = C19_rankPool.any (fastEntry (compactGoal 7 8) 4 C19_coords masks) := by
  unfold C19_patternScore
  split <;> rfl
theorem C19_patternScr_eq (s : Nat) (ws : List Nat) :
    C19_patternScr s ws = fastScr (compactGoal 7 8) s C19_coords 4 C19_rankPool ws := by
  unfold C19_patternScr fastScr
  split
  · rw [C19_patternScore_eq]
  · rfl
theorem C19_nonconstant : ∃ x y : Fin 7 → Bool, C19_f x ≠ C19_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C19_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C19_ori ws) := literalRouteOrient_run h C19_literalRoutes C19_good
theorem C19_checked : ∀ s ≤ 10, ∀ j < C19_N s, C19_Z s j = true := by
  apply certFlat_sound
  change span C19_F 798 0 = true
  exact (span_join (span_join C19_b0 (span_join C19_b1 C19_b2)) (span_join (span_join C19_b3 C19_b4) (span_join C19_b5 C19_b6)))
theorem C19_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C19_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C19_S) (N := C19_N) (idx := C19_idx) (ori := C19_ori)
    (early := C19_patternScr) (score := C19_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C19_patternScr_eq) (score_no_of_fastScr_eq C19_patternScr_eq)
    C19_ori_run C19_checked (by decide) (by decide) C19_initial_perm
theorem C19_no_small : ¬ HasMonoSize 7 C19_f 10 :=
  encoded_compact_exclusion C19_f C19_nonconstant 10 C19_rows C19_xs 7 8
    rfl C19_enc_goal C19_proper C19_no_run
theorem C19_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C19_f x) :
    11 ≤ C.size := mono_lower C19_f 10 C19_no_small C hmono hev
theorem C20_patternScore_eq (masks : List Nat) :
    C20_patternScore masks = C20_rankPool.any (fastEntry (compactGoal 7 8) 4 C20_coords masks) := by
  unfold C20_patternScore
  split <;> rfl
theorem C20_patternScr_eq (s : Nat) (ws : List Nat) :
    C20_patternScr s ws = fastScr (compactGoal 7 8) s C20_coords 4 C20_rankPool ws := by
  unfold C20_patternScr fastScr
  split
  · rw [C20_patternScore_eq]
  · rfl
theorem C20_nonconstant : ∃ x y : Fin 7 → Bool, C20_f x ≠ C20_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C20_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C20_ori ws) := literalRouteOrient_run h C20_literalRoutes C20_good
theorem C20_checked : ∀ s ≤ 10, ∀ j < C20_N s, C20_Z s j = true := by
  apply certFlat_sound
  change span C20_F 1499 0 = true
  exact (span_join (span_join (span_join C20_b0 (span_join C20_b1 C20_b2)) (span_join C20_b3 (span_join C20_b4 C20_b5))) (span_join (span_join C20_b6 (span_join C20_b7 C20_b8)) (span_join C20_b9 (span_join C20_b10 C20_b11))))
theorem C20_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C20_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C20_S) (N := C20_N) (idx := C20_idx) (ori := C20_ori)
    (early := C20_patternScr) (score := C20_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C20_patternScr_eq) (score_no_of_fastScr_eq C20_patternScr_eq)
    C20_ori_run C20_checked (by decide) (by decide) C20_initial_perm
theorem C20_no_small : ¬ HasMonoSize 7 C20_f 10 :=
  encoded_compact_exclusion C20_f C20_nonconstant 10 C20_rows C20_xs 7 8
    rfl C20_enc_goal C20_proper C20_no_run
theorem C20_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C20_f x) :
    11 ≤ C.size := mono_lower C20_f 10 C20_no_small C hmono hev
theorem C21_patternScore_eq (masks : List Nat) :
    C21_patternScore masks = C21_rankPool.any (fastEntry (compactGoal 8 8) 4 C21_coords masks) := by
  unfold C21_patternScore
  split <;> rfl
theorem C21_patternScr_eq (s : Nat) (ws : List Nat) :
    C21_patternScr s ws = fastScr (compactGoal 8 8) s C21_coords 4 C21_rankPool ws := by
  unfold C21_patternScr fastScr
  split
  · rw [C21_patternScore_eq]
  · rfl
theorem C21_nonconstant : ∃ x y : Fin 7 → Bool, C21_f x ≠ C21_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C21_ori_run {s ws} (h : MonRun (compactGoal 8 8) s ws) :
    MonRun (compactGoal 8 8) s (C21_ori ws) := literalRouteOrient_run h C21_literalRoutes C21_good
theorem C21_checked : ∀ s ≤ 10, ∀ j < C21_N s, C21_Z s j = true := by
  apply certFlat_sound
  change span C21_F 1166 0 = true
  exact (span_join (span_join (span_join C21_b0 C21_b1) (span_join C21_b2 (span_join C21_b3 C21_b4))) (span_join (span_join C21_b5 C21_b6) (span_join C21_b7 (span_join C21_b8 C21_b9))))
theorem C21_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 8 8) s C21_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 8) (cover := compactCover 8 8)
    (S := C21_S) (N := C21_N) (idx := C21_idx) (ori := C21_ori)
    (early := C21_patternScr) (score := C21_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C21_patternScr_eq) (score_no_of_fastScr_eq C21_patternScr_eq)
    C21_ori_run C21_checked (by decide) (by decide) C21_initial_perm
theorem C21_no_small : ¬ HasMonoSize 7 C21_f 10 :=
  encoded_compact_exclusion C21_f C21_nonconstant 10 C21_rows C21_xs 8 8
    rfl C21_enc_goal C21_proper C21_no_run
theorem C21_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C21_f x) :
    11 ≤ C.size := mono_lower C21_f 10 C21_no_small C hmono hev
theorem C22_patternScore_eq (masks : List Nat) :
    C22_patternScore masks = C22_rankPool.any (fastEntry (compactGoal 6 8) 4 C22_coords masks) := by
  unfold C22_patternScore
  split <;> rfl
theorem C22_patternScr_eq (s : Nat) (ws : List Nat) :
    C22_patternScr s ws = fastScr (compactGoal 6 8) s C22_coords 4 C22_rankPool ws := by
  unfold C22_patternScr fastScr
  split
  · rw [C22_patternScore_eq]
  · rfl
theorem C22_nonconstant : ∃ x y : Fin 7 → Bool, C22_f x ≠ C22_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C22_ori_run {s ws} (h : MonRun (compactGoal 6 8) s ws) :
    MonRun (compactGoal 6 8) s (C22_ori ws) := literalRouteOrient_run h C22_literalRoutes C22_good
theorem C22_checked : ∀ s ≤ 9, ∀ j < C22_N s, C22_Z s j = true := by
  apply certFlat_sound
  change span C22_F 85 0 = true
  exact C22_b0
theorem C22_no_run : ∀ s ≤ 9, ¬ MonRun (compactGoal 6 8) s C22_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 6 8) (cover := compactCover 6 8)
    (S := C22_S) (N := C22_N) (idx := C22_idx) (ori := C22_ori)
    (early := C22_patternScr) (score := C22_patternScr) (cap := 9) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C22_patternScr_eq) (score_no_of_fastScr_eq C22_patternScr_eq)
    C22_ori_run C22_checked (by decide) (by decide) C22_initial_perm
theorem C22_no_small : ¬ HasMonoSize 7 C22_f 9 :=
  encoded_compact_exclusion C22_f C22_nonconstant 9 C22_rows C22_xs 6 8
    rfl C22_enc_goal C22_proper C22_no_run
theorem C22_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C22_f x) :
    10 ≤ C.size := mono_lower C22_f 9 C22_no_small C hmono hev
theorem C23_patternScore_eq (masks : List Nat) :
    C23_patternScore masks = C23_rankPool.any (fastEntry (compactGoal 7 8) 4 C23_coords masks) := by
  unfold C23_patternScore
  split <;> rfl
theorem C23_patternScr_eq (s : Nat) (ws : List Nat) :
    C23_patternScr s ws = fastScr (compactGoal 7 8) s C23_coords 4 C23_rankPool ws := by
  unfold C23_patternScr fastScr
  split
  · rw [C23_patternScore_eq]
  · rfl
theorem C23_nonconstant : ∃ x y : Fin 7 → Bool, C23_f x ≠ C23_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C23_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C23_ori ws) := literalRouteOrient_run h C23_literalRoutes C23_good
theorem C23_checked : ∀ s ≤ 10, ∀ j < C23_N s, C23_Z s j = true := by
  apply certFlat_sound
  change span C23_F 430 0 = true
  exact (span_join (span_join C23_b0 C23_b1) (span_join C23_b2 C23_b3))
theorem C23_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C23_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C23_S) (N := C23_N) (idx := C23_idx) (ori := C23_ori)
    (early := C23_patternScr) (score := C23_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C23_patternScr_eq) (score_no_of_fastScr_eq C23_patternScr_eq)
    C23_ori_run C23_checked (by decide) (by decide) C23_initial_perm
theorem C23_no_small : ¬ HasMonoSize 7 C23_f 10 :=
  encoded_compact_exclusion C23_f C23_nonconstant 10 C23_rows C23_xs 7 8
    rfl C23_enc_goal C23_proper C23_no_run
theorem C23_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C23_f x) :
    11 ≤ C.size := mono_lower C23_f 10 C23_no_small C hmono hev
theorem C24_patternScore_eq (masks : List Nat) :
    C24_patternScore masks = C24_rankPool.any (fastEntry (compactGoal 9 8) 5 C24_coords masks) := by
  unfold C24_patternScore
  split <;> rfl
theorem C24_patternScr_eq (s : Nat) (ws : List Nat) :
    C24_patternScr s ws = fastScr (compactGoal 9 8) s C24_coords 5 C24_rankPool ws := by
  unfold C24_patternScr fastScr
  split
  · rw [C24_patternScore_eq]
  · rfl
theorem C24_nonconstant : ∃ x y : Fin 7 → Bool, C24_f x ≠ C24_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C24_ori_run {s ws} (h : MonRun (compactGoal 9 8) s ws) :
    MonRun (compactGoal 9 8) s (C24_ori ws) := literalRouteOrient_run h C24_literalRoutes C24_good
theorem C24_checked : ∀ s ≤ 10, ∀ j < C24_N s, C24_Z s j = true := by
  apply certFlat_sound
  change span C24_F 248 0 = true
  exact (span_join C24_b0 C24_b1)
theorem C24_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 9 8) s C24_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 9 8) (cover := compactCover 9 8)
    (S := C24_S) (N := C24_N) (idx := C24_idx) (ori := C24_ori)
    (early := C24_patternScr) (score := C24_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C24_patternScr_eq) (score_no_of_fastScr_eq C24_patternScr_eq)
    C24_ori_run C24_checked (by decide) (by decide) C24_initial_perm
theorem C24_no_small : ¬ HasMonoSize 7 C24_f 10 :=
  encoded_compact_exclusion C24_f C24_nonconstant 10 C24_rows C24_xs 9 8
    rfl C24_enc_goal C24_proper C24_no_run
theorem C24_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C24_f x) :
    11 ≤ C.size := mono_lower C24_f 10 C24_no_small C hmono hev
theorem C25_patternScore_eq (masks : List Nat) :
    C25_patternScore masks = C25_rankPool.any (fastEntry (compactGoal 7 8) 4 C25_coords masks) := by
  unfold C25_patternScore
  split <;> rfl
theorem C25_patternScr_eq (s : Nat) (ws : List Nat) :
    C25_patternScr s ws = fastScr (compactGoal 7 8) s C25_coords 4 C25_rankPool ws := by
  unfold C25_patternScr fastScr
  split
  · rw [C25_patternScore_eq]
  · rfl
theorem C25_nonconstant : ∃ x y : Fin 7 → Bool, C25_f x ≠ C25_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C25_ori_run {s ws} (h : MonRun (compactGoal 7 8) s ws) :
    MonRun (compactGoal 7 8) s (C25_ori ws) := literalRouteOrient_run h C25_literalRoutes C25_good
theorem C25_checked : ∀ s ≤ 10, ∀ j < C25_N s, C25_Z s j = true := by
  apply certFlat_sound
  change span C25_F 255 0 = true
  exact (span_join C25_b0 C25_b1)
theorem C25_no_run : ∀ s ≤ 10, ¬ MonRun (compactGoal 7 8) s C25_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 8) (cover := compactCover 7 8)
    (S := C25_S) (N := C25_N) (idx := C25_idx) (ori := C25_ori)
    (early := C25_patternScr) (score := C25_patternScr) (cap := 10) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C25_patternScr_eq) (score_no_of_fastScr_eq C25_patternScr_eq)
    C25_ori_run C25_checked (by decide) (by decide) C25_initial_perm
theorem C25_no_small : ¬ HasMonoSize 7 C25_f 10 :=
  encoded_compact_exclusion C25_f C25_nonconstant 10 C25_rows C25_xs 7 8
    rfl C25_enc_goal C25_proper C25_no_run
theorem C25_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C25_f x) :
    11 ≤ C.size := mono_lower C25_f 10 C25_no_small C hmono hev
theorem C26_patternScore_eq (masks : List Nat) :
    C26_patternScore masks = C26_rankPool.any (fastEntry (compactGoal 9 9) 5 C26_coords masks) := by
  unfold C26_patternScore
  split <;> rfl
theorem C26_patternScr_eq (s : Nat) (ws : List Nat) :
    C26_patternScr s ws = fastScr (compactGoal 9 9) s C26_coords 5 C26_rankPool ws := by
  unfold C26_patternScr fastScr
  split
  · rw [C26_patternScore_eq]
  · rfl
theorem C26_nonconstant : ∃ x y : Fin 7 → Bool, C26_f x ≠ C26_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C26_ori_run {s ws} (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_ori ws) := literalRouteOrient_run h C26_literalRoutes C26_good
theorem C26_checked : ∀ s ≤ 11, ∀ j < C26_N s, C26_Z s j = true := by
  apply certFlat_sound
  change span C26_F 1067 0 = true
  exact (span_join (span_join (span_join C26_b0 C26_b1) (span_join C26_b2 C26_b3)) (span_join (span_join C26_b4 C26_b5) (span_join C26_b6 (span_join C26_b7 C26_b8))))
theorem C26_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 9 9) s C26_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 9 9) (cover := compactCover 9 9)
    (S := C26_S) (N := C26_N) (idx := C26_idx) (ori := C26_ori)
    (early := C26_patternScr) (score := C26_patternScr) (cap := 11) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C26_patternScr_eq) (score_no_of_fastScr_eq C26_patternScr_eq)
    C26_ori_run C26_checked (by decide) (by decide) C26_initial_perm
theorem C26_no_small : ¬ HasMonoSize 7 C26_f 11 :=
  encoded_compact_exclusion C26_f C26_nonconstant 11 C26_rows C26_xs 9 9
    rfl C26_enc_goal C26_proper C26_no_run
theorem C26_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C26_f x) :
    12 ≤ C.size := mono_lower C26_f 11 C26_no_small C hmono hev
theorem C27_patternScore_eq (masks : List Nat) :
    C27_patternScore masks = C27_rankPool.any (fastEntry (compactGoal 8 9) 5 C27_coords masks) := by
  unfold C27_patternScore
  split <;> rfl
theorem C27_patternScr_eq (s : Nat) (ws : List Nat) :
    C27_patternScr s ws = fastScr (compactGoal 8 9) s C27_coords 5 C27_rankPool ws := by
  unfold C27_patternScr fastScr
  split
  · rw [C27_patternScore_eq]
  · rfl
theorem C27_nonconstant : ∃ x y : Fin 7 → Bool, C27_f x ≠ C27_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C27_ori_run {s ws} (h : MonRun (compactGoal 8 9) s ws) :
    MonRun (compactGoal 8 9) s (C27_ori ws) := literalRouteOrient_run h C27_literalRoutes C27_good
theorem C27_checked : ∀ s ≤ 11, ∀ j < C27_N s, C27_Z s j = true := by
  apply certFlat_sound
  change span C27_F 3124 0 = true
  exact (span_join (span_join (span_join (span_join C27_b0 (span_join C27_b1 C27_b2)) (span_join C27_b3 (span_join C27_b4 C27_b5))) (span_join (span_join C27_b6 (span_join C27_b7 C27_b8)) (span_join C27_b9 (span_join C27_b10 C27_b11)))) (span_join (span_join (span_join C27_b12 (span_join C27_b13 C27_b14)) (span_join C27_b15 (span_join C27_b16 C27_b17))) (span_join (span_join C27_b18 (span_join C27_b19 C27_b20)) (span_join (span_join C27_b21 C27_b22) (span_join C27_b23 C27_b24)))))
theorem C27_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 8 9) s C27_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 9) (cover := compactCover 8 9)
    (S := C27_S) (N := C27_N) (idx := C27_idx) (ori := C27_ori)
    (early := C27_patternScr) (score := C27_patternScr) (cap := 11) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C27_patternScr_eq) (score_no_of_fastScr_eq C27_patternScr_eq)
    C27_ori_run C27_checked (by decide) (by decide) C27_initial_perm
theorem C27_no_small : ¬ HasMonoSize 7 C27_f 11 :=
  encoded_compact_exclusion C27_f C27_nonconstant 11 C27_rows C27_xs 8 9
    rfl C27_enc_goal C27_proper C27_no_run
theorem C27_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C27_f x) :
    12 ≤ C.size := mono_lower C27_f 11 C27_no_small C hmono hev
theorem C28_patternScore_eq (masks : List Nat) :
    C28_patternScore masks = C28_rankPool.any (fastEntry (compactGoal 7 9) 4 C28_coords masks) := by
  unfold C28_patternScore
  split <;> rfl
theorem C28_patternScr_eq (s : Nat) (ws : List Nat) :
    C28_patternScr s ws = fastScr (compactGoal 7 9) s C28_coords 4 C28_rankPool ws := by
  unfold C28_patternScr fastScr
  split
  · rw [C28_patternScore_eq]
  · rfl
theorem C28_nonconstant : ∃ x y : Fin 7 → Bool, C28_f x ≠ C28_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C28_ori_run {s ws} (h : MonRun (compactGoal 7 9) s ws) :
    MonRun (compactGoal 7 9) s (C28_ori ws) := literalRouteOrient_run h C28_literalRoutes C28_good
theorem C28_checked : ∀ s ≤ 11, ∀ j < C28_N s, C28_Z s j = true := by
  apply certFlat_sound
  change span C28_F 5742 0 = true
  exact (span_join (span_join (span_join (span_join (span_join C28_b0 C28_b1) (span_join C28_b2 (span_join C28_b3 C28_b4))) (span_join (span_join C28_b5 (span_join C28_b6 C28_b7)) (span_join C28_b8 (span_join C28_b9 C28_b10)))) (span_join (span_join (span_join C28_b11 C28_b12) (span_join C28_b13 (span_join C28_b14 C28_b15))) (span_join (span_join C28_b16 (span_join C28_b17 C28_b18)) (span_join C28_b19 (span_join C28_b20 C28_b21))))) (span_join (span_join (span_join (span_join C28_b22 C28_b23) (span_join C28_b24 (span_join C28_b25 C28_b26))) (span_join (span_join C28_b27 (span_join C28_b28 C28_b29)) (span_join C28_b30 (span_join C28_b31 C28_b32)))) (span_join (span_join (span_join C28_b33 (span_join C28_b34 C28_b35)) (span_join C28_b36 (span_join C28_b37 C28_b38))) (span_join (span_join C28_b39 (span_join C28_b40 C28_b41)) (span_join C28_b42 (span_join C28_b43 C28_b44))))))
theorem C28_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 7 9) s C28_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 9) (cover := compactCover 7 9)
    (S := C28_S) (N := C28_N) (idx := C28_idx) (ori := C28_ori)
    (early := C28_patternScr) (score := C28_patternScr) (cap := 11) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C28_patternScr_eq) (score_no_of_fastScr_eq C28_patternScr_eq)
    C28_ori_run C28_checked (by decide) (by decide) C28_initial_perm
theorem C28_no_small : ¬ HasMonoSize 7 C28_f 11 :=
  encoded_compact_exclusion C28_f C28_nonconstant 11 C28_rows C28_xs 7 9
    rfl C28_enc_goal C28_proper C28_no_run
theorem C28_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C28_f x) :
    12 ≤ C.size := mono_lower C28_f 11 C28_no_small C hmono hev
theorem C29_patternScore_eq (masks : List Nat) :
    C29_patternScore masks = C29_rankPool.any (fastEntry (compactGoal 7 9) 4 C29_coords masks) := by
  unfold C29_patternScore
  split <;> rfl
theorem C29_patternScr_eq (s : Nat) (ws : List Nat) :
    C29_patternScr s ws = fastScr (compactGoal 7 9) s C29_coords 4 C29_rankPool ws := by
  unfold C29_patternScr fastScr
  split
  · rw [C29_patternScore_eq]
  · rfl
theorem C29_nonconstant : ∃ x y : Fin 7 → Bool, C29_f x ≠ C29_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C29_ori_run {s ws} (h : MonRun (compactGoal 7 9) s ws) :
    MonRun (compactGoal 7 9) s (C29_ori ws) := literalRouteOrient_run h C29_literalRoutes C29_good
theorem C29_checked : ∀ s ≤ 11, ∀ j < C29_N s, C29_Z s j = true := by
  apply certFlat_sound
  change span C29_F 2022 0 = true
  exact (span_join (span_join (span_join (span_join C29_b0 C29_b1) (span_join C29_b2 C29_b3)) (span_join (span_join C29_b4 C29_b5) (span_join C29_b6 C29_b7))) (span_join (span_join (span_join C29_b8 C29_b9) (span_join C29_b10 C29_b11)) (span_join (span_join C29_b12 C29_b13) (span_join C29_b14 C29_b15))))
theorem C29_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 7 9) s C29_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 7 9) (cover := compactCover 7 9)
    (S := C29_S) (N := C29_N) (idx := C29_idx) (ori := C29_ori)
    (early := C29_patternScr) (score := C29_patternScr) (cap := 11) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C29_patternScr_eq) (score_no_of_fastScr_eq C29_patternScr_eq)
    C29_ori_run C29_checked (by decide) (by decide) C29_initial_perm
theorem C29_no_small : ¬ HasMonoSize 7 C29_f 11 :=
  encoded_compact_exclusion C29_f C29_nonconstant 11 C29_rows C29_xs 7 9
    rfl C29_enc_goal C29_proper C29_no_run
theorem C29_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C29_f x) :
    12 ≤ C.size := mono_lower C29_f 11 C29_no_small C hmono hev
theorem C30_patternScore_eq (masks : List Nat) :
    C30_patternScore masks = C30_rankPool.any (fastEntry (compactGoal 8 9) 5 C30_coords masks) := by
  unfold C30_patternScore
  split <;> rfl
theorem C30_patternScr_eq (s : Nat) (ws : List Nat) :
    C30_patternScr s ws = fastScr (compactGoal 8 9) s C30_coords 5 C30_rankPool ws := by
  unfold C30_patternScr fastScr
  split
  · rw [C30_patternScore_eq]
  · rfl
theorem C30_nonconstant : ∃ x y : Fin 7 → Bool, C30_f x ≠ C30_f y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩
theorem C30_ori_run {s ws} (h : MonRun (compactGoal 8 9) s ws) :
    MonRun (compactGoal 8 9) s (C30_ori ws) := literalRouteOrient_run h C30_literalRoutes C30_good
theorem C30_checked : ∀ s ≤ 11, ∀ j < C30_N s, C30_Z s j = true := by
  apply certFlat_sound
  change span C30_F 5310 0 = true
  exact (span_join (span_join (span_join (span_join (span_join C30_b0 C30_b1) (span_join C30_b2 (span_join C30_b3 C30_b4))) (span_join (span_join C30_b5 C30_b6) (span_join C30_b7 (span_join C30_b8 C30_b9)))) (span_join (span_join (span_join C30_b10 C30_b11) (span_join C30_b12 (span_join C30_b13 C30_b14))) (span_join (span_join C30_b15 (span_join C30_b16 C30_b17)) (span_join C30_b18 (span_join C30_b19 C30_b20))))) (span_join (span_join (span_join (span_join C30_b21 C30_b22) (span_join C30_b23 (span_join C30_b24 C30_b25))) (span_join (span_join C30_b26 C30_b27) (span_join C30_b28 (span_join C30_b29 C30_b30)))) (span_join (span_join (span_join C30_b31 C30_b32) (span_join C30_b33 (span_join C30_b34 C30_b35))) (span_join (span_join C30_b36 (span_join C30_b37 C30_b38)) (span_join C30_b39 (span_join C30_b40 C30_b41))))))
theorem C30_no_run : ∀ s ≤ 11, ¬ MonRun (compactGoal 8 9) s C30_xs := by
  exact noRun_from_barEarlyScore (y := compactGoal 8 9) (cover := compactCover 8 9)
    (S := C30_S) (N := C30_N) (idx := C30_idx) (ori := C30_ori)
    (early := C30_patternScr) (score := C30_patternScr) (cap := 11) (i := 0)
    (fun h => compactCover_ok h)
    (score_no_of_fastScr_eq C30_patternScr_eq) (score_no_of_fastScr_eq C30_patternScr_eq)
    C30_ori_run C30_checked (by decide) (by decide) C30_initial_perm
theorem C30_no_small : ¬ HasMonoSize 7 C30_f 11 :=
  encoded_compact_exclusion C30_f C30_nonconstant 11 C30_rows C30_xs 8 9
    rfl C30_enc_goal C30_proper C30_no_run
theorem C30_lower (C : Circuit) (hmono : Monotone2 C)
    (hev : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = C30_f x) :
    12 ≤ C.size := mono_lower C30_f 11 C30_no_small C hmono hev
end PEqualNP.Outside.L_meta_984.Cert

theorem PEqualNP.Outside.L_meta_984 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) := by
  exact ⟨PEqualNP.Outside.L_meta_984.Cert.C0_lower, PEqualNP.Outside.L_meta_984.Cert.C1_lower, PEqualNP.Outside.L_meta_984.Cert.C2_lower, PEqualNP.Outside.L_meta_984.Cert.C3_lower, PEqualNP.Outside.L_meta_984.Cert.C4_lower, PEqualNP.Outside.L_meta_984.Cert.C5_lower, PEqualNP.Outside.L_meta_984.Cert.C6_lower, PEqualNP.Outside.L_meta_984.Cert.C7_lower, PEqualNP.Outside.L_meta_984.Cert.C8_lower, PEqualNP.Outside.L_meta_984.Cert.C9_lower, PEqualNP.Outside.L_meta_984.Cert.C10_lower, PEqualNP.Outside.L_meta_984.Cert.C11_lower, PEqualNP.Outside.L_meta_984.Cert.C12_lower, PEqualNP.Outside.L_meta_984.Cert.C13_lower, PEqualNP.Outside.L_meta_984.Cert.C14_lower, PEqualNP.Outside.L_meta_984.Cert.C15_lower, PEqualNP.Outside.L_meta_984.Cert.C16_lower, PEqualNP.Outside.L_meta_984.Cert.C17_lower, PEqualNP.Outside.L_meta_984.Cert.C18_lower, PEqualNP.Outside.L_meta_984.Cert.C19_lower, PEqualNP.Outside.L_meta_984.Cert.C20_lower, PEqualNP.Outside.L_meta_984.Cert.C21_lower, PEqualNP.Outside.L_meta_984.Cert.C22_lower, PEqualNP.Outside.L_meta_984.Cert.C23_lower, PEqualNP.Outside.L_meta_984.Cert.C24_lower, PEqualNP.Outside.L_meta_984.Cert.C25_lower, PEqualNP.Outside.L_meta_984.Cert.C26_lower, PEqualNP.Outside.L_meta_984.Cert.C27_lower, PEqualNP.Outside.L_meta_984.Cert.C28_lower, PEqualNP.Outside.L_meta_984.Cert.C29_lower, PEqualNP.Outside.L_meta_984.Cert.C30_lower⟩
