import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4334

open CircuitLowerBounds MetaComplexity

-- The preprocessing follows the checked L_meta_1004 compiler. As in L_meta_2902,
-- a repeated operand of a binary monotone gate is redirected to that operand.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => if j = k then (none, Stat.wire j) else (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => if j = k then (none, Stat.wire j) else (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with e | k
      · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
      · cases c <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases e <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · by_cases h : j = k
        · subst h
          simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with e | k
      · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
      · cases c <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · cases e <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      · by_cases h : j = k
        · subst h
          simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    rename_i j k
    by_cases h : j = k
    · simp [h] at hg
    · simp [h] at hg
      subst hg
      exact Or.inr ⟨Or.inl rfl, j, k, hv (.wire j) (by simp), hv (.wire k) (by simp), h, rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    rename_i j k
    by_cases h : j = k
    · simp [h] at hg
    · simp [h] at hg
      subst hg
      exact Or.inr ⟨Or.inr rfl, j, k, hv (.wire j) (by simp), hv (.wire k) (by simp), h, rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this


-- Removing a chosen raw gate inserts its value at the end of the input list.
-- Earlier gates skip that input. Later gates read it in place of the removed gate wire.
def moveGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem simulate (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h : ∀ i, w.getD (r i) false = v.getD i false)
    (next : ∀ i t, r i = w.length + t ↔ i = v.length + t) :
    ∀ i, (wiresFrom (gs.map (moveGate r)) w).getD (r i) false =
      (wiresFrom gs v).getD i false := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map (fun i => v.getD i false))
    have eg : (moveGate r g).op.eval ((moveGate r g).inputs.map (fun j => w.getD j false)) = b := by
      simp only [moveGate, List.map_map, Function.comp_def, h, b]
    change ∀ i, (wiresFrom (gs.map (moveGate r)) (w ++ [_])).getD (r i) false =
      (wiresFrom gs (v ++ [b])).getD i false
    rw [eg]
    apply ih
    · intro i
      have hn : r i = w.length ↔ i = v.length := by simpa using next i 0
      by_cases hi : i = v.length
      · rw [hn.mpr hi, hi]
        simp
      · rw [getD_snoc_ne _ _ _ _ (fun d => hi (hn.mp d)), getD_snoc_ne _ _ _ _ hi, h]
    · intro i t
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.add_assoc] using next i (1 + t)

def up (n i : ℕ) := if i < n then i else i + 1

def slot (n k i : ℕ) :=
  if i < n then i else if i < n + k then i + 1 else if i = n + k then n else i

theorem move_raw (n k : ℕ) (i : ℕ) :
    (up n i < n ↔ i < n) ∧ (slot n k i < n ↔ i < n) := by
  simp only [up, slot]
  split_ifs <;> omega

def withoutGate (n : ℕ) (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre.map (moveGate (up n)) ++ post.map (moveGate (slot n pre.length)), slot n pre.length out⟩

theorem without_eval (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (raw : ∀ j ∈ g.inputs, j < n) (b : Bool)
    (isBit : g.op.eval (g.inputs.map (fun j => (List.ofFn x).getD j false)) = b) :
    (withoutGate n pre post out).eval (List.ofFn x ++ [b]) =
      (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) := by
  let xs := List.ofFn x
  let V := wiresFrom pre xs
  let W := wiresFrom (pre.map (moveGate (up n))) (xs ++ [b])
  have lx : xs.length = n := by simp [xs]
  have lv : V.length = n + pre.length := by simp [V, length_wiresFrom, lx]
  have lw : W.length = n + pre.length + 1 := by
    simp [W, length_wiresFrom, lx]; omega
  have pref : ∀ i, W.getD (up n i) false = V.getD i false := by
    apply simulate
    · intro i
      by_cases hi : i < n
      · rw [show up n i = i by simp [up, hi], List.getD_append _ _ _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by simp [up, hi, lx]; omega),
          List.getD_eq_default _ _ (by omega)]
    · intro i t
      simp only [List.length_append, lx, List.length_cons, List.length_nil, up]
      split_ifs <;> omega
  have keep (gs : List Gate) (ws : List Bool) (j : ℕ) (h : j < ws.length) :
      (wiresFrom gs ws).getD j false = ws.getD j false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_start gs ws
    rw [ht, List.getD_append _ _ _ _ h]
  have bit : g.op.eval (g.inputs.map fun j => V.getD j false) = b := by
    rw [← isBit]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro j hj
    exact keep pre xs j (by rw [lx]; exact raw j hj)
  have same : ∀ i, W.getD (slot n pre.length i) false = (V ++ [b]).getD i false := by
    intro i
    by_cases h : i < n + pre.length
    · have eq : slot n pre.length i = up n i := by simp [slot, up, h]
      rw [eq, pref, List.getD_append _ _ _ _ (by omega)]
    · by_cases e : i = n + pre.length
      · have r : slot n pre.length i = n := by simp [slot, e]
        rw [r, ← lv] at *
        rw [e, getD_snoc_eq, show W.getD n false = (xs ++ [b]).getD n false from
          keep _ _ _ (by simp [lx]), ← lx, getD_snoc_eq]
      · have r : slot n pre.length i = i := by simp [slot, show ¬ i < n by omega, h, e]
        rw [r, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [lv]; omega)]
  have future : ∀ i t, slot n pre.length i = W.length + t ↔ i = (V ++ [b]).length + t := by
    intro i t
    simp only [slot, lw, lv, List.length_append, List.length_cons, List.length_nil]
    split_ifs <;> omega
  change (wiresFrom (_ ++ _) (xs ++ [b])).getD _ false = (wiresFrom (pre ++ g :: post) xs).getD _ false
  rw [wiresFrom_append, wiresFrom_append]
  change (wiresFrom (post.map (moveGate _)) W).getD _ false =
    (wiresFrom post (V ++ [g.op.eval (g.inputs.map (fun j => V.getD j false))])).getD _ false
  rw [bit]
  exact simulate _ post _ _ same future out

def Raw (n : ℕ) (g : Gate) : Prop := ∀ i ∈ g.inputs, i < n

def Priority (n : ℕ) (k : GateOp) (gs : List Gate) : Prop :=
  ∀ g ∈ gs, Raw n g → (k = .and ∨ g.op ≠ .and) ∧ (k ≠ .or ∨ g.op ≠ .not)

theorem select_priority {n : ℕ} {gs : List Gate} (cl : CleanL n gs) (ne : gs ≠ []) :
    ∃ g ∈ gs, Raw n g ∧ Priority n g.op gs := by
  by_cases ha : ∃ g ∈ gs, Raw n g ∧ g.op = .and
  · obtain ⟨g, hg, raw, op⟩ := ha
    exact ⟨g, hg, raw, fun _ _ _ => ⟨Or.inl op, Or.inl (by simp [op])⟩⟩
  have noAnd : ∀ g ∈ gs, Raw n g → g.op ≠ .and := fun g hg raw h => ha ⟨g,hg,raw,h⟩
  by_cases hn : ∃ g ∈ gs, Raw n g ∧ g.op = .not
  · obtain ⟨g, hg, raw, op⟩ := hn
    exact ⟨g, hg, raw, fun t ht r => ⟨Or.inr (noAnd t ht r), Or.inl (by simp [op])⟩⟩
  cases gs with
  | nil => contradiction
  | cons g gs =>
    have first := cl 0 g (by simp)
    have raw : Raw n g := by
      rcases first with ⟨_, j, hj, eq⟩ | ⟨_, j, k, hj, hk, _, eq⟩
      · simpa [Raw, eq] using hj
      · simpa [Raw, eq] using And.intro hj hk
    exact ⟨g, List.mem_cons_self, raw, fun t ht r =>
      ⟨Or.inr (noAnd t ht r), Or.inr (fun e => hn ⟨t,ht,r,e⟩)⟩⟩

theorem clean_fan {n : ℕ} {gs : List Gate} (cl : CleanL n gs) (out : ℕ) :
    FanInTwo ⟨gs,out⟩ := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hg
  rcases cl p g hp with ⟨op, j, hj, eq⟩ | ⟨op | op, j, k, hj, hk, _, eq⟩ <;> simp [eq, op]

theorem without_fan (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (fan : FanInTwo ⟨pre ++ g :: post, o⟩) : FanInTwo (withoutGate n pre post o) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    simpa only [moveGate, List.length_map] using fan s (List.mem_append_left _ hs)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    simpa only [moveGate, List.length_map] using fan s (List.mem_append_right _ (List.mem_cons_of_mem _ hs))

theorem without_priority (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (pr : Priority n g.op (pre ++ g :: post)) :
    Priority n g.op (withoutGate n pre post o).gates := by
  intro t ht raw
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact pr s (List.mem_append_left _ hs) (fun i hi =>
      (move_raw n pre.length i).1.mp (raw _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact pr s (List.mem_append_right _ (List.mem_cons_of_mem _ hs)) (fun i hi =>
      (move_raw n pre.length i).2.mp (raw _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))

theorem pick_inputs {n m : ℕ} {g : Gate} (shape : CleanGate m g) (raw : Raw n g) :
    ∃ a b : Fin n, (g.op = .not ∨ (g.op = .and ∨ g.op = .or) ∧ a ≠ b) ∧
      ∀ x : Fin n → Bool, g.op.eval (g.inputs.map (fun j => (List.ofFn x).getD j false)) =
        g.op.eval [x a, x b] := by
  rcases shape with ⟨op, j, _, eq⟩ | ⟨op, j, k, _, _, ne, eq⟩
  · let a : Fin n := ⟨j, raw j (by simp [eq])⟩
    refine ⟨a, a, Or.inl op, fun x => ?_⟩
    have hj : (List.ofFn x).getD j false = x a := by simp [a, List.getD_eq_getElem?_getD, a.isLt]
    simp only [eq, op, List.map_cons, List.map_nil, hj]
    rfl
  · let a : Fin n := ⟨j, raw j (by simp [eq])⟩
    let b : Fin n := ⟨k, raw k (by simp [eq])⟩
    refine ⟨a, b, Or.inr ⟨op, fun h => ne (congrArg Fin.val h)⟩, fun x => ?_⟩
    have hj : (List.ofFn x).getD j false = x a := by simp [a, List.getD_eq_getElem?_getD, a.isLt]
    have hk : (List.ofFn x).getD k false = x b := by simp [b, List.getD_eq_getElem?_getD, b.isLt]
    simp only [eq, List.map_cons, List.map_nil, hj, hk]

def rename (p : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (p ⟨i, h⟩).val else i

theorem rename_small (p : Fin n → Fin n) (i : ℕ) : rename p i < n ↔ i < n := by
  by_cases hi : i < n
  · simp [rename, hi, (p ⟨i, hi⟩).isLt]
  · simp [rename, hi]

theorem rename_internal (p : Fin n → Fin n) {i : ℕ} (hi : n ≤ i) : rename p i = i := by
  simp [rename, Nat.not_lt.mpr hi]

def mapGate (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename p)⟩

theorem raw_iff (p : Fin n → Fin n) (g : Gate) :
    (∀ i ∈ (mapGate p g).inputs, i < n) ↔ (∀ i ∈ g.inputs, i < n) := by
  simp only [mapGate, List.forall_mem_map, rename_small]

def mapCircuit (p : Fin n → Fin n) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate p), rename p C.output⟩

theorem map_fanin (p : Fin n → Fin n) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (mapCircuit p C) := by
  intro g hg
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
  simpa [mapGate] using h old hold

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem same_after_append {n : ℕ} (p : Fin n → Fin n) (old new : List Bool)
    (hlen : old.length = new.length) (hraw : n ≤ old.length)
    (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) (b : Bool) :
    ∀ i, (new ++ [b]).getD (rename p i) false = (old ++ [b]).getD i false := by
  intro i
  by_cases hi : i < old.length
  · have hnew : rename p i < new.length := by
      by_cases h : i < n
      · have hp := (rename_small p i).mpr h
        omega
      · rw [rename_internal p (Nat.le_of_not_gt h)]
        omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hnew,
      List.getElem?_append_left hi]
    simpa only [List.getD_eq_getElem?_getD] using hbit i
  · have hri := rename_internal p (by omega : n ≤ i)
    have hnew : new.length ≤ i := by omega
    rw [hri]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt hi),
      List.getElem?_append_right hnew, hlen]

theorem propagate {n : ℕ} (p : Fin n → Fin n) (gs : List Gate) (old new : List Bool)
    (hlen : old.length = new.length) (hraw : n ≤ old.length)
    (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) :
    ∀ i, ((gs.map (mapGate p)).foldl step new).getD (rename p i) false =
      (gs.foldl step old).getD i false := by
  induction gs generalizing old new with
  | nil => exact hbit
  | cons g gs ih =>
    change ∀ i, ((gs.map (mapGate p)).foldl step (step new (mapGate p g))).getD (rename p i) false =
      (gs.foldl step (step old g)).getD i false
    have eqb : (g.inputs.map (rename p)).map (fun i => new.getD i false) =
        g.inputs.map (fun i => old.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hbit i
    have hn : step new (mapGate p g) = new ++ [g.op.eval (g.inputs.map fun i => old.getD i false)] := by
      simp only [step, mapGate, eqb]
    rw [hn]
    exact ih _ _ (by simp [step, hlen]) (by simp [step]; omega)
      (same_after_append p old new hlen hraw hbit _)

theorem input_read {n : ℕ} (p : Fin n → Fin n) (x : Fin n → Bool) :
    ∀ i : ℕ, (List.ofFn x).getD (rename p i) false = (List.ofFn (x ∘ p)).getD i false := by
  intro i
  by_cases hi : i < n
  · simp [rename, hi, List.getD_eq_getElem?_getD, (p ⟨i, hi⟩).isLt]
  · simp [rename, hi, List.getD_eq_getElem?_getD]

theorem map_tail_eval {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (b : Bool) :
    (mapCircuit p C).eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ p) ++ [b]) := by
  have h := same_after_append p (List.ofFn (x ∘ p)) (List.ofFn x) (by simp) (by simp) (input_read p x) b
  exact propagate p C.gates (List.ofFn (x ∘ p) ++ [b]) (List.ofFn x ++ [b]) (by simp) (by simp) h C.output


def perms : Fin 12 → Fin 9 → Fin 9 :=
  ![
    ![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![0, 5, 8, 3, 4, 1, 7, 6, 2],
    ![1, 0, 5, 8, 6, 2, 4, 7, 3],
    ![1, 2, 3, 8, 6, 0, 7, 4, 5],
    ![2, 1, 0, 5, 7, 3, 6, 4, 8],
    ![2, 3, 8, 5, 7, 1, 4, 6, 0],
    ![3, 2, 1, 0, 4, 8, 7, 6, 5],
    ![3, 8, 5, 0, 4, 2, 6, 7, 1],
    ![5, 0, 1, 2, 7, 8, 4, 6, 3],
    ![5, 8, 3, 2, 7, 0, 6, 4, 1],
    ![8, 3, 2, 1, 6, 5, 4, 7, 0],
    ![8, 5, 0, 1, 6, 3, 7, 4, 2]]

def pairs : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
   (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]

def representatives : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (4, 6)]

def target (x : Fin 9 → Bool) : Bool := pairs.any fun (a, b) => x a && x b

theorem unary_orbit : ∀ a : Fin 9, ∃ p : Fin 12, perms p a ∈ ([0, 4] : List (Fin 9)) := by
  decide +kernel

theorem binary_orbit : ∀ a b : Fin 9, a ≠ b → ∃ p : Fin 12,
    (perms p a, perms p b) ∈ representatives ∨ (perms p b, perms p a) ∈ representatives := by
  decide +kernel

theorem permutation_injective : ∀ p : Fin 12, ∀ a b : Fin 9, perms p a = perms p b → a = b := by
  decide +kernel

def hasEdge (a b : Fin 9) : Bool := pairs.contains (a, b) || pairs.contains (b, a)

theorem preserves_edges_bool : ∀ p : Fin 12, ∀ a b : Fin 9,
    hasEdge a b = hasEdge (perms p a) (perms p b) := by
  decide +kernel

theorem preserves_edges (p : Fin 12) (a b : Fin 9) :
    ((a, b) ∈ pairs ∨ (b, a) ∈ pairs) ↔
    ((perms p a, perms p b) ∈ pairs ∨ (perms p b, perms p a) ∈ pairs) := by
  simpa [hasEdge, Bool.or_eq_true] using congrArg (· = true) (preserves_edges_bool p a b)

theorem target_invariant (p : Fin 12) (x : Fin 9 → Bool) :
    target (x ∘ perms p) = target x := by
  have surj : Function.Surjective (perms p) :=
    (Finite.injective_iff_surjective).mp (permutation_injective p)
  rw [Bool.eq_iff_iff]
  simp only [target, List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, h, hval⟩
    rcases (preserves_edges p a b).mp (Or.inl h) with hab | hba
    · exact ⟨(perms p a, perms p b), hab, hval⟩
    · exact ⟨(perms p b, perms p a), hba, by
        simpa only [Function.comp_apply, Bool.and_comm] using hval⟩
  · rintro ⟨⟨a, b⟩, h, hval⟩
    obtain ⟨a', e'a⟩ := surj a
    obtain ⟨b', e'b⟩ := surj b
    have hp : (perms p a', perms p b') ∈ pairs := by simpa only [e'a, e'b] using h
    rcases (preserves_edges p a' b').mpr (Or.inl hp) with hab | hba
    · exact ⟨(a', b'), hab, by simpa only [Function.comp_apply, e'a, e'b] using hval⟩
    · exact ⟨(b', a'), hba, by simpa only [Function.comp_apply, e'a, e'b, Bool.and_comm] using hval⟩


theorem seed_orbit {k : GateOp} {a b : Fin 9}
    (shape : k = .not ∨ (k = .and ∨ k = .or) ∧ a ≠ b) :
    ∃ (p : Fin 12) (u v : Fin 9),
      ((k = .not ∧ u ∈ ([0,4] : List (Fin 9))) ∨
        ((k = .and ∨ k = .or) ∧ (u,v) ∈ representatives)) ∧
      ∀ x : Fin 9 → Bool, k.eval [x u,x v] = k.eval [(x ∘ perms p) a, (x ∘ perms p) b] := by
  rcases shape with rfl | ⟨op, ne⟩
  · obtain ⟨p, hp⟩ := unary_orbit a
    exact ⟨p, perms p a, perms p b, Or.inl ⟨rfl,hp⟩, fun _ => rfl⟩
  · obtain ⟨p, h | h⟩ := binary_orbit a b ne
    · exact ⟨p, _, _, Or.inr ⟨op,h⟩, fun _ => rfl⟩
    · refine ⟨p, perms p b, perms p a, Or.inr ⟨op,h⟩, fun x => ?_⟩
      rcases op with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

theorem no_singleton : ∀ a : Fin 9, target (fun j => decide (j = a)) = false := by decide +kernel

theorem priority_seed {C : Circuit} (fan : FanInTwo C) (comp : circuitFun 9 C = target) :
    ∃ (D : Circuit) (k : GateOp) (u v : Fin 9), FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ((k = .not ∧ u ∈ ([0,4] : List (Fin 9))) ∨
        (k = .and ∨ k = .or) ∧ (u,v) ∈ representatives) ∧
      Priority 9 k D.gates ∧ ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [k.eval [x u, x v]]) = target x := by
  have nonconstant : ∃ x y : Fin 9 → Bool, target x ≠ target y :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨gs,o,cl,sz,eval⟩ := clean_of 9 target C.size nonconstant
    ⟨C, fan, le_rfl, fun x => congrFun comp x⟩
  have nonempty : gs ≠ [] := by
    rintro rfl
    by_cases hi : o < 9
    · let a : Fin 9 := ⟨o,hi⟩
      have h := eval (fun j => decide (j = a))
      rw [no_singleton] at h
      have pin {n : ℕ} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
        simp [List.getD_eq_getElem?_getD, i.isLt]
      change (List.ofFn (fun j => decide (j = a))).getD a.val false = false at h
      rw [pin] at h
      simp only [eq_self, decide_true] at h
      exact Bool.noConfusion h
    · have h := eval (fun _ => true)
      have no : (List.ofFn (fun _ : Fin 9 => true)).getD o false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      change (List.ofFn (fun _ : Fin 9 => true)).getD o false = true at h
      exact Bool.noConfusion (no.symm.trans h)
  obtain ⟨g,hg,raw,priority⟩ := select_priority cl nonempty
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
  obtain ⟨a,b,shape,gateBit⟩ := pick_inputs (cl j g hj) raw
  obtain ⟨pre,post,rfl⟩ := List.append_of_mem hg
  let B := withoutGate 9 pre post o
  have fanB : FanInTwo B := without_fan _ pre post g o (clean_fan cl o)
  have prB : Priority 9 g.op B.gates := without_priority _ pre post g o priority
  have bitB (x : Fin 9 → Bool) : B.eval (List.ofFn x ++ [g.op.eval [x a,x b]]) = target x :=
    (without_eval 9 pre post g o x raw _ (gateBit x)).trans (eval x)
  obtain ⟨p,u,v,rep,ep⟩ := seed_orbit shape
  refine ⟨mapCircuit (perms p) B, g.op, u, v, map_fanin _ B fanB, ?_, rep, ?_, ?_⟩
  · change (B.gates.map _).length + 1 ≤ C.size
    simpa [B, withoutGate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sz
  · intro h hh rh
    obtain ⟨old,hOld,rfl⟩ := List.mem_map.mp hh
    exact prB old hOld ((raw_iff _ old).mp rh)
  · intro x
    rw [map_tail_eval, ep, bitB, target_invariant]

end PEqualNP.Outside.L_meta_4334

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4334

theorem PEqualNP.Outside.L_meta_4334 :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.GateOp) (x7 : Fin (9 : ℕ)) (x8 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) ≤ x2.size ∧ (x6 = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x7 ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))] ∨ (x6 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (x7, x8) ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))]) ∧ (∀ x9 ∈ x5.gates, (∀ x11 ∈ x9.inputs, x11 < (9 : ℕ)) → (x6 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (x6 ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not)) ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x9 ++ [x6.eval [x9 x7, x9 x8]]) = x1 x9 := by
  dsimp only
  intro C h hC
  have eqTarget (x : Fin 9 → Bool) : target x = (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
    simp [target, pairs, Bool.or_assoc]
  have heq : circuitFun 9 C = target := by funext x; exact (congrFun hC x).trans (eqTarget x).symm
  obtain ⟨D,k,u,v,fan,sz,rep,pr,ev⟩ := priority_seed h heq
  exact ⟨D,k,u,v,fan,sz,rep,pr,fun x => (ev x).trans (eqTarget x)⟩
