import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4308_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

structure BGate where
  a : ℕ
  pa : Bool
  b : ℕ
  pb : Bool

def BGate.eval (w : List Bool) (g : BGate) : Bool :=
  (xor (w.getD g.a false) g.pa) && (xor (w.getD g.b false) g.pb)

def bwires (gs : List BGate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.eval w]) w

theorem bwires_append (gs gs' : List BGate) (w : List Bool) :
    bwires (gs ++ gs') w = bwires gs' (bwires gs w) := by
  simp [bwires, List.foldl_append]

theorem bwires_start (gs : List BGate) : ∀ w : List Bool,
    ∃ t : List Bool, bwires gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [bwires], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.eval w])
    refine ⟨g.eval w :: t, ?_, by simp [hl]⟩
    have : bwires (g :: gs) w = bwires gs (w ++ [g.eval w]) := rfl
    rw [this, ht]; simp

theorem length_bwires (gs : List BGate) (w : List Bool) :
    (bwires gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := bwires_start gs w
  rw [ht]; simp [hl]

theorem getD_bwires (gs : List BGate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (bwires gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := bwires_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def CleanB (n : ℕ) (gs : List BGate) : Prop :=
  ∀ (p : ℕ) (g : BGate), gs[p]? = some g → g.a < n + p ∧ g.b < n + p ∧ g.a ≠ g.b

def HasBSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ (gs : List BGate) (o : ℕ) (po : Bool),
    CleanB n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, xor ((bwires gs (List.ofFn x)).getD o false) po = f x

inductive BStat : Type
  | const (c : Bool)
  | wire (j : ℕ) (p : Bool)

def BStat.val (w : List Bool) : BStat → Bool
  | BStat.const c => c
  | BStat.wire j p => xor (w.getD j false) p

def BStat.Valid (m : ℕ) : BStat → Prop
  | BStat.const _ => True
  | BStat.wire j _ => j < m

theorem BStat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : BStat, s.Valid m → s.Valid m'
  | BStat.const _, _ => trivial
  | BStat.wire _ _, hj => lt_of_lt_of_le hj h

theorem BStat.val_append (w t : List Bool) : ∀ s : BStat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | BStat.const _, _ => rfl
  | BStat.wire j p, hj => by
    simp only [BStat.val]
    exact congrArg (fun b => xor b p) (List.getD_append w t false j hj)

def negBStat : BStat → BStat
  | BStat.const c => BStat.const (!c)
  | BStat.wire j p => BStat.wire j (!p)

theorem negBStat_valid {m : ℕ} : ∀ s : BStat, s.Valid m → (negBStat s).Valid m
  | BStat.const _, h => h
  | BStat.wire _ _, h => h

theorem negBStat_val (w : List Bool) : ∀ s : BStat, (negBStat s).val w = !(s.val w)
  | BStat.const c => by cases c <;> rfl
  | BStat.wire j p => by
    simp only [negBStat, BStat.val]
    cases w.getD j false <;> cases p <;> rfl

def simpBAnd (m : ℕ) : BStat → BStat → Option BGate × BStat
  | BStat.const c, s2 => (none, if c then s2 else BStat.const false)
  | BStat.wire j pj, BStat.const c => (none, if c then BStat.wire j pj else BStat.const false)
  | BStat.wire j pj, BStat.wire k pk =>
    if j = k then (none, if pj = pk then BStat.wire j pj else BStat.const false)
    else (some ⟨j, pj, k, pk⟩, BStat.wire m false)

def simpBOr (m : ℕ) (s1 s2 : BStat) : Option BGate × BStat :=
  let r := simpBAnd m (negBStat s1) (negBStat s2)
  (r.1, negBStat r.2)

def simpGate (op : GateOp) (m : ℕ) (ins : List BStat) : Option BGate × BStat :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (none, BStat.const true)
    | [s1] => (none, s1)
    | [s1, s2] => simpBAnd m s1 s2
    | _ => (none, BStat.const false)
  | GateOp.or =>
    match ins with
    | [] => (none, BStat.const false)
    | [s1] => (none, s1)
    | [s1, s2] => simpBOr m s1 s2
    | _ => (none, BStat.const false)
  | GateOp.not =>
    match ins with
    | [] => (none, BStat.const true)
    | s1 :: _ => (none, negBStat s1)
  | _ => (none, BStat.const false)

theorem simpBAnd_clean (m : ℕ) (s1 s2 : BStat) (h1 : s1.Valid m) (h2 : s2.Valid m) :
    ∀ g ∈ (simpBAnd m s1 s2).1, g.a < m ∧ g.b < m ∧ g.a ≠ g.b := by
  intro g hg
  cases s1 with
  | const c => simp [simpBAnd] at hg
  | wire j pj =>
    cases s2 with
    | const c => simp [simpBAnd] at hg
    | wire k pk =>
      simp only [simpBAnd] at hg
      split at hg
      · simp at hg
      · simp only [Option.mem_def, Option.some.injEq] at hg
        subst hg
        exact ⟨h1, h2, by assumption⟩

theorem simpBAnd_sound (w : List Bool) (s1 s2 : BStat)
    (h1 : s1.Valid w.length) (h2 : s2.Valid w.length) :
    (simpBAnd w.length s1 s2).2.Valid (w.length + (simpBAnd w.length s1 s2).1.toList.length) ∧
    (simpBAnd w.length s1 s2).2.val (bwires (simpBAnd w.length s1 s2).1.toList w) =
      (s1.val w && s2.val w) := by
  cases s1 with
  | const c =>
    cases c
    · simp [simpBAnd, BStat.val, bwires]; trivial
    · simp [simpBAnd, BStat.val, bwires]; exact h2
  | wire j pj =>
    cases s2 with
    | const c =>
      cases c
      · simp [simpBAnd, BStat.val, bwires]; trivial
      · simp [simpBAnd, BStat.val, bwires]; exact h1
    | wire k pk =>
      simp only [simpBAnd]
      split
      · rename_i hjk
        subst hjk
        by_cases hp : pj = pk
        · subst hp
          simp only [ite_true, Option.toList_none, List.length_nil, Nat.add_zero, bwires, List.foldl_nil]
          exact ⟨h1, by simp [BStat.val]⟩
        · simp only [hp, ite_false, Option.toList_none, List.length_nil, Nat.add_zero, bwires, List.foldl_nil]
          refine ⟨trivial, ?_⟩
          cases hwg : w.getD j false <;> cases pj <;> cases pk <;> simp_all [BStat.val]
      · simp only [Option.toList_some, List.length_singleton, BStat.Valid, lt_add_iff_pos_right, zero_lt_one,
          true_and, bwires, List.foldl_cons, List.foldl_nil, BStat.val, BGate.eval]
        rw [getD_snoc_eq, Bool.xor_false]

theorem simpBOr_clean (m : ℕ) (s1 s2 : BStat) (h1 : s1.Valid m) (h2 : s2.Valid m) :
    ∀ g ∈ (simpBOr m s1 s2).1, g.a < m ∧ g.b < m ∧ g.a ≠ g.b := by
  intro g hg
  exact simpBAnd_clean m (negBStat s1) (negBStat s2) (negBStat_valid _ h1) (negBStat_valid _ h2) g hg

theorem simpBOr_sound (w : List Bool) (s1 s2 : BStat)
    (h1 : s1.Valid w.length) (h2 : s2.Valid w.length) :
    (simpBOr w.length s1 s2).2.Valid (w.length + (simpBOr w.length s1 s2).1.toList.length) ∧
    (simpBOr w.length s1 s2).2.val (bwires (simpBOr w.length s1 s2).1.toList w) =
      (s1.val w || s2.val w) := by
  have hs := simpBAnd_sound w (negBStat s1) (negBStat s2) (negBStat_valid _ h1) (negBStat_valid _ h2)
  refine ⟨negBStat_valid _ hs.1, ?_⟩
  change (negBStat (simpBAnd w.length (negBStat s1) (negBStat s2)).2).val
    (bwires (simpBAnd w.length (negBStat s1) (negBStat s2)).1.toList w) = _
  rw [negBStat_val, hs.2, negBStat_val, negBStat_val]
  cases s1.val w <;> cases s2.val w <;> rfl

theorem simpGate_clean (op : GateOp) (m : ℕ) (ins : List BStat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simpGate op m ins).1, g.a < m ∧ g.b < m ∧ g.a ≠ g.b := by
  intro g hg
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, l⟩⟩⟩ <;> simp [simpGate] at hg
    exact simpBAnd_clean m s1 s2 (hv _ List.mem_cons_self)
      (hv _ (List.mem_cons_of_mem _ List.mem_cons_self)) g hg
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, l⟩⟩⟩ <;> simp [simpGate] at hg
    exact simpBOr_clean m s1 s2 (hv _ List.mem_cons_self)
      (hv _ (List.mem_cons_of_mem _ List.mem_cons_self)) g hg
  | not =>
    rcases ins with _ | ⟨s1, l⟩ <;> simp [simpGate] at hg
  | mod _ => simp [simpGate] at hg
  | maj => simp [simpGate] at hg

theorem simpGate_not_none (m : ℕ) (ins : List BStat) :
    (simpGate GateOp.not m ins).1 = none := by
  cases ins <;> rfl

theorem simpGate_sound (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (w : List Bool) (ins : List BStat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    (simpGate op w.length ins).2.Valid (w.length + (simpGate op w.length ins).1.toList.length) ∧
    (simpGate op w.length ins).2.val (bwires (simpGate op w.length ins).1.toList w) =
      op.eval (ins.map (BStat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, l⟩⟩⟩
    · simp [simpGate, BStat.Valid, BStat.val, GateOp.eval]
    · simp [simpGate, BStat.val, GateOp.eval, bwires, hv _ List.mem_cons_self]
    · simpa [simpGate, GateOp.eval] using simpBAnd_sound w s1 s2
        (hv _ List.mem_cons_self) (hv _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, l⟩⟩⟩
    · simp [simpGate, BStat.Valid, BStat.val, GateOp.eval]
    · simp [simpGate, BStat.val, GateOp.eval, bwires, hv _ List.mem_cons_self]
    · simpa [simpGate, GateOp.eval] using simpBOr_sound w s1 s2
        (hv _ List.mem_cons_self) (hv _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · simp at hlen
  · rcases ins with _ | ⟨s1, l⟩
    · simp [simpGate, BStat.Valid, BStat.val, GateOp.eval]
    · simp only [simpGate, BStat.Valid, BStat.val, GateOp.eval, bwires]
      exact ⟨negBStat_valid _ (hv _ List.mem_cons_self), by
        simpa [BStat.val] using negBStat_val w s1⟩

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def elimCStep (n : ℕ) (acc : List BStat × List BGate) (g : Gate) : List BStat × List BGate :=
  let ins := g.inputs.map fun i => acc.1.getD i (BStat.const false)
  let r := simpGate g.op (n + acc.2.length) ins
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimC (n : ℕ) (gs : List Gate) (acc : List BStat × List BGate) : List BStat × List BGate :=
  gs.foldl (elimCStep n) acc

def InvC (n : ℕ) (y : List Bool) (w : List Bool) (acc : List BStat × List BGate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (BStat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (BStat.const false)).val (bwires acc.2 y) = w.getD i false

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem inv_elimC (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      InvC n y w acc → InvC n y (wiresFrom gs w) (elimC n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimCStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := bwires acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_bwires, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (BStat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simpGate_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simpGate g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (BStat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : bwires (acc.2 ++ r.1.toList) y = bwires r.1.toList w' := by
      rw [bwires_append]
    obtain ⟨t, ht, _⟩ := bwires_start r.1.toList w'
    refine ⟨by simp [elimCStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (BStat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (BStat.const false)).val (bwires (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨BStat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, BStat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem clean_elimC (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      InvC n y w acc → CleanB n acc.2 → CleanB n (elimC n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : InvC n y (wiresFrom [g] w) (elimCStep n acc g) :=
      inv_elimC n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimCStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simpGate g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (BStat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simpGate_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

theorem elimC_countP (n : ℕ) (gs : List Gate) : ∀ acc : List BStat × List BGate,
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (elimC n gs acc).2.length ≤ acc.2.length + List.countP (fun g => !g.op.eval [Bool.false]) gs := by
  induction gs with
  | nil => intro acc _; simp [elimC]
  | cons g gs ih =>
    intro acc hok
    have ih' := ih (elimCStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    have h1 : elimC n (g :: gs) acc = elimC n gs (elimCStep n acc g) := rfl
    rw [h1]
    rcases (hok g List.mem_cons_self).1 with hop | hop | hop
    · have hnot : (!g.op.eval [Bool.false]) = true := by rw [hop]; rfl
      simp only [List.countP_cons, hnot, ↓reduceIte]
      have h2 : (elimCStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimCStep, List.length_append]
        have := toList_length_le (simpGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (BStat.const false))).1
        omega
      omega
    · have hnot : (!g.op.eval [Bool.false]) = true := by rw [hop]; rfl
      simp only [List.countP_cons, hnot, ↓reduceIte]
      have h2 : (elimCStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimCStep, List.length_append]
        have := toList_length_le (simpGate g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (BStat.const false))).1
        omega
      omega
    · simp only [Set.mem_singleton_iff] at hop
      have hnot : (!g.op.eval [Bool.false]) = false := by rw [hop]; rfl
      simp only [List.countP_cons, hnot, Bool.false_eq_true, ↓reduceIte]
      have h2 : (elimCStep n acc g).2.length = acc.2.length := by
        simp [elimCStep, hop, simpGate_not_none]
      omega

def idBStats (n : ℕ) : List BStat := List.ofFn (fun i : Fin n => BStat.wire i false)

theorem invC_id (n : ℕ) (y : List Bool) (hy : y.length = n) :
    InvC n y y (idBStats n, []) := by
  refine ⟨by simp [idBStats, hy], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idBStats, hlt, BStat.Valid, BStat.val, bwires]
  · rw [List.getD_eq_default _ _ (by simp [idBStats]; omega),
      List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial, rfl⟩

theorem convert_circuit (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ (gs : List BGate) (st : BStat),
      CleanB n gs ∧
      gs.length ≤ List.countP (fun g => !g.op.eval [Bool.false]) C.gates ∧
      st.Valid (n + gs.length) ∧
      ∀ y : List Bool, y.length = n → st.val (bwires gs y) = C.eval y := by
  set acc := elimC n C.gates (idBStats n, []) with hacc
  refine ⟨acc.2, acc.1.getD C.output (BStat.const false), ?_, ?_, ?_, ?_⟩
  · exact clean_elimC n (List.replicate n false) (by simp) C.gates _ _ hfan
      (invC_id n _ (by simp)) (by intro p g hp; simp at hp)
  · have := elimC_countP n C.gates (idBStats n, []) hfan
    rw [← hacc] at this
    simpa using this
  · exact ((inv_elimC n (List.replicate n false) (by simp) C.gates _ _ hfan
      (invC_id n _ (by simp))).2 C.output).1
  · intro y hy
    exact ((inv_elimC n y hy C.gates _ _ hfan (invC_id n y hy)).2 C.output).2

def elimBStep (m : ℕ) (acc : List BStat × List BGate) (g : BGate) : List BStat × List BGate :=
  let s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false)
  let s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false)
  let r := simpBAnd (m + acc.2.length) s1 s2
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimB (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate) : List BStat × List BGate :=
  gs.foldl (elimBStep m) acc

theorem elimB_cons (m : ℕ) (g : BGate) (gs : List BGate) (acc : List BStat × List BGate) :
    elimB m (g :: gs) acc = elimB m gs (elimBStep m acc g) := rfl

theorem elimB_append (m : ℕ) (pre post : List BGate) (acc : List BStat × List BGate) :
    elimB m (pre ++ post) acc = elimB m post (elimB m pre acc) := by
  simp [elimB, List.foldl_append]

theorem elimB_fst_len (m : ℕ) (gs : List BGate) : ∀ acc : List BStat × List BGate,
    (elimB m gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elimB_cons, ih]
    simp only [elimBStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elimB_fst_getD (m k : ℕ) (d : BStat) (gs : List BGate) : ∀ acc : List BStat × List BGate,
    k < acc.1.length → (elimB m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elimB_cons, ih (elimBStep m acc g) (by simp [elimBStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

def InvB (m : ℕ) (y' : List Bool) (w : List Bool) (acc : List BStat × List BGate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (BStat.const false)).Valid (m + acc.2.length) ∧
    (acc.1.getD i (BStat.const false)).val (bwires acc.2 y') = w.getD i false

theorem inv_elimB (m : ℕ) (y' : List Bool) (hy' : y'.length = m) (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate), InvB m y' w acc →
      InvB m y' (bwires gs w) (elimB m gs acc) := by
  induction gs with
  | nil => intro w acc h; exact h
  | cons g gs ih =>
    intro w acc h
    apply ih (w ++ [g.eval w]) (elimBStep m acc g)
    obtain ⟨hl, hi⟩ := h
    set w' := bwires acc.2 y' with hw'
    have lw' : w'.length = m + acc.2.length := by rw [hw', length_bwires, hy']
    set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
      else acc.1.getD g.a (BStat.const false) with hs1
    set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
      else acc.1.getD g.b (BStat.const false) with hs2
    have hv1 : s1.Valid w'.length := by
      rw [lw']
      cases hpa : g.pa
      · rw [hs1, hpa]; exact (hi g.a).1
      · rw [hs1, hpa]; exact negBStat_valid _ (hi g.a).1
    have hv2 : s2.Valid w'.length := by
      rw [lw']
      cases hpb : g.pb
      · rw [hs2, hpb]; exact (hi g.b).1
      · rw [hs2, hpb]; exact negBStat_valid _ (hi g.b).1
    have hs := simpBAnd_sound w' s1 s2 hv1 hv2
    rw [lw'] at hs
    set r := simpBAnd (m + acc.2.length) s1 s2 with hr
    have hval1 : s1.val w' = xor (w.getD g.a false) g.pa := by
      cases hpa : g.pa
      · rw [hs1, hpa]; simpa using (hi g.a).2
      · rw [hs1, hpa]; simpa [negBStat_val] using congrArg not (hi g.a).2
    have hval2 : s2.val w' = xor (w.getD g.b false) g.pb := by
      cases hpb : g.pb
      · rw [hs2, hpb]; simpa using (hi g.b).2
      · rw [hs2, hpb]; simpa [negBStat_val] using congrArg not (hi g.b).2
    have hnew : bwires (acc.2 ++ r.1.toList) y' = bwires r.1.toList w' := by
      rw [bwires_append]
    obtain ⟨t, ht, _⟩ := bwires_start r.1.toList w'
    refine ⟨by simp [elimBStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (BStat.const false)).Valid (m + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (BStat.const false)).val (bwires (acc.2 ++ r.1.toList) y') = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hval1, hval2]; rfl⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨BStat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, BStat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem clean_elimB (m : ℕ) (y' : List Bool) (hy' : y'.length = m) (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate), InvB m y' w acc →
      CleanB m acc.2 → CleanB m (elimB m gs acc).2 := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hinv hcl
    have hinv' : InvB m y' (bwires [g] w) (elimBStep m acc g) :=
      inv_elimB m y' hy' [g] w acc hinv
    refine ih _ (elimBStep m acc g) hinv' ?_
    intro p g' hp
    set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
      else acc.1.getD g.a (BStat.const false) with hs1
    set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
      else acc.1.getD g.b (BStat.const false) with hs2
    have hp' : (acc.2 ++ (simpBAnd (m + acc.2.length) s1 s2).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨_, hmem⟩ := toList_getElem? _ _ _ hp'
      have hv1 : s1.Valid (m + acc.2.length) := by
        cases hpa : g.pa
        · rw [hs1, hpa]; exact (hinv.2 g.a).1
        · rw [hs1, hpa]; exact negBStat_valid _ (hinv.2 g.a).1
      have hv2 : s2.Valid (m + acc.2.length) := by
        cases hpb : g.pb
        · rw [hs2, hpb]; exact (hinv.2 g.b).1
        · rw [hs2, hpb]; exact negBStat_valid _ (hinv.2 g.b).1
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simpBAnd_clean _ _ _ hv1 hv2 g' hmem

theorem elimB_len (m : ℕ) (gs : List BGate) : ∀ acc : List BStat × List BGate,
    (elimB m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimB]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimBStep m acc g)
    have h2 : (elimBStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimBStep, List.length_append]
      have := toList_length_le (simpBAnd (m + acc.2.length)
        (if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false))
        (if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false))).1
      omega
    rw [elimB_cons, List.length_cons]
    omega

def stepAcc (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate) (p : ℕ) :
    List BStat × List BGate :=
  elimB m (gs.take p) acc

def isDroppedAt (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧
    (elimBStep m (stepAcc m gs acc p) g).2.length = (stepAcc m gs acc p).2.length

theorem stepAcc_fst_len (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate) (p : ℕ)
    (hp : p ≤ gs.length) : (stepAcc m gs acc p).1.length = acc.1.length + p := by
  unfold stepAcc
  rw [elimB_fst_len, List.length_take_of_le hp]

theorem take_split {α : Type} : ∀ (p q : ℕ) (gs : List α), p ≤ q →
    gs.take q = gs.take p ++ (gs.drop p).take (q - p)
  | 0, _, _, _ => by simp
  | _ + 1, _, [], _ => by simp
  | p + 1, q, a :: t, hpq => by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, Nat.add_sub_add_right]
    congr 1
    exact take_split p q' t (by omega)

theorem take_succ_eq {α : Type} : ∀ (p : ℕ) (gs : List α) (g : α), gs[p]? = some g →
    gs.take (p + 1) = gs.take p ++ [g]
  | 0, _ :: _, g, h => by simp at h; simp [h]
  | p + 1, a :: t, g, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [List.take_succ_cons, take_succ_eq p t g h]
  | _, [], _, h => by simp at h

theorem stepAcc_getD_ge (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate)
    (p q k : ℕ) (hpq : p ≤ q) (hk : k < acc.1.length + min p gs.length) (d : BStat) :
    (stepAcc m gs acc q).1.getD k d = (stepAcc m gs acc p).1.getD k d := by
  unfold stepAcc
  rw [take_split p q gs hpq, elimB_append]
  apply elimB_fst_getD
  rw [elimB_fst_len, List.length_take]
  exact hk

theorem isDroppedAt_cons_zero (m : ℕ) (g : BGate) (gs : List BGate) (acc : List BStat × List BGate) :
    isDroppedAt m (g :: gs) acc 0 ↔
      (elimBStep m acc g).2.length = acc.2.length := by
  simp [isDroppedAt, stepAcc, elimB]

theorem isDroppedAt_cons_succ (m : ℕ) (g : BGate) (gs : List BGate)
    (acc : List BStat × List BGate) (p : ℕ) :
    isDroppedAt m (g :: gs) acc (p + 1) ↔
      isDroppedAt m gs (elimBStep m acc g) p := by
  simp [isDroppedAt, stepAcc, elimB_cons]

theorem dropped_le (m : ℕ) (gs : List BGate) :
    ∀ (acc : List BStat × List BGate) (D : Finset ℕ),
      (∀ p ∈ D, isDroppedAt m gs acc p) →
      (elimB m gs acc).2.length + D.card ≤ acc.2.length + gs.length := by
  induction gs with
  | nil =>
    intro acc D hD
    have hE : D = ∅ := by
      ext p
      simp only [Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨g, hg, _⟩ := hD p hp
      simp at hg
    subst hE
    simp [elimB]
  | cons g gs ih =>
    intro acc D hD
    let D' : Finset ℕ := (D.erase 0).image (fun p => p - 1)
    have hD' : ∀ q ∈ D', isDroppedAt m gs (elimBStep m acc g) q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨hp0, hpD⟩ := Finset.mem_erase.1 hp
      have hp1 : p = (p - 1) + 1 := by omega
      have := hD p hpD
      rw [hp1, isDroppedAt_cons_succ] at this
      exact this
    have ih' := ih (elimBStep m acc g) D' hD'
    have hcard : D'.card = (D.erase 0).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have ha0 : a ≠ 0 := (Finset.mem_erase.1 ha).1
      have hb0 : b ≠ 0 := (Finset.mem_erase.1 hb).1
      dsimp only at hab
      omega
    rw [elimB_cons, List.length_cons]
    by_cases h0 : 0 ∈ D
    · have hdrop0 := (isDroppedAt_cons_zero m g gs acc).1 (hD 0 h0)
      have hDc : D.card = D'.card + 1 := by
        rw [hcard, Finset.card_erase_of_mem h0]
        have := Finset.card_pos.2 ⟨0, h0⟩
        omega
      omega
    · have hDc : D.card = D'.card := by
        rw [hcard, Finset.erase_eq_of_notMem h0]
      have h2 : (elimBStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimBStep, List.length_append]
        have := toList_length_le (simpBAnd (m + acc.2.length)
          (if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false))
          (if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false))).1
        omega
      omega

theorem elimBStep_none_of_const_left (m : ℕ) (acc : List BStat × List BGate) (g : BGate)
    (c : Bool) (hc : acc.1.getD g.a (BStat.const false) = BStat.const c) :
    (elimBStep m acc g).2.length = acc.2.length := by
  simp only [elimBStep, hc]
  cases g.pa <;> simp [negBStat, simpBAnd]

theorem elimBStep_none_of_const_right (m : ℕ) (acc : List BStat × List BGate) (g : BGate)
    (c : Bool) (hc : acc.1.getD g.b (BStat.const false) = BStat.const c) :
    (elimBStep m acc g).2.length = acc.2.length := by
  simp only [elimBStep, hc]
  cases hpb : g.pb <;> cases acc.1.getD g.a (BStat.const false) <;> cases g.pa <;>
    simp [hpb, negBStat, simpBAnd]

theorem elimBStep_const_of_const_left (m : ℕ) (acc : List BStat × List BGate) (g : BGate)
    (hc : acc.1.getD g.a (BStat.const false) = BStat.const g.pa) :
    (elimBStep m acc g).1.getD acc.1.length (BStat.const false) = BStat.const false := by
  simp only [elimBStep, hc, getD_snoc_eq]
  cases g.pa <;> simp [negBStat, simpBAnd]

theorem elimBStep_const_of_const_right (m : ℕ) (acc : List BStat × List BGate) (g : BGate)
    (hc : acc.1.getD g.b (BStat.const false) = BStat.const g.pb) :
    (elimBStep m acc g).1.getD acc.1.length (BStat.const false) = BStat.const false := by
  simp only [elimBStep, hc, getD_snoc_eq]
  cases hpb : g.pb <;> cases acc.1.getD g.a (BStat.const false) <;> cases g.pa <;>
    simp [hpb, negBStat, simpBAnd]

theorem elimBStep_const_of_both_const (m : ℕ) (acc : List BStat × List BGate) (g : BGate)
    (ca cb : Bool) (ha : acc.1.getD g.a (BStat.const false) = BStat.const ca)
    (hb : acc.1.getD g.b (BStat.const false) = BStat.const cb) :
    ∃ c, (elimBStep m acc g).1.getD acc.1.length (BStat.const false) = BStat.const c := by
  simp only [elimBStep, ha, hb, getD_snoc_eq]
  cases g.pa <;> cases g.pb <;> cases ca <;> cases cb <;> simp [negBStat, simpBAnd]

theorem stepAcc_succ_getD (m : ℕ) (gs : List BGate) (acc : List BStat × List BGate)
    (p : ℕ) (g : BGate) (hg : gs[p]? = some g) (d : BStat) :
    (stepAcc m gs acc (p + 1)).1.getD (acc.1.length + p) d =
      (elimBStep m (stepAcc m gs acc p) g).1.getD (stepAcc m gs acc p).1.length d := by
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  unfold stepAcc
  rw [take_succ_eq p gs g hg, elimB_append]
  change (elimBStep m (elimB m (gs.take p) acc) g).1.getD (acc.1.length + p) d = _
  rw [elimB_fst_len, List.length_take_of_le (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shBGate (K : ℕ) (g : BGate) : BGate :=
  ⟨shift K g.a, g.pa, shift K g.b, g.pb⟩

def RelDB (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relDB_wires (K : ℕ) (post : List BGate) : ∀ W W' : List Bool,
    (∀ g ∈ post, g.a ≠ K ∧ g.b ≠ K) → RelDB K W W' →
    RelDB K (bwires post W) (bwires (post.map (shBGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have haK := (hno g List.mem_cons_self).1
    have hbK := (hno g List.mem_cons_self).2
    have hv : (shBGate K g).eval W' = g.eval W := by
      simp only [shBGate, BGate.eval, h3 g.a haK, h3 g.b hbK]
    have s1 : bwires (g :: post) W = bwires post (W ++ [g.eval W]) := rfl
    have s2 : bwires ((g :: post).map (shBGate K)) W'
        = bwires (post.map (shBGate K)) (W' ++ [(shBGate K g).eval W']) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK'
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK'
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem shift_lt_of_lt {K a m : ℕ} (ha : a < m + 1) (haK : a ≠ K) (hKm : K ≤ m) :
    shift K a < m := by
  unfold shift
  split <;> omega

theorem shift_ne {K a b : ℕ} (haK : a ≠ K) (hbK : b ≠ K) (hab : a ≠ b) :
    shift K a ≠ shift K b := by
  unfold shift
  split <;> split <;> omega

theorem cleanB_del_bgate (n : ℕ) (pre : List BGate) (g : BGate) (post : List BGate)
    (hcl : CleanB n (pre ++ g :: post))
    (hno : ∀ g' ∈ post, g'.a ≠ n + pre.length ∧ g'.b ≠ n + pre.length) :
    CleanB n (pre ++ post.map (shBGate (n + pre.length))) := by
  intro p g' hp
  by_cases hlt : p < pre.length
  · rw [List.getElem?_append_left hlt] at hp
    exact hcl p g' (by rw [List.getElem?_append_left hlt]; exact hp)
  · rw [List.getElem?_append_right (by omega)] at hp
    have hmap : (post.map (shBGate (n + pre.length)))[p - pre.length]? =
        Option.map (shBGate (n + pre.length)) post[p - pre.length]? := by
      simp [List.getElem?_map]
    rw [hmap] at hp
    rcases hp_eq : post[p - pre.length]? with _ | g0
    · rw [hp_eq] at hp; simp at hp
    · rw [hp_eq] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      subst hp
      have hg0mem : g0 ∈ post := List.mem_of_getElem? hp_eq
      have h0no := hno g0 hg0mem
      have h0cl := hcl (pre.length + 1 + (p - pre.length)) g0 (by
        rw [List.getElem?_append_right (by omega)]
        have he : pre.length + 1 + (p - pre.length) - pre.length = (p - pre.length) + 1 := by omega
        rw [he]
        exact hp_eq)
      have ha' : shift (n + pre.length) g0.a < n + p :=
        shift_lt_of_lt (by omega) h0no.1 (by omega)
      have hb' : shift (n + pre.length) g0.b < n + p :=
        shift_lt_of_lt (by omega) h0no.2 (by omega)
      have hab' : shift (n + pre.length) g0.a ≠ shift (n + pre.length) g0.b :=
        shift_ne h0no.1 h0no.2 h0cl.2.2
      exact ⟨ha', hb', hab'⟩

theorem del_bgate_wires (n : ℕ) (pre : List BGate) (g : BGate) (post : List BGate) (o : ℕ)
    (hno : ∀ g' ∈ post, g'.a ≠ n + pre.length ∧ g'.b ≠ n + pre.length)
    (ho : o ≠ n + pre.length) (y : List Bool) (hy : y.length = n) :
    (bwires (pre ++ post.map (shBGate (n + pre.length))) y).getD (shift (n + pre.length) o) false =
      (bwires (pre ++ g :: post) y).getD o false := by
  have h1 : bwires (pre ++ g :: post) y = bwires post (bwires pre y ++ [g.eval (bwires pre y)]) := by
    rw [bwires_append]; rfl
  have hl : (bwires pre y).length = n + pre.length := by
    rw [length_bwires, hy]
  rw [h1, bwires_append]
  refine (relDB_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
  intro a ha
  by_cases hlt : a < n + pre.length
  · have : shift (n + pre.length) a = a := by simp [shift, hlt]
    rw [this, List.getD_append _ _ _ _ (by omega)]
  · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
    rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem bsize_congr {n s : ℕ} {f g : BFn n} (h : ∀ x, f x = g x)
    (hc : HasBSize n f s) : HasBSize n g s := by
  obtain ⟨gs, o, po, hcl, hlen, hev⟩ := hc
  exact ⟨gs, o, po, hcl, hlen, fun x => (hev x).trans (h x)⟩

theorem getD_ofFn {α : Type} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (h : i < m) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [h]

theorem nodup_of_len_le_toFinset {α : Type} [DecidableEq α] :
    ∀ L : List α, L.length ≤ L.toFinset.card → L.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    by_cases ha : a ∈ t
    · have heq : (a :: t).toFinset = t.toFinset := by simp [List.toFinset_cons, ha]
      have hle := List.toFinset_card_le t
      rw [heq] at h
      simp only [List.length_cons] at h
      omega
    · exact List.nodup_cons.2 ⟨ha, nodup_of_len_le_toFinset t (by
        have heq : (a :: t).toFinset.card = t.toFinset.card + 1 := by
          simp [List.toFinset_cons, Finset.card_insert_of_notMem, ha]
        simp only [List.length_cons] at h
        omega)⟩

theorem flatMap_pair_len (gs : List BGate) :
    (gs.flatMap fun g => [g.a, g.b]).length = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem xor_out_eq (w pj po res fval : Bool) (h1 : xor w pj = res) (h2 : xor res po = fval) :
    xor w (xor pj po) = fval := by
  rw [← Bool.xor_assoc, h1, h2]

theorem bsize_relabel {n m : ℕ} (π : Fin n → Fin m) (f : BFn n) (s : ℕ)
    (hc : HasBSize n f s) : HasBSize m (fun y => f (y ∘ π)) s := by
  obtain ⟨gs, o, po, hcl, hlen, hev⟩ := hc
  let init : List BStat := List.ofFn (fun i : Fin n => BStat.wire (π i).val false)
  set acc := elimB m gs (init, []) with hacc
  have hinv_init : ∀ y : Fin m → Bool,
      InvB m (List.ofFn y) (List.ofFn (y ∘ π)) (init, []) := by
    intro y
    refine ⟨by simp [init], ?_⟩
    intro i
    by_cases hlt : i < n
    · simp [init, hlt, BStat.Valid, BStat.val, bwires, (π ⟨i, hlt⟩).2]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool,
      InvB m (List.ofFn y) (bwires gs (List.ofFn (y ∘ π))) acc :=
    fun y => inv_elimB m (List.ofFn y) (by simp) gs _ _ (hinv_init y)
  have hcl' : CleanB m acc.2 := by
    exact clean_elimB m (List.ofFn fun _ : Fin m => false) (by simp) gs _ _
      (hinv_init (fun _ => false)) (by intro p g hp; simp at hp)
  have hlen' : acc.2.length ≤ s := by
    have := elimB_len m gs (init, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD o (BStat.const false) with
  | const c =>
    refine ⟨[], m, xor c po, by intro p g hp; simp at hp, by simp, ?_⟩
    intro y
    have h0 : (bwires [] (List.ofFn y)).getD m false = false := by
      rw [bwires, List.foldl_nil, List.getD_eq_default _ _ (by simp)]
    have h1 := ((hinv y).2 o).2
    rw [hst] at h1
    simp only [BStat.val] at h1
    have he := hev (y ∘ π)
    dsimp only
    rw [← he, ← h1, h0, Bool.false_xor]
  | wire j pj =>
    refine ⟨acc.2, j, xor pj po, hcl', hlen', ?_⟩
    intro y
    have h1 := ((hinv y).2 o).2
    rw [hst] at h1
    simp only [BStat.val] at h1
    exact xor_out_eq _ pj po _ (f (y ∘ π)) h1 (hev (y ∘ π))

def gateSuppB {n : ℕ} (L : List (Finset (Fin n))) (g : BGate) : Finset (Fin n) :=
  L.getD g.a ∅ ∪ L.getD g.b ∅

def suppsFromB {n : ℕ} (gs : List BGate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSuppB L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def AgreeB {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_bwires {n : ℕ} (x y : Fin n → Bool) (gs : List BGate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), AgreeB x y L w w' →
      AgreeB x y (suppsFromB gs L) (bwires gs w) (bwires gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSuppB L g]) (w ++ [g.eval w]) (w' ++ [g.eval w'])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      simp only [gateSuppB, Finset.mem_union] at hj
      have ha := h3 g.a (fun i hi => hj i (Or.inl hi))
      have hb := h3 g.b (fun i hi => hj i (Or.inr hi))
      simp only [BGate.eval]
      rw [ha, hb]
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputsB {n : ℕ} (x y : Fin n → Bool) :
    AgreeB x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def CntB {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cntB_inputs {n : ℕ} : CntB (n := n) 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cntB_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : BGate)
    (h : CntB t L) : CntB (t + 1) (L ++ [gateSuppB L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSuppB L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ {g.a, g.b}).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        rcases Finset.mem_union.1 hij with hia | hib
        · exact ⟨g.a, Finset.mem_union_right _ (by simp), hia⟩
        · exact ⟨g.b, Finset.mem_union_right _ (by simp), hib⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ {g.a, g.b}).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      have h2 : ({g.a, g.b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      omega
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ {g.a, g.b})
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSuppB L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cntB_suppsFromB {n : ℕ} (gs : List BGate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    CntB t L → CntB (t + gs.length) (suppsFromB gs L) := by
  induction gs with
  | nil => intro t L h; exact h
  | cons g gs ih =>
    intro t L h
    have := ih (t + 1) (L ++ [gateSuppB L g]) (cntB_step t L g h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_b (n : ℕ) (f : BFn n)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasBSize n f s) : n ≤ s + 1 := by
  obtain ⟨gs, o, po, _, hsz, hev⟩ := h
  set S := (suppsFromB gs (inputSupps n)).getD o ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_bwires (Function.update x i (!x i)) x gs _ _ _
      (agree_inputsB _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev, hag]
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cntB_suppsFromB gs 0 (inputSupps n) cntB_inputs {o}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem suppB_noread {n : ℕ} (k : ℕ) (hk : k < n) (gs : List BGate) :
    ∀ L : List (Finset (Fin n)),
      (∀ g ∈ gs, g.a ≠ k ∧ g.b ≠ k) → (∀ j : ℕ, j ≠ k → (⟨k, hk⟩ : Fin n) ∉ L.getD j ∅) →
      ∀ j : ℕ, j ≠ k → (⟨k, hk⟩ : Fin n) ∉ (suppsFromB gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSuppB L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      rcases Finset.mem_union.1 hmem with ha | hb
      · exact h g.a (hno g List.mem_cons_self).1 ha
      · exact h g.b (hno g List.mem_cons_self).2 hb
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_noread {n : ℕ} (k : ℕ) (hk : k < n) :
    ∀ j : ℕ, j ≠ k → (⟨k, hk⟩ : Fin n) ∉ (inputSupps n).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n
  · have e : (inputSupps n).getD j ∅ = {⟨j, hlt⟩} := by simp [inputSupps, hlt]
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (congrArg Fin.val e').symm
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem wire_read_of_dep {n : ℕ} (gs : List BGate) (o : ℕ) (po : Bool) (f : BFn n)
    (hev : ∀ x : Fin n → Bool, xor ((bwires gs (List.ofFn x)).getD o false) po = f x)
    (k : Fin n) (ho : o ≠ k.val)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x k (!x k)) ≠ f x) :
    ∃ g ∈ gs, g.a = k.val ∨ g.b = k.val := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hdep
  apply hx
  have hns := suppB_noread k.val k.isLt gs (inputSupps n)
    (fun g hg => hno g hg) (inputSupps_noread k.val k.isLt) o ho
  have hag := (agree_bwires (Function.update x k (!x k)) x gs _ _ _
    (agree_inputsB _ _)).2.2 o (by
      intro i hi
      have : i ≠ k := fun e => hns (e ▸ hi)
      simp [Function.update_of_ne this])
  rw [← hev, ← hev, hag]

theorem exists_min_cleanB (n : ℕ) (f : BFn n) (s : ℕ) (h : HasBSize n f s) :
    ∃ (gs : List BGate) (o : ℕ) (po : Bool),
      CleanB n gs ∧ gs.length ≤ s ∧
      (∀ x : Fin n → Bool, xor ((bwires gs (List.ofFn x)).getD o false) po = f x) ∧
      (∀ gs1 o1 po1, CleanB n gs1 →
        (∀ x : Fin n → Bool, xor ((bwires gs1 (List.ofFn x)).getD o1 false) po1 = f x) →
        gs.length ≤ gs1.length) := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List BGate) (o : ℕ) (po : Bool),
    CleanB n gs ∧ gs.length = t ∧
    ∀ x : Fin n → Bool, xor ((bwires gs (List.ofFn x)).getD o false) po = f x
  obtain ⟨gs0, o0, po0, hcl0, hlen0, hev0⟩ := h
  have hex : ∃ t, P t := ⟨gs0.length, gs0, o0, po0, hcl0, rfl, hev0⟩
  have hmin : Nat.find hex ≤ gs0.length := Nat.find_min' hex ⟨gs0, o0, po0, hcl0, rfl, hev0⟩
  obtain ⟨gs, o, po, hcl, hlen, hev⟩ := Nat.find_spec hex
  refine ⟨gs, o, po, hcl, by omega, hev, ?_⟩
  intro gs1 o1 po1 hcl1 hev1
  have hP1 : P gs1.length := ⟨gs1, o1, po1, hcl1, rfl, hev1⟩
  have := Nat.find_min' hex hP1
  omega

theorem min_cleanB_used (n : ℕ) (f : BFn n) (gs : List BGate) (o : ℕ) (po : Bool)
    (hcl : CleanB n gs)
    (hev : ∀ x : Fin n → Bool, xor ((bwires gs (List.ofFn x)).getD o false) po = f x)
    (hmin : ∀ gs1 o1 po1, CleanB n gs1 →
      (∀ x : Fin n → Bool, xor ((bwires gs1 (List.ofFn x)).getD o1 false) po1 = f x) →
      gs.length ≤ gs1.length) :
    ∀ p < gs.length, n + p = o ∨ ∃ (q : ℕ) (g : BGate), gs[q]? = some g ∧ (g.a = n + p ∨ g.b = n + p) := by
  intro p hp
  by_contra hcon
  push Not at hcon
  obtain ⟨hpo, hno⟩ := hcon
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
  have hno' : ∀ g' ∈ post, g'.a ≠ n + pre.length ∧ g'.b ≠ n + pre.length := by
    intro g' hg'
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
    have := hno (pre.length + 1 + q) g' (by
      rw [List.getElem?_append_right (by omega)]
      have he : pre.length + 1 + q - pre.length = q + 1 := by omega
      rw [he]; simpa using hq)
    rw [hpl]; exact this
  have hcl' := cleanB_del_bgate n pre g post hcl hno'
  have hev' : ∀ x : Fin n → Bool,
      xor ((bwires (pre ++ post.map (shBGate (n + pre.length))) (List.ofFn x)).getD
        (shift (n + pre.length) o) false) po = f x := by
    intro x
    rw [del_bgate_wires n pre g post o hno' (by rw [hpl]; exact fun e => hpo e.symm) (List.ofFn x) (by simp)]
    exact hev x
  have hle := hmin (pre ++ post.map (shBGate (n + pre.length))) (shift (n + pre.length) o) po hcl' hev'
  simp at hle

theorem bwires_agree_outside {n : ℕ} (u v : Fin n) (gs : List BGate)
    (hno : ∀ g ∈ gs, g.a ≠ u.val ∧ g.b ≠ u.val ∧ g.a ≠ v.val ∧ g.b ≠ v.val) :
    ∀ W W' : List Bool,
      W.length = W'.length ∧ (∀ w, w ≠ u.val → w ≠ v.val → W.getD w false = W'.getD w false) →
      ∀ w, w ≠ u.val → w ≠ v.val → (bwires gs W).getD w false = (bwires gs W').getD w false := by
  induction gs with
  | nil => intro W W' h w hwu hwv; exact h.2 w hwu hwv
  | cons g gs ih =>
    intro W W' ⟨hl, hagree⟩
    have hg := hno g List.mem_cons_self
    have heval : g.eval W = g.eval W' := by
      simp only [BGate.eval]
      rw [hagree g.a hg.1 hg.2.2.1, hagree g.b hg.2.1 hg.2.2.2]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (W ++ [g.eval W]) (W' ++ [g.eval W'])
    refine ⟨by simp [hl], ?_⟩
    intro w hwu hwv
    by_cases hw : w = W.length
    · subst hw; rw [getD_snoc_eq, hl, getD_snoc_eq, heval]
    · rw [getD_snoc_ne _ _ _ _ hw, getD_snoc_ne _ _ _ _ (by omega)]
      exact hagree w hwu hwv

theorem lower_ge_n (n : ℕ) (hn : 2 ≤ n) (f : BFn n)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (hpair : ∀ (u v : Fin n) (pu pv : Bool), u ≠ v →
      ∃ x y : Fin n → Bool, (∀ i, i ≠ u → i ≠ v → x i = y i) ∧
        ((xor (x u) pu && xor (x v) pv) = (xor (y u) pu && xor (y v) pv)) ∧ f x ≠ f y)
    (s : ℕ) (hs : HasBSize n f s) : n ≤ s := by
  by_contra hlt
  push Not at hlt
  obtain ⟨gs, o, po, hcl, hlen, hev, hmin_len⟩ := exists_min_cleanB n f s hs
  have hmin := min_cleanB_used n f gs o po hcl hev hmin_len
  have hdl := dep_lower_b n f hdep gs.length ⟨gs, o, po, hcl, le_rfl, hev⟩
  have hglen : gs.length = n - 1 := by omega
  have ho_ge : n ≤ o := by
    by_contra ho_lt
    push Not at ho_lt
    let i0 : Fin n := ⟨o, ho_lt⟩
    let j : Fin n := if o = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hji0 : j ≠ i0 := by
      dsimp [j, i0]
      by_cases h0 : o = 0
      · simp [h0, Fin.ext_iff]
      · simp [h0, Fin.ext_iff]; omega
    obtain ⟨x, hx⟩ := hdep j
    apply hx
    have e1 : (bwires gs (List.ofFn (Function.update x j (!x j)))).getD o false =
        (Function.update x j (!x j)) i0 := by
      rw [getD_bwires _ _ _ (by simp [ho_lt]), getD_ofFn _ _ _ ho_lt]
    have e2 : (bwires gs (List.ofFn x)).getD o false = x i0 := by
      rw [getD_bwires _ _ _ (by simp [ho_lt]), getD_ofFn _ _ _ ho_lt]
    rw [← hev (Function.update x j (!x j)), ← hev x, e1, e2, Function.update_of_ne hji0.symm]
  have ho_lt : o < n + gs.length := by
    by_contra ho_ge2
    push Not at ho_ge2
    obtain ⟨x, hx⟩ := hdep ⟨0, by omega⟩
    apply hx
    have e1 : (bwires gs (List.ofFn (Function.update x ⟨0, by omega⟩ (!x ⟨0, by omega⟩)))).getD o false = false :=
      List.getD_eq_default _ _ (by rw [length_bwires]; simp; omega)
    have e2 : (bwires gs (List.ofFn x)).getD o false = false :=
      List.getD_eq_default _ _ (by rw [length_bwires]; simp; omega)
    rw [← hev _, ← hev x, e1, e2]
  let L : List ℕ := gs.flatMap fun g => [g.a, g.b]
  have hLlen : L.length = 2 * gs.length := flatMap_pair_len gs
  let W : Finset ℕ := (Finset.range (n + gs.length)).erase o
  have hWcard : W.card = 2 * gs.length := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 ho_lt), Finset.card_range]
    omega
  have hWsub : W ⊆ L.toFinset := by
    intro w hw
    obtain ⟨hwo, hwr⟩ := Finset.mem_erase.1 hw
    have hwlt := Finset.mem_range.1 hwr
    rw [List.mem_toFinset, List.mem_flatMap]
    by_cases hwn : w < n
    · obtain ⟨g, hg, hmem⟩ := wire_read_of_dep gs o po f hev ⟨w, hwn⟩ (fun e => by omega) (hdep ⟨w, hwn⟩)
      exact ⟨g, hg, by rcases hmem with h | h <;> simp [h]⟩
    · have hp : w - n < gs.length := by omega
      rcases hmin (w - n) hp with heq | ⟨q, g, hq, hmem⟩
      · exfalso; apply hwo; omega
      · exact ⟨g, List.mem_of_getElem? hq, by rcases hmem with h | h <;> simp [h, show n + (w - n) = w by omega]⟩
  have hLnodup : L.Nodup := by
    have hc1 : W.card ≤ L.toFinset.card := Finset.card_le_card hWsub
    exact nodup_of_len_le_toFinset L (by omega)
  rcases gs with _ | ⟨g0, gs'⟩
  · simp at hglen; omega
  · have hg0 := hcl 0 g0 rfl
    simp only [Nat.add_zero] at hg0
    have hLcons : L = g0.a :: g0.b :: (gs'.flatMap fun g => [g.a, g.b]) := by
      simp [L]
    rw [hLcons] at hLnodup
    have hnd1 := (List.nodup_cons.1 hLnodup).2
    have ha_not : g0.a ∉ gs'.flatMap fun g => [g.a, g.b] :=
      fun hm => (List.nodup_cons.1 hLnodup).1 (List.mem_cons_of_mem _ hm)
    have hb_not : g0.b ∉ gs'.flatMap fun g => [g.a, g.b] :=
      (List.nodup_cons.1 hnd1).1
    let uF : Fin n := ⟨g0.a, hg0.1⟩
    let vF : Fin n := ⟨g0.b, hg0.2.1⟩
    have huv : uF ≠ vF := fun e => hg0.2.2 (congrArg Fin.val e)
    obtain ⟨x, y, hxy, hg0eq, hfne⟩ := hpair uF vF g0.pa g0.pb huv
    apply hfne
    have hno' : ∀ g ∈ gs', g.a ≠ uF.val ∧ g.b ≠ uF.val ∧ g.a ≠ vF.val ∧ g.b ≠ vF.val := by
      intro g hg
      refine ⟨fun e => ha_not (List.mem_flatMap.2 ⟨g, hg, by simp [uF, e]⟩),
        fun e => ha_not (List.mem_flatMap.2 ⟨g, hg, by simp [uF, e]⟩),
        fun e => hb_not (List.mem_flatMap.2 ⟨g, hg, by simp [vF, e]⟩),
        fun e => hb_not (List.mem_flatMap.2 ⟨g, hg, by simp [vF, e]⟩)⟩
    have hg0eval : g0.eval (List.ofFn x) = g0.eval (List.ofFn y) := by
      simp only [BGate.eval]
      rw [getD_ofFn x false g0.a hg0.1, getD_ofFn x false g0.b hg0.2.1,
        getD_ofFn y false g0.a hg0.1, getD_ofFn y false g0.b hg0.2.1]
      exact hg0eq
    have hbw : (bwires (g0 :: gs') (List.ofFn x)).getD o false =
        (bwires (g0 :: gs') (List.ofFn y)).getD o false := by
      change (bwires gs' (List.ofFn x ++ [g0.eval (List.ofFn x)])).getD o false =
        (bwires gs' (List.ofFn y ++ [g0.eval (List.ofFn y)])).getD o false
      apply bwires_agree_outside uF vF gs' hno'
      · refine ⟨by simp, ?_⟩
        intro w hwu hwv
        by_cases hwn : w < n
        · rw [List.getD_append _ _ _ _ (by simp; exact hwn),
            List.getD_append _ _ _ _ (by simp; exact hwn),
            getD_ofFn x false w hwn, getD_ofFn y false w hwn]
          exact hxy ⟨w, hwn⟩ (fun e => hwu (congrArg Fin.val e)) (fun e => hwv (congrArg Fin.val e))
        · by_cases hweq : w = n
          · subst hweq
            rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hg0eval]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro e; omega
      · intro e; omega
    rw [← hev x, ← hev y, hbw]

def initAt {n : ℕ} (u : Fin (n + 1)) (c : Bool) : List BStat :=
  List.ofFn fun i : Fin (n + 1) =>
    if i = u then BStat.const c
    else BStat.wire (if i.val < u.val then i.val else i.val - 1) false

theorem succAbove_of_ne {n : ℕ} (u i : Fin (n + 1)) (hi : i ≠ u) :
    u.succAbove ⟨if i.val < u.val then i.val else i.val - 1, by
      have hne : i.val ≠ u.val := fun e => hi (Fin.ext e)
      split <;> omega⟩ = i := by
  have hne : i.val ≠ u.val := fun e => hi (Fin.ext e)
  ext
  by_cases hiu : i.val < u.val
  · have hl : (⟨if i.val < u.val then i.val else i.val - 1, by split <;> omega⟩ : Fin n).castSucc < u := by
      rw [Fin.lt_def, Fin.val_castSucc]; simp [hiu]
    rw [Fin.succAbove_of_castSucc_lt _ _ hl]; simp [hiu]
  · have hr : u ≤ (⟨if i.val < u.val then i.val else i.val - 1, by split <;> omega⟩ : Fin n).castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]; simp only [hiu, ↓reduceIte]; omega
    rw [Fin.succAbove_of_le_castSucc _ _ hr]; simp only [Fin.val_succ, hiu, ↓reduceIte]; omega

theorem invB_initAt {n : ℕ} (u : Fin (n + 1)) (c : Bool) (y : Fin n → Bool) :
    InvB n (List.ofFn y) (List.ofFn (u.insertNth c y)) (initAt u c, []) := by
  refine ⟨by simp [initAt], ?_⟩
  intro i
  by_cases hlt : i < n + 1
  · let iF : Fin (n + 1) := ⟨i, hlt⟩
    have e1 : (initAt u c).getD i (BStat.const false) =
        if iF = u then BStat.const c
        else BStat.wire (if i < u.val then i else i - 1) false := by
      rw [initAt, getD_ofFn _ _ _ hlt]
    have e2 : (List.ofFn (u.insertNth c y : Fin (n + 1) → Bool)).getD i false =
        (u.insertNth c y : Fin (n + 1) → Bool) ⟨i, hlt⟩ :=
      getD_ofFn (u.insertNth c y : Fin (n + 1) → Bool) false i hlt
    rw [e1, e2]
    by_cases hiu : iF = u
    · simp only [hiu, ↓reduceIte, BStat.Valid, BStat.val, true_and]
      rw [show (⟨i, hlt⟩ : Fin (n + 1)) = u from hiu, Fin.insertNth_apply_same (α := fun _ => Bool)]
    · simp only [hiu, ↓reduceIte, BStat.Valid, BStat.val, bwires, List.foldl_nil]
      have hne : i ≠ u.val := fun e => hiu (Fin.ext e)
      let j : Fin n := ⟨if i < u.val then i else i - 1, by split <;> omega⟩
      have hvalid : j.val < n + ([] : List BGate).length := by simp [j.isLt]
      refine ⟨hvalid, ?_⟩
      have hj : (List.ofFn y).getD j.val false = y j := getD_ofFn y false j.val j.isLt
      rw [hj, Bool.xor_false]
      have hsub := succAbove_of_ne u iF hiu
      have heq : (u.insertNth c y : Fin (n + 1) → Bool) ⟨i, hlt⟩ =
          (u.insertNth c y : Fin (n + 1) → Bool) (u.succAbove j) :=
        congrArg (u.insertNth c y : Fin (n + 1) → Bool) hsub.symm
      rw [heq, Fin.insertNth_apply_succAbove (α := fun _ => Bool)]
  · rw [List.getD_eq_default _ _ (by simp [initAt]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem initAt_getD_eq {n : ℕ} (u : Fin (n + 1)) (c : Bool) :
    (initAt u c).getD u.val (BStat.const false) = BStat.const c := by
  simp only [initAt]
  rw [getD_ofFn _ _ _ u.isLt]
  simp

theorem elim_var_at {n s : ℕ} (u : Fin (n + 1)) (c : Bool) (f : BFn (n + 1))
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x u (!x u)) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (u.insertNth c y) ≠ f (u.insertNth c y'))
    (hs : HasBSize (n + 1) f s) :
    1 ≤ s ∧ HasBSize n (fun y : Fin n → Bool => f (u.insertNth c y)) (s - 1) := by
  obtain ⟨gs, o, po, _, hlen, hev⟩ := hs
  set acc := elimB n gs (initAt u c, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      InvB n (List.ofFn y) (bwires gs (List.ofFn (u.insertNth c y))) acc :=
    fun y => inv_elimB n (List.ofFn y) (by simp) gs _ _ (invB_initAt u c y)
  have hcl' : CleanB n acc.2 :=
    clean_elimB n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (invB_initAt u c _) (by intro p g hp; simp at hp)
  have ho : o ≠ u.val := by
    intro e
    subst e
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev (u.insertNth c y), ← hev (u.insertNth c y')]
    rw [getD_bwires _ _ _ (by simp [u.isLt]), getD_bwires _ _ _ (by simp [u.isLt]),
      getD_ofFn _ _ _ u.isLt, getD_ofFn _ _ _ u.isLt]
    simp [Fin.insertNth_apply_same]
  obtain ⟨g, hg, hmem⟩ := wire_read_of_dep gs o po f hev u ho hdep
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  have hdrop : isDroppedAt n gs (initAt u c, []) p := by
    refine ⟨g, hp, ?_⟩
    have hpu : (stepAcc n gs (initAt u c, []) p).1.getD u.val (BStat.const false) =
        BStat.const c := by
      unfold stepAcc
      rw [elimB_fst_getD _ _ _ _ _ (by simp [initAt, u.isLt])]
      exact initAt_getD_eq u c
    rcases hmem with ha | hb
    · exact elimBStep_none_of_const_left _ _ _ c (ha ▸ hpu)
    · exact elimBStep_none_of_const_right _ _ _ c (hb ▸ hpu)
  have hle := dropped_le n gs (initAt u c, []) {p} (by simpa using hdrop)
  rw [← hacc] at hle
  simp only [Finset.card_singleton, List.length_nil, zero_add] at hle
  refine ⟨by omega, ?_⟩
  cases hst : acc.1.getD o (BStat.const false) with
  | const d =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 o).2
    have e2 := ((hinv y').2 o).2
    rw [hst] at e1 e2
    simp only [BStat.val] at e1 e2
    rw [← hev (u.insertNth c y), ← hev (u.insertNth c y'), ← e1, ← e2]
  | wire j pj =>
    refine ⟨acc.2, j, xor pj po, hcl', by omega, ?_⟩
    intro y
    have e1 := ((hinv y).2 o).2
    rw [hst] at e1
    simp only [BStat.val] at e1
    exact xor_out_eq _ pj po _ (f (u.insertNth c y)) e1 (hev (u.insertNth c y))

theorem elim_kill_var {n s : ℕ} (u : Fin (n + 1)) (f : BFn (n + 1))
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x u (!x u)) ≠ f x)
    (hnc0 : ∃ y y' : Fin n → Bool, f (u.insertNth false y) ≠ f (u.insertNth false y'))
    (hnc1 : ∃ y y' : Fin n → Bool, f (u.insertNth true y) ≠ f (u.insertNth true y'))
    (hs : HasBSize (n + 1) f s) :
    2 ≤ s ∧ (HasBSize n (fun y : Fin n → Bool => f (u.insertNth false y)) (s - 2) ∨
      HasBSize n (fun y : Fin n → Bool => f (u.insertNth true y)) (s - 2)) := by
  obtain ⟨gs, o, po, hcl, hlen, hev, hmin_len⟩ := exists_min_cleanB (n + 1) f s hs
  have hmin := min_cleanB_used (n + 1) f gs o po hcl hev hmin_len
  have ho : o ≠ u.val := by
    intro e
    subst e
    obtain ⟨y, y', hne⟩ := hnc0
    apply hne
    rw [← hev (u.insertNth false y), ← hev (u.insertNth false y')]
    rw [getD_bwires _ _ _ (by simp [u.isLt]), getD_bwires _ _ _ (by simp [u.isLt]),
      getD_ofFn _ _ _ u.isLt, getD_ofFn _ _ _ u.isLt]
    simp [Fin.insertNth_apply_same]
  obtain ⟨g, hg, hmem⟩ := wire_read_of_dep gs o po f hev u ho hdep
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
  have hklt : k < gs.length := (List.getElem?_eq_some_iff.1 hk).1
  let c : Bool := if g.a = u.val then g.pa else g.pb
  have hnc_c : ∃ y y' : Fin n → Bool, f (u.insertNth c y) ≠ f (u.insertNth c y') := by
    cases hc : c <;> [exact hnc0; exact hnc1]
  set acc := elimB n gs (initAt u c, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      InvB n (List.ofFn y) (bwires gs (List.ofFn (u.insertNth c y))) acc :=
    fun y => inv_elimB n (List.ofFn y) (by simp) gs _ _ (invB_initAt u c y)
  have hcl' : CleanB n acc.2 :=
    clean_elimB n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (invB_initAt u c _) (by intro p g' hp; simp at hp)
  have hku : (stepAcc n gs (initAt u c, []) k).1.getD u.val (BStat.const false) =
      BStat.const c := by
    unfold stepAcc
    rw [elimB_fst_getD _ _ _ _ _ (by simp [initAt, u.isLt])]
    exact initAt_getD_eq u c
  have hinit_len : (initAt u c).length = n + 1 := by simp [initAt]
  have hk_const : (stepAcc n gs (initAt u c, []) (k + 1)).1.getD (n + 1 + k) (BStat.const false) =
      BStat.const false := by
    rw [← hinit_len, stepAcc_succ_getD _ _ _ _ g hk]
    change (elimBStep n (stepAcc n gs (initAt u c, []) k) g).1.getD _ _ = _
    by_cases ha : g.a = u.val
    · have hc_eq : g.pa = c := by simp [c, ha]
      exact elimBStep_const_of_const_left _ _ _ (ha ▸ hc_eq ▸ hku)
    · have hb : g.b = u.val := by rcases hmem with h | h; exact absurd h ha; exact h
      have hc_eq : g.pb = c := by simp [c, ha]
      exact elimBStep_const_of_const_right _ _ _ (hb ▸ hc_eq ▸ hku)
  have hk_const_all : ∀ q, k + 1 ≤ q →
      (stepAcc n gs (initAt u c, []) q).1.getD (n + 1 + k) (BStat.const false) = BStat.const false := by
    intro q hkq
    rw [stepAcc_getD_ge n gs (initAt u c, []) (k + 1) q (n + 1 + k) hkq
      (by simp [initAt]; omega)]
    exact hk_const
  have hko : n + 1 + k ≠ o := by
    intro e
    obtain ⟨y, y', hne⟩ := hnc_c
    apply hne
    have h1 := ((hinv y).2 o).2
    have h2 := ((hinv y').2 o).2
    have hacc_eq : acc.1.getD o (BStat.const false) = BStat.const false := by
      rw [← e, hacc]
      have htake : gs = gs.take gs.length := (List.take_length).symm
      change (elimB n gs (initAt u c, [])).1.getD (n + 1 + k) (BStat.const false) = _
      rw [htake]
      exact hk_const_all gs.length (by omega)
    rw [hacc_eq] at h1 h2
    simp only [BStat.val] at h1 h2
    rw [← hev (u.insertNth c y), ← hev (u.insertNth c y'), ← h1, ← h2]
  rcases hmin k hklt with hcon | ⟨m, gm, hm, hmem_m⟩
  · exact absurd hcon hko
  · have hm_lt : m < gs.length := (List.getElem?_eq_some_iff.1 hm).1
    have hkm : k < m := by
      have hmcl := hcl m gm hm
      rcases hmem_m with hma | hmb <;> omega
    have hdrop_k : isDroppedAt n gs (initAt u c, []) k := by
      refine ⟨g, hk, ?_⟩
      rcases hmem with ha | hb
      · exact elimBStep_none_of_const_left _ _ _ c (ha ▸ hku)
      · exact elimBStep_none_of_const_right _ _ _ c (hb ▸ hku)
    have hdrop_m : isDroppedAt n gs (initAt u c, []) m := by
      refine ⟨gm, hm, ?_⟩
      have hmc := hk_const_all m (by omega)
      rcases hmem_m with hma | hmb
      · exact elimBStep_none_of_const_left _ _ _ false (hma ▸ hmc)
      · exact elimBStep_none_of_const_right _ _ _ false (hmb ▸ hmc)
    have hle := dropped_le n gs (initAt u c, []) {k, m} (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption)
    rw [Finset.card_pair (Nat.ne_of_lt hkm), ← hacc] at hle
    simp only [List.length_nil, zero_add] at hle
    refine ⟨by omega, ?_⟩
    cases hst : acc.1.getD o (BStat.const false) with
    | const d =>
      exfalso
      obtain ⟨y, y', hne⟩ := hnc_c
      apply hne
      have e1 := ((hinv y).2 o).2
      have e2 := ((hinv y').2 o).2
      rw [hst] at e1 e2
      simp only [BStat.val] at e1 e2
      rw [← hev (u.insertNth c y), ← hev (u.insertNth c y'), ← e1, ← e2]
    | wire j pj =>
      have hbs : HasBSize n (fun y : Fin n → Bool => f (u.insertNth c y)) (s - 2) := by
        refine ⟨acc.2, j, xor pj po, hcl', by omega, ?_⟩
        intro y
        have e1 := ((hinv y).2 o).2
        rw [hst] at e1
        simp only [BStat.val] at e1
        exact xor_out_eq _ pj po _ (f (u.insertNth c y)) e1 (hev (u.insertNth c y))
      cases hc : c
      · rw [hc] at hbs; exact Or.inl hbs
      · rw [hc] at hbs; exact Or.inr hbs

def simpULeaf (m u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ) (p1 p2 : Bool) :
    Option BGate × BStat :=
  if p1 = pu then
    if p2 then (some ⟨u, pu, v, !pv⟩, BStat.wire m false)
    else (none, BStat.wire n0 false)
  else
    if p2 then (none, BStat.wire u (!pu))
    else (none, BStat.const false)

def simpUAnd (m u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ)
    (s1 s2 : BStat) : Option BGate × BStat :=
  match s1, s2 with
  | BStat.wire j pj, BStat.wire k pk =>
    if j = u ∧ k = n0 then simpULeaf m u pu v pv n0 pj pk
    else if j = n0 ∧ k = u then simpULeaf m u pu v pv n0 pk pj
    else simpBAnd m s1 s2
  | _, _ => simpBAnd m s1 s2

theorem simpULeaf_clean (m u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ) (p1 p2 : Bool)
    (hu : u < m) (hv : v < m) (huv : u ≠ v) (hvn : v ≠ n0) :
    ∀ g ∈ (simpULeaf m u pu v pv n0 p1 p2).1,
      (g.a < m ∧ g.b < m ∧ g.a ≠ g.b) ∧ ¬ ((g.a = u ∧ g.b = n0) ∨ (g.a = n0 ∧ g.b = u)) := by
  intro g hg
  simp only [simpULeaf] at hg
  split_ifs at hg <;> simp at hg
  subst hg
  refine ⟨⟨hu, hv, huv⟩, ?_⟩
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · exact hvn h
  · exact huv h.symm

theorem simpUAnd_clean (m u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ) (s1 s2 : BStat)
    (hu : u < m) (hv : v < m) (huv : u ≠ v) (hvn : v ≠ n0)
    (h1 : s1.Valid m) (h2 : s2.Valid m) :
    ∀ g ∈ (simpUAnd m u pu v pv n0 s1 s2).1,
      (g.a < m ∧ g.b < m ∧ g.a ≠ g.b) ∧ ¬ ((g.a = u ∧ g.b = n0) ∨ (g.a = n0 ∧ g.b = u)) := by
  intro g hg
  cases s1 with
  | const c => exact ⟨simpBAnd_clean m _ _ h1 h2 g hg, fun h => by simp [simpUAnd, simpBAnd] at hg⟩
  | wire j pj =>
    cases s2 with
    | const c => exact ⟨simpBAnd_clean m _ _ h1 h2 g hg, fun h => by simp [simpUAnd, simpBAnd] at hg⟩
    | wire k pk =>
      simp only [simpUAnd] at hg
      split_ifs at hg with hjk hkj
      · exact simpULeaf_clean m u pu v pv n0 pj pk hu hv huv hvn g hg
      · exact simpULeaf_clean m u pu v pv n0 pk pj hu hv huv hvn g hg
      · refine ⟨simpBAnd_clean m _ _ h1 h2 g hg, ?_⟩
        simp only [simpBAnd] at hg
        split_ifs at hg <;> simp at hg
        subst hg
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hjk ⟨rfl, rfl⟩
        · exact hkj ⟨rfl, rfl⟩

theorem simpULeaf_sound (w : List Bool) (u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ)
    (p1 p2 : Bool) (hu : u < w.length) (hn0 : n0 < w.length)
    (hw0 : w.getD n0 false = ((xor (w.getD u false) pu) && (xor (w.getD v false) pv))) :
    (simpULeaf w.length u pu v pv n0 p1 p2).2.Valid
      (w.length + (simpULeaf w.length u pu v pv n0 p1 p2).1.toList.length) ∧
    (simpULeaf w.length u pu v pv n0 p1 p2).2.val
      (bwires (simpULeaf w.length u pu v pv n0 p1 p2).1.toList w) =
      ((xor (w.getD u false) p1) && (xor (w.getD n0 false) p2)) := by
  simp only [simpULeaf]
  by_cases hp1 : p1 = pu
  · subst hp1
    cases p2
    · simp only [↓reduceIte, Bool.false_eq_true, Option.toList_none, List.length_nil, Nat.add_zero,
        BStat.Valid, BStat.val, bwires, List.foldl_nil, Bool.bne_false]
      refine ⟨hn0, ?_⟩
      rw [hw0]
      cases w.getD u false <;> cases p1 <;> cases w.getD v false <;> cases pv <;> rfl
    · simp only [↓reduceIte, Option.toList_some, List.length_singleton, BStat.Valid,
        lt_add_iff_pos_right, zero_lt_one, true_and, bwires, List.foldl_cons, List.foldl_nil,
        BStat.val, BGate.eval]
      rw [getD_snoc_eq, Bool.xor_false, hw0]
      cases w.getD u false <;> cases p1 <;> cases w.getD v false <;> cases pv <;> rfl
  · cases p2
    · simp only [hp1, ↓reduceIte, Bool.false_eq_true, BStat.Valid, BStat.val, Bool.bne_false,
        true_and]
      rw [hw0]
      cases w.getD u false <;> cases pu <;> cases p1 <;> cases w.getD v false <;> cases pv <;>
        simp_all
    · simp only [hp1, ↓reduceIte, Option.toList_none, List.length_nil, Nat.add_zero, BStat.Valid,
        BStat.val, bwires, List.foldl_nil]
      refine ⟨hu, ?_⟩
      rw [hw0]
      cases w.getD u false <;> cases pu <;> cases p1 <;> cases w.getD v false <;> cases pv <;>
        simp_all

theorem simpUAnd_sound (w : List Bool) (u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (n0 : ℕ)
    (s1 s2 : BStat) (hu : u < w.length) (hn0 : n0 < w.length)
    (hw0 : w.getD n0 false = ((xor (w.getD u false) pu) && (xor (w.getD v false) pv)))
    (h1 : s1.Valid w.length) (h2 : s2.Valid w.length) :
    (simpUAnd w.length u pu v pv n0 s1 s2).2.Valid
      (w.length + (simpUAnd w.length u pu v pv n0 s1 s2).1.toList.length) ∧
    (simpUAnd w.length u pu v pv n0 s1 s2).2.val
      (bwires (simpUAnd w.length u pu v pv n0 s1 s2).1.toList w) =
      (s1.val w && s2.val w) := by
  cases s1 with
  | const c => exact simpBAnd_sound w _ _ h1 h2
  | wire j pj =>
    cases s2 with
    | const c => exact simpBAnd_sound w _ _ h1 h2
    | wire k pk =>
      simp only [simpUAnd]
      split_ifs with hjk hkj
      · obtain ⟨hju, hkn⟩ := hjk
        subst hju; subst hkn
        exact simpULeaf_sound w j pu v pv k pj pk hu hn0 hw0
      · obtain ⟨hjn, hku⟩ := hkj
        subst hjn; subst hku
        have hs := simpULeaf_sound w k pu v pv j pk pj hu hn0 hw0
        refine ⟨hs.1, ?_⟩
        rw [hs.2, Bool.and_comm]
        rfl
      · exact simpBAnd_sound w _ _ h1 h2

def elimUStep (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool)
    (acc : List BStat × List BGate) (g : BGate) : List BStat × List BGate :=
  let s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
    else acc.1.getD g.a (BStat.const false)
  let s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
    else acc.1.getD g.b (BStat.const false)
  let r := simpUAnd (n + acc.2.length) u pu v pv n s1 s2
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimU (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (gs : List BGate)
    (acc : List BStat × List BGate) : List BStat × List BGate :=
  gs.foldl (elimUStep n u pu v pv) acc

theorem inv_elimU (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (hu : u < n) (hv : v < n)
    (y' : List Bool) (hy' : y'.length = n)
    (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate),
      InvB n y' w acc → 1 ≤ acc.2.length →
      (bwires acc.2 y').getD n false =
        ((xor (y'.getD u false) pu) && (xor (y'.getD v false) pv)) →
      InvB n y' (bwires gs w) (elimU n u pu v pv gs acc) := by
  induction gs with
  | nil => intro w acc h _ _; exact h
  | cons g gs ih =>
    intro w acc h hlenpos hw0
    apply ih (w ++ [g.eval w]) (elimUStep n u pu v pv acc g)
    · obtain ⟨hl, hi⟩ := h
      set w' := bwires acc.2 y' with hw'
      have lw' : w'.length = n + acc.2.length := by rw [hw', length_bwires, hy']
      set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
        else acc.1.getD g.a (BStat.const false) with hs1
      set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
        else acc.1.getD g.b (BStat.const false) with hs2
      have hv1 : s1.Valid w'.length := by
        rw [lw']
        cases hpa : g.pa
        · rw [hs1, hpa]; exact (hi g.a).1
        · rw [hs1, hpa]; exact negBStat_valid _ (hi g.a).1
      have hv2 : s2.Valid w'.length := by
        rw [lw']
        cases hpb : g.pb
        · rw [hs2, hpb]; exact (hi g.b).1
        · rw [hs2, hpb]; exact negBStat_valid _ (hi g.b).1
      have hw0' : w'.getD n false = ((xor (w'.getD u false) pu) && (xor (w'.getD v false) pv)) := by
        rw [hw0, hw', getD_bwires _ _ _ (by omega), getD_bwires _ _ _ (by omega)]
      have hs := simpUAnd_sound w' u pu v pv n s1 s2 (by omega) (by omega) hw0' hv1 hv2
      rw [lw'] at hs
      set r := simpUAnd (n + acc.2.length) u pu v pv n s1 s2 with hr
      have hval1 : s1.val w' = xor (w.getD g.a false) g.pa := by
        cases hpa : g.pa
        · rw [hs1, hpa]; simpa using (hi g.a).2
        · rw [hs1, hpa]; simpa [negBStat_val] using congrArg not (hi g.a).2
      have hval2 : s2.val w' = xor (w.getD g.b false) g.pb := by
        cases hpb : g.pb
        · rw [hs2, hpb]; simpa using (hi g.b).2
        · rw [hs2, hpb]; simpa [negBStat_val] using congrArg not (hi g.b).2
      have hnew : bwires (acc.2 ++ r.1.toList) y' = bwires r.1.toList w' := by
        rw [bwires_append]
      obtain ⟨t, ht, _⟩ := bwires_start r.1.toList w'
      refine ⟨by simp [elimUStep, hl], ?_⟩
      intro i
      show ((acc.1 ++ [r.2]).getD i (BStat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
        ((acc.1 ++ [r.2]).getD i (BStat.const false)).val (bwires (acc.2 ++ r.1.toList) y') = _
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [getD_snoc_eq, hl, getD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hval1, hval2]; rfl⟩
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨BStat.valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, BStat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2
    · simp only [elimUStep, List.length_append]; omega
    · simp only [elimUStep]
      rw [bwires_append, getD_bwires _ _ _ (by rw [length_bwires, hy']; omega)]
      exact hw0

def NoPair (u n0 : ℕ) (gs : List BGate) : Prop :=
  ∀ p, 0 < p → ∀ g, gs[p]? = some g → ¬ ((g.a = u ∧ g.b = n0) ∨ (g.a = n0 ∧ g.b = u))

theorem elimUStep_inv (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (hu : u < n) (hv : v < n)
    (y' : List Bool) (hy' : y'.length = n) (g : BGate)
    (w : List Bool) (acc : List BStat × List BGate)
    (h : InvB n y' w acc) (hlenpos : 1 ≤ acc.2.length)
    (hw0 : (bwires acc.2 y').getD n false =
      ((xor (y'.getD u false) pu) && (xor (y'.getD v false) pv))) :
    InvB n y' (bwires [g] w) (elimUStep n u pu v pv acc g) ∧
    1 ≤ (elimUStep n u pu v pv acc g).2.length ∧
    (bwires (elimUStep n u pu v pv acc g).2 y').getD n false =
      ((xor (y'.getD u false) pu) && (xor (y'.getD v false) pv)) := by
  have h1 := inv_elimU n u pu v pv hu hv y' hy' [g] w acc h hlenpos hw0
  refine ⟨h1, by simp only [elimUStep, List.length_append]; omega, ?_⟩
  simp only [elimUStep]
  rw [bwires_append, getD_bwires _ _ _ (by rw [length_bwires, hy']; omega)]
  exact hw0

theorem clean_elimU (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool)
    (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (y' : List Bool) (hy' : y'.length = n) (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate),
      InvB n y' w acc → 1 ≤ acc.2.length →
      (bwires acc.2 y').getD n false =
        ((xor (y'.getD u false) pu) && (xor (y'.getD v false) pv)) →
      CleanB n acc.2 → NoPair u n acc.2 →
      CleanB n (elimU n u pu v pv gs acc).2 ∧ NoPair u n (elimU n u pu v pv gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ _ hcl hnp; exact ⟨hcl, hnp⟩
  | cons g gs ih =>
    intro w acc hinv hlenpos hw0 hcl hnp
    set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
      else acc.1.getD g.a (BStat.const false) with hs1
    set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
      else acc.1.getD g.b (BStat.const false) with hs2
    set r := simpUAnd (n + acc.2.length) u pu v pv n s1 s2
    have hv1 : s1.Valid (n + acc.2.length) := by
      cases hpa : g.pa
      · rw [hs1, hpa]; exact (hinv.2 g.a).1
      · rw [hs1, hpa]; exact negBStat_valid _ (hinv.2 g.a).1
    have hv2 : s2.Valid (n + acc.2.length) := by
      cases hpb : g.pb
      · rw [hs2, hpb]; exact (hinv.2 g.b).1
      · rw [hs2, hpb]; exact negBStat_valid _ (hinv.2 g.b).1
    have hcnew := simpUAnd_clean (n + acc.2.length) u pu v pv n s1 s2
      (by omega) (by omega) huv (by omega) hv1 hv2
    have hcl' : CleanB n (elimUStep n u pu v pv acc g).2 := by
      intro p g' hp
      change (acc.2 ++ r.1.toList)[p]? = some g' at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp; exact hcl p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        obtain ⟨_, hmem⟩ := toList_getElem? _ _ _ hp
        have hpl : p = acc.2.length := by omega
        rw [hpl]
        exact (hcnew g' hmem).1
    have hnp' : NoPair u n (elimUStep n u pu v pv acc g).2 := by
      intro p hp0 g' hp
      change (acc.2 ++ r.1.toList)[p]? = some g' at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp; exact hnp p hp0 g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        obtain ⟨_, hmem⟩ := toList_getElem? _ _ _ hp
        exact (hcnew g' hmem).2
    have hstep := elimUStep_inv n u pu v pv hu hv y' hy' g w acc hinv hlenpos hw0
    exact ih (bwires [g] w) (elimUStep n u pu v pv acc g) hstep.1 hstep.2.1 hstep.2.2 hcl' hnp'

theorem elimU_len (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (gs : List BGate) :
    ∀ acc : List BStat × List BGate,
      (elimU n u pu v pv gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimU]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimUStep n u pu v pv acc g)
    have h2 : (elimUStep n u pu v pv acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimUStep, List.length_append]
      have := toList_length_le (simpUAnd (n + acc.2.length) u pu v pv n
        (if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false))
        (if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false))).1
      omega
    have h3 : elimU n u pu v pv (g :: gs) acc = elimU n u pu v pv gs (elimUStep n u pu v pv acc g) := rfl
    rw [h3, List.length_cons]
    omega

theorem elimU_head (n u : ℕ) (pu : Bool) (v : ℕ) (pv : Bool) (g0 : BGate) (gs : List BGate) :
    ∀ (st : List BStat) (pre : List BGate),
      (elimU n u pu v pv gs (st, g0 :: pre)).2[0]? = some g0 := by
  induction gs with
  | nil => intro st pre; simp [elimU]
  | cons g gs ih =>
    intro st pre
    have h3 : elimU n u pu v pv (g :: gs) (st, g0 :: pre) =
        elimU n u pu v pv gs (elimUStep n u pu v pv (st, g0 :: pre) g) := rfl
    rw [h3]
    change (elimU n u pu v pv gs (st ++ _, g0 :: (pre ++ _))).2[0]? = some g0
    exact ih _ _

theorem bwires_tail_noread {n : ℕ} (u : Fin n) (gs : List BGate)
    (hno : ∀ g ∈ gs, g.a ≠ u.val ∧ g.b ≠ u.val) :
    ∀ W W' : List Bool,
      W.length = W'.length ∧ (∀ w, w ≠ u.val → W.getD w false = W'.getD w false) →
      ∀ w, w ≠ u.val → (bwires gs W).getD w false = (bwires gs W').getD w false := by
  induction gs with
  | nil => intro W W' h w hwu; exact h.2 w hwu
  | cons g gs ih =>
    intro W W' ⟨hl, hagree⟩
    have hg := hno g List.mem_cons_self
    have heval : g.eval W = g.eval W' := by
      simp only [BGate.eval]
      rw [hagree g.a hg.1, hagree g.b hg.2]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (W ++ [g.eval W]) (W' ++ [g.eval W'])
    refine ⟨by simp [hl], ?_⟩
    intro w hwu
    by_cases hw : w = W.length
    · subst hw; rw [getD_snoc_eq, hl, getD_snoc_eq, heval]
    · rw [getD_snoc_ne _ _ _ _ hw, getD_snoc_ne _ _ _ _ (by omega)]
      exact hagree w hwu

theorem master_elim (n s : ℕ) (hn : 2 ≤ n) (f : BFn (n + 1))
    (hdep : ∀ i : Fin (n + 1), ∃ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) ≠ f x)
    (hnb : ∀ (u v : Fin (n + 1)) (c : Bool), u ≠ v →
      ∃ x : Fin (n + 1) → Bool, x v = c ∧ f (Function.update x u (!x u)) ≠ f x)
    (hnc : ∀ (u : Fin (n + 1)) (c : Bool),
      ∃ y y' : Fin n → Bool, f (u.insertNth c y) ≠ f (u.insertNth c y'))
    (hs : HasBSize (n + 1) f s) :
    ∃ u : Fin (n + 1),
      let f0 : BFn n := fun y => f (u.insertNth false y)
      let f1 : BFn n := fun y => f (u.insertNth true y)
      (4 ≤ s ∧ HasBSize n f0 (s - 4) ∧ HasBSize n f1 (s - 2)) ∨
      (4 ≤ s ∧ HasBSize n f1 (s - 4) ∧ HasBSize n f0 (s - 2)) ∨
      (3 ≤ s ∧ HasBSize n f0 (s - 3) ∧ HasBSize n f1 (s - 3)) := by
  obtain ⟨gs, o, po, hcl, hlen, hev, hmin_len⟩ := exists_min_cleanB (n + 1) f s hs
  have hdl := dep_lower_b (n + 1) f hdep gs.length ⟨gs, o, po, hcl, le_rfl, hev⟩
  have hglen_pos : 1 ≤ gs.length := by omega
  rcases gs with _ | ⟨g0, gs'⟩
  · simp at hglen_pos
  · have hg0 := hcl 0 g0 rfl
    simp only [Nat.add_zero] at hg0
    let u := g0.a
    let pu := g0.pa
    let v := g0.b
    let pv := g0.pb
    have hu : u < n + 1 := hg0.1
    have hv : v < n + 1 := hg0.2.1
    have huv : u ≠ v := hg0.2.2
    let uF : Fin (n + 1) := ⟨u, hu⟩
    let vF : Fin (n + 1) := ⟨v, hv⟩
    have huvF : uF ≠ vF := fun e => huv (congrArg Fin.val e)
    let initU : List BStat := idBStats (n + 1) ++ [BStat.wire (n + 1) false]
    set accU := elimU (n + 1) u pu v pv gs' (initU, [g0]) with haccU
    have hinv_start : ∀ x : Fin (n + 1) → Bool,
        InvB (n + 1) (List.ofFn x) (bwires [g0] (List.ofFn x)) (initU, [g0]) := by
      intro x
      refine ⟨by simp [initU, idBStats, length_bwires], ?_⟩
      intro i
      by_cases hi : i < n + 1
      · have e1 : initU.getD i (BStat.const false) = BStat.wire i false := by
          simp only [initU, idBStats]
          rw [List.getD_append _ _ _ _ (by simp [hi]), getD_ofFn _ _ _ hi]
        have e2 : (bwires [g0] (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
          rw [getD_bwires _ _ _ (by simp [hi]), getD_ofFn _ _ _ hi]
        rw [e1, e2]
        refine ⟨by simp [BStat.Valid]; omega, ?_⟩
        simp only [BStat.val]
        rw [getD_bwires _ _ _ (by simp [hi]), getD_ofFn _ _ _ hi]
        simp
      · by_cases hieq : i = n + 1
        · subst hieq
          have e1 : initU.getD (n + 1) (BStat.const false) = BStat.wire (n + 1) false := by
            simp only [initU, idBStats]
            rw [getD_snoc_len _ _ _ _ (by simp)]
          rw [e1]
          refine ⟨by simp [BStat.Valid], ?_⟩
          simp only [BStat.val, Bool.xor_false]
        · have e1 : initU.getD i (BStat.const false) = BStat.const false := by
            simp only [initU, idBStats]
            exact List.getD_eq_default _ _ (by simp; omega)
          have e2 : (bwires [g0] (List.ofFn x)).getD i false = false :=
            List.getD_eq_default _ _ (by rw [length_bwires]; simp; omega)
          rw [e1, e2]
          exact ⟨trivial, rfl⟩
    have hw0_start : ∀ x : Fin (n + 1) → Bool,
        (bwires [g0] (List.ofFn x)).getD (n + 1) false =
          ((xor ((List.ofFn x).getD u false) pu) && (xor ((List.ofFn x).getD v false) pv)) := by
      intro x
      simp only [bwires, List.foldl_cons, List.foldl_nil, BGate.eval]
      rw [getD_snoc_len _ _ _ _ (by simp)]
    have hinvU : ∀ x : Fin (n + 1) → Bool,
        InvB (n + 1) (List.ofFn x) (bwires (g0 :: gs') (List.ofFn x)) accU := by
      intro x
      have : bwires (g0 :: gs') (List.ofFn x) = bwires gs' (bwires [g0] (List.ofFn x)) := rfl
      rw [this]
      exact inv_elimU (n + 1) u pu v pv hu hv (List.ofFn x) (by simp) gs' _ _
        (hinv_start x) (by simp) (hw0_start x)
    have hclnpU : CleanB (n + 1) accU.2 ∧ NoPair u (n + 1) accU.2 := by
      refine clean_elimU (n + 1) u pu v pv hu hv huv (List.ofFn fun _ : Fin (n + 1) => false)
        (by simp) gs' _ _ (hinv_start _) (by simp) (hw0_start _) ?_ ?_
      · intro p g hp
        cases p with
        | zero => simp at hp; subst hp; exact hg0
        | succ p => simp at hp
      · intro p hp0 g hp
        cases p with
        | zero => omega
        | succ p => simp at hp
    have hlenU : accU.2.length ≤ (g0 :: gs').length := by
      have := elimU_len (n + 1) u pu v pv gs' (initU, [g0])
      rw [← haccU] at this
      simpa [Nat.add_comm] using this
    have hheadU : accU.2[0]? = some g0 := by
      rw [haccU]; exact elimU_head (n + 1) u pu v pv g0 gs' initU []
    cases hstU : accU.1.getD o (BStat.const false) with
    | const d =>
      exfalso
      obtain ⟨x, hx⟩ := hdep ⟨0, by omega⟩
      apply hx
      have e1 := ((hinvU (Function.update x ⟨0, by omega⟩ (!x ⟨0, by omega⟩))).2 o).2
      have e2 := ((hinvU x).2 o).2
      rw [hstU] at e1 e2
      simp only [BStat.val] at e1 e2
      rw [← hev (Function.update x ⟨0, by omega⟩ (!x ⟨0, by omega⟩)), ← hev x, ← e1, ← e2]
    | wire oU po' =>
      let gsU := accU.2
      let poU := xor po' po
      have hheadU' : gsU[0]? = some g0 := hheadU
      have hgsU_len : gsU.length ≤ s := le_trans hlenU hlen
      have hevU : ∀ x : Fin (n + 1) → Bool,
          xor ((bwires gsU (List.ofFn x)).getD oU false) poU = f x := by
        intro x
        have e1 := ((hinvU x).2 o).2
        rw [hstU] at e1
        simp only [BStat.val] at e1
        exact xor_out_eq _ po' po _ (f x) e1 (hev x)
      have hminU : ∀ p < gsU.length, n + 1 + p = oU ∨
          ∃ (q : ℕ) (g : BGate), gsU[q]? = some g ∧ (g.a = n + 1 + p ∨ g.b = n + 1 + p) := by
        apply min_cleanB_used (n + 1) f gsU oU poU hclnpU.1 hevU
        intro gs1 o1 po1 hcl1 hev1
        exact le_trans hlenU (hmin_len gs1 o1 po1 hcl1 hev1)
      have hoU_ne_u : oU ≠ u := by
        intro e
        subst e
        obtain ⟨y, y', hne⟩ := hnc uF false
        apply hne
        rw [← hevU (uF.insertNth false y), ← hevU (uF.insertNth false y')]
        rw [getD_bwires _ _ _ (by simp [hu]), getD_bwires _ _ _ (by simp [hu]),
          getD_ofFn _ _ _ hu, getD_ofFn _ _ _ hu]
        simp [uF, Fin.insertNth_apply_same]
      have hoU_ne_0 : oU ≠ n + 1 := by
        intro e
        obtain ⟨y, y', hne⟩ := hnc uF pu
        apply hne
        have heval0 : ∀ z : Fin n → Bool,
            (bwires gsU (List.ofFn (uF.insertNth pu z))).getD (n + 1) false = false := by
          intro z
          rcases hgsU : gsU with _ | ⟨g0', gsU'⟩
          · rw [hgsU] at hheadU'; simp at hheadU'
          · have hg0_eq : g0' = g0 := by rw [hgsU] at hheadU'; simpa using hheadU'
            change (bwires gsU' (List.ofFn (uF.insertNth pu z) ++ [g0'.eval (List.ofFn (uF.insertNth pu z))])).getD (n + 1) false = false
            rw [getD_bwires _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
            simp only [BGate.eval]
            rw [hg0_eq, getD_ofFn _ _ _ hu]
            have hxu : ((uF.insertNth pu z : Fin (n + 1) → Bool) ⟨g0.a, hu⟩) = pu :=
              Fin.insertNth_apply_same (α := fun _ => Bool) uF pu z
            dsimp only [pu] at hxu
            rw [hxu]
            cases g0.pa <;> simp
        rw [← hevU (uF.insertNth pu y), ← hevU (uF.insertNth pu y'), e, heval0 y, heval0 y']
      have hk_ex : ∃ (k : ℕ) (gk : BGate), 0 < k ∧ gsU[k]? = some gk ∧ (gk.a = u ∨ gk.b = u) := by
        rcases hgsU : gsU with _ | ⟨g0', gsU'⟩
        · rw [hgsU] at hheadU'; simp at hheadU'
        · have hg0_eq : g0' = g0 := by rw [hgsU] at hheadU'; simpa using hheadU'
          rw [hg0_eq] at hgsU
          by_contra hno_k
          push Not at hno_k
          have hno' : ∀ g ∈ gsU', g.a ≠ u ∧ g.b ≠ u := by
            intro g hg
            obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
            exact hno_k (q + 1) g (by omega) (by simpa using hq)
          obtain ⟨x, hxv, hxne⟩ := hnb uF vF pv huvF
          apply hxne
          let x' := Function.update x uF (!x uF)
          have hg0_eval : g0.eval (List.ofFn x') = g0.eval (List.ofFn x) := by
            simp only [BGate.eval]
            have h1 : (List.ofFn x').getD g0.b false = pv := by
              rw [getD_ofFn _ _ _ hv]
              simpa [x', vF, Function.update_of_ne huvF.symm] using hxv
            have h2 : (List.ofFn x).getD g0.b false = pv := by
              rw [getD_ofFn _ _ _ hv]
              simpa [vF] using hxv
            rw [h1, h2]
            dsimp only [pv]
            cases g0.pb <;> simp
          have hbw : (bwires (g0 :: gsU') (List.ofFn x')).getD oU false =
              (bwires (g0 :: gsU') (List.ofFn x)).getD oU false := by
            change (bwires gsU' (List.ofFn x' ++ [g0.eval (List.ofFn x')])).getD oU false =
              (bwires gsU' (List.ofFn x ++ [g0.eval (List.ofFn x)])).getD oU false
            apply bwires_tail_noread uF gsU' hno'
            · refine ⟨by simp, ?_⟩
              intro w hwu
              by_cases hwn : w < n + 1
              · rw [List.getD_append _ _ _ _ (by simp; omega),
                  List.getD_append _ _ _ _ (by simp; omega),
                  getD_ofFn _ _ _ hwn, getD_ofFn _ _ _ hwn]
                exact Function.update_of_ne (fun e => hwu (congrArg Fin.val e)) _ x
              · by_cases hweq : w = n + 1
                · subst hweq
                  rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hg0_eval]
                · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
            · exact hoU_ne_u
          rw [← hevU x', ← hevU x, hgsU]
          exact congrArg (fun b => xor b poU) hbw
      obtain ⟨k, gk, hkpos, hk, hkm⟩ := hk_ex
      have hklt : k < gsU.length := (List.getElem?_eq_some_iff.1 hk).1
      have hh_ex : ∃ (h : ℕ) (gh : BGate), 0 < h ∧ gsU[h]? = some gh ∧
          (gh.a = n + 1 ∨ gh.b = n + 1) := by
        rcases hminU 0 (by
          rcases hgsU : gsU with _ | ⟨_, _⟩
          · rw [hgsU] at hheadU'; simp at hheadU'
          · simp) with hcon | ⟨h, gh, hh, hhm⟩
        · exact absurd hcon (by omega)
        · have hhcl := hclnpU.1 h gh hh
          have hhpos : 0 < h := by rcases hhm with ha | hb <;> omega
          exact ⟨h, gh, hhpos, hh, hhm⟩
      obtain ⟨h, gh, hhpos, hh, hhm⟩ := hh_ex
      have hkh : k ≠ h := by
        intro e
        subst e
        rw [hk] at hh
        cases hh
        apply hclnpU.2 k hkpos gk hk
        rcases hkm with h1 | h2 <;> rcases hhm with h3 | h4
        · exact absurd (h1.symm.trans h3) (by omega)
        · exact Or.inl ⟨h1, h4⟩
        · exact Or.inr ⟨h3, h2⟩
        · exact absurd (h2.symm.trans h4) (by omega)
      let pk : Bool := if gk.a = u then gk.pa else gk.pb
      have run_c : ∀ c : Bool,
          let accC := elimB n gsU (initAt uF c, [])
          HasBSize n (fun y => f (uF.insertNth c y)) accC.2.length := by
        intro c
        set accC := elimB n gsU (initAt uF c, []) with haccC
        have hinvC : ∀ y : Fin n → Bool,
            InvB n (List.ofFn y) (bwires gsU (List.ofFn (uF.insertNth c y))) accC :=
          fun y => inv_elimB n (List.ofFn y) (by simp) gsU _ _ (invB_initAt uF c y)
        have hclC : CleanB n accC.2 :=
          clean_elimB n (List.ofFn fun _ : Fin n => false) (by simp) gsU _ _
            (invB_initAt uF c _) (by intro p g' hp; simp at hp)
        cases hstC : accC.1.getD oU (BStat.const false) with
        | const d =>
          exfalso
          obtain ⟨y, y', hne⟩ := hnc uF c
          apply hne
          have e1 := ((hinvC y).2 oU).2
          have e2 := ((hinvC y').2 oU).2
          rw [hstC] at e1 e2
          simp only [BStat.val] at e1 e2
          rw [← hevU (uF.insertNth c y), ← hevU (uF.insertNth c y'), ← e1, ← e2]
        | wire j pj =>
          refine ⟨accC.2, j, xor pj poU, hclC, le_rfl, ?_⟩
          intro y
          have e1 := ((hinvC y).2 oU).2
          rw [hstC] at e1
          simp only [BStat.val] at e1
          exact xor_out_eq _ pj poU _ (f (uF.insertNth c y)) e1 (hevU (uF.insertNth c y))
      have h_u_at : ∀ c p, (stepAcc n gsU (initAt uF c, []) p).1.getD u (BStat.const false) =
          BStat.const c := by
        intro c p
        unfold stepAcc
        rw [elimB_fst_getD _ _ _ _ _ (by simp [initAt, hu])]
        exact initAt_getD_eq uF c
      have h_drop_0 : ∀ c, isDroppedAt n gsU (initAt uF c, []) 0 := by
        intro c
        refine ⟨g0, hheadU', elimBStep_none_of_const_left _ _ _ c (h_u_at c 0)⟩
      have h_drop_k : ∀ c, isDroppedAt n gsU (initAt uF c, []) k := by
        intro c
        refine ⟨gk, hk, ?_⟩
        rcases hkm with ha | hb
        · exact elimBStep_none_of_const_left _ _ _ c (ha ▸ h_u_at c k)
        · exact elimBStep_none_of_const_right _ _ _ c (hb ▸ h_u_at c k)
      have hinit_lenU : ∀ c, (initAt uF c).length = n + 1 := by intro c; simp [initAt]
      have h_const_0 : ∀ q, 1 ≤ q →
          (stepAcc n gsU (initAt uF pu, []) q).1.getD (n + 1) (BStat.const false) =
          BStat.const false := by
        intro q hq
        rw [stepAcc_getD_ge n gsU (initAt uF pu, []) 1 q (n + 1) hq (by simp [initAt]; omega)]
        have hs1 := stepAcc_succ_getD n gsU (initAt uF pu, []) 0 g0 hheadU' (BStat.const false)
        rw [hinit_lenU pu, Nat.add_zero] at hs1
        rw [hs1]
        exact elimBStep_const_of_const_left _ _ _ (h_u_at pu 0)
      have h_drop_h : isDroppedAt n gsU (initAt uF pu, []) h := by
        refine ⟨gh, hh, ?_⟩
        have hc0 := h_const_0 h hhpos
        rcases hhm with ha | hb
        · exact elimBStep_none_of_const_left _ _ _ false (ha ▸ hc0)
        · exact elimBStep_none_of_const_right _ _ _ false (hb ▸ hc0)
      have h_const_k : ∀ c, c = pk → ∀ q, k + 1 ≤ q →
          (stepAcc n gsU (initAt uF c, []) q).1.getD (n + 1 + k) (BStat.const false) =
          BStat.const false := by
        intro c hc q hq
        rw [stepAcc_getD_ge n gsU (initAt uF c, []) (k + 1) q (n + 1 + k) hq
          (by simp [initAt]; omega)]
        have hsk := stepAcc_succ_getD n gsU (initAt uF c, []) k gk hk (BStat.const false)
        rw [hinit_lenU c] at hsk
        rw [hsk]
        by_cases ha : gk.a = u
        · have hpk : gk.pa = c := by simp [pk, ha, hc]
          exact elimBStep_const_of_const_left _ _ _ (ha ▸ hpk ▸ h_u_at c k)
        · have hb : gk.b = u := by rcases hkm with h1 | h2; exact absurd h1 ha; exact h2
          have hpk : gk.pb = c := by simp [pk, ha, hc]
          exact elimBStep_const_of_const_right _ _ _ (hb ▸ hpk ▸ h_u_at c k)
      have h_ne_out : ∀ c (p : ℕ), p < gsU.length →
          (∀ q, p + 1 ≤ q → ∃ d, (stepAcc n gsU (initAt uF c, []) q).1.getD (n + 1 + p) (BStat.const false) =
            BStat.const d) →
          n + 1 + p ≠ oU := by
        intro c p hp hconst e
        obtain ⟨d, hd⟩ := hconst gsU.length hp
        obtain ⟨y, y', hne⟩ := hnc uF c
        apply hne
        have hinvC : ∀ z : Fin n → Bool,
            InvB n (List.ofFn z) (bwires gsU (List.ofFn (uF.insertNth c z)))
              (elimB n gsU (initAt uF c, [])) :=
          fun z => inv_elimB n (List.ofFn z) (by simp) gsU _ _ (invB_initAt uF c z)
        have h1 := ((hinvC y).2 oU).2
        have h2 := ((hinvC y').2 oU).2
        have hacc_eq : (elimB n gsU (initAt uF c, [])).1.getD oU (BStat.const false) = BStat.const d := by
          rw [← e]
          have htake : gsU = gsU.take gsU.length := List.take_length.symm
          change (elimB n gsU (initAt uF c, [])).1.getD (n + 1 + p) (BStat.const false) = _
          rw [htake]
          exact hd
        rw [hacc_eq] at h1 h2
        simp only [BStat.val] at h1 h2
        rw [← hevU (uF.insertNth c y), ← hevU (uF.insertNth c y'), ← h1, ← h2]
      have h_bsize_of_drop : ∀ (c : Bool) (D : Finset ℕ),
          (∀ p ∈ D, isDroppedAt n gsU (initAt uF c, []) p) →
          D.card ≤ s ∧ HasBSize n (fun y => f (uF.insertNth c y)) (s - D.card) := by
        intro c D hD
        have hle := dropped_le n gsU (initAt uF c, []) D hD
        simp only [List.length_nil, zero_add] at hle
        have hb := run_c c
        refine ⟨by omega, ?_⟩
        obtain ⟨gsC, oC, poC, hclC, hlenC, hevC⟩ := hb
        exact ⟨gsC, oC, poC, hclC, by omega, hevC⟩
      refine ⟨uF, ?_⟩
      by_cases hpk : pk = pu
      · have hb_not : 2 ≤ s ∧ HasBSize n (fun y => f (uF.insertNth (!pu) y)) (s - 2) := by
          have hD := h_bsize_of_drop (!pu) {0, k} (by
            intro p hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl
            · exact h_drop_0 (!pu)
            · exact h_drop_k (!pu))
          rw [Finset.card_pair (Nat.ne_of_lt hkpos)] at hD
          exact hD
        have hko : n + 1 + k ≠ oU :=
          h_ne_out pu k hklt (fun q hq => ⟨false, h_const_k pu hpk.symm q hq⟩)
        rcases hminU k hklt with hcon | ⟨m, gm, hm, hmm⟩
        · exact absurd hcon hko
        · have hmcl := hclnpU.1 m gm hm
          have hkm_lt : k < m := by rcases hmm with ha | hb <;> omega
          have hm_drop : isDroppedAt n gsU (initAt uF pu, []) m := by
            refine ⟨gm, hm, ?_⟩
            have hck := h_const_k pu hpk.symm m (by omega)
            rcases hmm with ha | hb
            · exact elimBStep_none_of_const_left _ _ _ false (ha ▸ hck)
            · exact elimBStep_none_of_const_right _ _ _ false (hb ▸ hck)
          have hb_pu : 4 ≤ s ∧ HasBSize n (fun y => f (uF.insertNth pu y)) (s - 4) := by
            by_cases hmh : m = h
            · subst hmh
              have hgm : gh = gm := by
                rw [hh] at hm
                injection hm
              subst hgm
              have hmlt : m < gsU.length := (List.getElem?_eq_some_iff.1 hm).1
              have h_const_m : ∀ q, m + 1 ≤ q → ∃ d,
                  (stepAcc n gsU (initAt uF pu, []) q).1.getD (n + 1 + m) (BStat.const false) =
                  BStat.const d := by
                intro q hq
                have hsm := stepAcc_succ_getD n gsU (initAt uF pu, []) m gh hh (BStat.const false)
                rw [hinit_lenU pu] at hsm
                have hacc_both : ∃ d, (elimBStep n (stepAcc n gsU (initAt uF pu, []) m) gh).1.getD
                    (stepAcc n gsU (initAt uF pu, []) m).1.length (BStat.const false) = BStat.const d := by
                  have hc0 := h_const_0 m hhpos
                  have hck := h_const_k pu hpk.symm m (by omega)
                  rcases hhm with ha0 | hb0 <;> rcases hmm with ham | hbm
                  · exact absurd (ha0.symm.trans ham) (by omega)
                  · exact elimBStep_const_of_both_const _ _ _ false false (ha0 ▸ hc0) (hbm ▸ hck)
                  · exact elimBStep_const_of_both_const _ _ _ false false (ham ▸ hck) (hb0 ▸ hc0)
                  · exact absurd (hb0.symm.trans hbm) (by omega)
                obtain ⟨d, hd⟩ := hacc_both
                refine ⟨d, ?_⟩
                rw [stepAcc_getD_ge n gsU (initAt uF pu, []) (m + 1) q (n + 1 + m) hq
                  (by rw [hinit_lenU pu]; omega)]
                rw [hsm, hd]
              have hmo : n + 1 + m ≠ oU := h_ne_out pu m hmlt h_const_m
              rcases hminU m hmlt with hcon | ⟨h', gh', hh', hhm'⟩
              · exact absurd hcon hmo
              · have hh'cl := hclnpU.1 h' gh' hh'
                have hmh' : m < h' := by rcases hhm' with ha | hb <;> omega
                have hdrop_h' : isDroppedAt n gsU (initAt uF pu, []) h' := by
                  refine ⟨gh', hh', ?_⟩
                  obtain ⟨d, hd⟩ := h_const_m h' (by omega)
                  rcases hhm' with ha | hb
                  · exact elimBStep_none_of_const_left _ _ _ d (ha ▸ hd)
                  · exact elimBStep_none_of_const_right _ _ _ d (hb ▸ hd)
                have hD := h_bsize_of_drop pu {0, k, m, h'} (by
                  intro p hp
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                  rcases hp with rfl | rfl | rfl | rfl
                  · exact h_drop_0 pu
                  · exact h_drop_k pu
                  · exact h_drop_h
                  · exact hdrop_h')
                have hcard4 : ({0, k, m, h'} : Finset ℕ).card = 4 := by
                  rw [Finset.card_insert_of_notMem (by simp; omega),
                    Finset.card_insert_of_notMem (by simp; omega),
                    Finset.card_pair (Nat.ne_of_lt hmh')]
                rw [hcard4] at hD
                exact hD
            · have hD := h_bsize_of_drop pu {0, k, h, m} (by
                intro p hp
                simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                rcases hp with rfl | rfl | rfl | rfl
                · exact h_drop_0 pu
                · exact h_drop_k pu
                · exact h_drop_h
                · exact hm_drop)
              have hcard4 : ({0, k, h, m} : Finset ℕ).card = 4 := by
                rw [Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_pair (fun e => hmh e.symm)]
              rw [hcard4] at hD
              exact hD
          cases hpu : pu
          · rw [hpu] at hb_pu hb_not
            exact Or.inl ⟨hb_pu.1, hb_pu.2, hb_not.2⟩
          · rw [hpu] at hb_pu hb_not
            exact Or.inr (Or.inl ⟨hb_pu.1, hb_pu.2, hb_not.2⟩)
      · have hpk_not : pk = !pu := by
          cases h1 : pk <;> cases h2 : pu <;> simp_all
        have hb_pu : 3 ≤ s ∧ HasBSize n (fun y => f (uF.insertNth pu y)) (s - 3) := by
          have hD := h_bsize_of_drop pu {0, k, h} (by
            intro p hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl | rfl
            · exact h_drop_0 pu
            · exact h_drop_k pu
            · exact h_drop_h)
          have hcard3 : ({0, k, h} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega),
              Finset.card_pair hkh]
          rw [hcard3] at hD
          exact hD
        have hko : n + 1 + k ≠ oU :=
          h_ne_out (!pu) k hklt (fun q hq => ⟨false, h_const_k (!pu) hpk_not.symm q hq⟩)
        rcases hminU k hklt with hcon | ⟨m, gm, hm, hmm⟩
        · exact absurd hcon hko
        · have hmcl := hclnpU.1 m gm hm
          have hkm_lt : k < m := by rcases hmm with ha | hb <;> omega
          have hm_drop : isDroppedAt n gsU (initAt uF (!pu), []) m := by
            refine ⟨gm, hm, ?_⟩
            have hck := h_const_k (!pu) hpk_not.symm m (by omega)
            rcases hmm with ha | hb
            · exact elimBStep_none_of_const_left _ _ _ false (ha ▸ hck)
            · exact elimBStep_none_of_const_right _ _ _ false (hb ▸ hck)
          have hb_not : 3 ≤ s ∧ HasBSize n (fun y => f (uF.insertNth (!pu) y)) (s - 3) := by
            have hD := h_bsize_of_drop (!pu) {0, k, m} (by
              intro p hp
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl | rfl
              · exact h_drop_0 (!pu)
              · exact h_drop_k (!pu)
              · exact hm_drop)
            have hcard3 : ({0, k, m} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_pair (Nat.ne_of_lt hkm_lt)]
            rw [hcard3] at hD
            exact hD
          cases hpu : pu
          · rw [hpu] at hb_pu hb_not
            exact Or.inr (Or.inr ⟨hb_pu.1, hb_pu.2, hb_not.2⟩)
          · rw [hpu] at hb_pu hb_not
            exact Or.inr (Or.inr ⟨hb_pu.1, hb_not.2, hb_pu.2⟩)

def edgeFun {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  E.any (fun e => x e.1 && x e.2)

def orEdgeFun {n : ℕ} (L : List (Fin n)) (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  L.any (fun i => x i) || edgeFun E x

def adjE {n : ℕ} (E : List (Fin n × Fin n)) (i j : Fin n) : Bool :=
  E.any (fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i))

def effAdj {n : ℕ} (L : List (Fin n)) (E : List (Fin n × Fin n)) (i j : Fin n) : Bool :=
  !(L.any (· == i)) && !(L.any (· == j)) && adjE E i j

theorem edgeFun_eq_true_iff {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) :
    edgeFun E x = true ↔ ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
  simp [edgeFun, List.any_eq_true, Bool.and_eq_true]

theorem adjE_eq_true_iff {n : ℕ} (E : List (Fin n × Fin n)) (i j : Fin n) :
    adjE E i j = true ↔ ∃ e ∈ E, (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i) := by
  simp [adjE, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]

theorem edgeFun_eq_of_adj {n : ℕ} (E1 E2 : List (Fin n × Fin n))
    (h : ∀ i j : Fin n, adjE E1 i j = adjE E2 i j) (x : Fin n → Bool) :
    edgeFun E1 x = edgeFun E2 x := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro hx
    obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E1 x).1 hx
    have hadj : adjE E2 e.1 e.2 = true := by
      rw [← h]
      exact (adjE_eq_true_iff E1 e.1 e.2).2 ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e', he', (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E2 e.1 e.2).1 hadj
    · exact (edgeFun_eq_true_iff E2 x).2 ⟨e', he', ha ▸ h1, hb ▸ h2⟩
    · exact (edgeFun_eq_true_iff E2 x).2 ⟨e', he', ha ▸ h2, hb ▸ h1⟩
  · intro hx
    obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E2 x).1 hx
    have hadj : adjE E1 e.1 e.2 = true := by
      rw [h]
      exact (adjE_eq_true_iff E2 e.1 e.2).2 ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e', he', (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E1 e.1 e.2).1 hadj
    · exact (edgeFun_eq_true_iff E1 x).2 ⟨e', he', ha ▸ h1, hb ▸ h2⟩
    · exact (edgeFun_eq_true_iff E1 x).2 ⟨e', he', ha ▸ h2, hb ▸ h1⟩

theorem edgeFun_relabel {n m : ℕ} (E : List (Fin n × Fin n)) (π : Fin n → Fin m)
    (y : Fin m → Bool) :
    edgeFun E (y ∘ π) = edgeFun (E.map (fun e => (π e.1, π e.2))) y := by
  simp [edgeFun, List.any_map]
  rfl

theorem edgeFun_bsize_relabel_eq {n s : ℕ} (E1 E2 : List (Fin n × Fin n)) (π : Fin n → Fin n)
    (hadj : ∀ i j : Fin n, adjE (E1.map (fun e => (π e.1, π e.2))) i j = adjE E2 i j)
    (hs : HasBSize n (edgeFun E1) s) :
    HasBSize n (edgeFun E2) s := by
  apply bsize_congr (fun y => ?_) (bsize_relabel π (edgeFun E1) s hs)
  rw [edgeFun_relabel]
  exact edgeFun_eq_of_adj _ _ hadj y

theorem fin_succAbove_eq_or {n : ℕ} (u k : Fin (n + 1)) :
    k = u ∨ ∃ i : Fin n, u.succAbove i = k := by
  by_cases h : k = u
  · exact Or.inl h
  · exact Or.inr (Fin.exists_succAbove_eq h)

theorem edgeFun_insertNth_false {n : ℕ} (u : Fin (n + 1))
    (E : List (Fin (n + 1) × Fin (n + 1))) (E0 : List (Fin n × Fin n))
    (h : ∀ i j : Fin n, adjE E (u.succAbove i) (u.succAbove j) = adjE E0 i j)
    (y : Fin n → Bool) :
    edgeFun E (u.insertNth false y) = edgeFun E0 y := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro hx
    obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 hx
    have h1u : e.1 ≠ u := by
      intro eq1
      rw [eq1, Fin.insertNth_apply_same] at h1
      cases h1
    have h2u : e.2 ≠ u := by
      intro eq2
      rw [eq2, Fin.insertNth_apply_same] at h2
      cases h2
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq h1u
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h2u
    have yi : y i = true := by simpa [← hi, Fin.insertNth_apply_succAbove] using h1
    have yj : y j = true := by simpa [← hj, Fin.insertNth_apply_succAbove] using h2
    have hadj : adjE E0 i j = true := by
      rw [← h, hi, hj]
      exact (adjE_eq_true_iff E e.1 e.2).2 ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e', he', (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E0 i j).1 hadj
    · exact (edgeFun_eq_true_iff E0 y).2 ⟨e', he', ha ▸ yi, hb ▸ yj⟩
    · exact (edgeFun_eq_true_iff E0 y).2 ⟨e', he', ha ▸ yj, hb ▸ yi⟩
  · intro hx
    obtain ⟨e', he', h1, h2⟩ := (edgeFun_eq_true_iff E0 y).1 hx
    have hadj : adjE E (u.succAbove e'.1) (u.succAbove e'.2) = true := by
      rw [h]
      exact (adjE_eq_true_iff E0 e'.1 e'.2).2 ⟨e', he', Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ :=
        (adjE_eq_true_iff E (u.succAbove e'.1) (u.succAbove e'.2)).1 hadj
    · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
      · simpa [ha, Fin.insertNth_apply_succAbove] using h1
      · simpa [hb, Fin.insertNth_apply_succAbove] using h2
    · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
      · simpa [ha, Fin.insertNth_apply_succAbove] using h2
      · simpa [hb, Fin.insertNth_apply_succAbove] using h1

theorem hasBSize_edgeFun_insertNth_false {n s : ℕ} (u : Fin (n + 1))
    (E : List (Fin (n + 1) × Fin (n + 1))) (E0 : List (Fin n × Fin n))
    (h : ∀ i j : Fin n, adjE E (u.succAbove i) (u.succAbove j) = adjE E0 i j)
    (hs : HasBSize n (fun y => edgeFun E (u.insertNth false y)) s) :
    HasBSize n (edgeFun E0) s :=
  bsize_congr (edgeFun_insertNth_false u E E0 h) hs

theorem edgeFun_insertNth_true {n : ℕ} (u : Fin (n + 1))
    (E : List (Fin (n + 1) × Fin (n + 1))) (L : List (Fin n)) (E1 : List (Fin n × Fin n))
    (hnoLoop : adjE E u u = false)
    (hL : ∀ i : Fin n, adjE E u (u.succAbove i) = L.any (· == i))
    (hE : ∀ i j : Fin n,
      (!(L.any (· == i)) && !(L.any (· == j)) && adjE E (u.succAbove i) (u.succAbove j)) =
        effAdj L E1 i j)
    (y : Fin n → Bool) :
    edgeFun E (u.insertNth true y) = orEdgeFun L E1 y := by
  apply Bool.eq_iff_iff.2
  have hmem_L : ∀ i : Fin n, L.any (· == i) = true → y i = true → orEdgeFun L E1 y = true := by
    intro i hi hyi
    simp only [orEdgeFun, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    obtain ⟨k, hk, hki⟩ := List.any_eq_true.1 hi
    rw [beq_iff_eq] at hki
    exact Or.inl ⟨k, hk, hki ▸ hyi⟩
  constructor
  · intro hx
    obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 hx
    rcases fin_succAbove_eq_or u e.1 with h1u | ⟨i, hi⟩ <;>
        rcases fin_succAbove_eq_or u e.2 with h2u | ⟨j, hj⟩
    · have hloop := (adjE_eq_true_iff E u u).2 ⟨e, he, Or.inl ⟨h1u, h2u⟩⟩
      rw [hnoLoop] at hloop
      cases hloop
    · have hyj : y j = true := by simpa [← hj, Fin.insertNth_apply_succAbove] using h2
      have hadj : L.any (· == j) = true := by
        rw [← hL j, hj]
        exact (adjE_eq_true_iff E u e.2).2 ⟨e, he, Or.inl ⟨h1u, rfl⟩⟩
      exact hmem_L j hadj hyj
    · have hyi : y i = true := by simpa [← hi, Fin.insertNth_apply_succAbove] using h1
      have hadj : L.any (· == i) = true := by
        rw [← hL i, hi]
        exact (adjE_eq_true_iff E u e.1).2 ⟨e, he, Or.inr ⟨rfl, h2u⟩⟩
      exact hmem_L i hadj hyi
    · have hyi : y i = true := by simpa [← hi, Fin.insertNth_apply_succAbove] using h1
      have hyj : y j = true := by simpa [← hj, Fin.insertNth_apply_succAbove] using h2
      by_cases hLi : L.any (· == i) = true
      · exact hmem_L i hLi hyi
      · by_cases hLj : L.any (· == j) = true
        · exact hmem_L j hLj hyj
        · have hLi' : L.any (· == i) = false := Bool.eq_false_iff.2 hLi
          have hLj' : L.any (· == j) = false := Bool.eq_false_iff.2 hLj
          have hadjE : adjE E (u.succAbove i) (u.succAbove j) = true := by
            rw [hi, hj]
            exact (adjE_eq_true_iff E e.1 e.2).2 ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
          have heff : effAdj L E1 i j = true := by
            rw [← hE i j, hLi', hLj', hadjE]
            rfl
          simp only [effAdj, Bool.and_eq_true] at heff
          obtain ⟨e', he', (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E1 i j).1 heff.2
          · exact Bool.or_eq_true_iff.2
              (Or.inr ((edgeFun_eq_true_iff E1 y).2 ⟨e', he', ha ▸ hyi, hb ▸ hyj⟩))
          · exact Bool.or_eq_true_iff.2
              (Or.inr ((edgeFun_eq_true_iff E1 y).2 ⟨e', he', ha ▸ hyj, hb ▸ hyi⟩))
  · intro hx
    simp only [orEdgeFun, Bool.or_eq_true] at hx
    rcases hx with hLx | hEx
    · obtain ⟨k, hk, hyk⟩ := List.any_eq_true.1 hLx
      have hLk : L.any (· == k) = true := List.any_eq_true.2 ⟨k, hk, beq_iff_eq.2 rfl⟩
      have hadj : adjE E u (u.succAbove k) = true := by rw [hL k, hLk]
      obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u (u.succAbove k)).1 hadj
      · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
        · simpa [ha, Fin.insertNth_apply_same]
        · simpa [hb, Fin.insertNth_apply_succAbove] using hyk
      · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
        · simpa [ha, Fin.insertNth_apply_succAbove] using hyk
        · simpa [hb, Fin.insertNth_apply_same]
    · obtain ⟨e', he', hy1, hy2⟩ := (edgeFun_eq_true_iff E1 y).1 hEx
      by_cases hL1 : L.any (· == e'.1) = true
      · obtain ⟨k, hk, hke⟩ := List.any_eq_true.1 hL1
        rw [beq_iff_eq] at hke
        have hLk : L.any (· == k) = true := List.any_eq_true.2 ⟨k, hk, beq_iff_eq.2 rfl⟩
        have hadj : adjE E u (u.succAbove k) = true := by rw [hL k, hLk]
        obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u (u.succAbove k)).1 hadj
        · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
          · simpa [ha, Fin.insertNth_apply_same]
          · simpa [hb, Fin.insertNth_apply_succAbove, hke] using hy1
        · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
          · simpa [ha, Fin.insertNth_apply_succAbove, hke] using hy1
          · simpa [hb, Fin.insertNth_apply_same]
      · by_cases hL2 : L.any (· == e'.2) = true
        · obtain ⟨k, hk, hke⟩ := List.any_eq_true.1 hL2
          rw [beq_iff_eq] at hke
          have hLk : L.any (· == k) = true := List.any_eq_true.2 ⟨k, hk, beq_iff_eq.2 rfl⟩
          have hadj : adjE E u (u.succAbove k) = true := by rw [hL k, hLk]
          obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u (u.succAbove k)).1 hadj
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simpa [ha, Fin.insertNth_apply_same]
            · simpa [hb, Fin.insertNth_apply_succAbove, hke] using hy2
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simpa [ha, Fin.insertNth_apply_succAbove, hke] using hy2
            · simpa [hb, Fin.insertNth_apply_same]
        · have hL1' : L.any (· == e'.1) = false := Bool.eq_false_iff.2 hL1
          have hL2' : L.any (· == e'.2) = false := Bool.eq_false_iff.2 hL2
          have heff : effAdj L E1 e'.1 e'.2 = true := by
            simp only [effAdj, hL1', hL2', Bool.not_false, Bool.true_and]
            exact (adjE_eq_true_iff E1 e'.1 e'.2).2 ⟨e', he', Or.inl ⟨rfl, rfl⟩⟩
          rw [← hE e'.1 e'.2] at heff
          simp only [Bool.and_eq_true] at heff
          obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ :=
              (adjE_eq_true_iff E (u.succAbove e'.1) (u.succAbove e'.2)).1 heff.2
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simpa [ha, Fin.insertNth_apply_succAbove] using hy1
            · simpa [hb, Fin.insertNth_apply_succAbove] using hy2
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simpa [ha, Fin.insertNth_apply_succAbove] using hy2
            · simpa [hb, Fin.insertNth_apply_succAbove] using hy1

theorem orEdgeFun_nil {n : ℕ} (E : List (Fin n × Fin n)) (x : Fin n → Bool) :
    orEdgeFun [] E x = edgeFun E x := rfl

theorem orEdgeFun_insertNth_false {n : ℕ} (u : Fin (n + 1))
    (L : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (L' : List (Fin n)) (E' : List (Fin n × Fin n))
    (hL : ∀ i : Fin n, L.any (· == u.succAbove i) = L'.any (· == i))
    (hE : ∀ i j : Fin n, effAdj L E (u.succAbove i) (u.succAbove j) = effAdj L' E' i j)
    (y : Fin n → Bool) :
    orEdgeFun L E (u.insertNth false y) = orEdgeFun L' E' y := by
  apply Bool.eq_iff_iff.2
  have step_L : ∀ i : Fin n, L'.any (· == i) = true → y i = true → orEdgeFun L E (u.insertNth false y) = true := by
    intro i hi hyi
    rw [← hL i] at hi
    obtain ⟨k, hk, hku⟩ := List.any_eq_true.1 hi
    rw [beq_iff_eq] at hku
    simp only [orEdgeFun, Bool.or_eq_true, List.any_eq_true]
    refine Or.inl ⟨k, hk, ?_⟩
    simpa [hku, Fin.insertNth_apply_succAbove] using hyi
  have step_L' : ∀ i : Fin n, L.any (· == u.succAbove i) = true → y i = true → orEdgeFun L' E' y = true := by
    intro i hi hyi
    rw [hL i] at hi
    obtain ⟨k, hk, hki⟩ := List.any_eq_true.1 hi
    rw [beq_iff_eq] at hki
    simp only [orEdgeFun, Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨k, hk, hki ▸ hyi⟩
  constructor
  · intro hx
    simp only [orEdgeFun, Bool.or_eq_true] at hx
    rcases hx with hLx | hEx
    · obtain ⟨k, hk, hxk⟩ := List.any_eq_true.1 hLx
      rcases fin_succAbove_eq_or u k with rfl | ⟨i, hi⟩
      · rw [Fin.insertNth_apply_same] at hxk; cases hxk
      · have hyi : y i = true := by simpa [← hi, Fin.insertNth_apply_succAbove] using hxk
        have hLi : L.any (· == u.succAbove i) = true :=
          List.any_eq_true.2 ⟨k, hk, beq_iff_eq.2 hi.symm⟩
        exact step_L' i hLi hyi
    · obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 hEx
      have h1u : e.1 ≠ u := by intro eq1; rw [eq1, Fin.insertNth_apply_same] at h1; cases h1
      have h2u : e.2 ≠ u := by intro eq2; rw [eq2, Fin.insertNth_apply_same] at h2; cases h2
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq h1u
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h2u
      have hyi : y i = true := by simpa [← hi, Fin.insertNth_apply_succAbove] using h1
      have hyj : y j = true := by simpa [← hj, Fin.insertNth_apply_succAbove] using h2
      by_cases hLi : L.any (· == u.succAbove i) = true
      · exact step_L' i hLi hyi
      · by_cases hLj : L.any (· == u.succAbove j) = true
        · exact step_L' j hLj hyj
        · have heff : effAdj L E (u.succAbove i) (u.succAbove j) = true := by
            simp only [effAdj, Bool.eq_false_iff.2 hLi, Bool.eq_false_iff.2 hLj, Bool.not_false, Bool.true_and]
            rw [hi, hj]
            exact (adjE_eq_true_iff E e.1 e.2).2 ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
          rw [hE i j] at heff
          simp only [effAdj, Bool.and_eq_true] at heff
          obtain ⟨e', he', (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E' i j).1 heff.2
          · exact Bool.or_eq_true_iff.2
              (Or.inr ((edgeFun_eq_true_iff E' y).2 ⟨e', he', ha ▸ hyi, hb ▸ hyj⟩))
          · exact Bool.or_eq_true_iff.2
              (Or.inr ((edgeFun_eq_true_iff E' y).2 ⟨e', he', ha ▸ hyj, hb ▸ hyi⟩))
  · intro hx
    simp only [orEdgeFun, Bool.or_eq_true] at hx
    rcases hx with hLx | hEx
    · obtain ⟨k, hk, hyk⟩ := List.any_eq_true.1 hLx
      exact step_L k (List.any_eq_true.2 ⟨k, hk, beq_iff_eq.2 rfl⟩) hyk
    · obtain ⟨e', he', hy1, hy2⟩ := (edgeFun_eq_true_iff E' y).1 hEx
      by_cases hL1 : L'.any (· == e'.1) = true
      · exact step_L e'.1 hL1 hy1
      · by_cases hL2 : L'.any (· == e'.2) = true
        · exact step_L e'.2 hL2 hy2
        · have heff : effAdj L' E' e'.1 e'.2 = true := by
            simp only [effAdj, Bool.eq_false_iff.2 hL1, Bool.eq_false_iff.2 hL2, Bool.not_false, Bool.true_and]
            exact (adjE_eq_true_iff E' e'.1 e'.2).2 ⟨e', he', Or.inl ⟨rfl, rfl⟩⟩
          rw [← hE e'.1 e'.2] at heff
          simp only [effAdj, Bool.and_eq_true] at heff
          obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ :=
              (adjE_eq_true_iff E (u.succAbove e'.1) (u.succAbove e'.2)).1 heff.2
          · refine Bool.or_eq_true_iff.2 (Or.inr ((edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩))
            · simpa [ha, Fin.insertNth_apply_succAbove] using hy1
            · simpa [hb, Fin.insertNth_apply_succAbove] using hy2
          · refine Bool.or_eq_true_iff.2 (Or.inr ((edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩))
            · simpa [ha, Fin.insertNth_apply_succAbove] using hy2
            · simpa [hb, Fin.insertNth_apply_succAbove] using hy1

theorem orEdgeFun_dep_all {n : ℕ} (L : List (Fin n)) (E : List (Fin n × Fin n))
    (hnoLoop : ∀ z : Fin n, adjE E z z = false)
    (hcov : ∀ w : Fin n, L.any (· == w) = true ∨
      ∃ v : Fin n, w ≠ v ∧ adjE E w v = true ∧ L.any (· == v) = false) :
    ∀ w : Fin n, ∃ x, orEdgeFun L E (Function.update x w (!x w)) ≠ orEdgeFun L E x := by
  intro w
  rcases hcov w with hw | ⟨v, hwv, hadj, hvL⟩
  · refine ⟨fun _ => false, ?_⟩
    have h0 : orEdgeFun L E (fun _ => false) = false := by simp [orEdgeFun, edgeFun]
    have h1 : orEdgeFun L E (Function.update (fun _ : Fin n => false) w true) = true := by
      simp only [orEdgeFun, Bool.or_eq_true, List.any_eq_true]
      obtain ⟨k, hk, hkw⟩ := List.any_eq_true.1 hw
      rw [beq_iff_eq] at hkw
      exact Or.inl ⟨k, hk, by simp [hkw]⟩
    simpa [h0, h1]
  · refine ⟨fun i => i == v, ?_⟩
    have h0 : orEdgeFun L E (fun i => i == v) = false := by
      apply Bool.eq_false_iff.2
      intro htr
      simp only [orEdgeFun, Bool.or_eq_true] at htr
      rcases htr with hL | hE
      · obtain ⟨k, hk, hkv⟩ := List.any_eq_true.1 hL
        rw [beq_iff_eq] at hkv
        have : L.any (· == v) = true := List.any_eq_true.2 ⟨k, hk, by simp [hkv]⟩
        rw [hvL] at this
        cases this
      · obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 hE
        rw [beq_iff_eq] at h1 h2
        have := (adjE_eq_true_iff E v v).2 ⟨e, he, Or.inl ⟨h1, h2⟩⟩
        rw [hnoLoop v] at this
        cases this
    have h1 : orEdgeFun L E (Function.update (fun i => i == v) w (!(w == v))) = true := by
      have hwb : (w == v) = false := beq_false_of_ne hwv
      rw [hwb, Bool.not_false]
      obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E w v).1 hadj
      · refine Bool.or_eq_true_iff.2 (Or.inr ((edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩))
        · simp [ha]
        · simp [hb, hwv.symm]
      · refine Bool.or_eq_true_iff.2 (Or.inr ((edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩))
        · simp [ha, hwv.symm]
        · simp [hb]
    rw [h0, h1]
    decide

theorem edgeFun_dep_all {n : ℕ} (E : List (Fin n × Fin n))
    (hnoLoop : ∀ z : Fin n, adjE E z z = false)
    (hcov : ∀ w : Fin n, ∃ v : Fin n, w ≠ v ∧ adjE E w v = true) :
    ∀ w : Fin n, ∃ x, edgeFun E (Function.update x w (!x w)) ≠ edgeFun E x :=
  orEdgeFun_dep_all [] E hnoLoop (fun w => Or.inr (by obtain ⟨v, h1, h2⟩ := hcov w; exact ⟨v, h1, h2, rfl⟩))

theorem orEdgeFun_nonconst {n : ℕ} (L : List (Fin n)) (E : List (Fin n × Fin n))
    (hne : L.isEmpty = false ∨ E.isEmpty = false) :
    ∃ y y', orEdgeFun L E y ≠ orEdgeFun L E y' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : orEdgeFun L E (fun _ => false) = false := by simp [orEdgeFun, edgeFun]
  have h1 : orEdgeFun L E (fun _ => true) = true := by
    rcases hne with hL | hE
    · rcases L with _ | ⟨k, _⟩
      · cases hL
      · simp [orEdgeFun]
    · rcases E with _ | ⟨e, _⟩
      · cases hE
      · simp [orEdgeFun, edgeFun]
  rw [h0, h1]
  decide

theorem orEdgeFun_peel_one {n s : ℕ} (u : Fin (n + 1))
    (L : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (L' : List (Fin n)) (E' : List (Fin n × Fin n))
    (hdep : ∀ w : Fin (n + 1), ∃ x, orEdgeFun L E (Function.update x w (!x w)) ≠ orEdgeFun L E x)
    (hL : ∀ i : Fin n, L.any (· == u.succAbove i) = L'.any (· == i))
    (hE : ∀ i j : Fin n, effAdj L E (u.succAbove i) (u.succAbove j) = effAdj L' E' i j)
    (hne : L'.isEmpty = false ∨ E'.isEmpty = false)
    (hs : HasBSize (n + 1) (orEdgeFun L E) s) :
    1 ≤ s ∧ HasBSize n (orEdgeFun L' E') (s - 1) := by
  have heq := orEdgeFun_insertNth_false u L E L' E' hL hE
  have hnc : ∃ y y', orEdgeFun L E (u.insertNth false y) ≠ orEdgeFun L E (u.insertNth false y') := by
    obtain ⟨y, y', hy⟩ := orEdgeFun_nonconst L' E' hne
    refine ⟨y, y', ?_⟩
    rw [heq y, heq y']
    exact hy
  obtain ⟨hle, hs'⟩ := elim_var_at u false (orEdgeFun L E) (hdep u) hnc hs
  exact ⟨hle, bsize_congr heq hs'⟩

theorem edgeFun_nonblocking {n : ℕ} (E : List (Fin n × Fin n))
    (hnoLoop : ∀ z : Fin n, adjE E z z = false)
    (hcond : ∀ u v : Fin n, u ≠ v →
      (∃ w : Fin n, w ≠ u ∧ w ≠ v ∧ adjE E u w = true) ∧
      (adjE E u v = true ∨ ∃ w : Fin n, w ≠ u ∧ w ≠ v ∧ adjE E u w = true ∧ adjE E v w = false)) :
    ∀ (u v : Fin n) (c : Bool), u ≠ v →
      ∃ x, x v = c ∧ edgeFun E (Function.update x u (!x u)) ≠ edgeFun E x := by
  intro u v c huv
  obtain ⟨⟨wf, hwu, hwv, hadjf⟩, hct⟩ := hcond u v huv
  cases c
  · refine ⟨fun i => i == wf, ?_, ?_⟩
    · simp [hwv.symm]
    · have h0 : edgeFun E (fun i => i == wf) = false := by
        apply Bool.eq_false_iff.2
        intro ht
        obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 ht
        rw [beq_iff_eq] at h1 h2
        have := (adjE_eq_true_iff E wf wf).2 ⟨e, he, Or.inl ⟨h1, h2⟩⟩
        rw [hnoLoop wf] at this
        cases this
      have h1 : edgeFun E (Function.update (fun i => i == wf) u (!(u == wf))) = true := by
        have huw : (u == wf) = false := beq_false_of_ne hwu.symm
        rw [huw, Bool.not_false]
        obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u wf).1 hadjf
        · exact (edgeFun_eq_true_iff E _).2 ⟨e, he, by simp [ha], by simp [hb, hwu]⟩
        · exact (edgeFun_eq_true_iff E _).2 ⟨e, he, by simp [ha, hwu], by simp [hb]⟩
      rw [h0, h1]
      decide
  · rcases hct with hadjuv | ⟨wt, hwtu, hwtv, hadjuw, hnovw⟩
    · refine ⟨fun i => i == v, ?_, ?_⟩
      · simp
      · have h0 : edgeFun E (fun i => i == v) = false := by
          apply Bool.eq_false_iff.2
          intro ht
          obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 ht
          rw [beq_iff_eq] at h1 h2
          have := (adjE_eq_true_iff E v v).2 ⟨e, he, Or.inl ⟨h1, h2⟩⟩
          rw [hnoLoop v] at this
          cases this
        have h1 : edgeFun E (Function.update (fun i => i == v) u (!(u == v))) = true := by
          have huvb : (u == v) = false := beq_false_of_ne huv
          rw [huvb, Bool.not_false]
          obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u v).1 hadjuv
          · exact (edgeFun_eq_true_iff E _).2 ⟨e, he, by simp [ha], by simp [hb, huv.symm]⟩
          · exact (edgeFun_eq_true_iff E _).2 ⟨e, he, by simp [ha, huv.symm], by simp [hb]⟩
        rw [h0, h1]
        decide
    · refine ⟨fun i => (i == v) || (i == wt), ?_, ?_⟩
      · simp
      · have h0 : edgeFun E (fun i => (i == v) || (i == wt)) = false := by
          apply Bool.eq_false_iff.2
          intro ht
          obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 ht
          simp only [Bool.or_eq_true, beq_iff_eq] at h1 h2
          rcases h1 with h1' | h1' <;> rcases h2 with h2' | h2'
          · have h_vv := (adjE_eq_true_iff E v v).2 ⟨e, he, Or.inl ⟨h1', h2'⟩⟩
            rw [hnoLoop v] at h_vv; cases h_vv
          · have h_vw := (adjE_eq_true_iff E v wt).2 ⟨e, he, Or.inl ⟨h1', h2'⟩⟩
            rw [hnovw] at h_vw; cases h_vw
          · have h_wv := (adjE_eq_true_iff E v wt).2 ⟨e, he, Or.inr ⟨h1', h2'⟩⟩
            rw [hnovw] at h_wv; cases h_wv
          · have h_ww := (adjE_eq_true_iff E wt wt).2 ⟨e, he, Or.inl ⟨h1', h2'⟩⟩
            rw [hnoLoop wt] at h_ww; cases h_ww
        have h1 : edgeFun E (Function.update (fun i => (i == v) || (i == wt)) u (!((u == v) || (u == wt)))) = true := by
          have hub : ((u == v) || (u == wt)) = false := by
            simp [beq_false_of_ne huv, beq_false_of_ne hwtu.symm]
          rw [hub, Bool.not_false]
          obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E u wt).1 hadjuw
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simp [ha]
            · simp [hb, hwtu]
          · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
            · simp [ha, hwtu]
            · simp [hb]
        rw [h0, h1]
        decide

theorem edgeFun_nonconst_insertNth {n : ℕ} (E : List (Fin (n + 1) × Fin (n + 1)))
    (hnoLoop : ∀ z : Fin (n + 1), adjE E z z = false)
    (hEdge : ∀ u : Fin (n + 1), ∃ a b : Fin (n + 1), a ≠ u ∧ b ≠ u ∧ adjE E a b = true) :
    ∀ (u : Fin (n + 1)) (c : Bool), ∃ y y', edgeFun E (u.insertNth c y) ≠ edgeFun E (u.insertNth c y') := by
  intro u c
  obtain ⟨a, b, hau, hbu, hadj⟩ := hEdge u
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : edgeFun E (u.insertNth c (fun _ => false)) = false := by
    apply Bool.eq_false_iff.2
    intro ht
    obtain ⟨e, he, h1, h2⟩ := (edgeFun_eq_true_iff E _).1 ht
    by_cases h1u : e.1 = u
    · by_cases h2u : e.2 = u
      · have := (adjE_eq_true_iff E u u).2 ⟨e, he, Or.inl ⟨h1u, h2u⟩⟩
        rw [hnoLoop u] at this; cases this
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h2u
        rw [← hj, Fin.insertNth_apply_succAbove] at h2
        cases h2
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq h1u
      rw [← hi, Fin.insertNth_apply_succAbove] at h1
      cases h1
  have h1 : edgeFun E (u.insertNth c (fun _ => true)) = true := by
    obtain ⟨ia, hia⟩ := Fin.exists_succAbove_eq hau
    obtain ⟨ib, hib⟩ := Fin.exists_succAbove_eq hbu
    obtain ⟨e, he, (⟨ha, hb⟩ | ⟨ha, hb⟩)⟩ := (adjE_eq_true_iff E a b).1 hadj
    · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
      · simpa [ha, ← hia, Fin.insertNth_apply_succAbove]
      · simpa [hb, ← hib, Fin.insertNth_apply_succAbove]
    · refine (edgeFun_eq_true_iff E _).2 ⟨e, he, ?_, ?_⟩
      · simpa [ha, ← hib, Fin.insertNth_apply_succAbove]
      · simpa [hb, ← hia, Fin.insertNth_apply_succAbove]
  rw [h0, h1]
  decide

def bitsFn {n : ℕ} (m : Fin (2 ^ n)) (i : Fin n) : Bool :=
  m.val.testBit i.val

theorem edgeFun_hpair_of_bits {n : ℕ} (E : List (Fin n × Fin n))
    (h : ∀ (u v : Fin n) (pu pv : Bool), u ≠ v →
      ∃ (mx : Fin (2 ^ n)) (bu bv : Bool),
        (xor (bitsFn mx u) pu && xor (bitsFn mx v) pv) = (xor bu pu && xor bv pv) ∧
        edgeFun E (bitsFn mx) ≠
          edgeFun E (fun i => if i == u then bu else if i == v then bv else bitsFn mx i)) :
    ∀ (u v : Fin n) (pu pv : Bool), u ≠ v →
      ∃ x y : Fin n → Bool,
        (∀ i, i ≠ u → i ≠ v → x i = y i) ∧
        ((xor (x u) pu && xor (x v) pv) = (xor (y u) pu && xor (y v) pv)) ∧
        edgeFun E x ≠ edgeFun E y := by
  intro u v pu pv huv
  obtain ⟨mx, bu, bv, heq, hne⟩ := h u v pu pv huv
  refine ⟨bitsFn mx, fun i => if i == u then bu else if i == v then bv else bitsFn mx i,
    ?_, ?_, hne⟩
  · intro i hiu hiv
    simp [hiu, hiv]
  · simpa [huv.symm] using heq

def E_P4 : List (Fin 4 × Fin 4) := [(0,1),(1,2),(2,3)]
def E_P5 : List (Fin 5 × Fin 5) := [(0,1),(1,2),(2,3),(3,4)]
def E_C5 : List (Fin 5 × Fin 5) := [(0,1),(1,2),(2,3),(3,4),(4,0)]
def E_C6 : List (Fin 6 × Fin 6) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)]
def E_fT : List (Fin 7 × Fin 7) := [(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
def E_G8 : List (Fin 8 × Fin 8) := [(0,1),(1,2),(2,3),(3,4),(4,0),(1,5),(2,6),(3,7),(5,7)]
def E_H8 : List (Fin 8 × Fin 8) := [(0,1),(2,3),(4,0),(4,2),(5,0),(5,3),(6,1),(6,2),(7,1),(7,3)]
def E_G9 : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

theorem P4_dep : ∀ i : Fin 4, ∃ x, edgeFun E_P4 (Function.update x i (!x i)) ≠ edgeFun E_P4 x :=
  edgeFun_dep_all E_P4 (by decide) (by decide)

theorem P4_pair : ∀ (u v : Fin 4) (pu pv : Bool), u ≠ v →
    ∃ x y : Fin 4 → Bool,
      (∀ i, i ≠ u → i ≠ v → x i = y i) ∧
      ((xor (x u) pu && xor (x v) pv) = (xor (y u) pu && xor (y v) pv)) ∧
      edgeFun E_P4 x ≠ edgeFun E_P4 y :=
  edgeFun_hpair_of_bits E_P4 (by decide)

theorem P4_lower (s : ℕ) (hs : HasBSize 4 (edgeFun E_P4) s) : 4 ≤ s :=
  lower_ge_n 4 (by omega) (edgeFun E_P4) P4_dep P4_pair s hs

theorem P5_dep : ∀ i : Fin 5, ∃ x, edgeFun E_P5 (Function.update x i (!x i)) ≠ edgeFun E_P5 x :=
  edgeFun_dep_all E_P5 (by decide) (by decide)

theorem P5_pair : ∀ (u v : Fin 5) (pu pv : Bool), u ≠ v →
    ∃ x y : Fin 5 → Bool,
      (∀ i, i ≠ u → i ≠ v → x i = y i) ∧
      ((xor (x u) pu && xor (x v) pv) = (xor (y u) pu && xor (y v) pv)) ∧
      edgeFun E_P5 x ≠ edgeFun E_P5 y :=
  edgeFun_hpair_of_bits E_P5 (by decide)

theorem P5_lower (s : ℕ) (hs : HasBSize 5 (edgeFun E_P5) s) : 5 ≤ s :=
  lower_ge_n 5 (by omega) (edgeFun E_P5) P5_dep P5_pair s hs

theorem adjE_symm {n : ℕ} (E : List (Fin n × Fin n)) (i j : Fin n) :
    adjE E i j = adjE E j i := by
  apply Bool.eq_iff_iff.2
  simp only [adjE_eq_true_iff]
  constructor <;> rintro ⟨e, he, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
  · exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩
  · exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨e, he, Or.inr ⟨h1, h2⟩⟩
  · exact ⟨e, he, Or.inl ⟨h1, h2⟩⟩

def delV {n : ℕ} (u : Fin (n + 1)) (E : List (Fin (n + 1) × Fin (n + 1))) :
    List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if adjE E (u.succAbove i) (u.succAbove j) then some (i, j) else none

theorem adjE_delV {n : ℕ} (u : Fin (n + 1)) (E : List (Fin (n + 1) × Fin (n + 1))) (i j : Fin n) :
    adjE E (u.succAbove i) (u.succAbove j) = adjE (delV u E) i j := by
  symm
  apply Bool.eq_iff_iff.2
  simp only [adjE_eq_true_iff, delV, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨e, ⟨a, b, hb⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · split at hb
      · rename_i h_adj; injection hb with hab; subst hab; exact h_adj
      · cases hb
    · split at hb
      · rename_i h_adj; injection hb with hab; subst hab; simpa only [or_comm] using h_adj
      · cases hb
  · intro h
    refine ⟨(i, j), ⟨i, j, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
    simp [h]

theorem hasBSize_delV {n s : ℕ} (u : Fin (n + 1))
    (E : List (Fin (n + 1) × Fin (n + 1)))
    (hs : HasBSize n (fun y => edgeFun E (u.insertNth false y)) s) :
    HasBSize n (edgeFun (delV u E)) s :=
  hasBSize_edgeFun_insertNth_false u E (delV u E) (adjE_delV u E) hs

def delL {n : ℕ} (u : Fin (n + 1)) (L : List (Fin (n + 1))) : List (Fin n) :=
  (List.finRange n).filter fun i => L.any (· == u.succAbove i)

theorem delL_any {n : ℕ} (u : Fin (n + 1)) (L : List (Fin (n + 1))) (i : Fin n) :
    L.any (· == u.succAbove i) = (delL u L).any (· == i) := by
  apply Bool.eq_iff_iff.2
  simp only [delL, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · intro ⟨k, hk, hki⟩
    exact ⟨i, ⟨k, hk, hki⟩, rfl⟩
  · rintro ⟨a, ha, hai⟩
    rw [hai] at ha
    exact ha

def trueL {n : ℕ} (u : Fin (n + 1)) (E : List (Fin (n + 1) × Fin (n + 1))) : List (Fin n) :=
  (List.finRange n).filter fun i => adjE E u (u.succAbove i)

theorem trueL_any {n : ℕ} (u : Fin (n + 1)) (E : List (Fin (n + 1) × Fin (n + 1))) (i : Fin n) :
    adjE E u (u.succAbove i) = (trueL u E).any (· == i) := by
  apply Bool.eq_iff_iff.2
  simp only [trueL, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · intro h
    exact ⟨i, h, rfl⟩
  · rintro ⟨a, ha, hai⟩
    rw [hai] at ha
    exact ha

theorem edgeFun_insertNth_true_auto {n : ℕ} (u : Fin (n + 1))
    (E : List (Fin (n + 1) × Fin (n + 1))) (hnoLoop : adjE E u u = false) (y : Fin n → Bool) :
    edgeFun E (u.insertNth true y) = orEdgeFun (trueL u E) (delV u E) y :=
  edgeFun_insertNth_true u E (trueL u E) (delV u E) hnoLoop (trueL_any u E)
    (fun i j => by simp only [effAdj, trueL_any u E, adjE_delV u E]) y

theorem orEdgeFun_peel_auto {n s : ℕ} (u : Fin (n + 1))
    (L : List (Fin (n + 1))) (E : List (Fin (n + 1) × Fin (n + 1)))
    (hdep : ∀ w : Fin (n + 1), ∃ x, orEdgeFun L E (Function.update x w (!x w)) ≠ orEdgeFun L E x)
    (hne : (delL u L).isEmpty = false ∨ (delV u E).isEmpty = false)
    (hs : HasBSize (n + 1) (orEdgeFun L E) s) :
    1 ≤ s ∧ HasBSize n (orEdgeFun (delL u L) (delV u E)) (s - 1) :=
  orEdgeFun_peel_one u L E (delL u L) (delV u E) hdep (delL_any u L)
    (fun i j => by simp only [effAdj, delL_any u L, adjE_delV u E]) hne hs

theorem orEdgeFun_of_isEmpty {n : ℕ} (L : List (Fin n)) (E : List (Fin n × Fin n))
    (hL : L.isEmpty = true) (x : Fin n → Bool) :
    orEdgeFun L E x = edgeFun E x := by
  cases L <;> simp_all [orEdgeFun]

theorem C5_lower (s : ℕ) (hs : HasBSize 5 (edgeFun E_C5) s) : 7 ≤ s := by
  have hdep := edgeFun_dep_all E_C5 (by decide) (by decide)
  have hnb := edgeFun_nonblocking E_C5 (by decide) (by decide)
  have hnc := edgeFun_nonconst_insertNth E_C5 (by decide) (by decide)
  obtain ⟨u, hres⟩ := master_elim 4 s (by omega) (edgeFun E_C5) hdep hnb hnc hs
  have h_f0 : ∀ (u : Fin 5) (t : ℕ),
      HasBSize 4 (fun y => edgeFun E_C5 (u.insertNth false y)) t → 4 ≤ t := by
    intro u t ht
    fin_cases u
    · exact P4_lower t (edgeFun_bsize_relabel_eq _ E_P4 ![0,1,2,3] (by decide) (hasBSize_delV 0 E_C5 ht))
    · exact P4_lower t (edgeFun_bsize_relabel_eq _ E_P4 ![3,0,1,2] (by decide) (hasBSize_delV 1 E_C5 ht))
    · exact P4_lower t (edgeFun_bsize_relabel_eq _ E_P4 ![2,3,0,1] (by decide) (hasBSize_delV 2 E_C5 ht))
    · exact P4_lower t (edgeFun_bsize_relabel_eq _ E_P4 ![1,2,3,0] (by decide) (hasBSize_delV 3 E_C5 ht))
    · exact P4_lower t (edgeFun_bsize_relabel_eq _ E_P4 ![0,1,2,3] (by decide) (hasBSize_delV 4 E_C5 ht))
  have h_f1 : ∀ (u : Fin 5) (t : ℕ),
      HasBSize 4 (fun y => edgeFun E_C5 (u.insertNth true y)) t → 3 ≤ t := by
    intro u t ht
    fin_cases u <;> (
      have ht' := bsize_congr (edgeFun_insertNth_true_auto _ E_C5 (by decide)) ht
      have hd := dep_lower_b 4 _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) t ht'
      omega)
  rcases hres with ⟨h4, hf0, _⟩ | ⟨h4, hf1, _⟩ | ⟨h3, hf0, _⟩
  · have := h_f0 u (s - 4) hf0; omega
  · have := h_f1 u (s - 4) hf1; omega
  · have := h_f0 u (s - 3) hf0; omega

theorem C6_lower (s : ℕ) (hs : HasBSize 6 (edgeFun E_C6) s) : 8 ≤ s := by
  have hdep := edgeFun_dep_all E_C6 (by decide) (by decide)
  have hnb := edgeFun_nonblocking E_C6 (by decide) (by decide)
  have hnc := edgeFun_nonconst_insertNth E_C6 (by decide) (by decide)
  obtain ⟨u, hres⟩ := master_elim 5 s (by omega) (edgeFun E_C6) hdep hnb hnc hs
  have h_f0 : ∀ (u : Fin 6) (t : ℕ),
      HasBSize 5 (fun y => edgeFun E_C6 (u.insertNth false y)) t → 5 ≤ t := by
    intro u t ht
    fin_cases u
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![0,1,2,3,4] (by decide) (hasBSize_delV 0 E_C6 ht))
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![4,0,1,2,3] (by decide) (hasBSize_delV 1 E_C6 ht))
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![3,4,0,1,2] (by decide) (hasBSize_delV 2 E_C6 ht))
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![2,3,4,0,1] (by decide) (hasBSize_delV 3 E_C6 ht))
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![1,2,3,4,0] (by decide) (hasBSize_delV 4 E_C6 ht))
    · exact P5_lower t (edgeFun_bsize_relabel_eq _ E_P5 ![0,1,2,3,4] (by decide) (hasBSize_delV 5 E_C6 ht))
  have h_f1 : ∀ (u : Fin 6) (t : ℕ),
      HasBSize 5 (fun y => edgeFun E_C6 (u.insertNth true y)) t → 4 ≤ t := by
    intro u t ht
    fin_cases u <;> (
      have ht' := bsize_congr (edgeFun_insertNth_true_auto _ E_C6 (by decide)) ht
      have hd := dep_lower_b 5 _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) t ht'
      omega)
  rcases hres with ⟨h4, hf0, _⟩ | ⟨h4, hf1, _⟩ | ⟨h3, hf0, _⟩
  · have := h_f0 u (s - 4) hf0; omega
  · have := h_f1 u (s - 4) hf1; omega
  · have := h_f0 u (s - 3) hf0; omega

theorem fT_lower (s : ℕ) (hs : HasBSize 7 (edgeFun E_fT) s) : 9 ≤ s := by
  have hdep := edgeFun_dep_all E_fT (by decide) (by decide)
  have hnc := (edgeFun_nonconst_insertNth E_fT (by decide) (by decide)) 2 false
  obtain ⟨h1, hs0⟩ := elim_var_at 2 false (edgeFun E_fT) (hdep 2) hnc hs
  have hc6 := C6_lower (s - 1) (edgeFun_bsize_relabel_eq _ E_C6 ![0,3,1,2,5,4] (by decide)
    (hasBSize_delV 2 E_fT hs0))
  omega

theorem G8_lower (s : ℕ) (hs : HasBSize 8 (edgeFun E_G8) s) : 11 ≤ s := by
  have hdep := edgeFun_dep_all E_G8 (by decide) (by decide)
  have hnc0 := (edgeFun_nonconst_insertNth E_G8 (by decide) (by decide)) 6 false
  have hnc1 := (edgeFun_nonconst_insertNth E_G8 (by decide) (by decide)) 6 true
  obtain ⟨h2, hs0 | hs1⟩ := elim_kill_var 6 (edgeFun E_G8) (hdep 6) hnc0 hnc1 hs
  · have hft := fT_lower (s - 2) (edgeFun_bsize_relabel_eq _ E_fT ![3,0,2,1,4,5,6] (by decide)
      (hasBSize_delV 6 E_G8 hs0))
    omega
  · have h1' := bsize_congr (edgeFun_insertNth_true_auto 6 E_G8 (by decide)) hs1
    obtain ⟨h1p, h1''⟩ := orEdgeFun_peel_auto 2 _ _
      (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) h1'
    have hc6 := C6_lower (s - 2 - 1) (edgeFun_bsize_relabel_eq _ E_C6 ![0,1,4,5,2,3] (by decide)
      (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) h1''))
    omega

theorem H8_lower (s : ℕ) (hs : HasBSize 8 (edgeFun E_H8) s) : 11 ≤ s := by
  have hdep := edgeFun_dep_all E_H8 (by decide) (by decide)
  have hnb := edgeFun_nonblocking E_H8 (by decide) (by decide)
  have hnc := edgeFun_nonconst_insertNth E_H8 (by decide) (by decide)
  obtain ⟨u, hres⟩ := master_elim 7 s (by omega) (edgeFun E_H8) hdep hnb hnc hs
  have h_f0 : ∀ (u : Fin 8) (t : ℕ),
      HasBSize 7 (fun y => edgeFun E_H8 (u.insertNth false y)) t → 9 ≤ t := by
    intro u t ht
    fin_cases u
    · have ht0 := hasBSize_delV 0 E_H8 ht
      obtain ⟨h1a, ht1⟩ := elim_var_at 4 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 4)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 4 false) ht0
      obtain ⟨h1b, ht2⟩ := elim_var_at 3 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 3)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 3 false) (hasBSize_delV 4 _ ht1)
      have hc5 := C5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_C5 ![0,2,3,1,4] (by decide)
        (hasBSize_delV 3 _ ht2))
      omega
    · have ht0 := hasBSize_delV 1 E_H8 ht
      obtain ⟨h1a, ht1⟩ := elim_var_at 6 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 6)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 6 false) ht0
      obtain ⟨h1b, ht2⟩ := elim_var_at 5 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 5)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 5 false) (hasBSize_delV 6 _ ht1)
      have hc5 := C5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_C5 ![0,2,3,1,4] (by decide)
        (hasBSize_delV 5 _ ht2))
      omega
    · have ht0 := hasBSize_delV 2 E_H8 ht
      obtain ⟨h1a, ht1⟩ := elim_var_at 5 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 5)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 5 false) ht0
      obtain ⟨h1b, ht2⟩ := elim_var_at 3 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 3)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 3 false) (hasBSize_delV 5 _ ht1)
      have hc5 := C5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_C5 ![0,1,3,4,2] (by decide)
        (hasBSize_delV 3 _ ht2))
      omega
    · have ht0 := hasBSize_delV 3 E_H8 ht
      obtain ⟨h1a, ht1⟩ := elim_var_at 6 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 6)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 6 false) ht0
      obtain ⟨h1b, ht2⟩ := elim_var_at 4 false _ ((edgeFun_dep_all _ (by decide) (by decide)) 4)
        ((edgeFun_nonconst_insertNth _ (by decide) (by decide)) 4 false) (hasBSize_delV 6 _ ht1)
      have hc5 := C5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_C5 ![0,1,3,4,2] (by decide)
        (hasBSize_delV 4 _ ht2))
      omega
    · exact fT_lower t (edgeFun_bsize_relabel_eq _ E_fT ![5,0,4,1,6,3,2] (by decide) (hasBSize_delV 4 E_H8 ht))
    · exact fT_lower t (edgeFun_bsize_relabel_eq _ E_fT ![3,0,1,6,4,2,5] (by decide) (hasBSize_delV 5 E_H8 ht))
    · exact fT_lower t (edgeFun_bsize_relabel_eq _ E_fT ![0,5,4,1,3,2,6] (by decide) (hasBSize_delV 6 E_H8 ht))
    · exact fT_lower t (edgeFun_bsize_relabel_eq _ E_fT ![0,5,1,4,2,3,6] (by decide) (hasBSize_delV 7 E_H8 ht))
  have h_f1 : ∀ (u : Fin 8) (t : ℕ),
      HasBSize 7 (fun y => edgeFun E_H8 (u.insertNth true y)) t → 7 ≤ t := by
    intro u t ht
    fin_cases u
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 0 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 4 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 3 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht1
      obtain ⟨h1c, ht3⟩ := orEdgeFun_peel_auto 0 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht2
      have hp4 := P4_lower (t - 1 - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P4 ![1,2,0,3] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht3))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 1 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 6 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 5 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht1
      obtain ⟨h1c, ht3⟩ := orEdgeFun_peel_auto 0 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht2
      have hp4 := P4_lower (t - 1 - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P4 ![1,2,0,3] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht3))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 2 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 5 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 3 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht1
      obtain ⟨h1c, ht3⟩ := orEdgeFun_peel_auto 2 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht2
      have hp4 := P4_lower (t - 1 - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P4 ![1,2,0,3] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht3))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 3 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 6 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 4 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht1
      obtain ⟨h1c, ht3⟩ := orEdgeFun_peel_auto 2 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht2
      have hp4 := P4_lower (t - 1 - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P4 ![1,2,0,3] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht3))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 4 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 2 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 0 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht1
      have hp5 := P5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P5 ![1,3,4,0,2] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht2))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 5 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 3 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 0 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht1
      have hp5 := P5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P5 ![1,3,4,2,0] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht2))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 6 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 2 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 1 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht1
      have hp5 := P5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P5 ![1,3,0,2,4] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht2))
      omega
    · have ht0 := bsize_congr (edgeFun_insertNth_true_auto 7 E_H8 (by decide)) ht
      obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 3 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) ht0
      obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 1 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht1
      have hp5 := P5_lower (t - 1 - 1) (edgeFun_bsize_relabel_eq _ E_P5 ![1,3,2,0,4] (by decide)
        (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht2))
      omega
  rcases hres with ⟨h4, hf0, _⟩ | ⟨h4, hf1, _⟩ | ⟨h3, hf0, _⟩
  · have := h_f0 u (s - 4) hf0; omega
  · have := h_f1 u (s - 4) hf1; omega
  · have := h_f0 u (s - 3) hf0; omega

theorem G9_x6_false_lower (s : ℕ)
    (hs : HasBSize 8 (fun y => edgeFun E_G9 ((6 : Fin 9).insertNth false y)) s) : 11 ≤ s :=
  H8_lower s (edgeFun_bsize_relabel_eq _ E_H8 ![0,4,2,3,5,1,6,7] (by decide) (hasBSize_delV 6 E_G9 hs))

theorem G9_x6_true_lower (s : ℕ)
    (hs : HasBSize 8 (fun y => edgeFun E_G9 ((6 : Fin 9).insertNth true y)) s) : 10 ≤ s := by
  have hs' := bsize_congr (edgeFun_insertNth_true_auto 6 E_G9 (by decide)) hs
  obtain ⟨h1a, ht1⟩ := orEdgeFun_peel_auto 7 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inl (by decide)) hs'
  obtain ⟨h1b, ht2⟩ := orEdgeFun_peel_auto 1 _ _ (orEdgeFun_dep_all _ _ (by decide) (by decide)) (Or.inr (by decide)) ht1
  have hc6 := C6_lower (s - 1 - 1) (edgeFun_bsize_relabel_eq _ E_C6 ![0,3,2,1,5,4] (by decide)
    (bsize_congr (orEdgeFun_of_isEmpty _ _ (by decide)) ht2))
  omega

theorem G9_lower (s : ℕ) (hs : HasBSize 9 (edgeFun E_G9) s) : 13 ≤ s := by
  have hdep := edgeFun_dep_all E_G9 (by decide) (by decide)
  have hnb := edgeFun_nonblocking E_G9 (by decide) (by decide)
  have hnc := edgeFun_nonconst_insertNth E_G9 (by decide) (by decide)
  obtain ⟨u, hres⟩ := master_elim 8 s (by omega) (edgeFun E_G9) hdep hnb hnc hs
  have h_f0 : ∀ (u : Fin 9) (t : ℕ),
      HasBSize 8 (fun y => edgeFun E_G9 (u.insertNth false y)) t → 11 ≤ t := by
    intro u t ht
    fin_cases u
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![0,1,2,6,7,4,5,3] (by decide) (hasBSize_delV 0 E_G9 ht))
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![4,5,1,0,3,6,7,2] (by decide) (hasBSize_delV 1 E_G9 ht))
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![1,5,4,0,2,7,6,3] (by decide) (hasBSize_delV 2 E_G9 ht))
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![2,1,0,6,3,5,4,7] (by decide) (hasBSize_delV 3 E_G9 ht))
    · exact H8_lower t (edgeFun_bsize_relabel_eq _ E_H8 ![4,0,1,7,2,5,6,3] (by decide) (hasBSize_delV 4 E_G9 ht))
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![0,1,2,3,4,5,6,7] (by decide) (hasBSize_delV 5 E_G9 ht))
    · exact G9_x6_false_lower t ht
    · exact H8_lower t (edgeFun_bsize_relabel_eq _ E_H8 ![0,1,6,2,4,5,7,3] (by decide) (hasBSize_delV 7 E_G9 ht))
    · exact G8_lower t (edgeFun_bsize_relabel_eq _ E_G8 ![1,2,3,4,0,5,6,7] (by decide) (hasBSize_delV 8 E_G9 ht))
  rcases hres with ⟨h4, hf0, _⟩ | ⟨h4, _, hf0⟩ | ⟨h3, hf0, _⟩
  · have := h_f0 u (s - 4) hf0; omega
  · have := h_f0 u (s - 2) hf0; omega
  · have := h_f0 u (s - 3) hf0; omega

def wInput (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 6]

theorem length_wInput (x : Fin 9 → Bool) : (wInput x).length = 10 := by
  simp [wInput]

def HasWSize (s : ℕ) : Prop :=
  ∃ (gs : List BGate) (o : ℕ) (po : Bool),
    CleanB 10 gs ∧ gs.length ≤ s ∧
    ∀ x : Fin 9 → Bool, xor ((bwires gs (wInput x)).getD o false) po = edgeFun E_G9 x

theorem exists_min_cleanW (s : ℕ) (h : HasWSize s) :
    ∃ (gs : List BGate) (o : ℕ) (po : Bool),
      CleanB 10 gs ∧ gs.length ≤ s ∧
      (∀ x : Fin 9 → Bool, xor ((bwires gs (wInput x)).getD o false) po = edgeFun E_G9 x) ∧
      (∀ gs1 o1 po1, CleanB 10 gs1 →
        (∀ x : Fin 9 → Bool, xor ((bwires gs1 (wInput x)).getD o1 false) po1 = edgeFun E_G9 x) →
        gs.length ≤ gs1.length) := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List BGate) (o : ℕ) (po : Bool),
    CleanB 10 gs ∧ gs.length = t ∧
    ∀ x : Fin 9 → Bool, xor ((bwires gs (wInput x)).getD o false) po = edgeFun E_G9 x
  obtain ⟨gs0, o0, po0, hcl0, hlen0, hev0⟩ := h
  have hex : ∃ t, P t := ⟨gs0.length, gs0, o0, po0, hcl0, rfl, hev0⟩
  have hmin : Nat.find hex ≤ gs0.length := Nat.find_min' hex ⟨gs0, o0, po0, hcl0, rfl, hev0⟩
  obtain ⟨gs, o, po, hcl, hlen, hev⟩ := Nat.find_spec hex
  refine ⟨gs, o, po, hcl, by omega, hev, ?_⟩
  intro gs1 o1 po1 hcl1 hev1
  have hP1 : P gs1.length := ⟨gs1, o1, po1, hcl1, rfl, hev1⟩
  have := Nat.find_min' hex hP1
  omega

theorem min_cleanW_used (gs : List BGate) (o : ℕ) (po : Bool)
    (hcl : CleanB 10 gs)
    (hev : ∀ x : Fin 9 → Bool, xor ((bwires gs (wInput x)).getD o false) po = edgeFun E_G9 x)
    (hmin : ∀ gs1 o1 po1, CleanB 10 gs1 →
      (∀ x : Fin 9 → Bool, xor ((bwires gs1 (wInput x)).getD o1 false) po1 = edgeFun E_G9 x) →
      gs.length ≤ gs1.length) :
    ∀ p < gs.length, 10 + p = o ∨ ∃ (q : ℕ) (g : BGate), gs[q]? = some g ∧ (g.a = 10 + p ∨ g.b = 10 + p) := by
  intro p hp
  by_contra hcon
  push Not at hcon
  obtain ⟨hpo, hno⟩ := hcon
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
  have hno' : ∀ g' ∈ post, g'.a ≠ 10 + pre.length ∧ g'.b ≠ 10 + pre.length := by
    intro g' hg'
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
    have := hno (pre.length + 1 + q) g' (by
      rw [List.getElem?_append_right (by omega)]
      have he : pre.length + 1 + q - pre.length = q + 1 := by omega
      rw [he]; simpa using hq)
    rw [hpl]; exact this
  have hcl' := cleanB_del_bgate 10 pre g post hcl hno'
  have hev' : ∀ x : Fin 9 → Bool,
      xor ((bwires (pre ++ post.map (shBGate (10 + pre.length))) (wInput x)).getD
        (shift (10 + pre.length) o) false) po = edgeFun E_G9 x := by
    intro x
    rw [del_bgate_wires 10 pre g post o hno' (by rw [hpl]; exact fun e => hpo e.symm) (wInput x) (length_wInput x)]
    exact hev x
  have hle := hmin (pre ++ post.map (shBGate (10 + pre.length))) (shift (10 + pre.length) o) po hcl' hev'
  simp at hle

def NoW69 (gs : List BGate) : Prop :=
  ∀ g ∈ gs, ¬ ((g.a = 6 ∧ g.b = 9) ∨ (g.a = 9 ∧ g.b = 6))

def simpWPair (m : ℕ) (p6 p9 : Bool) : Option BGate × BStat :=
  match p6, p9 with
  | false, false => (none, BStat.wire 6 false)
  | false, true  => (none, BStat.const false)
  | true, false  => simpBAnd m (BStat.wire 6 true) (BStat.wire 0 false)
  | true, true   => simpBAnd m (BStat.wire 6 true) (BStat.wire 0 true)

def simpWAnd (m : ℕ) (s1 s2 : BStat) : Option BGate × BStat :=
  match s1, s2 with
  | BStat.wire 6 p6, BStat.wire 9 p9 => simpWPair m p6 p9
  | BStat.wire 9 p9, BStat.wire 6 p6 => simpWPair m p6 p9
  | _, _ => simpBAnd m s1 s2

theorem simpWAnd_clean (m : ℕ) (hm : 10 ≤ m) (s1 s2 : BStat) (h1 : s1.Valid m) (h2 : s2.Valid m) :
    ∀ g ∈ (simpWAnd m s1 s2).1, g.a < m ∧ g.b < m ∧ g.a ≠ g.b ∧
      ¬ ((g.a = 6 ∧ g.b = 9) ∨ (g.a = 9 ∧ g.b = 6)) := by
  intro g hg
  cases s1 with
  | const c =>
    have hc := simpBAnd_clean m (BStat.const c) s2 h1 h2 g hg
    exact ⟨hc.1, hc.2.1, hc.2.2, by simp [simpWAnd, simpBAnd] at hg⟩
  | wire j pj =>
    cases s2 with
    | const c =>
      simp only [simpWAnd] at hg
      have hc := simpBAnd_clean m (BStat.wire j pj) (BStat.const c) h1 h2 g hg
      exact ⟨hc.1, hc.2.1, hc.2.2, by simp [simpBAnd] at hg⟩
    | wire k pk =>
      by_cases h69 : (j = 6 ∧ k = 9) ∨ (j = 9 ∧ k = 6)
      · rcases h69 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · cases pj <;> cases pk <;> simp [simpWAnd, simpWPair, simpBAnd] at hg <;>
            first | (rw [← hg]; simp only [ne_eq, or_self, not_false_eq_true, and_true]; exact ⟨by omega, by omega⟩) | exact absurd rfl hm
        · cases pj <;> cases pk <;> simp [simpWAnd, simpWPair, simpBAnd] at hg <;>
            first | (rw [← hg]; simp only [ne_eq, or_self, not_false_eq_true, and_true]; exact ⟨by omega, by omega⟩) | exact absurd rfl hm
      · have hnot : simpWAnd m (BStat.wire j pj) (BStat.wire k pk) =
            simpBAnd m (BStat.wire j pj) (BStat.wire k pk) := by
          unfold simpWAnd
          split <;> simp_all
        rw [hnot] at hg
        have hc := simpBAnd_clean m (BStat.wire j pj) (BStat.wire k pk) h1 h2 g hg
        simp only [simpBAnd] at hg
        split at hg
        · simp at hg
        · simp only [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact ⟨hc.1, hc.2.1, hc.2.2, h69⟩

theorem simpWAnd_sound (w : List Bool) (hw : 10 ≤ w.length)
    (hw9 : w.getD 9 false = (w.getD 0 false || w.getD 6 false))
    (s1 s2 : BStat) (h1 : s1.Valid w.length) (h2 : s2.Valid w.length) :
    (simpWAnd w.length s1 s2).2.Valid (w.length + (simpWAnd w.length s1 s2).1.toList.length) ∧
    (simpWAnd w.length s1 s2).2.val (bwires (simpWAnd w.length s1 s2).1.toList w) =
      (s1.val w && s2.val w) := by
  have hpair : ∀ p6 p9 : Bool,
      (simpWPair w.length p6 p9).2.Valid (w.length + (simpWPair w.length p6 p9).1.toList.length) ∧
      (simpWPair w.length p6 p9).2.val (bwires (simpWPair w.length p6 p9).1.toList w) =
        ((xor (w.getD 6 false) p6) && (xor (w.getD 9 false) p9)) := by
    intro p6 p9
    cases p6 <;> cases p9
    · simp only [simpWPair, Option.toList_none, List.length_nil, Nat.add_zero, bwires, List.foldl_nil,
        BStat.Valid, BStat.val, hw9]
      refine ⟨by omega, ?_⟩
      cases w.getD 0 false <;> cases w.getD 6 false <;> rfl
    · simp only [simpWPair, Option.toList_none, List.length_nil, Nat.add_zero, bwires, List.foldl_nil,
        BStat.Valid, BStat.val, hw9]
      refine ⟨trivial, ?_⟩
      cases w.getD 0 false <;> cases w.getD 6 false <;> rfl
    · have hs := simpBAnd_sound w (BStat.wire 6 true) (BStat.wire 0 false) (by simp [BStat.Valid]; omega) (by simp [BStat.Valid]; omega)
      refine ⟨hs.1, ?_⟩
      simp only [simpWPair]
      rw [hs.2]
      simp only [BStat.val, hw9]
      cases w.getD 0 false <;> cases w.getD 6 false <;> rfl
    · have hs := simpBAnd_sound w (BStat.wire 6 true) (BStat.wire 0 true) (by simp [BStat.Valid]; omega) (by simp [BStat.Valid]; omega)
      refine ⟨hs.1, ?_⟩
      simp only [simpWPair]
      rw [hs.2]
      simp only [BStat.val, hw9]
      cases w.getD 0 false <;> cases w.getD 6 false <;> rfl
  cases s1 with
  | const c => exact simpBAnd_sound w (BStat.const c) s2 h1 h2
  | wire j pj =>
    cases s2 with
    | const c => simp only [simpWAnd]; exact simpBAnd_sound w (BStat.wire j pj) (BStat.const c) h1 h2
    | wire k pk =>
      by_cases hj6 : j = 6
      · subst hj6
        by_cases hk9 : k = 9
        · subst hk9; exact hpair pj pk
        · simp [simpWAnd, hk9]; exact simpBAnd_sound w (BStat.wire 6 pj) (BStat.wire k pk) h1 h2
      · by_cases hj9 : j = 9
        · subst hj9
          by_cases hk6 : k = 6
          · subst hk6
            have hp := hpair pk pj
            simp only [simpWAnd]
            refine ⟨hp.1, ?_⟩
            rw [hp.2, Bool.and_comm]
            rfl
          · simp [simpWAnd, hk6]; exact simpBAnd_sound w (BStat.wire 9 pj) (BStat.wire k pk) h1 h2
        · simp [simpWAnd, hj6, hj9]; exact simpBAnd_sound w (BStat.wire j pj) (BStat.wire k pk) h1 h2

def elimWStep (acc : List BStat × List BGate) (g : BGate) : List BStat × List BGate :=
  let s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false)
  let s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false)
  let r := simpWAnd (10 + acc.2.length) s1 s2
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimW (gs : List BGate) (acc : List BStat × List BGate) : List BStat × List BGate :=
  gs.foldl elimWStep acc

theorem inv_elimW (y' : List Bool) (hy' : y'.length = 10)
    (hy'9 : y'.getD 9 false = (y'.getD 0 false || y'.getD 6 false)) (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate), InvB 10 y' w acc →
      InvB 10 y' (bwires gs w) (elimW gs acc) := by
  induction gs with
  | nil => intro w acc h; exact h
  | cons g gs ih =>
    intro w acc h
    apply ih (w ++ [g.eval w]) (elimWStep acc g)
    obtain ⟨hl, hi⟩ := h
    set w' := bwires acc.2 y' with hw'
    have lw' : w'.length = 10 + acc.2.length := by rw [hw', length_bwires, hy']
    have hw'9 : w'.getD 9 false = (w'.getD 0 false || w'.getD 6 false) := by
      rw [hw', getD_bwires _ _ _ (by rw [hy']; omega),
        getD_bwires _ _ _ (by rw [hy']; omega),
        getD_bwires _ _ _ (by rw [hy']; omega)]
      exact hy'9
    set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
      else acc.1.getD g.a (BStat.const false) with hs1
    set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
      else acc.1.getD g.b (BStat.const false) with hs2
    have hv1 : s1.Valid w'.length := by
      rw [lw']
      cases hpa : g.pa
      · rw [hs1, hpa]; exact (hi g.a).1
      · rw [hs1, hpa]; exact negBStat_valid _ (hi g.a).1
    have hv2 : s2.Valid w'.length := by
      rw [lw']
      cases hpb : g.pb
      · rw [hs2, hpb]; exact (hi g.b).1
      · rw [hs2, hpb]; exact negBStat_valid _ (hi g.b).1
    have hs := simpWAnd_sound w' (by rw [lw']; omega) hw'9 s1 s2 hv1 hv2
    rw [lw'] at hs
    set r := simpWAnd (10 + acc.2.length) s1 s2 with hr
    have hval1 : s1.val w' = xor (w.getD g.a false) g.pa := by
      cases hpa : g.pa
      · rw [hs1, hpa]; simpa using (hi g.a).2
      · rw [hs1, hpa]; simpa [negBStat_val] using congrArg not (hi g.a).2
    have hval2 : s2.val w' = xor (w.getD g.b false) g.pb := by
      cases hpb : g.pb
      · rw [hs2, hpb]; simpa using (hi g.b).2
      · rw [hs2, hpb]; simpa [negBStat_val] using congrArg not (hi g.b).2
    have hnew : bwires (acc.2 ++ r.1.toList) y' = bwires r.1.toList w' := by
      rw [bwires_append]
    obtain ⟨t, ht, _⟩ := bwires_start r.1.toList w'
    refine ⟨by simp [elimWStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (BStat.const false)).Valid (10 + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (BStat.const false)).val (bwires (acc.2 ++ r.1.toList) y') = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hval1, hval2]; rfl⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨BStat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, BStat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem clean_elimW (y' : List Bool) (hy' : y'.length = 10)
    (hy'9 : y'.getD 9 false = (y'.getD 0 false || y'.getD 6 false)) (gs : List BGate) :
    ∀ (w : List Bool) (acc : List BStat × List BGate), InvB 10 y' w acc →
      CleanB 10 acc.2 → NoW69 acc.2 →
      CleanB 10 (elimW gs acc).2 ∧ NoW69 (elimW gs acc).2 := by
  induction gs with
  | nil => intro w acc _ hcl hnp; exact ⟨hcl, hnp⟩
  | cons g gs ih =>
    intro w acc hinv hcl hnp
    have hinv' : InvB 10 y' (bwires [g] w) (elimWStep acc g) :=
      inv_elimW y' hy' hy'9 [g] w acc hinv
    set s1 := if g.pa then negBStat (acc.1.getD g.a (BStat.const false))
      else acc.1.getD g.a (BStat.const false) with hs1
    set s2 := if g.pb then negBStat (acc.1.getD g.b (BStat.const false))
      else acc.1.getD g.b (BStat.const false) with hs2
    set r := simpWAnd (10 + acc.2.length) s1 s2 with hr
    have hv1 : s1.Valid (10 + acc.2.length) := by
      cases hpa : g.pa
      · rw [hs1, hpa]; exact (hinv.2 g.a).1
      · rw [hs1, hpa]; exact negBStat_valid _ (hinv.2 g.a).1
    have hv2 : s2.Valid (10 + acc.2.length) := by
      cases hpb : g.pb
      · rw [hs2, hpb]; exact (hinv.2 g.b).1
      · rw [hs2, hpb]; exact negBStat_valid _ (hinv.2 g.b).1
    have hcnew := simpWAnd_clean (10 + acc.2.length) (by omega) s1 s2 hv1 hv2
    refine ih _ (elimWStep acc g) hinv' ?_ ?_
    · intro p g' hp
      change (acc.2 ++ r.1.toList)[p]? = some g' at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp; exact hcl p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        obtain ⟨_, hmem⟩ := toList_getElem? _ _ _ hp
        have hpl : p = acc.2.length := by omega
        rw [hpl]
        have := hcnew g' hmem
        exact ⟨this.1, this.2.1, this.2.2.1⟩
    · intro g' hg'
      change g' ∈ acc.2 ++ r.1.toList at hg'
      rcases List.mem_append.1 hg' with hm | hm
      · exact hnp g' hm
      · exact (hcnew g' (by cases hr1 : r.1 <;> simp_all)).2.2.2

theorem elimW_len (gs : List BGate) : ∀ acc : List BStat × List BGate,
    (elimW gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimW]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimWStep acc g)
    have h2 : (elimWStep acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimWStep, List.length_append]
      have := toList_length_le (simpWAnd (10 + acc.2.length)
        (if g.pa then negBStat (acc.1.getD g.a (BStat.const false)) else acc.1.getD g.a (BStat.const false))
        (if g.pb then negBStat (acc.1.getD g.b (BStat.const false)) else acc.1.getD g.b (BStat.const false))).1
      omega
    change (elimW gs (elimWStep acc g)).2.length ≤ acc.2.length + (gs.length + 1)
    omega

theorem invB_idW (x : Fin 9 → Bool) :
    InvB 10 (wInput x) (wInput x) (idBStats 10, []) := by
  refine ⟨by simp [idBStats, wInput], ?_⟩
  intro i
  by_cases hlt : i < 10
  · simp only [idBStats]
    rw [getD_ofFn _ _ _ hlt]
    simp [BStat.Valid, BStat.val, bwires, hlt]
  · rw [List.getD_eq_default _ _ (by simp [idBStats]; omega),
      List.getD_eq_default _ _ (by simp [wInput]; omega)]
    exact ⟨trivial, rfl⟩

def initW8 (c : Bool) : List BStat :=
  initAt (6 : Fin 9) c ++ [if c then BStat.const true else BStat.wire 0 false]

theorem length_initW8 (c : Bool) : (initW8 c).length = 10 := by
  simp [initW8, initAt]

theorem getD_wInput_lt (x : Fin 9 → Bool) (i : ℕ) (h : i < 9) :
    (wInput x).getD i false = x ⟨i, h⟩ := by
  rw [wInput, List.getD_append _ _ _ _ (by simp; omega), getD_ofFn _ _ _ h]

theorem getD_wInput_9 (x : Fin 9 → Bool) :
    (wInput x).getD 9 false = (x 0 || x 6) := by
  rw [wInput, getD_snoc_len _ _ _ _ (by simp)]

theorem invB_initW8 (c : Bool) (y : Fin 8 → Bool) :
    InvB 8 (List.ofFn y) (wInput ((6 : Fin 9).insertNth c y)) (initW8 c, []) := by
  have hb := invB_initAt (6 : Fin 9) c y
  refine ⟨by simp [initW8, initAt, wInput], ?_⟩
  intro i
  by_cases hi9 : i < 9
  · rw [initW8, List.getD_append _ _ _ _ (by simp [initAt]; omega), getD_wInput_lt _ _ hi9]
    have hbi := hb.2 i
    rw [getD_ofFn _ _ _ hi9] at hbi
    exact hbi
  · by_cases hieq : i = 9
    · subst hieq
      rw [initW8, getD_snoc_len _ _ _ _ (by simp [initAt]), getD_wInput_9]
      have h0 : ((6 : Fin 9).insertNth c y : Fin 9 → Bool) 0 = y 0 := by
        simpa using Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) c y (0 : Fin 8)
      have h6 : ((6 : Fin 9).insertNth c y : Fin 9 → Bool) 6 = c :=
        Fin.insertNth_apply_same (α := fun _ => Bool) (6 : Fin 9) c y
      rw [h0, h6]
      cases c
      · simp [BStat.Valid, BStat.val, bwires]
      · simp [BStat.Valid, BStat.val]
    · rw [List.getD_eq_default _ _ (by simp [initW8, initAt]; omega),
        List.getD_eq_default _ _ (by simp [wInput]; omega)]
      exact ⟨trivial, rfl⟩

theorem initW8_getD_6 (c : Bool) :
    (initW8 c).getD 6 (BStat.const false) = BStat.const c := by
  rw [initW8, List.getD_append _ _ _ _ (by simp [initAt])]
  exact initAt_getD_eq (6 : Fin 9) c

theorem initW8_getD_9 (c : Bool) :
    (initW8 c).getD 9 (BStat.const false) = if c then BStat.const true else BStat.wire 0 false := by
  rw [initW8, getD_snoc_len _ _ _ _ (by simp [initAt])]

theorem not_hasWSize_12 : ¬ HasWSize 12 := by
  intro hs12
  obtain ⟨gs0, o0, po0, hcl0, hlen0, hev0, hmin_len0⟩ := exists_min_cleanW 12 hs12
  set xex : Fin 9 → Bool := fun _ => false
  have hxex9 : (wInput xex).getD 9 false = ((wInput xex).getD 0 false || (wInput xex).getD 6 false) := rfl
  set accW := elimW gs0 (idBStats 10, []) with haccW
  have hinvW : ∀ x : Fin 9 → Bool,
      InvB 10 (wInput x) (bwires gs0 (wInput x)) accW :=
    fun x => inv_elimW (wInput x) (length_wInput x) rfl gs0 _ _ (invB_idW x)
  have hclnpW : CleanB 10 accW.2 ∧ NoW69 accW.2 :=
    clean_elimW (wInput xex) (length_wInput xex) hxex9 gs0 _ _ (invB_idW xex)
      (by intro p g hp; simp at hp) (by intro g hg; simp at hg)
  have hlenW : accW.2.length ≤ gs0.length := by
    simpa [haccW] using elimW_len gs0 (idBStats 10, [])
  cases hstW : accW.1.getD o0 (BStat.const false) with
  | const d =>
    exfalso
    have h0 : edgeFun E_G9 (fun _ => false) = false := by decide
    have h1 : edgeFun E_G9 (fun i => i == 0 || i == 1) = true := by decide
    have e0 := ((hinvW (fun _ => false)).2 o0).2
    have e1 := ((hinvW (fun i => i == 0 || i == 1)).2 o0).2
    rw [hstW] at e0 e1
    simp only [BStat.val] at e0 e1
    rw [← hev0 (fun _ => false), ← e0] at h0
    rw [← hev0 (fun i => i == 0 || i == 1), ← e1] at h1
    rw [h0] at h1
    cases h1
  | wire oW po' =>
    let gsW := accW.2
    let poW := xor po' po0
    have hgsW_len : gsW.length ≤ 12 := le_trans hlenW hlen0
    have hevW : ∀ x : Fin 9 → Bool,
        xor ((bwires gsW (wInput x)).getD oW false) poW = edgeFun E_G9 x := by
      intro x
      have e1 := ((hinvW x).2 o0).2
      rw [hstW] at e1
      simp only [BStat.val] at e1
      exact xor_out_eq _ po' po0 _ (edgeFun E_G9 x) e1 (hev0 x)
    have hminW : ∀ p < gsW.length, 10 + p = oW ∨
        ∃ (q : ℕ) (g : BGate), gsW[q]? = some g ∧ (g.a = 10 + p ∨ g.b = 10 + p) := by
      apply min_cleanW_used gsW oW poW hclnpW.1 hevW
      intro gs1 o1 po1 hcl1 hev1
      exact le_trans hlenW (hmin_len0 gs1 o1 po1 hcl1 hev1)
    have hoW_ne_9 : oW ≠ 9 := by
      intro e
      subst e
      have h0 : edgeFun E_G9 (fun i => i == 0) = false := by decide
      have h1 : edgeFun E_G9 (fun i => i == 0 || i == 4) = true := by decide
      have e0 := hevW (fun i => i == 0)
      have e1 := hevW (fun i => i == 0 || i == 4)
      rw [getD_bwires _ _ _ (by simp [wInput]), getD_wInput_9] at e0
      rw [getD_bwires _ _ _ (by simp [wInput]), getD_wInput_9] at e1
      have hw0 : ((fun i : Fin 9 => i == 0) 0 || (fun i : Fin 9 => i == 0) 6) = true := by decide
      have hw1 : ((fun i : Fin 9 => i == 0 || i == 4) 0 || (fun i : Fin 9 => i == 0 || i == 4) 6) = true := by decide
      rw [hw0, h0] at e0
      rw [hw1, h1] at e1
      rw [e0] at e1
      cases e1
    have hoW_ne_6 : oW ≠ 6 := by
      intro e
      subst e
      have h0 : edgeFun E_G9 (fun _ => false) = false := by decide
      have h1 : edgeFun E_G9 (fun i => i == 0 || i == 4) = true := by decide
      have e0 := hevW (fun _ => false)
      have e1 := hevW (fun i => i == 0 || i == 4)
      rw [getD_bwires _ _ _ (by simp [wInput]), getD_wInput_lt _ 6 (by omega)] at e0
      rw [getD_bwires _ _ _ (by simp [wInput]), getD_wInput_lt _ 6 (by omega)] at e1
      simp only [h0] at e0
      simp only [h1] at e1
      have e1' : (false ^^ poW) = true := by simpa using e1
      rw [e0] at e1'
      cases e1'
    by_cases hread9 : ∃ (h : ℕ) (gh : BGate), gsW[h]? = some gh ∧ (gh.a = 9 ∨ gh.b = 9)
    · obtain ⟨h, gh, hh, hhm⟩ := hread9
      have hhlt : h < gsW.length := (List.getElem?_eq_some_iff.1 hh).1
      have hk_ex : ∃ (k : ℕ) (gk : BGate), gsW[k]? = some gk ∧ (gk.a = 6 ∨ gk.b = 6) := by
        by_contra hno6
        push Not at hno6
        have hno6' : ∀ g ∈ gsW, g.a ≠ 6 ∧ g.b ≠ 6 := by
          intro g hg
          obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
          exact hno6 q g hq
        let x1 : Fin 9 → Bool := fun i => (i == 0) || (i == 8)
        let x2 : Fin 9 → Bool := fun i => (i == 0) || (i == 8) || (i == 6)
        have hf1 : edgeFun E_G9 x1 = false := by decide
        have hf2 : edgeFun E_G9 x2 = true := by decide
        have hbw : (bwires gsW (wInput x1)).getD oW false = (bwires gsW (wInput x2)).getD oW false := by
          apply bwires_tail_noread (6 : Fin 10) gsW hno6'
          · refine ⟨by simp [wInput], ?_⟩
            intro w hw6
            by_cases hw9 : w < 9
            · rw [getD_wInput_lt _ _ hw9, getD_wInput_lt _ _ hw9]
              dsimp [x1, x2]
              have : (⟨w, hw9⟩ : Fin 9) ≠ 6 := fun e => hw6 (congrArg Fin.val e)
              simp [beq_false_of_ne this]
            · by_cases hw9eq : w = 9
              · subst hw9eq
                rw [getD_wInput_9, getD_wInput_9]
                decide
              · rw [List.getD_eq_default _ _ (by simp [wInput]; omega),
                  List.getD_eq_default _ _ (by simp [wInput]; omega)]
          · exact hoW_ne_6
        have e1 := hevW x1
        have e2 := hevW x2
        rw [hbw, e2, hf2, hf1] at e1
        cases e1
      obtain ⟨k, gk, hk, hkm⟩ := hk_ex
      have hklt : k < gsW.length := (List.getElem?_eq_some_iff.1 hk).1
      have hkh : k ≠ h := by
        intro e
        subst e
        rw [hk] at hh
        injection hh with hgk
        subst hgk
        apply hclnpW.2 gk (List.mem_of_getElem? hk)
        rcases hkm with h1 | h2 <;> rcases hhm with h3 | h4
        · exact absurd (h1.symm.trans h3) (by omega)
        · exact Or.inl ⟨h1, h4⟩
        · exact Or.inr ⟨h3, h2⟩
        · exact absurd (h2.symm.trans h4) (by omega)
      let p6 : Bool := if gk.a = 6 then gk.pa else gk.pb
      set acc8 := elimB 8 gsW (initW8 p6, []) with hacc8
      have hinv8 : ∀ y : Fin 8 → Bool,
          InvB 8 (List.ofFn y) (bwires gsW (wInput ((6 : Fin 9).insertNth p6 y))) acc8 :=
        fun y => inv_elimB 8 (List.ofFn y) (by simp) gsW _ _ (invB_initW8 p6 y)
      have hcl8 : CleanB 8 acc8.2 :=
        clean_elimB 8 (List.ofFn fun _ : Fin 8 => false) (by simp) gsW _ _
          (invB_initW8 p6 _) (by intro p g' hp; simp at hp)
      have hnc6 : ∃ y y' : Fin 8 → Bool,
          edgeFun E_G9 ((6 : Fin 9).insertNth p6 y) ≠ edgeFun E_G9 ((6 : Fin 9).insertNth p6 y') :=
        edgeFun_nonconst_insertNth E_G9 (by decide) (by decide) 6 p6
      have hbsize_of_drop : ∀ D : Finset ℕ, (∀ p ∈ D, isDroppedAt 8 gsW (initW8 p6, []) p) →
          HasBSize 8 (fun y => edgeFun E_G9 ((6 : Fin 9).insertNth p6 y)) (gsW.length - D.card) := by
        intro D hD
        have hle := dropped_le 8 gsW (initW8 p6, []) D hD
        simp only [List.length_nil, zero_add, ← hacc8] at hle
        cases hst8 : acc8.1.getD oW (BStat.const false) with
        | const d =>
          exfalso
          obtain ⟨y, y', hne⟩ := hnc6
          apply hne
          have e1 := ((hinv8 y).2 oW).2
          have e2 := ((hinv8 y').2 oW).2
          rw [hst8] at e1 e2
          simp only [BStat.val] at e1 e2
          rw [← hevW ((6 : Fin 9).insertNth p6 y), ← hevW ((6 : Fin 9).insertNth p6 y'), ← e1, ← e2]
        | wire o8 po8 =>
          refine ⟨acc8.2, o8, xor po8 poW, hcl8, by omega, ?_⟩
          intro y
          have e1 := ((hinv8 y).2 oW).2
          rw [hst8] at e1
          simp only [BStat.val] at e1
          exact xor_out_eq _ po8 poW _ _ e1 (hevW ((6 : Fin 9).insertNth p6 y))
      have hk6_at : ∀ p, (stepAcc 8 gsW (initW8 p6, []) p).1.getD 6 (BStat.const false) = BStat.const p6 := by
        intro p
        unfold stepAcc
        rw [elimB_fst_getD _ _ _ _ _ (by simp [initW8, initAt])]
        exact initW8_getD_6 p6
      have hdrop_k : isDroppedAt 8 gsW (initW8 p6, []) k := by
        refine ⟨gk, hk, ?_⟩
        rcases hkm with ha | hb
        · exact elimBStep_none_of_const_left _ _ _ p6 (ha ▸ hk6_at k)
        · exact elimBStep_none_of_const_right _ _ _ p6 (hb ▸ hk6_at k)
      have hconst_k : ∀ q, k + 1 ≤ q →
          (stepAcc 8 gsW (initW8 p6, []) q).1.getD (10 + k) (BStat.const false) = BStat.const false := by
        intro q hq
        rw [stepAcc_getD_ge 8 gsW (initW8 p6, []) (k + 1) q (10 + k) hq (by rw [length_initW8]; omega)]
        have hsk := stepAcc_succ_getD 8 gsW (initW8 p6, []) k gk hk (BStat.const false)
        rw [length_initW8] at hsk
        rw [hsk]
        by_cases ha : gk.a = 6
        · have hpk : gk.pa = p6 := by simp [p6, ha]
          exact elimBStep_const_of_const_left _ _ _ (ha ▸ hpk ▸ hk6_at k)
        · have hb : gk.b = 6 := by rcases hkm with h1 | h2; exact absurd h1 ha; exact h2
          have hpk : gk.pb = p6 := by simp [p6, ha]
          exact elimBStep_const_of_const_right _ _ _ (hb ▸ hpk ▸ hk6_at k)
      have hne_out : ∀ p < gsW.length,
          (∀ q, p + 1 ≤ q → ∃ d, (stepAcc 8 gsW (initW8 p6, []) q).1.getD (10 + p) (BStat.const false) =
            BStat.const d) →
          10 + p ≠ oW := by
        intro p hp hcon e
        obtain ⟨d, hd⟩ := hcon gsW.length hp
        obtain ⟨y, y', hne⟩ := hnc6
        apply hne
        have h1 := ((hinv8 y).2 oW).2
        have h2 := ((hinv8 y').2 oW).2
        have hacc_eq : acc8.1.getD oW (BStat.const false) = BStat.const d := by
          rw [← e, hacc8]
          have htake : gsW = gsW.take gsW.length := List.take_length.symm
          change (elimB 8 gsW (initW8 p6, [])).1.getD (10 + p) (BStat.const false) = _
          rw [htake]
          exact hd
        rw [hacc_eq] at h1 h2
        simp only [BStat.val] at h1 h2
        rw [← hevW ((6 : Fin 9).insertNth p6 y), ← hevW ((6 : Fin 9).insertNth p6 y'), ← h1, ← h2]
      have hko : 10 + k ≠ oW := hne_out k hklt (fun q hq => ⟨false, hconst_k q hq⟩)
      rcases hminW k hklt with hcon | ⟨m, gm, hm, hmm⟩
      · exact absurd hcon hko
      · have hmcl := hclnpW.1 m gm hm
        have hkm_lt : k < m := by rcases hmm with ha | hb <;> omega
        have hm_drop : isDroppedAt 8 gsW (initW8 p6, []) m := by
          refine ⟨gm, hm, ?_⟩
          have hck := hconst_k m (by omega)
          rcases hmm with ha | hb
          · exact elimBStep_none_of_const_left _ _ _ false (ha ▸ hck)
          · exact elimBStep_none_of_const_right _ _ _ false (hb ▸ hck)
        cases hp6 : p6
        · have hb2 := hbsize_of_drop {k, m} (by
            intro p hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl <;> assumption)
          rw [Finset.card_pair (Nat.ne_of_lt hkm_lt)] at hb2
          have hlow := G9_x6_false_lower (gsW.length - 2) (by simpa [hp6] using hb2)
          omega
        · have h9_at : ∀ p, (stepAcc 8 gsW (initW8 true, []) p).1.getD 9 (BStat.const false) = BStat.const true := by
            intro p
            unfold stepAcc
            rw [elimB_fst_getD _ _ _ _ _ (by simp [initW8, initAt])]
            simpa using initW8_getD_9 true
          have hh_drop : isDroppedAt 8 gsW (initW8 p6, []) h := by
            refine ⟨gh, hh, ?_⟩
            rw [hp6]
            rcases hhm with ha | hb
            · exact elimBStep_none_of_const_left _ _ _ true (ha ▸ h9_at h)
            · exact elimBStep_none_of_const_right _ _ _ true (hb ▸ h9_at h)
          by_cases hmh : m = h
          · subst hmh
            have hgm : gh = gm := by rw [hh] at hm; injection hm
            subst hgm
            have hmlt : m < gsW.length := (List.getElem?_eq_some_iff.1 hm).1
            have h_const_m : ∀ q, m + 1 ≤ q → ∃ d,
                (stepAcc 8 gsW (initW8 p6, []) q).1.getD (10 + m) (BStat.const false) = BStat.const d := by
              intro q hq
              have hsm := stepAcc_succ_getD 8 gsW (initW8 p6, []) m gh hh (BStat.const false)
              rw [length_initW8] at hsm
              have hacc_both : ∃ d, (elimBStep 8 (stepAcc 8 gsW (initW8 p6, []) m) gh).1.getD
                  (stepAcc 8 gsW (initW8 p6, []) m).1.length (BStat.const false) = BStat.const d := by
                have h9m : (stepAcc 8 gsW (initW8 p6, []) m).1.getD 9 (BStat.const false) = BStat.const true := by
                  rw [hp6]; exact h9_at m
                have hkm_c := hconst_k m (by omega)
                rcases hhm with ha0 | hb0 <;> rcases hmm with ham | hbm
                · exact absurd (ha0.symm.trans ham) (by omega)
                · exact elimBStep_const_of_both_const _ _ _ true false (ha0 ▸ h9m) (hbm ▸ hkm_c)
                · exact elimBStep_const_of_both_const _ _ _ false true (ham ▸ hkm_c) (hb0 ▸ h9m)
                · exact absurd (hb0.symm.trans hbm) (by omega)
              obtain ⟨d, hd⟩ := hacc_both
              refine ⟨d, ?_⟩
              rw [stepAcc_getD_ge 8 gsW (initW8 p6, []) (m + 1) q (10 + m) hq (by rw [length_initW8]; omega)]
              rw [hsm, hd]
            have hmo : 10 + m ≠ oW := hne_out m hmlt h_const_m
            rcases hminW m hmlt with hcon | ⟨h', gh', hh', hhm'⟩
            · exact absurd hcon hmo
            · have hh'cl := hclnpW.1 h' gh' hh'
              have hmh' : m < h' := by rcases hhm' with ha | hb <;> omega
              have hdrop_h' : isDroppedAt 8 gsW (initW8 p6, []) h' := by
                refine ⟨gh', hh', ?_⟩
                obtain ⟨d, hd⟩ := h_const_m h' (by omega)
                rcases hhm' with ha | hb
                · exact elimBStep_none_of_const_left _ _ _ d (ha ▸ hd)
                · exact elimBStep_none_of_const_right _ _ _ d (hb ▸ hd)
              have hb3 := hbsize_of_drop {k, m, h'} (by
                intro p hp
                simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                rcases hp with rfl | rfl | rfl <;> assumption)
              have hcard3 : ({k, m, h'} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_pair (Nat.ne_of_lt hmh')]
              rw [hcard3] at hb3
              have hlow := G9_x6_true_lower (gsW.length - 3) (by simpa [hp6] using hb3)
              omega
          · have hb3 := hbsize_of_drop {k, h, m} (by
              intro p hp
              simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl | rfl <;> assumption)
            have hcard3 : ({k, h, m} : Finset ℕ).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp; omega),
                Finset.card_pair (fun e => hmh e.symm)]
            rw [hcard3] at hb3
            have hlow := G9_x6_true_lower (gsW.length - 3) (by simpa [hp6] using hb3)
            omega
    · push Not at hread9
      have hno9 : ∀ g ∈ gsW, g.a ≠ 9 ∧ g.b ≠ 9 := by
        intro g hg
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
        exact hread9 q g hq
      let gs9 := gsW.map (shBGate 9)
      have hcl9 : CleanB 9 gs9 := by
        intro p g' hp
        simp only [gs9, List.getElem?_map] at hp
        rcases hp_eq : gsW[p]? with _ | g0
        · rw [hp_eq] at hp; simp at hp
        · rw [hp_eq] at hp
          simp only [Option.map_some, Option.some.injEq] at hp
          subst hp
          have h0cl := hclnpW.1 p g0 hp_eq
          have h0no := hno9 g0 (List.mem_of_getElem? hp_eq)
          exact ⟨shift_lt_of_lt (by omega) h0no.1 (by omega),
            shift_lt_of_lt (by omega) h0no.2 (by omega),
            shift_ne h0no.1 h0no.2 h0cl.2.2⟩
      have hev9 : ∀ x : Fin 9 → Bool,
          xor ((bwires gs9 (List.ofFn x)).getD (shift 9 oW) false) poW = edgeFun E_G9 x := by
        intro x
        have hrel := relDB_wires 9 gsW (wInput x) (List.ofFn x) hno9 ⟨by simp [wInput], by simp, ?_⟩
        · rw [hrel.2.2 oW hoW_ne_9]
          exact hevW x
        · intro a ha
          by_cases ha9 : a < 9
          · have hs : shift 9 a = a := by simp [shift, ha9]
            rw [hs, getD_ofFn _ _ _ ha9, getD_wInput_lt _ _ ha9]
          · have hs : shift 9 a = a - 1 := by simp [shift, ha9]
            rw [hs, List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [wInput]; omega)]
      have hlow := G9_lower 12 ⟨gs9, shift 9 oW, poW, hcl9, by simp [gs9, hgsW_len], hev9⟩
      omega

theorem main4308 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo x1 →
    (∀ (x3 : Fin 9 → Bool), x1.eval (List.ofFn x3 ++ [x3 0 || x3 6]) =
      (x3 0 && x3 1 || x3 1 && x3 2 || x3 2 && x3 3 || x3 3 && x3 4 || x3 4 && x3 0 ||
        x3 0 && x3 5 || x3 1 && x3 6 || x3 2 && x3 7 || x3 3 && x3 8 ||
        x3 5 && x3 7 || x3 6 && x3 8 || x3 8 && x3 5)) →
    13 ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates := by
  intro C hfan heval
  by_contra hlt
  push Not at hlt
  obtain ⟨gs, st, hcl, hlen, _, hceval⟩ := convert_circuit 10 C hfan
  have hG9 : ∀ x : Fin 9 → Bool, st.val (bwires gs (wInput x)) = edgeFun E_G9 x := by
    intro x
    rw [hceval (wInput x) (length_wInput x), wInput, heval x]
    simp only [edgeFun, E_G9, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  cases hst : st with
  | const d =>
    have h0 : edgeFun E_G9 (fun _ => false) = false := by decide
    have h1 : edgeFun E_G9 (fun i => i == 0 || i == 1) = true := by decide
    have e0 := hG9 (fun _ => false)
    have e1 := hG9 (fun i => i == 0 || i == 1)
    rw [hst] at e0 e1
    simp only [BStat.val] at e0 e1
    rw [← e0] at h0
    rw [← e1] at h1
    rw [h0] at h1
    cases h1
  | wire o po =>
    apply not_hasWSize_12
    refine ⟨gs, o, po, hcl, by omega, ?_⟩
    intro x
    have e1 := hG9 x
    rw [hst] at e1
    exact e1

end PEqualNP.Outside.L_meta_4308_aux

theorem PEqualNP.Outside.L_meta_4308 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates := by
  exact PEqualNP.Outside.L_meta_4308_aux.main4308

