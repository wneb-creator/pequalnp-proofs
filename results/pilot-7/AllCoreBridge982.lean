import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Reuses project proofs at 3ec921591ffc6536fad46069ec0c219464fb6ffc.

-- Adapted from PEqualNP.MetaComplexity.Helpers.Shannon in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

 
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

 

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.Support in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

 
end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.Elim in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

 
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

 

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

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
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

 
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

 

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

 

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

 

end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

 

end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity3 in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

 

 

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

 
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
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

 
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

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
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
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

 

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

 

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

end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.Parity4 in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base

open PEqualNP.CircuitLowerBounds

 

 
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Sum.inl false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

 
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

 
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Sum.inl c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

 

 
section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

end

 

 
end PEqualNP.Outside.L_meta_982_aux.Finite.Base

-- Adapted from PEqualNP.MetaComplexity.Helpers.PermInputs in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

 

end PEqualNP.Outside.L_meta_982_aux.Finite.Base.PermInputs

-- Adapted from PEqualNP.MetaComplexity.Helpers.ForestElim in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_982_aux.Finite.Base.PermInputs

 
end PEqualNP.Outside.L_meta_982_aux.Finite.Base.Forest

-- Adapted from PEqualNP.MetaComplexity.Helpers.Readers in the Apache-2.0 project.
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Base.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_982_aux.Finite.Base
open PEqualNP.Outside.L_meta_982_aux.Finite.Base.PermInputs

 

 
def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length

theorem Least.hcl {m f gs o} (h : Least m f gs o) : CleanL m gs := h.1

theorem Least.hev {m f gs o} (h : Least m f gs o) :
    ∀ x : Fin m → Bool, vl gs x o = f x := h.2.1

theorem Least.hmin {m f gs o} (h : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      gs.length ≤ gs'.length := h.2.2

 
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

 

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

 

 
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

 

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

 
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

 
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

end
end PEqualNP.Outside.L_meta_982_aux.Finite.Base.Readers

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_982_aux.Finite.Base

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

-- A run can retain either operand for a later gate. Permutations only reorder live wires.
def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (neg save : Bool)
    (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp
end

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
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

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

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
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
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
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
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, L, hlen⟩ := Readers.exists_least n f s hnc h
  have hev : ∀ x, val gs n o x = f x := L.hev
  have ho : o < n + gs.length := by
    by_contra! hout
    obtain ⟨x, y, hn⟩ := hnc
    exact hn (by rw [← L.hev x, ← L.hev y, Readers.vl_beyond _ _ _ hout, Readers.vl_beyond _ _ _ hout])
  have hnd (p : ℕ) (hp : p < gs.length) : n+p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n+p ∈ g.inputs := by
    by_cases e : n+p = o
    · exact Or.inl e
    · obtain ⟨q, _, hg⟩ := L.live hnc p hp (Ne.symm e)
      exact Or.inr ⟨q, hg⟩
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
    exact run_live n gs o L.hcl ho hnd gs.length 0 (by omega)
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
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

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
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

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

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

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
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

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Live

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

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

-- Each successor must fail a necessary condition or match a state in the next layer.
def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

end PEqualNP.Outside.L_meta_982_aux.Finite.Live

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Full
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next m (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _
theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next m (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def wordMask : Nat := 2^512-1

def badPair (y : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code % 512
  let b := code / 512 % 512
  (y.testBit a != y.testBit b) &&
    ws.all (fun w => w.testBit a == w.testBit b)

theorem badPair_no {y s ws} (h : NatRun wordMask y s ws) (code : Nat) :
    badPair y ws code = false := by
  cases hb : badPair y ws code with
  | false => rfl
  | true =>
    have he := run_bits h (code % 512) (code / 512 % 512)
    have hm : wordMask.testBit (code % 512) = wordMask.testBit (code / 512 % 512) := by
      simp [wordMask, Nat.testBit_two_pow_sub_one, Nat.mod_lt _ (by decide : 0 < 512)]
    simp only [badPair, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, beq_iff_eq] at hb
    exact False.elim (hb.1 (he hm hb.2))

def scoreCheck (y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f y

theorem scoreCheck_no {y s ws} (h : NatRun wordMask y s ws) (code : Nat) :
    scoreCheck y s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def bar (y : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat)
    (pairAdvice scoreAdvice : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next wordMask (s + 2 - ws.length) ws fun _ zs =>
      !(badPair y zs (pairAdvice s zs)) &&
      !(scoreCheck y s zs (scoreAdvice s zs)) &&
      !(found S N idx s (ori zs)))

theorem bar_sound {y S N idx ori pairAdvice scoreAdvice} {s i : Nat}
    (hb : bar y S N idx ori pairAdvice scoreAdvice s i = true)
    (hr : ∀ {u ys}, NatRun wordMask y u ys → NatRun wordMask y u (ori ys))
    (h : NatRun wordMask y s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun wordMask y q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      !(badPair y zs (pairAdvice s zs)) &&
      !(scoreCheck y s zs (scoreAdvice s zs)) &&
      !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun wordMask y s zs) : F tag zs = true := by
      simp only [F, badPair_no hz, scoreCheck_no hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {y S N idx ori pairAdvice scoreAdvice} {cap : Nat}
    (hr : ∀ {u ys}, NatRun wordMask y u ys → NatRun wordMask y u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s,
      bar y S N idx ori pairAdvice scoreAdvice s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun wordMask y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end PEqualNP.Outside.L_meta_982_aux.Finite.Full

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_982_aux.Finite.Base PEqualNP.Outside.L_meta_982_aux.Finite.Live

abbrev Fresh {α : Type} (forbidden : List α) (a : α) (ws : List α) : Prop :=
  a ∉ forbidden ∧ a ∉ ws

theorem Fresh.perm {α : Type} {forbidden : List α} {a : α} {xs ys : List α}
    (hp : xs.Perm ys) (h : Fresh forbidden a xs) : Fresh forbidden a ys :=
  ⟨h.1, fun hm => h.2 (hp.mem_iff.2 hm)⟩

theorem Fresh.map {α β : Type} {forbidden : List α} {a : α} {xs : List α}
    (e : α → β) (he : Function.Injective e) (h : Fresh forbidden a xs) :
    Fresh (forbidden.map e) (e a) (xs.map e) := by
  constructor
  · rintro hm
    obtain ⟨b,hb,heq⟩ := List.mem_map.1 hm
    exact h.1 (he heq ▸ hb)
  · rintro hm
    obtain ⟨b,hb,heq⟩ := List.mem_map.1 hm
    exact h.2 (he heq ▸ hb)

def RRun {α : Type} (forbidden : List α) (inv : α → α)
    (meet join : α → α → α) (y : α) (t : Nat) (ws : List α) : Prop :=
  ∀ P : Nat → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, xs.Perm zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool),
      Fresh forbidden (if neg then inv a else a) (a::r) →
      P s ((if neg then inv a else a)::kept save a r) → P (s+1) (a::r)) →
    (∀ {s a b r} (c ka kb : Bool),
      Fresh forbidden (if c then meet a b else join a b) (a::b::r) →
      P s ((if c then meet a b else join a b)::kept ka a (kept kb b r)) →
      P (s+1) (a::b::r)) → P t ws

section
variable {α : Type} {forbidden : List α} {inv : α → α}
  {meet join : α → α → α} {y : α}

theorem RRun.done : RRun forbidden inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem RRun.perm {s xs zs} (p : xs.Perm zs)
    (h : RRun forbidden inv meet join y s xs) : RRun forbidden inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem RRun.one {s a r} (neg save : Bool)
    (hf : Fresh forbidden (if neg then inv a else a) (a::r))
    (h : RRun forbidden inv meet join y s ((if neg then inv a else a)::kept save a r)) :
    RRun forbidden inv meet join y (s+1) (a::r) := fun P d q u b => u neg save hf (h P d q u b)

theorem RRun.two {s a b r} (c ka kb : Bool)
    (hf : Fresh forbidden (if c then meet a b else join a b) (a::b::r))
    (h : RRun forbidden inv meet join y s
      ((if c then meet a b else join a b)::kept ka a (kept kb b r))) :
    RRun forbidden inv meet join y (s+1) (a::b::r) := fun P d q u v => v c ka kb hf (h P d q u v)

theorem RRun.toRun {s ws} (h : RRun forbidden inv meet join y s ws) :
    Run inv meet join y s ws := by
  apply h (fun t ws => Run inv meet join y t ws) Run.done
  · exact fun hp hh => Run.perm hp hh
  · exact fun neg save _ hh => Run.one neg save hh
  · exact fun c ka kb _ hh => Run.two c ka kb hh

theorem RRun.fold {P : ∀ t ws, RRun forbidden inv meet join y t ws → Prop}
    (done : P 0 [y] RRun.done)
    (perm : ∀ {s xs zs} (hp : xs.Perm zs) (h : RRun forbidden inv meet join y s xs),
      P s xs h → P s zs (RRun.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (hf : Fresh forbidden (if neg then inv a else a) (a::r))
      (h : RRun forbidden inv meet join y s ((if neg then inv a else a)::kept save a r)),
      P _ _ h → P _ _ (RRun.one neg save hf h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (hf : Fresh forbidden (if c then meet a b else join a b) (a::b::r))
      (h : RRun forbidden inv meet join y s
        ((if c then meet a b else join a b)::kept ka a (kept kb b r))),
      P _ _ h → P _ _ (RRun.two c ka kb hf h))
    {t ws} (h : RRun forbidden inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RRun forbidden inv meet join y s xs, P s xs h')
    ⟨RRun.done,done⟩
    (fun hp ⟨h',ih⟩ => ⟨RRun.perm hp h',perm hp h' ih⟩)
    (fun n k hf ⟨h',ih⟩ => ⟨RRun.one n k hf h',one n k hf h' ih⟩)
    (fun c a b hf ⟨h',ih⟩ => ⟨RRun.two c a b hf h',two c a b hf h' ih⟩)
  exact hex.elim fun _ hp => hp
end

open Classical in
theorem run_live (n : ℕ) (forbidden : List (BFn n)) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (hfr : ∀ p g, gs[p]? = some g → Fresh forbidden (val gs n (n+p))
      ((liveList gs n o p).map (val gs n))) :
    ∀ d p, p + d = gs.length →
      RRun forbidden (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
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
    exact RRun.perm (hperm.map (val gs n)) RRun.done
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
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        RRun forbidden (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := RRun.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      have hf : Fresh forbidden (if neg then invF (val gs n j) else val gs n j)
          ((val gs n j) :: ((liveList gs n o p).erase j).map (val gs n)) := by
        rw [←hval]
        exact Fresh.perm (by simpa using hp1.map (val gs n)) (hfr p g hg)
      exact RRun.perm (hp1.map (val gs n)).symm (RRun.one neg _ hf IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
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
        have IH' := RRun.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        have hf : Fresh forbidden
            (if decide (g.op = GateOp.and) then meetF (val gs n j) (val gs n k)
              else joinF (val gs n j) (val gs n k))
            ((val gs n j) :: (val gs n k) ::
              (((liveList gs n o p).erase j).erase k).map (val gs n)) := by
          rw [←hval]
          exact Fresh.perm (by simpa using hp1.map (val gs n)) (hfr p g hg)
        exact RRun.perm (hp1.map (val gs n)).symm (RRun.two _ _ _ hf IH')


def forbiddenFns (n : Nat) : List (BFn n) :=
  (fun _ => false) :: (fun _ => true) :: List.ofFn (fun i : Fin n => fun x => x i)

open Classical in
theorem least_fresh {n : Nat} {f : BFn n} {gs : List Gate} {o : Nat}
    (L : Readers.Least n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (p : Nat) (g : Gate) (hg : gs[p]? = some g) :
    Fresh (forbiddenFns n) (val gs n (n+p)) ((liveList gs n o p).map (val gs n)) := by
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  constructor
  · intro hm
    simp only [forbiddenFns,List.mem_cons,List.mem_ofFn] at hm
    rcases hm with h | h | ⟨i,h⟩
    · apply L.no_const hnc p hp false
      intro u
      exact congrFun h u
    · apply L.no_const hnc p hp true
      intro u
      exact congrFun h u
    · apply L.no_alias hnc p hp i (by omega)
      intro u
      have he := congrFun h u
      change val gs n (n+p) u = val gs n i u
      rw [val_input]
      exact he.symm
  · rintro hm
    obtain ⟨a,ha,he⟩ := List.mem_map.1 hm
    have hal := (mem_liveList gs n o p a).1 ha
    apply L.no_alias hnc p hp a hal.1
    intro u
    exact (congrFun he u).symm

open Classical in
theorem exists_run {n : Nat} (f : BFn n) (hnc : ∃ x y, f x ≠ f y) (s : Nat)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun i : Fin n => fun x : Fin n → Bool => x i) ∧
      RRun (forbiddenFns n) invF meetF joinF f s' ws := by
  obtain ⟨gs,o,L,hlen⟩ := Readers.exists_least n f s hnc h
  have hev : ∀ x, val gs n o x = f x := L.hev
  have ho : o < n + gs.length := by
    by_contra! hout
    obtain ⟨x,y,hn⟩ := hnc
    exact hn (by rw [←L.hev x,←L.hev y,Readers.vl_beyond _ _ _ hout,Readers.vl_beyond _ _ _ hout])
  have hnd (p : Nat) (hp : p < gs.length) : n+p = o ∨
      ∃ (q : Nat) (g : Gate), gs[q]? = some g ∧ n+p ∈ g.inputs := by
    by_cases e : n+p = o
    · exact Or.inl e
    · obtain ⟨q,_,hg⟩ := L.live hnc p hp (Ne.symm e)
      exact Or.inr ⟨q,hg⟩
  refine ⟨gs.length,by omega,(liveList gs n o 0).map (val gs n),?_,?_⟩
  · have e : (List.ofFn fun i : Fin n => fun x : Fin n → Bool => x i) =
        (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
        exact (val_input gs n ⟨i,by simpa using h1⟩).symm
    rw [e]
    exact List.filter_sublist.map _
  · have hf : val gs n o = f := funext hev
    rw [←hf]
    exact run_live n _ gs o L.hcl ho hnd (least_fresh L hnc) gs.length 0 (by omega)

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem RRun.map {α β : Type} (e : α → β) (he : Function.Injective e)
    {forbidden : List α} {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : Nat} {ws : List α} (h : RRun forbidden inv meet join y s ws) :
    RRun (forbidden.map e) inv' meet' join' (e y) s (ws.map e) := by
  induction h using RRun.fold with
  | done => exact RRun.done
  | perm hp _ ih => exact RRun.perm (hp.map e) ih
  | @one s a rest neg save hf _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    apply RRun.one neg save _ ih
    have hfr := Fresh.map e he hf
    cases neg <;> simpa [hi] using hfr
  | @two s a b rest conj ka kb hf _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    apply RRun.two conj ka kb _ ih
    have hfr := Fresh.map e he hf
    cases conj <;> simpa [hm,hj] using hfr

abbrev RNatRun (forbidden : List Nat) (m : Nat) :=
  RRun forbidden (· ^^^ m) (· &&& ·) (· ||| ·)

def next (forbidden : List Nat) (m sl : Nat) (ws : List Nat)
    (f : Nat → List Nat → Bool) : Bool :=
  Live.next m sl ws (fun t zs => decide (Fresh forbidden (zs.headD 0) ws) && f t zs)

theorem next_one {forbidden m y a rest} {neg save : Bool} {s ws}
    (p : (a :: rest).Perm ws)
    (fresh : Fresh forbidden (if neg then a ^^^ m else a) (a::rest))
    (h : RNatRun forbidden m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, RNatRun forbidden m y s ys → f t ys = true) :
    next forbidden m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h.toRun
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  unfold next Live.next
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (RRun.perm ((keep_perm pr save a).cons _) h)
  have hfr := Fresh.perm p fresh
  cases save with
  | false => simp [kept] at ht; simp [ht,hfr]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2,hfr]

theorem next_two_sorted {forbidden m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (fresh : Fresh forbidden (if conj then a &&& b else a ||| b) (a::b::rest))
    (h : RNatRun forbidden m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, RNatRun forbidden m y s ys → f t ys = true) :
    next forbidden m (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h.toRun
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  unfold next Live.next
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (RRun.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  have hfr := Fresh.perm p fresh
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp [Fresh, hfr.1, hfr.2, ht] <;> omega

theorem next_two {forbidden m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (fresh : Fresh forbidden (if conj then a &&& b else a ||| b) (a::b::rest))
    (h : RNatRun forbidden m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, RNatRun forbidden m y s ys → f t ys = true) :
    next forbidden m (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p fresh h f hf
  · have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    have hfr := Fresh.perm (List.Perm.swap b a rest) fresh
    rw [he] at hfr h
    apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba
      ((List.Perm.swap _ _ _).trans p) hfr _ f hf
    apply RRun.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem next_complete {forbidden m y t ws} (h : RNatRun forbidden m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, RNatRun forbidden m y s ys → f t ys = true) →
      next forbidden m (s+2-zs.length) zs f = true := by
  induction h using RRun.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save fresh h ih => intro s he zs p f hf; cases he; exact next_one p fresh h f hf
  | two conj ka kb fresh h ih => intro s he zs p f hf; cases he; exact next_two p fresh h f hf

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live
open PEqualNP.Outside.L_meta_982_aux.Finite.Full (wordMask badPair scoreCheck)
def bar (forbidden : List Nat) (y : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat)
    (pairAdvice scoreAdvice : Nat → List Nat → Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next forbidden wordMask (s + 2 - ws.length) ws fun _ zs =>
      !(badPair y zs (pairAdvice s zs)) &&
      !(Full.scoreCheck y s zs (scoreAdvice s zs)) &&
      !(found S N idx s (ori zs)))

theorem bar_sound {forbidden y S N idx ori pairAdvice scoreAdvice} {s i : Nat}
    (hb : bar forbidden y S N idx ori pairAdvice scoreAdvice s i = true)
    (hr : ∀ {u ys}, RNatRun forbidden wordMask y u ys → RNatRun forbidden wordMask y u (ori ys))
    (h : RNatRun forbidden wordMask y s (S s i)) :
    ∃ q < s, ∃ j < N q, RNatRun forbidden wordMask y q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h.toRun rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      !(badPair y zs (pairAdvice s zs)) &&
      !(Full.scoreCheck y s zs (scoreAdvice s zs)) &&
      !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : RNatRun forbidden wordMask y s zs) : F tag zs = true := by
      simp only [F, Full.badPair_no hz.toRun, Full.scoreCheck_no hz.toRun, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (RRun.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {forbidden y S N idx ori pairAdvice scoreAdvice} {cap : Nat}
    (hr : ∀ {u ys}, RNatRun forbidden wordMask y u ys → RNatRun forbidden wordMask y u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s,
      bar forbidden y S N idx ori pairAdvice scoreAdvice s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RNatRun forbidden wordMask y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

def pack9 (x : Fin 9 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pack9_spec (x : Fin 9 → Bool) : pack9 x < 512 ∧ pt 9 (pack9 x) = x := by
  revert x
  decide +kernel

def encode9 (f : BFn 9) : Nat := encL f (List.range 512)

theorem encode9_injective : Function.Injective encode9 := by
  intro a b he
  funext x
  obtain ⟨hx,heq⟩ := pack9_spec x
  have hb := congrArg (fun w : Nat => w.testBit (pack9 x)) he
  simp only [encode9,encL_testBit] at hb
  simpa [hx,heq] using hb

theorem encode9_inv (a : BFn 9) : encode9 (invF a) = encode9 a ^^^ Full.wordMask := by
  simpa [encode9,Full.wordMask] using encL_inv a (List.range 512)

theorem encode9_and (a b : BFn 9) : encode9 (meetF a b) = encode9 a &&& encode9 b :=
  encL_and a b (List.range 512)

theorem encode9_or (a b : BFn 9) : encode9 (joinF a b) = encode9 a ||| encode9 b :=
  encL_or a b (List.range 512)

set_option maxRecDepth 100000 in
theorem encoded_run {y : BFn 9} {s ws} (h : RRun (forbiddenFns 9) invF meetF joinF y s ws) :
    RNatRun ((forbiddenFns 9).map encode9) Full.wordMask (encode9 y) s (ws.map encode9) :=
  h.map encode9 encode9_injective encode9_inv encode9_and encode9_or

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live
open PEqualNP.Outside.L_meta_982_aux.Finite.Full (wordMask)

theorem RRun.forbidden_mono {α : Type} {A B : List α} {inv meet join y s ws}
    (hsub : B.Subset A) (h : @RRun α A inv meet join y s ws) :
    RRun B inv meet join y s ws := by
  induction h using RRun.fold with
  | done => exact RRun.done
  | perm hp _ ih => exact RRun.perm hp ih
  | one neg save hf _ ih => exact RRun.one neg save ⟨fun hm => hf.1 (hsub hm),hf.2⟩ ih
  | two conj ka kb hf _ ih => exact RRun.two conj ka kb ⟨fun hm => hf.1 (hsub hm),hf.2⟩ ih

def checkBar (forbidden : List Nat) (y : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat)
    (reject : Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [y])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next forbidden wordMask (s + 2 - ws.length) ws fun _ zs =>
      !(reject s zs) && !(found S N idx s (ori zs)))

theorem checkBar_sound {forbidden y S N idx ori reject} {s i : Nat}
    (hb : checkBar forbidden y S N idx ori reject s i = true)
    (hr : ∀ {u ys}, RNatRun forbidden wordMask y u ys → RNatRun forbidden wordMask y u (ori ys))
    (hj : ∀ {u ys}, RNatRun forbidden wordMask y u ys → reject u ys = false)
    (h : RNatRun forbidden wordMask y s (S s i)) :
    ∃ q < s, ∃ j < N q, RNatRun forbidden wordMask y q (S q j) := by
  cases s with
  | zero => simp [checkBar, zero_done h.toRun rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) := !(reject s zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : RNatRun forbidden wordMask y s zs) : F tag zs = true := by
      simp only [F, hj hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hidx
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hidx (RRun.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem checkBar_all {forbidden y S N idx ori reject} {cap : Nat}
    (hr : ∀ {u ys}, RNatRun forbidden wordMask y u ys → RNatRun forbidden wordMask y u (ori ys))
    (hj : ∀ {u ys}, RNatRun forbidden wordMask y u ys → reject u ys = false)
    (hc : ∀ s ≤ cap, ∀ i < N s, checkBar forbidden y S N idx ori reject s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RNatRun forbidden wordMask y s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj',h⟩ := checkBar_sound (hc s hs i hi) hr hj hh
    exact ih q hq (by omega) j hj' h

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem encL_injective_of_cover {n : Nat} (rows : List Nat)
    (hc : ∀ x : Fin n → Bool, ∃ v ∈ rows, pt n v = x) :
    Function.Injective (fun f : BFn n => encL f rows) := by
  intro a b he
  funext x
  obtain ⟨v,hv,hx⟩ := hc x
  obtain ⟨i,hi,hi'⟩ := List.mem_iff_getElem.1 hv
  have hb := congrArg (fun w : Nat => w.testBit i) he
  simp only [encL_testBit] at hb
  simpa [hi,hi',hx] using hb

theorem encoded_run_rows {n : Nat} {y : BFn n} {s ws} (rows : List Nat)
    (hc : ∀ x : Fin n → Bool, ∃ v ∈ rows, pt n v = x)
    (h : RRun (forbiddenFns n) invF meetF joinF y s ws) :
    RNatRun ((forbiddenFns n).map fun f => encL f rows) (2^rows.length-1)
      (encL y rows) s (ws.map fun f => encL f rows) :=
  h.map _ (encL_injective_of_cover rows hc) (fun a => encL_inv a rows)
    (fun a b => encL_and a b rows) (fun a b => encL_or a b rows)

theorem initial_full {m y s initial ws}
    (hn : initial.Nodup) (hs : ws.Sublist initial)
    (he : ∀ a ∈ initial, ∃ i j : Nat, m.testBit i = m.testBit j ∧
      y.testBit i ≠ y.testBit j ∧ ∀ b ∈ initial, b ≠ a → b.testBit i = b.testBit j)
    (h : NatRun m y s ws) : ws.Perm initial := by
  apply (List.perm_ext_iff_of_nodup (hn.sublist hs) hn).2
  intro a
  constructor
  · exact fun ha => hs.subset ha
  · intro ha
    by_contra hnmem
    obtain ⟨i,j,hm,hy,hb⟩ := he a ha
    apply hy
    apply run_bits h i j hm
    intro b hbw
    exact hb b (hs.subset hbw) (fun hba => hnmem (hba ▸ hbw))

def scoreCheckW (k width s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    ws.length == s+1 &&
      (ws.map (eval6 (fld code width 0) (fld code width 1) (fld code width 2)
        (fld code width 3) (fld code width 4) (fld code width 5))).sum <
      eval6 (fld code width 0) (fld code width 1) (fld code width 2)
        (fld code width 3) (fld code width 4) (fld code width 5) (goal k)

theorem scoreCheckW_no {k s ws} (width code : Nat)
    (h : NatRun (mask k) (goal k) s ws) : scoreCheckW k width s ws code = false := by
  unfold scoreCheckW
  split
  · rfl
  · by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def scrW (k width s : Nat) (pool : List Nat) (ws : List Nat) : Bool :=
  ws.length == s+1 && pool.any (scoreCheckW k width s ws)

theorem scrW_no {k s ws} (width : Nat) (pool : List Nat)
    (h : NatRun (mask k) (goal k) s ws) : scrW k width s pool ws = false := by
  unfold scrW
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro code _
  rw [scoreCheckW_no width code h]
  simp

def pairedBar (forbidden : List Nat) (k width : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → Nat → Nat → Nat)
    (ori : Nat → Nat → Nat → List Nat → List Nat)
    (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next forbidden (mask k) (s+2-ws.length) ws fun tag zs =>
      covers k s zs && !(scrW k width s pool zs) &&
        !(decide (idx (s+1) i tag < N s) &&
          (ori (s+1) i tag zs).isPerm (S s (idx (s+1) i tag))))

theorem pairedBar_sound {forbidden k width S N idx ori pool} {s i : Nat}
    (hb : pairedBar forbidden k width S N idx ori pool s i = true)
    (hr : ∀ p i tag {u ys}, RNatRun forbidden (mask k) (goal k) u ys →
      RNatRun forbidden (mask k) (goal k) u (ori p i tag ys))
    (h : RNatRun forbidden (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, RNatRun forbidden (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [pairedBar,zero_done h.toRun rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) :=
      covers k s zs && !(scrW k width s pool zs) &&
        !(decide (idx (s+1) i tag < N s) &&
          (ori (s+1) i tag zs).isPerm (S s (idx (s+1) i tag)))
    have hF (tag : Nat) (zs) (hz : RNatRun forbidden (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz.toRun,scrW_no width pool hz.toRun,Bool.not_false,Bool.true_and]
      simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (RRun.perm p (hr (s+1) i tag hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem pairedBar_all {forbidden k width S N idx ori pool} {cap : Nat}
    (hr : ∀ p i tag {u ys}, RNatRun forbidden (mask k) (goal k) u ys →
      RNatRun forbidden (mask k) (goal k) u (ori p i tag ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, pairedBar forbidden k width S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RNatRun forbidden (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := pairedBar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

def rejectDepth (forbidden : List Nat) (k width : Nat) (pool : List Nat) :
    Nat → Nat → List Nat → Bool
  | 0,s,ws => !(covers k s ws) || scrW k width s pool ws
  | _+1,0,ws => !(covers k 0 ws) || scrW k width 0 pool ws || !(ws == [goal k])
  | d+1,s+1,ws => !(covers k (s+1) ws) || scrW k width (s+1) pool ws ||
      !(next forbidden (mask k) (s+2-ws.length) ws fun _ zs =>
        !(rejectDepth forbidden k width pool d s zs))

theorem rejectDepth_no {forbidden k width pool} (d : Nat) {s ws}
    (h : RNatRun forbidden (mask k) (goal k) s ws) :
    rejectDepth forbidden k width pool d s ws = false := by
  induction d generalizing s ws with
  | zero => simp [rejectDepth,covers_ok h.toRun,scrW_no width pool h.toRun]
  | succ d ih =>
    cases s with
    | zero =>
      have hw := zero_done h.toRun rfl
      subst ws
      simp [rejectDepth,covers_ok h.toRun,scrW_no width pool h.toRun]
    | succ s =>
      let F (_ : Nat) (zs : List Nat) : Bool := !(rejectDepth forbidden k width pool d s zs)
      have hF (tag : Nat) (zs : List Nat) (hz : RNatRun forbidden (mask k) (goal k) s zs) :
          F tag zs = true := by simp [F,ih hz]
      have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
      simpa [rejectDepth,covers_ok h.toRun,scrW_no width pool h.toRun,F] using hN

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Fast
open PEqualNP.Outside.L_meta_982_aux.Finite

def diff (k w : Nat) : Nat := w ^^^ (w / 2^k)

theorem diff_eq (k w : Nat) : diff k w = Live.diff k w := by
  simp [diff, Live.diff, Nat.shiftRight_eq_div_pow]

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_eq (k : Nat) (ws : List Nat) : cov k ws = Live.cov k ws := by
  induction ws with
  | nil => rfl
  | cons a t ih => simp [cov, Live.cov, diff_eq, ih]

def diffUp (k w : Nat) : Nat := (w / 2^k) &&& (w ^^^ Live.lo k)

theorem diffUp_eq (k w : Nat) : diffUp k w = Live.diffUp k w := by
  simp [diffUp, Live.diffUp, Nat.shiftRight_eq_div_pow]

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_eq (k : Nat) (ws : List Nat) : covUp k ws = Live.covUp k ws := by
  induction ws with
  | nil => rfl
  | cons a t ih => simp [covUp, Live.covUp, diffUp_eq, ih]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws % 2^k == Live.lo k
  else cov k ws % 2^k == Live.lo k

theorem covers_eq (k s : Nat) (ws : List Nat) : covers k s ws = Live.covers k s ws := by
  simp [covers, Live.covers, cov_eq, covUp_eq, Live.lo,
    Nat.and_two_pow_sub_one_eq_mod]

def bit (w i : Nat) : Bool := decide (w / 2^i % 2 = 1)

theorem bit_eq (w i : Nat) : bit w i = w.testBit i :=
  Nat.testBit_eq_decide_div_mod_eq.symm

def eval6 (a b c d e f v : Nat) : Nat :=
  Live.value6 (bit v a) (bit v b) (bit v c) (bit v d) (bit v e) (bit v f)

theorem eval6_eq (a b c d e f v : Nat) : eval6 a b c d e f v = Live.eval6 a b c d e f v := by
  simp [eval6, Live.eval6, bit_eq]

theorem eval6_fun_eq : eval6 = Live.eval6 := by
  funext a b c d e f v
  exact eval6_eq a b c d e f v

def fld (T w i : Nat) : Nat := (T / 2^(w*i)) % 2^w

theorem fld_eq (T w i : Nat) : fld T w i = Live.fld T w i := by
  simp [fld, Live.fld, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

def scoreCheck (k width s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    ws.length == s+1 &&
      (ws.map (eval6 (fld code width 0) (fld code width 1) (fld code width 2)
        (fld code width 3) (fld code width 4) (fld code width 5))).sum <
      eval6 (fld code width 0) (fld code width 1) (fld code width 2)
        (fld code width 3) (fld code width 4) (fld code width 5) (Live.goal k)

theorem scoreCheck_eq (k width s : Nat) (ws : List Nat) (code : Nat) :
    scoreCheck k width s ws code = Reduced.scoreCheckW k width s ws code := by
  simp [scoreCheck, Reduced.scoreCheckW, fld_eq, eval6_fun_eq]

theorem scoreCheck_fun_eq : scoreCheck = Reduced.scoreCheckW := by
  funext k width s ws code
  exact scoreCheck_eq k width s ws code

def scr (k width s : Nat) (pool : List Nat) (ws : List Nat) : Bool :=
  ws.length == s+1 && pool.any (scoreCheck k width s ws)

theorem scr_eq (k width s : Nat) (pool : List Nat) (ws : List Nat) :
    scr k width s pool ws = Reduced.scrW k width s pool ws := by
  simp [scr, Reduced.scrW, scoreCheck_fun_eq]

def rejectDepth (forbidden : List Nat) (k width : Nat) (pool : List Nat) :
    Nat → Nat → List Nat → Bool
  | 0,s,ws => !(covers k s ws) || scr k width s pool ws
  | _+1,0,ws => !(covers k 0 ws) || scr k width 0 pool ws || !(ws == [Live.goal k])
  | d+1,s+1,ws => !(covers k (s+1) ws) || scr k width (s+1) pool ws ||
      !(Reduced.next forbidden (Live.mask k) (s+2-ws.length) ws fun _ zs =>
        !(rejectDepth forbidden k width pool d s zs))

theorem rejectDepth_eq (forbidden : List Nat) (k width : Nat) (pool : List Nat)
    (d s : Nat) (ws : List Nat) :
    rejectDepth forbidden k width pool d s ws =
      Reduced.rejectDepth forbidden k width pool d s ws := by
  induction d generalizing s ws with
  | zero => simp [rejectDepth, Reduced.rejectDepth, covers_eq, scr_eq]
  | succ d ih => cases s <;> simp [rejectDepth, Reduced.rejectDepth, covers_eq, scr_eq, ih]

def pairedBar (forbidden : List Nat) (k width : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → Nat → Nat → Nat)
    (ori : Nat → Nat → Nat → List Nat → List Nat)
    (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Live.goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(Reduced.next forbidden (Live.mask k) (s+2-ws.length) ws fun tag zs =>
      covers k s zs && !(scr k width s pool zs) &&
        !(decide (idx (s+1) i tag < N s) &&
          (ori (s+1) i tag zs).isPerm (S s (idx (s+1) i tag))))

theorem pairedBar_eq (forbidden : List Nat) (k width : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → Nat → Nat → Nat)
    (ori : Nat → Nat → Nat → List Nat → List Nat)
    (pool : List Nat) (s i : Nat) :
    pairedBar forbidden k width S N idx ori pool s i =
      Reduced.pairedBar forbidden k width S N idx ori pool s i := by
  cases s <;> simp [pairedBar, Reduced.pairedBar, covers_eq, scr_eq]

end PEqualNP.Outside.L_meta_982_aux.Finite.Fast

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem lower_from_rows {n bound : Nat} (f : BFn n) (rows : List Nat)
    (initial forbidden : List Nat) (m y : Nat)
    (hnc : ∃ x z, f x ≠ f z)
    (hcover : ∀ x : Fin n → Bool, ∃ v ∈ rows, pt n v = x)
    (hi : (List.ofFn (fun i : Fin n => fun x : Fin n → Bool => x i)).map
      (fun g => encL g rows) = initial)
    (hf : (forbiddenFns n).map (fun g => encL g rows) = forbidden)
    (hm : 2^rows.length-1 = m) (hy : encL f rows = y)
    (hn : initial.Nodup)
    (he : ∀ a ∈ initial, ∃ i j : Nat, m.testBit i = m.testBit j ∧
      y.testBit i ≠ y.testBit j ∧ ∀ b ∈ initial, b ≠ a → b.testBit i = b.testBit j)
    (hno : ∀ t < bound, ¬ RNatRun forbidden m y t initial) :
    ∀ s, HasCircuitSize n f s → bound ≤ s := by
  intro s hs
  by_contra! hlt
  obtain ⟨t,ht,ws,hsub,hrun⟩ := exists_run f hnc s hs
  have hr := encoded_run_rows rows hcover hrun
  rw [hf,hm,hy] at hr
  have hsub' : (ws.map (fun g => encL g rows)).Sublist initial := by
    rw [←hi]
    exact hsub.map _
  have hp := initial_full hn hsub' he hr.toRun
  exact hno t (by omega) (RRun.perm hp hr)

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed0K : Nat := 151

def seed0ScoreWidth : Nat := 10



def seed0Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 6, 7, 9, 11, 13, 14, 15, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 3, 5, 6, 9, 11, 13, 63, 3, 63, 5, 63, 9, 24, 25, 40, 41, 48, 63, 3, 6, 9, 11, 14, 24, 26, 40, 42, 63, 5, 6, 9, 13, 14, 24, 28, 40, 44, 63, 24, 63, 3, 5, 9, 19, 21, 24, 25, 48, 49, 63, 3, 6, 19, 22, 24, 26, 48, 50, 54, 63, 5, 6, 21, 22, 24, 28, 48, 52, 54, 63, 40, 63, 3, 5, 9, 35, 37, 40, 41, 48, 49, 63, 3, 6, 35, 38, 40, 42, 48, 50, 54, 63, 5, 6, 37, 38, 40, 44, 48, 52, 54, 63]

def seed0Inputs : List Nat := [0x2058175fa058175fa0d836affbaaaaaabaabbd800007fe000007fe00000000fe000000000000, 0x30aebe09b0aebe09a12d6e05d5ccccccdccdd6801ff800001ff800001ff80300000000000000, 0x3afc2a12bafc2a12b5b84a0766f0f0f0ef0ee77fe000007fe000007fe0000c00000000000000, 0x2308c264e308c264ffcff2fd78ff00ff0ff0f800000000000000007ffffff000000000000000, 0x3c0f0380bfcff3f8e609833540ffff000fff00000000007fffffff8000000000000000000000, 0x3fcff3f8fc0f0380b80e03c540fffffff000007fffffff800000000000000000000000000000]

def seed0Mask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed0Goal : Nat := 0x3fffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000

def seed0Forbidden : List Nat := [0, seed0Mask] ++ seed0Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed8K : Nat := 218

def seed8ScoreWidth : Nat := 10



def seed8Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 6, 6, 6, 6, 8, 9, 9, 9, 9, 12, 12, 12, 12, 12, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 32, 33, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 64, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 68, 68, 68, 68, 70, 70, 70, 70, 70, 70, 70, 72, 72, 72, 72, 73, 73, 73, 73, 73, 73, 73, 76, 76, 76, 76, 76, 76, 76, 3, 5, 7, 10, 11, 13, 14, 15, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 35, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 71, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 127, 127, 127, 3, 5, 7, 127, 127, 3, 10, 11, 127, 5, 10, 28, 44, 127, 127, 5, 20, 21, 127, 3, 20, 26, 82, 127, 26, 28, 40, 80, 127, 10, 20, 56, 57, 88, 89, 127, 127, 3, 37, 40, 97, 127, 10, 40, 42, 127, 20, 37, 44, 96, 127, 5, 40, 52, 54, 100, 102, 127, 80, 96, 112, 127, 5, 35, 41, 51, 57, 96, 127, 10, 19, 22, 51, 54, 80, 127, 127, 5, 67, 80, 97, 127, 10, 67, 82, 96, 127, 20, 80, 84, 127, 3, 74, 78, 80, 98, 102, 127, 40, 96, 104, 127, 3, 69, 77, 81, 89, 96, 127, 13, 14, 20, 40, 77, 78, 127]

def seed8Inputs : List Nat := [0xa37e20c4b7957e20ca37d108ee3bff5555555555556f555aaf556dc07f00000f807f00000fbf801e07808000000000000000000000000, 0xc5063bc5e5bf2a344363831ec65fdf999999999999bb999ccb9e7740000fe1f03f800fe0f00003e0003d0000000000000000000000000, 0xef1a326c23a9063ede2585297fb1efe1e1e1e1e1e1cde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000, 0xf75363446183522153e9fb7a47dd8ffe01fe01fe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000, 0x8962247d29fd63664621fdbf76918ffffe0001fffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000, 0x9183f84631b1fbbf7bbd994847118ffffffffe000001fffffe000000000000003fffffffffc0000000000000000000000000000000000, 0xe1fbbf77bdc183f86231e18c46118ffffffffffffffe00000000003fffffffffc00000000000000000000000000000000000000000000]

def seed8Mask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed8Goal : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000

def seed8Forbidden : List Nat := [0, seed8Mask] ++ seed8Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed13K : Nat := 276

def seed13ScoreWidth : Nat := 10



def seed13Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8, 8, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 36, 36, 36, 36, 36, 36, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 96, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 104, 104, 104, 104, 104, 104, 104, 104, 112, 112, 112, 112, 112, 112, 112, 112, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 35, 37, 38, 39, 41, 42, 43, 45, 46, 47, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 68, 69, 70, 71, 73, 75, 76, 77, 78, 79, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 98, 99, 100, 101, 102, 103, 105, 106, 107, 108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 9, 11, 13, 17, 19, 21, 24, 34, 37, 41, 49, 67, 68, 73, 81, 127, 3, 34, 35, 98, 127, 5, 68, 69, 100, 127, 9, 127, 6, 9, 14, 24, 26, 42, 127, 6, 9, 14, 24, 28, 76, 127, 17, 127, 6, 17, 22, 24, 26, 50, 127, 6, 17, 22, 24, 28, 84, 127, 34, 127, 3, 5, 35, 37, 127, 5, 34, 38, 68, 100, 127, 9, 127, 14, 24, 28, 34, 37, 41, 45, 46, 60, 68, 100, 108, 127, 17, 127, 22, 24, 28, 34, 37, 49, 53, 54, 60, 68, 100, 116, 127, 68, 127, 3, 5, 67, 69, 127, 3, 34, 68, 70, 98, 127, 9, 127, 14, 24, 26, 34, 67, 68, 73, 75, 78, 90, 98, 106, 127, 17, 127, 22, 24, 26, 34, 67, 68, 81, 83, 86, 90, 98, 114, 127, 34, 68, 127, 9, 17, 34, 37, 67, 68, 99, 101, 105, 113, 127, 9, 34, 68, 105, 106, 108, 120, 127, 17, 34, 68, 113, 114, 116, 120, 127]

def seed13Inputs : List Nat := [0x8989fb721a1c34387f41c383870fe850b850bad7bcffaaab56aaaaebad55b6daaaf7b0000ffe0000000003e0000000007c00000000003ffff0000000000000000000000000, 0x92928a97f3b7e76eeb4226844d3578bd68bd687e2249cccd9b3cccb2ce66db6f335ad00000003ffe7ffcfc00000000000001fc01fc07c00000000000000000000000000000, 0xa4a4951a2434486b35ff56feadeeaeb16eb16fc24492f0f1e3cf0f3cf7871c73c39ce0000000000000000007ffcfff9f80fe00fe00f8000000000000000000000000000000, 0xc0f9a03240d6f1f821441acf3f042b162fdfb842891cff01fc0ff03f07f81f83fc1f000ff00000007fff0000000fffe0000000ffff00000000000000000000000000000000, 0xf9c0c05378fc81a821679f8835042fdfbb16284311e0fffe000fffc007ffe003ffe00ff000003fff80000007fff0000000ffff000000000000000000000000000000000000, 0xfafaf9978117022ca177e2efc5b7381828182c7a1e00fffffff0000007fffffc00000fffffffc00000000007ffffffffff0000000000000000000000000000000000000000, 0xfcfcfe1bfe17fc2f39f802f005c42c102c102f63e000fffffffffffff800000000000ffffffffffffffffff800000000000000000000000000000000000000000000000000]

def seed13Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed13Goal : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000

def seed13Forbidden : List Nat := [0, seed13Mask] ++ seed13Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed18K : Nat := 276

def seed18ScoreWidth : Nat := 10



def seed18Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 10, 12, 16, 16, 16, 18, 20, 24, 24, 24, 24, 24, 24, 26, 26, 26, 26, 26, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 48, 48, 48, 48, 48, 48, 48, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 72, 72, 72, 72, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 25, 27, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 73, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 6, 9, 11, 13, 17, 19, 21, 25, 35, 37, 49, 67, 69, 73, 127, 3, 6, 127, 5, 6, 127, 40, 41, 127, 127, 127, 80, 81, 127, 127, 127, 9, 17, 25, 40, 80, 127, 6, 25, 27, 30, 40, 58, 80, 90, 127, 6, 25, 29, 30, 40, 60, 80, 92, 127, 40, 127, 3, 5, 9, 17, 35, 37, 40, 41, 49, 96, 97, 127, 3, 6, 35, 40, 42, 98, 127, 5, 6, 37, 40, 44, 100, 127, 17, 40, 49, 80, 96, 112, 127, 6, 35, 38, 40, 49, 51, 54, 58, 80, 96, 114, 127, 6, 37, 38, 40, 49, 53, 54, 60, 80, 96, 116, 127, 80, 127, 3, 5, 9, 17, 67, 69, 73, 80, 81, 96, 97, 127, 3, 6, 67, 80, 82, 98, 127, 5, 6, 69, 80, 84, 100, 127, 9, 40, 73, 80, 96, 104, 127, 6, 40, 67, 70, 73, 75, 78, 80, 90, 96, 106, 127, 6, 40, 69, 70, 73, 77, 78, 80, 92, 96, 108, 127]

def seed18Inputs : List Nat := [0x8348348b162ebfd065065162c5dbfa0d069fdeb7fff75555555555557baabd55def7b000000000007ff800000000000fff00000000003fffe0000000000000000000000000, 0x849d6d810bbc08d08b9cf02177811a13ad839cde492b999999999999adccd666eb5ad000fff0003f8000001ffe0007f000001ff01081c00000000000000000000000000000, 0xd6d84981de141159cf08b03bc2822b5b09839cfa924de1e1e1e1e1e1cef0e787739cefff00001fc00001ffe00003f800003fe000210e000000000000000000000000000000, 0xd72d72cf02042251111110ac588c4f7dbeb79f930471fe01fe01fe01f0ff07f87c1f0fffffffe0000000000000000000003fffffc1f0000000000000000000000000000000, 0x9809809162c4c47be1be1b6040908bddeedbfc922781fffe0001fffe00fff8007fe00000000000000001fffffffc0000003ffffffe00000000000000000000000000000000, 0xe02e02e58307005dfddfddbe7cff0e6130a39f923801fffffffe000000ffffff80000000000000000001ffffffffffffffc000000000000000000000000000000000000000, 0xffcffcf9f3e7f87e01e01e3060e00b81c0c3fc93c001ffffffffffffff00000000000ffffffffffffffe000000000000000000000000000000000000000000000000000000]

def seed18Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed18Goal : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000

def seed18Forbidden : List Nat := [0, seed18Mask] ++ seed18Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed19K : Nat := 284

def seed19ScoreWidth : Nat := 10



def seed19Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 20, 20, 20, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 33, 33, 33, 34, 34, 34, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 96, 96, 96, 96, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 3, 5, 6, 7, 9, 11, 13, 14, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 36, 37, 38, 39, 41, 43, 44, 45, 46, 47, 50, 51, 52, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 9, 11, 13, 35, 41, 67, 127, 3, 6, 18, 19, 22, 35, 50, 67, 127, 36, 100, 127, 9, 72, 127, 3, 6, 9, 11, 14, 18, 26, 72, 74, 127, 6, 9, 14, 36, 44, 76, 127, 18, 80, 127, 3, 5, 9, 18, 19, 21, 25, 80, 81, 127, 5, 18, 21, 36, 52, 84, 127, 92, 127, 5, 6, 9, 18, 29, 30, 36, 60, 72, 76, 80, 84, 88, 92, 127, 127, 35, 41, 127, 35, 50, 127, 9, 127, 3, 14, 18, 36, 41, 43, 46, 58, 74, 104, 106, 127, 18, 127, 3, 9, 21, 36, 50, 51, 53, 57, 81, 112, 113, 127, 9, 18, 36, 57, 58, 60, 72, 80, 120, 127, 72, 80, 88, 127, 5, 9, 69, 73, 80, 81, 127, 6, 18, 70, 72, 74, 82, 127, 5, 6, 36, 69, 70, 72, 76, 80, 84, 100, 127, 36, 72, 80, 100, 127, 9, 35, 67, 69, 72, 80, 99, 100, 101, 104, 105, 113, 127, 18, 35, 67, 70, 72, 80, 99, 100, 102, 106, 112, 114, 127]

def seed19Inputs : List Nat := [0x823753e102606f882779e831efc015a2eef2141b66a7ff5555555aaaaaabab5575b6d7b0007ffc000007f0003ffc000070000007fe000000003fe0000000000000000000000000, 0xda7c11a104bbc0884a0c7de7bdc02aa143362ef727ff539999999ccccccdcd9e59db7adfff80000003f800000000fff38000000000007fe07fc000000000000000000000000000, 0x8c446233d7e2c5889213284aa4eaf3fec453ec253c4a25e1e1e1ef0f0f0ef1e79ee39ce00000001ffc0000000000000007fff3f8003f8003800000000000000000000000000000, 0x90858465182c4adde620aff2e6f3b4e04893b7b9e402b9fe01fe0ff00ff0fe07e0fc1f0000000000000000ffc000fffc07fffc00003ffffc000000000000000000000000000000, 0xe10e0829603170eeebfd3884b4fcb8fb7f1e04c1257201fffe000ffff000fff800ffe00000000000000000ffffff000007ffffffffc00000000000000000000000000000000000, 0xfe17f0b38120408cf3be2ef8bfc0c0ac4012c4013d82c1fffffff0000000ffffff00000fffffffe0000000fffffffffff800000000000000000000000000000000000000000000, 0xffe7ff3dfe3e7cff03c02f00a4ff00f0701b0701b60301ffffffffffffff00000000000fffffffffffffff00000000000000000000000000000000000000000000000000000000]

def seed19Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed19Goal : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000

def seed19Forbidden : List Nat := [0, seed19Mask] ++ seed19Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed20K : Nat := 270

def seed20ScoreWidth : Nat := 10



def seed20Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 64, 65, 65, 65, 66, 66, 66, 66, 66, 66, 68, 68, 80, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 96, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 3, 5, 6, 7, 9, 11, 13, 14, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 99, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 9, 11, 13, 21, 25, 35, 37, 67, 69, 72, 127, 3, 6, 18, 19, 35, 67, 82, 127, 127, 9, 40, 72, 104, 127, 3, 6, 9, 11, 14, 18, 26, 40, 42, 72, 74, 127, 6, 9, 14, 40, 44, 72, 76, 127, 18, 48, 127, 5, 9, 21, 25, 48, 49, 127, 127, 9, 18, 25, 26, 40, 48, 72, 88, 127, 6, 9, 21, 26, 29, 30, 44, 48, 60, 72, 92, 127, 40, 48, 127, 3, 9, 35, 37, 40, 41, 49, 67, 127, 40, 42, 48, 127, 5, 37, 40, 44, 48, 52, 127, 127, 5, 9, 127, 3, 18, 70, 74, 82, 127, 69, 127, 48, 127, 5, 18, 25, 48, 67, 72, 82, 83, 85, 89, 113, 127, 5, 18, 48, 69, 72, 85, 86, 92, 116, 127, 127, 35, 48, 69, 99, 101, 105, 113, 127, 3, 6, 18, 42, 48, 72, 82, 99, 102, 106, 114, 127, 6, 37, 44, 48, 76, 101, 102, 108, 116, 127]

def seed20Inputs : List Nat := [0x88a207f714fcadc3f0e3df205a0bdf20a0363b9bffd555555d55aaaeaaaaaaedb5ec00000ff001ffe007000ff8000003f8000000003ffe0000000000000000000000000, 0x907f3e272146957f302b0b20a615816175ee1ff944e666666e66f33733333376deb400fff000000001f800f0000000000000fff03fc0000000000000000000000000000, 0xfde40a53f4c80dc97ae21135d6018b35604a182a9978787877873c3bc3c3c3b8e73bff000007fe0006007f0000fff00400ff00004000000000000000000000000000000, 0xa528a28348512551b32e657debbb953fbf73f80c2e7f807f87f83fc3fc03fc3f07c00000000000000000000000fffff800ffffff8000000000000000000000000000000, 0xc231530bf37e77653c3281b6f35df9e021821cc8307fff8007ffc003fffc003ff80000000007fffff800000000ffffffff0000000000000000000000000000000000000, 0xfbbe63ef826047413fbef9e70261e1a626035908c07ffffff8000003ffffffc00003fffffff8000000007fffff000000000000000000000000000000000000000000000, 0xfc3f83f3fc7f85f9302301380381813838039e0f007ffffffffffffc000000000003ffffffffffffffff800000000000000000000000000000000000000000000000000]

def seed20Mask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed20Goal : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000

def seed20Forbidden : List Nat := [0, seed20Mask] ++ seed20Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed23K : Nat := 265

def seed23ScoreWidth : Nat := 10



def seed23Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 6, 7, 9, 11, 13, 14, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 73, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 5, 9, 11, 13, 25, 35, 37, 67, 73, 127, 6, 18, 19, 22, 26, 35, 50, 67, 70, 127, 5, 6, 127, 9, 40, 127, 6, 9, 11, 14, 26, 42, 127, 6, 40, 127, 18, 80, 127, 5, 18, 19, 21, 25, 81, 127, 5, 80, 127, 25, 26, 40, 56, 80, 88, 127, 9, 14, 18, 21, 29, 30, 40, 60, 80, 92, 127, 40, 127, 9, 35, 40, 96, 97, 127, 3, 6, 18, 35, 38, 40, 42, 50, 96, 98, 127, 6, 40, 44, 100, 127, 127, 3, 5, 9, 50, 51, 53, 56, 57, 80, 97, 113, 127, 5, 40, 44, 50, 53, 54, 60, 84, 96, 116, 127, 80, 127, 3, 5, 9, 67, 69, 73, 80, 81, 96, 97, 127, 18, 67, 80, 96, 98, 127, 5, 80, 84, 100, 127, 127, 3, 6, 18, 40, 73, 75, 78, 88, 90, 98, 106, 127, 6, 44, 73, 77, 78, 80, 84, 92, 96, 108, 127]

def seed23Inputs : List Nat := [0x206418e316bfa08f5be10273a0cc1bf648d6d49ffd555555555555eeaad5576daf6000000003ff8003ffc0001f800000fe0000000ffc0000000000000000000000000, 0x208fb3e19c09a1440ce3b7e2a134291adfb37ff526666666666666b733799bb6f5a003ffc0fc0000000000ffe00000000007f03ff0000000000000000000000000000, 0x36dc217b0412b7ac117b04a0b5d40b265933e1324f8787878787873bc39e1dc739dffc001f00001ffc001f00001ffc07003801c000000000000000000000000000000, 0x34f6fc610424a234626d1825f79ef9426fde4218f7f807f807f807c3fc1fe1f83e1fffffe000000000000000001ffff8003ffe0000000000000000000000000000000, 0x2704c26d2cc0f7c6fc612120bde7bdfbca124bd087fff80007fff803ffe001ffc00000000000001fffffe000001fffffffc0000000000000000000000000000000000, 0x38170471c700bbf77c7dfe3ee604c9026c1a4c1307fffffff8000003fffffe00000000000000001fffffffffffe000000000000000000000000000000000000000000, 0x3fe7f87df7f8fc078071c038b8070d834812701c07fffffffffffffc00000000001fffffffffffe000000000000000000000000000000000000000000000000000000]

def seed23Mask : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed23Goal : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000000

def seed23Forbidden : List Nat := [0, seed23Mask] ++ seed23Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed24K : Nat := 285

def seed24ScoreWidth : Nat := 10



def seed24Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 4, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 40, 40, 40, 40, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 72, 72, 72, 72, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 3, 5, 6, 7, 9, 11, 13, 14, 15, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 37, 38, 39, 41, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 73, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 6, 9, 11, 13, 19, 21, 127, 127, 127, 9, 24, 25, 127, 3, 6, 9, 11, 14, 26, 127, 5, 6, 9, 13, 14, 28, 127, 24, 49, 56, 81, 88, 96, 127, 3, 5, 9, 19, 21, 24, 25, 48, 49, 51, 53, 80, 81, 83, 85, 127, 3, 6, 19, 22, 24, 26, 48, 50, 80, 82, 127, 5, 6, 21, 22, 24, 28, 48, 52, 80, 84, 127, 127, 3, 5, 9, 35, 37, 41, 48, 49, 96, 97, 127, 35, 38, 50, 98, 127, 37, 38, 52, 100, 127, 24, 41, 48, 56, 96, 104, 127, 3, 6, 9, 14, 24, 43, 46, 48, 58, 96, 104, 106, 127, 5, 6, 9, 14, 24, 45, 46, 48, 60, 96, 104, 108, 127, 127, 3, 5, 9, 67, 69, 73, 80, 81, 96, 97, 127, 67, 70, 82, 98, 127, 69, 70, 84, 100, 127, 24, 73, 80, 88, 96, 104, 127, 3, 6, 9, 14, 24, 75, 78, 80, 90, 96, 104, 106, 127, 5, 6, 9, 14, 24, 77, 78, 80, 92, 96, 104, 108, 127]

def seed24Inputs : List Nat := [0x204b0258518ebfc09604b0a31d7f80b017dd7e54d9bbfeaaaaaaaaaaaabdd5555eeaaef600000000003ff800000000007ff000001fffe0000003f80000000000000000000000000, 0x209596b812fc09c12b2d7025f813815abe8826052f71d5ccccccccccccd6e6666b73375a000fff8007c000001fff000f800000ffe00000007f04000000000000000000000000000, 0x32d704a81f9412e5ae09503f2825d5f02b104a07ba51e9f0f0f0f0f0f0e7787873bc3b9dfff00000f80003ffe00001f00007ff000000003f8008000000000000000000000000000, 0x3af9d7cd708424f5f3af9ae108498610c20192afcf9fceff00ff00ff00f87f807c3fc3e1ffffffff000003fffffffe00000000000000003ffff0000000000000000000000000000, 0x23211909b4a4c0c6423213694981ff9ff3ffe2fe0c1df0ffff0000ffff007fff803ffc000000000000000000000000000007ffffffffffc00000000000000000000000000000000, 0x3c01e00e18c700ff83fc1fbffff19813021e03340811c0ffffffff0000007fffffc0000000000000000003fffffffffffff80000000000000000000000000000000000000000000, 0x3fc1fe0fdffff8f803c01c318e01e01c03e003c40811c0ffffffffffffff800000000001fffffffffffffc000000000000000000000000000000000000000000000000000000000]

def seed24Mask : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed24Goal : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000

def seed24Forbidden : List Nat := [0, seed24Mask] ++ seed24Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed25K : Nat := 277

def seed25ScoreWidth : Nat := 10



def seed25Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 40, 40, 40, 40, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 68, 68, 68, 68, 68, 68, 68, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 96, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 3, 5, 7, 9, 11, 13, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 36, 37, 38, 39, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 7, 9, 11, 13, 21, 25, 127, 3, 18, 19, 127, 36, 127, 18, 127, 72, 127, 18, 127, 127, 3, 13, 15, 18, 30, 36, 46, 72, 78, 127, 18, 48, 49, 50, 80, 81, 82, 112, 127, 3, 5, 9, 18, 19, 21, 25, 48, 49, 57, 80, 81, 85, 127, 5, 18, 21, 22, 36, 48, 80, 84, 127, 9, 18, 25, 26, 48, 56, 72, 80, 127, 13, 18, 21, 25, 29, 30, 36, 56, 60, 72, 84, 92, 127, 36, 127, 3, 5, 9, 35, 36, 41, 48, 49, 127, 3, 127, 36, 41, 44, 56, 72, 104, 127, 3, 9, 18, 36, 43, 44, 46, 48, 58, 72, 104, 106, 127, 72, 127, 3, 5, 9, 67, 69, 72, 80, 81, 127, 3, 127, 36, 69, 72, 76, 84, 100, 127, 3, 5, 18, 36, 71, 72, 76, 78, 80, 86, 100, 102, 127, 127, 3, 36, 41, 49, 69, 72, 81, 99, 101, 105, 112, 113, 127, 3, 18, 36, 72, 99, 102, 106, 112, 114, 127]

def seed25Inputs : List Nat := [0x211deee0270bcfd01385ebe80ec160bdbbc9207d56ffeaaaaaab555555eaaaabadb6fe007ffc000007fc000003fe00000000fffc00000003fe0000000000000000000000000, 0x373840f52b0384d95581c2681142a1500cd275df77c573333333999999733332cedbabff8001fff01800fff80c0000000000000001ffb33c000000000000000000000000000, 0x2248897db5ee8950688b44bebac033b81140376d5c59bc3c3c3de1e1e1bc3c3cf71ccc000001ffffe000000000007ffc01ff000001ffc3c0000000000000000000000000000, 0x24891261c132927f72fd492ddcdb601122403d6dd46e3fc03fc1fe01fe3fc03f07e0f000000000000000fffff0007ffffe00000001fffc00000000000000000000000000000, 0x382e24660942e0518491702edf6fbddffc7fe18f77703fffc001fffe003fffc007ff0000000000000000000000007ffffffffffffe000000000000000000000000000000000, 0x3f4fc7781186805df8df7e38e04c2611c063a60d5c403ffffffe0000003ffffff80001fffffe00000000ffffffff80000000000000000000000000000000000000000000000, 0x3f8ff87fe1fafc7e00e1402f0070381e007c380dd4403fffffffffffffc00000000001ffffffffffffff0000000000000000000000000000000000000000000000000000000]

def seed25Mask : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed25Goal : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000000000

def seed25Forbidden : List Nat := [0, seed25Mask] ++ seed25Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed26K : Nat := 399

def seed26ScoreWidth : Nat := 10



def seed26Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 16, 16, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 32, 32, 32, 32, 32, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 40, 40, 40, 40, 40, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 48, 48, 48, 48, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 64, 64, 64, 64, 64, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 72, 72, 72, 72, 72, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 74, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 80, 80, 80, 80, 80, 80, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 35, 37, 38, 39, 41, 43, 45, 46, 47, 49, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 65, 67, 69, 70, 71, 73, 75, 77, 78, 79, 81, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 6, 7, 9, 11, 13, 17, 19, 21, 24, 25, 33, 35, 37, 41, 49, 65, 67, 69, 73, 81, 96, 97, 127, 3, 5, 6, 7, 24, 96, 127, 3, 5, 6, 7, 24, 96, 127, 6, 9, 17, 24, 25, 96, 127, 3, 6, 9, 14, 24, 26, 30, 127, 5, 6, 9, 14, 24, 28, 30, 127, 6, 9, 17, 24, 25, 96, 127, 3, 6, 17, 22, 24, 26, 30, 127, 5, 6, 17, 22, 24, 28, 30, 127, 6, 24, 33, 65, 96, 97, 127, 3, 6, 33, 38, 96, 98, 102, 127, 5, 6, 33, 38, 96, 100, 102, 127, 9, 24, 33, 56, 96, 104, 120, 127, 3, 6, 9, 14, 24, 26, 33, 38, 43, 46, 56, 58, 96, 98, 104, 106, 127, 5, 6, 9, 14, 24, 28, 33, 38, 45, 46, 56, 60, 96, 100, 104, 108, 127, 17, 24, 33, 56, 96, 112, 120, 127, 3, 6, 17, 22, 24, 26, 33, 38, 51, 54, 56, 58, 96, 98, 112, 114, 127, 5, 6, 17, 22, 24, 28, 33, 38, 53, 54, 56, 60, 96, 100, 112, 116, 127, 6, 24, 33, 65, 96, 97, 127, 3, 6, 65, 70, 96, 98, 102, 127, 5, 6, 65, 70, 96, 100, 102, 127, 9, 24, 65, 88, 96, 104, 120, 127, 3, 6, 9, 14, 24, 26, 65, 70, 75, 78, 88, 90, 96, 98, 104, 106, 127, 5, 6, 9, 14, 24, 28, 65, 70, 77, 78, 88, 92, 96, 100, 104, 108, 127, 17, 24, 65, 88, 96, 112, 120, 127, 3, 6, 17, 22, 24, 26, 65, 70, 83, 86, 88, 90, 96, 98, 112, 114, 127, 5, 6, 17, 22, 24, 28, 65, 70, 85, 86, 88, 92, 96, 100, 112, 116, 127]

def seed26Inputs : List Nat := [0x2028b01458580a2c0516161617640516028b0b014580a2c2c2c2ec8585ad0b0b5a5cbdffdfdd5555555555ef7aabdef557bd800000000000000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000, 0x20515abab8081456aeae032bae0c0a2b575701028ad5d5c06575c1caeb8395d7066cd821096e6666666666b5accd6b599ad680003fffe000000ffff80007f8000007fffc000001ffff0000ff0001fe0003fc000fe0000000000000000000000000000000, 0x35757028a80d5d5c0a2a03af2a0eaeae051501abab81454075e541ebca83d7950674e8421277878787878739cf0e739e1ce77fffc000001ffff0000007f8000ffff8000003fffe000000ff0001fe0003fc0007f000000000000000000000000000000000, 0x218610c30cae79e73cf3ae02021430c2186195cf3ce79e75c04042f0f0b5f9f96a8508846387f807f807f83e0ff07c1fe0f800000000001ffffffffff80000000000000003ffffffffff000000000003fffff80000000000000000000000000000000000, 0x39e79cf3ceb8618430c32a0202173cf39e79d70c30861865404042fcfcb9e1e1728509087c07fff80007ffc00fff801fff007fffffffffe0000000000000000ffffffffffc0000000000000001fffffc0000000000000000000000000000000000000000, 0x3e001f000f0f8007c003c3c3c3a7ff03ff81f9ffc0ffe07e7e7e748080c1010183060e0f8007fffffff800000fffffe00000000000000000000000000000000ffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000, 0x3ff81ffc0fcffe07ff03f3f3f3c7c003e001e1f000f800787878788080c1010183060ff00007fffffffffffff000000000007ffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000]

def seed26Mask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed26Goal : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def seed26Forbidden : List Nat := [0, seed26Mask] ++ seed26Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed27K : Nat := 360

def seed27ScoreWidth : Nat := 10



def seed27Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 16, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 36, 36, 36, 36, 36, 36, 36, 36, 40, 40, 40, 40, 40, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 48, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 68, 68, 68, 68, 68, 68, 68, 68, 72, 72, 72, 72, 72, 72, 72, 72, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 76, 80, 80, 80, 80, 80, 80, 80, 80, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 35, 37, 38, 39, 41, 42, 43, 45, 46, 47, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 66, 67, 69, 70, 71, 73, 74, 75, 77, 78, 79, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 6, 7, 9, 11, 17, 19, 24, 25, 37, 41, 49, 69, 73, 81, 96, 127, 3, 5, 6, 7, 14, 22, 24, 34, 35, 42, 50, 66, 67, 74, 82, 96, 98, 127, 3, 5, 6, 127, 9, 17, 25, 26, 28, 127, 3, 6, 9, 11, 14, 24, 26, 34, 41, 42, 66, 73, 74, 96, 127, 5, 6, 9, 14, 24, 28, 108, 127, 9, 17, 25, 26, 28, 127, 3, 6, 17, 19, 22, 24, 26, 34, 49, 50, 66, 81, 82, 96, 127, 5, 6, 17, 22, 24, 28, 116, 127, 34, 66, 97, 98, 100, 127, 3, 5, 9, 17, 24, 34, 35, 37, 41, 42, 49, 50, 96, 97, 127, 5, 6, 34, 37, 60, 96, 100, 127, 9, 34, 41, 42, 56, 104, 120, 127, 5, 6, 14, 24, 28, 37, 41, 42, 45, 46, 56, 60, 96, 100, 104, 108, 127, 17, 34, 49, 50, 56, 112, 120, 127, 5, 6, 22, 24, 28, 37, 49, 50, 53, 54, 56, 60, 96, 100, 112, 116, 127, 34, 66, 97, 98, 100, 127, 3, 5, 9, 17, 24, 66, 67, 69, 73, 74, 81, 82, 96, 97, 127, 5, 6, 66, 69, 92, 96, 100, 127, 9, 66, 73, 74, 88, 104, 120, 127, 5, 6, 14, 24, 28, 69, 73, 74, 77, 78, 88, 92, 96, 100, 104, 108, 127, 17, 66, 81, 82, 88, 112, 120, 127, 5, 6, 22, 24, 28, 69, 81, 82, 85, 86, 88, 92, 96, 100, 112, 116, 127]

def seed27Inputs : List Nat := [0x80b0c2c058616272e7c901618580b0c2c4e5cf9216486cf0b24367b8442efefbaaaaaaaaaab6db555b6daaaf7b000000000000003fff80000000000000007fff0000000000000000000003ffff00000000000000000000000000, 0x81434540a1a2a1a530d702868a814345434a61ae2ab6dd1155b6e8ddfef600adccccccccccdb6de66db6f335ad000000000000000000000000000000000000000003fff8001fffc00ffffc000000000000000000000000000000, 0xd59bc06acde036e04161ab3780d59bc06dc082c3ae00961d7004b0e800fa240ef0f0f0f0f0e38e7871c73c39ceffff807fffc03fc00001ffff00ffff807f800003fc00001fe00000f00000000000000000000000000000000000, 0x860c6873f73f64218a410c18d0e7ee7ec8431482c20307bf96df3d8889424b30ff00ff00ff03f07f81f83fc1f00000007fffffc0000000000000ffffff800000000000001fffffff000000000000000000000000000000000000, 0xe7ee7ec3063424260c41cfdcfd860c68484c1883f2dbe7d610183e89118293c0ffff0000fffc007ffe003ffe00ffffff80000000000001ffffff00000000000003ffffffe0000000000000000000000000000000000000000000, 0xf800707c00383838007bffe0fefff07f7e7fe0f7031c041818e0208e1e031c00ffffffff0000007fffffc0000000000000000000000001fffffffffffffffffffc00000000000000000000000000000000000000000000000000, 0xfff07f7ff83fbf3ff07df000e0f80070707000fb03e004181f00208fe003e000ffffffffffffff800000000000fffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000]

def seed27Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed27Goal : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def seed27Forbidden : List Nat := [0, seed27Mask] ++ seed27Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed28K : Nat := 341

def seed28ScoreWidth : Nat := 10



def seed28Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 36, 36, 36, 36, 40, 40, 40, 40, 40, 40, 40, 40, 40, 40, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 48, 48, 48, 48, 48, 48, 48, 48, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 52, 64, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 80, 80, 80, 80, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 6, 7, 9, 11, 13, 14, 15, 17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 35, 37, 38, 39, 41, 42, 43, 45, 46, 47, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 7, 9, 11, 13, 17, 19, 21, 25, 37, 41, 49, 67, 69, 81, 127, 3, 5, 6, 7, 14, 34, 35, 42, 127, 3, 127, 9, 17, 24, 25, 26, 72, 73, 74, 127, 3, 6, 9, 11, 14, 24, 26, 30, 34, 41, 42, 67, 72, 74, 96, 106, 127, 6, 9, 13, 14, 24, 28, 72, 76, 127, 9, 127, 3, 6, 19, 22, 24, 26, 34, 50, 127, 21, 22, 28, 30, 127, 34, 96, 97, 104, 112, 127, 3, 5, 6, 9, 17, 34, 35, 37, 41, 42, 49, 50, 56, 67, 96, 97, 127, 37, 96, 100, 127, 9, 34, 41, 42, 56, 72, 96, 104, 112, 127, 5, 6, 14, 24, 28, 37, 38, 41, 42, 45, 46, 56, 60, 72, 76, 100, 108, 127, 34, 49, 50, 56, 96, 112, 116, 127, 17, 21, 22, 24, 28, 34, 37, 50, 53, 54, 56, 60, 100, 112, 116, 127, 72, 96, 97, 98, 100, 127, 3, 5, 9, 17, 24, 41, 67, 69, 70, 72, 73, 74, 76, 81, 96, 97, 127, 3, 34, 67, 70, 72, 74, 96, 98, 100, 127, 69, 70, 72, 76, 96, 100, 116, 127, 81, 96, 112, 127, 6, 17, 22, 24, 26, 34, 50, 67, 70, 74, 81, 83, 86, 88, 90, 112, 114, 127, 5, 6, 21, 22, 28, 70, 72, 76, 81, 85, 86, 92, 100, 112, 116, 127]

def seed28Inputs : List Nat := [0x20c160c8298181749df240a1c14054302ce976e48c17834283697d2fffff55555555557aabaab6db555ef600000000000001ffff0000000000000003fffe00000000000000001ffff00000000000000000000000000, 0x210ab5bf5882abe12834415242c0a8d0544a9961d7be84eb76f21ff6412b9999999999accdccdb6de66b5a0001ffff8007fe000000000000000000000000003fe003fffe003fe000000000000000000000000000000, 0x37afe11058ebc22230586dab607acef006c021a0fc2ad6c024a0147a8a4de1e1e1e1e1cf0ef0e38e78739dfffe000007f800000003fffc03ffff003c000007c007fc000000c00000000000000000000000000000000, 0x22342621888c8c23c690c60c446ff395ec44c228e4c3ff6dbf3fb6421471fe01fe01fe0ff0ff03f07f83e000000000000000000000000003ffffffc00000000007ffffffff000000000000000000000000000000000, 0x3bc73fc5edc08024031077cff743031884470430fef298403823d4032781fffe0001fff000fffc007ffc01fffffffff80000000003fffffc00000000000007fff800000000000000000000000000000000000000000, 0x3c0038060ef0f0b8041f7ff07ff3fc1ef7f7f83f87028071c02017823801fffffffe000000ffffff80000000000000000000000003fffffffffffffffffff8000000000000000000000000000000000000000000000, 0x3ff83ff80fffff3ff81ff800787c001f0778003e8402e07e003c1403c001ffffffffffffff000000000001fffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000]

def seed28Mask : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed28Goal : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def seed28Forbidden : List Nat := [0, seed28Mask] ++ seed28Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed29K : Nat := 347

def seed29ScoreWidth : Nat := 10



def seed29Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 40, 40, 40, 40, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 49, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 56, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 3, 5, 6, 7, 9, 11, 13, 14, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 36, 37, 38, 39, 41, 43, 44, 45, 46, 47, 50, 51, 52, 53, 54, 55, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 6, 9, 11, 13, 25, 41, 73, 127, 3, 5, 6, 18, 19, 22, 26, 50, 82, 127, 3, 5, 6, 36, 37, 38, 44, 52, 100, 127, 9, 72, 73, 127, 3, 6, 9, 11, 14, 18, 25, 26, 72, 74, 127, 5, 6, 9, 13, 14, 36, 41, 44, 72, 76, 127, 18, 80, 82, 127, 3, 5, 9, 18, 19, 21, 25, 26, 80, 81, 127, 5, 6, 18, 21, 22, 36, 50, 52, 80, 84, 127, 25, 26, 92, 127, 9, 14, 18, 21, 25, 26, 29, 30, 36, 44, 52, 60, 76, 84, 88, 92, 127, 36, 96, 100, 127, 3, 5, 9, 35, 36, 37, 41, 44, 96, 97, 127, 3, 6, 18, 35, 36, 38, 50, 52, 96, 98, 127, 41, 44, 106, 127, 9, 14, 18, 26, 35, 36, 41, 43, 44, 46, 50, 58, 74, 98, 104, 106, 127, 50, 52, 113, 127, 9, 18, 21, 25, 35, 36, 41, 50, 51, 52, 53, 57, 81, 97, 112, 113, 127, 9, 18, 25, 26, 36, 41, 44, 50, 52, 57, 58, 60, 72, 80, 92, 96, 106, 113, 120, 127, 72, 73, 74, 76, 80, 81, 82, 84, 88, 96, 97, 98, 100, 104, 112, 127, 3, 5, 9, 67, 69, 72, 73, 80, 81, 96, 97, 127, 3, 6, 18, 67, 70, 72, 74, 80, 82, 96, 98, 127, 5, 6, 36, 69, 70, 72, 76, 80, 84, 96, 100, 127]

def seed29Inputs : List Nat := [0x202602757e108a808977abb900d198139be200b330273bc44d89bb09c27fdd55555555555555d5aabadb6bd8000007ff8000000007fffc000000003ff8000000007ff0000000000003ff00000000000000000000000000, 0x204b57e02621124122a03253be9eccdf0262014d515a4cec12d77112ffb0ae66666666666666e6cf2cedbd68007ff800000000000000003fffe1ffc000000000000000001ffc000ffc0000000000000000000000000000, 0x357e04a04a4222125420c4950322a9652cb77f959aee1146bb8251ff44d1378787878787878778f3cf71ce77ff800000000000000000000000000000007fffc3ff8000ffe0003ff0000000000000000000000000000000, 0x2182182192843f579b610931dbcbf8013123b5e7f0026247dcfb9f20481fc7f807f807f807f87f03f07e0f800000000000007ffff800003ffffe0000007ffffc000000ffffffc000000000000000000000000000000000, 0x260261260307c39be3bbf1df0c0c89890023d9f9ff73fc7c009c11407f1207fff80007fff8007ffc007ff0000000000000007fffffffffc000000000007fffffffffff0000000000000000000000000000000000000000, 0x3813803803f803e3fc3dfe1feff0fff1fe3e1e0113820044e08011fc501407fffffff80000007fffff8000000000000000007fffffffffffffffffffff8000000000000000000000000000000000000000000000000000, 0x3fe3fe3fe3fffffc003e0019f000ce01c03be0019c03807700e01d80601807ffffffffffffff800000000007ffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000]

def seed29Mask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed29Goal : Nat := 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def seed29Forbidden : List Nat := [0, seed29Mask] ++ seed29Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed30K : Nat := 344

def seed30ScoreWidth : Nat := 10



def seed30Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 64, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 68, 68, 68, 68, 68, 68, 68, 68, 68, 68, 80, 80, 80, 80, 80, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 81, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 84, 3, 5, 6, 7, 9, 11, 13, 14, 15, 18, 19, 21, 22, 23, 25, 26, 27, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 3, 5, 7, 9, 11, 13, 21, 25, 37, 69, 127, 3, 6, 7, 14, 18, 26, 35, 38, 50, 82, 127, 3, 5, 6, 127, 9, 25, 40, 41, 72, 73, 74, 76, 88, 104, 127, 3, 5, 6, 9, 11, 14, 18, 25, 26, 35, 40, 42, 67, 72, 74, 98, 127, 6, 9, 13, 14, 40, 44, 72, 76, 127, 18, 48, 50, 127, 5, 6, 9, 18, 19, 21, 25, 48, 49, 127, 18, 21, 48, 52, 127, 9, 18, 25, 26, 48, 56, 72, 88, 96, 127, 5, 14, 21, 22, 25, 26, 29, 30, 40, 44, 52, 60, 72, 76, 88, 92, 127, 40, 42, 48, 49, 50, 52, 96, 97, 98, 104, 127, 3, 5, 9, 25, 35, 37, 38, 40, 41, 42, 44, 48, 49, 72, 96, 97, 127, 3, 6, 18, 35, 37, 38, 40, 42, 48, 50, 52, 74, 82, 96, 98, 102, 127, 5, 6, 37, 38, 40, 44, 48, 52, 72, 96, 100, 127, 40, 72, 96, 127, 3, 5, 9, 67, 69, 73, 96, 97, 127, 3, 5, 6, 18, 67, 70, 72, 74, 82, 96, 98, 127, 5, 6, 69, 70, 72, 76, 96, 100, 102, 127, 18, 48, 82, 88, 127, 3, 5, 21, 25, 49, 67, 69, 72, 82, 83, 85, 88, 89, 97, 112, 113, 127, 5, 6, 21, 52, 69, 72, 76, 82, 85, 86, 88, 92, 96, 102, 116, 127]

def seed30Inputs : List Nat := [0x8115db3fc205813dfc402c0067227f22200ab02cb7588344a6e15dc45fff55555555556aabaaaaaabb6d7b0000ffff8000000ff800000003fffe00000000003ff00000000000000ffe00000000000000000000000000, 0xa2828190d70adbd84c40576abe04a344a015505461ad84f6dd6206fff82b9999999999bccdccccccddb7ad000000000000fff0000007fffc000000000000000000007fffc0007ff00000000000000000000000000000, 0xeb5f822343af826894657e10ca08c50835d9f006a238d6c009a40748eecde1e1e1e1e1cf0ef0f0f0ee39ceffff000003ff0000007ff800000000003fffe007c000ff8000000780000000000000000000000000000000, 0x8c608c4462308c0925c98423024f1980ff7e576c2448ff5b6e3ffc428971fe01fe01fe0ff0ff00ff0fc1f0000000000000000000000000000000003ffffff80000fffffffff800000000000000000000000000000000, 0xcf8cef8e7e0090880446045c1230110f399f95f7ff8f8040702814730981fffe0001fff000ffff000ffe00fffffffffc00000000000000000000003fffffffffff000000000000000000000000000000000000000000, 0xf008f0084bc0e00e06f7e79fe3bfe1ffe1e01987380e98638030645c0a01fffffffe000000fffffff000000000000000000000007fffffffffffffc00000000000000000000000000000000000000000000000000000, 0xfff0fff073fcff0fc77807e003c001f03e001e042008e07c003f84600c01ffffffffffffff000000000000ffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000]

def seed30Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed30Goal : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def seed30Forbidden : List Nat := [0, seed30Mask] ++ seed30Inputs

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed0Fn : BFn 6 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)
def seed0Pack (x : Fin 6 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed0Pack_spec (x : Fin 6 → Bool) :
    seed0Pack x < 64 ∧ pt 6 (seed0Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed0Rows_cover : ∀ x : Fin 6 → Bool, ∃ v ∈ seed0Rows, pt 6 v = x := by
  have hmem : ∀ v : Fin 64, v.val ∈ seed0Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed0Pack_spec x
  exact ⟨seed0Pack x,hmem ⟨_,hb⟩,he⟩

def seed0Witnesses : List (Nat × Nat) := [(56, 151), (49, 151), (49, 152), (49, 155), (60, 164), (60, 176)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed0Essential : ∀ a ∈ seed0Inputs, ∃ i j : Nat,
    seed0Mask.testBit i = seed0Mask.testBit j ∧
    seed0Goal.testBit i ≠ seed0Goal.testBit j ∧
    ∀ b ∈ seed0Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed0Inputs, ∃ p : Fin 6,
      seed0Mask.testBit (seed0Witnesses.getD p.val (0,0)).1 =
        seed0Mask.testBit (seed0Witnesses.getD p.val (0,0)).2 ∧
      seed0Goal.testBit (seed0Witnesses.getD p.val (0,0)).1 ≠
        seed0Goal.testBit (seed0Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed0Inputs, b ≠ a →
        b.testBit (seed0Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed0Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed0Witnesses.getD p.val (0,0)).1,(seed0Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed0Lower_of_noRun
    (hno : ∀ t < 10, ¬ RNatRun seed0Forbidden seed0Mask seed0Goal t seed0Inputs) :
    ∀ s, HasCircuitSize 6 seed0Fn s → 10 ≤ s := by
  apply lower_from_rows seed0Fn seed0Rows seed0Inputs seed0Forbidden seed0Mask seed0Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed0Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed0Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed8Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def seed8Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Pack_spec (x : Fin 7 → Bool) :
    seed8Pack x < 128 ∧ pt 7 (seed8Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed8Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed8Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed8Pack_spec x
  exact ⟨seed8Pack x,hmem ⟨_,hb⟩,he⟩

def seed8Witnesses : List (Nat × Nat) := [(100, 218), (99, 218), (99, 219), (100, 221), (101, 227), (106, 240), (116, 269)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Essential : ∀ a ∈ seed8Inputs, ∃ i j : Nat,
    seed8Mask.testBit i = seed8Mask.testBit j ∧
    seed8Goal.testBit i ≠ seed8Goal.testBit j ∧
    ∀ b ∈ seed8Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed8Inputs, ∃ p : Fin 7,
      seed8Mask.testBit (seed8Witnesses.getD p.val (0,0)).1 =
        seed8Mask.testBit (seed8Witnesses.getD p.val (0,0)).2 ∧
      seed8Goal.testBit (seed8Witnesses.getD p.val (0,0)).1 ≠
        seed8Goal.testBit (seed8Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed8Inputs, b ≠ a →
        b.testBit (seed8Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed8Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed8Witnesses.getD p.val (0,0)).1,(seed8Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Lower_of_noRun
    (hno : ∀ t < 10, ¬ RNatRun seed8Forbidden seed8Mask seed8Goal t seed8Inputs) :
    ∀ s, HasCircuitSize 7 seed8Fn s → 10 ≤ s := by
  apply lower_from_rows seed8Fn seed8Rows seed8Inputs seed8Forbidden seed8Mask seed8Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed8Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed8Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed13Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)
def seed13Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed13Pack_spec (x : Fin 7 → Bool) :
    seed13Pack x < 128 ∧ pt 7 (seed13Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed13Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed13Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed13Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed13Pack_spec x
  exact ⟨seed13Pack x,hmem ⟨_,hb⟩,he⟩

def seed13Witnesses : List (Nat × Nat) := [(118, 276), (100, 276), (100, 277), (100, 280), (100, 285), (118, 298), (123, 324)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed13Essential : ∀ a ∈ seed13Inputs, ∃ i j : Nat,
    seed13Mask.testBit i = seed13Mask.testBit j ∧
    seed13Goal.testBit i ≠ seed13Goal.testBit j ∧
    ∀ b ∈ seed13Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed13Inputs, ∃ p : Fin 7,
      seed13Mask.testBit (seed13Witnesses.getD p.val (0,0)).1 =
        seed13Mask.testBit (seed13Witnesses.getD p.val (0,0)).2 ∧
      seed13Goal.testBit (seed13Witnesses.getD p.val (0,0)).1 ≠
        seed13Goal.testBit (seed13Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed13Inputs, b ≠ a →
        b.testBit (seed13Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed13Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed13Witnesses.getD p.val (0,0)).1,(seed13Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed13Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed13Forbidden seed13Mask seed13Goal t seed13Inputs) :
    ∀ s, HasCircuitSize 7 seed13Fn s → 11 ≤ s := by
  apply lower_from_rows seed13Fn seed13Rows seed13Inputs seed13Forbidden seed13Mask seed13Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed13Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed13Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed18Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def seed18Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed18Pack_spec (x : Fin 7 → Bool) :
    seed18Pack x < 128 ∧ pt 7 (seed18Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed18Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed18Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed18Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed18Pack_spec x
  exact ⟨seed18Pack x,hmem ⟨_,hb⟩,he⟩

def seed18Witnesses : List (Nat × Nat) := [(118, 276), (101, 276), (101, 277), (101, 280), (101, 285), (124, 299), (129, 329)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed18Essential : ∀ a ∈ seed18Inputs, ∃ i j : Nat,
    seed18Mask.testBit i = seed18Mask.testBit j ∧
    seed18Goal.testBit i ≠ seed18Goal.testBit j ∧
    ∀ b ∈ seed18Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed18Inputs, ∃ p : Fin 7,
      seed18Mask.testBit (seed18Witnesses.getD p.val (0,0)).1 =
        seed18Mask.testBit (seed18Witnesses.getD p.val (0,0)).2 ∧
      seed18Goal.testBit (seed18Witnesses.getD p.val (0,0)).1 ≠
        seed18Goal.testBit (seed18Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed18Inputs, b ≠ a →
        b.testBit (seed18Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed18Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed18Witnesses.getD p.val (0,0)).1,(seed18Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed18Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed18Forbidden seed18Mask seed18Goal t seed18Inputs) :
    ∀ s, HasCircuitSize 7 seed18Fn s → 11 ≤ s := by
  apply lower_from_rows seed18Fn seed18Rows seed18Inputs seed18Forbidden seed18Mask seed18Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed18Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed18Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed19Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)
def seed19Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed19Pack_spec (x : Fin 7 → Bool) :
    seed19Pack x < 128 ∧ pt 7 (seed19Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed19Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed19Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed19Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed19Pack_spec x
  exact ⟨seed19Pack x,hmem ⟨_,hb⟩,he⟩

def seed19Witnesses : List (Nat × Nat) := [(110, 284), (101, 284), (101, 285), (101, 288), (110, 293), (119, 305), (122, 332)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed19Essential : ∀ a ∈ seed19Inputs, ∃ i j : Nat,
    seed19Mask.testBit i = seed19Mask.testBit j ∧
    seed19Goal.testBit i ≠ seed19Goal.testBit j ∧
    ∀ b ∈ seed19Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed19Inputs, ∃ p : Fin 7,
      seed19Mask.testBit (seed19Witnesses.getD p.val (0,0)).1 =
        seed19Mask.testBit (seed19Witnesses.getD p.val (0,0)).2 ∧
      seed19Goal.testBit (seed19Witnesses.getD p.val (0,0)).1 ≠
        seed19Goal.testBit (seed19Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed19Inputs, b ≠ a →
        b.testBit (seed19Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed19Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed19Witnesses.getD p.val (0,0)).1,(seed19Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed19Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed19Forbidden seed19Mask seed19Goal t seed19Inputs) :
    ∀ s, HasCircuitSize 7 seed19Fn s → 11 ≤ s := by
  apply lower_from_rows seed19Fn seed19Rows seed19Inputs seed19Forbidden seed19Mask seed19Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed19Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed19Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed20Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)
def seed20Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed20Pack_spec (x : Fin 7 → Bool) :
    seed20Pack x < 128 ∧ pt 7 (seed20Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed20Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed20Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed20Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed20Pack_spec x
  exact ⟨seed20Pack x,hmem ⟨_,hb⟩,he⟩

def seed20Witnesses : List (Nat × Nat) := [(114, 270), (101, 270), (101, 271), (101, 274), (114, 279), (123, 294), (123, 322)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed20Essential : ∀ a ∈ seed20Inputs, ∃ i j : Nat,
    seed20Mask.testBit i = seed20Mask.testBit j ∧
    seed20Goal.testBit i ≠ seed20Goal.testBit j ∧
    ∀ b ∈ seed20Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed20Inputs, ∃ p : Fin 7,
      seed20Mask.testBit (seed20Witnesses.getD p.val (0,0)).1 =
        seed20Mask.testBit (seed20Witnesses.getD p.val (0,0)).2 ∧
      seed20Goal.testBit (seed20Witnesses.getD p.val (0,0)).1 ≠
        seed20Goal.testBit (seed20Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed20Inputs, b ≠ a →
        b.testBit (seed20Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed20Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed20Witnesses.getD p.val (0,0)).1,(seed20Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed20Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed20Forbidden seed20Mask seed20Goal t seed20Inputs) :
    ∀ s, HasCircuitSize 7 seed20Fn s → 11 ≤ s := by
  apply lower_from_rows seed20Fn seed20Rows seed20Inputs seed20Forbidden seed20Mask seed20Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed20Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed20Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed23Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def seed23Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed23Pack_spec (x : Fin 7 → Bool) :
    seed23Pack x < 128 ∧ pt 7 (seed23Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed23Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed23Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed23Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed23Pack_spec x
  exact ⟨seed23Pack x,hmem ⟨_,hb⟩,he⟩

def seed23Witnesses : List (Nat × Nat) := [(112, 265), (102, 265), (102, 266), (102, 269), (112, 274), (125, 289), (138, 319)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed23Essential : ∀ a ∈ seed23Inputs, ∃ i j : Nat,
    seed23Mask.testBit i = seed23Mask.testBit j ∧
    seed23Goal.testBit i ≠ seed23Goal.testBit j ∧
    ∀ b ∈ seed23Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed23Inputs, ∃ p : Fin 7,
      seed23Mask.testBit (seed23Witnesses.getD p.val (0,0)).1 =
        seed23Mask.testBit (seed23Witnesses.getD p.val (0,0)).2 ∧
      seed23Goal.testBit (seed23Witnesses.getD p.val (0,0)).1 ≠
        seed23Goal.testBit (seed23Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed23Inputs, b ≠ a →
        b.testBit (seed23Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed23Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed23Witnesses.getD p.val (0,0)).1,(seed23Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed23Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed23Forbidden seed23Mask seed23Goal t seed23Inputs) :
    ∀ s, HasCircuitSize 7 seed23Fn s → 11 ≤ s := by
  apply lower_from_rows seed23Fn seed23Rows seed23Inputs seed23Forbidden seed23Mask seed23Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed23Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed23Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed24Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def seed24Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed24Pack_spec (x : Fin 7 → Bool) :
    seed24Pack x < 128 ∧ pt 7 (seed24Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed24Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed24Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed24Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed24Pack_spec x
  exact ⟨seed24Pack x,hmem ⟨_,hb⟩,he⟩

def seed24Witnesses : List (Nat × Nat) := [(110, 285), (103, 285), (103, 286), (103, 289), (112, 298), (130, 315), (130, 340)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed24Essential : ∀ a ∈ seed24Inputs, ∃ i j : Nat,
    seed24Mask.testBit i = seed24Mask.testBit j ∧
    seed24Goal.testBit i ≠ seed24Goal.testBit j ∧
    ∀ b ∈ seed24Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed24Inputs, ∃ p : Fin 7,
      seed24Mask.testBit (seed24Witnesses.getD p.val (0,0)).1 =
        seed24Mask.testBit (seed24Witnesses.getD p.val (0,0)).2 ∧
      seed24Goal.testBit (seed24Witnesses.getD p.val (0,0)).1 ≠
        seed24Goal.testBit (seed24Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed24Inputs, b ≠ a →
        b.testBit (seed24Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed24Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed24Witnesses.getD p.val (0,0)).1,(seed24Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed24Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed24Forbidden seed24Mask seed24Goal t seed24Inputs) :
    ∀ s, HasCircuitSize 7 seed24Fn s → 11 ≤ s := by
  apply lower_from_rows seed24Fn seed24Rows seed24Inputs seed24Forbidden seed24Mask seed24Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed24Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed24Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed25Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)
def seed25Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed25Pack_spec (x : Fin 7 → Bool) :
    seed25Pack x < 128 ∧ pt 7 (seed25Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed25Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed25Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed25Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed25Pack_spec x
  exact ⟨seed25Pack x,hmem ⟨_,hb⟩,he⟩

def seed25Witnesses : List (Nat × Nat) := [(110, 277), (101, 277), (101, 278), (101, 280), (110, 284), (114, 296), (118, 325)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed25Essential : ∀ a ∈ seed25Inputs, ∃ i j : Nat,
    seed25Mask.testBit i = seed25Mask.testBit j ∧
    seed25Goal.testBit i ≠ seed25Goal.testBit j ∧
    ∀ b ∈ seed25Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed25Inputs, ∃ p : Fin 7,
      seed25Mask.testBit (seed25Witnesses.getD p.val (0,0)).1 =
        seed25Mask.testBit (seed25Witnesses.getD p.val (0,0)).2 ∧
      seed25Goal.testBit (seed25Witnesses.getD p.val (0,0)).1 ≠
        seed25Goal.testBit (seed25Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed25Inputs, b ≠ a →
        b.testBit (seed25Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed25Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed25Witnesses.getD p.val (0,0)).1,(seed25Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed25Lower_of_noRun
    (hno : ∀ t < 11, ¬ RNatRun seed25Forbidden seed25Mask seed25Goal t seed25Inputs) :
    ∀ s, HasCircuitSize 7 seed25Fn s → 11 ≤ s := by
  apply lower_from_rows seed25Fn seed25Rows seed25Inputs seed25Forbidden seed25Mask seed25Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed25Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed25Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed26Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)
def seed26Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed26Pack_spec (x : Fin 7 → Bool) :
    seed26Pack x < 128 ∧ pt 7 (seed26Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed26Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed26Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed26Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed26Pack_spec x
  exact ⟨seed26Pack x,hmem ⟨_,hb⟩,he⟩

def seed26Witnesses : List (Nat × Nat) := [(125, 399), (100, 399), (100, 400), (100, 403), (100, 408), (100, 421), (100, 444)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed26Essential : ∀ a ∈ seed26Inputs, ∃ i j : Nat,
    seed26Mask.testBit i = seed26Mask.testBit j ∧
    seed26Goal.testBit i ≠ seed26Goal.testBit j ∧
    ∀ b ∈ seed26Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed26Inputs, ∃ p : Fin 7,
      seed26Mask.testBit (seed26Witnesses.getD p.val (0,0)).1 =
        seed26Mask.testBit (seed26Witnesses.getD p.val (0,0)).2 ∧
      seed26Goal.testBit (seed26Witnesses.getD p.val (0,0)).1 ≠
        seed26Goal.testBit (seed26Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed26Inputs, b ≠ a →
        b.testBit (seed26Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed26Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed26Witnesses.getD p.val (0,0)).1,(seed26Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed26Lower_of_noRun
    (hno : ∀ t < 12, ¬ RNatRun seed26Forbidden seed26Mask seed26Goal t seed26Inputs) :
    ∀ s, HasCircuitSize 7 seed26Fn s → 12 ≤ s := by
  apply lower_from_rows seed26Fn seed26Rows seed26Inputs seed26Forbidden seed26Mask seed26Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed26Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed26Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed27Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)
def seed27Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed27Pack_spec (x : Fin 7 → Bool) :
    seed27Pack x < 128 ∧ pt 7 (seed27Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed27Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed27Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed27Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed27Pack_spec x
  exact ⟨seed27Pack x,hmem ⟨_,hb⟩,he⟩

def seed27Witnesses : List (Nat × Nat) := [(122, 360), (104, 360), (104, 361), (104, 364), (104, 369), (122, 382), (122, 407)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed27Essential : ∀ a ∈ seed27Inputs, ∃ i j : Nat,
    seed27Mask.testBit i = seed27Mask.testBit j ∧
    seed27Goal.testBit i ≠ seed27Goal.testBit j ∧
    ∀ b ∈ seed27Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed27Inputs, ∃ p : Fin 7,
      seed27Mask.testBit (seed27Witnesses.getD p.val (0,0)).1 =
        seed27Mask.testBit (seed27Witnesses.getD p.val (0,0)).2 ∧
      seed27Goal.testBit (seed27Witnesses.getD p.val (0,0)).1 ≠
        seed27Goal.testBit (seed27Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed27Inputs, b ≠ a →
        b.testBit (seed27Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed27Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed27Witnesses.getD p.val (0,0)).1,(seed27Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed27Lower_of_noRun
    (hno : ∀ t < 12, ¬ RNatRun seed27Forbidden seed27Mask seed27Goal t seed27Inputs) :
    ∀ s, HasCircuitSize 7 seed27Fn s → 12 ≤ s := by
  apply lower_from_rows seed27Fn seed27Rows seed27Inputs seed27Forbidden seed27Mask seed27Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed27Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed27Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed28Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)
def seed28Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed28Pack_spec (x : Fin 7 → Bool) :
    seed28Pack x < 128 ∧ pt 7 (seed28Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed28Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed28Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed28Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed28Pack_spec x
  exact ⟨seed28Pack x,hmem ⟨_,hb⟩,he⟩

def seed28Witnesses : List (Nat × Nat) := [(121, 341), (104, 341), (104, 342), (104, 345), (104, 350), (121, 363), (132, 392)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed28Essential : ∀ a ∈ seed28Inputs, ∃ i j : Nat,
    seed28Mask.testBit i = seed28Mask.testBit j ∧
    seed28Goal.testBit i ≠ seed28Goal.testBit j ∧
    ∀ b ∈ seed28Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed28Inputs, ∃ p : Fin 7,
      seed28Mask.testBit (seed28Witnesses.getD p.val (0,0)).1 =
        seed28Mask.testBit (seed28Witnesses.getD p.val (0,0)).2 ∧
      seed28Goal.testBit (seed28Witnesses.getD p.val (0,0)).1 ≠
        seed28Goal.testBit (seed28Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed28Inputs, b ≠ a →
        b.testBit (seed28Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed28Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed28Witnesses.getD p.val (0,0)).1,(seed28Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed28Lower_of_noRun
    (hno : ∀ t < 12, ¬ RNatRun seed28Forbidden seed28Mask seed28Goal t seed28Inputs) :
    ∀ s, HasCircuitSize 7 seed28Fn s → 12 ≤ s := by
  apply lower_from_rows seed28Fn seed28Rows seed28Inputs seed28Forbidden seed28Mask seed28Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed28Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed28Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed29Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
def seed29Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed29Pack_spec (x : Fin 7 → Bool) :
    seed29Pack x < 128 ∧ pt 7 (seed29Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed29Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed29Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed29Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed29Pack_spec x
  exact ⟨seed29Pack x,hmem ⟨_,hb⟩,he⟩

def seed29Witnesses : List (Nat × Nat) := [(114, 347), (104, 347), (104, 348), (104, 351), (114, 356), (124, 368), (134, 395)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed29Essential : ∀ a ∈ seed29Inputs, ∃ i j : Nat,
    seed29Mask.testBit i = seed29Mask.testBit j ∧
    seed29Goal.testBit i ≠ seed29Goal.testBit j ∧
    ∀ b ∈ seed29Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed29Inputs, ∃ p : Fin 7,
      seed29Mask.testBit (seed29Witnesses.getD p.val (0,0)).1 =
        seed29Mask.testBit (seed29Witnesses.getD p.val (0,0)).2 ∧
      seed29Goal.testBit (seed29Witnesses.getD p.val (0,0)).1 ≠
        seed29Goal.testBit (seed29Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed29Inputs, b ≠ a →
        b.testBit (seed29Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed29Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed29Witnesses.getD p.val (0,0)).1,(seed29Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed29Lower_of_noRun
    (hno : ∀ t < 12, ¬ RNatRun seed29Forbidden seed29Mask seed29Goal t seed29Inputs) :
    ∀ s, HasCircuitSize 7 seed29Fn s → 12 ≤ s := by
  apply lower_from_rows seed29Fn seed29Rows seed29Inputs seed29Forbidden seed29Mask seed29Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed29Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed29Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed30Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)
def seed30Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed30Pack_spec (x : Fin 7 → Bool) :
    seed30Pack x < 128 ∧ pt 7 (seed30Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed30Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed30Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed30Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed30Pack_spec x
  exact ⟨seed30Pack x,hmem ⟨_,hb⟩,he⟩

def seed30Witnesses : List (Nat × Nat) := [(116, 344), (105, 344), (105, 345), (105, 348), (116, 353), (131, 368), (131, 396)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed30Essential : ∀ a ∈ seed30Inputs, ∃ i j : Nat,
    seed30Mask.testBit i = seed30Mask.testBit j ∧
    seed30Goal.testBit i ≠ seed30Goal.testBit j ∧
    ∀ b ∈ seed30Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed30Inputs, ∃ p : Fin 7,
      seed30Mask.testBit (seed30Witnesses.getD p.val (0,0)).1 =
        seed30Mask.testBit (seed30Witnesses.getD p.val (0,0)).2 ∧
      seed30Goal.testBit (seed30Witnesses.getD p.val (0,0)).1 ≠
        seed30Goal.testBit (seed30Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed30Inputs, b ≠ a →
        b.testBit (seed30Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed30Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed30Witnesses.getD p.val (0,0)).1,(seed30Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed30Lower_of_noRun
    (hno : ∀ t < 12, ¬ RNatRun seed30Forbidden seed30Mask seed30Goal t seed30Inputs) :
    ∀ s, HasCircuitSize 7 seed30Fn s → 12 ≤ s := by
  apply lower_from_rows seed30Fn seed30Rows seed30Inputs seed30Forbidden seed30Mask seed30Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed30Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed30Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite
