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

def seed0NegativeRows : List Nat := [0, 1, 2, 4, 8, 10, 12, 16, 17, 18, 20, 32, 33, 34, 36]

def seed0PositiveRows : List Nat := [3, 5, 6, 7, 9, 11, 13, 14, 15, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

def seed0Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 36, 36, 36, 36, 36, 3, 5, 6, 7, 9, 11, 13, 14, 15, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 3, 5, 6, 9, 11, 13, 63, 3, 63, 5, 63, 9, 24, 25, 40, 41, 48, 63, 3, 6, 9, 11, 14, 24, 26, 40, 42, 63, 5, 6, 9, 13, 14, 24, 28, 40, 44, 63, 24, 63, 3, 5, 9, 19, 21, 24, 25, 48, 49, 63, 3, 6, 19, 22, 24, 26, 48, 50, 54, 63, 5, 6, 21, 22, 24, 28, 48, 52, 54, 63, 40, 63, 3, 5, 9, 35, 37, 40, 41, 48, 49, 63, 3, 6, 35, 38, 40, 42, 48, 50, 54, 63, 5, 6, 37, 38, 40, 44, 48, 52, 54, 63]

def seed0Inputs : List Nat := [0x2058175fa058175fa0d836affbaaaaaabaabbd800007fe000007fe00000000fe000000000000, 0x30aebe09b0aebe09a12d6e05d5ccccccdccdd6801ff800001ff800001ff80300000000000000, 0x3afc2a12bafc2a12b5b84a0766f0f0f0ef0ee77fe000007fe000007fe0000c00000000000000, 0x2308c264e308c264ffcff2fd78ff00ff0ff0f800000000000000007ffffff000000000000000, 0x3c0f0380bfcff3f8e609833540ffff000fff00000000007fffffff8000000000000000000000, 0x3fcff3f8fc0f0380b80e03c540fffffff000007fffffff800000000000000000000000000000]

def seed0Mask : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed0Goal : Nat := 0x3fffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000

def seed0Forbidden : List Nat := [0, seed0Mask] ++ seed0Inputs

def seed0Pool : List Nat := [100278865460616347, 136307696851901595, 100289871314313371, 136318702705598619, 100289826207720600, 136318623226684568, 100278841828861079, 136307638847825047, 136307651763137712, 100278889103912100, 136318646879415472, 100289884220189860, 100278841826762903, 136307638845726871, 100289826205621400, 136318623224585368, 100278889103933604, 136307651763146928, 100289884220211364, 136318646879424688, 111562064510738583, 147626080261529751, 122821052841745560, 158885068592536728, 111537898909778084, 147566661568991408, 122807903831900324, 158836666491113648, 122796908715622564, 158825671374835888, 111548894026055844, 147577656685269168, 147590895889440919, 136342857577554071, 158849884220447896, 136353841956412568, 122832037219556505, 158896052970347673, 147601811572953272, 158871816495075512, 86768090188242073, 86768055828503705, 136331828125667512, 136331817388249272, 100271168881319067, 136300000272604315, 100271179620835483, 136300011012120731, 75489276300787867, 75489310673121435, 86748286106633371, 86748320478966939, 75489252666925207, 86748240997932184, 100271192522539172, 136299955181752496]

def seed0Words : Array Nat := #[0x300c0700300c0701f07c0abf0000000000ff80000000000000007fffffffffffffffffffff,
0x300c0700f03c1f01f07c0abf000000000fff800000007fffffffffffffffffffffffffffff,
0x1004070350d47f46d1b43abb00000003f339800000007fffffffffffffffffffffffffffff,
0x300c0303f0fc3b4731cc1287000000055f47800000007fffffffffffffffffffffffffffff,
0x30080603f0e87647f1d83a2e00000007766b000000007fffffffffffffffffffffffffffff,
0x1004070050145f00d0342abb0000000aabbd80000000000007fe00000000fe000000000000,
0x200c0100a0bc0901216c00950000000ccdd680000000001ff800001ff80300000000000000,
0x40300c06447c1f038380000000ff0f800000000000000007ffffff000000000000000,
0x3c0f07846018030000000000fff00000000007fffffff8000000000000000000000,
0x403c0f07c47c1f038380000000ffff8000000007ffffffffffffff000000000000000,
0x300c0703f0fc7f47f1fc3abf0000000fffff800000007fffffffffffffffffffffffffffff,
0xf03c1b00f03c1b00300c0287000000f00f07ffffffffffffffff8000000fffffffffffffff,
0xf03c1f03f0fc7f47f1fc3abf000000ffffffffffffffffffffffffffffffffffffffffffff,
0x35040764010000618d210ca2a0000332000297fe007ff800000007fe007fcffffffffffffff,
0x3a0e8204020080019264840040000554000427ffff801800000007fffffff01ffffffffffff,
0x300c0644300c0645fc7f0f8380000ff0ff0f800000000000000007ffffff000000000000000,
0x3f0fc7f40300c0719f67ccabf0000fff000ffffffffff800000007fffffffffffffffffffff,
0x3f0fc7f43f0fc7f5ff7fcfabf0000ffffffffffffffffffffffffffffffffffffffffffffff,
0xc53159b0c53159b0010050283003f00300301ffffffffffffffff8000000fffffffffffffff,
0x1ca728801ca7288000200900040055004004027ffff801fffff8018000000f01ffffffffffff,
0x1cf729921cf7299200300902060077006006037fffffffffffffff8000000fffffffffffffff,
0x50151b0050151b001004028300aa00b00b05800007fe000007fe00000000fe000000000000,
0x10a63c0910a63c0900200c008500cc00d00d06801ff800001ff8000000000300000000000000,
0x1c0701801cc73198000001000000ff00000f00000000007fffffff8000000000000000000000,
0x1cf73d9b1cf73d9b00300d028700ff00f00f07ffffffffffffffff8000000fffffffffffffff,
0x1fc7f1f85c070180180601c00000fffff000007fffffff800000000000000000000000000000,
0x50141e4450141e44a4291f808030303003008000007ff800007ff800007f0ffffffffffffff,
0x503d5ed4503d5ed4a47b5f8990f0f0f10f118801fffff801fffff801ffff3ffffffffffffff,
0xf0140a04f0140a05e028150001111110110007fe00001ffe00001ffe007fc01ffffffffffff,
0xf5141f64f5141f65ed291fa2a3333332332297fe007ffffe007ffffe007fcffffffffffffff,
0xff1fdff4f714df75ff6fdfabf3333fff332ffffffffffffe007ffffffffffffffffffffffff,
0x300c0644300c0645ec7b0f8383f003f03f03800000000000000007ffffff000000000000000,
0xf43d1f84c030180180601c0003f3f3f3000007fffffff800000000000000000000000000000,
0xf53d5ff4f53d5ff5ed7b5fabb3f3f3f33f339ffffffffffffffffffffffffffffffffffffff,
0x1fa7e8a05fa7e8a05f27c950045555554554427ffff801fffff801ffffffff01ffffffffffff,
0x1ff7fcff5fb7eca75ff7fddabf5555fff554fffffffffffffff801ffffffffffffffffffffff,
0x1fc7f1b85c070180180601400055ff55f000007fffffff800000000000000000000000000000,
0x1ff7fdbb5ff7fdbb5f37cd528755ff55f55f47ffffffffffffffffffffffffffffffffffffff,
0x300c0644300c0645fc7d0f82877007707706800000000000000007ffffff000000000000000,
0x1fc7e1f05c070180180601c0007777776000007fffffff800000000000000000000000000000,
0x1ff7e9f65ff7e9f65ff7d9fa2e77777767766b7fffffffffffffffffffffffffffffffffffff,
0x20080200a0080200a00802054080808088088400000000000000000000000000000000000000,
0x20080200a0080200a00822055088008808809000000000000000000000000000000000000000,
0x20080200a0081208a00802054088880008890000000000000000000000000000000000000000,
0x20081609a0081609a0082605d188888898899480000000000000000000000000000000000000,
0x20381e0fa3f8fe7fe7f9fe3fff8888889fffff800000007fffffffffffffffffffffffffffff,
0x3cff3f9bbcff3f9ba0382f07d788ff88f88f97ffffffffffffffff8000000fffffffffffffff,
0x2058161ba058161ba0982607f3a8a8a8ba8bb580000000000000000000000000000000000000,
0x20080244a0080244a0c832ad78aa00aa0aa0b800000000000000000000000000000000000000,
0x20380e47a3f8fe7fe7f9febfffaa00aa0fffff800000007fffffffffffffffffffffffffffff,
0x20080300a0080300a008020540aaaa0000000000000000000000000000000000000000000000,
0x20080300a0481358a008022540aaaa000aab0000000000000007fe0000000000000000000000,
0x20081709a0481759a0082625d1aaaa889aab9480000000000007fe0000000000000000000000,
0x20481358a0080300a008028540aaaaaab00000000007fe000000000000000000000000000000,
0x2058175fa058175fa0d836affbaaaaaabaabbd800007fe000007fe00000000fe000000000000,
0x20781f5fa3f8ff7fe7f9febfffaaaaaabfffff800007fe7fffffffffffffffffffffffffffff,
0x3cff3fdfbcff3fdfa0f83fafffaaffaafaafbfffffffffffffffff8000000fffffffffffffff,
0x300c0200b08c2200a008020540c0c0000c0c0000000000000000000000000000000000000000,
0x30ac2a00b0ac2a00a1284a0544c0c0c0cc0cc600000000000000000000000000000000000000,
0x30bc2e07b3fcfe7fe7f9fe3fffc0c0c0cfffff800000007fffffffffffffffffffffffffffff,
0x38fc2a12b8fc2a12a1384a0746c0f0c0ec0ec77fe000007fe000000000000c00000000000000,
0x3cff3f9bbcff3f9ba1384f07c7c0ffc0fc0fc7ffffffffffffffff8000000fffffffffffffff,
0x20088200a0088200a10d620550cc00cc0cc0d00000000000000000001ff80000000000000000,
0x20089609a0089609a10d6605d1cc88cc9cc9d48000000000000000001ff80000000000000000,
0x300e0200b08eb208a009020540cccc000ccd0000000000001ff8000000000000000000000000,
0x300e1609b08eb609a0092605d1cccc889ccd9480000000001ff8000000000000000000000000,
0x308eb208b00e0200a00c020540ccccccd00000001ff800000000000000000000000000000000,
0x30aebe09b0aebe09a12d6e05d5ccccccdccdd6801ff800001ff800001ff80300000000000000,
0x30bebe0fb3fefe7fe7fdfe3fffccccccdfffff801ff8007fffffffffffffffffffffffffffff,
0x3cffbf9bbcffbf9ba13d6f07d7ccffccfccfd7ffffffffffffffff801ff80fffffffffffffff,
0x30fc2a12b0fc2a12a1b84a0766e0e0e0ee0ee700000000000000000000000000000000000000,
0x30fc3f5fb0fc3f5fa1f87eafffeaeaeafeafff800007fe000007fe00000000fe000000000000,
0x20088244a0088244a1cd72ad78ee00ee0ee0f80000000000000000001ff80000000000000000,
0x30aebe4db0aebe4da1ed7eadfdeecceedeedfe801ff800001ff800001ff80300000000000000,
0x300e0300b0ceb358a009022540eeee000eef0000000000001ffffe0000000000000000000000,
0x305e175fb0deb75fa0d936affbeeeeaabeefbd800007fe001ffffe00000000fe000000000000,
0x30aebf09b0eebf59a12d6e25d5eeeeccdeefd6801ff800001ffffe001ff80300000000000000,
0x30febf5fb0febf5fa1fd7eafffeeeeeefeefff801ffffe001ffffe001ff803fe000000000000,
0x38ac2a00baec2a10a5284a0544f0f0c0cf0ec6000000007fe000000000000000000000000000,
0x3afc2a12bafc2a12b5b84a0766f0f0f0ef0ee77fe000007fe000007fe0000c00000000000000,
0x3afc3e1bbafc3e1bb5b86e07f7f8f8f8ff8ff7ffe000007fe000007fe0000c00000000000000,
0x3afc2a56bafc2a56b5f87aaf7efaf0faefaeff7fe000007fe000007fe0000c00000000000000,
0x3afc3f5fbafc3f5fb5f87eaffffafafaffafffffe007fe7fe007fe7fe0000cfe000000000000,
0x22088200a2088200b58d620570fc00fc0fc0f000000000000000007ffff80000000000000000,
0x380e0200baceb218a409020540fcfc000fcf00000000007ffff8000000000000000000000000,
0x3afe2a12bafeba1ab5b94a0766fcfcf0efcfe77fe000007ffff8007fe0000c00000000000000,
0x3afebe1bbafebe1bb5bd6e07f7fcfcfcffcff7fffff8007ffff8007ffff80f00000000000000,
0x3afebf5fbafebf5fb5fd7eaffffefefeffeffffffffffe7ffffffe7ffff80ffe000000000000,
0x20080200a308c260e609823540ff00000ff00000000000000000000000000000000000000000,
0x20380e07a3f8fe7fe7f9fe3fffff00000fffff800000007fffffffffffffffffffffffffffff,
0x20080244a308c264e6c9b2bd78ff00aa0ff0b800000000000000000000000000000000000000,
0x2308c260e0080200b80e02c540ff00ff00000000000000000000000000000000000000000000,
0x2308c264e0080244b8ce32ed78ff00ff0aa0b800000000000000000000000000000000000000,
0x2308c260e308c260fe0f82f540ff00ff0ff00000000000000000000000000000000000000000,
0x2308c264e308c264fecfb2fd78ff00ff0ff0b800000000000000000000000000000000000000,
0x2308c264e308c264ffcff2fd78ff00ff0ff0f800000000000000007ffffff000000000000000,
0x2338ce67e3f8fe7ffffffeffffff00ff0fffff800000007fffffffffffffffffffffffffffff,
0x2308c264e308c264ffcff2fd78ff80ff8ff8fc00000000000000007ffffff000000000000000,
0x2308c264e308d26cffcff2fd78ff88ff0ff9f800000000000000007ffffff000000000000000,
0x2308d66de308d66dffcff6fdf9ff88ff9ff9fc80000000000000007ffffff000000000000000,
0x2358c276e358c276ffdff2ff7affa0ffaffafd00000000000000007ffffff000000000000000,
0x2358d67fe358d67fffdff6fffbffa8ffbffbfd80000000000000007ffffff000000000000000,
0x2308c364e308c364ffcff2fd78ffaaff0ff0f800000000000000007ffffff000000000000000,
0x2308c364e348d37cffcff2fd78ffaaff0ffbf800000000000007fe7ffffff000000000000000,
0x2358d77fe058175fb8de36effbffaaffbaabbd800007fe000007fe00000000fe000000000000,
0x2358d77fe358d77fffdff6fffbffaaffbffbfd800007fe000007fe7ffffff0fe000000000000,
0x330cc264f38ce264ffcff2fd78ffc0ff0ffcf800000000000000007ffffff000000000000000,
0x33acea64f3acea64ffeffafd7cffc0ffcffcfe00000000000000007ffffff000000000000000,
0x330ec264f30ec264ffcff2fd78ffccff0ff0f800000000000000007ffffff000000000000000,
0x33aefe6df3aefe6dffeffefdfdffccffdffdfe801ff800001ff8007ffffff300000000000000,
0x33fcea76f3fcea76fffffaff7effe0ffeffeff00000000000000007ffffff000000000000000,
0x33feff7ff3feff7ffffffeffffffeeffffffff801ffffe001ffffe7ffffff3fe000000000000,
0x3afc2a12bbfcea72f7b9ca3766fff0f0effee77fe000007fe000007fe0000c00000000000000,
0x3bfcea76fbfcea76fffffaff7efff0ffeffeff7fe000007fe000007ffffffc00000000000000,
0x3c0f0380bc0f0380a008030540ffff0000000000000000000000000000000000000000000000,
0x3c0f0380bfcff3f8e609833540ffff000fff00000000007fffffff8000000000000000000000,
0x3c3f0f87bfffffffe7f9ff3fffffff000fffff800000007fffffffffffffffffffffffffffff,
0x3cff3f9bbcff3f9ba0380f07c7ffff00f00f07ffffffffffffffff8000000fffffffffffffff,
0x3cff3f9bbffffffbe6398f37c7ffff00ffff07ffffffffffffffff8000000fffffffffffffff,
0x3f8fe3a0fc0f0380b80e034540ffff554000007ffff801800000000000000000000000000000,
0x3c0f1789bfcff7f9e609a735d1ffff889fff94800000007fffffff8000000000000000000000,
0x3c0f03c4bfcff3fce6c9b3bd78ffffaa0fffb8000000007fffffff8000000000000000000000,
0x3c4f13d8bc0f0380a008038540ffffaab00000000007fe000000000000000000000000000000,
0x3c5f17dfbc5f17dfa0d837affbffffaabaabbd800007fe000007fe00000000fe000000000000,
0x3c5f17dfbfdff7ffe6d9b7bffbffffaabfffbd800007fe7fffffff80000000fe000000000000,
0x3caf2b80bfeffbf8e729cb3544ffffc0cfffc6000000007fffffff8000000000000000000000,
0x3cafbf89bfeffff9e72def35d5ffffccdfffd6801ff8007fffffff801ff80300000000000000,
0x3cff2b92bffffbfae7b9cb3766ffffe0efffe7000000007fffffff8000000000000000000000,
0x3cffbfdfbfffffffe7fdffbfffffffeeffffff801ffffe7fffffff801ff803fe000000000000,
0x3eff2b92beff2b92b5b84b0766fffff0ef0ee77fe000007fe000007fe0000c00000000000000,
0x3effbf9bbffffffbf7bdef37f7fffffcfffff7fffff8007ffffffffffff80f00000000000000,
0x3f0fc3e0fc0f0380b80e03c540ffffff00000000000000000000000000000000000000000000,
0x3f0fc3e0ff0fc3e0fe0f83f540ffffff0ff00000000000000000000000000000000000000000,
0x3f0fc3e4ff0fc3e4fecfb3fd78ffffff0ff0b800000000000000000000000000000000000000,
0x3f0fc3e4ff0fc3e4ffcff3fd78ffffff0ff0f800000000000000007ffffff000000000000000,
0x3f0fc3e0ffcff3f8fe0f83f540ffffff0fff00000000007fffffff8000000000000000000000,
0x3f0fc3e4ffcff3fcffcff3fd78ffffff0ffff8000000007ffffffffffffff000000000000000,
0x3f4fd3f8fc0f0380b80e03c540ffffffb00000000007fe000000000000000000000000000000,
0x3f5fd7fffc5f17dfb8de37effbffffffbaabbd800007fe000007fe00000000fe000000000000,
0x3f5fd7ffff5fd7fffedfb7fffbffffffbffbbd800007fe000007fe00000000fe000000000000,
0x3f8ff3e8fc0f0380b80e03c540ffffffd00000001ff800000000000000000000000000000000,
0x3fcff3f8fc0f0380b80e03c540fffffff000007fffffff800000000000000000000000000000,
0x3ffffffbfc3f0f83b83e0fc7c7fffffff00007ffffffff800000000000000fffffffffffffff,
0x3fdff7fffc1f0787b8de37cffbfffffff000bdffffffff8000000000000000fe000000000000,
0x3fcff3f8fc0f0380b80e03c540fffffff808847fffffff800000000000000000000000000000,
0x3fcff3f8fc0f0380b80e23c550fffffff880907fffffff800000000000000000000000000000,
0x3fcff3f8fc0f1388b80e03c540fffffff889007fffffff800000000000000000000000000000,
0x3fcff7f9fc0f1789b80e27c5d1fffffff88994ffffffff800000000000000000000000000000,
0x3fdff3fafc5f0392b89e03c762fffffffa0aa57fffffff800000000000000000000000000000,
0x3fdff7fbfc5f179bb89e27c7f3fffffffa8bb5ffffffff800000000000000000000000000000,
0x3fcff3f8fc0f03c0b80e03e540fffffffaa0007fffffff800000000000000000000000000000,
0x3fcff3fcfc0f03c4b8ce33ed78fffffffaa0b87fffffff800000000000000000000000000000,
0x3fcff7fdfc0f17cdb8ce37edf9fffffffaa9bcffffffff800000000000000000000000000000,
0x3fcff3f8fc4f13d8b80e03e540fffffffaab007fffffff800007fe0000000000000000000000,
0x3fdff7fffc5f17dfb8de37effbfffffffaabbdffffffff800007fe00000000fe000000000000,
0x3fcff3f8fc0f0380b90e43c540fffffffc00c07fffffff800000000000000000000000000000,
0x3fcff3f8fc8f2380b80e03c540fffffffc0c007fffffff800000000000000000000000000000,
0x3feffbf8fcaf2b80b92e4bc544fffffffc0cc67fffffff800000000000000000000000000000,
0x3fcff3f8fc0f8380b80f03c540fffffffcc0007fffffff800000000000000000000000000000,
0x3feffff9fcafbf89b92f6fc5d5fffffffccdd6ffffffff801ff800001ff80300000000000000,
0x3ffffbfafcff2b92b9be4bc766fffffffe0ee77fffffff800000000000000000000000000000,
0x3ffffbfafeff2b92bdbe4bc766ffffffff0ee77fffffffffe000007fe0000c00000000000000,
0x3fcff3f8ff0fc3e0fe0f83f540fffffffff0007fffffff800000000000000000000000000000,
0x3fcff3fcff0fc3e4fecfb3fd78fffffffff0b87fffffff800000000000000000000000000000,
0x3fcff3fcff0fc3e4ffcff3fd78fffffffff0f87fffffff800000007ffffff000000000000000,
0x3fcff3f8ffcff3f8fe0f83f540ffffffffff007fffffffffffffff8000000000000000000000,
0x3fdff7ffffdff7fffedfb7fffbffffffffffbdffffffffffffffff80000000fe000000000000]

def seed0StateIndices : Array (Array (List Nat)) := #[#[],
#[],
#[],
#[],
#[[54, 67, 79, 133],
[67, 79, 134, 139]],
#[[54, 95, 67, 79, 115, 141],
[54, 67, 79, 134, 165],
[34, 67, 79, 134, 165],
[54, 99, 70, 115, 141],
[54, 95, 67, 79, 132],
[90, 54, 67, 79, 131],
[54, 67, 79, 136, 163],
[67, 79, 115, 134, 138],
[54, 67, 110, 115, 160],
[54, 95, 67, 127, 160],
[54, 67, 79, 134, 162],
[104, 67, 79, 115, 134],
[67, 79, 124, 134, 154],
[54, 109, 113, 115, 157],
[54, 67, 79, 134, 166],
[54, 94, 67, 79, 114],
[27, 54, 67, 134, 165],
[54, 101, 58, 115, 141],
[67, 79, 123, 134, 165],
[54, 107, 86, 115, 157],
[54, 95, 86, 125, 157],
[54, 67, 129, 134, 165],
[0, 54, 67, 79, 134],
[54, 67, 79, 132, 134],
[11, 54, 67, 79, 165]],
#[[54, 95, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 141],
[10, 54, 95, 67, 79, 115],
[24, 34, 67, 79, 115, 141],
[27, 24, 54, 67, 115, 141],
[10, 24, 54, 67, 79, 115],
[54, 95, 67, 79, 115, 131],
[54, 95, 67, 79, 115, 162],
[54, 99, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 147],
[54, 95, 67, 79, 115, 151],
[10, 27, 54, 95, 67, 115],
[10, 16, 54, 95, 67, 79],
[54, 95, 67, 79, 114, 165],
[54, 67, 79, 115, 134, 141],
[54, 67, 107, 79, 115, 141],
[54, 95, 67, 79, 115, 157],
[10, 24, 34, 67, 79, 115],
[24, 54, 67, 70, 115, 141],
[24, 54, 67, 80, 115, 141],
[24, 54, 67, 79, 115, 147],
[54, 67, 79, 115, 46, 141],
[27, 29, 24, 54, 115, 141],
[10, 27, 24, 54, 67, 115],
[24, 54, 58, 86, 115, 141],
[34, 67, 79, 115, 134, 141],
[24, 54, 67, 79, 115, 157],
[54, 67, 79, 115, 61, 141],
[24, 54, 67, 60, 115, 141],
[10, 16, 24, 54, 67, 79],
[24, 54, 67, 79, 114, 165],
[34, 67, 107, 79, 115, 141],
[24, 54, 67, 115, 129, 141],
[54, 67, 79, 115, 117, 141],
[24, 54, 67, 79, 115, 131],
[34, 99, 67, 79, 115, 141],
[24, 54, 67, 112, 115, 141],
[24, 54, 67, 79, 115, 162],
[24, 54, 67, 81, 115, 141],
[24, 54, 67, 79, 115, 151],
[54, 95, 67, 79, 115, 119],
[54, 100, 67, 82, 115, 141],
[88, 54, 95, 67, 79, 131],
[54, 95, 67, 79, 136, 162],
[54, 67, 79, 115, 136, 162],
[54, 67, 79, 136, 165, 164],
[16, 54, 95, 67, 79, 131],
[54, 95, 67, 79, 131, 165],
[54, 92, 67, 79, 115, 164],
[54, 95, 67, 79, 124, 131],
[9, 54, 95, 67, 79, 115],
[54, 67, 70, 110, 115, 141],
[27, 54, 95, 67, 115, 131],
[54, 95, 67, 70, 115, 160],
[54, 67, 79, 115, 131, 134],
[54, 95, 67, 79, 131, 135],
[12, 54, 95, 67, 79, 115],
[54, 67, 110, 79, 115, 141],
[54, 95, 67, 79, 115, 160],
[54, 95, 67, 79, 115, 137],
[54, 95, 67, 79, 115, 140],
[54, 95, 67, 79, 115, 142],
[27, 54, 100, 67, 115, 141],
[27, 54, 95, 67, 115, 148],
[16, 54, 95, 67, 79, 162],
[54, 100, 58, 67, 115, 141],
[54, 91, 67, 79, 115, 134],
[54, 95, 67, 79, 114, 162],
[27, 54, 99, 67, 115, 141],
[27, 54, 95, 67, 115, 147],
[89, 54, 95, 67, 79, 115],
[27, 54, 95, 67, 115, 162],
[1, 54, 95, 67, 79, 115],
[54, 99, 67, 80, 115, 141],
[54, 95, 67, 80, 115, 147],
[54, 97, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 144],
[10, 54, 99, 67, 79, 115],
[20, 54, 67, 79, 115, 141],
[54, 99, 67, 79, 115, 147],
[54, 95, 67, 79, 115, 150],
[54, 95, 67, 79, 115, 145],
[16, 54, 95, 67, 79, 147],
[45, 54, 95, 67, 79, 115],
[4, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 120, 147],
[54, 95, 67, 79, 115, 158],
[54, 98, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 146],
[25, 54, 95, 67, 79, 115],
[38, 54, 67, 79, 115, 141],
[39, 54, 95, 67, 79, 115],
[54, 105, 67, 81, 115, 141],
[27, 54, 95, 67, 115, 151],
[16, 54, 95, 67, 79, 151],
[49, 54, 95, 67, 79, 115],
[3, 54, 95, 67, 79, 115],
[54, 95, 67, 81, 115, 151],
[54, 95, 67, 79, 121, 151],
[36, 54, 95, 67, 79, 115],
[54, 58, 109, 113, 115, 141],
[54, 95, 67, 79, 115, 152],
[54, 95, 67, 79, 115, 163],
[54, 95, 67, 115, 129, 154],
[54, 67, 79, 115, 134, 154],
[54, 95, 67, 79, 114, 166],
[54, 94, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 155],
[54, 102, 67, 79, 115, 141],
[16, 54, 95, 67, 79, 143],
[10, 16, 27, 54, 95, 67],
[27, 54, 95, 67, 114, 165],
[27, 54, 67, 115, 134, 141],
[10, 54, 67, 107, 79, 115],
[16, 54, 95, 67, 79, 157],
[54, 95, 67, 59, 79, 115],
[27, 54, 67, 107, 115, 141],
[27, 54, 95, 67, 115, 157],
[10, 54, 67, 79, 115, 134],
[54, 95, 67, 79, 115, 143],
[54, 93, 95, 67, 79, 114],
[54, 101, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 149],
[54, 58, 107, 86, 115, 141],
[54, 95, 67, 114, 129, 165],
[54, 67, 79, 134, 165],
[54, 95, 67, 79, 134, 165],
[54, 67, 79, 114, 134, 165],
[0, 54, 95, 67, 79, 114],
[17, 54, 95, 67, 79, 165],
[54, 67, 79, 115, 134, 165],
[11, 54, 67, 79, 115, 141],
[67, 71, 107, 79, 115, 141],
[54, 67, 115, 129, 134, 141],
[18, 54, 67, 79, 115, 141],
[54, 67, 107, 79, 115, 157],
[2, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 125, 157],
[54, 67, 108, 79, 115, 141],
[54, 67, 106, 79, 115, 141],
[54, 95, 67, 79, 115, 156],
[15, 54, 67, 79, 115, 141],
[31, 54, 67, 79, 115, 141],
[32, 54, 95, 67, 79, 115]],
#[[54, 95, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 141],
[34, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 77, 79, 115, 141],
[44, 54, 95, 67, 79, 115, 141],
[54, 95, 105, 67, 79, 115, 141],
[48, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 124, 141],
[51, 54, 95, 67, 79, 115, 141],
[10, 54, 95, 67, 79, 115],
[29, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 86, 115, 141],
[54, 95, 58, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 126, 141],
[54, 95, 64, 67, 79, 115, 141],
[24, 34, 67, 79, 115, 141],
[24, 34, 54, 67, 79, 115, 141],
[24, 54, 67, 77, 79, 115, 141],
[24, 44, 54, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 124, 141],
[24, 51, 54, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 56, 141],
[21, 24, 54, 67, 79, 115, 141],
[27, 24, 54, 67, 115, 141],
[29, 24, 54, 67, 79, 115, 141],
[24, 54, 67, 79, 86, 115, 141],
[24, 54, 58, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 126, 141],
[24, 54, 64, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 69, 141],
[22, 24, 54, 67, 79, 115, 141],
[10, 24, 54, 67, 79, 115],
[16, 24, 54, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 141, 165],
[24, 54, 67, 79, 114, 115, 141],
[24, 54, 67, 79, 115, 118, 141],
[23, 24, 54, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 136, 141],
[24, 88, 54, 67, 79, 115, 141],
[24, 54, 105, 67, 79, 115, 141],
[24, 48, 54, 67, 79, 115, 141],
[24, 54, 67, 109, 79, 115, 141],
[24, 62, 54, 67, 79, 115, 141],
[10, 24, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 118, 141],
[23, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 56, 141],
[21, 54, 95, 67, 79, 115, 141],
[10, 34, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 69, 141],
[22, 54, 95, 67, 79, 115, 141],
[54, 91, 95, 67, 79, 115, 164],
[88, 54, 67, 79, 115, 136, 141],
[54, 67, 79, 115, 136, 141, 164],
[10, 54, 95, 67, 79, 115, 164],
[54, 95, 67, 79, 115, 165, 164],
[54, 95, 67, 79, 115, 164, 154],
[10, 54, 95, 67, 79, 115, 136],
[54, 95, 67, 79, 87, 115, 141],
[54, 95, 67, 79, 115, 131],
[54, 95, 67, 70, 79, 115, 141],
[54, 95, 67, 79, 115, 131, 136],
[54, 95, 67, 111, 79, 115, 141],
[72, 54, 95, 67, 79, 115, 141],
[10, 54, 95, 67, 77, 79, 115],
[54, 95, 67, 79, 115, 128, 141],
[54, 95, 74, 67, 79, 115, 141],
[28, 54, 95, 67, 79, 115, 141],
[10, 54, 91, 95, 67, 79, 115],
[54, 91, 95, 67, 79, 114, 115],
[10, 88, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 162],
[54, 95, 67, 79, 80, 115, 141],
[88, 54, 95, 67, 79, 115, 162],
[41, 54, 95, 67, 79, 115, 141],
[54, 99, 67, 79, 115, 141],
[54, 95, 99, 67, 79, 115, 141],
[44, 54, 99, 67, 79, 115, 141],
[42, 54, 95, 67, 79, 115, 141],
[10, 44, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 147],
[54, 95, 67, 79, 115, 120, 141],
[44, 54, 95, 67, 79, 115, 147],
[43, 54, 95, 67, 79, 115, 141],
[40, 54, 95, 67, 79, 115, 141],
[48, 54, 105, 67, 79, 115, 141],
[54, 105, 67, 109, 79, 115, 141],
[10, 54, 95, 105, 67, 79, 115],
[63, 54, 95, 67, 79, 115, 141],
[19, 54, 95, 67, 79, 115, 141],
[10, 48, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 151],
[54, 95, 67, 73, 79, 115, 141],
[48, 54, 95, 67, 79, 115, 151],
[37, 54, 95, 67, 79, 115, 141],
[53, 54, 95, 67, 79, 115, 154],
[62, 54, 67, 109, 79, 115, 141],
[54, 67, 109, 79, 113, 115, 141],
[10, 54, 95, 67, 109, 79, 115],
[54, 95, 67, 79, 115, 154, 159],
[54, 95, 65, 67, 79, 115, 141],
[90, 54, 95, 67, 79, 115, 141],
[10, 54, 95, 67, 79, 115, 154],
[54, 95, 67, 79, 114, 115, 154],
[10, 54, 95, 67, 79, 115, 124],
[54, 95, 67, 79, 115, 141, 166],
[54, 95, 67, 79, 115, 122, 141],
[14, 54, 95, 67, 79, 115, 141],
[10, 62, 54, 95, 67, 79, 115],
[54, 95, 67, 76, 79, 115, 141],
[54, 95, 103, 67, 79, 115, 141],
[10, 53, 54, 95, 67, 79, 115],
[10, 51, 54, 95, 67, 79, 115],
[54, 95, 67, 79, 115, 141, 153],
[50, 54, 95, 67, 79, 115, 141],
[35, 54, 95, 67, 79, 115, 141],
[10, 54, 55, 95, 67, 79, 115],
[5, 10, 54, 95, 67, 79, 115],
[10, 27, 54, 95, 67, 115],
[10, 29, 54, 95, 67, 79, 115],
[10, 54, 95, 67, 79, 86, 115],
[10, 54, 95, 58, 67, 79, 115],
[10, 54, 95, 67, 79, 115, 126],
[10, 54, 95, 64, 67, 79, 115],
[10, 54, 95, 67, 68, 79, 115],
[6, 10, 54, 95, 67, 79, 115],
[10, 54, 95, 96, 67, 79, 115],
[7, 10, 54, 95, 67, 79, 115],
[10, 16, 54, 95, 67, 79],
[10, 16, 54, 95, 67, 79, 115],
[10, 54, 95, 67, 79, 115, 116],
[8, 10, 54, 95, 67, 79, 115],
[54, 95, 96, 67, 79, 115, 141],
[7, 54, 95, 67, 79, 115, 141],
[10, 54, 95, 67, 79, 115, 165],
[10, 54, 95, 67, 79, 114, 115],
[10, 54, 95, 67, 79, 115, 159],
[10, 54, 95, 66, 67, 79, 115],
[54, 95, 67, 79, 115, 116, 141],
[8, 54, 95, 67, 79, 115, 141],
[54, 55, 95, 67, 79, 115, 141],
[5, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 68, 79, 115, 141],
[6, 54, 95, 67, 79, 115, 141],
[47, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 114, 165],
[54, 95, 67, 79, 114, 115, 165],
[54, 83, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 130, 141],
[54, 95, 67, 84, 79, 115, 141],
[26, 54, 95, 67, 79, 115, 141],
[54, 67, 79, 115, 134, 141],
[54, 95, 67, 71, 79, 115, 141],
[54, 67, 79, 114, 115, 134, 141],
[54, 67, 107, 79, 115, 141],
[54, 95, 67, 107, 79, 115, 141],
[54, 58, 67, 107, 79, 115, 141],
[54, 95, 67, 79, 115, 157],
[54, 95, 67, 79, 115, 125, 141],
[54, 95, 58, 67, 79, 115, 157],
[54, 95, 57, 67, 79, 115, 141],
[33, 54, 95, 67, 79, 115, 141],
[52, 54, 95, 67, 79, 115, 141],
[54, 95, 66, 67, 79, 115, 159],
[54, 95, 67, 79, 115, 159, 161],
[54, 95, 67, 78, 79, 115, 141],
[13, 54, 95, 67, 79, 115, 141],
[54, 95, 75, 67, 79, 115, 141],
[54, 95, 67, 79, 85, 115, 141],
[30, 54, 95, 67, 79, 115, 141]],
#[[54, 95, 67, 79, 115, 141],
[24, 54, 67, 79, 115, 141],
[34, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 77, 79, 115, 141],
[44, 54, 95, 67, 79, 115, 141],
[54, 95, 105, 67, 79, 115, 141],
[48, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 124, 141],
[51, 54, 95, 67, 79, 115, 141],
[10, 54, 95, 67, 79, 115],
[29, 54, 95, 67, 79, 115, 141],
[54, 95, 67, 79, 86, 115, 141],
[54, 95, 58, 67, 79, 115, 141],
[54, 95, 67, 79, 115, 126, 141],
[54, 95, 64, 67, 79, 115, 141]],
#[[54, 95, 67, 79, 115, 141]]]

def seed0AdviceData : Array (Array (Array Nat)) := #[#[],
#[],
#[],
#[],
#[#[],
#[]],
#[#[],
#[],
#[],
#[],
#[],
#[1152],
#[1180],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[1180],
#[1160],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[66656],
#[]],
#[#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[66696],
#[66752],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[136272],
#[132288],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[199796],
#[201784,
263336],
#[263372],
#[],
#[66756],
#[],
#[66696],
#[395400,
329932],
#[328844],
#[],
#[463944,
526480,
525496],
#[],
#[525416,
591000],
#[459904,
657560],
#[657544],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[726088],
#[721976,
657544],
#[656520],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[791608,
854152,
853168],
#[],
#[394376],
#[857184],
#[787552,
918720],
#[918664,
984244],
#[984268],
#[],
#[],
#[],
#[],
#[1049744],
#[1049792],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[1119288,
263344],
#[1115252],
#[],
#[1184824,
1247368,
1246384],
#[1250400,
1377384,
1315952],
#[132098,
1051654,
1049610,
1573902,
1442834,
918658,
1508510],
#[263372],
#[1180768,
1379432,
1377392],
#[1443000],
#[],
#[],
#[1574088],
#[1184864],
#[1377464],
#[],
#[1246312],
#[],
#[1311856],
#[],
#[],
#[],
#[],
#[],
#[]],
#[#[70658,
66566,
138250,
136206,
133138,
132118],
#[197638,
265226,
263182,
329746,
328726],
#[],
#[398492],
#[525384,
464000,
592040,
591064],
#[],
#[662624,
660608,
657576,
656600],
#[],
#[],
#[267270,
328714,
723982,
721938,
787478],
#[],
#[857204],
#[922696,
984144,
857240,
1050808,
1049832],
#[],
#[],
#[1121290,
1119246,
1116178,
1115158],
#[],
#[1180828],
#[1377336,
1246344,
1312944,
1311968],
#[],
#[],
#[],
#[],
#[1119242,
1442830,
1509394,
1508374],
#[],
#[1574004],
#[1770568,
1643600,
1574040,
1706168,
1705192],
#[],
#[],
#[1836228],
#[],
#[1115146,
1510414,
1508370,
1901590],
#[],
#[1967308],
#[2163840,
2036872,
2100368,
2098328,
1967360],
#[],
#[],
#[2229508],
#[2298960,
2362472,
2360456,
2426080],
#[],
#[2493544,
2491528,
2558128,
2557152],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[2626756],
#[],
#[2692152,
2820272,
2754820],
#[2884824],
#[2950336,
918780],
#[3016964],
#[2950280,
3082492,
460036],
#[3213516,
3146980,
656644],
#[3278044],
#[],
#[1184770,
2229254,
3410954,
3408910,
3015698,
3671062,
3212418,
2753678,
3347625,
3540145,
3480761,
3478721,
3605705],
#[922720,
3736680,
466032,
3085456,
3803328,
3802352],
#[],
#[3871900],
#[662624],
#[3413196],
#[3937476],
#[],
#[4002944],
#[4068432,
4136080,
4134072,
4196584],
#[4265016,
394416,
4326584,
4393184],
#[4588600,
4461648,
4529288,
4527280],
#[1250306,
2425862,
4656138,
4654094,
4195346,
4719638,
2884745,
2819210,
3606733],
#[4396148,
400532],
#[4789304,
4856928,
4854912],
#[4916296,
4982952,
4981976],
#[2294786,
5112838,
4066314,
4457486,
5048338,
5047318,
2690122,
4263029],
#[],
#[4785280,
5179560,
5178584],
#[5248128,
5310632,
5309656],
#[5440568,
5047400,
4658352,
5376224],
#[2364418,
1311750,
4131850,
4523022,
5374994,
5506070],
#[],
#[5178440,
4850816,
5571752],
#[5702728,
5641344,
5768408],
#[5899340,
5837956,
5965996,
5965020],
#[6032480,
6030464],
#[525420],
#[],
#[525384],
#[],
#[6227000,
6102152,
6100144,
6162656],
#[2495490,
2556934,
6097930,
6095886,
6161426,
6292502,
6034489],
#[],
#[6360160,
6358144,
6423720],
#[6495332,
6493316,
6490284,
6489308],
#[],
#[],
#[6554732,
984212],
#[],
#[591108],
#[592056],
#[529464,
6626400,
6624384,
657576,
3147960,
6685912],
#[],
#[6816904,
6753424,
6751384,
6558888,
6882560],
#[],
#[6882508,
6948068],
#[988328],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[7078984,
7019616,
7017600],
#[],
#[],
#[7145688],
#[1512458,
1508366,
7214098,
7210006],
#[],
#[7279772],
#[7537760,
7345256,
7406704,
7279816,
7473392],
#[],
#[],
#[],
#[],
#[],
#[],
#[1446922,
1901582,
7212050,
7210006],
#[],
#[],
#[],
#[],
#[],
#[],
#[7607472,
7734456,
7675072,
7673032],
#[],
#[],
#[],
#[],
#[],
#[7801000],
#[],
#[],
#[7930952,
466016,
464000,
7869596,
7997608,
7996632],
#[1577986,
1967110,
7277578,
7275534,
8455186,
8389654,
8066177,
8193160,
8324233,
8258698,
8129681,
8127641,
6882474,
7865526],
#[8520840],
#[],
#[],
#[],
#[8393884],
#[1639426,
7343110,
7341066,
7735310,
8586258,
7734294,
6817890,
3541149,
6816938,
8193216,
8521921,
8520898,
3540174],
#[4332620,
400500,
4330628,
8262800,
398492],
#[8655968,
8719464,
8717424,
8324344],
#[2032642,
7605254,
8782858,
7603214,
7407634,
7406614],
#[],
#[8651832,
8062096,
8849584,
8848608],
#[2102274,
1704966,
7670794,
7668750,
7472146,
8913942,
6757458,
6755434],
#[],
#[8721480,
8848464,
8131736,
8979640],
#[9049160,
9110608,
9176296],
#[9245756,
9307212,
8459416,
9373868,
9372892],
#[592040],
#[],
#[1049860],
#[1050816],
#[],
#[],
#[],
#[]],
#[#[70658,
132099,
66566,
136199,
597002,
656395,
594958,
658447,
591890,
660499,
590870,
661527,
328763,
394303,
197707,
263247,
463955,
529495,
199779,
265319,
466027,
531567,
722035,
787575,
459907,
525447,
201867,
267407,
853139,
918679,
855195,
920735,
460971,
526511,
202931,
268471,
854203,
919743,
856259,
921799,
726219,
791759],
#[984070,
1049607,
1510410,
1573899,
1508366,
1575951,
2033682,
2098195,
2032662,
2099223,
1377339,
1442879,
1901643,
1967183,
1115219,
1180759,
1903715,
1969255,
1117291,
1182831,
1639539,
1705079,
2294915,
2360455,
1246347,
1311887,
1770643,
1836183,
1772699,
1838239,
2295979,
2361519,
1247411,
1312951,
1771707,
1837247,
1773763,
1839303,
2163915,
2229455],
#[1049610,
2825230,
2823186,
3147798,
3146778,
3019849,
3085389,
2561105,
2626645,
2888801,
2954341,
2430057,
2495597,
2890881,
2956421,
2432137,
2497677,
3216553,
3282093,
2692273,
2757813,
3217625,
3283165,
2693345,
2758885],
#[2429954,
1115142,
3546122,
4391950,
3740690,
4196374,
4195354,
3413069,
3349582,
3677266,
4064362,
4129902,
3478657,
3611793,
3802265,
3871900,
3933341,
4002974,
4261057,
4326597,
4262129,
4327669],
#[5506050,
2495494,
1180682,
4463630,
4592658,
5179414,
5178394,
4916296,
4981833,
5047370,
5112909,
3413097,
3349610,
4658304,
4719745,
4789378,
4850821,
4529309,
5245096,
5309609,
5376170,
5440685,
5244120,
5310681,
5375194,
5441757],
#[2561026,
2556934,
5833738,
5708814,
5706770,
5703702,
5702682,
5575741,
5571646,
5637225,
4064369,
5768309,
5639305,
4066449,
5770389,
5641385,
4068537,
5772477,
5642457,
4069609,
5773549],
#[6161410,
2626566,
2622474,
5905422,
5903378,
5900310,
5899290,
5575761,
5571666,
5971040,
6030433,
6102114,
5112933,
5969024,
6032513,
6100098,
5115013,
5965992,
6034601,
6097066,
5117101,
5965016,
6035673,
6096090,
5118173],
#[2692098,
1246214,
6429706,
6427662,
6686738,
7013398,
6816794,
5641273,
6296709,
6228102,
3672202,
6490258,
6492314,
4068530,
6620342,
4261050,
6554814,
4263106,
6556870,
6362329,
6752509,
6882561,
6948101],
#[7537666,
2757638,
1311754,
7085070,
7083026,
7276566,
7341082,
7210057,
5117005,
7144545,
5440613,
7146625,
5442693,
6296753,
6228146,
7406809,
7472349],
#[1512454,
3146759,
2032650,
2819083,
7736334,
7799823,
7734290,
7801875,
8389654,
8455191,
7603259,
7668799,
8258635,
8324175,
5702739,
5899351,
8127587,
8193127,
4195435,
5178479,
6423667,
7079031,
8129667,
8195207,
4197515,
5180559,
6425747,
7081111,
7865499,
7931039,
8520875,
8586415,
6816947,
7341239,
3736763,
4588735,
7996611,
8062151,
7998667,
8064207],
#[2102278,
1573898,
8459282,
7800854,
7799834,
8657977,
8723517,
9182281,
9247821,
3546218,
4463726,
6691954,
7281782,
9051265,
9116805,
8789145,
8854685,
9313449,
9378989,
8920257,
8985797,
9314521,
9380061,
8921329,
8986869],
#[2167810,
1639430,
8789002,
8786958,
9831442,
7866390,
7865370,
3611722,
3609698,
9507956,
9575541,
9573494,
3802242,
9438342,
6886538,
9634958,
9700553,
9766093,
9701625,
9767165],
#[2233346,
1704966,
10552330,
8854542,
8852498,
7931926,
7930906,
9901128,
10032201,
9962570,
4850766,
10093648,
10224721,
10159186,
7476310,
4529254,
6757482,
4527238,
6755466,
9507992,
9575577,
9573530,
10291384,
10355897,
10422458,
10486973,
10290408,
10356969,
10421482,
10488045],
#[1774594,
1770502,
8920074,
8000526,
8914962,
10880022,
7996442,
6495314,
6490242,
10689685,
10684566,
10750106,
4261034,
10618030,
4265138,
10622134,
9700546,
10814662,
10755305,
9704705,
10818821],
#[1840130,
1836038,
11076618,
8985614,
8066066,
8980502,
8061978,
10945610,
5440590,
10949714,
5444694,
11011217,
10486933,
10689729,
10684610,
11015401,
10491117]],
#[#[70658,
132099,
66566,
136199,
597002,
656395,
594958,
658447,
591890,
660499,
590870,
661527,
328763,
394303,
197707,
263247,
463955,
529495,
199779,
265319,
466027,
531567,
722035,
787575,
459907,
525447,
201867,
267407,
853139,
918679,
855195,
920735,
460971,
526511,
202931,
268471,
854203,
919743,
856259,
921799,
726219,
791759]]]

def seed0States (s i : Nat) : List Nat := ((seed0StateIndices.getD s #[]).getD i []).map (fun j => seed0Words.getD j 0)

def seed0Count (s : Nat) : Nat := (seed0StateIndices.getD s #[]).size

def seed0Advice (s i : Nat) : Array Nat := (seed0AdviceData.getD s #[]).getD i #[]

def seed0Roots : List (Nat × Nat) := [(5, 0), (6, 0), (7, 0), (8, 0), (9, 0)]

def seed0VertexPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5],
[0, 1, 2, 3, 5, 4],
[0, 2, 1, 3, 4, 5],
[0, 2, 1, 3, 5, 4],
[3, 4, 5, 0, 1, 2],
[3, 4, 5, 0, 2, 1],
[3, 5, 4, 0, 1, 2],
[3, 5, 4, 0, 2, 1]]

def seed0InversePerms : Array Nat := #[0,
1,
2,
3,
4,
6,
5,
7]

def seed0NegPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
[0, 1, 2, 3, 4, 5, 6, 11, 12, 13, 14, 7, 8, 9, 10],
[0, 1, 3, 2, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13],
[0, 1, 3, 2, 4, 6, 5, 11, 12, 14, 13, 7, 8, 10, 9],
[0, 4, 7, 11, 1, 8, 12, 2, 5, 9, 13, 3, 6, 10, 14],
[0, 4, 11, 7, 1, 12, 8, 2, 5, 13, 9, 3, 6, 14, 10],
[0, 4, 7, 11, 1, 8, 12, 3, 6, 10, 14, 2, 5, 9, 13],
[0, 4, 11, 7, 1, 12, 8, 3, 6, 14, 10, 2, 5, 13, 9]]

def seed0PosPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48],
[0, 1, 2, 3, 4, 5, 6, 7, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48],
[1, 0, 2, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 13, 14, 17, 18, 15, 16, 19, 20, 22, 21, 23, 24, 25, 26, 29, 30, 27, 28, 31, 32, 33, 34, 37, 38, 35, 36, 39, 40, 41, 42, 45, 46, 43, 44, 47, 48],
[1, 0, 2, 3, 4, 6, 5, 7, 8, 22, 21, 23, 24, 25, 26, 29, 30, 27, 28, 31, 32, 10, 9, 11, 12, 13, 14, 17, 18, 15, 16, 19, 20, 33, 34, 37, 38, 35, 36, 39, 40, 41, 42, 45, 46, 43, 44, 47, 48],
[13, 25, 33, 41, 4, 14, 26, 34, 42, 15, 27, 35, 43, 0, 5, 9, 16, 21, 28, 36, 44, 17, 29, 37, 45, 1, 6, 10, 18, 22, 30, 38, 46, 2, 7, 11, 19, 23, 31, 39, 47, 3, 8, 12, 20, 24, 32, 40, 48],
[25, 13, 33, 41, 4, 26, 14, 34, 42, 27, 15, 35, 43, 0, 5, 21, 28, 9, 16, 36, 44, 29, 17, 37, 45, 1, 6, 22, 30, 10, 18, 38, 46, 2, 7, 23, 31, 11, 19, 39, 47, 3, 8, 24, 32, 12, 20, 40, 48],
[13, 25, 33, 41, 4, 14, 26, 34, 42, 17, 29, 37, 45, 1, 6, 10, 18, 22, 30, 38, 46, 15, 27, 35, 43, 0, 5, 9, 16, 21, 28, 36, 44, 2, 7, 11, 19, 23, 31, 39, 47, 3, 8, 12, 20, 24, 32, 40, 48],
[25, 13, 33, 41, 4, 26, 14, 34, 42, 29, 17, 37, 45, 1, 6, 22, 30, 10, 18, 38, 46, 27, 15, 35, 43, 0, 5, 21, 28, 9, 16, 36, 44, 2, 7, 23, 31, 11, 19, 39, 47, 3, 8, 24, 32, 12, 20, 40, 48]]

def seed0PairPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150],
[0, 1, 2, 3, 4, 5, 6, 7, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 63, 64, 61, 62, 65, 66, 67, 68, 69, 70, 71, 74, 75, 72, 73, 76, 77, 78, 79, 80, 81, 84, 85, 82, 83, 86, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118],
[1, 0, 2, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 13, 14, 17, 18, 15, 16, 19, 20, 22, 21, 23, 24, 25, 26, 29, 30, 27, 28, 31, 32, 33, 34, 37, 38, 35, 36, 39, 40, 41, 42, 45, 46, 43, 44, 47, 48, 50, 49, 51, 52, 54, 53, 55, 58, 59, 56, 57, 60, 61, 62, 63, 64, 65, 66, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 87, 88, 90, 89, 91, 93, 92, 94, 95, 96, 97, 98, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 119, 120, 122, 121, 123, 125, 124, 126, 127, 128, 129, 130, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140],
[1, 0, 2, 3, 4, 6, 5, 7, 8, 22, 21, 23, 24, 25, 26, 29, 30, 27, 28, 31, 32, 10, 9, 11, 12, 13, 14, 17, 18, 15, 16, 19, 20, 33, 34, 37, 38, 35, 36, 39, 40, 41, 42, 45, 46, 43, 44, 47, 48, 50, 49, 51, 52, 54, 53, 55, 58, 59, 56, 57, 60, 63, 64, 61, 62, 65, 66, 77, 78, 79, 80, 81, 84, 85, 82, 83, 86, 67, 68, 69, 70, 71, 74, 75, 72, 73, 76, 119, 120, 122, 121, 123, 125, 124, 126, 127, 128, 129, 130, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 87, 88, 90, 89, 91, 93, 92, 94, 95, 96, 97, 98, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108],
[13, 25, 33, 41, 4, 14, 26, 34, 42, 15, 27, 35, 43, 0, 5, 9, 16, 21, 28, 36, 44, 17, 29, 37, 45, 1, 6, 10, 18, 22, 30, 38, 46, 2, 7, 11, 19, 23, 31, 39, 47, 3, 8, 12, 20, 24, 32, 40, 48, 61, 63, 65, 60, 62, 64, 66, 87, 88, 119, 120, 52, 49, 53, 50, 54, 51, 55, 94, 96, 91, 95, 97, 89, 92, 90, 93, 98, 126, 128, 123, 127, 129, 121, 124, 122, 125, 130, 56, 57, 72, 74, 69, 73, 75, 67, 70, 68, 71, 76, 103, 105, 104, 106, 99, 101, 100, 102, 107, 108, 135, 137, 136, 138, 131, 133, 132, 134, 139, 140, 58, 59, 82, 84, 79, 83, 85, 77, 80, 78, 81, 86, 113, 115, 114, 116, 109, 111, 110, 112, 117, 118, 145, 147, 146, 148, 141, 143, 142, 144, 149, 150],
[25, 13, 33, 41, 4, 26, 14, 34, 42, 27, 15, 35, 43, 0, 5, 21, 28, 9, 16, 36, 44, 29, 17, 37, 45, 1, 6, 22, 30, 10, 18, 38, 46, 2, 7, 23, 31, 11, 19, 39, 47, 3, 8, 24, 32, 12, 20, 40, 48, 63, 61, 65, 60, 64, 62, 66, 119, 120, 87, 88, 52, 49, 53, 50, 54, 51, 55, 126, 128, 123, 127, 129, 121, 124, 122, 125, 130, 94, 96, 91, 95, 97, 89, 92, 90, 93, 98, 56, 57, 74, 72, 69, 75, 73, 67, 70, 68, 71, 76, 135, 137, 136, 138, 131, 133, 132, 134, 139, 140, 103, 105, 104, 106, 99, 101, 100, 102, 107, 108, 58, 59, 84, 82, 79, 85, 83, 77, 80, 78, 81, 86, 145, 147, 146, 148, 141, 143, 142, 144, 149, 150, 113, 115, 114, 116, 109, 111, 110, 112, 117, 118],
[13, 25, 33, 41, 4, 14, 26, 34, 42, 17, 29, 37, 45, 1, 6, 10, 18, 22, 30, 38, 46, 15, 27, 35, 43, 0, 5, 9, 16, 21, 28, 36, 44, 2, 7, 11, 19, 23, 31, 39, 47, 3, 8, 12, 20, 24, 32, 40, 48, 61, 63, 65, 60, 62, 64, 66, 87, 88, 119, 120, 52, 50, 54, 49, 53, 51, 55, 94, 96, 91, 95, 97, 90, 93, 89, 92, 98, 126, 128, 123, 127, 129, 122, 125, 121, 124, 130, 58, 59, 82, 84, 79, 83, 85, 77, 80, 78, 81, 86, 113, 115, 114, 116, 109, 111, 110, 112, 117, 118, 145, 147, 146, 148, 141, 143, 142, 144, 149, 150, 56, 57, 72, 74, 69, 73, 75, 67, 70, 68, 71, 76, 103, 105, 104, 106, 99, 101, 100, 102, 107, 108, 135, 137, 136, 138, 131, 133, 132, 134, 139, 140],
[25, 13, 33, 41, 4, 26, 14, 34, 42, 29, 17, 37, 45, 1, 6, 22, 30, 10, 18, 38, 46, 27, 15, 35, 43, 0, 5, 21, 28, 9, 16, 36, 44, 2, 7, 23, 31, 11, 19, 39, 47, 3, 8, 24, 32, 12, 20, 40, 48, 63, 61, 65, 60, 64, 62, 66, 119, 120, 87, 88, 52, 50, 54, 49, 53, 51, 55, 126, 128, 123, 127, 129, 122, 125, 121, 124, 130, 94, 96, 91, 95, 97, 90, 93, 89, 92, 98, 58, 59, 84, 82, 79, 85, 83, 77, 80, 78, 81, 86, 145, 147, 146, 148, 141, 143, 142, 144, 149, 150, 113, 115, 114, 116, 109, 111, 110, 112, 117, 118, 56, 57, 74, 72, 69, 75, 73, 67, 70, 68, 71, 76, 135, 137, 136, 138, 131, 133, 132, 134, 139, 140, 103, 105, 104, 106, 99, 101, 100, 102, 107, 108]]

end PEqualNP.Outside.L_meta_982_aux.Finite
namespace PEqualNP.Outside.L_meta_982_aux.Finite

def seed8K : Nat := 218

def seed8ScoreWidth : Nat := 10

def seed8NegativeRows : List Nat := [0, 1, 2, 4, 6, 8, 9, 12, 16, 17, 18, 24, 25, 32, 33, 34, 36, 38, 48, 49, 50, 64, 65, 66, 68, 70, 72, 73, 76]

def seed8PositiveRows : List Nat := [3, 5, 7, 10, 11, 13, 14, 15, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 35, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 71, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

def seed8Rows : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 6, 6, 6, 6, 8, 9, 9, 9, 9, 12, 12, 12, 12, 12, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 32, 33, 33, 33, 33, 33, 34, 34, 34, 34, 36, 36, 36, 36, 36, 38, 38, 38, 38, 38, 38, 38, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 49, 50, 50, 50, 50, 50, 50, 50, 64, 65, 65, 65, 65, 65, 66, 66, 66, 66, 66, 68, 68, 68, 68, 70, 70, 70, 70, 70, 70, 70, 72, 72, 72, 72, 73, 73, 73, 73, 73, 73, 73, 76, 76, 76, 76, 76, 76, 76, 3, 5, 7, 10, 11, 13, 14, 15, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 35, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 67, 69, 71, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 127, 127, 127, 3, 5, 7, 127, 127, 3, 10, 11, 127, 5, 10, 28, 44, 127, 127, 5, 20, 21, 127, 3, 20, 26, 82, 127, 26, 28, 40, 80, 127, 10, 20, 56, 57, 88, 89, 127, 127, 3, 37, 40, 97, 127, 10, 40, 42, 127, 20, 37, 44, 96, 127, 5, 40, 52, 54, 100, 102, 127, 80, 96, 112, 127, 5, 35, 41, 51, 57, 96, 127, 10, 19, 22, 51, 54, 80, 127, 127, 5, 67, 80, 97, 127, 10, 67, 82, 96, 127, 20, 80, 84, 127, 3, 74, 78, 80, 98, 102, 127, 40, 96, 104, 127, 3, 69, 77, 81, 89, 96, 127, 13, 14, 20, 40, 77, 78, 127]

def seed8Inputs : List Nat := [0xa37e20c4b7957e20ca37d108ee3bff5555555555556f555aaf556dc07f00000f807f00000fbf801e07808000000000000000000000000, 0xc5063bc5e5bf2a344363831ec65fdf999999999999bb999ccb9e7740000fe1f03f800fe0f00003e0003d0000000000000000000000000, 0xef1a326c23a9063ede2585297fb1efe1e1e1e1e1e1cde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000, 0xf75363446183522153e9fb7a47dd8ffe01fe01fe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000, 0x8962247d29fd63664621fdbf76918ffffe0001fffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000, 0x9183f84631b1fbbf7bbd994847118ffffffffe000001fffffe000000000000003fffffffffc0000000000000000000000000000000000, 0xe1fbbf77bdc183f86231e18c46118ffffffffffffffe00000000003fffffffffc00000000000000000000000000000000000000000000]

def seed8Mask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def seed8Goal : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000

def seed8Forbidden : List Nat := [0, seed8Mask] ++ seed8Inputs

def seed8Pool : List Nat := []

def seed8Words : Array Nat := #[0x204008002147c0088061000a82a7000000000000001555aaf556dc000000000007f00000fbf801e07808000000000000000000000000,
0xe000008022804069c04042139a06000000000000001e1ef0de7b9800000000000000fff00000000f83e0000000000000000000000000,
0x8000008003c600604001c3330800000000000000001fff001ffc000000000003ffff000003fffff00000000000000000000000000000,
0x1e044088423e7c079dce1e73b9ee7000000000000001ffffffffffc0000000003ffffffffffffffffffffffffffffffffffffffffffff,
0x4c000739484a0040044026b710c40000000000aaaa90000000aa923f80fffff04000000000007fe1f87f7ffffffffffffffffffffffff,
0x6e7c07b9ce4e0440844266b7b8ee7000000001fffffe000001ffffffffffffffc0000000003ffffffffffffffffffffffffffffffffff,
0x769ddb82d6029c99b9de0240896e700001fffe0001fe000ffe003fffffffffffc0000fffffc00000fffffffffffffffffffffffffffff,
0x8809c3b086881de2400048510000000aa00aa00aa0000a000028000000ffff07f80fffff04003e1003f7ffffffffffffffffffffffff,
0x8ac9cbb9e7caddeac160485b8227001fe01fe01fe0e01f00e07c1c0000fffffffffffffffc003ff003ffffffffffffffffffffffffff,
0x60f99f139c4081d8201060840000001e1ffffe1e1ffe00000000003fffffffffc00000000000000000000000000000000000000000000,
0xe99d339c4081d8201060840000001ffe1ffe1ffe3e0000000000007fffffffc00000000000000000000000000000000000000000000,
0x1881c43a084081cb34882ce11180002222222222220022211020803f80f01e004000f01f00407c01f8427ffffffffffffffffffffffff,
0x5c81df3b486a81df35c82ef711c400aaaaaaaaaaaa90aaa550aa923f80fffff07f80fffff0407fe1f87f7ffffffffffffffffffffffff,
0x7efddfbbce6e85dfb5ca6ef7b9ee70aaaaaaabfffffeaaa551ffffffffffffffff80fffff07ffffffffffffffffffffffffffffffffff,
0x5caddfbbde7eaddfbdde2ef7b9e670abfeabfeabfe9eabf55eafd3ff80ffffffffffffffffc07ffff87ffffffffffffffffffffffffff,
0x40e19f339c4081d820106084000000bebebebebebeb200000000003fffffffffc00000000000000000000000000000000000000000000,
0x60f99f33184081d820106084000000eeeeeeeeeeeed400000000003fffffffffc00000000000000000000000000000000000000000000,
0x7ef9df3b5a6ad5dfbddc7ef739e420eeeeeeeeeeeed4eee774eb9abffffffffffffffffffffffffffffffffffffffffffffffffffffff,
0x8102204421810220422181084611cf0101010101010901080904210000000000000000000000000000000000000000000000000000000,
0x81022044219522204221810846118f1110000111100111100114400000000000000000000000000000000000000000000000000000000,
0x81022044a58102204221810846118f1111111111112a00000000000000000000000000000000000000000000000000000000000000000,
0x810620c4a5952a2042238108c61bdf1111111111112b11188b14654000000000000000000000000000000000000000000000000000000,
0xa31a204423810620ca2581086e31ef4141414141414d414a0d45298000000000000000000000000000000000000000000000000000000,
0x81422044218142204221d10846118f540000015400015400015000000000000000000000003f800000000000000000000000000000000,
0xa3522044218152204221d10846198f54015401540161540aa1502c007f00000000000000003f800007800000000000000000000000000,
0x8102204431917a204a35910846118f55555554000001555aae00000000000000007f00000f80000000000000000000000000000000000,
0xa37e20c4b7957e20ca37d108ee3bff5555555555556f555aaf556dc07f00000f807f00000fbf801e07808000000000000000000000000,
0xbf7e60ccf7bf7e27dfffdf7bffffff5555555555556fffffffffffc07f00000fbffffffffffffffffffffffffffffffffffffffffffff,
0xc50623c4e5972a204363831ac65fdf991199119911bb991ccb9c774000000000000000000000000000000000000000000000000000000,
0x810638c4a5b52a3443238108c61bdf9999999911112b999ccb146540000000003f800fe0f000000000000000000000000000000000000,
0xc5063bc5e5bf2a344363831ec65fdf999999999999bb999ccb9e7740000fe1f03f800fe0f00003e0003d0000000000000000000000000,
0xe71a324423a90634ca2581086e31efc1c1c1c1c1c1cdc1ce0dc73980000fe00000000fe000000000003c0000000000000000000000000,
0xe7563bc5e5bf7a344363d31ec65fdfdd99dd99dd99fbdd9eebde7f407f0fe1f03f800fe0f03f83e007bd0000000000000000000000000,
0x8162204521bd62244221d11e66118fdddc0001dddc01ddd001df4000000000003fff0000003f83fe00000000000000000000000000000,
0xc5063bc5f5bf7a344b77931ec65fdfdddddddd9999bbdddeef9e7740000fe1f03fff0fe0ff8003e0003d0000000000000000000000000,
0xe17a3b45b58102304231c10c46118fddddddddddddfe0000000000007f0fe1ff800000000000000000000000000000000000000000000,
0xe77e3bc5f7bf7e34cb77d31eee7fffddddddddddddffdddeefdf7fc07f0fe1ffbfff0fe0ffbf83fe07bd8000000000000000000000000,
0xe7122244218102205221812847918fe001e001e001c1e00f01e0383f800000000000000000000000f8000000000000000000000000000,
0xe71a224423810620da2581286fb1efe141e141e141cde14f0de539bf800000000000000000000000f8000000000000000000000000000,
0x8902206c21a902264621852976918fe1e00001e1e001e1e001e7800000000000000000000000000000000000000000000000000000000,
0xa31a304423a1063eda2581086f31efe1e1e1e141414de1ef0d4529800000000000000fff0000000000000000000000000000000000000,
0xef1a326c23a9063ede2585297fb1efe1e1e1e1e1e1cde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000,
0xff1e72ec63bf7e3fdfef9f7bffffffe1e1e1e1e1e1cdffffffffffff800ffe003ffffffffffffffffffffffffffffffffffffffffffff,
0xef1e32eca7bd2e3ede278529ffbbfff1f1f1f1f1f1eff1ff8ff7fdff800ffe0000000fff00000000f83e0000000000000000000000000,
0xef5a326c23a9563ede25d5297fb9eff5e1f5e1f5e1edf5efadf7bdbfff0ffe0000000fff003f8000ffbe0000000000000000000000000,
0xef1a326c33b97e3ede3595297fb1eff5f5f5f5e1e1cdf5ffafe7b9bf800ffe00007f0fff0f800000f83e0000000000000000000000000,
0xef7e3bedf7bf7e3edf77d73ffffffffdfdfdfdfdfdfffdffefffffffff0fffffbfff0fffffbf83feffbf8000000000000000000000000,
0x910360442181522153a9994847118ffe01fe00000001fe0ff000000000000000000000000000000000000000000000000000000000000,
0xd50363446183522153e99b5a475d8ffe01fe019801b1fe0ff198360000000000000000000000000000000000000000000000000000000,
0xf75363446183522153e9fb7a47dd8ffe01fe01fe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000,
0xf75763c4e5977a2153ebfb7ac7dfdfff11ff11ff11fbff1ffbfc7f7ffff0000000000000003ffc00ffc00000000000000000000000000,
0x81622044219562204221f93a66918fff540001ff5401ff5001fd400000000000007f0000003ffc1e00000000000000000000000000000,
0xf77f63c4f7977e21dbfffb7aefffffff55ff55ff55ffff5ffffd7ffffff0000f807f00000fbffc1effc08000000000000000000000000,
0xff5b636c63ab5627dfedff7b7ffdefffe1ff41ffe1fdffeffdffbfbffff0000000000000003ffc00ffc00000000000000000000000000,
0x8162204421b563264221d90866118ffffe0001555401fff001554000000000003ffff000003f801e00000000000000000000000000000,
0x8162247529c103604221e18c46118ffffe0001fffe0000000000000000000000000000000000000000000000000000000000000000000,
0x8962247d29e903664621e5ad76918ffffe0001fffe01e1e001e7800000000000000000000000000000000000000000000000000000000,
0x8962247d29fd63664621fdbf76918ffffe0001fffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000,
0x9f6664fd6bff7f67dfeffffffffffffffe0001fffe01ffffffffffc0000000003ffffffffffffffffffffffffffffffffffffffffffff,
0x81eabc77bdc183f86231e18c46118ffffe01fffffe0e000000000000000fffffc00000000000000000000000000000000000000000000,
0x896624fdadfd6b664623fdbff69bdfffff1111ffff2bfff88bffe540000000003ffff000003fffff00000000000000000000000000000,
0xab7a247d2bfd6766ce25fdbf7eb1efffff4141ffff4dfffa0dffe980000000003ffff000003fffff00000000000000000000000000000,
0xab72247d29fd73664621fdbf76998fffff5401ffff61fffaa1ffec007f0000003ffff000003fffff07800000000000000000000000000,
0x8962247d39fd7b664e35fdbf76918fffff5555fffe01fffaafffc000000000003ffff0000fbfffff00000000000000000000000000000,
0xab7e24fdbffd7f66ce37fdbffebbffffff5555ffff6ffffaafffedc07f00000fbffff0000fbfffff07808000000000000000000000000,
0xcd62277d69ff63664761ffbf76dd8fffff9801ffffb1fffcc1fff600000000003ffff000003fffff00000000000000000000000000000,
0xef7e3ffdffff7f76cf77ffbffeffffffffddddfffffffffeefffffc07f0fe1ffbfffffe0ffbfffff07bd8000000000000000000000000,
0xef7a367d2be9077ede25e5ad7fb1efffffe1e1ffffcde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000,
0xdd63677d69ff736757e9ffff77dd8ffffffe01ffffb1fffff1fff600000000003ffff000003fffff00000000000000000000000000000,
0xff7f67fdffff7f67dfffffffffffffffffff55fffffffffffffffffffff0000fbffff0000fbfffffffc08000000000000000000000000,
0x8183b846318183b86231810846118ffffffffe00000000000000000000000000000000000000000000000000000000000000000000000,
0x9183f8463181d3b973b9994847118ffffffffe000001fe0ff000000000000000000000000000000000000000000000000000000000000,
0x9183f84631b1fbbf7bbd994847118ffffffffe000001fffffe000000000000003fffffffffc0000000000000000000000000000000000,
0x9187f8c6b5b5fbbf7bbf9948c71bdfffffffff11112bffffff146540000000003fffffffffc0000000000000000000000000000000000,
0xb39bf84633b1ffbffbbd99486f31efffffffff41414dffffff452980000000003fffffffffc0000000000000000000000000000000000,
0xb3fff8c6b7b5ffbffbbfd948ef3bffffffffff55556fffffff556dc07f00000fbfffffffffff801e07808000000000000000000000000,
0xd583fb4671b3fbbf7bfd9b5a475d8fffffffff9801b1ffffff983600000000003fffffffffc0000000000000000000000000000000000,
0xd587fbc7f5bffbbf7bff9b5ec75fdfffffffff9999bbffffff9e7740000fe1f03fffffffffc003e0003d0000000000000000000000000,
0xbb9bf86e33b9ffbfffbd9d697fb1efffffffffe1e14dffffffe7a980000000003fffffffffc0000000000000000000000000000000000,
0xf7d3fb467183d3b973f9fb7a47dd8ffffffffffe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000,
0x81e3bc7739c183f86231e18c46118ffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000,
0x91e3fc7739c1d3f973b9f9cc47118ffffffffffffe01fe0ff000000000000000000000000000000000000000000000000000000000000,
0x99e3fc7f39e9d3ff77b9fded77918ffffffffffffe01ffeff1e7800000000000000000000000000000000000000000000000000000000,
0x89e3bc7f39fde3fe6631fdbf76918ffffffffffffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000,
0x91e3fc7739f1fbff7bbdf9cc47118ffffffffffffe01fffffe000000000000003fffffffffc0000000000000000000000000000000000,
0x99e3fc7f39f9fbff7fbdfded77918ffffffffffffe01ffffffe78000000000003fffffffffc0000000000000000000000000000000000,
0x99e3fc7f39fdfbff7fbdfdff77918ffffffffffffe01ffffffffc000000000003fffffffffffffff00000000000000000000000000000,
0xa1fbbc77bdc183f86231e18c46118fffffffffffff6e0000000000007f00000f800000000000000000000000000000000000000000000,
0xe1fbbe7739c183f86231e18c46118fffffffffffffcc00000000003f800ffe00000000000000000000000000000000000000000000000,
0xeffbbe7f3be987fefe35e5ad7fb1efffffffffffffcde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000,
0xf7f3ff7779c3d3f973f9fbfe47dd8ffffffffffffff1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000,
0xe1fbbf77bdc183f86231e18c46118ffffffffffffffe00000000003fffffffffc00000000000000000000000000000000000000000000,
0xe7ffbff7ffc387f8e273e38cce7ffffffffffffffffe000000003fffffffffffc000000000000000fffffffffffffffffffffffffffff,
0xeffbbf7fbfc987f8e631e5ad7eb1effffffffffffffe000001e7b9bfffffffffc000000000000000f83e0000000000000000000000000,
0xe1fbbf77bdc183f86231e18c4611cfffffffffffffff01080904213fffffffffc00000000000000000000000000000000000000000000,
0xe1fbbf77bdd5a3f86231e18c46118fffffffffffffff11100114403fffffffffc00000000000000000000000000000000000000000000,
0xe1ffbff7bdd5abf86233e18cc61bdfffffffffffffff11188b14657fffffffffc00000000000000000000000000000000000000000000,
0xe3fbbf77bdc183f86231e18c46118fffffffffffffff400a0140283fffffffffc00000000000000000000000000000000000000000000,
0xe1fbbf77bdc183f86231e18c66118fffffffffffffff41400145003fffffffffc00000000000000000000000000000000000000000000,
0xe1fbbf77bdc183f86a35e18c46118fffffffffffffff414a0c00003fffffffffc00000000000000000000000000000000000000000000,
0xe3fbbf77bfc187f8ea35e18c6e31efffffffffffffff414a0d4529bfffffffffc00000000000000000000000000000000000000000000,
0xe3ffbff7bfd5fff8ea37f18cee3bffffffffffffffff555aaf556dffffffffffc07f00000fbf801e07808000000000000000000000000,
0xe1fbbf77bde983fc6231e18c46118fffffffffffffff81800186003fffffffffc00000000000000000000000000000000000000000000,
0xe5fbbf77fdc383f86371e39e465d8fffffffffffffff980cc198363fffffffffc00000000000000000000000000000000000000000000,
0xe5ffbff7fdd7abf86373e39ec65fdfffffffffffffff991ccb9c777fffffffffc00000000000000000000000000000000000000000000,
0xe5ffbff7fdffabfc6373e39ec65fdfffffffffffffff999ccb9e777fffffffffff800fe0f00003e0003d0000000000000000000000000,
0xe7ffbff7fffffffceb77f39eee7fffffffffffffffffdddeefdf7fffffffffffffff0fe0ffbf83fe07bd8000000000000000000000000,
0xe1fbbf77bdc183f86231e1ac46918fffffffffffffffe00001e0003fffffffffc00000000000000000000000000000000000000000000,
0xe7fbbf77bdc183f87231e1ac47918fffffffffffffffe00f01e0383fffffffffc000000000000000f8000000000000000000000000000,
0xe7fbbf77bfc187f8fa35e1ac6fb1efffffffffffffffe14f0de539bfffffffffc000000000000000f8000000000000000000000000000,
0xe1fbbf77bde183fe6231e18c46118fffffffffffffffe1e00000003fffffffffc00000000000000000000000000000000000000000000,
0xe9fbbf7fbde983fe6631e5ad76918fffffffffffffffe1e001e7803fffffffffc00000000000000000000000000000000000000000000,
0xeffbbf7fbde983fe7631e5ad77918fffffffffffffffe1ef01e7b83fffffffffc000000000000000f8000000000000000000000000000,
0xeffbbf7fbfe987fefe35e5ad7fb1efffffffffffffffe1ef0de7b9bfffffffffc0000fff00000000f83e0000000000000000000000000,
0xf1fbff77bdc1d3f973b9f9cc47118ffffffffffffffffe0ff000003fffffffffc00000000000000000000000000000000000000000000,
0xf5fbff77fdc3d3f973f9fbde475d8ffffffffffffffffe0ff198363fffffffffc00000000000000000000000000000000000000000000,
0xf7fbff77fdc3d3f973f9fbfe47dd8ffffffffffffffffe0ff1f83e3fffffffffc0000000003ffc00ffc00000000000000000000000000,
0xe9fbbf7fbdfde3fe6631fdbf76918ffffffffffffffffff001ffc03ffffffffffffff000003fffff00000000000000000000000000000]

def seed8StateIndices : Array (Array (List Nat)) := #[#[],
#[],
#[],
#[],
#[[82, 26, 30, 41, 49]],
#[[57, 72, 26, 30, 67, 79],
[56, 72, 26, 30, 41, 79],
[57, 81, 26, 30, 41, 49],
[85, 26, 30, 111, 41, 49],
[56, 71, 26, 30, 41, 49],
[57, 26, 78, 30, 91, 53],
[72, 26, 30, 68, 41, 115],
[57, 72, 26, 30, 89, 90]],
#[[59, 57, 72, 26, 30, 41, 49],
[57, 72, 26, 30, 41, 93, 49],
[57, 72, 26, 30, 111, 41, 49],
[57, 72, 26, 30, 88, 41, 49],
[39, 84, 26, 30, 91, 41, 49],
[80, 57, 72, 26, 30, 41, 49],
[72, 26, 30, 65, 91, 41, 116],
[84, 26, 64, 30, 91, 41, 49],
[57, 84, 26, 30, 41, 49, 116],
[80, 57, 47, 26, 30, 41, 49],
[57, 71, 26, 30, 41, 114, 49],
[83, 72, 26, 30, 91, 41, 79],
[60, 72, 26, 30, 91, 41, 50],
[26, 61, 74, 30, 91, 41, 49],
[57, 26, 30, 76, 103, 41, 49],
[57, 72, 26, 30, 98, 41, 49],
[57, 72, 26, 30, 94, 41, 49],
[60, 73, 26, 30, 91, 41, 49],
[57, 73, 26, 30, 96, 41, 49],
[57, 72, 26, 30, 110, 41, 49],
[57, 72, 26, 30, 102, 41, 49],
[57, 72, 26, 30, 97, 41, 49],
[57, 72, 26, 30, 95, 41, 49],
[57, 72, 26, 30, 107, 41, 49],
[57, 72, 26, 30, 99, 41, 49],
[9, 57, 72, 26, 30, 41, 49],
[15, 57, 72, 26, 30, 41, 49],
[16, 57, 72, 26, 30, 41, 49],
[80, 57, 26, 30, 77, 41, 49],
[57, 72, 26, 30, 108, 41, 49],
[57, 72, 26, 30, 100, 41, 49],
[72, 26, 30, 48, 68, 91, 41],
[56, 85, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 41, 115, 49],
[57, 72, 26, 30, 104, 41, 49],
[57, 72, 26, 30, 109, 41, 49],
[57, 72, 87, 26, 30, 41, 49],
[57, 72, 26, 30, 92, 41, 49],
[57, 72, 26, 30, 96, 41, 49],
[57, 72, 26, 30, 41, 112, 49],
[10, 57, 72, 26, 30, 41, 49]],
#[[8, 6, 72, 26, 30, 91, 41],
[5, 6, 26, 30, 91, 41, 49],
[3, 5, 57, 26, 30, 41, 49],
[57, 72, 58, 26, 30, 91, 41, 49],
[2, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 91, 41, 49, 42],
[1, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 27, 30, 91, 41, 49],
[0, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 117, 41, 113, 49],
[57, 72, 26, 30, 91, 41, 46, 49],
[57, 72, 26, 30, 91, 31, 41, 49],
[57, 72, 26, 30, 91, 41, 66, 49],
[33, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 91, 106, 41, 49],
[57, 72, 26, 30, 35, 91, 41, 49],
[11, 57, 72, 26, 30, 91, 41, 49],
[55, 70, 57, 72, 26, 30, 41, 49],
[55, 57, 72, 26, 30, 41, 49, 116],
[57, 72, 26, 30, 111, 41, 49],
[57, 72, 26, 30, 91, 41, 43, 49],
[39, 57, 72, 26, 30, 111, 41, 49],
[18, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 100, 41, 49],
[57, 60, 72, 26, 30, 91, 41, 49],
[57, 72, 22, 26, 30, 100, 41, 49],
[19, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 96, 41, 49],
[57, 72, 26, 30, 91, 96, 41, 49],
[21, 57, 72, 26, 30, 96, 41, 49],
[20, 57, 72, 26, 30, 91, 41, 49],
[17, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 41, 113, 49, 116],
[57, 72, 26, 30, 101, 41, 113, 49],
[80, 57, 72, 26, 30, 41, 49],
[57, 72, 26, 28, 30, 91, 41, 49],
[80, 57, 72, 86, 26, 30, 41, 49],
[57, 72, 26, 30, 91, 38, 41, 49],
[57, 72, 26, 30, 91, 41, 49, 69],
[51, 57, 72, 26, 30, 91, 41, 49],
[7, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 91, 32, 41, 49],
[57, 72, 26, 30, 91, 41, 44, 49],
[57, 72, 26, 62, 30, 91, 41, 49],
[23, 57, 72, 26, 30, 91, 41, 49],
[14, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 101, 105, 41, 49],
[29, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 40, 26, 30, 91, 41, 49],
[54, 57, 72, 26, 30, 91, 41, 49],
[4, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 34, 91, 41, 49],
[57, 72, 26, 30, 91, 41, 45, 49],
[57, 72, 26, 30, 108, 41, 49],
[57, 63, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 37, 108, 41, 49],
[13, 57, 72, 26, 30, 91, 41, 49]],
#[[3, 57, 72, 26, 30, 41, 49],
[12, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 91, 36, 41, 49],
[21, 57, 72, 26, 30, 91, 41, 49],
[57, 72, 26, 30, 91, 41, 49, 52],
[57, 72, 24, 26, 30, 91, 41, 49],
[57, 72, 26, 75, 30, 91, 41, 49],
[25, 57, 72, 26, 30, 91, 41, 49]],
#[[57, 72, 26, 30, 91, 41, 49]]]

def seed8AdviceData : Array (Array (Array Nat)) := #[#[],
#[],
#[],
#[],
#[#[]],
#[#[],
#[],
#[],
#[],
#[1080],
#[],
#[],
#[]],
#[#[],
#[],
#[],
#[],
#[5192],
#[],
#[],
#[70844],
#[132324],
#[132168,
69776],
#[199736],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[264444],
#[],
#[],
#[394432,
330992],
#[463944,
197760,
395480],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[]],
#[#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[9460],
#[70712],
#[132348],
#[],
#[141504],
#[206084],
#[],
#[],
#[],
#[],
#[328760,
269528,
266520],
#[525384,
399488,
466088,
592164],
#[529465,
658565,
267454,
464066],
#[341228],
#[919624,
728160,
792704,
856336],
#[988216,
1050696,
1049768,
989456],
#[],
#[],
#[920648,
1181776,
790672,
1116448],
#[1378376,
1442984,
1254616,
1317136],
#[400458,
397418],
#[],
#[1182776,
1180744,
857304,
854288],
#[1578040,
1574984,
1516760,
1513744],
#[1709116,
1706060,
1770668,
1647836,
1644820],
#[1840300,
1837340,
1901884],
#[1967356],
#[660538,
657482,
2040930,
1838185,
2037890,
1836177,
2104490,
593077,
2101466,
591085],
#[2235488,
2166888,
144496,
2229440,
2174192,
137512],
#[],
#[2294984,
1972536],
#[2369836,
2368828],
#[1913952],
#[2435200],
#[],
#[],
#[],
#[],
#[],
#[2491596],
#[1968200],
#[2492496,
2566288],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[2626620]],
#[#[134150,
132106,
7182,
4114,
70678,
67610],
#[342073,
407613,
472137,
537677,
210049,
275589,
473257,
538797,
211161,
276701,
341265,
406805],
#[1049622,
787626,
853166,
789682,
855222,
918730,
984270,
600305,
656641,
722181,
603425,
658745,
724285],
#[2032642,
1512504,
1573945,
1643578,
1705021,
1509448,
1576009,
1640522,
1707085,
1193066,
1190034,
1770664,
1836201,
1901738,
1967277,
1254616,
1311961,
1385690,
1443037,
1127669,
1251600,
1314065,
1382674,
1445141,
1124661],
#[2622494,
2110538,
2176082,
603249,
1194173,
1188070,
596210,
2103546,
2169090,
2491666,
2557206,
795930,
2432286,
658730,
2238764,
2369837,
2295086,
2497842,
2563382,
788794,
2426174],
#[2950154,
2819146,
2884686,
2759762,
1713238,
2688145,
1445013,
2825401,
2890941,
2753769,
1706221],
#[3277838,
2498658,
3212390,
2164873,
789657,
3081373,
3028153,
931009,
3157189,
3016929,
919793,
3146997,
2176289,
795945,
3091757],
#[3671042,
3478584,
3540025,
3609658,
2891837,
3343489,
1707141,
3419305,
1979565,
3409113,
1968349,
3353873,
1713429]],
#[#[5122,
73731,
2054,
76807,
13322,
66571,
10254,
68623,
1042,
77843,
9238,
69655,
6170,
72731,
272443,
337983,
264267,
329807,
394323,
459863,
396387,
461927,
267371,
332911,
132211,
197751,
141443,
206983,
144523,
210063,
395411,
460951,
398491,
464031,
137387,
202927,
399539,
465079,
133307,
198847,
265411,
330951,
268491,
334031,
402651,
468191,
140515,
206055,
263403,
328943,
136435,
201975,
271611,
337151,
397571,
463111]]]

def seed8States (s i : Nat) : List Nat := ((seed8StateIndices.getD s #[]).getD i []).map (fun j => seed8Words.getD j 0)

def seed8Count (s : Nat) : Nat := (seed8StateIndices.getD s #[]).size

def seed8Advice (s i : Nat) : Array Nat := (seed8AdviceData.getD s #[]).getD i #[]

def seed8Roots : List (Nat × Nat) := [(9, 0)]

def seed8VertexPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6],
[0, 2, 1, 4, 3, 6, 5],
[1, 0, 3, 2, 5, 4, 6],
[1, 3, 0, 5, 2, 6, 4],
[2, 0, 4, 1, 6, 3, 5],
[2, 4, 0, 6, 1, 5, 3],
[3, 1, 5, 0, 6, 2, 4],
[3, 5, 1, 6, 0, 4, 2],
[4, 2, 6, 0, 5, 1, 3],
[4, 6, 2, 5, 0, 3, 1],
[5, 3, 6, 1, 4, 0, 2],
[5, 6, 3, 4, 1, 2, 0],
[6, 4, 5, 2, 3, 0, 1],
[6, 5, 4, 3, 2, 1, 0]]

def seed8InversePerms : Array Nat := #[0,
1,
2,
4,
3,
5,
6,
8,
7,
9,
10,
12,
11,
13]

def seed8NegPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28],
[0, 1, 3, 2, 4, 8, 9, 10, 5, 6, 7, 11, 12, 21, 22, 24, 23, 25, 26, 27, 28, 13, 14, 16, 15, 17, 18, 19, 20],
[0, 2, 1, 5, 6, 3, 4, 7, 13, 15, 14, 16, 17, 8, 10, 9, 11, 12, 18, 20, 19, 21, 23, 22, 26, 27, 24, 25, 28],
[0, 3, 1, 8, 9, 2, 4, 10, 21, 24, 22, 23, 25, 5, 7, 6, 11, 12, 26, 28, 27, 13, 16, 14, 18, 19, 15, 17, 20],
[0, 2, 5, 1, 6, 13, 15, 14, 3, 4, 7, 16, 17, 21, 23, 26, 22, 27, 24, 25, 28, 8, 10, 11, 9, 12, 18, 20, 19],
[0, 3, 8, 1, 9, 21, 24, 22, 2, 4, 10, 23, 25, 13, 16, 18, 14, 19, 15, 17, 20, 5, 7, 11, 6, 12, 26, 28, 27],
[0, 5, 2, 13, 15, 1, 6, 14, 21, 26, 23, 22, 27, 3, 7, 4, 16, 17, 24, 28, 25, 8, 11, 10, 18, 20, 9, 12, 19],
[0, 8, 3, 21, 24, 1, 9, 22, 13, 18, 16, 14, 19, 2, 10, 4, 23, 25, 15, 20, 17, 5, 11, 7, 26, 28, 6, 12, 27],
[0, 5, 13, 2, 15, 21, 26, 23, 1, 6, 14, 22, 27, 8, 11, 18, 10, 20, 9, 12, 19, 3, 7, 16, 4, 17, 24, 28, 25],
[0, 8, 21, 3, 24, 13, 18, 16, 1, 9, 22, 14, 19, 5, 11, 26, 7, 28, 6, 12, 27, 2, 10, 23, 4, 25, 15, 20, 17],
[0, 13, 5, 21, 26, 2, 15, 23, 8, 18, 11, 10, 20, 1, 14, 6, 22, 27, 9, 19, 12, 3, 16, 7, 24, 28, 4, 17, 25],
[0, 21, 8, 13, 18, 3, 24, 16, 5, 26, 11, 7, 28, 1, 22, 9, 14, 19, 6, 27, 12, 2, 23, 10, 15, 20, 4, 25, 17],
[0, 13, 21, 5, 26, 8, 18, 11, 2, 15, 23, 10, 20, 3, 16, 24, 7, 28, 4, 17, 25, 1, 14, 22, 6, 27, 9, 19, 12],
[0, 21, 13, 8, 18, 5, 26, 11, 3, 24, 16, 7, 28, 2, 23, 15, 10, 20, 4, 25, 17, 1, 22, 14, 9, 19, 6, 27, 12]]

def seed8PosPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98],
[1, 0, 2, 9, 10, 8, 11, 12, 5, 3, 4, 6, 7, 15, 16, 13, 14, 17, 18, 44, 43, 45, 51, 52, 55, 56, 53, 54, 57, 58, 48, 46, 47, 49, 50, 59, 60, 63, 64, 61, 62, 65, 66, 20, 19, 21, 31, 32, 30, 33, 34, 22, 23, 26, 27, 24, 25, 28, 29, 35, 36, 39, 40, 37, 38, 41, 42, 67, 68, 71, 72, 69, 70, 73, 74, 83, 84, 87, 88, 85, 86, 89, 90, 75, 76, 79, 80, 77, 78, 81, 82, 91, 92, 95, 96, 93, 94, 97, 98],
[0, 3, 4, 1, 2, 6, 5, 7, 19, 22, 24, 23, 25, 20, 21, 26, 28, 27, 29, 8, 13, 14, 9, 11, 10, 12, 15, 17, 16, 18, 30, 35, 37, 36, 38, 31, 33, 32, 34, 39, 41, 40, 42, 43, 46, 47, 44, 45, 49, 48, 50, 67, 69, 68, 70, 75, 77, 76, 78, 71, 73, 72, 74, 79, 81, 80, 82, 51, 53, 52, 54, 59, 61, 60, 62, 55, 57, 56, 58, 63, 65, 64, 66, 83, 85, 84, 86, 91, 93, 92, 94, 87, 89, 88, 90, 95, 97, 96, 98],
[1, 9, 10, 0, 2, 11, 8, 12, 44, 51, 55, 52, 56, 43, 45, 53, 57, 54, 58, 5, 15, 16, 3, 6, 4, 7, 13, 17, 14, 18, 48, 59, 63, 60, 64, 46, 49, 47, 50, 61, 65, 62, 66, 20, 31, 32, 19, 21, 33, 30, 34, 67, 71, 68, 72, 83, 87, 84, 88, 69, 73, 70, 74, 85, 89, 86, 90, 22, 26, 23, 27, 35, 39, 36, 40, 24, 28, 25, 29, 37, 41, 38, 42, 75, 79, 76, 80, 91, 95, 92, 96, 77, 81, 78, 82, 93, 97, 94, 98],
[3, 0, 4, 22, 24, 19, 23, 25, 6, 1, 2, 5, 7, 26, 28, 20, 21, 27, 29, 46, 43, 47, 67, 69, 75, 77, 68, 70, 76, 78, 49, 44, 45, 48, 50, 71, 73, 79, 81, 72, 74, 80, 82, 13, 8, 14, 35, 37, 30, 36, 38, 9, 11, 15, 17, 10, 12, 16, 18, 31, 33, 39, 41, 32, 34, 40, 42, 51, 53, 59, 61, 52, 54, 60, 62, 83, 85, 91, 93, 84, 86, 92, 94, 55, 57, 63, 65, 56, 58, 64, 66, 87, 89, 95, 97, 88, 90, 96, 98],
[9, 1, 10, 51, 55, 44, 52, 56, 11, 0, 2, 8, 12, 53, 57, 43, 45, 54, 58, 31, 20, 32, 67, 71, 83, 87, 68, 72, 84, 88, 33, 19, 21, 30, 34, 69, 73, 85, 89, 70, 74, 86, 90, 15, 5, 16, 59, 63, 48, 60, 64, 3, 6, 13, 17, 4, 7, 14, 18, 46, 49, 61, 65, 47, 50, 62, 66, 22, 26, 35, 39, 23, 27, 36, 40, 75, 79, 91, 95, 76, 80, 92, 96, 24, 28, 37, 41, 25, 29, 38, 42, 77, 81, 93, 97, 78, 82, 94, 98],
[3, 22, 24, 0, 4, 23, 19, 25, 46, 67, 75, 69, 77, 43, 47, 68, 76, 70, 78, 6, 26, 28, 1, 5, 2, 7, 20, 27, 21, 29, 49, 71, 79, 73, 81, 44, 48, 45, 50, 72, 80, 74, 82, 13, 35, 37, 8, 14, 36, 30, 38, 51, 59, 53, 61, 83, 91, 85, 93, 52, 60, 54, 62, 84, 92, 86, 94, 9, 15, 11, 17, 31, 39, 33, 41, 10, 16, 12, 18, 32, 40, 34, 42, 55, 63, 57, 65, 87, 95, 89, 97, 56, 64, 58, 66, 88, 96, 90, 98],
[9, 51, 55, 1, 10, 52, 44, 56, 31, 67, 83, 71, 87, 20, 32, 68, 84, 72, 88, 11, 53, 57, 0, 8, 2, 12, 43, 54, 45, 58, 33, 69, 85, 73, 89, 19, 30, 21, 34, 70, 86, 74, 90, 15, 59, 63, 5, 16, 60, 48, 64, 22, 35, 26, 39, 75, 91, 79, 95, 23, 36, 27, 40, 76, 92, 80, 96, 3, 13, 6, 17, 46, 61, 49, 65, 4, 14, 7, 18, 47, 62, 50, 66, 24, 37, 28, 41, 77, 93, 81, 97, 25, 38, 29, 42, 78, 94, 82, 98],
[22, 3, 24, 67, 75, 46, 69, 77, 23, 0, 4, 19, 25, 68, 76, 43, 47, 70, 78, 35, 13, 37, 51, 59, 83, 91, 53, 61, 85, 93, 36, 8, 14, 30, 38, 52, 60, 84, 92, 54, 62, 86, 94, 26, 6, 28, 71, 79, 49, 73, 81, 1, 5, 20, 27, 2, 7, 21, 29, 44, 48, 72, 80, 45, 50, 74, 82, 9, 15, 31, 39, 11, 17, 33, 41, 55, 63, 87, 95, 57, 65, 89, 97, 10, 16, 32, 40, 12, 18, 34, 42, 56, 64, 88, 96, 58, 66, 90, 98],
[51, 9, 55, 67, 83, 31, 71, 87, 52, 1, 10, 44, 56, 68, 84, 20, 32, 72, 88, 59, 15, 63, 22, 35, 75, 91, 26, 39, 79, 95, 60, 5, 16, 48, 64, 23, 36, 76, 92, 27, 40, 80, 96, 53, 11, 57, 69, 85, 33, 73, 89, 0, 8, 43, 54, 2, 12, 45, 58, 19, 30, 70, 86, 21, 34, 74, 90, 3, 13, 46, 61, 6, 17, 49, 65, 24, 37, 77, 93, 28, 41, 81, 97, 4, 14, 47, 62, 7, 18, 50, 66, 25, 38, 78, 94, 29, 42, 82, 98],
[22, 67, 75, 3, 24, 69, 46, 77, 35, 51, 83, 59, 91, 13, 37, 53, 85, 61, 93, 23, 68, 76, 0, 19, 4, 25, 43, 70, 47, 78, 36, 52, 84, 60, 92, 8, 30, 14, 38, 54, 86, 62, 94, 26, 71, 79, 6, 28, 73, 49, 81, 9, 31, 15, 39, 55, 87, 63, 95, 11, 33, 17, 41, 57, 89, 65, 97, 1, 20, 5, 27, 44, 72, 48, 80, 2, 21, 7, 29, 45, 74, 50, 82, 10, 32, 16, 40, 56, 88, 64, 96, 12, 34, 18, 42, 58, 90, 66, 98],
[51, 67, 83, 9, 55, 71, 31, 87, 59, 22, 75, 35, 91, 15, 63, 26, 79, 39, 95, 52, 68, 84, 1, 44, 10, 56, 20, 72, 32, 88, 60, 23, 76, 36, 92, 5, 48, 16, 64, 27, 80, 40, 96, 53, 69, 85, 11, 57, 73, 33, 89, 3, 46, 13, 61, 24, 77, 37, 93, 6, 49, 17, 65, 28, 81, 41, 97, 0, 43, 8, 54, 19, 70, 30, 86, 2, 45, 12, 58, 21, 74, 34, 90, 4, 47, 14, 62, 25, 78, 38, 94, 7, 50, 18, 66, 29, 82, 42, 98],
[67, 22, 75, 51, 83, 35, 59, 91, 69, 3, 24, 46, 77, 53, 85, 13, 37, 61, 93, 71, 26, 79, 9, 31, 55, 87, 15, 39, 63, 95, 73, 6, 28, 49, 81, 11, 33, 57, 89, 17, 41, 65, 97, 68, 23, 76, 52, 84, 36, 60, 92, 0, 19, 43, 70, 4, 25, 47, 78, 8, 30, 54, 86, 14, 38, 62, 94, 1, 20, 44, 72, 5, 27, 48, 80, 10, 32, 56, 88, 16, 40, 64, 96, 2, 21, 45, 74, 7, 29, 50, 82, 12, 34, 58, 90, 18, 42, 66, 98],
[67, 51, 83, 22, 75, 59, 35, 91, 71, 9, 55, 31, 87, 26, 79, 15, 63, 39, 95, 69, 53, 85, 3, 46, 24, 77, 13, 61, 37, 93, 73, 11, 57, 33, 89, 6, 49, 28, 81, 17, 65, 41, 97, 68, 52, 84, 23, 76, 60, 36, 92, 1, 44, 20, 72, 10, 56, 32, 88, 5, 48, 27, 80, 16, 64, 40, 96, 0, 43, 19, 70, 8, 54, 30, 86, 4, 47, 25, 78, 14, 62, 38, 94, 2, 45, 21, 74, 12, 58, 34, 90, 7, 50, 29, 82, 18, 66, 42, 98]]

def seed8PairPerms : Array (List Nat) := #[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217],
[1, 0, 2, 9, 10, 8, 11, 12, 5, 3, 4, 6, 7, 15, 16, 13, 14, 17, 18, 44, 43, 45, 51, 52, 55, 56, 53, 54, 57, 58, 48, 46, 47, 49, 50, 59, 60, 63, 64, 61, 62, 65, 66, 20, 19, 21, 31, 32, 30, 33, 34, 22, 23, 26, 27, 24, 25, 28, 29, 35, 36, 39, 40, 37, 38, 41, 42, 67, 68, 71, 72, 69, 70, 73, 74, 83, 84, 87, 88, 85, 86, 89, 90, 75, 76, 79, 80, 77, 78, 81, 82, 91, 92, 95, 96, 93, 94, 97, 98, 99, 101, 100, 103, 102, 104, 105, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 127, 126, 129, 128, 130, 132, 131, 135, 136, 133, 134, 137, 178, 179, 180, 181, 182, 183, 189, 190, 191, 192, 184, 185, 186, 187, 188, 193, 196, 194, 195, 197, 198, 199, 200, 201, 202, 203, 204, 205, 207, 206, 208, 209, 210, 213, 211, 212, 215, 216, 214, 217, 138, 139, 140, 141, 142, 143, 148, 149, 150, 151, 152, 144, 145, 146, 147, 153, 155, 156, 154, 157, 158, 159, 160, 161, 162, 163, 164, 165, 167, 166, 168, 169, 170, 172, 173, 171, 176, 174, 175, 177],
[0, 3, 4, 1, 2, 6, 5, 7, 19, 22, 24, 23, 25, 20, 21, 26, 28, 27, 29, 8, 13, 14, 9, 11, 10, 12, 15, 17, 16, 18, 30, 35, 37, 36, 38, 31, 33, 32, 34, 39, 41, 40, 42, 43, 46, 47, 44, 45, 49, 48, 50, 67, 69, 68, 70, 75, 77, 76, 78, 71, 73, 72, 74, 79, 81, 80, 82, 51, 53, 52, 54, 59, 61, 60, 62, 55, 57, 56, 58, 63, 65, 64, 66, 83, 85, 84, 86, 91, 93, 92, 94, 87, 89, 88, 90, 95, 97, 96, 98, 100, 99, 106, 107, 108, 109, 110, 101, 102, 103, 104, 105, 112, 111, 114, 113, 115, 138, 144, 145, 146, 147, 139, 141, 140, 142, 143, 149, 150, 148, 151, 152, 153, 154, 155, 156, 157, 158, 159, 116, 121, 123, 122, 124, 125, 117, 118, 119, 120, 128, 126, 127, 129, 130, 131, 132, 133, 134, 135, 136, 137, 161, 160, 162, 163, 171, 172, 173, 174, 175, 176, 177, 164, 165, 166, 167, 168, 169, 170, 178, 184, 185, 187, 186, 188, 179, 180, 182, 181, 183, 200, 201, 202, 203, 204, 205, 206, 209, 207, 208, 210, 189, 190, 191, 192, 193, 194, 195, 197, 198, 196, 199, 212, 211, 214, 213, 216, 215, 217],
[1, 9, 10, 0, 2, 11, 8, 12, 44, 51, 55, 52, 56, 43, 45, 53, 57, 54, 58, 5, 15, 16, 3, 6, 4, 7, 13, 17, 14, 18, 48, 59, 63, 60, 64, 46, 49, 47, 50, 61, 65, 62, 66, 20, 31, 32, 19, 21, 33, 30, 34, 67, 71, 68, 72, 83, 87, 84, 88, 69, 73, 70, 74, 85, 89, 86, 90, 22, 26, 23, 27, 35, 39, 36, 40, 24, 28, 25, 29, 37, 41, 38, 42, 75, 79, 76, 80, 91, 95, 92, 96, 77, 81, 78, 82, 93, 97, 94, 98, 101, 99, 116, 117, 118, 119, 120, 100, 103, 102, 104, 105, 122, 121, 124, 123, 125, 178, 189, 190, 191, 192, 179, 181, 180, 182, 183, 185, 186, 184, 187, 188, 193, 196, 194, 195, 197, 198, 199, 106, 111, 113, 112, 114, 115, 107, 108, 109, 110, 129, 127, 126, 128, 130, 132, 131, 135, 136, 133, 134, 137, 201, 200, 202, 203, 213, 211, 212, 215, 216, 214, 217, 204, 205, 207, 206, 208, 209, 210, 138, 148, 149, 151, 150, 152, 139, 140, 142, 141, 143, 160, 161, 162, 163, 164, 165, 167, 169, 166, 168, 170, 144, 145, 146, 147, 153, 155, 156, 157, 158, 154, 159, 173, 172, 176, 171, 175, 174, 177],
[3, 0, 4, 22, 24, 19, 23, 25, 6, 1, 2, 5, 7, 26, 28, 20, 21, 27, 29, 46, 43, 47, 67, 69, 75, 77, 68, 70, 76, 78, 49, 44, 45, 48, 50, 71, 73, 79, 81, 72, 74, 80, 82, 13, 8, 14, 35, 37, 30, 36, 38, 9, 11, 15, 17, 10, 12, 16, 18, 31, 33, 39, 41, 32, 34, 40, 42, 51, 53, 59, 61, 52, 54, 60, 62, 83, 85, 91, 93, 84, 86, 92, 94, 55, 57, 63, 65, 56, 58, 64, 66, 87, 89, 95, 97, 88, 90, 96, 98, 100, 106, 99, 108, 107, 109, 110, 138, 144, 145, 146, 147, 139, 141, 140, 142, 143, 101, 102, 103, 104, 105, 112, 111, 114, 113, 115, 150, 149, 151, 148, 152, 154, 153, 157, 158, 155, 156, 159, 178, 184, 185, 187, 186, 188, 200, 201, 202, 203, 179, 180, 182, 181, 183, 204, 209, 205, 206, 207, 208, 210, 189, 190, 191, 192, 193, 194, 197, 195, 198, 196, 199, 214, 212, 211, 216, 215, 213, 217, 116, 121, 123, 122, 124, 125, 128, 126, 127, 129, 130, 117, 118, 119, 120, 131, 133, 134, 132, 135, 136, 137, 161, 160, 162, 163, 171, 172, 174, 173, 175, 176, 177, 165, 166, 164, 169, 167, 168, 170],
[9, 1, 10, 51, 55, 44, 52, 56, 11, 0, 2, 8, 12, 53, 57, 43, 45, 54, 58, 31, 20, 32, 67, 71, 83, 87, 68, 72, 84, 88, 33, 19, 21, 30, 34, 69, 73, 85, 89, 70, 74, 86, 90, 15, 5, 16, 59, 63, 48, 60, 64, 3, 6, 13, 17, 4, 7, 14, 18, 46, 49, 61, 65, 47, 50, 62, 66, 22, 26, 35, 39, 23, 27, 36, 40, 75, 79, 91, 95, 76, 80, 92, 96, 24, 28, 37, 41, 25, 29, 38, 42, 77, 81, 93, 97, 78, 82, 94, 98, 101, 116, 99, 118, 117, 119, 120, 178, 189, 190, 191, 192, 179, 181, 180, 182, 183, 100, 103, 102, 104, 105, 122, 121, 124, 123, 125, 186, 185, 187, 184, 188, 196, 193, 197, 198, 194, 195, 199, 138, 148, 149, 151, 150, 152, 160, 161, 162, 163, 139, 140, 142, 141, 143, 164, 169, 165, 167, 166, 168, 170, 144, 145, 146, 147, 153, 155, 157, 156, 158, 154, 159, 176, 173, 172, 175, 174, 171, 177, 106, 111, 113, 112, 114, 115, 129, 127, 126, 128, 130, 107, 108, 109, 110, 132, 135, 136, 131, 133, 134, 137, 201, 200, 202, 203, 213, 211, 215, 212, 216, 214, 217, 205, 207, 204, 209, 206, 208, 210],
[3, 22, 24, 0, 4, 23, 19, 25, 46, 67, 75, 69, 77, 43, 47, 68, 76, 70, 78, 6, 26, 28, 1, 5, 2, 7, 20, 27, 21, 29, 49, 71, 79, 73, 81, 44, 48, 45, 50, 72, 80, 74, 82, 13, 35, 37, 8, 14, 36, 30, 38, 51, 59, 53, 61, 83, 91, 85, 93, 52, 60, 54, 62, 84, 92, 86, 94, 9, 15, 11, 17, 31, 39, 33, 41, 10, 16, 12, 18, 32, 40, 34, 42, 55, 63, 57, 65, 87, 95, 89, 97, 56, 64, 58, 66, 88, 96, 90, 98, 106, 100, 138, 144, 145, 146, 147, 99, 108, 107, 109, 110, 141, 139, 142, 140, 143, 178, 200, 201, 202, 203, 184, 187, 185, 186, 188, 180, 182, 179, 181, 183, 204, 209, 205, 206, 207, 208, 210, 101, 112, 114, 111, 113, 115, 102, 103, 104, 105, 151, 150, 149, 148, 152, 154, 153, 157, 158, 155, 156, 159, 190, 189, 191, 192, 214, 212, 211, 216, 215, 213, 217, 193, 194, 197, 195, 198, 196, 199, 116, 128, 126, 129, 127, 130, 121, 123, 124, 122, 125, 161, 160, 162, 163, 171, 172, 174, 176, 173, 175, 177, 117, 118, 119, 120, 131, 133, 134, 135, 136, 132, 137, 166, 165, 169, 164, 168, 167, 170],
[9, 51, 55, 1, 10, 52, 44, 56, 31, 67, 83, 71, 87, 20, 32, 68, 84, 72, 88, 11, 53, 57, 0, 8, 2, 12, 43, 54, 45, 58, 33, 69, 85, 73, 89, 19, 30, 21, 34, 70, 86, 74, 90, 15, 59, 63, 5, 16, 60, 48, 64, 22, 35, 26, 39, 75, 91, 79, 95, 23, 36, 27, 40, 76, 92, 80, 96, 3, 13, 6, 17, 46, 61, 49, 65, 4, 14, 7, 18, 47, 62, 50, 66, 24, 37, 28, 41, 77, 93, 81, 97, 25, 38, 29, 42, 78, 94, 82, 98, 116, 101, 178, 189, 190, 191, 192, 99, 118, 117, 119, 120, 181, 179, 182, 180, 183, 138, 160, 161, 162, 163, 148, 151, 149, 150, 152, 140, 142, 139, 141, 143, 164, 169, 165, 167, 166, 168, 170, 100, 122, 124, 121, 123, 125, 103, 102, 104, 105, 187, 186, 185, 184, 188, 196, 193, 197, 198, 194, 195, 199, 145, 144, 146, 147, 176, 173, 172, 175, 174, 171, 177, 153, 155, 157, 156, 158, 154, 159, 106, 129, 127, 128, 126, 130, 111, 113, 114, 112, 115, 201, 200, 202, 203, 213, 211, 215, 214, 212, 216, 217, 107, 108, 109, 110, 132, 135, 136, 133, 134, 131, 137, 207, 205, 209, 204, 208, 206, 210],
[22, 3, 24, 67, 75, 46, 69, 77, 23, 0, 4, 19, 25, 68, 76, 43, 47, 70, 78, 35, 13, 37, 51, 59, 83, 91, 53, 61, 85, 93, 36, 8, 14, 30, 38, 52, 60, 84, 92, 54, 62, 86, 94, 26, 6, 28, 71, 79, 49, 73, 81, 1, 5, 20, 27, 2, 7, 21, 29, 44, 48, 72, 80, 45, 50, 74, 82, 9, 15, 31, 39, 11, 17, 33, 41, 55, 63, 87, 95, 57, 65, 89, 97, 10, 16, 32, 40, 12, 18, 34, 42, 56, 64, 88, 96, 58, 66, 90, 98, 106, 138, 100, 145, 144, 146, 147, 178, 200, 201, 202, 203, 184, 187, 185, 186, 188, 99, 108, 107, 109, 110, 141, 139, 142, 140, 143, 182, 180, 181, 179, 183, 209, 204, 207, 208, 205, 206, 210, 116, 128, 126, 129, 127, 130, 161, 160, 162, 163, 121, 123, 124, 122, 125, 171, 176, 172, 174, 173, 175, 177, 117, 118, 119, 120, 131, 133, 135, 134, 136, 132, 137, 169, 166, 165, 168, 167, 164, 170, 101, 112, 114, 111, 113, 115, 151, 150, 149, 148, 152, 102, 103, 104, 105, 154, 157, 158, 153, 155, 156, 159, 190, 189, 191, 192, 214, 212, 216, 211, 215, 213, 217, 194, 197, 193, 196, 195, 198, 199],
[51, 9, 55, 67, 83, 31, 71, 87, 52, 1, 10, 44, 56, 68, 84, 20, 32, 72, 88, 59, 15, 63, 22, 35, 75, 91, 26, 39, 79, 95, 60, 5, 16, 48, 64, 23, 36, 76, 92, 27, 40, 80, 96, 53, 11, 57, 69, 85, 33, 73, 89, 0, 8, 43, 54, 2, 12, 45, 58, 19, 30, 70, 86, 21, 34, 74, 90, 3, 13, 46, 61, 6, 17, 49, 65, 24, 37, 77, 93, 28, 41, 81, 97, 4, 14, 47, 62, 7, 18, 50, 66, 25, 38, 78, 94, 29, 42, 82, 98, 116, 178, 101, 190, 189, 191, 192, 138, 160, 161, 162, 163, 148, 151, 149, 150, 152, 99, 118, 117, 119, 120, 181, 179, 182, 180, 183, 142, 140, 141, 139, 143, 169, 164, 166, 168, 165, 167, 170, 106, 129, 127, 128, 126, 130, 201, 200, 202, 203, 111, 113, 114, 112, 115, 213, 214, 211, 215, 212, 216, 217, 107, 108, 109, 110, 132, 135, 133, 136, 134, 131, 137, 209, 207, 205, 208, 206, 204, 210, 100, 122, 124, 121, 123, 125, 187, 186, 185, 184, 188, 103, 102, 104, 105, 196, 197, 198, 193, 194, 195, 199, 145, 144, 146, 147, 176, 173, 175, 172, 174, 171, 177, 155, 157, 153, 154, 156, 158, 159],
[22, 67, 75, 3, 24, 69, 46, 77, 35, 51, 83, 59, 91, 13, 37, 53, 85, 61, 93, 23, 68, 76, 0, 19, 4, 25, 43, 70, 47, 78, 36, 52, 84, 60, 92, 8, 30, 14, 38, 54, 86, 62, 94, 26, 71, 79, 6, 28, 73, 49, 81, 9, 31, 15, 39, 55, 87, 63, 95, 11, 33, 17, 41, 57, 89, 65, 97, 1, 20, 5, 27, 44, 72, 48, 80, 2, 21, 7, 29, 45, 74, 50, 82, 10, 32, 16, 40, 56, 88, 64, 96, 12, 34, 18, 42, 58, 90, 66, 98, 138, 106, 178, 200, 201, 202, 203, 100, 145, 144, 146, 147, 187, 184, 186, 185, 188, 116, 161, 160, 162, 163, 128, 129, 126, 127, 130, 123, 124, 121, 122, 125, 171, 176, 172, 174, 173, 175, 177, 99, 141, 142, 139, 140, 143, 108, 107, 109, 110, 181, 182, 180, 179, 183, 209, 204, 207, 208, 205, 206, 210, 118, 117, 119, 120, 169, 166, 165, 168, 167, 164, 170, 131, 133, 135, 134, 136, 132, 137, 101, 151, 150, 148, 149, 152, 112, 114, 113, 111, 115, 190, 189, 191, 192, 214, 212, 216, 213, 211, 215, 217, 102, 103, 104, 105, 154, 157, 158, 155, 156, 153, 159, 197, 194, 196, 193, 198, 195, 199],
[51, 67, 83, 9, 55, 71, 31, 87, 59, 22, 75, 35, 91, 15, 63, 26, 79, 39, 95, 52, 68, 84, 1, 44, 10, 56, 20, 72, 32, 88, 60, 23, 76, 36, 92, 5, 48, 16, 64, 27, 80, 40, 96, 53, 69, 85, 11, 57, 73, 33, 89, 3, 46, 13, 61, 24, 77, 37, 93, 6, 49, 17, 65, 28, 81, 41, 97, 0, 43, 8, 54, 19, 70, 30, 86, 2, 45, 12, 58, 21, 74, 34, 90, 4, 47, 14, 62, 25, 78, 38, 94, 7, 50, 18, 66, 29, 82, 42, 98, 178, 116, 138, 160, 161, 162, 163, 101, 190, 189, 191, 192, 151, 148, 150, 149, 152, 106, 201, 200, 202, 203, 129, 128, 127, 126, 130, 113, 114, 111, 112, 115, 213, 214, 211, 215, 212, 216, 217, 99, 181, 182, 179, 180, 183, 118, 117, 119, 120, 141, 142, 140, 139, 143, 169, 164, 166, 168, 165, 167, 170, 108, 107, 109, 110, 209, 207, 205, 208, 206, 204, 210, 132, 135, 133, 136, 134, 131, 137, 100, 187, 186, 184, 185, 188, 122, 124, 123, 121, 125, 145, 144, 146, 147, 176, 173, 175, 171, 172, 174, 177, 103, 102, 104, 105, 196, 197, 198, 194, 195, 193, 199, 157, 155, 154, 153, 158, 156, 159],
[67, 22, 75, 51, 83, 35, 59, 91, 69, 3, 24, 46, 77, 53, 85, 13, 37, 61, 93, 71, 26, 79, 9, 31, 55, 87, 15, 39, 63, 95, 73, 6, 28, 49, 81, 11, 33, 57, 89, 17, 41, 65, 97, 68, 23, 76, 52, 84, 36, 60, 92, 0, 19, 43, 70, 4, 25, 47, 78, 8, 30, 54, 86, 14, 38, 62, 94, 1, 20, 44, 72, 5, 27, 48, 80, 10, 32, 56, 88, 16, 40, 64, 96, 2, 21, 45, 74, 7, 29, 50, 82, 12, 34, 58, 90, 18, 42, 66, 98, 138, 178, 106, 201, 200, 202, 203, 116, 161, 160, 162, 163, 128, 129, 126, 127, 130, 100, 145, 144, 146, 147, 187, 184, 186, 185, 188, 124, 123, 122, 121, 125, 176, 171, 173, 175, 172, 174, 177, 101, 151, 150, 148, 149, 152, 190, 189, 191, 192, 112, 114, 113, 111, 115, 214, 213, 212, 216, 211, 215, 217, 102, 103, 104, 105, 154, 157, 155, 158, 156, 153, 159, 196, 197, 194, 198, 195, 193, 199, 99, 141, 142, 139, 140, 143, 181, 182, 180, 179, 183, 108, 107, 109, 110, 209, 207, 208, 204, 205, 206, 210, 118, 117, 119, 120, 169, 166, 168, 165, 167, 164, 170, 133, 135, 131, 132, 134, 136, 137],
[67, 51, 83, 22, 75, 59, 35, 91, 71, 9, 55, 31, 87, 26, 79, 15, 63, 39, 95, 69, 53, 85, 3, 46, 24, 77, 13, 61, 37, 93, 73, 11, 57, 33, 89, 6, 49, 28, 81, 17, 65, 41, 97, 68, 52, 84, 23, 76, 60, 36, 92, 1, 44, 20, 72, 10, 56, 32, 88, 5, 48, 27, 80, 16, 64, 40, 96, 0, 43, 19, 70, 8, 54, 30, 86, 4, 47, 25, 78, 14, 62, 38, 94, 2, 45, 21, 74, 12, 58, 34, 90, 7, 50, 29, 82, 18, 66, 42, 98, 178, 138, 116, 161, 160, 162, 163, 106, 201, 200, 202, 203, 129, 128, 127, 126, 130, 101, 190, 189, 191, 192, 151, 148, 150, 149, 152, 114, 113, 112, 111, 115, 214, 213, 212, 216, 211, 215, 217, 100, 187, 186, 184, 185, 188, 145, 144, 146, 147, 122, 124, 123, 121, 125, 176, 171, 173, 175, 172, 174, 177, 103, 102, 104, 105, 196, 197, 194, 198, 195, 193, 199, 154, 157, 155, 158, 156, 153, 159, 99, 181, 182, 179, 180, 183, 141, 142, 140, 139, 143, 118, 117, 119, 120, 169, 166, 168, 164, 165, 167, 170, 108, 107, 109, 110, 209, 207, 208, 205, 206, 204, 210, 135, 133, 132, 131, 136, 134, 137]]

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
