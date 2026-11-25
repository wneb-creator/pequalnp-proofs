import PEqualNP.Defs

-- The simplifier and its semantic/count invariants are copied from checked L_meta_5026,
-- with only the surrounding namespace changed. That infrastructure credits the checked
-- L_meta_3620/L_meta_1549 development. The two-drop control theorem below is new.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.Pilot110TwoDrop
namespace CircuitProof

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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool ℕ

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
    (hv : ∀ s ∈ ins, Stat.Valid w.length s) :
    Stat.Valid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, Stat.Valid m s → Stat.Valid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, Stat.Valid w.length s →
    Stat.val (w ++ t) s = Stat.val w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    show Stat.Valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, Stat.Valid m s) :
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


theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


end CircuitProof

namespace Restrict

open CircuitProof

-- Restricting inputs of a circuit with the simplifier of the first part.
-- The start state sends every old input to a constant or to an input of the new circuit.

theorem elim_snoc (n : ℕ) (A : List Gate) (g : Gate) (acc : List Stat × List Gate) :
    elim n (A ++ [g]) acc = elimStep n (elim n A acc) g := by
  simp [elim, List.foldl_append]

theorem elim_stats_length (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih]
    simp [elimStep]
    omega

theorem inv_start {n n' : ℕ} (s0 : Fin n → Stat) (hv : ∀ i, Stat.Valid n' (s0 i))
    (y : Fin n' → Bool) :
    Inv n' (List.ofFn y) (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)) (List.ofFn s0, []) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hlt : i < n
  · have h1 : (List.ofFn s0).getD i (Sum.inl false) = s0 ⟨i, hlt⟩ :=
      getD_ofFn n s0 _ ⟨i, hlt⟩
    have h2 : (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)).getD i false
        = Stat.val (List.ofFn y) (s0 ⟨i, hlt⟩) :=
      getD_ofFn n (fun i => Stat.val (List.ofFn y) (s0 i)) _ ⟨i, hlt⟩
    show Stat.Valid (n' + ([] : List Gate).length) ((List.ofFn s0).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom [] (List.ofFn y)) ((List.ofFn s0).getD i (Sum.inl false)) = _
    rw [h1, h2]
    exact ⟨by simpa using hv ⟨i, hlt⟩, rfl⟩
  · show Stat.Valid (n' + ([] : List Gate).length) ((List.ofFn s0).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom [] (List.ofFn y)) ((List.ofFn s0).getD i (Sum.inl false)) = _
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem restrict_sem {n n' : ℕ} (gs : List Gate) (hok : ∀ g ∈ gs, Ok g) (s0 : Fin n → Stat)
    (hv : ∀ i, Stat.Valid n' (s0 i)) :
    CleanL n' (elim n' gs (List.ofFn s0, [])).2 ∧
    ∀ (y : Fin n' → Bool) (o : ℕ),
      Stat.val (wiresFrom (elim n' gs (List.ofFn s0, [])).2 (List.ofFn y))
        ((elim n' gs (List.ofFn s0, [])).1.getD o (Sum.inl false)) =
      (wiresFrom gs (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i))).getD o false := by
  constructor
  · exact clean_elim n' (List.ofFn fun _ : Fin n' => false) (by simp) gs _ _ hok
      (inv_start s0 hv _) (by intro p g hp; simp at hp)
  · intro y o
    exact ((inv_elim n' (List.ofFn y) (by simp) gs _ _ hok (inv_start s0 hv y)).2 o).2

theorem clean_fan (n : ℕ) (gs : List Gate) (o : ℕ) (h : CleanL n gs) : FanInTwo ⟨gs, o⟩ := by
  intro g hg
  exact (clean_nok n gs h g hg).1

-- The general form: restrict and renumber, the count of binary gates does not grow.
theorem restrict_core {n n' : ℕ} (C : Circuit) (hfan : FanInTwo C) (s0 : Fin n → Stat)
    (hv : ∀ i, Stat.Valid n' (s0 i)) (f' : (Fin n' → Bool) → Bool)
    (he : ∀ y : Fin n' → Bool,
      C.eval (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)) = f' y)
    (hnc : ∃ y y', f' y ≠ f' y') :
    ∃ C' : Circuit, FanInTwo C' ∧ nonNotCount C'.gates ≤ nonNotCount C.gates ∧
      ∀ y : Fin n' → Bool, C'.eval (List.ofFn y) = f' y := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  obtain ⟨hclean, hsem⟩ := restrict_sem C.gates hok s0 hv
  have hval : ∀ y : Fin n' → Bool,
      Stat.val (wiresFrom (elim n' C.gates (List.ofFn s0, [])).2 (List.ofFn y))
        ((elim n' C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false)) = f' y := by
    intro y
    rw [hsem y C.output, ← he y]
    rfl
  cases hst : (elim n' C.gates (List.ofFn s0, [])).1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨⟨(elim n' C.gates (List.ofFn s0, [])).2, j⟩, clean_fan n' _ j hclean, ?_, ?_⟩
    · simpa [nonNotCount] using elim_nonNotCount n' C.gates (List.ofFn s0, [])
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem elim_count_marked (n : ℕ) (A B : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hg : isNotGate g.op = false)
    (hnone : (simplify g.op (n + (elim n A acc).2.length)
      (g.inputs.map fun i => (elim n A acc).1.getD i (Sum.inl false))).1 = none) :
    nonNotCount (elim n (A ++ g :: B) acc).2 + 1 ≤ nonNotCount acc.2 + nonNotCount (A ++ g :: B) := by
  have h1 : elim n (A ++ g :: B) acc = elim n B (elimStep n (elim n A acc) g) := by
    simp [elim, List.foldl_append]
  have h2 := elim_nonNotCount n B (elimStep n (elim n A acc) g)
  have h3 := elim_nonNotCount n A acc
  have h4 : nonNotCount (elimStep n (elim n A acc) g).2 = nonNotCount (elim n A acc).2 := by
    show nonNotCount ((elim n A acc).2 ++ (simplify g.op (n + (elim n A acc).2.length)
      (g.inputs.map fun i => (elim n A acc).1.getD i (Sum.inl false))).1.toList) = _
    rw [hnone]
    simp
  have h5 : nonNotCount (A ++ g :: B) = nonNotCount A + nonNotCount B + 1 := by
    simp [nonNotCount, List.countP_append, List.countP_cons, hg]
    omega
  rw [h1, h5]
  omega

theorem simplify_binary_some (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (m : ℕ)
    (ins : List Stat) (h : (simplify op m ins).1 ≠ none) :
    ∃ a b, ins = [Sum.inr a, Sum.inr b] := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at h ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at h ⊢

theorem simplify_not_inr (m : ℕ) (ins : List Stat) (k : ℕ)
    (h : (simplify GateOp.not m ins).2 = Sum.inr k) : ∃ a rest, ins = Sum.inr a :: rest := by
  rcases ins with _ | ⟨a, l⟩
  · simp [simplify, simpNot] at h
  · cases a with
    | inl c => simp [simplify, simpNot] at h
    | inr a => exact ⟨a, l, rfl⟩


lemma no_drop_indep (n : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, Ok g) :
    ∀ (acc : List Stat × List Gate) (w1 w2 : List Bool),
      acc.1.length = w1.length → w1.length = w2.length →
      (∀ i, ∀ j, acc.1.getD i (Sum.inl false) = Sum.inr j → w1.getD i false = w2.getD i false) →
      (nonNotCount (elim n gs acc).2 = nonNotCount acc.2 + nonNotCount gs) →
      ∀ i, ∀ j, (elim n gs acc).1.getD i (Sum.inl false) = Sum.inr j →
        (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false := by
  induction gs with
  | nil =>
    intro acc w1 w2 _ _ hag _
    exact hag
  | cons g gs ih =>
    intro acc w1 w2 hl1 hl2 hag hnodrop
    have hstep_le : nonNotCount (elimStep n acc g).2 ≤ nonNotCount acc.2 + (if !(isNotGate g.op) then 1 else 0) := by
      have h1 : nonNotCount (elimStep n acc g).2 =
          nonNotCount acc.2 + nonNotCount (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList :=
        opCount_append (fun op => !(isNotGate op)) acc.2 _
      have h2 := simplify_opCount_le (fun op => !(isNotGate op)) g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      change opCount (fun op => !(isNotGate op)) _ ≤ _ at h2
      change nonNotCount _ ≤ _ at h2
      omega
    have htail_le := elim_nonNotCount n gs (elimStep n acc g)
    have hcons : nonNotCount (g :: gs) = nonNotCount gs + (if !(isNotGate g.op) then 1 else 0) :=
      opCount_cons (fun op => !(isNotGate op)) g gs
    have hrest_eq : nonNotCount (elim n gs (elimStep n acc g)).2 =
        nonNotCount (elimStep n acc g).2 + nonNotCount gs := by
      change nonNotCount (elim n gs (elimStep n acc g)).2 = _ at hnodrop
      omega
    have hcur_eq : nonNotCount (elimStep n acc g).2 =
        nonNotCount acc.2 + (if !(isNotGate g.op) then 1 else 0) := by
      change nonNotCount (elim n gs (elimStep n acc g)).2 = _ at hnodrop
      omega
    apply ih (fun g' hg' => hfan g' (by simp [hg'])) (elimStep n acc g)
      (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
      (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
      (by simp [elimStep, hl1]) (by simp [hl2]) _ hrest_eq
    intro i j hij
    by_cases hil : i = acc.1.length
    · subst hil
      change (acc.1 ++ [_]).getD acc.1.length (Sum.inl false) = Sum.inr j at hij
      rw [getD_snoc_eq] at hij
      rw [hl1, getD_snoc_eq, hl2, getD_snoc_eq]
      have hok := hfan g (by simp)
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using hok.1
      set ins := g.inputs.map fun k => acc.1.getD k (Sum.inl false) with hins
      rcases hop with hop | hop | hop
      · have hne : (simplify g.op (n + acc.2.length) ins).1 ≠ none := by
          intro hnone
          rw [elimStep] at hcur_eq
          dsimp only at hcur_eq
          rw [← hins, hnone] at hcur_eq
          simp only [Option.toList_none, List.append_nil, hop, isNotGate, Bool.not_false, ite_true] at hcur_eq
          omega
        rw [hop] at hne hij
        rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rw [hins, hgi] at hne; simp [simplify, simpAnd] at hne
        · rw [hins, hgi] at hne; simp only [List.map_cons, List.map_nil] at hne
          cases ha : acc.1.getD a (Sum.inl false) <;> (rw [ha] at hne; simp [simplify, simpAnd] at hne)
        · rw [hins, hgi] at hne; simp only [List.map_cons, List.map_nil] at hne
          cases ha : acc.1.getD a (Sum.inl false) <;> cases hb : acc.1.getD b (Sum.inl false)
          · rw [ha, hb] at hne; simp [simplify, simpAnd] at hne
          · rw [ha, hb] at hne; simp [simplify, simpAnd] at hne
          · rw [ha, hb] at hne; simp [simplify, simpAnd] at hne
          · rename_i ja jb
            have e1 := hag a ja ha
            have e2 := hag b jb hb
            simp only [List.map_cons, List.map_nil]
            rw [e1, e2]
        · have := hok.2; rw [hgi] at this; simp at this
      · have hne : (simplify g.op (n + acc.2.length) ins).1 ≠ none := by
          intro hnone
          rw [elimStep] at hcur_eq
          dsimp only at hcur_eq
          rw [← hins, hnone] at hcur_eq
          simp only [Option.toList_none, List.append_nil, hop, isNotGate, Bool.not_false, ite_true] at hcur_eq
          omega
        rw [hop] at hne hij
        rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rw [hins, hgi] at hne; simp [simplify, simpOr] at hne
        · rw [hins, hgi] at hne; simp only [List.map_cons, List.map_nil] at hne
          cases ha : acc.1.getD a (Sum.inl false) <;> (rw [ha] at hne; simp [simplify, simpOr] at hne)
        · rw [hins, hgi] at hne; simp only [List.map_cons, List.map_nil] at hne
          cases ha : acc.1.getD a (Sum.inl false) <;> cases hb : acc.1.getD b (Sum.inl false)
          · rw [ha, hb] at hne; simp [simplify, simpOr] at hne
          · rw [ha, hb] at hne; simp [simplify, simpOr] at hne
          · rw [ha, hb] at hne; simp [simplify, simpOr] at hne
          · rename_i ja jb
            have e1 := hag a ja ha
            have e2 := hag b jb hb
            simp only [List.map_cons, List.map_nil]
            rw [e1, e2]
        · have := hok.2; rw [hgi] at this; simp at this
      · rw [hop] at hij ⊢
        rcases hgi : g.inputs with _ | ⟨a, rest⟩
        · rw [hins, hgi] at hij; simp [simplify, simpNot] at hij
        · rw [hins, hgi] at hij; simp only [List.map_cons] at hij
          cases ha : acc.1.getD a (Sum.inl false) with
          | inl c => rw [ha] at hij; simp [simplify, simpNot] at hij
          | inr ja =>
            have e1 := hag a ja ha
            simp only [GateOp.eval, List.map_cons, List.headD_cons]
            rw [e1]
    · change (acc.1 ++ [_]).getD i (Sum.inl false) = Sum.inr j at hij
      rw [getD_snoc_ne _ _ _ _ hil] at hij
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hag i j hij

theorem drop_of_difference (n : ℕ) (gs : List Gate) (hfan : ∀ g ∈ gs, Ok g)
    (acc : List Stat × List Gate) (w1 w2 : List Bool)
    (hl1 : acc.1.length = w1.length) (hl2 : w1.length = w2.length)
    (hag : ∀ i j, acc.1.getD i (Sum.inl false) = Sum.inr j →
      w1.getD i false = w2.getD i false)
    (o j : ℕ) (hst : (elim n gs acc).1.getD o (Sum.inl false) = Sum.inr j)
    (hne : (wiresFrom gs w1).getD o false ≠ (wiresFrom gs w2).getD o false) :
    nonNotCount (elim n gs acc).2 + 1 ≤ nonNotCount acc.2 + nonNotCount gs := by
  have hle := elim_nonNotCount n gs acc
  by_contra h
  have heq : nonNotCount (elim n gs acc).2 = nonNotCount acc.2 + nonNotCount gs := by omega
  exact hne (no_drop_indep n gs hfan acc w1 w2 hl1 hl2 hag heq o j hst)

def zeroStats {n : ℕ} (p : Fin n) : Fin n → Stat :=
  fun i => if i = p then Sum.inl false else Sum.inr i.val

theorem zeroStats_agree {n : ℕ} (p : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ p → x i = y i) (i j : ℕ)
    (hst : (List.ofFn (zeroStats p)).getD i (Sum.inl false) = Sum.inr j) :
    (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  by_cases hi : i < n
  · have hs : (List.ofFn (zeroStats p)).getD i (Sum.inl false) = zeroStats p ⟨i, hi⟩ :=
      getD_ofFn n _ _ ⟨i, hi⟩
    have hne : (⟨i, hi⟩ : Fin n) ≠ p := by
      intro heq
      rw [hs] at hst
      simp [zeroStats, heq] at hst
    rw [getD_ofFn n x false ⟨i, hi⟩, getD_ofFn n y false ⟨i, hi⟩]
    exact hxy ⟨i, hi⟩ hne
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hst
    cases hst

theorem zero_prefix_literal_constant {n : ℕ} (A : List Gate)
    (hfan : ∀ q ∈ A, Ok q) (hA : nonNotCount A = 0)
    (p : Fin n) (i : ℕ) (b : Bool)
    (hlit : ∀ x : Fin n → Bool,
      (wiresFrom A (List.ofFn x)).getD i false = if b then !(x p) else x p) :
    ∃ c : Bool, (elim n A (List.ofFn (zeroStats p), [])).1.getD i (Sum.inl false)
      = Sum.inl c := by
  cases hst : (elim n A (List.ofFn (zeroStats p), [])).1.getD i (Sum.inl false) with
  | inl c => exact ⟨c, rfl⟩
  | inr j =>
    exfalso
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun q => decide (q = p)
    have hxy : ∀ q, q ≠ p → x q = y q := by intro q hq; simp [x, y, hq]
    have hle := elim_nonNotCount n A (List.ofFn (zeroStats p), [])
    change nonNotCount (elim n A (List.ofFn (zeroStats p), [])).2 ≤ 0 + nonNotCount A at hle
    have heq : nonNotCount (elim n A (List.ofFn (zeroStats p), [])).2
        = nonNotCount ([] : List Gate) + nonNotCount A := by
      have hz : nonNotCount ([] : List Gate) = 0 := rfl
      omega
    have h := no_drop_indep n A hfan (List.ofFn (zeroStats p), [])
      (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (zeroStats_agree p x y hxy) heq i j hst
    rw [hlit x, hlit y] at h
    cases b <;> simp [x, y] at h

theorem binary_drops_with_constant_input (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : ℕ) (stats : List Stat) (i j : ℕ) (c : Bool)
    (hc : stats.getD i (Sum.inl false) = Sum.inl c) :
    (simplify op m ([i, j].map fun a => stats.getD a (Sum.inl false))).1 = none := by
  change (simplify op m [stats.getD i (Sum.inl false), stats.getD j (Sum.inl false)]).1 = none
  rw [hc]
  rcases hop with rfl | rfl <;>
    cases hother : stats.getD j (Sum.inl false) <;> cases c <;>
    rfl

-- If a first binary gate disappears and its value agrees on a distinguishing pair,
-- then a second binary gate must disappear later. Unary gates may remain or disappear.
theorem two_drop_of_control {n : ℕ} (A B : List Gate) (g : Gate)
    (hfan : ∀ q ∈ A ++ g :: B, Ok q)
    (hA : nonNotCount A = 0) (hg : isNotGate g.op = false)
    (p : Fin n) (x y : Fin n → Bool) (hxy : ∀ i, i ≠ p → x i = y i)
    (hgdrop : (simplify g.op (n + (elim n A (List.ofFn (zeroStats p), [])).2.length)
      (g.inputs.map fun i => (elim n A (List.ofFn (zeroStats p), [])).1.getD i
        (Sum.inl false))).1 = none)
    (hcontrol : g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn x)).getD i false)
      = g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn y)).getD i false))
    (o j : ℕ)
    (hst : (elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).1.getD o (Sum.inl false)
      = Sum.inr j)
    (hne : (wiresFrom (A ++ g :: B) (List.ofFn x)).getD o false ≠
      (wiresFrom (A ++ g :: B) (List.ofFn y)).getD o false) :
    nonNotCount (elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).2 + 2
      ≤ nonNotCount (A ++ g :: B) := by
  let initial : List Stat × List Gate := (List.ofFn (zeroStats p), [])
  let pre := elim n A initial
  let mid := elimStep n pre g
  let wx := wiresFrom A (List.ofFn x)
  let wy := wiresFrom A (List.ofFn y)
  let vx := wx ++ [g.op.eval (g.inputs.map fun i => wx.getD i false)]
  let vy := wy ++ [g.op.eval (g.inputs.map fun i => wy.getD i false)]
  have hpre : nonNotCount pre.2 = 0 := by
    have h := elim_nonNotCount n A initial
    change nonNotCount pre.2 ≤ 0 + nonNotCount A at h
    omega
  have hmid : nonNotCount mid.2 = 0 := by
    change nonNotCount (pre.2 ++ _) = 0
    change (simplify g.op (n + pre.2.length)
      (g.inputs.map fun i => pre.1.getD i (Sum.inl false))).1 = none at hgdrop
    rw [hgdrop]
    simpa using hpre
  have hprelen : pre.1.length = wx.length := by
    simp [pre, initial, wx, elim_stats_length, length_wiresFrom]
  have hxylen : wx.length = wy.length := by simp [wx, wy, length_wiresFrom]
  have hpreagree : ∀ i k, pre.1.getD i (Sum.inl false) = Sum.inr k →
      wx.getD i false = wy.getD i false := by
    apply no_drop_indep n A (fun q hq => hfan q (by simp [hq])) initial
      (List.ofFn x) (List.ofFn y) (by simp [initial]) (by simp)
      (zeroStats_agree p x y hxy)
    change nonNotCount pre.2 = 0 + nonNotCount A
    omega
  have hmidagree : ∀ i k, mid.1.getD i (Sum.inl false) = Sum.inr k →
      vx.getD i false = vy.getD i false := by
    intro i k hik
    by_cases hi : i = pre.1.length
    · rw [hi]
      change (wx ++ [_]).getD pre.1.length false = (wy ++ [_]).getD pre.1.length false
      rw [hprelen, getD_snoc_eq, hxylen, getD_snoc_eq]
      exact hcontrol
    · change (pre.1 ++ [_]).getD i (Sum.inl false) = Sum.inr k at hik
      rw [getD_snoc_ne _ _ _ _ hi] at hik
      change (wx ++ [_]).getD i false = (wy ++ [_]).getD i false
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hpreagree i k hik
  have helim : elim n (A ++ g :: B) initial = elim n B mid := by
    simp [elim, List.foldl_append, mid, pre]
  have hwirex : wiresFrom (A ++ g :: B) (List.ofFn x) = wiresFrom B vx := by
    rw [wiresFrom_append]; rfl
  have hwirey : wiresFrom (A ++ g :: B) (List.ofFn y) = wiresFrom B vy := by
    rw [wiresFrom_append]; rfl
  change (elim n (A ++ g :: B) initial).1.getD o (Sum.inl false) = Sum.inr j at hst
  rw [helim] at hst
  rw [hwirex, hwirey] at hne
  have hdrop := drop_of_difference n B (fun q hq => hfan q (by simp [hq])) mid vx vy
    (by simp [mid, elimStep, vx, hprelen]) (by simp [vx, vy, hxylen])
    hmidagree o j hst hne
  have hcount : nonNotCount (A ++ g :: B) = nonNotCount B + 1 := by
    simp [nonNotCount, List.countP_append, hg] at hA ⊢
    omega
  change nonNotCount (elim n (A ++ g :: B) initial).2 + 2 ≤ _
  rw [helim, hcount]
  omega

theorem restrict_two_drop {n : ℕ} (A B : List Gate) (g : Gate) (o : ℕ)
    (hfan : FanInTwo ⟨A ++ g :: B, o⟩)
    (hA : nonNotCount A = 0) (hg : isNotGate g.op = false)
    (p : Fin n) (f : (Fin n → Bool) → Bool)
    (he : ∀ z, Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn z) = f z)
    (hnc : ∃ z z', f (Function.update z p false) ≠ f (Function.update z' p false))
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ p → x i = y i) (hneq : f x ≠ f y)
    (hgdrop : (simplify g.op (n + (elim n A (List.ofFn (zeroStats p), [])).2.length)
      (g.inputs.map fun i => (elim n A (List.ofFn (zeroStats p), [])).1.getD i
        (Sum.inl false))).1 = none)
    (hcontrol : g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn x)).getD i false)
      = g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn y)).getD i false)) :
    ∃ D : Circuit, FanInTwo D ∧ nonNotCount D.gates + 2 ≤ nonNotCount (A ++ g :: B) ∧
      ∀ z, D.eval (List.ofFn z) = f (Function.update z p false) := by
  have hok : ∀ q ∈ A ++ g :: B, Ok q := hfan
  have hv : ∀ i, Stat.Valid n (zeroStats p i) := by
    intro i
    by_cases hi : i = p
    · simp [zeroStats, hi, Stat.Valid]
    · simp [zeroStats, hi, Stat.Valid, i.isLt]
  have hold : ∀ z : Fin n → Bool,
      (fun i => Stat.val (List.ofFn z) (zeroStats p i)) = Function.update z p false := by
    intro z
    funext i
    by_cases hi : i = p
    · simp [zeroStats, hi, Stat.val]
    · simp [zeroStats, hi, Stat.val, Function.update_of_ne hi]
  obtain ⟨hclean, hsem⟩ := restrict_sem (A ++ g :: B) hok (zeroStats p) hv
  have hval : ∀ z : Fin n → Bool,
      Stat.val (wiresFrom (elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).2 (List.ofFn z))
        ((elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).1.getD o (Sum.inl false))
        = f (Function.update z p false) := by
    intro z
    rw [hsem z o, hold z, ← he]
    rfl
  cases hst : (elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨z, z', hne⟩ := hnc
    apply hne
    rw [← hval z, ← hval z', hst]
    rfl
  | inr j =>
    refine ⟨⟨(elim n (A ++ g :: B) (List.ofFn (zeroStats p), [])).2, j⟩,
      clean_fan n _ j hclean, ?_, ?_⟩
    · apply two_drop_of_control A B g hok hA hg p x y hxy hgdrop hcontrol o j hst
      change Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) ≠
        Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn y)
      simpa only [he] using hneq
    · intro z
      have h := hval z
      rw [hst] at h
      exact h

end Restrict
end PEqualNP.Outside.Pilot110TwoDrop
