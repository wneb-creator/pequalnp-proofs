import PEqualNP.Defs

-- The simplifier and its semantic/count invariants are copied from checked L_meta_5026,
-- with only the surrounding namespace changed. That infrastructure credits the checked
-- L_meta_3620/L_meta_1549 development. The two-drop control theorem below is new.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion
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

end Restrict
end PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion


namespace PEqualNP.Outside.L_meta_2583_aux.PrimeReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire monotonicity infrastructure adapted from the checked L_meta_610 proof.
def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk


lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma append_signal_le (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases he : i = w.length
  · subst i
    rw [getD_append_last_eq w a _ rfl] at hi
    rw [getD_append_last_eq v b _ hlen.symm]
    exact hab hi
  · rw [getD_snoc_ne _ _ _ he] at hi
    rw [getD_snoc_ne _ _ _ (by omega)]
    exact h i hi

def MonoFn {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def edgeInput {n : ℕ} (e : Fin n × Fin n) : Fin n → Bool :=
  fun i => decide (i = e.1 ∨ i = e.2)

def edgeValue {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)

lemma edgeInput_le {n : ℕ} (e : Fin n × Fin n) (x : Fin n → Bool)
    (ha : x e.1 = true) (hb : x e.2 = true) :
    ∀ i, edgeInput e i = true → x i = true := by
  intro i hi
  have h : i = e.1 ∨ i = e.2 := of_decide_eq_true hi
  rcases h with rfl | rfl
  · exact ha
  · exact hb

lemma edgeValue_pair {n : ℕ} (E : Finset (Fin n × Fin n)) (e : Fin n × Fin n)
    (he : e ∈ E) : edgeValue E (edgeInput e) = true := by
  apply decide_eq_true
  exact ⟨e, he, by simp [edgeInput], by simp [edgeInput]⟩

lemma lowered_eq_on_edges {n : ℕ} (E : Finset (Fin n × Fin n))
    (f : (Fin n → Bool) → Bool) (mono : MonoFn f)
    (below : ∀ x, f x = true → edgeValue E x = true)
    (edges : ∀ e ∈ E, f (edgeInput e) = true) :
    ∀ x, f x = edgeValue E x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact below x
  · intro hx
    obtain ⟨e, he, ha, hb⟩ := of_decide_eq_true hx
    exact mono (edgeInput e) x (edgeInput_le e x ha hb) (edges e he)

lemma input_list_le {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hil : i < n
  · rw [getD_ofFn x i hil] at hi
    rw [getD_ofFn y i hil]
    exact h ⟨i, hil⟩ hi
  · rw [getD_ge_length _ _ (by simp; omega)] at hi
    cases hi

def replacedValue {n : ℕ} (A B : List Gate) (r : (Fin n → Bool) → Bool) (o : ℕ)
    (x : Fin n → Bool) : Bool :=
  (B.foldl wiresStep (A.foldl wiresStep (List.ofFn x) ++ [r x])).getD o false

lemma replaced_mono {n : ℕ} (A B : List Gate)
    (hA : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ g ∈ B, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r) (o : ℕ) :
    MonoFn (replacedValue A B r o) := by
  intro x y hxy
  apply monotone_foldl_wiresStep B hB _ _
    (by simp [foldl_wiresStep_length])
  apply append_signal_le _ _ _ _ (by simp [foldl_wiresStep_length])
  · exact monotone_foldl_wiresStep A hA _ _ (by simp) (input_list_le x y hxy)
  · exact hr x y hxy

-- A lower monotone replacement that agrees on every accepted edge preserves the whole function.
theorem lower_wire_preserves {n : ℕ} (E : Finset (Fin n × Fin n))
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hA : ∀ t ∈ A, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ t ∈ B, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r)
    (below : ∀ x, r x = true →
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn x)).getD i false) = true)
    (same : ∀ e ∈ E, r (edgeInput e) =
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false))
    (computes : ∀ x : Fin n → Bool, Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x) :
    ∀ x, replacedValue A B r o x = edgeValue E x := by
  apply lowered_eq_on_edges E _ (replaced_mono A B hA hB r hr o)
  · intro x hx
    have hle := monotone_foldl_wiresStep B hB
      (A.foldl wiresStep (List.ofFn x) ++ [r x])
      (wiresStep (A.foldl wiresStep (List.ofFn x)) g)
      (by simp [wiresStep])
      (append_signal_le _ _ _ _ rfl (fun _ h => h) (below x)) o hx
    have horig : (B.foldl wiresStep (wiresStep (A.foldl wiresStep (List.ofFn x)) g)).getD o false
        = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes x] at hle
    exact hle
  · intro e he
    rw [replacedValue, same e he]
    have horig :
        (B.foldl wiresStep (A.foldl wiresStep (List.ofFn (edgeInput e)) ++
          [g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false)])).getD o false
          = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn (edgeInput e)) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes]
    exact edgeValue_pair E e he

-- The dual argument uses any monotone-complete family of negative inputs.
theorem raised_eq_on_negatives {n : ℕ} (E : Finset (Fin n × Fin n))
    (B : Finset (Fin n → Bool)) (f : (Fin n → Bool) → Bool) (mono : MonoFn f)
    (above : ∀ x, edgeValue E x = true → f x = true)
    (cover : ∀ x, edgeValue E x = false →
      ∃ y ∈ B, ∀ i, x i = true → y i = true)
    (negative : ∀ y ∈ B, f y = false) : ∀ x, f x = edgeValue E x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    cases he : edgeValue E x with
    | true => rfl
    | false =>
      obtain ⟨y, hy, hxy⟩ := cover x he
      have h := mono x y hxy hx
      rw [negative y hy] at h
      cases h
  · exact above x

theorem raise_wire_preserves {n : ℕ} (E : Finset (Fin n × Fin n))
    (negativeInputs : Finset (Fin n → Bool))
    (cover : ∀ x, edgeValue E x = false →
      ∃ y ∈ negativeInputs, ∀ i, x i = true → y i = true)
    (negative : ∀ y ∈ negativeInputs, edgeValue E y = false)
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hA : ∀ t ∈ A, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hB : ∀ t ∈ B, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (r : (Fin n → Bool) → Bool) (hr : MonoFn r)
    (above : ∀ x,
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn x)).getD i false) = true → r x = true)
    (same : ∀ y ∈ negativeInputs, r y =
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn y)).getD i false))
    (computes : ∀ x : Fin n → Bool, Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x) :
    ∀ x, replacedValue A B r o x = edgeValue E x := by
  apply raised_eq_on_negatives E negativeInputs _ (replaced_mono A B hA hB r hr o) ?_ cover ?_
  · intro x hx
    have horg : (B.foldl wiresStep (wiresStep (A.foldl wiresStep (List.ofFn x)) g)).getD o false = true := by
      have heq : (B.foldl wiresStep (wiresStep (A.foldl wiresStep (List.ofFn x)) g)).getD o false =
          Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) := by
        simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
        rfl
      rw [heq, computes x]
      exact hx
    exact monotone_foldl_wiresStep B hB _ _ (by simp [wiresStep])
      (append_signal_le _ _ _ _ rfl (fun _ h => h) (above x)) o horg
  · intro y hy
    rw [replacedValue, same y hy]
    have horig :
        (B.foldl wiresStep (A.foldl wiresStep (List.ofFn y) ++
          [g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn y)).getD i false)])).getD o false
          = Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn y) := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [horig, computes]
    exact negative y hy

end PEqualNP.Outside.L_meta_2583_aux.PrimeReplacement

namespace PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof Restrict

lemma nonNotCount_eq_length (gs : List Gate)
    (hn : ∀ g ∈ gs, isNotGate g.op = false) : nonNotCount gs = gs.length := by
  apply List.countP_eq_length.mpr
  intro g hg
  simp [hn g hg]

lemma noNot_ao {m : ℕ} {g : Gate} (hc : CleanGate m g) (hn : isNotGate g.op = false) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  rcases hc with ⟨hop, j, _, hins⟩ | ⟨hop, j, k, _, _, hins⟩
  · rw [hop] at hn
    cases hn
  · exact ⟨hop, by simp [hins]⟩

lemma clean_ao {n : ℕ} (gs : List Gate) (o : ℕ) (hc : CleanL n gs)
    (hn : ∀ g ∈ gs, isNotGate g.op = false) : PEqualNP.TopForm.IsAO2 n ⟨gs, o⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    exact (noNot_ao (hc j g hj) (hn g hg)).1
  · intro j hj i hi
    have hget : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
    have hat : NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by
      simp only [NestedCover.gateAt, List.getD_eq_getElem?_getD, hget, Option.getD_some]
    rw [hat] at hi
    exact (hc j gs[j] hget).lt i hi
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    exact (noNot_ao (hc j g hj) (hn g hg)).2

-- Normalizing a source circuit containing one empty OR removes at least that gate.
theorem delete_empty_or {n : ℕ} (A B : List Gate) (o : ℕ)
    (hfan : FanInTwo ⟨A ++ ⟨GateOp.or, []⟩ :: B, o⟩)
    (hao : ∀ g ∈ A ++ ⟨GateOp.or, []⟩ :: B, g.op = .and ∨ g.op = .or)
    (f : (Fin n → Bool) → Bool)
    (he : ∀ x, Circuit.eval ⟨A ++ ⟨GateOp.or, []⟩ :: B, o⟩ (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      D.size + 1 ≤ (A ++ ⟨GateOp.or, []⟩ :: B).length ∧
      ∀ x, D.eval (List.ofFn x) = f x := by
  let gs := A ++ (⟨GateOp.or, []⟩ : Gate) :: B
  let s0 : Fin n → Stat := fun i => Sum.inr i.val
  let acc := elim n gs (List.ofFn s0, [])
  have hn : ∀ g ∈ gs, isNotGate g.op = false := by
    intro g hg
    rcases hao g hg with h | h <;> rw [h] <;> rfl
  have hncount : opCount isNotGate gs = 0 := by
    apply List.countP_eq_zero.mpr
    intro g hg
    simp [hn g hg]
  have hno : opCount isNotGate acc.2 = 0 := by
    have h := elim_opCount_le isNotGate n gs (List.ofFn s0, [])
    change opCount isNotGate acc.2 ≤ 0 + opCount isNotGate gs at h
    omega
  have hnoall : ∀ g ∈ acc.2, isNotGate g.op = false := by
    intro g hg
    have h := List.countP_eq_zero.mp hno g hg
    cases hv : isNotGate g.op <;> simp_all
  have hv : ∀ i, Stat.Valid n (s0 i) := fun i => i.isLt
  have hidentity : ∀ x : Fin n → Bool, (fun i => Stat.val (List.ofFn x) (s0 i)) = x := by
    intro x
    funext i
    simp [s0, Stat.val]
  obtain ⟨hc, hsem⟩ := restrict_sem gs (show ∀ g ∈ gs, Ok g from hfan) s0 hv
  have hval : ∀ x : Fin n → Bool,
      Stat.val (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false)) = f x := by
    intro x
    rw [hsem x o, hidentity x]
    exact he x
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, clean_ao _ j hc hnoall, ?_, ?_⟩
    · have hcount := elim_count_marked n A B (⟨GateOp.or, []⟩ : Gate)
        (List.ofFn s0, []) rfl rfl
      change nonNotCount acc.2 + 1 ≤ 0 + nonNotCount gs at hcount
      rw [nonNotCount_eq_length acc.2 hnoall, nonNotCount_eq_length gs hn] at hcount
      simpa only [Circuit.size, Nat.zero_add, gs] using hcount
    · intro x
      have h := hval x
      rw [hst] at h
      exact h

end PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion

namespace PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof Restrict
open PEqualNP.Outside.L_meta_2583_aux.PrimeReplacement

-- A gate invisible on every prime edge can be removed at strictly smaller size.
theorem delete_prime_dead {n : ℕ} (E : Finset (Fin n × Fin n))
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 n ⟨A ++ g :: B, o⟩)
    (computes : ∀ x : Fin n → Bool,
      Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x)
    (nonconstant : ∃ x y, edgeValue E x ≠ edgeValue E y)
    (dead : ∀ e ∈ E,
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false) = false) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      D.size + 1 ≤ (A ++ g :: B).length ∧
      ∀ x, D.eval (List.ofFn x) = edgeValue E x := by
  have hA : ∀ t ∈ A, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
    intro t ht
    exact hao.1 t (by simp [ht])
  have hB : ∀ t ∈ B, t.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
    intro t ht
    exact hao.1 t (by simp [ht])
  have hreplace := lower_wire_preserves E A B g o hA hB (fun _ => false)
    (by intro _ _ _ h; cases h) (by intro _ h; cases h)
    (fun e he => (dead e he).symm) computes
  have hnew : ∀ x : Fin n → Bool,
      Circuit.eval ⟨A ++ ⟨GateOp.or, []⟩ :: B, o⟩ (List.ofFn x) = edgeValue E x := by
    intro x
    have heq : Circuit.eval ⟨A ++ ⟨GateOp.or, []⟩ :: B, o⟩ (List.ofFn x)
        = replacedValue A B (fun _ => false) o x := by
      simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
      rfl
    rw [heq]
    exact hreplace x
  have hfan : FanInTwo ⟨A ++ ⟨GateOp.or, []⟩ :: B, o⟩ := by
    intro t ht
    have original : t ∈ A ++ g :: B → t.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)
        ∧ t.inputs.length ≤ 2 := by
      intro hm
      refine ⟨?_, ?_⟩
      · rcases hao.1 t hm with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rw [hao.2.2 t hm]
    rcases List.mem_append.mp ht with ha | hb
    · exact original (by simp [ha])
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨Or.inr (Or.inl rfl), by decide⟩
      · exact original (by simp [hb])
  have hnewAO : ∀ t ∈ A ++ (⟨GateOp.or, []⟩ : Gate) :: B,
      t.op = GateOp.and ∨ t.op = GateOp.or := by
    intro t ht
    rcases List.mem_append.mp ht with ha | hb
    · exact hao.1 t (by simp [ha])
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inr rfl
      · exact hao.1 t (by simp [hb])
  obtain ⟨D, hD, hsize, he⟩ := delete_empty_or A B o hfan hnewAO (edgeValue E) hnew nonconstant
  refine ⟨D, hD, ?_, he⟩
  simpa only [List.length_append, List.length_cons] using hsize

theorem least_gate_has_edge {n : ℕ} (E : Finset (Fin n × Fin n))
    (A B : List Gate) (g : Gate) (o : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 n ⟨A ++ g :: B, o⟩)
    (computes : ∀ x : Fin n → Bool,
      Circuit.eval ⟨A ++ g :: B, o⟩ (List.ofFn x) = edgeValue E x)
    (nonconstant : ∃ x y, edgeValue E x ≠ edgeValue E y)
    (least : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = edgeValue E x) →
      (A ++ g :: B).length ≤ D.size) :
    ∃ e ∈ E,
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false) = true := by
  by_contra noEdge
  have dead : ∀ e ∈ E,
      g.op.eval (g.inputs.map fun i => (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false) = false := by
    intro e he
    cases hv : g.op.eval (g.inputs.map fun i =>
        (A.foldl wiresStep (List.ofFn (edgeInput e))).getD i false) with
    | false => rfl
    | true => exact False.elim (noEdge ⟨e, he, hv⟩)
  obtain ⟨D, hD, hsize, he⟩ := delete_prime_dead E A B g o hao computes nonconstant dead
  have h := least D hD he
  omega

end PEqualNP.Outside.L_meta_2583_aux.ConstantDeletion
