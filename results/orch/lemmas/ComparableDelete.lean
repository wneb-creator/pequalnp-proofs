import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.ConstantDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

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

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

lemma inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


end CircuitProof

open CircuitProof

def MonoGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma monoGates_ok {gs : List Gate} (h : MonoGates gs) : ∀ g ∈ gs, Ok g := by
  intro g hg
  obtain ⟨hop, hlen⟩ := h g hg
  refine ⟨?_, hlen⟩
  rcases hop with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

lemma elim_mono (n : Nat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    MonoGates gs → MonoGates acc.2 → MonoGates (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
      intro acc hg ha
      apply ih (elimStep n acc g) (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      intro k hk
      change k ∈ acc.2 ++ _ at hk
      rcases List.mem_append.mp hk with hk | hk
      · exact ha k hk
      · have member : k ∈ (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 := by
          simpa using hk
        have same := simplify_same_op _ _ _ k member
        refine ⟨?_, (simplify_ok _ _ _ k member).2⟩
        rw [same]
        exact (hg g List.mem_cons_self).1

lemma elim_length_strict (n : Nat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∃ g ∈ gs, g.inputs = []) →
      (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc h; simpa using h
  | cons g gs ih =>
      intro acc h
      obtain ⟨k, hk, he⟩ := h
      rcases List.mem_cons.mp hk with hkg | hk
      · subst k
        have empty : (simplify g.op (n + acc.2.length)
              (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
          rw [he]
          cases g.op <;> rfl
        have hb := elim_len n gs (elimStep n acc g)
        have sameLength : (elimStep n acc g).2.length = acc.2.length := by
          change (acc.2 ++ (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
          rw [empty]
          simp
        rw [sameLength] at hb
        change (elim n gs (elimStep n acc g)).2.length + 1 ≤ _
        simp only [List.length_cons]
        omega
      · have hb := ih (elimStep n acc g) ⟨k, hk, he⟩
        have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g.op (n + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
          omega
        change (elim n gs (elimStep n acc g)).2.length + 1 ≤ _
        simp only [List.length_cons]
        omega

lemma drop_constant {n : Nat} (C : Circuit) (mono : Monotone2 C)
    (constant : ∃ g ∈ C.gates, g.inputs = [])
    (nonconstant : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hm : MonoGates C.gates := by
    simpa only [MonoGates, Monotone2, Set.mem_insert_iff, Set.mem_singleton_iff] using mono
  let acc := elim n C.gates (idStats n, [])
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ (monoGates_ok hm) (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn y) := fun y => ((hinv y).2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
      exfalso
      obtain ⟨x, y, hxy⟩ := nonconstant
      apply hxy
      rw [← hval x, ← hval y, hst]
      rfl
  | inr j =>
      refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
      · have hc := elim_mono n C.gates (idStats n, []) hm (by intro g hg; simp at hg)
        simpa only [Monotone2, MonoGates, Set.mem_insert_iff, Set.mem_singleton_iff] using hc
      · simpa [acc, Circuit.size] using elim_length_strict n C.gates (idStats n, []) constant
      · intro y
        simpa only [hst, Stat.val, Circuit.eval, Circuit.wires, wiresFrom] using hval y

def Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

lemma above_snoc {v v' : List Bool} {a a' : Bool} (h : Above v v')
    (ha : a = true → a' = true) : Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]
    exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

lemma above_run (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, Above v v' → Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
      intro v v' h
      change Above (wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]))
        (wiresFrom gs (v' ++ [g.op.eval (g.inputs.map fun i => v'.getD i false)]))
      apply ih (fun k hk => hgs k (List.mem_cons_of_mem _ hk))
      apply above_snoc h
      rcases hgs g List.mem_cons_self with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
        intro hall b hb
        obtain ⟨j, hj, rfl⟩ := hb
        exact h.2 j (hall _ ⟨j, hj, rfl⟩)
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
        rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
        exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

def constantGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

def plugged (pre post : List Gate) (out : Nat) (b : Bool) : Circuit :=
  ⟨pre ++ constantGate b :: post, out⟩

def bracket (pre post : List Gate) (out : Nat) (x : List Bool) (b : Bool) : Bool :=
  (wiresFrom post (wiresFrom pre x ++ [b])).getD out false

def notSource (pre : List Gate) (ins : List Nat) (x : List Bool) : Bool :=
  (ins.map fun i => (wiresFrom pre x).getD i false).headD false

lemma plugged_eval (pre post : List Gate) (out : Nat) (x : List Bool) (b : Bool) :
    (plugged pre post out b).eval x = bracket pre post out x b := by
  change (wiresFrom (pre ++ constantGate b :: post) x).getD out false = _
  rw [wiresFrom_append]
  cases b <;> rfl

lemma not_eval (pre post : List Gate) (ins : List Nat) (out : Nat) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ x =
      bracket pre post out x (!(notSource pre ins x)) := by
  change (wiresFrom (pre ++ ⟨GateOp.not, ins⟩ :: post) x).getD out false = _
  rw [wiresFrom_append]
  rfl

lemma bracket_monotone (pre post : List Gate) (out : Nat) (x : List Bool)
    (mono : MonoGates post) : Monotone (bracket pre post out x) := by
  intro a b hab
  apply Bool.le_iff_imp.mpr
  exact (above_run post (fun g hg => (mono g hg).1) _ _
    (above_snoc ⟨rfl, fun _ h => h⟩ (Bool.le_iff_imp.mp hab))).2 out

lemma plugged_mono (pre post : List Gate) (out : Nat) (b : Bool)
    (hp : MonoGates pre) (hq : MonoGates post) : Monotone2 (plugged pre post out b) := by
  intro g hg
  have hmono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    rcases List.mem_append.mp hg with h | h
    · exact hp g h
    · rcases List.mem_cons.mp h with h | h
      · subst g
        cases b <;> simp [constantGate]
      · exact hq g h
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmono

lemma comparable_replacement {n : Nat} (pre post : List Gate) (ins : List Nat) (out : Nat)
    (hq : MonoGates post)
    (compare :
      (∀ x : Fin n → Bool, notSource pre ins (List.ofFn x) ≤
        Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x)) ∨
      (∀ x : Fin n → Bool, Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) ≤
        notSource pre ins (List.ofFn x))) :
    ∃ b : Bool, ∀ x : Fin n → Bool,
      (plugged pre post out b).eval (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) := by
  rcases compare with below | above
  · refine ⟨true, ?_⟩
    intro x
    have order := bracket_monotone pre post out (List.ofFn x) hq
      (show false ≤ true from by decide)
    have h := below x
    rw [plugged_eval, not_eval]
    rw [not_eval] at h
    cases hs : notSource pre ins (List.ofFn x) <;>
      cases ht : bracket pre post out (List.ofFn x) true <;>
      cases hf : bracket pre post out (List.ofFn x) false <;>
      simp_all [Bool.le_iff_imp]
  · refine ⟨false, ?_⟩
    intro x
    have order := bracket_monotone pre post out (List.ofFn x) hq
      (show false ≤ true from by decide)
    have h := above x
    rw [plugged_eval, not_eval]
    rw [not_eval] at h
    cases hs : notSource pre ins (List.ofFn x) <;>
      cases ht : bracket pre post out (List.ofFn x) true <;>
      cases hf : bracket pre post out (List.ofFn x) false <;>
      simp_all [Bool.le_iff_imp]

lemma eliminate_comparable_not {n : Nat} (pre post : List Gate) (ins : List Nat) (out : Nat)
    (hp : MonoGates pre) (hq : MonoGates post)
    (nonconstant : ∃ x y : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) ≠
        Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn y))
    (compare :
      (∀ x : Fin n → Bool, notSource pre ins (List.ofFn x) ≤
        Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x)) ∨
      (∀ x : Fin n → Bool, Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) ≤
        notSource pre ins (List.ofFn x))) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ pre.length + 1 + post.length ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) := by
  obtain ⟨b, same⟩ := comparable_replacement pre post ins out hq compare
  have hc : ∃ g ∈ (plugged pre post out b).gates, g.inputs = [] := by
    refine ⟨constantGate b, List.mem_append.mpr (Or.inr List.mem_cons_self), ?_⟩
    cases b <;> rfl
  have hn : ∃ x y : Fin n → Bool,
      (plugged pre post out b).eval (List.ofFn x) ≠
        (plugged pre post out b).eval (List.ofFn y) := by
    obtain ⟨x, y, h⟩ := nonconstant
    exact ⟨x, y, by simpa only [same] using h⟩
  obtain ⟨D, mono, size, computes⟩ := drop_constant (plugged pre post out b)
    (plugged_mono pre post out b hp hq) hc hn
  refine ⟨D, mono, ?_, fun x => (computes x).trans (same x)⟩
  simpa [plugged, Circuit.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using size

end PEqualNP.Outside.L_meta_2592.ConstantDrop
