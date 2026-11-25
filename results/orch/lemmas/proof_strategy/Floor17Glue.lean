import PEqualNP.Defs



namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds

def signedBit (b x : Bool) : Bool := if b then !x else x

lemma signedBit_flip (b x : Bool) : Bool.not (signedBit b x) = signedBit (!b) x := by
  cases b <;> cases x <;> rfl

lemma signedBit_constant (b x y : Bool) (h : x = y) : signedBit b x = signedBit b y :=
  congrArg (signedBit b) h

lemma not_prefix_signed (n : ℕ) (gs : List Gate)
    (clean : ∀ (p : ℕ) (g : Gate), gs[p]? = some g →
      ∃ j, j < n + p ∧ g.op = GateOp.not ∧ g.inputs = [j]) :
    ∀ i, i < n + gs.length → ∃ (j : Fin n) (b : Bool),
      ∀ x : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false = signedBit b (x j) := by
  have go (gates : List Gate) : ∀ (m : ℕ) (w : (Fin n → Bool) → List Bool),
      (∀ x, (w x).length = m) →
      (∀ i, i < m → ∃ (j : Fin n) (b : Bool), ∀ x, (w x).getD i false = signedBit b (x j)) →
      (∀ (p : ℕ) (g : Gate), gates[p]? = some g →
        ∃ j, j < m + p ∧ g.op = GateOp.not ∧ g.inputs = [j]) →
      ∀ i, i < m + gates.length → ∃ (j : Fin n) (b : Bool),
        ∀ x, (Circuit.wires ⟨gates, 0⟩ (w x)).getD i false = signedBit b (x j) := by
    induction gates with
    | nil =>
      intro m w hlen hsign _ i hi
      exact hsign i hi
    | cons g gates ih =>
      intro m w hlen hsign hclean i hi
      obtain ⟨read, hr, hop, hins⟩ := hclean 0 g (by simp)
      have hr' : read < m := by omega
      obtain ⟨v, b, hv⟩ := hsign read hr'
      let next : (Fin n → Bool) → List Bool := fun x => w x ++ [signedBit (!b) (x v)]
      have step (x : Fin n → Bool) :
          w x ++ [g.op.eval (g.inputs.map fun j => (w x).getD j false)] = next x := by
        simp only [hop, hins, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
          hv, signedBit_flip, next]
      have result : ∃ (j : Fin n) (c : Bool), ∀ x,
          (Circuit.wires ⟨gates, 0⟩ (next x)).getD i false = signedBit c (x j) := by
        apply ih (m + 1) next (by intro x; simp [next, hlen]) ?_ ?_ i (by simp only [List.length_cons] at hi; omega)
        · intro j hj
          by_cases before : j < m
          · obtain ⟨u, c, hu⟩ := hsign j before
            refine ⟨u, c, fun x => ?_⟩
            change (w x ++ [_]).getD j false = _
            rw [List.getD_append _ _ _ _ (by rw [hlen]; exact before)]
            exact hu x
          · have e : j = m := by omega
            subst j
            refine ⟨v, !b, fun x => ?_⟩
            change (w x ++ [_]).getD m false = _
            rw [← hlen x]
            simp
        · intro p a ha
          obtain ⟨j, hj, hop, hins⟩ := hclean (p + 1) a (by simpa using ha)
          exact ⟨j, by omega, hop, hins⟩
      obtain ⟨u, c, hu⟩ := result
      refine ⟨u, c, fun x => ?_⟩
      change (Circuit.wires ⟨gates, 0⟩ (w x ++ [_])).getD i false = _
      rw [step]
      exact hu x
  apply go gs n (fun x => List.ofFn x) (by intro x; simp) ?_ clean
  intro i hi
  refine ⟨⟨i, hi⟩, false, ?_⟩
  intro x
  simp [List.getD_eq_getElem?_getD, hi, signedBit]

lemma signed_same_input_binary (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Bool) :
    (∃ c : Bool, ∀ x : Bool, op.eval [signedBit a x, signedBit b x] = c) ∨
    ∀ x : Bool, op.eval [signedBit a x, signedBit b x] = signedBit a x := by
  rcases hop with rfl | rfl <;> cases a <;> cases b
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inl ⟨false, by intro x; cases x <;> rfl⟩
  · exact Or.inl ⟨false, by intro x; cases x <;> rfl⟩
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inr (by intro x; cases x <;> rfl)
  · exact Or.inl ⟨true, by intro x; cases x <;> rfl⟩
  · exact Or.inl ⟨true, by intro x; cases x <;> rfl⟩
  · exact Or.inr (by intro x; cases x <;> rfl)

lemma signed_binary_control (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (b : Bool) : ∃ v c : Bool, ∀ a : Bool, op.eval [a, signedBit b v] = c := by
  rcases hop with rfl | rfl <;> cases b
  · exact ⟨false, false, by intro a; cases a <;> rfl⟩
  · exact ⟨true, false, by intro a; cases a <;> rfl⟩
  · exact ⟨true, true, by intro a; cases a <;> rfl⟩
  · exact ⟨false, true, by intro a; cases a <;> rfl⟩

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux

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

abbrev Stat := Bool ⊕ Nat

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

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
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
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
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
      simp [simpAnd] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; rfl
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
    simp [opCount, he]

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

namespace CircuitProof

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

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
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
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
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


end CircuitProof
namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs ∧ (∀ x : Fin m → Bool, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

lemma Least.hcl {m f gs o} (L : Least m f gs o) : CleanL m gs := L.1
lemma Least.hev {m f gs o} (L : Least m f gs o) (x : Fin m → Bool) : vl gs x o = f x := L.2.1 x
lemma Least.hmin {m f gs o} (L : Least m f gs o) :
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
      nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length := L.2.2

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
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
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
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
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end LocalSection1

end CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof CircuitProof.Readers

lemma least_no_constant {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (nonconstant : ∃ x y : Fin n → Bool, f x ≠ f y)
    (p : ℕ) (hp : p < gs.length) (c : Bool) :
    ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = c := by
  intro constant
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  obtain ⟨gs', o', hc, hlen, hcost, heval⟩ :=
    drop_core n pre g post L.hcl o (.inl c)
      (fun x => ⟨trivial, (constant x).symm⟩) (L.ncv nonconstant)
  have small : nonNotCount gs' ≤ nonNotCount (pre ++ g :: post) := by
    apply hcost.trans
    simp only [nonNotCount, List.countP_append, List.countP_cons]
    omega
  have minLength := L.hmin gs' o' hc (fun x => (heval x).trans (L.hev x)) small
  omega

lemma least_first_binary_signed {n : ℕ} {f : (Fin n → Bool) → Bool}
    {A B : List Gate} {g : Gate} {o a b : ℕ}
    (L : Least n f (A ++ g :: B) o)
    (nonconstant : ∃ x y : Fin n → Bool, f x ≠ f y)
    (prefixNot : ∀ t ∈ A, t.op = GateOp.not)
    (binary : g.op = GateOp.and ∨ g.op = GateOp.or)
    (inputs : g.inputs = [a, b]) :
    ∃ (u v : Fin n) (sa sb : Bool), u ≠ v ∧
      (∀ x : Fin n → Bool, (wiresFrom A (List.ofFn x)).getD a false = signedBit sa (x u)) ∧
      (∀ x : Fin n → Bool, (wiresFrom A (List.ofFn x)).getD b false = signedBit sb (x v)) := by
  have atGate : (A ++ g :: B)[A.length]? = some g := by simp
  have gateClean := L.hcl A.length g atGate
  have aBound : a < n + A.length := gateClean.lt a (by simp [inputs])
  have bBound : b < n + A.length := gateClean.lt b (by simp [inputs])
  have prefixClean : ∀ (p : ℕ) (t : Gate), A[p]? = some t →
      ∃ j, j < n + p ∧ t.op = GateOp.not ∧ t.inputs = [j] := by
    intro p t ht
    have hp : p < A.length := (List.getElem?_eq_some_iff.mp ht).1
    have full : (A ++ g :: B)[p]? = some t := by
      rw [List.getElem?_append_left hp]
      exact ht
    have notOp := prefixNot t (List.mem_iff_getElem?.mpr ⟨p, ht⟩)
    rcases L.hcl p t full with ⟨_, j, hj, hins⟩ | ⟨hops, j, k, hj, hk, hins⟩
    · exact ⟨j, hj, notOp, hins⟩
    · simp [notOp] at hops
  obtain ⟨u, sa, ha⟩ := not_prefix_signed n A prefixClean a aBound
  obtain ⟨v, sb, hb⟩ := not_prefix_signed n A prefixClean b bBound
  have fullA (x : Fin n → Bool) : vl (A ++ g :: B) x a = signedBit sa (x u) := by
    change (wiresFrom (A ++ g :: B) (List.ofFn x)).getD a false = _
    rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simpa using aBound)]
    exact ha x
  have fullB (x : Fin n → Bool) : vl (A ++ g :: B) x b = signedBit sb (x v) := by
    change (wiresFrom (A ++ g :: B) (List.ofFn x)).getD b false = _
    rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simpa using bBound)]
    exact hb x
  have distinct : u ≠ v := by
    intro same
    subst v
    rcases signed_same_input_binary g.op binary sa sb with ⟨c, constant⟩ | sameInput
    · apply least_no_constant L nonconstant A.length (by simp) c
      intro x
      rw [vl_gate _ L.hcl x A.length g atGate, inputs]
      simpa only [List.map_cons, List.map_nil, fullA, fullB] using constant (x u)
    · apply L.no_alias nonconstant A.length (by simp) a aBound
      intro x
      rw [vl_gate _ L.hcl x A.length g atGate, inputs]
      simpa only [List.map_cons, List.map_nil, fullA, fullB] using sameInput (x u)
  exact ⟨u, v, sa, sb, distinct, ha, hb⟩

lemma split_first_binary (gs : List Gate) (h : ∃ g ∈ gs, g.op ≠ GateOp.not) :
    ∃ (A B : List Gate) (g : Gate), gs = A ++ g :: B ∧
      (∀ t ∈ A, t.op = GateOp.not) ∧ g.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hn : g.op = GateOp.not
    · have tail : ∃ t ∈ gs, t.op ≠ GateOp.not := by
        obtain ⟨t, ht, htNot⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact (htNot hn).elim
        · exact ⟨t, ht, htNot⟩
      obtain ⟨A, B, t, split, allNot, ht⟩ := ih tail
      refine ⟨g :: A, B, t, by simp [split], ?_, ht⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hn
      · exact allNot a ha
    · exact ⟨[], gs, g, rfl, by simp, hn⟩

lemma least_has_binary {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (nonconstant : ∃ x y : Fin n → Bool, f x ≠ f y)
    (notLiteral : ∀ (j : Fin n) (b : Bool), ¬ ∀ x, f x = signedBit b (x j)) :
    ∃ g ∈ gs, g.op ≠ GateOp.not := by
  by_contra! allNot
  have outBound : o < n + gs.length := by
    by_contra! far
    obtain ⟨x, y, different⟩ := L.ncv nonconstant
    apply different
    rw [vl_beyond gs x o far, vl_beyond gs y o far]
  have prefixClean : ∀ (p : ℕ) (g : Gate), gs[p]? = some g →
      ∃ j, j < n + p ∧ g.op = GateOp.not ∧ g.inputs = [j] := by
    intro p g hp
    have hn := allNot g (List.mem_iff_getElem?.mpr ⟨p, hp⟩)
    rcases L.hcl p g hp with ⟨_, j, hj, hins⟩ | ⟨hops, j, k, hj, hk, hins⟩
    · exact ⟨j, hj, hn, hins⟩
    · simp [hn] at hops
  obtain ⟨j, b, hvalue⟩ := not_prefix_signed n gs prefixClean o outBound
  apply notLiteral j b
  intro x
  exact (L.hev x).symm.trans (hvalue x)

lemma least_first_binary {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (nonconstant : ∃ x y : Fin n → Bool, f x ≠ f y)
    (notLiteral : ∀ (j : Fin n) (b : Bool), ¬ ∀ x, f x = signedBit b (x j)) :
    ∃ (A B : List Gate) (g : Gate) (a b : ℕ) (u v : Fin n) (sa sb : Bool),
      gs = A ++ g :: B ∧ (∀ t ∈ A, t.op = GateOp.not) ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs = [a, b] ∧
      u ≠ v ∧
      (∀ x : Fin n → Bool, (wiresFrom A (List.ofFn x)).getD a false = signedBit sa (x u)) ∧
      (∀ x : Fin n → Bool, (wiresFrom A (List.ofFn x)).getD b false = signedBit sb (x v)) := by
  obtain ⟨A, B, g, rfl, prefixNot, nonNot⟩ := split_first_binary gs (least_has_binary L nonconstant notLiteral)
  have atGate : (A ++ g :: B)[A.length]? = some g := by simp
  rcases L.hcl A.length g atGate with ⟨hn, a, ha, hin⟩ | ⟨binary, a, b, ha, hb, hin⟩
  · exact (nonNot hn).elim
  · obtain ⟨u, v, sa, sb, distinct, hu, hv⟩ := least_first_binary_signed L nonconstant prefixNot binary hin
    exact ⟨A, B, g, a, b, u, v, sa, sb, rfl, prefixNot, binary, hin, distinct, hu, hv⟩

end PEqualNP.Outside.L_meta_2592_aux


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


namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds

def satEdgeFunction (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_dependency_witness :
    ∀ u v : Fin 10, u ≠ v → ∀ b : Bool, ∃ w : Fin 10,
      ∀ a : Bool,
        satEdgeFunction (fun i =>
          if i = u then a else if i = v then b else decide (i = w)) = a := by
  decide

lemma sat_cofactor_essential (u v : Fin 10) (huv : u ≠ v) (b : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ u → x i = y i) ∧ x v = b ∧ y v = b ∧
      satEdgeFunction x ≠ satEdgeFunction y := by
  obtain ⟨w, hw⟩ := sat_dependency_witness u v huv b
  refine ⟨(fun i => if i = u then false else if i = v then b else decide (i = w)),
    (fun i => if i = u then true else if i = v then b else decide (i = w)),
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hi]
  · simp [Ne.symm huv]
  · simp [Ne.symm huv]
  · rw [hw false, hw true]
    decide

def satStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma sat_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl satStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, satStep, Nat.add_comm, Nat.add_left_comm]

lemma sat_fold_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl satStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl satStep (satStep x g)).getD i false = _
    rw [ih _ (by simp [satStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma sat_eval_input (C : Circuit) (x : Fin 10 → Bool) (i : Fin 10)
    (output : C.output = i.val) : C.eval (List.ofFn x) = x i := by
  unfold Circuit.eval Circuit.wires
  change (C.gates.foldl satStep (List.ofFn x)).getD C.output false = x i
  rw [output, sat_fold_getD _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_eq_left,
    Option.getD_some]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_edge_avoids :
    ∀ i : Fin 10, ∃ u v : Fin 10,
      (fun j : Fin 10 => decide (j = u ∨ j = v)) i = false ∧
      satEdgeFunction (fun j => decide (j = u ∨ j = v)) = true := by
  decide

lemma sat_nonconstant :
    ∃ x y : Fin 10 → Bool, satEdgeFunction x ≠ satEdgeFunction y := by
  refine ⟨(fun _ => false), (fun j => decide (j = 0 ∨ j = 1)), ?_⟩
  decide

lemma sat_not_signed_input (u : Fin 10) (b : Bool) :
    ¬ (∀ x : Fin 10 → Bool, satEdgeFunction x = if b then !(x u) else x u) := by
  intro computes
  cases b with
  | false =>
    obtain ⟨a, c, zero, one⟩ := sat_edge_avoids u
    have value := computes (fun j => decide (j = a ∨ j = c))
    change satEdgeFunction (fun j => decide (j = a ∨ j = c)) =
      (fun j : Fin 10 => decide (j = a ∨ j = c)) u at value
    rw [one, zero] at value
    cases value
  | true =>
    have value := computes (fun _ => false)
    change false = true at value
    cases value

lemma sat_output_bounds (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) :
    10 ≤ C.output ∧ C.output < 10 + C.size := by
  constructor
  · by_contra! small
    let i : Fin 10 := ⟨C.output, small⟩
    obtain ⟨u, v, zero, one⟩ := sat_edge_avoids i
    let x : Fin 10 → Bool := fun j => decide (j = u ∨ j = v)
    have value : C.eval (List.ofFn x) = false := (sat_eval_input C x i rfl).trans zero
    have target : satEdgeFunction x = true := one
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad
  · by_contra! large
    let x : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have target : satEdgeFunction x = true := by decide
    have length : (C.wires (List.ofFn x)).length = 10 + C.size := by
      change (C.gates.foldl satStep (List.ofFn x)).length = 10 + C.gates.length
      rw [sat_fold_length, List.length_ofFn]
    have value : C.eval (List.ofFn x) = false := by
      apply List.getD_eq_default
      omega
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.Pilot110Floor16

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.Outside.L_meta_2592_aux.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.CircuitProof.Readers

lemma sat_cofactor_nonconstant (u : Fin 10) :
    ∃ x y, satEdgeFunction (Function.update x u false) ≠
      satEdgeFunction (Function.update y u false) := by
  let v : Fin 10 := if u = 0 then 1 else 0
  have hv : v ≠ u := by
    simp only [v]
    split <;> rename_i h
    · subst u; decide
    · exact Ne.symm h
  obtain ⟨x, y, _, hx, hy, hne⟩ := sat_cofactor_essential v u hv false
  have ex : Function.update x u false = x := by
    rw [← hx]
    exact Function.update_eq_self u x
  have ey : Function.update y u false = y := by
    rw [← hy]
    exact Function.update_eq_self u y
  exact ⟨x, y, by simpa only [ex, ey] using hne⟩

theorem petersen_two_drop (C : Circuit) (hf : FanInTwo C)
    (he : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) :
    ∃ (u : Fin 10) (D : Circuit), FanInTwo D ∧
      nonNotCount D.gates + 2 ≤ nonNotCount C.gates ∧
      ∀ x, D.eval (List.ofFn x) = satEdgeFunction (Function.update x u false) := by
  obtain ⟨gs, o, L, budget⟩ := least_with_budget C hf he sat_nonconstant
  obtain ⟨A, B, g, a, b, u, v, sa, sb, rfl, prefixNot, binary, inputs, distinct, hu, hv⟩ :=
    least_first_binary L sat_nonconstant (fun j b => sat_not_signed_input j b)
  have hfan : FanInTwo ⟨A ++ g :: B, o⟩ := by
    intro q hq
    exact (clean_nok 10 _ L.hcl q hq).1
  have hA : nonNotCount A = 0 := by
    apply List.countP_eq_zero.mpr
    intro q hq
    simp [prefixNot q hq, isNotGate]
  have hg : isNotGate g.op = false := by
    rcases binary with h | h <;> rw [h] <;> rfl
  obtain ⟨control, c, hc⟩ := signed_binary_control g.op binary sb
  obtain ⟨x, y, hxy, hxv, hyv, hneq⟩ := sat_cofactor_essential u v distinct control
  have hcontrol : g.op.eval (g.inputs.map fun i =>
      (Pilot110TwoDrop.CircuitProof.wiresFrom A (List.ofFn x)).getD i false)
      = g.op.eval (g.inputs.map fun i =>
      (Pilot110TwoDrop.CircuitProof.wiresFrom A (List.ofFn y)).getD i false) := by
    change g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn x)).getD i false) =
      g.op.eval (g.inputs.map fun i => (wiresFrom A (List.ofFn y)).getD i false)
    simp only [inputs, List.map_cons, List.map_nil, hu, hv, hxv, hyv, hc]
  have hfA : ∀ q ∈ A, Pilot110TwoDrop.CircuitProof.Ok q := by
    intro q hq
    exact hfan q (by simp [hq])
  obtain ⟨constant, hconstant⟩ :=
    Pilot110TwoDrop.Restrict.zero_prefix_literal_constant A hfA hA u a sa hu
  have hgdrop :
      (Pilot110TwoDrop.CircuitProof.simplify g.op
        (10 + (Pilot110TwoDrop.CircuitProof.elim 10 A
          (List.ofFn (Pilot110TwoDrop.Restrict.zeroStats u), [])).2.length)
        (g.inputs.map fun i => (Pilot110TwoDrop.CircuitProof.elim 10 A
          (List.ofFn (Pilot110TwoDrop.Restrict.zeroStats u), [])).1.getD i (Sum.inl false))).1
        = none := by
    rw [inputs]
    exact Pilot110TwoDrop.Restrict.binary_drops_with_constant_input g.op binary _ _ a b constant hconstant
  obtain ⟨D, hD, hcount, hcalc⟩ := Pilot110TwoDrop.Restrict.restrict_two_drop
    A B g o hfan hA hg u satEdgeFunction (fun z => L.hev z)
    (sat_cofactor_nonconstant u) x y hxy hneq hgdrop hcontrol
  refine ⟨u, D, hD, ?_, hcalc⟩
  change nonNotCount D.gates + 2 ≤ nonNotCount (A ++ g :: B) at hcount
  omega

end PEqualNP.Outside.Pilot110Floor16


namespace PEqualNP.Outside.Pilot110SymmetryDeletion

def petersenFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
  x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def edges : List (Fin 10 × Fin 10) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7),
   (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)]

def adjacent (a b : Fin 10) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges

def perm (u v : Fin 10) : Fin 10 :=
  (([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    [2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    [3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    [5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    [6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    [7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    [8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    [9, 6, 8, 5, 7, 4, 1, 3, 0, 2]] : List (List (Fin 10))).getD u.val []).getD v.val 0

lemma perm_zero : ∀ u : Fin 10, perm u 0 = u := by
  decide +kernel

set_option maxHeartbeats 1000000 in
lemma perm_bijective : ∀ u : Fin 10, Function.Bijective (perm u) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
lemma perm_adjacent : ∀ u a b : Fin 10, adjacent (perm u a) (perm u b) ↔ adjacent a b := by
  unfold adjacent edges
  decide +kernel

lemma function_edges (x : Fin 10 → Bool) :
    petersenFunction x = edges.any (fun e => x e.1 && x e.2) := by
  simp [petersenFunction, edges, Bool.or_assoc]

lemma function_true_iff (x : Fin 10 → Bool) :
    petersenFunction x = true ↔
      ∃ a b : Fin 10, adjacent a b ∧ x a = true ∧ x b = true := by
  rw [function_edges]
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, member, ha, hb⟩
    exact ⟨a,b,Or.inl member,ha,hb⟩
  · rintro ⟨a,b,adj,ha,hb⟩
    rcases adj with member | member
    · exact ⟨(a,b),member,ha,hb⟩
    · exact ⟨(b,a),member,hb,ha⟩

lemma petersenFunction_comp_of_adjacent (σ : Fin 10 → Fin 10)
    (bij : Function.Bijective σ)
    (pres : ∀ a b : Fin 10, adjacent (σ a) (σ b) ↔ adjacent a b)
    (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (σ i)) = petersenFunction x := by
  apply Bool.eq_iff_iff.mpr
  rw [function_true_iff, function_true_iff]
  constructor
  · rintro ⟨a,b,adj,ha,hb⟩
    exact ⟨σ a,σ b,(pres a b).mpr adj,ha,hb⟩
  · rintro ⟨a,b,adj,ha,hb⟩
    obtain ⟨a,rfl⟩ := bij.surjective a
    obtain ⟨b,rfl⟩ := bij.surjective b
    exact ⟨a,b,(pres a b).mp adj,ha,hb⟩

lemma petersenFunction_comp_perm (u : Fin 10) (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (perm u i)) = petersenFunction x :=
  petersenFunction_comp_of_adjacent (perm u) (perm_bijective u) (perm_adjacent u) x

def permLast (u v : Fin 10) : Fin 10 :=
  perm u (perm 9 (perm 9 (perm 9 v)))

lemma permLast_last (u : Fin 10) : permLast u 9 = u := by
  change perm u 0 = u
  exact perm_zero u

lemma permLast_bijective (u : Fin 10) : Function.Bijective (permLast u) :=
  (perm_bijective u).comp ((perm_bijective 9).comp
    ((perm_bijective 9).comp (perm_bijective 9)))

lemma permLast_adjacent (u a b : Fin 10) :
    adjacent (permLast u a) (permLast u b) ↔ adjacent a b :=
  (perm_adjacent u _ _).trans ((perm_adjacent 9 _ _).trans
    ((perm_adjacent 9 _ _).trans (perm_adjacent 9 _ _)))

lemma petersenFunction_comp_permLast (u : Fin 10) (x : Fin 10 → Bool) :
    petersenFunction (fun i => x (permLast u i)) = petersenFunction x :=
  petersenFunction_comp_of_adjacent (permLast u) (permLast_bijective u)
    (permLast_adjacent u) x

lemma exists_last_equiv (u : Fin 10) :
    ∃ e : Fin 10 ≃ Fin 10, e 9 = u ∧
      ∀ x : Fin 10 → Bool, petersenFunction (fun i => x (e i)) = petersenFunction x := by
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (permLast u) (permLast_bijective u)
  exact ⟨e, permLast_last u, petersenFunction_comp_permLast u⟩

lemma rename_last_update (F : (Fin 10 → Bool) → Bool) (u : Fin 10)
    (e : Fin 10 ≃ Fin 10) (he : e 9 = u)
    (hinv : ∀ x : Fin 10 → Bool, F (fun i => x (e i)) = F x)
    (y : Fin 9 → Bool) :
    let z : Fin 10 → Bool := fun i => Fin.lastCases false y (e.symm i)
    z u = false ∧ F (Function.update z u false) = F (Fin.lastCases false y) := by
  let z : Fin 10 → Bool := fun i => Fin.lastCases false y (e.symm i)
  change z u = false ∧ F (Function.update z u false) = _
  have zero : z u = false := by
    change Fin.lastCases false y (e.symm u) = false
    rw [← he, Equiv.symm_apply_apply]
    exact Fin.lastCases_last
  have update : Function.update z u false = z := by
    rw [← zero]
    exact Function.update_eq_self u z
  refine ⟨zero, ?_⟩
  rw [update]
  simpa only [z, Equiv.symm_apply_apply] using (hinv z).symm

end PEqualNP.Outside.Pilot110SymmetryDeletion


namespace PEqualNP.Outside.Pilot110Residual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Pilot110TwoDrop.CircuitProof
open PEqualNP.Outside.Pilot110TwoDrop.Restrict
open PEqualNP.Outside.Pilot110SymmetryDeletion

lemma residual_rename (D : Circuit) (hfan : FanInTwo D) (u : Fin 10)
    (hcompute : ∀ x : Fin 10 → Bool,
      D.eval (List.ofFn x) = petersenFunction (Function.update x u false)) :
    ∃ E : Circuit, FanInTwo E ∧ nonNotCount E.gates ≤ nonNotCount D.gates ∧
      ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersenFunction (Fin.lastCases false y) := by
  obtain ⟨e, helast, hinv⟩ := exists_last_equiv u
  let s0 : Fin 10 → Stat := fun i =>
    Fin.lastCases (Sum.inl false) (fun j : Fin 9 => Sum.inr j.val) (e.symm i)
  have valid : ∀ i, Stat.Valid 9 (s0 i) := by
    intro i
    change Stat.Valid 9
      (Fin.lastCases (Sum.inl false) (fun j : Fin 9 => Sum.inr j.val) (e.symm i))
    refine Fin.lastCases ?_ (fun j => ?_) (e.symm i)
    · simp only [Fin.lastCases_last, Stat.Valid]
    · simpa only [Fin.lastCases_castSucc, Stat.Valid] using j.isLt
  have values (y : Fin 9 → Bool) :
      (fun i => Stat.val (List.ofFn y) (s0 i)) =
      (fun i => Fin.lastCases false y (e.symm i)) := by
    funext i
    change Stat.val (List.ofFn y)
      (Fin.lastCases (Sum.inl false) (fun j : Fin 9 => Sum.inr j.val) (e.symm i)) =
        Fin.lastCases false y (e.symm i)
    refine Fin.lastCases ?_ (fun j => ?_) (e.symm i)
    · simp only [Fin.lastCases_last, Stat.val]
    · simpa only [Fin.lastCases_castSucc, Stat.val] using getD_ofFn 9 y false j
  have computes : ∀ y : Fin 9 → Bool,
      D.eval (List.ofFn fun i => Stat.val (List.ofFn y) (s0 i)) =
        petersenFunction (Fin.lastCases false y) := by
    intro y
    rw [values y, hcompute]
    exact (rename_last_update petersenFunction u e helast hinv y).2
  have nonconstant : ∃ y y' : Fin 9 → Bool,
      petersenFunction (Fin.lastCases false y) ≠
        petersenFunction (Fin.lastCases false y') := by
    exact ⟨fun _ => false, fun _ => true, by decide⟩
  exact restrict_core D hfan s0 valid
    (fun y => petersenFunction (Fin.lastCases false y)) computes nonconstant

end PEqualNP.Outside.Pilot110Residual

namespace PEqualNP.Outside.Pilot110Floor17

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.Outside.L_meta_2592_aux.CircuitProof

def deletedEdge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

lemma deleted_function_eq (x : Fin 9 → Bool) :
    Pilot110SymmetryDeletion.petersenFunction (Fin.lastCases false x) = deletedEdge x := by
  change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 4 && false || x 5 && x 7 || x 7 && false ||
    false && x 6 || x 6 && x 8 || x 8 && x 5) = _
  simp only [Bool.and_false, Bool.false_and, Bool.or_false]
  rfl

theorem atLeastSeventeen_of_deleted_floor
    (deletedFloor : ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin 9 → Bool, E.eval (List.ofFn x) = deletedEdge x) →
      15 ≤ nonNotCount E.gates)
    (C : Circuit) (hf : FanInTwo C)
    (he : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) :
    17 ≤ nonNotCount C.gates := by
  obtain ⟨u, D, hD, hcost, hcompute⟩ := Pilot110Floor16.petersen_two_drop C hf he
  obtain ⟨E, hE, hcostE, heE⟩ := Pilot110Residual.residual_rename D hD u hcompute
  have h15 := deletedFloor E hE (fun x => (heE x).trans (deleted_function_eq x))
  change nonNotCount E.gates ≤ nonNotCount D.gates at hcostE
  omega

end PEqualNP.Outside.Pilot110Floor17
