import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure

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

end PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure

namespace PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure

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

end PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure

namespace PEqualNP.Outside.L_meta_2590_aux.MonoFirst

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof.Readers

def MonoL (gs : List Gate) : Prop := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

lemma elimStep_mono (n : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (ha : MonoL acc.2) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    MonoL (elimStep n acc g).2 := by
  intro q hq
  change q ∈ acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ha q hq
  · have hopt : q ∈ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 := by simpa using hq
    rw [simplify_same_op _ _ _ q hopt]
    exact hg

lemma elim_mono (n : ℕ) (gs : List Gate) (hg : MonoL gs)
    (acc : List Stat × List Gate) (ha : MonoL acc.2) : MonoL (elim n gs acc).2 := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    apply ih (fun q hq => hg q (List.mem_cons_of_mem g hq))
    exact elimStep_mono n acc g ha (hg g (by simp))

theorem drop_core_mono (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (hm : MonoL (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ MonoL gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
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
    refine ⟨_, j, hc3, ?_, hlen, ?_, ?_⟩
    · apply elim_mono k post (fun q hq => hm q (by simp [hq]))
      apply elim_mono k pre (fun q hq => hm q (by simp [hq]))
      intro q hq; simp at hq
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem clean_mono {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hmono : Monotone2 C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ MonoL gs ∧ gs.length ≤ C.size ∧ ∀ x, vl gs x o = f x := by
  have mono : MonoL C.gates := by intro g hg; simpa using (hmono g hg).1
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, (hmono g hg).2⟩
    rcases mono g hg with h | h <;> simp [h]
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
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · exact elim_mono n C.gates mono (idStats n, []) (by intro g hg; simp at hg)
    · simpa [hacc, Circuit.size] using elim_len n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

def LeastMono (n : ℕ) (f : (Fin n → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL n gs ∧ MonoL gs ∧ (∀ x, vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL n gs' → MonoL gs' →
      (∀ x, vl gs' x o' = f x) → gs.length ≤ gs'.length

theorem least_mono {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hmono : Monotone2 C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, LeastMono n f gs o ∧ gs.length ≤ C.size := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ MonoL gs ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, mono, count, he⟩ := clean_mono C hmono hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, mono, he, rfl⟩
  obtain ⟨gs', o', hc, hm, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, hm, he', ?_⟩, ?_⟩
  · intro testGates testOut testClean testMono testEval
    exact hl.trans_le (Nat.find_min' existsAdmissible
      (show admissible testGates.length from ⟨testGates, testOut, testClean, testMono, testEval, rfl⟩))
  · exact (hl.trans_le (Nat.find_min' existsAdmissible
      (show admissible gs.length from ⟨gs, o, clean, mono, he, rfl⟩))).trans count

theorem least_mono_first {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : LeastMono n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (notInput : ∀ j : Fin n, ¬ ∀ x, f x = x j) :
    ∃ (g : Gate) (B : List Gate) (u v : Fin n), gs = g :: B ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs = [u.val, v.val] ∧ u ≠ v := by
  have nc : ∃ x y : Fin n → Bool, vl gs x o ≠ vl gs y o := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by simpa only [L.2.2.1] using h⟩
  cases gs with
  | nil =>
    by_cases ho : o < n
    · exfalso
      apply notInput ⟨o, ho⟩
      intro x
      exact (L.2.2.1 x).symm.trans (vl_input [] x o ho)
    · obtain ⟨x, y, hxy⟩ := nc
      have bound : n + ([] : List Gate).length ≤ o := by simp; omega
      rw [vl_beyond [] x o bound, vl_beyond [] y o bound] at hxy
      exact (hxy rfl).elim
  | cons g B =>
    have binary := L.2.1 g (by simp)
    have clean := L.1 0 g (by simp)
    rcases clean with ⟨hn, a, ha, inputs⟩ | ⟨_, a, b, ha, hb, inputs⟩
    · simp [hn] at binary
    · have hab : a ≠ b := by
        intro eq
        subst b
        have gv : ∀ x : Fin n → Bool, vl (g :: B) x n = x ⟨a, by omega⟩ := by
          intro x
          have e := vl_gate (g :: B) L.1 x 0 g (by simp)
          simp only [Nat.add_zero, inputs, List.map_cons, List.map_nil] at e
          rw [vl_input (g :: B) x a (by omega)] at e
          rcases binary with hop | hop <;> simpa [hop, GateOp.eval] using e
        obtain ⟨gs', o', hc, hm, shorter, _, he⟩ := drop_core_mono n [] g B L.1 L.2.1 o
          (Sum.inr a) (by
            intro x
            refine ⟨by simpa [elim, Stat.Valid] using ha, ?_⟩
            change (List.ofFn x).getD a false = vl (g :: B) x n
            rw [gv x]
            exact getD_ofFn n x false ⟨a, by omega⟩) nc
        have hmin := L.2.2.2 gs' o' hc hm (fun x => (he x).trans (L.2.2.1 x))
        simp only [List.nil_append] at shorter
        omega
      exact ⟨g, B, ⟨a, by omega⟩, ⟨b, by omega⟩, rfl, binary, inputs,
        fun h => hab (congrArg Fin.val h)⟩

end PEqualNP.Outside.L_meta_2590_aux.MonoFirst

namespace PEqualNP.Outside.L_meta_2590_aux.MonoFirst
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof.Readers
theorem drop_alias_mono (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (hm : MonoL gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ MonoL gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core_mono k pre g post hcl hm o ((elim k pre (idStats k, [])).1.getD j (Sum.inl false))
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
theorem drop_dead_mono (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (hm : MonoL gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ MonoL gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
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
  have hmono' : MonoL gs' := by
    intro q hq
    obtain ⟨r, hr⟩ := List.mem_iff_getElem?.mp hq
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr
      cases hr
      exact Or.inl rfl
    · rw [hget_ne r hrp] at hr
      exact hm q (List.mem_iff_getElem?.mpr ⟨r, hr⟩)
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
  obtain ⟨gs'', o'', hc'', hm'', hl'', hcost, he''⟩ :=
    drop_alias_mono k gs' hcl' hmono' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', hm'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

lemma least_mono_gate_read {n : ℕ} {f : (Fin n → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (L : LeastMono n f gs o)
    (hnc : ∃ x y, f x ≠ f y) (p : ℕ) (hp : p < gs.length) (ho : o ≠ n + p) :
    ∃ q, Reads gs q (n + p) := by
  by_contra h
  have hno : ∀ q, ¬ Reads gs q (n + p) := by
    intro q hq
    exact h ⟨q, hq⟩
  have nc : ∃ x y : Fin n → Bool, vl gs x o ≠ vl gs y o := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, by rw [L.2.2.1 x, L.2.2.1 y]; exact hxy⟩
  obtain ⟨gs', o', hc, hm, hl, _, he⟩ := drop_dead_mono n gs L.1 L.2.1 o p hp ho hno nc
  have low := L.2.2.2 gs' o' hc hm (fun x => (he x).trans (L.2.2.1 x))
  omega

end PEqualNP.Outside.L_meta_2590_aux.MonoFirst


namespace PEqualNP.Outside.L_meta_2590_aux.ReaderBridge

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma append_agree_except (u : ℕ) (w z : List Bool) (b c : Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) (same : b = c) :
    ∀ i, i ≠ u → (w ++ [b]).getD i false = (z ++ [c]).getD i false := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
    exact agree i hi
  · by_cases heq : i = w.length
    · subst i
      rw [show (w ++ [b]).getD w.length false = b by simp, lengths]
      simpa using same
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma fold_agree_except (u : ℕ) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ u) (w z : List Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) :
    ∀ i, i ≠ u → (gs.foldl step w).getD i false = (gs.foldl step z).getD i false := by
  induction gs generalizing w z with
  | nil => exact agree
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (avoid g (by simp) i hi)
    exact ih (fun q hq => avoid q (List.mem_cons_of_mem g hq))
      (step w g) (step z g) (by simp [step, lengths])
      (append_agree_except u w z _ _ lengths agree same)

lemma ofFn_agree_except {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) :
    ∀ i, i ≠ u.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    exact agree ⟨i,hlt⟩ (fun h => hi (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)]

lemma first_gate_masks_unique_read {n : ℕ} (u v : Fin n) (g : Gate) (gs : List Gate)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val)
    (out : ℕ) (out_ne : out ≠ u.val) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) (xv : x v = b) (yv : y v = b) :
    (Circuit.mk (g :: gs) out).eval (List.ofFn x) =
      (Circuit.mk (g :: gs) out).eval (List.ofFn y) := by
  have masked (z : Fin n → Bool) (hz : z v = b) :
      g.op.eval (g.inputs.map fun i => (List.ofFn z).getD i false) = b := by
    rcases pins with hp | hp <;> rcases control with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ <;>
      simp [hp, hop, GateOp.eval, hz]
  have initial := append_agree_except u.val (List.ofFn x) (List.ofFn y) _ _
    (by simp) (ofFn_agree_except u x y agree) ((masked x xv).trans (masked y yv).symm)
  exact fold_agree_except u.val gs avoid (step (List.ofFn x) g) (step (List.ofFn y) g)
    (by simp [step]) initial out out_ne

lemma first_gate_must_read_again {n : ℕ} (f : (Fin n → Bool) → Bool)
    (u v : Fin n) (g : Gate) (gs : List Gate) (out : ℕ)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (out_ne : out ≠ u.val)
    (essential : ∃ x y : Fin n → Bool, (∀ i, i ≠ u → x i = y i) ∧
      x v = b ∧ y v = b ∧ f x ≠ f y)
    (computes : ∀ x : Fin n → Bool, (Circuit.mk (g :: gs) out).eval (List.ofFn x) = f x) :
    ∃ q ∈ gs, u.val ∈ q.inputs := by
  by_contra h
  have avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val := by
    intro q hq i hi eq
    subst i
    exact h ⟨q,hq,hi⟩
  obtain ⟨x,y,agree,xv,yv,different⟩ := essential
  have same := first_gate_masks_unique_read u v g gs pins b control avoid out out_ne x y agree xv yv
  rw [computes x, computes y] at same
  exact different same

end PEqualNP.Outside.L_meta_2590_aux.ReaderBridge


namespace PEqualNP.Outside.L_meta_2590_aux.Cofactor

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

lemma sat_gate_count_partition (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    C.size = C.gates.countP (fun g => !g.op.eval [false]) + PEqualNP.NotBracket.notCount C := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  let isNot : Gate → Bool := fun g => decide (g.op = GateOp.not)
  have negSame : (fun g : Gate => decide (¬ isNot g = true)) = (fun g => !isNot g) := by
    funext g
    cases isNot g <;> rfl
  have eqCount : C.gates.countP (fun g => !isNot g) =
      C.gates.countP (fun g => !g.op.eval [false]) := by
    apply List.countP_congr
    intro g hg
    obtain ⟨op, ins⟩ := g
    have hop := (fan _ hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with (h | h | h) <;> change op = _ at h <;> subst op <;> rfl
  have eqNot : C.gates.countP isNot = PEqualNP.NotBracket.notCount C := by
    rw [List.countP_eq_length_filter]
    rfl
  have count := List.length_eq_countP_add_countP isNot (l := C.gates)
  rw [negSame, eqCount, eqNot] at count
  simpa only [Circuit.size, Nat.add_comm] using count

lemma sat_not_bound (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (k : ℕ) (floor : k ≤ C.gates.countP (fun g => !g.op.eval [false])) :
    k + PEqualNP.NotBracket.notCount C ≤ C.size := by
  rw [sat_gate_count_partition C fan]
  omega

end PEqualNP.Outside.L_meta_2590_aux.Cofactor


namespace PEqualNP.Outside.L_meta_2590_aux.PinBudget

open scoped BigOperators

lemma tight_nineteen_budget
    (inputs : Fin 10 → ℕ) (uses : Fin 19 → ℕ) (output : Fin 19)
    (input_lb : ∀ i, 2 ≤ inputs i)
    (gate_lb : ∀ j, j ≠ output → 1 ≤ uses j)
    (total : (∑ i, inputs i) + (∑ j, uses j) ≤ 38) :
    (∀ i, inputs i = 2) ∧
      (∀ j, uses j = if j = output then 0 else 1) := by
  classical
  let base : Fin 19 → ℕ := fun j => if j = output then 0 else 1
  have base_le : ∀ j, base j ≤ uses j := by
    intro j
    by_cases h : j = output
    · simp [base, h]
    · simpa [base, h] using gate_lb j h
  have base_sum : (∑ j, base j) = 18 := by
    have split : (∑ _j : Fin 19, 1) =
        (∑ j : Fin 19, if j = output then 1 else 0) + ∑ j, base j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = output <;> simp [base, h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at split
    omega
  have input_sum : 20 ≤ ∑ i, inputs i := by
    calc
      20 = ∑ _i : Fin 10, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => input_lb i
  have gate_sum : 18 ≤ ∑ j, uses j := by
    calc
      18 = ∑ j, base j := base_sum.symm
      _ ≤ _ := Finset.sum_le_sum fun j _ => base_le j
  constructor
  · intro i
    by_contra h
    have strict : 2 < inputs i := by have := input_lb i; omega
    have hs : (∑ _j : Fin 10, 2) < ∑ j, inputs j :=
      Finset.sum_lt_sum (fun j _ => input_lb j) ⟨i, Finset.mem_univ i, strict⟩
    have : 20 < ∑ j, inputs j := by simpa using hs
    omega
  · intro j
    change uses j = base j
    by_contra h
    have strict : base j < uses j := by have := base_le j; omega
    have hs : (∑ k, base k) < ∑ k, uses k :=
      Finset.sum_lt_sum (fun k _ => base_le k) ⟨j, Finset.mem_univ j, strict⟩
    rw [base_sum] at hs
    omega

lemma sum_count_le_length (xs : List ℕ) (S : Finset ℕ) :
    (∑ i ∈ S, xs.count i) ≤ xs.length := by
  have restricted : (∑ i ∈ S, xs.count i) = ∑ i ∈ S ∩ xs.toFinset, xs.count i := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hn
    have no : i ∉ xs := by
      intro hm
      exact hn (Finset.mem_inter.mpr ⟨hi, List.mem_toFinset.mpr hm⟩)
    exact List.count_eq_zero.mpr no
  rw [restricted]
  calc
    (∑ i ∈ S ∩ xs.toFinset, xs.count i) ≤ ∑ i ∈ xs.toFinset, xs.count i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => Nat.zero_le _)
    _ = xs.length := List.sum_toFinset_count_eq_length xs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pins (C : Circuit) : List ℕ := C.gates.flatMap Gate.inputs

lemma pins_length_bound (C : Circuit) (h : Monotone2 C) :
    (pins C).length ≤ 2 * C.size := by
  have aux : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro arity
      have hg := arity g (by simp)
      have hs := ih (fun a ha => arity a (List.mem_cons_of_mem g ha))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  exact aux C.gates (fun g hg => (h g hg).2)

lemma circuit_nineteen_no_sharing (C : Circuit) (h : Monotone2 C)
    (size : C.size = 19) (output : Fin 19)
    (inputs : ∀ i : Fin 10, 2 ≤ (pins C).count i.val)
    (live : ∀ j : Fin 19, j ≠ output → 1 ≤ (pins C).count (10 + j.val)) :
    (∀ i : Fin 10, (pins C).count i.val = 2) ∧
      (∀ j : Fin 19, (pins C).count (10 + j.val) =
        if j = output then 0 else 1) := by
  apply tight_nineteen_budget (fun i => (pins C).count i.val)
    (fun j => (pins C).count (10 + j.val)) output inputs live
  have bound : (∑ i : Fin 10, (pins C).count i.val) +
      (∑ j : Fin 19, (pins C).count (10 + j.val)) ≤ (pins C).length := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (pins C).count i) 10,
      Fin.sum_univ_eq_sum_range (fun j => (pins C).count (10 + j)) 19,
      ← Finset.sum_range_add]
    exact sum_count_le_length (pins C) (Finset.range 29)
  have len := pins_length_bound C h
  rw [size] at len
  omega

lemma nineteen_primary_once_or_no_sharing (C : Circuit) (h : Monotone2 C)
    (size : C.size = 19) (output : Fin 19)
    (essential : ∀ i : Fin 10, 1 ≤ (pins C).count i.val)
    (live : ∀ j : Fin 19, j ≠ output → 1 ≤ (pins C).count (10 + j.val)) :
    (∃ i : Fin 10, (pins C).count i.val = 1) ∨
      ((∀ i : Fin 10, (pins C).count i.val = 2) ∧
        (∀ j : Fin 19, (pins C).count (10 + j.val) =
          if j = output then 0 else 1)) := by
  classical
  by_cases twice : ∀ i : Fin 10, 2 ≤ (pins C).count i.val
  · exact Or.inr (circuit_nineteen_no_sharing C h size output twice live)
  · push_neg at twice
    obtain ⟨i, hi⟩ := twice
    left
    refine ⟨i, ?_⟩
    have := essential i
    omega

end PEqualNP.Outside.L_meta_2590_aux.PinBudget

namespace PEqualNP.Outside.L_meta_2590_aux.Liveness
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof
open PEqualNP.Outside.L_meta_2590_aux.FirstInfrastructure.CircuitProof.Readers
open PEqualNP.Outside.L_meta_2590_aux.MonoFirst
open PEqualNP.Outside.L_meta_2590_aux.Cofactor
open PEqualNP.Outside.L_meta_2590_aux.ReaderBridge
open PEqualNP.Outside.L_meta_2590_aux.PinBudget

lemma petersen_input_used (C : Circuit)
    (he : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) (u : Fin 10) :
    1 ≤ (pins C).count u.val := by
  have used : u.val ∈ pins C := by
    by_contra absent
    have avoid : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≠ u.val := by
      intro g hg i hi eq
      subst i
      apply absent
      exact List.mem_flatMap.mpr ⟨g, hg, hi⟩
    let v : Fin 10 := if u = 0 then 1 else 0
    have huv : u ≠ v := by
      simp only [v]
      split <;> rename_i h
      · subst u; decide
      · exact h
    obtain ⟨x, y, agree, _, _, different⟩ := sat_cofactor_essential u v huv false
    have output := (sat_output_bounds C he).1
    have same := fold_agree_except u.val C.gates avoid (List.ofFn x) (List.ofFn y)
      (by simp) (ofFn_agree_except u x y agree) C.output (by omega)
    change C.eval (List.ofFn x) = C.eval (List.ofFn y) at same
    rw [he x, he y] at same
    exact different same
  have pos := List.count_pos_iff.mpr used
  omega

lemma least_mono_gate_used {n : ℕ} {f : (Fin n → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (L : LeastMono n f gs o)
    (hnc : ∃ x y, f x ≠ f y) (p : ℕ) (hp : p < gs.length) (ho : o ≠ n + p) :
    1 ≤ (pins ⟨gs, o⟩).count (n + p) := by
  obtain ⟨q, g, hg, hpin⟩ := least_mono_gate_read L hnc p hp ho
  have mem : n + p ∈ pins ⟨gs, o⟩ :=
    List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨q, hg⟩, hpin⟩
  have pos := List.count_pos_iff.mpr mem
  omega

end PEqualNP.Outside.L_meta_2590_aux.Liveness
