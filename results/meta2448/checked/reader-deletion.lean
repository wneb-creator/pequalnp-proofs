import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Compiler primitives adapted from the accepted L_meta_2453 proof.

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ ℕ

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
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

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

def MonoGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma mono_nok (g : Gate) (h : MonoGate g) : NOk g := by
  refine ⟨⟨?_, h.2⟩, ?_⟩
  · rcases h.1 with ha | ho
    · exact Or.inl ha
    · exact Or.inr (Or.inl ho)
  · intro hn
    rcases h.1 with ha | ho <;> simp_all

lemma simplify_mono (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, MonoGate g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at hg <;> (subst hg; simp [MonoGate])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at hg <;> (subst hg; simp [MonoGate])

lemma elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MonoGate g) → (∀ g ∈ acc.2, MonoGate g) →
    ∀ g ∈ (elim n gs acc).2, MonoGate g := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs hacc
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hacc g' h
    · exact simplify_mono _ _ _ (hgs g List.mem_cons_self).1 g' (by simpa using h)

def readerCount (k : ℕ) (gs : List Gate) : ℕ :=
  gs.countP (fun g => decide (k ∈ g.inputs))

theorem elim_readers (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MonoGate g) → k < acc.1.length →
    acc.1.getD k (Sum.inl false) = Sum.inl false →
    (elim n gs acc).2.length + readerCount k gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim, readerCount]
  | cons g gs ih =>
    intro acc hmono hk hc
    have hstep : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hk' : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      change (acc.1 ++ [_]).getD k _ = _
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hi := ih (elimStep n acc g)
      (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) hk' hc'
    rw [hstep]
    by_cases hread : k ∈ g.inputs
    · have hn := mono_nok g (hmono g List.mem_cons_self)
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        exact simplify_count _ _ _ hn.1.1 (by simpa using hn.1.2)
          (fun h => by simpa using hn.2 h)
          ⟨false, List.mem_map.mpr ⟨k, hread, hc⟩⟩
      have hlen : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      simp [readerCount, hread] at *
      omega
    · have hlen : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp [readerCount, hread] at *
      omega

def seed (n : ℕ) (pre : List Gate) : List Stat × List Gate :=
  (List.ofFn (fun i : Fin (n + pre.length) => (Sum.inr i.val : Stat)) ++
    [Sum.inl false], pre)

def lowered (n : ℕ) (pre post : List Gate) : List Stat × List Gate :=
  elim n post (seed n pre)

theorem lowered_size (n : ℕ) (pre post : List Gate)
    (hmono : ∀ g ∈ post, MonoGate g) :
    (lowered n pre post).2.length + readerCount (n + pre.length) post + 1 ≤
      pre.length + 1 + post.length := by
  have h := elim_readers n (n + pre.length) post (seed n pre) hmono
    (by simp [seed]) (by simp [seed])
  change (lowered n pre post).2.length + readerCount (n + pre.length) post ≤
    pre.length + post.length at h
  omega

lemma seed_inv (n : ℕ) (pre : List Gate) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x) ++ [false]) (seed n pre) := by
  have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
    rw [length_wiresFrom, List.length_ofFn]
  refine ⟨by simp [seed, hl], ?_⟩
  intro i
  by_cases hi : i = n + pre.length
  · subst i
    simp only [seed]
    rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ hl]
    exact ⟨trivial, rfl⟩
  · simp only [seed]
    rw [getD_snoc_ne _ _ _ _ (by simpa using hi), getD_snoc_ne _ _ _ _ (by simpa [hl] using hi)]
    by_cases hlt : i < n + pre.length
    · simp [hlt, Stat.Valid, Stat.val]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

def forcedEval (n : ℕ) (pre post : List Gate) (out : ℕ) (x : Fin n → Bool) : Bool :=
  (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [false])).getD out false

lemma lowered_correct (n : ℕ) (pre post : List Gate) (out : ℕ)
    (hmono : ∀ g ∈ post, MonoGate g) (x : Fin n → Bool) :
    ((lowered n pre post).1.getD out (Sum.inl false)).Valid
        (n + (lowered n pre post).2.length) ∧
      ((lowered n pre post).1.getD out (Sum.inl false)).val
        (wiresFrom (lowered n pre post).2 (List.ofFn x)) = forcedEval n pre post out x := by
  exact (inv_elim n (List.ofFn x) (by simp) post _ (seed n pre)
    (fun g hg => (mono_nok g (hmono g hg)).1) (seed_inv n pre x)).2 out

theorem reader_deletion_circuit (n : ℕ) (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, MonoGate g) (hpost : ∀ g ∈ post, MonoGate g)
    (hzero : forcedEval n pre post out (fun _ => false) = false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + readerCount (n + pre.length) post + 1 ≤ pre.length + 1 + post.length ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = forcedEval n pre post out x := by
  let acc := lowered n pre post
  have hM : ∀ g ∈ acc.2, MonoGate g := elim_mono n post (seed n pre) hpost hpre
  have hlen := lowered_size n pre post hpost
  have hval := lowered_correct n pre post out hpost
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have h := (hval (fun _ => false)).2
      change (acc.1.getD out (Sum.inl false)).val _ = _ at h
      rw [hs] at h
      exact h.trans hzero
    subst b
    refine ⟨⟨acc.2, n + acc.2.length⟩, hM, hlen, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = _
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_ofFn])]
    exact h
  | inr w =>
    refine ⟨⟨acc.2, w⟩, hM, hlen, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    exact h

theorem three_readers_delete_four (n : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C)
    (hread : 3 ≤ readerCount (n + pre.length) post)
    (hzero : forcedEval n pre post C.output (fun _ => false) = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 4 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = forcedEval n pre post C.output x := by
  have hpre : ∀ h ∈ pre, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  obtain ⟨D, hD, hsize, heval⟩ := reader_deletion_circuit n pre post C.output hpre hpost hzero
  refine ⟨D, hD, ?_, heval⟩
  have hlen : C.size = pre.length + 1 + post.length := by
    simp [Circuit.size, hC]
    omega
  omega

end PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
