import MemoBoolFastTest
namespace PEqualNP.Outside.L_meta_670_aux.MetadataReplay

open LiveCheck

structure Edge where
  nots : Nat
  wires : List Sig
  hint : Sig → Nat
  cut : Bool

structure Config where
  limit : Nat
  count : Nat → Nat → Nat
  state : Nat → Nat → Nat → List Sig
  enabled : Nat → Nat → Nat → Bool
  transport : (Sig → Nat) → Fin 12 → List Sig → List Sig
  lookup : (Sig → Nat) → Nat → Nat → List Sig → Nat × Fin 12
  terminal : Nat → Nat → Nat → List Sig → Bool
  edges : Nat → Nat → Nat → List Edge

structure Valid (c : Config) : Prop where
  transport : ∀ hint g k t w z, (c.transport hint g w).Perm z →
    Impossible k t z → Impossible k t w
  terminal : ∀ k t j v, c.terminal k t j v = true → Impossible k t v
  cuts : ∀ k t j e, e ∈ c.edges (k+1) t j →
    e.cut = true → Impossible k e.nots e.wires

def linkCheck (c : Config) (hint : Sig → Nat) (k t : Nat) (w : List Sig) : Bool :=
  let found := c.lookup hint k t w
  decide (found.1 < c.count k t) && c.enabled k t found.1 &&
    (c.transport hint found.2 w).isPerm (c.state k t found.1)

lemma linkCheck_sound (c : Config) (hc : Valid c)
    {hint : Sig → Nat} {k t : Nat} {w : List Sig}
    (known : ∀ j < c.count k t, c.enabled k t j = true → Impossible k t (c.state k t j))
    (h : linkCheck c hint k t w = true) : Impossible k t w := by
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at h
  exact hc.transport hint (c.lookup hint k t w).2 k t w _ h.2
    (known _ h.1.1 h.1.2)

def edgeCheck (c : Config) (k : Nat) (e : Edge) : Bool :=
  e.cut || (decide (e.nots ≤ c.limit) && linkCheck c e.hint k e.nots e.wires)

lemma edgeCheck_sound (c : Config) (hc : Valid c) {k : Nat} {e : Edge}
    (known : ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j))
    (cutSound : e.cut = true → Impossible k e.nots e.wires)
    (h : edgeCheck c k e = true) : Impossible k e.nots e.wires := by
  simp only [edgeCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨ht,hl⟩
  · exact cutSound h
  · exact linkCheck_sound c hc (known e.nots ht) hl

def fill (c : Config) (k : Nat) : List Edge → MemoBoolFast.Memo → MemoBoolFast.Memo
  | [], m => m
  | e :: es, m => fill c k es
      (if edgeCheck c k e then MemoBoolFast.save (fun _ _ _ => true) k e.nots e.wires m else m)

lemma fill_sound (c : Config) (hc : Valid c) {k : Nat}
    (known : ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j))
    (es : List Edge)
    (cutSound : ∀ e ∈ es, e.cut = true → Impossible k e.nots e.wires)
    {m : MemoBoolFast.Memo} (hm : MemoBoolFast.Sound m) :
    MemoBoolFast.Sound (fill c k es m) := by
  induction es generalizing m with
  | nil => exact hm
  | cons e es ih =>
    apply ih (fun a ha => cutSound a (List.mem_cons_of_mem e ha))
    split
    · rename_i he
      exact MemoBoolFast.save_sound _ hm
        (edgeCheck_sound c hc known (cutSound e (List.mem_cons_self)) he)
    · exact hm

def nodeCheck (c : Config) (k t j : Nat) : Bool :=
  let v := c.state k t j
  !(c.enabled k t j) || c.terminal k t j v || (BoolNodup.check v &&
    match k with
    | 0 => !(search 0 t v)
    | k+1 =>
      let m := fill c k (c.edges (k+1) t j) .empty
      !(stepTest k t v (fun w => MemoBoolFast.answer k (t-1) w m)
        (fun w => MemoBoolFast.answer k t w m)))

lemma nodeCheck_zero_sound (c : Config) (hc : Valid c) {t j : Nat}
    (he : c.enabled 0 t j = true) (h : nodeCheck c 0 t j = true) :
    Impossible 0 t (c.state 0 t j) := by
  simp only [nodeCheck,he,Bool.not_true,Bool.false_or,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true'] at h
  rcases h with ht | ⟨hn,hs⟩
  · exact hc.terminal 0 t j _ ht
  · exact exclude_search (BoolNodup.sound hn) hs

lemma nodeCheck_succ_sound (c : Config) (hc : Valid c) {k t j : Nat}
    (known : ∀ u ≤ c.limit, ∀ i < c.count k u,
      c.enabled k u i = true → Impossible k u (c.state k u i))
    (he : c.enabled (k+1) t j = true) (h : nodeCheck c (k+1) t j = true) :
    Impossible (k+1) t (c.state (k+1) t j) := by
  simp only [nodeCheck,he,Bool.not_true,Bool.false_or,Bool.or_eq_true,
    Bool.and_eq_true,Bool.not_eq_true'] at h
  rcases h with ht | ⟨hn,hs⟩
  · exact hc.terminal (k+1) t j _ ht
  · have hm : MemoBoolFast.Sound (fill c k (c.edges (k+1) t j) .empty) :=
      fill_sound c hc known _ (hc.cuts k t j) trivial
    apply exclude_step (BoolNodup.sound hn) _ _ hs
    · intro w hw
      exact MemoBoolFast.answer_false hm hw
    · intro w hw
      exact MemoBoolFast.answer_false hm hw

lemma levels_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      nodeCheck c k t j = true) :
    ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j) := by
  intro k
  induction k with
  | zero =>
    intro hk t ht j hj he
    exact nodeCheck_zero_sound c hc he (checks 0 hk t ht j hj)
  | succ k ih =>
    intro hk t ht j hj he
    exact nodeCheck_succ_sound c hc (ih (by omega)) he (checks (k+1) hk t ht j hj)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, start => f start && span f n (start+1)

lemma span_point {f : Nat → Bool} {n start j : Nat}
    (h : span f n start = true) (hs : start ≤ j) (hj : j < start+n) : f j = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h
    by_cases he : j = start
    · simpa only [he] using h.1
    · exact ih h.2 (by omega) (by omega)

lemma span_join {f : Nat → Bool} {a b start : Nat}
    (h₁ : span f a start = true) (h₂ : span f b (start+a) = true) :
    span f (a+b) start = true := by
  induction a generalizing start with
  | zero => simpa only [Nat.zero_add,Nat.add_zero] using h₂
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at h₁
    rw [Nat.succ_add,span,Bool.and_eq_true]
    refine ⟨h₁.1,ih h₁.2 ?_⟩
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₂

lemma span_of_points {f : Nat → Bool} {n start : Nat}
    (h : ∀ j, start ≤ j → j < start+n → f j = true) : span f n start = true := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [span,Bool.and_eq_true]
    exact ⟨h start (by omega) (by omega),ih (fun j hj hjn => h j (by omega) (by omega))⟩

lemma span_of_fin {f : Nat → Bool} {n start : Nat}
    (h : ∀ i : Fin n, f (start+i.val) = true) : span f n start = true := by
  apply span_of_points
  intro j hj hjn
  have hi : j-start < n := by omega
  have he : start+(j-start) = j := by omega
  simpa only [he] using h ⟨j-start,hi⟩

def levelCheck (c : Config) (k t : Nat) : Bool :=
  span (nodeCheck c k t) (c.count k t) 0

def enabledNodes (c : Config) (k t : Nat) : List Nat :=
  (List.range (c.count k t)).filter (c.enabled k t)

lemma levelCheck_of_enabled (c : Config) {k t : Nat}
    (checks : ∀ j ∈ enabledNodes c k t, nodeCheck c k t j = true) :
    levelCheck c k t = true := by
  apply span_of_points
  intro j hj hjn
  by_cases he : c.enabled k t j = true
  · apply checks
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),he⟩
  · have hf : c.enabled k t j = false := by cases h : c.enabled k t j <;> simp_all
    simp only [nodeCheck,hf,Bool.not_false,Bool.true_or]

lemma levelCheck_of_list (c : Config) {k t : Nat} (nodes : List Nat)
    (enumeration : enabledNodes c k t = nodes)
    (checks : ∀ i : Fin nodes.length, nodeCheck c k t nodes[i.val] = true) :
    levelCheck c k t = true := by
  apply levelCheck_of_enabled
  intro j hj
  rw [enumeration] at hj
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hj
  simpa only [he] using checks ⟨i,hi⟩

lemma checked_levels_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, levelCheck c k t = true) :
    ∀ k ≤ budget, ∀ t ≤ c.limit, ∀ j < c.count k t,
      c.enabled k t j = true → Impossible k t (c.state k t j) := by
  apply levels_sound c hc budget
  intro k hk t ht j hj
  exact span_point (checks k hk t ht) (Nat.zero_le j) (by omega)

lemma checked_link_sound (c : Config) (hc : Valid c) (budget : Nat)
    (checks : ∀ k ≤ budget, ∀ t ≤ c.limit, levelCheck c k t = true)
    {hint : Sig → Nat} {k t : Nat} {w : List Sig} (hk : k ≤ budget) (ht : t ≤ c.limit)
    (h : linkCheck c hint k t w = true) : Impossible k t w := by
  exact linkCheck_sound c hc (checked_levels_sound c hc budget checks k hk t ht) h

end PEqualNP.Outside.L_meta_670_aux.MetadataReplay
