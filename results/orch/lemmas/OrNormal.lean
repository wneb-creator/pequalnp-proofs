import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_5112_aux.OrNormal

abbrev Gate := Bool × Nat × Nat
abbrev OrGate := List Nat × List Nat
abbrev Sig (α : Type) := α → Bool

def read {α : Type} (xs : List (Sig α)) (i : Nat) : Sig α := xs.getD i (fun _ => false)

def step {α : Type} (xs : List (Sig α)) (g : Gate) : List (Sig α) :=
  xs ++ [fun r => if g.1 then read xs g.2.1 r || read xs g.2.2 r
    else read xs g.2.1 r && read xs g.2.2 r]

def meet {α : Type} (w : List (Sig α)) (l : List Nat) : Sig α :=
  fun r => l.all (fun j => read w j r)

def orStep {α : Type} (w : List (Sig α)) (g : OrGate) : List (Sig α) :=
  w ++ [fun r => meet w g.1 r || meet w g.2 r]

def ors (gs : List Gate) := gs.countP (fun g => g.1)

def Valid (n : Nat) (env : List (List Nat)) : Prop :=
  ∀ l ∈ env, ∀ j ∈ l, j < n

def Represents {α : Type} (env : List (List Nat)) (xs w : List (Sig α)) : Prop :=
  env.length = xs.length ∧ 0 < w.length ∧ read w 0 = (fun _ => false) ∧
    Valid w.length env ∧ ∀ i r, meet w (env.getD i [0]) r = read xs i r

lemma getD_snoc {α : Type} (xs : List α) (x d : α) (i : Nat) :
    (xs ++ [x]).getD i d = if i = xs.length then x else xs.getD i d := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
  · by_cases he : i = xs.length
    · subst i; simp
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma read_snoc {α : Type} (xs : List (Sig α)) (x : Sig α) (i : Nat) :
    read (xs ++ [x]) i = if i = xs.length then x else read xs i :=
  getD_snoc xs x (fun _ => false) i

lemma read_extend {α : Type} (w : List (Sig α)) (x : Sig α) (i : Nat)
    (hi : i < w.length) : read (w ++ [x]) i = read w i :=
  List.getD_append w [x] (fun _ => false) i hi

lemma meet_append {α : Type} (w : List (Sig α)) (a b : List Nat) (r : α) :
    meet w (a ++ b) r = (meet w a r && meet w b r) := by simp [meet]

lemma meet_extend {α : Type} (w : List (Sig α)) (x : Sig α) (l : List Nat)
    (hl : ∀ j ∈ l, j < w.length) : meet (w ++ [x]) l = meet w l := by
  funext r
  induction l with
  | nil => rfl
  | cons j js ih =>
    have hfirst := read_extend w x j (hl j (by simp))
    have hrest := ih (fun j hj => hl j (by simp [hj]))
    simp only [meet, List.all_cons] at hrest ⊢
    rw [hfirst, hrest]

lemma valid_read {n : Nat} {env : List (List Nat)} (hn : 0 < n) (he : Valid n env)
    (i : Nat) : ∀ j ∈ env.getD i [0], j < n := by
  by_cases hi : i < env.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact he _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    intro j hj
    simpa only [List.mem_singleton.mp hj] using hn

lemma represents_and {α : Type} {env : List (List Nat)} {xs w : List (Sig α)}
    (h : Represents env xs w) (a b : Nat) :
    Represents (env ++ [env.getD a [0] ++ env.getD b [0]]) (step xs (false,a,b)) w := by
  obtain ⟨hl, hp, hz, hv, he⟩ := h
  refine ⟨by simp [step, hl], hp, hz, ?_, ?_⟩
  · intro l hmem j hj
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hv l hmem j hj
    · have heq : l = env.getD a [0] ++ env.getD b [0] := List.mem_singleton.mp hmem
      subst l
      rcases List.mem_append.mp hj with hj | hj
      · exact valid_read hp hv a j hj
      · exact valid_read hp hv b j hj
  · intro i r
    simp only [getD_snoc, step, read_snoc, hl]
    by_cases hi : i = xs.length
    · simp only [hi, ↓reduceIte, meet_append, he, Bool.false_eq_true]
    · simp only [hi, ↓reduceIte]
      exact he i r

lemma represents_or {α : Type} {env : List (List Nat)} {xs w : List (Sig α)}
    (h : Represents env xs w) (a b : Nat) :
    Represents (env ++ [[w.length]]) (step xs (true,a,b))
      (orStep w (env.getD a [0], env.getD b [0])) := by
  obtain ⟨hl, hp, hz, hv, he⟩ := h
  let f := fun r => meet w (env.getD a [0]) r || meet w (env.getD b [0]) r
  change Represents _ _ (w ++ [f])
  refine ⟨by simp [step, hl], by simp, ?_, ?_, ?_⟩
  · rw [read_extend w f 0 hp, hz]
  · intro l hmem j hj
    rcases List.mem_append.mp hmem with hmem | hmem
    · have hj := hv l hmem j hj
      simp only [List.length_append, List.length_singleton]; omega
    · have heq : l = [w.length] := List.mem_singleton.mp hmem
      subst l
      have hj' : j = w.length := List.mem_singleton.mp hj
      simp [hj']
  · intro i r
    simp only [getD_snoc, step, read_snoc, hl]
    by_cases hi : i = xs.length
    · simp only [hi, ↓reduceIte, meet, List.all_cons, List.all_nil, Bool.and_true]
      rw [read_snoc]
      simp only [↓reduceIte, f, he]
    · simp only [hi, ↓reduceIte]
      rw [meet_extend w f _ (valid_read hp hv i)]
      exact he i r

lemma normalize {α : Type} (gs : List Gate) {env : List (List Nat)} {xs w : List (Sig α)}
    (h : Represents env xs w) :
    ∃ (ps : List OrGate) (env' : List (List Nat)), ps.length = ors gs ∧
      Represents env' (gs.foldl step xs) (ps.foldl orStep w) ∧
      ∀ k g, ps[k]? = some g → (∀ j ∈ g.1, j < w.length + k) ∧
        (∀ j ∈ g.2, j < w.length + k) := by
  induction gs generalizing env xs w with
  | nil => exact ⟨[],env,rfl,h,by simp⟩
  | cons g gs ih =>
    rcases g with ⟨op,a,b⟩
    cases op
    · obtain ⟨ps,env',hlen,hrep,hvalid⟩ := ih (represents_and h a b)
      refine ⟨ps,env',?_,hrep,hvalid⟩
      simpa [ors] using hlen
    · obtain ⟨ps,env',hlen,hrep,hvalid⟩ := ih (represents_or h a b)
      refine ⟨(env.getD a [0],env.getD b [0]) :: ps,env',?_,hrep,?_⟩
      · simp [List.length_cons,hlen,ors]
      · intro k g hk
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst g
          exact ⟨by simpa using valid_read h.2.1 h.2.2.2.1 a,
            by simpa using valid_read h.2.1 h.2.2.2.1 b⟩
        | succ k =>
          have hd := hvalid k g hk
          simpa [orStep, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd

lemma initial_represents {α : Type} (xs : List (Sig α)) :
    Represents ((List.range xs.length).map fun i => [i+1]) xs ((fun _ => false) :: xs) := by
  refine ⟨by simp, by simp, rfl, ?_, ?_⟩
  · intro l hl j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have hj' : j = i+1 := List.mem_singleton.mp hj
    simp only [List.mem_range] at hi
    simp [hj']; omega
  · intro i r
    by_cases hi : i < xs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range, meet, List.all_cons, List.all_nil,
        Bool.and_true, read, List.getD_cons_succ]
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp only [meet, List.all_cons, List.all_nil, Bool.and_true, read,
        List.getD_cons_zero, List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]

lemma canonical_or_program {α : Type} (gs : List Gate) (xs : List (Sig α)) (out : Nat) :
    ∃ (ps : List OrGate) (final : List Nat), ps.length = ors gs ∧
      (∀ r, meet (ps.foldl orStep ((fun _ => false) :: xs)) final r =
        read (gs.foldl step xs) out r) ∧
      (∀ k g, ps[k]? = some g → (∀ j ∈ g.1, j < xs.length + 1 + k) ∧
        (∀ j ∈ g.2, j < xs.length + 1 + k)) ∧
      ∀ j ∈ final, j < xs.length + 1 + ps.length := by
  obtain ⟨ps,env,hlen,hrep,hvalid⟩ := normalize gs (initial_represents xs)
  refine ⟨ps,env.getD out [0],hlen,hrep.2.2.2.2 out,?_,?_⟩
  · simpa [Nat.add_comm] using hvalid
  · have hs : (ps.foldl orStep ((fun _ => false) :: xs)).length = xs.length + 1 + ps.length := by
      have length_fold (ls : List OrGate) (w : List (Sig α)) :
          (ls.foldl orStep w).length = w.length + ls.length := by
        induction ls generalizing w with
        | nil => simp
        | cons a ls ih => simp [List.foldl_cons, ih, orStep, Nat.add_assoc, Nat.add_comm]
      simpa [Nat.add_comm] using length_fold ps ((fun _ => false) :: xs)
    simpa [hs] using valid_read hrep.2.1 hrep.2.2.2.1 out

end PEqualNP.Outside.L_meta_5112_aux.OrNormal
