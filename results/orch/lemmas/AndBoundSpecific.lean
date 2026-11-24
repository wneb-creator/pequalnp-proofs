import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Choose
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_meta_5112_aux.AndBound

abbrev Gate := Bool × Nat × Nat
abbrev Sig (α : Type) := α → Bool

def read {α : Type} (xs : List (Sig α)) (i : Nat) : Sig α := xs.getD i (fun _ => false)

def step {α : Type} (xs : List (Sig α)) (g : Gate) : List (Sig α) :=
  xs ++ [fun r => if g.1 then read xs g.2.1 r || read xs g.2.2 r
    else read xs g.2.1 r && read xs g.2.2 r]

def approx {α : Type} : List Gate → List (Sig α) → List (List (Sig α))
  | [], xs => [xs]
  | g :: gs, xs => if g.1 then approx gs (step xs g)
      else approx gs (xs ++ [read xs g.2.1]) ++ approx gs (xs ++ [read xs g.2.2])

def ands (gs : List Gate) := gs.countP (fun g => !g.1)

lemma approx_length {α : Type} (gs : List Gate) (xs : List (Sig α)) :
    (approx gs xs).length = 2 ^ ands gs := by
  induction gs generalizing xs with
  | nil => simp [approx, ands]
  | cons g gs ih =>
    rcases g with ⟨b,a,c⟩
    cases b <;> simp [approx, ands, ih, Nat.pow_succ, Nat.mul_two]

lemma read_append {α : Type} (xs : List (Sig α)) (s : Sig α) (i : Nat) :
    read (xs ++ [s]) i = if i = xs.length then s else read xs i := by
  unfold read
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (Nat.ne_of_lt hi)]
  · by_cases he : i = xs.length
    · subst i; simp
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma step_length {α : Type} (xs : List (Sig α)) (g : Gate) :
    (step xs g).length = xs.length + 1 := by simp [step]

def Dom {α : Type} (xs ys : List (Sig α)) : Prop :=
  xs.length = ys.length ∧ ∀ i r, read xs i r = true → read ys i r = true

lemma Dom.refl {α : Type} (xs : List (Sig α)) : Dom xs xs := ⟨rfl, fun _ _ h => h⟩

lemma Dom.snoc {α : Type} {xs ys : List (Sig α)} (h : Dom xs ys)
    {a b : Sig α} (hab : ∀ r, a r = true → b r = true) :
    Dom (xs ++ [a]) (ys ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i r hi
  simp only [read_append, h.1] at hi ⊢
  by_cases hk : i = ys.length
  · simp only [hk, ↓reduceIte] at hi ⊢
    exact hab r hi
  · simp only [hk, ↓reduceIte] at hi ⊢
    exact h.2 i r hi

lemma Dom.step {α : Type} {xs ys : List (Sig α)} (h : Dom xs ys) (g : Gate) :
    Dom (step xs g) (step ys g) := by
  apply h.snoc
  intro r hr
  cases hb : g.1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, Bool.or_eq_true] at hr ⊢
  · exact ⟨h.2 _ r hr.1, h.2 _ r hr.2⟩
  · exact hr.elim (fun h' => Or.inl (h.2 _ r h')) (fun h' => Or.inr (h.2 _ r h'))

lemma approx_dom {α : Type} (gs : List Gate) {xs ys zs : List (Sig α)}
    (hxy : Dom xs ys) (hz : zs ∈ approx gs ys) : Dom (gs.foldl step xs) zs := by
  induction gs generalizing xs ys zs with
  | nil =>
    simp only [approx, List.mem_singleton] at hz
    subst zs
    exact hxy
  | cons g gs ih =>
    simp only [List.foldl_cons]
    cases hb : g.1
    · simp only [approx, hb, Bool.false_eq_true, ↓reduceIte, List.mem_append] at hz
      rcases hz with hz | hz
      · apply ih (hxy.snoc ?_) hz
        intro r hr
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hr
        exact hxy.2 _ r hr.1
      · apply ih (hxy.snoc ?_) hz
        intro r hr
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hr
        exact hxy.2 _ r hr.2
    · simp only [approx, hb, ↓reduceIte] at hz
      exact ih (hxy.step g) hz

lemma eval_row {α : Type} (gs : List Gate) {xs ys : List (Sig α)} (r : α)
    (hl : xs.length = ys.length) (he : ∀ i, read xs i r = read ys i r) :
    ∀ i, read (gs.foldl step xs) i r = read (gs.foldl step ys) i r := by
  induction gs generalizing xs ys with
  | nil => exact he
  | cons g gs ih =>
    apply ih (by simp [step_length, hl])
    intro i
    simp only [step, read_append, hl]
    split
    · simp only [he]
    · exact he i

lemma approx_cover {α : Type} (gs : List Gate) (xs : List (Sig α)) (r : α) :
    ∃ ys ∈ approx gs xs, ∀ i, read ys i r = read (gs.foldl step xs) i r := by
  induction gs generalizing xs with
  | nil => exact ⟨xs, by simp [approx], fun _ => rfl⟩
  | cons g gs ih =>
    cases hb : g.1
    · let j := if read xs g.2.1 r then g.2.2 else g.2.1
      obtain ⟨ys, hys, he⟩ := ih (xs ++ [read xs j])
      refine ⟨ys, ?_, ?_⟩
      · simp only [approx, hb, Bool.false_eq_true, ↓reduceIte, List.mem_append]
        dsimp only [j] at hys
        cases h : read xs g.2.1 r
        · exact Or.inl (by simpa [h] using hys)
        · exact Or.inr (by simpa [h] using hys)
      · intro i
        rw [he i, List.foldl_cons]
        apply eval_row gs r (by simp [step])
        intro k
        simp only [step, read_append, hb, Bool.false_eq_true, ↓reduceIte]
        split
        · dsimp only [j]
          cases h : read xs g.2.1 r <;> simp [h]
        · rfl
    · simpa only [approx, hb, ↓reduceIte, List.foldl_cons] using ih (step xs g)

lemma read_good {α : Type} {P : Sig α → Prop} (hfalse : P (fun _ => false))
    {xs : List (Sig α)} (h : ∀ f ∈ xs, P f) (i : Nat) : P (read xs i) := by
  by_cases hi : i < xs.length
  · unfold read
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · unfold read
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact hfalse

lemma approx_good {α : Type} {P : Sig α → Prop} (hfalse : P (fun _ => false))
    (hor : ∀ f g, P f → P g → P (fun r => f r || g r))
    (gs : List Gate) {xs ys : List (Sig α)} (hx : ∀ f ∈ xs, P f)
    (hy : ys ∈ approx gs xs) : ∀ f ∈ ys, P f := by
  induction gs generalizing xs ys with
  | nil =>
    simp only [approx, List.mem_singleton] at hy
    subst ys
    exact hx
  | cons g gs ih =>
    have rd := read_good hfalse hx
    have snoc (a) (ha : P a) : ∀ f ∈ xs ++ [a], P f := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hx f hf
      · exact List.mem_singleton.mp hf ▸ ha
    cases hb : g.1
    · simp only [approx, hb, Bool.false_eq_true, ↓reduceIte, List.mem_append] at hy
      exact hy.elim (fun h => ih (snoc _ (rd _)) h) (fun h => ih (snoc _ (rd _)) h)
    · simp only [approx, hb, ↓reduceIte] at hy
      apply ih _ hy
      simpa only [step, hb, ↓reduceIte] using snoc _ (hor _ _ (rd _) (rd _))

def Good {α : Type} {n : Nat} (neg : Fin n → α) (pos : Fin n → Fin n → α)
    (f : Sig α) : Prop :=
  ∀ i j, i ≠ j → f (neg i) = false → f (neg j) = false → f (pos i j) = false

lemma good_false {α : Type} {n : Nat} (neg : Fin n → α) (pos : Fin n → Fin n → α) :
    Good neg pos (fun _ => false) := by intro i j hne hi hj; rfl

lemma good_or {α : Type} {n : Nat} {neg : Fin n → α} {pos : Fin n → Fin n → α}
    (f g : Sig α) (hf : Good neg pos f) (hg : Good neg pos g) :
    Good neg pos (fun r => f r || g r) := by
  intro i j hne hi hj
  simp only [Bool.or_eq_false_iff] at hi hj ⊢
  exact ⟨hf i j hne hi.1 hj.1, hg i j hne hi.2 hj.2⟩

lemma and_count_bound {α : Type} {n : Nat} (neg : Fin n → α) (pos : Fin n → Fin n → α)
    (gs : List Gate) (xs : List (Sig α)) (out : Nat)
    (hxs : ∀ f ∈ xs, Good neg pos f)
    (hneg : ∀ i, read (gs.foldl step xs) out (neg i) = false)
    (hpos : ∀ i j, i ≠ j → read (gs.foldl step xs) out (pos i j) = true) :
    n ≤ 2 ^ ands gs := by
  classical
  let A := approx gs xs
  have choice : ∀ i : Fin n, ∃ j : Fin A.length, read (A.get j) out (neg i) = false := by
    intro i
    obtain ⟨ys, hy, he⟩ := approx_cover gs xs (neg i)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hy
    refine ⟨j, ?_⟩
    change read ((approx gs xs).get j) out (neg i) = false
    rw [hj, he, hneg]
  choose f hf using choice
  have injective : Function.Injective f := by
    intro i j hij
    by_contra hne
    have mem : A.get (f i) ∈ approx gs xs := List.get_mem A (f i)
    have good := read_good (good_false neg pos)
      (approx_good (good_false neg pos) good_or gs hxs mem) out
    have no := good i j hne (hf i) (by rw [hij]; exact hf j)
    have yes := (approx_dom gs (Dom.refl xs) mem).2 out (pos i j) (hpos i j hne)
    exact Bool.noConfusion (no.symm.trans yes)
  have count := Fintype.card_le_of_injective f injective
  simpa only [Fintype.card_fin, A, approx_length] using count

def natStep (xs : List Nat) (g : Gate) : List Nat :=
  xs ++ [if g.1 then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0]

def mapBits (xs : List Nat) : List (Sig Nat) := xs.map fun n r => n.testBit r

lemma read_mapBits (xs : List Nat) (i r : Nat) :
    read (mapBits xs) i r = (xs.getD i 0).testBit r := by
  induction xs generalizing i with
  | nil => simp [mapBits, read]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [mapBits, read] using ih i

lemma mapBits_step (xs : List Nat) (g : Gate) :
    mapBits (natStep xs g) = step (mapBits xs) g := by
  simp only [natStep, mapBits, List.map_append, List.map_cons, List.map_nil, step]
  congr 2
  funext r
  change (if g.1 then xs.getD g.2.1 0 ||| xs.getD g.2.2 0
    else xs.getD g.2.1 0 &&& xs.getD g.2.2 0).testBit r =
      (if g.1 then read (mapBits xs) g.2.1 r || read (mapBits xs) g.2.2 r
        else read (mapBits xs) g.2.1 r && read (mapBits xs) g.2.2 r)
  rw [read_mapBits, read_mapBits]
  cases g.1 <;> simp [Nat.testBit_or, Nat.testBit_and]

lemma mapBits_fold (gs : List Gate) (xs : List Nat) :
    mapBits (gs.foldl natStep xs) = gs.foldl step (mapBits xs) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons, ih, mapBits_step]

def initial : List Nat :=
  [256463372304,8521482511360,14003410187716736,55389823206179104,
   155696362464215096,218994303131713984,183565875465424384,
   229736628136996864,270286071508729856,288160007409369088,
   192860064594267704,288166778660192704,283797140973809664]

def neg (i : Fin 12) : Nat :=
  ([21,23,25,28,32,37,38,42,46,53,55,57] : List Nat).getD i.val 0

def pos (i j : Fin 12) : Nat :=
  ([0,4,7,10,13,7,15,4,19,4,10,4,
    4,0,4,4,4,4,5,7,5,13,5,7,
    7,4,0,8,7,10,8,4,7,4,8,4,
    10,4,8,0,11,8,10,4,11,4,15,4,
    13,4,7,11,0,7,13,4,14,4,11,4,
    7,4,10,8,7,0,8,4,7,4,8,4,
    15,5,8,10,13,8,0,5,17,5,10,5,
    4,7,4,4,4,4,5,0,5,7,5,10,
    19,5,7,11,14,7,17,5,0,5,11,5,
    4,13,4,4,4,4,5,7,5,0,5,7,
    10,5,8,15,11,8,10,5,11,5,0,5,
    4,7,4,4,4,4,5,10,5,7,5,0] : List Nat).getD (12 * i.val + j.val) 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma initial_good : ∀ f ∈ mapBits initial, Good neg pos f := by
  have cert : initial.all (fun v => decide (∀ i j : Fin 12, i ≠ j →
      v.testBit (neg i) = false → v.testBit (neg j) = false →
      v.testBit (pos i j) = false)) = true := by
    decide +kernel
  intro f hf
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hf
  unfold Good
  exact of_decide_eq_true (List.all_eq_true.mp cert v hv)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma target_negative : ∀ i : Fin 12, (1764784 : Nat).testBit (neg i) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma target_positive : ∀ i j : Fin 12, i ≠ j → (1764784 : Nat).testBit (pos i j) = true := by
  decide +kernel

lemma at_least_four_ands (gs : List Gate) (out : Nat)
    (houtput : (gs.foldl natStep initial).getD out 0 = 1764784) : 4 ≤ ands gs := by
  have bound := and_count_bound neg pos gs (mapBits initial) out initial_good
    (fun i => by rw [← mapBits_fold, read_mapBits, houtput]; exact target_negative i)
    (fun i j hij => by rw [← mapBits_fold, read_mapBits, houtput]; exact target_positive i j hij)
  by_contra h
  have hk : ands gs ≤ 3 := by omega
  interval_cases hval : ands gs <;> norm_num [hval] at bound

end PEqualNP.Outside.L_meta_5112_aux.AndBound
