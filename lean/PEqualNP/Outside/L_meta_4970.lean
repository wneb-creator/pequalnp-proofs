import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Basic
import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card) {a a' : Fin p}
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  exact hC4 a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma star_leaf_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {P : Finset (Fin p)} (hP : 2 ≤ P.card) {b b' : Fin l}
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  exact hC4 a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma pure_or_support_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (S T : Finset α)
    (h : ∀ x : β → Bool,
      decide (∃ a ∈ S, x (f a) = true) = decide (∃ a ∈ T, x (f a) = true)) : S = T := by
  classical
  ext a
  have hi := h (fun b => decide (b = f a))
  simpa [hf.eq_iff] using hi

lemma below_pure_or_iff {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true) :
    (∀ x, f x = true → ∃ i ∈ S, x i = true) ↔
      f (fun i => decide (i ∉ S)) = false := by
  constructor
  · intro h
    cases hcomp : f (fun i => decide (i ∉ S)) with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hni⟩ := h _ hcomp
      simp [hi] at hni
  · intro h x hx
    by_contra hn
    have hle : ∀ i, x i = true → decide (i ∉ S) = true := by
      intro i hi
      simp only [decide_eq_true_eq]
      intro his
      exact hn ⟨i, his, hi⟩
    have hc := hf x (fun i => decide (i ∉ S)) hle hx
    rw [h] at hc
    contradiction

lemma and_below_pure_or {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (h : ∀ x, (f x && g x) = true → ∃ i ∈ S, x i = true) :
    (∀ x, f x = true → ∃ i ∈ S, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ S, x i = true) := by
  by_cases hfc : f (fun i => decide (i ∉ S)) = false
  · exact Or.inl ((below_pure_or_iff S f hf).mpr hfc)
  · right
    apply (below_pure_or_iff S g hg).mpr
    cases hgc : g (fun i => decide (i ∉ S)) with
    | false => rfl
    | true =>
      have hft : f (fun i => decide (i ∉ S)) = true := by
        cases he : f (fun i => decide (i ∉ S)) <;> simp_all
      obtain ⟨i, hi, hni⟩ := h (fun i => decide (i ∉ S)) (by rw [hft, hgc]; rfl)
      simp [hi] at hni

def singletonSupport {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) : Finset α :=
  Finset.univ.filter fun i => f (fun j => decide (j = i)) = true

lemma mem_singletonSupport {α : Type} [Fintype α] [DecidableEq α]
    (f : (α → Bool) → Bool) (i : α) :
    i ∈ singletonSupport f ↔ f (fun j => decide (j = i)) = true := by
  simp [singletonSupport]

lemma singletonSupport_pureOr {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    singletonSupport (fun x => decide (∃ i ∈ S, x i = true)) = S := by
  ext i
  simp [singletonSupport]

lemma singletonSupport_and {α : Type} [Fintype α] [DecidableEq α]
    (f g : (α → Bool) → Bool) :
    singletonSupport (fun x => f x && g x) = singletonSupport f ∩ singletonSupport g := by
  ext i
  simp [singletonSupport]

lemma singletonSupport_or {α : Type} [Fintype α] [DecidableEq α]
    (f g : (α → Bool) → Bool) :
    singletonSupport (fun x => f x || g x) = singletonSupport f ∪ singletonSupport g := by
  ext i
  simp [singletonSupport]

lemma singletonSupport_subset {α : Type} [Fintype α] [DecidableEq α]
    (f g : (α → Bool) → Bool) (h : ∀ x, f x = true → g x = true) :
    singletonSupport f ⊆ singletonSupport g := by
  intro i hi
  exact (mem_singletonSupport g i).mpr (h _ ((mem_singletonSupport f i).mp hi))

lemma singletonSupport_subset_of_below_or {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → ∃ i ∈ S, x i = true) : singletonSupport f ⊆ S := by
  intro i hi
  obtain ⟨j, hj, hji⟩ := h _ ((mem_singletonSupport f i).mp hi)
  have : j = i := by simpa using hji
  simpa [this] using hj

lemma nontrivial_support_unique_centre {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (f : (Fin l → Bool) → Bool) (hf : 2 ≤ (singletonSupport f).card)
    {Q Q' : Finset (Fin l)} {a a' : Fin p}
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E)
    (hQ : ∀ x, f x = true → ∃ b ∈ Q, x b = true)
    (hQ' : ∀ x, f x = true → ∃ b ∈ Q', x b = true) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < (singletonSupport f).card)
  have hsub := singletonSupport_subset_of_below_or Q f hQ
  have hsub' := singletonSupport_subset_of_below_or Q' f hQ'
  exact hC4 a a' b b' hne hbb'
    ⟨ha b (hsub hb), ha b' (hsub hb'), ha' b (hsub' hb), ha' b' (hsub' hb')⟩

lemma selected_forest_card {α : Type} [DecidableEq α]
    (G O L : Finset α) (children : α → Finset α) (r : α)
    (hr : r ∈ G) (hO : O ⊆ G) (hLG : Disjoint L G)
    (hcover : L ∪ G.erase r ⊆ G.biUnion children)
    (hdegree : ∀ g ∈ G, (children g).card ≤ 1 + if g ∈ O then 1 else 0) :
    L.card ≤ O.card + 1 := by
  have hdis : Disjoint L (G.erase r) := hLG.mono_right (Finset.erase_subset r G)
  have hlow : L.card + (G.erase r).card ≤ ∑ g ∈ G, (children g).card := by
    calc
      L.card + (G.erase r).card = (L ∪ G.erase r).card :=
        (Finset.card_union_of_disjoint hdis).symm
      _ ≤ (G.biUnion children).card := Finset.card_le_card hcover
      _ ≤ ∑ g ∈ G, (children g).card := Finset.card_biUnion_le
  have hfilter : G.filter (fun g => g ∈ O) = O := by
    ext g
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hO h, h⟩⟩
  have hupp : (∑ g ∈ G, (children g).card) ≤ G.card + O.card := by
    calc
      (∑ g ∈ G, (children g).card) ≤ ∑ g ∈ G, (1 + if g ∈ O then 1 else 0) :=
        Finset.sum_le_sum hdegree
      _ = G.card + (G.filter (fun g => g ∈ O)).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
          simp
      _ = G.card + O.card := by rw [hfilter]
  have herase := Finset.card_erase_add_one hr
  omega

lemma pure_or_and_prime {α : Type*} (S : Set α) (f g : Set α → Prop)
    (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x ∧ g x) ↔ ∃ a ∈ S, a ∈ x) :
    (∀ x, f x ↔ ∃ a ∈ S, a ∈ x) ∨
      (∀ x, g x ↔ ∃ a ∈ S, a ∈ x) := by
  classical
  have hfalse : ¬ (f Sᶜ ∧ g Sᶜ) := by
    intro hx
    obtain ⟨a, ha, hna⟩ := (h Sᶜ).mp hx
    exact hna ha
  rcases not_and_or.mp hfalse with hf0 | hg0
  · left
    intro x
    constructor
    · intro hx
      by_contra hn
      have hs : x ⊆ Sᶜ := by
        intro a hax has
        exact hn ⟨a, has, hax⟩
      exact hf0 (hf hs hx)
    · intro hx
      exact ((h x).mpr hx).1
  · right
    intro x
    constructor
    · intro hx
      by_contra hn
      have hs : x ⊆ Sᶜ := by
        intro a hax has
        exact hn ⟨a, has, hax⟩
      exact hg0 (hg hs hx)
    · intro hx
      exact ((h x).mpr hx).2

def StarFunction {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool) (c : Fin (p + l)) : Prop :=
  (∃ (a : Fin p) (Q : Finset (Fin l)), c = Fin.castAdd l a ∧
    2 ≤ Q.card ∧ (∀ b ∈ Q, (a, b) ∈ E) ∧
    ∀ x, f x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) ∨
  (∃ (b : Fin l) (P : Finset (Fin p)), c = Fin.natAdd p b ∧
    2 ≤ P.card ∧ (∀ a ∈ P, (a, b) ∈ E) ∧
    ∀ x, f x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true))

lemma pure_or_cross_ne {p l : ℕ} (Q : Finset (Fin l)) (P : Finset (Fin p))
    (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ a ∈ P, x (Fin.castAdd l a) = true)) := by
  intro h
  let x : Fin (p + l) → Bool := fun i => decide (p ≤ i.val)
  have hl : ∀ a : Fin p, x (Fin.castAdd l a) = false := by
    intro a
    simp [x, Nat.not_le.mpr a.isLt]
  have hr : ∀ b : Fin l, x (Fin.natAdd p b) = true := by
    intro b
    simp [x]
  have he := h x
  have ht : decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) = true := by
    exact decide_eq_true (hQ.imp fun b hb => ⟨hb, hr b⟩)
  have hf : decide (∃ a ∈ P, x (Fin.castAdd l a) = true) = false := by
    simp [hl]
  simp [ht, hf] at he

lemma star_function_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {f : (Fin (p + l) → Bool) → Bool} {c c' : Fin (p + l)}
    (hc : StarFunction E f c) (hc' : StarFunction E f c') : c = c' := by
  rcases hc with ⟨a, Q, rfl, hQ, ha, hf⟩ | ⟨b, P, rfl, hP, hb, hf⟩
  · rcases hc' with ⟨a', Q', rfl, hQ', ha', hf'⟩ | ⟨b', P', rfl, hP', hb', hf'⟩
    · have hQQ : Q = Q' := pure_or_support_eq (Fin.natAdd p)
        (by intro i j h; exact Fin.ext (by simpa using congrArg Fin.val h)) Q Q'
        (by intro x; simpa using (hf x).symm.trans (hf' x))
      subst Q'
      exact congrArg (Fin.castAdd l) (star_centre_unique E hC4 hQ ha ha')
    · exact False.elim (pure_or_cross_ne Q P'
        (Finset.card_pos.mp (by omega)) (fun x => (hf x).symm.trans (hf' x)))
  · rcases hc' with ⟨a', Q', rfl, hQ', ha', hf'⟩ | ⟨b', P', rfl, hP', hb', hf'⟩
    · exact False.elim (pure_or_cross_ne Q' P
        (Finset.card_pos.mp (by omega)) (fun x => (hf' x).symm.trans (hf x)))
    · have hPP : P = P' := pure_or_support_eq (Fin.castAdd l)
        (by intro i j h; exact Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h)) P P'
        (by intro x; simpa using (hf x).symm.trans (hf' x))
      subst P'
      exact congrArg (Fin.natAdd p) (star_leaf_unique E hC4 hP hb hb')

lemma cover_of_star_functions {p l k : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (f : Fin k → (Fin (p + l) → Bool) → Bool)
    (hw : ∀ a b, (a, b) ∈ E → ∃ j,
      StarFunction E (f j) (Fin.castAdd l a) ∨
        StarFunction E (f j) (Fin.natAdd p b)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ k := by
  classical
  let S : Finset (Fin (p + l)) := Finset.univ.filter fun c => ∃ j, StarFunction E (f j) c
  have hs : ∀ c ∈ S, ∃ j, StarFunction E (f j) c := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  let pick : {c // c ∈ S} → Fin k := fun c => Classical.choose (hs c.val c.property)
  have hpick : Function.Injective pick := by
    intro c c' he
    apply Subtype.ext
    have hc := Classical.choose_spec (hs c.val c.property)
    have hc' := Classical.choose_spec (hs c'.val c'.property)
    change StarFunction E (f (pick c)) c.val at hc
    change StarFunction E (f (pick c')) c'.val at hc'
    rw [he] at hc
    exact star_function_unique hC4 hc hc'
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    obtain ⟨j, hj | hj⟩ := hw a b hab
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj⟩)
  · simpa using Fintype.card_le_of_injective pick hpick

namespace Semantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

lemma circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

lemma W_nil (w : List Bool) : W [] w = w := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

lemma W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

lemma W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

lemma W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

lemma val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

lemma circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

lemma and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

lemma or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

end Semantics

noncomputable def downCone (children : ℕ → Finset ℕ) (r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (r + 1)).filter fun w =>
    Relation.ReflTransGen (fun a b => b ∈ children a) r w

lemma downReach_le (children : ℕ → Finset ℕ)
    (hback : ∀ a b, b ∈ children a → b < a) {r w : ℕ}
    (h : Relation.ReflTransGen (fun a b => b ∈ children a) r w) : w ≤ r := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hbc hc ih => exact (hback b c hc).le.trans ih

lemma mem_downCone_iff (children : ℕ → Finset ℕ)
    (hback : ∀ a b, b ∈ children a → b < a) (r w : ℕ) :
    w ∈ downCone children r ↔ Relation.ReflTransGen (fun a b => b ∈ children a) r w := by
  classical
  simp only [downCone, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by have := downReach_le children hback h; omega, h⟩⟩

lemma downCone_root (children : ℕ → Finset ℕ) (r : ℕ) : r ∈ downCone children r := by
  classical
  simp only [downCone, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Relation.ReflTransGen.refl⟩

lemma downCone_child (children : ℕ → Finset ℕ)
    (hback : ∀ a b, b ∈ children a → b < a) {r a b : ℕ}
    (ha : a ∈ downCone children r) (hb : b ∈ children a) : b ∈ downCone children r := by
  apply (mem_downCone_iff children hback r b).mpr
  exact ((mem_downCone_iff children hback r a).mp ha).tail hb

lemma support_descends_to_leaf {α : Type} [DecidableEq α]
    (support : ℕ → Finset α) (children : ℕ → Finset ℕ)
    (hback : ∀ a b, b ∈ children a → b < a)
    (hflow : ∀ a, 2 ≤ (support a).card → support a ⊆ (children a).biUnion support)
    (r : ℕ) {a : ℕ} (ha : a ∈ downCone children r) {i : α} (hi : i ∈ support a) :
    ∃ b ∈ downCone children r, (support b).card ≤ 1 ∧ i ∈ support b := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    by_cases hsmall : (support a).card ≤ 1
    · exact ⟨a, ha, hsmall, hi⟩
    · have hbig : 2 ≤ (support a).card := by omega
      obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp (hflow a hbig hi)
      exact ih b (hback a b hb) (downCone_child children hback ha hb) hib

lemma pruned_support_card {α : Type} [DecidableEq α]
    (support : ℕ → Finset α) (children : ℕ → Finset ℕ) (isOr : ℕ → Prop)
    [DecidablePred isOr]
    (hback : ∀ a b, b ∈ children a → b < a)
    (hstop : ∀ a, (support a).card ≤ 1 → children a = ∅)
    (hflow : ∀ a, 2 ≤ (support a).card → support a ⊆ (children a).biUnion support)
    (hdegree : ∀ a, (children a).card ≤ 1 + if isOr a then 1 else 0)
    (r : ℕ) :
    (support r).card ≤ ((downCone children r).filter isOr).card + 1 := by
  classical
  by_cases hsmall : (support r).card ≤ 1
  · omega
  have hbig : 2 ≤ (support r).card := by omega
  let D := downCone children r
  let G := D.filter fun a => 2 ≤ (support a).card
  let L := D.filter fun a => (support a).card ≤ 1
  let O := G.filter isOr
  have hrD : r ∈ D := downCone_root children r
  have hrG : r ∈ G := Finset.mem_filter.mpr ⟨hrD, hbig⟩
  have hO : O ⊆ G := Finset.filter_subset _ _
  have hLG : Disjoint L G := by
    apply Finset.disjoint_left.mpr
    intro a haL haG
    have ha1 := (Finset.mem_filter.mp haL).2
    have ha2 := (Finset.mem_filter.mp haG).2
    omega
  have hcover : L ∪ G.erase r ⊆ G.biUnion children := by
    intro a ha
    have haD : a ∈ D := by
      rcases Finset.mem_union.mp ha with haL | haG
      · exact (Finset.mem_filter.mp haL).1
      · exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase haG)).1
    have har : a ≠ r := by
      rcases Finset.mem_union.mp ha with haL | haG
      · intro he
        subst a
        have := (Finset.mem_filter.mp haL).2
        omega
      · exact Finset.ne_of_mem_erase haG
    have hreach := (mem_downCone_iff children hback r a).mp haD
    rcases hreach.cases_tail with he | ⟨b, hb, hba⟩
    · exact (har he).elim
    · have hbD : b ∈ D := (mem_downCone_iff children hback r b).mpr hb
      have hbG : b ∈ G := by
        apply Finset.mem_filter.mpr
        refine ⟨hbD, ?_⟩
        by_contra hnb
        have he := hstop b (by omega)
        rw [he] at hba
        exact Finset.notMem_empty a hba
      exact Finset.mem_biUnion.mpr ⟨b, hbG, hba⟩
  have hdeg : ∀ a ∈ G, (children a).card ≤ 1 + if a ∈ O then 1 else 0 := by
    intro a ha
    simpa only [O, Finset.mem_filter, ha, true_and] using hdegree a
  have hforest := selected_forest_card G O L children r hrG hO hLG hcover hdeg
  have hsupport : support r ⊆ L.biUnion support := by
    intro i hi
    obtain ⟨a, haD, hasmall, hia⟩ :=
      support_descends_to_leaf support children hback hflow r hrD hi
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨haD, hasmall⟩, hia⟩
  have hleaves : (support r).card ≤ L.card := by
    calc
      (support r).card ≤ (L.biUnion support).card := Finset.card_le_card hsupport
      _ ≤ ∑ a ∈ L, (support a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ L, 1 := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2
      _ = L.card := by simp
  have hOrSub : O ⊆ D.filter isOr := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1,
      (Finset.mem_filter.mp ha).2⟩
  have hOrCard := Finset.card_le_card hOrSub
  change (support r).card ≤ (D.filter isOr).card + 1
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Semantics

noncomputable def wireSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  singletonSupport (fun x => val C (List.ofFn x) w)

lemma wireSupport_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    wireSupport n C w = {⟨w, hw⟩} := by
  ext i
  simp only [wireSupport, mem_singletonSupport, val_ofFn_lt C _ w hw,
    decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma wireSupport_ge (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireSupport n C w = ∅ := by
  ext i
  simp only [wireSupport, mem_singletonSupport]
  rw [val_ge (n := n) (by simp) hw]
  simp

lemma wireSupport_large_gate (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : 2 ≤ (wireSupport n C w).card) : n ≤ w ∧ w < n + C.gates.length := by
  constructor
  · by_contra h
    have he := wireSupport_input n C w (by omega)
    rw [he] at hw
    simp at hw
  · by_contra h
    have he := wireSupport_ge n C w (by omega)
    rw [he] at hw
    simp at hw

noncomputable def maskedSupport (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (w : ℕ) : Finset (Fin n) :=
  if val C (List.ofFn fun i => decide (i ∉ S)) w = false then wireSupport n C w else ∅

lemma maskedSupport_large (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ)
    (hw : 2 ≤ (maskedSupport n C S w).card) :
    val C (List.ofFn fun i => decide (i ∉ S)) w = false ∧
      2 ≤ (wireSupport n C w).card ∧ n ≤ w ∧ w < n + C.gates.length := by
  unfold maskedSupport at hw
  split_ifs at hw with h
  · exact ⟨h, hw, wireSupport_large_gate n C w hw⟩
  · simp at hw

noncomputable def goodOrWire (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or ∧
    2 ≤ (wireSupport n C w).card ∧ val C (List.ofFn fun i => decide (i ∉ S)) w = false

lemma exists_pruned_children (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S : Finset (Fin n)) [DecidablePred (goodOrWire n C S)] (w : ℕ) :
    ∃ L : Finset ℕ,
      (∀ v ∈ L, v < w) ∧
      (2 ≤ (maskedSupport n C S w).card → maskedSupport n C S w ⊆ L.biUnion (maskedSupport n C S)) ∧
      (L.card ≤ 1 + (if goodOrWire n C S w then 1 else 0)) ∧
      ((maskedSupport n C S w).card ≤ 1 → L = ∅) := by
  classical
  by_cases hbig : 2 ≤ (maskedSupport n C S w).card
  · obtain ⟨hc, hlarge, hn, hlen⟩ := maskedSupport_large n C S w hbig
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hwj : n + j = w := by dsimp [j]; omega
    have hinputs : (gateAt C j).inputs.length = 2 := hC.2.2 _ (gateAt_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hinputs
    have ha : a < w := by
      have := hC.2.1 j hj a (by simp [hab])
      omega
    have hb : b < w := by
      have := hC.2.1 j hj b (by simp [hab])
      omega
    have hop := hC.1 _ (gateAt_mem hj)
    rcases hop with hop | hop
    · have hval : ∀ x : Fin n → Bool,
          val C (List.ofFn x) w = (val C (List.ofFn x) a && val C (List.ofFn x) b) := by
        intro x
        simpa [hwj, hab] using and_val n C hC (List.ofFn x) (by simp) j hj hop
      have hs : wireSupport n C w = wireSupport n C a ∩ wireSupport n C b := by
        unfold wireSupport
        rw [show (fun x => val C (List.ofFn x) w) =
          (fun x => val C (List.ofFn x) a && val C (List.ofFn x) b) by funext x; exact hval x]
        exact singletonSupport_and _ _
      by_cases hca : val C (List.ofFn fun i => decide (i ∉ S)) a = false
      · refine ⟨{a}, ?_, ?_, ?_, ?_⟩
        · intro v hv
          have : v = a := Finset.mem_singleton.mp hv
          simpa [this] using ha
        · intro _ i hi
          rw [maskedSupport, if_pos hc, hs] at hi
          apply Finset.mem_biUnion.mpr
          refine ⟨a, by simp, ?_⟩
          rw [maskedSupport, if_pos hca]
          exact (Finset.mem_inter.mp hi).1
        · simp
        · intro hsmall
          omega
      · have hcb : val C (List.ofFn fun i => decide (i ∉ S)) b = false := by
          have he := hval (fun i => decide (i ∉ S))
          rw [hc] at he
          cases hfa : val C (List.ofFn fun i => decide (i ∉ S)) a <;>
            cases hfb : val C (List.ofFn fun i => decide (i ∉ S)) b <;> simp_all
        refine ⟨{b}, ?_, ?_, ?_, ?_⟩
        · intro v hv
          have : v = b := Finset.mem_singleton.mp hv
          simpa [this] using hb
        · intro _ i hi
          rw [maskedSupport, if_pos hc, hs] at hi
          apply Finset.mem_biUnion.mpr
          refine ⟨b, by simp, ?_⟩
          rw [maskedSupport, if_pos hcb]
          exact (Finset.mem_inter.mp hi).2
        · simp
        · intro hsmall
          omega
    · have hval : ∀ x : Fin n → Bool,
          val C (List.ofFn x) w = (val C (List.ofFn x) a || val C (List.ofFn x) b) := by
        intro x
        simpa [hwj, hab] using or_val n C hC (List.ofFn x) (by simp) j hj hop
      have hs : wireSupport n C w = wireSupport n C a ∪ wireSupport n C b := by
        unfold wireSupport
        rw [show (fun x => val C (List.ofFn x) w) =
          (fun x => val C (List.ofFn x) a || val C (List.ofFn x) b) by funext x; exact hval x]
        exact singletonSupport_or _ _
      have hcc : val C (List.ofFn fun i => decide (i ∉ S)) a = false ∧
          val C (List.ofFn fun i => decide (i ∉ S)) b = false := by
        have he := hval (fun i => decide (i ∉ S))
        rw [hc] at he
        cases hfa : val C (List.ofFn fun i => decide (i ∉ S)) a <;>
          cases hfb : val C (List.ofFn fun i => decide (i ∉ S)) b <;> simp_all
      refine ⟨{a, b}, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ha
        · have : v = b := Finset.mem_singleton.mp hv
          simpa [this] using hb
      · intro _ i hi
        rw [maskedSupport, if_pos hc, hs] at hi
        rcases Finset.mem_union.mp hi with hi | hi
        · apply Finset.mem_biUnion.mpr
          refine ⟨a, by simp, ?_⟩
          rw [maskedSupport, if_pos hcc.1]
          exact hi
        · apply Finset.mem_biUnion.mpr
          refine ⟨b, by simp, ?_⟩
          rw [maskedSupport, if_pos hcc.2]
          exact hi
      · have hg : goodOrWire n C S w := ⟨hn, hlen, hop, hlarge, hc⟩
        rw [if_pos hg]
        calc
          ({a, b} : Finset ℕ).card ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      · intro hsmall
        omega
  · refine ⟨∅, by simp, ?_, by simp, by simp⟩
    intro h
    exact (hbig h).elim

noncomputable def goodOrWires (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.gates.length)).filter (goodOrWire n C S)

lemma pure_or_card_le_goodOrWires (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S : Finset (Fin n)) (r : ℕ)
    (hroot : ∀ x : Fin n → Bool,
      val C (List.ofFn x) r = decide (∃ i ∈ S, x i = true)) :
    S.card ≤ (goodOrWires n C S).card + 1 := by
  classical
  choose children hback hflow hdegree hstop using exists_pruned_children n C hC S
  have hb : ∀ a b, b ∈ children a → b < a := by
    intro a b hb
    exact hback a b hb
  have hs : ∀ a, (maskedSupport n C S a).card ≤ 1 → children a = ∅ := hstop
  have hf : ∀ a, 2 ≤ (maskedSupport n C S a).card →
      maskedSupport n C S a ⊆ (children a).biUnion (maskedSupport n C S) := hflow
  have hcard := pruned_support_card (maskedSupport n C S) children (goodOrWire n C S)
    hb hs hf hdegree r
  have hfalse : val C (List.ofFn fun i => decide (i ∉ S)) r = false := by
    rw [hroot]
    simp
  have hsupport : wireSupport n C r = S := by
    ext i
    simp [wireSupport, singletonSupport, hroot]
  have hmask : maskedSupport n C S r = S := by
    rw [maskedSupport, if_pos hfalse, hsupport]
  rw [hmask] at hcard
  have hsub : (downCone children r).filter (goodOrWire n C S) ⊆ goodOrWires n C S := by
    intro a ha
    have hg := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hg.2.1, hg⟩
  have hc := Finset.card_le_card hsub
  omega

lemma wireSupport_subset_of_complement_false (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (S : Finset (Fin n)) (w : ℕ)
    (hw : val C (List.ofFn fun i => decide (i ∉ S)) w = false) :
    wireSupport n C w ⊆ S := by
  apply singletonSupport_subset_of_below_or S (fun x => val C (List.ofFn x) w)
  apply (below_pure_or_iff S (fun x => val C (List.ofFn x) w) ?_).mpr hw
  intro x y hxy hf
  exact mono n C hC.1 x y hxy w hf

lemma goodOrWires_disjoint (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 1) :
    Disjoint (goodOrWires n C S) (goodOrWires n C T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwS hwT
  have hs := (Finset.mem_filter.mp hwS).2
  have ht := (Finset.mem_filter.mp hwT).2
  have hsubS := wireSupport_subset_of_complement_false n C hC S w hs.2.2.2.2
  have hsubT := wireSupport_subset_of_complement_false n C hC T w ht.2.2.2.2
  have hsub : wireSupport n C w ⊆ S ∩ T := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hsubS hi, hsubT hi⟩
  have hc := Finset.card_le_card hsub
  have hlarge := hs.2.2.2.1
  omega

lemma pure_or_family_gate_bound {κ : Type} [DecidableEq κ]
    (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (F : Finset κ) (sets : κ → Finset (Fin n)) (roots : κ → ℕ)
    (hroot : ∀ k ∈ F, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (roots k) = decide (∃ i ∈ sets k, x i = true))
    (hsep : ∀ k ∈ F, ∀ k' ∈ F, k ≠ k' → (sets k ∩ sets k').card ≤ 1) :
    (∑ k ∈ F, ((sets k).card - 1)) ≤ C.size := by
  classical
  have hp : (F : Set κ).PairwiseDisjoint (fun k => goodOrWires n C (sets k)) := by
    intro k hk k' hk' hne
    exact goodOrWires_disjoint n C hC _ _ (hsep k hk k' hk' hne)
  have hbound : (∑ k ∈ F, ((sets k).card - 1)) ≤
      ∑ k ∈ F, (goodOrWires n C (sets k)).card := by
    apply Finset.sum_le_sum
    intro k hk
    have := pure_or_card_le_goodOrWires n C hC (sets k) (roots k) (hroot k hk)
    omega
  have hsub : (F.biUnion fun k => goodOrWires n C (sets k)) ⊆ Finset.Ico n (n + C.gates.length) := by
    intro w hw
    obtain ⟨k, hk, hw⟩ := Finset.mem_biUnion.mp hw
    have hg := (Finset.mem_filter.mp hw).2
    exact Finset.mem_Ico.mpr ⟨hg.1, hg.2.1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hp] at hc
  have hIco : (Finset.Ico n (n + C.gates.length)).card = C.size := by
    simp [Circuit.size]
  rw [hIco] at hc
  exact hbound.trans hc

namespace OutputLedger

open PEqualNP.MetaComplexity
open Semantics

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

lemma orAncestor_false_of_output_false (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hOut : circuitFun n C x = false) (j : ℕ)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    val C (List.ofFn x) (n + j) = false := by
  cases hv : val C (List.ofFn x) (n + j) with
  | false => rfl
  | true =>
    have hf := reach_up n C (List.ofFn x) (by simp) j hv C.output hr
    change val C (List.ofFn x) C.output = false at hOut
    rw [hOut] at hf
    contradiction

def singletonAssignment {n : ℕ} (u : Fin n) : Fin n → Bool := fun v => decide (v = u)

lemma output_orCone_singleton_false (n : ℕ) (C : Circuit)
    (hOut : ∀ u : Fin n, circuitFun n C (singletonAssignment u) = false)
    (j : ℕ) (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    ∀ u : Fin n, val C (List.ofFn (singletonAssignment u)) (n + j) = false := by
  intro u
  exact orAncestor_false_of_output_false n C (singletonAssignment u) (hOut u) j hr

lemma singleton_live_not_output_orCone (n : ℕ) (C : Circuit)
    (hOut : ∀ u : Fin n, circuitFun n C (singletonAssignment u) = false)
    (j : ℕ) (hu : ∃ u : Fin n, val C (List.ofFn (singletonAssignment u)) (n + j) = true) :
    ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output j := by
  intro hr
  obtain ⟨u, hu⟩ := hu
  have hf := output_orCone_singleton_false n C hOut j hr u
  rw [hf] at hu
  contradiction

lemma singleton_live_disjoint_output_orCone (n : ℕ) (C : Circuit)
    (hOut : ∀ u : Fin n, circuitFun n C (singletonAssignment u) = false) :
    Disjoint {j | ∃ u : Fin n, val C (List.ofFn (singletonAssignment u)) (n + j) = true}
      {j | PEqualNP.CleanedNonEdge.OrReaches n C C.output j} := by
  rw [Set.disjoint_left]
  intro j hu hr
  exact singleton_live_not_output_orCone n C hOut j hu hr

end OutputLedger

def bipartiteFun {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have he := congrArg (fun i : Fin (p + l) => i.val) h
  change a.val = p + b.val at he
  have ha := a.isLt
  omega

lemma right_ne_left {p l : ℕ} (b : Fin l) (a : Fin p) :
    Fin.natAdd p b ≠ Fin.castAdd l a := Ne.symm (left_ne_right a b)

lemma bipartiteFun_singleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (u : Fin (p + l)) :
    bipartiteFun E (fun i => decide (i = u)) = false := by
  apply decide_eq_false
  rintro ⟨a, b, hab, ha, hb⟩
  have ha' : Fin.castAdd l a = u := of_decide_eq_true ha
  have hb' : Fin.natAdd p b = u := of_decide_eq_true hb
  exact left_ne_right a b (ha'.trans hb'.symm)

lemma bipartiteFun_pair {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l) :
    bipartiteFun E (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)) =
      decide ((a, b) ∈ E) := by
  have hleft : ∀ a' : Fin p, Fin.castAdd l a' = Fin.castAdd l a ↔ a' = a := by
    intro a'
    exact ⟨fun h => Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h), fun h => congrArg _ h⟩
  have hright : ∀ b' : Fin l, Fin.natAdd p b' = Fin.natAdd p b ↔ b' = b := by
    intro b'
    constructor
    · intro h
      apply Fin.ext
      have he := congrArg (fun i : Fin (p + l) => i.val) h
      change p + b'.val = p + b.val at he
      omega
    · exact congrArg _
  simp [bipartiteFun, hleft, hright, left_ne_right, right_ne_left]

lemma bipartiteFun_left_pair {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a a' : Fin p) :
    bipartiteFun E (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.castAdd l a')) = false := by
  simp [bipartiteFun, right_ne_left]

lemma bipartiteFun_right_pair {p l : ℕ} (E : Finset (Fin p × Fin l))
    (b b' : Fin l) :
    bipartiteFun E (fun i => decide (i = Fin.natAdd p b ∨ i = Fin.natAdd p b')) = false := by
  simp [bipartiteFun, left_ne_right]

lemma singletonSupport_embedded_or {α β : Type} [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (Q : Finset α) :
    singletonSupport (fun x => decide (∃ a ∈ Q, x (f a) = true)) = Q.image f := by
  classical
  ext i
  simp [singletonSupport, Finset.mem_image, eq_comm]

lemma star_inter_small {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (hne : a ≠ a') (Q Q' : Finset (Fin l))
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_contra h
  apply hne
  exact star_centre_unique E hC4 (Q := Q ∩ Q') (by omega)
    (fun b hb => ha b (Finset.mem_inter.mp hb).1)
    (fun b hb => ha' b (Finset.mem_inter.mp hb).2)

lemma star_inter_small_right {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (hne : b ≠ b') (P P' : Finset (Fin p))
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P', (a, b') ∈ E) :
    (P ∩ P').card ≤ 1 := by
  by_contra h
  apply hne
  exact star_leaf_unique E hC4 (P := P ∩ P') (by omega)
    (fun a ha => hb a (Finset.mem_inter.mp ha).1)
    (fun a ha => hb' a (Finset.mem_inter.mp ha).2)

namespace CleanRoots

open PEqualNP.MetaComplexity Semantics OutputLedger

def pairAssignment {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun z => decide (z = u ∨ z = v)

lemma singleton_pair_left {n : ℕ} (u v i : Fin n)
    (h : singletonAssignment u i = true) : pairAssignment u v i = true := by
  simp only [singletonAssignment, decide_eq_true_eq] at h
  simp only [pairAssignment, decide_eq_true_eq]
  exact Or.inl h

lemma singleton_pair_right {n : ℕ} (u v i : Fin n)
    (h : singletonAssignment v i = true) : pairAssignment u v i = true := by
  simp only [singletonAssignment, decide_eq_true_eq] at h
  simp only [pairAssignment, decide_eq_true_eq]
  exact Or.inr h

lemma clean_rt_pair_accepted (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j)
    (u v : Fin n)
    (hu : val C (List.ofFn (singletonAssignment u)) ((gateAt C j).inputs.getD 0 0) = true)
    (hv : val C (List.ofFn (singletonAssignment v)) ((gateAt C j).inputs.getD 1 0) = true) :
    circuitFun n C (pairAssignment u v) = true := by
  have hl := mono n C hC.1 (singletonAssignment u) (pairAssignment u v)
    (singleton_pair_left u v) ((gateAt C j).inputs.getD 0 0) hu
  have hright := mono n C hC.1 (singletonAssignment v) (pairAssignment u v)
    (singleton_pair_right u v) ((gateAt C j).inputs.getD 1 0) hv
  have hgate : val C (List.ofFn (pairAssignment u v)) (n + j) = true := by
    rw [and_val n C hC _ (by simp) j hj hop, hl, hright]
    rfl
  exact reach_up n C _ (by simp) j hgate C.output hr

def inputSingletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (singletonAssignment u)) w = true

lemma clean_rt_support_disjoint (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hOut : ∀ u : Fin n, circuitFun n C (singletonAssignment u) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    Disjoint (inputSingletonSupport n C ((gateAt C j).inputs.getD 0 0))
      (inputSingletonSupport n C ((gateAt C j).inputs.getD 1 0)) := by
  rw [Finset.disjoint_left]
  intro u hu hv
  have hl : val C (List.ofFn (singletonAssignment u)) ((gateAt C j).inputs.getD 0 0) = true := by
    simpa only [inputSingletonSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hu
  have hright : val C (List.ofFn (singletonAssignment u)) ((gateAt C j).inputs.getD 1 0) = true := by
    simpa only [inputSingletonSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hgate : val C (List.ofFn (singletonAssignment u)) (n + j) = true := by
    rw [and_val n C hC _ (by simp) j hj hop, hl, hright]
    rfl
  have hf := reach_up n C _ (by simp) j hgate C.output hr
  have hfalse := hOut u
  change val C (List.ofFn (singletonAssignment u)) C.output = false at hfalse
  rw [hfalse] at hf
  contradiction

end CleanRoots

namespace OutputCounting

open PEqualNP.MetaComplexity Semantics OutputLedger

open PEqualNP.CleanedNonEdge

lemma s2233_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def s2233_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma s2233_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (s2233_par n C O).card ≤ O.card * 2 := by
  unfold s2233_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (s2233_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := s2233_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold s2233_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := s2233_par_card n C O (fun k hk => hlen _ (gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (s2233_par n C O)
  omega

lemma three_count (L : ℕ) (F : Finset ℕ) (A B : Set ℕ)
    (hF : ∀ j ∈ F, j < L) (hA : ∀ i ∈ A, i < L) (hB : ∀ i ∈ B, i < L)
    (hFA : ∀ j ∈ F, j ∉ A) (hFB : ∀ j ∈ F, j ∉ B) (hAB : ∀ i ∈ A, i ∉ B) :
    F.card + A.ncard + B.ncard ≤ L := by
  classical
  have hAf : A.Finite := (Set.finite_lt_nat L).subset (fun i hi => hA i hi)
  have hBf : B.Finite := (Set.finite_lt_nat L).subset (fun i hi => hB i hi)
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  have h1 : Disjoint F hAf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    exact hFA j hj ((Set.Finite.mem_toFinset hAf).mp hj2)
  have h2 : Disjoint (F ∪ hAf.toFinset) hBf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjB := (Set.Finite.mem_toFinset hBf).mp hj2
    rcases Finset.mem_union.mp hj with h | h
    · exact hFB j h hjB
    · exact hAB j ((Set.Finite.mem_toFinset hAf).mp h) hjB
  have h3 : (F ∪ hAf.toFinset) ∪ hBf.toFinset ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hF j h
      · exact hA j ((Set.Finite.mem_toFinset hAf).mp h)
    · exact hB j ((Set.Finite.mem_toFinset hBf).mp h)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at h4
  exact h4

lemma output_roots_charge (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hOut : ∀ u : Fin n, circuitFun n C (singletonAssignment u) = false)
    (F A : Finset ℕ)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      PEqualNP.CleanedNonEdge.OrReaches n C C.output j)
    (hA : ∀ j ∈ A, j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      ∃ u : Fin n, val C (List.ofFn (singletonAssignment u)) (n + j) = true) :
    A.card + 2 * F.card ≤ C.size + 1 := by
  let O : Set ℕ := {j | j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
    PEqualNP.CleanedNonEdge.OrReaches n C C.output j}
  have hroot : F.card ≤ O.ncard + 1 := s2233 n C F hC hF
  have hcount : F.card + (↑A : Set ℕ).ncard + O.ncard ≤ C.gates.length := by
    apply three_count
    · intro j hj
      exact (hF j hj).1
    · intro j hj
      exact (hA j hj).1
    · intro j hj
      exact hj.1
    · intro j hj ha
      have h1 := (hF j hj).2.1
      have h2 := (hA j ha).2.1
      rw [h1] at h2
      cases h2
    · intro j hj ho
      have h1 := (hF j hj).2.1
      have h2 := ho.2.1
      rw [h1] at h2
      cases h2
    · intro j hj ho
      exact singleton_live_not_output_orCone n C hOut j (hA j hj).2.2 ho.2.2
  rw [Set.ncard_coe_finset] at hcount
  change A.card + 2 * F.card ≤ C.gates.length + 1
  omega

end OutputCounting

lemma graph_vertices_le_edges_components {α : Type} [Fintype α] (G : SimpleGraph α) :
    Fintype.card α ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hbound : ∀ c : G.ConnectedComponent,
      c.supp.ncard ≤ c.toSimpleGraph.edgeSet.ncard + 1 := by
    intro c
    exact c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hs := Finset.sum_le_sum (fun (c : G.ConnectedComponent) (_ : c ∈ Finset.univ) => hbound c)
  rw [G.sum_connectedComponent_ncard_supp, Finset.sum_add_distrib,
    G.sum_connectedComponent_ncard_edgeSet] at hs
  change Nat.card α ≤ Nat.card G.edgeSet + ∑ _c : G.ConnectedComponent, 1 at hs
  simpa using hs

lemma connected_cover_card_le {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (U R : Finset α)
    (hcover : ∀ u ∈ U, ∃ r ∈ R, G.Reachable u r) :
    U.card ≤ Nat.card G.edgeSet + R.card := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hcomp : (Finset.univ : Finset G.ConnectedComponent) ⊆
      ((Finset.univ \ U).image G.connectedComponentMk) ∪ R.image G.connectedComponentMk := by
    intro c hc
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ u =>
      by_cases hu : u ∈ U
      · obtain ⟨r, hr, hur⟩ := hcover u hu
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨r, hr, (SimpleGraph.ConnectedComponent.sound hur).symm⟩)
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, by simp [hu], rfl⟩)
  have hcompcard : Nat.card G.ConnectedComponent ≤ (Fintype.card α - U.card) + R.card := by
    calc
      Nat.card G.ConnectedComponent = (Finset.univ : Finset G.ConnectedComponent).card := by simp
      _ ≤ (((Finset.univ \ U).image G.connectedComponentMk) ∪ R.image G.connectedComponentMk).card :=
        Finset.card_le_card hcomp
      _ ≤ ((Finset.univ \ U).image G.connectedComponentMk).card + (R.image G.connectedComponentMk).card :=
        Finset.card_union_le _ _
      _ ≤ (Finset.univ \ U).card + R.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = (Fintype.card α - U.card) + R.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
        simp
  have hall := graph_vertices_le_edges_components G
  have hU : U.card ≤ Fintype.card α := Finset.card_le_univ U
  omega

def operand0 (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := (gateAt C (w - n)).inputs.getD 0 0
def operand1 (n : ℕ) (C : Circuit) (w : ℕ) : ℕ := (gateAt C (w - n)).inputs.getD 1 0

noncomputable def bridgeFor (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) :
    Finset (Sym2 (Fin n)) := by
  classical
  exact if h : goodOrWire n C S w ∧
      (maskedSupport n C S (operand0 n C w)).Nonempty ∧
      (maskedSupport n C S (operand1 n C w)).Nonempty then
    {s(h.2.1.choose, h.2.2.choose)} else ∅

noncomputable def bridgeSet (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (Finset.range (n + C.gates.length)).biUnion (bridgeFor n C S)

noncomputable def supportGraph (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (bridgeSet n C S : Set (Sym2 (Fin n)))

lemma bridgeSet_card_le (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    (bridgeSet n C S).card ≤ (goodOrWires n C S).card := by
  classical
  calc
    (bridgeSet n C S).card ≤ ∑ w ∈ Finset.range (n + C.gates.length), (bridgeFor n C S w).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ w ∈ Finset.range (n + C.gates.length), if goodOrWire n C S w then 1 else 0 := by
      apply Finset.sum_le_sum
      intro w hw
      unfold bridgeFor
      split_ifs with h hg
      · simp
      · exact (hg h.1).elim
      · simp
      · simp
    _ = (goodOrWires n C S).card := by
      rw [← Finset.sum_filter]
      simp [goodOrWires]

lemma supportGraph_edges_le (n : ℕ) (C : Circuit) (S : Finset (Fin n)) :
    Nat.card (supportGraph n C S).edgeSet ≤ (goodOrWires n C S).card := by
  classical
  calc
    Nat.card (supportGraph n C S).edgeSet ≤ (bridgeSet n C S).card := by
      rw [Nat.card_coe_set_eq]
      unfold supportGraph
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact (Set.ncard_mono Set.diff_subset).trans_eq (by simp)
    _ ≤ (goodOrWires n C S).card := bridgeSet_card_le n C S

lemma bridge_reachable (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ)
    (hg : goodOrWire n C S w)
    (ha : (maskedSupport n C S (operand0 n C w)).Nonempty)
    (hb : (maskedSupport n C S (operand1 n C w)).Nonempty) :
    (supportGraph n C S).Reachable ha.choose hb.choose := by
  classical
  by_cases he : ha.choose = hb.choose
  · exact he ▸ SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    change s(ha.choose, hb.choose) ∈ bridgeSet n C S ∧ ha.choose ≠ hb.choose
    refine ⟨?_, he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_range.mpr hg.2.1, ?_⟩
    unfold bridgeFor
    rw [dif_pos ⟨hg, ha, hb⟩]
    exact Finset.mem_singleton_self _

lemma maskedSupport_connected (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) :
    ∀ u ∈ maskedSupport n C S w, ∀ v ∈ maskedSupport n C S w,
      (supportGraph n C S).Reachable u v := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu v hv
    by_cases hsmall : (maskedSupport n C S w).card ≤ 1
    · have he : u = v := Finset.card_le_one.mp hsmall u hu v hv
      exact he ▸ SimpleGraph.Reachable.rfl
    · have hbig : 2 ≤ (maskedSupport n C S w).card := by omega
      obtain ⟨hc, hlarge, hn, hlen⟩ := maskedSupport_large n C S w hbig
      let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hwj : n + j = w := by dsimp [j]; omega
      have hinputs : (gateAt C j).inputs.length = 2 := hC.2.2 _ (gateAt_mem hj)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hinputs
      have ha : a < w := by
        have := hC.2.1 j hj a (by simp [hab])
        omega
      have hb : b < w := by
        have := hC.2.1 j hj b (by simp [hab])
        omega
      have hop := hC.1 _ (gateAt_mem hj)
      rcases hop with hop | hop
      · have hval : ∀ x : Fin n → Bool,
            val C (List.ofFn x) w = (val C (List.ofFn x) a && val C (List.ofFn x) b) := by
          intro x
          simpa [hwj, hab] using and_val n C hC (List.ofFn x) (by simp) j hj hop
        have hs : wireSupport n C w = wireSupport n C a ∩ wireSupport n C b := by
          unfold wireSupport
          rw [show (fun x => val C (List.ofFn x) w) =
            (fun x => val C (List.ofFn x) a && val C (List.ofFn x) b) by funext x; exact hval x]
          exact singletonSupport_and _ _
        by_cases hca : val C (List.ofFn fun i => decide (i ∉ S)) a = false
        · have hsub : maskedSupport n C S w ⊆ maskedSupport n C S a := by
            intro i hi
            rw [maskedSupport, if_pos hc, hs] at hi
            rw [maskedSupport, if_pos hca]
            exact (Finset.mem_inter.mp hi).1
          exact ih a ha u (hsub hu) v (hsub hv)
        · have hcb : val C (List.ofFn fun i => decide (i ∉ S)) b = false := by
            have he := hval (fun i => decide (i ∉ S))
            rw [hc] at he
            cases hfa : val C (List.ofFn fun i => decide (i ∉ S)) a <;>
              cases hfb : val C (List.ofFn fun i => decide (i ∉ S)) b <;> simp_all
          have hsub : maskedSupport n C S w ⊆ maskedSupport n C S b := by
            intro i hi
            rw [maskedSupport, if_pos hc, hs] at hi
            rw [maskedSupport, if_pos hcb]
            exact (Finset.mem_inter.mp hi).2
          exact ih b hb u (hsub hu) v (hsub hv)
      · have hval : ∀ x : Fin n → Bool,
            val C (List.ofFn x) w = (val C (List.ofFn x) a || val C (List.ofFn x) b) := by
          intro x
          simpa [hwj, hab] using or_val n C hC (List.ofFn x) (by simp) j hj hop
        have hs : wireSupport n C w = wireSupport n C a ∪ wireSupport n C b := by
          unfold wireSupport
          rw [show (fun x => val C (List.ofFn x) w) =
            (fun x => val C (List.ofFn x) a || val C (List.ofFn x) b) by funext x; exact hval x]
          exact singletonSupport_or _ _
        have hcc : val C (List.ofFn fun i => decide (i ∉ S)) a = false ∧
            val C (List.ofFn fun i => decide (i ∉ S)) b = false := by
          have he := hval (fun i => decide (i ∉ S))
          rw [hc] at he
          cases hfa : val C (List.ofFn fun i => decide (i ∉ S)) a <;>
            cases hfb : val C (List.ofFn fun i => decide (i ∉ S)) b <;> simp_all
        have hmask : maskedSupport n C S w = maskedSupport n C S a ∪ maskedSupport n C S b := by
          rw [maskedSupport, if_pos hc, hs, maskedSupport, if_pos hcc.1,
            maskedSupport, if_pos hcc.2]
        have hoa : operand0 n C w = a := by
          change (gateAt C j).inputs.getD 0 0 = a
          simp [hab]
        have hob : operand1 n C w = b := by
          change (gateAt C j).inputs.getD 1 0 = b
          simp [hab]
        have hg : goodOrWire n C S w := ⟨hn, hlen, hop, hlarge, hc⟩
        have hcross : ∀ x ∈ maskedSupport n C S a, ∀ y ∈ maskedSupport n C S b,
            (supportGraph n C S).Reachable x y := by
          intro x hx y hy
          have haN : (maskedSupport n C S (operand0 n C w)).Nonempty := by
            rw [hoa]
            exact ⟨x, hx⟩
          have hbN : (maskedSupport n C S (operand1 n C w)).Nonempty := by
            rw [hob]
            exact ⟨y, hy⟩
          have haRep : haN.choose ∈ maskedSupport n C S a := by
            simpa only [hoa] using haN.choose_spec
          have hbRep : hbN.choose ∈ maskedSupport n C S b := by
            simpa only [hob] using hbN.choose_spec
          exact (ih a ha x hx _ haRep).trans ((bridge_reachable n C S w hg haN hbN).trans
            (ih b hb _ hbRep y hy))
        rw [hmask] at hu hv
        rcases Finset.mem_union.mp hu with hua | hub <;>
          rcases Finset.mem_union.mp hv with hva | hvb
        · exact ih a ha u hua v hva
        · exact hcross u hua v hvb
        · exact (hcross v hva u hub).symm
        · exact ih b hb u hub v hvb

lemma pure_or_overlap_family_bound {κ : Type} [DecidableEq κ]
    (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (S : Finset (Fin n)) (F : Finset κ) (sets : κ → Finset (Fin n)) (roots : κ → ℕ)
    (hsub : ∀ k ∈ F, sets k ⊆ S)
    (hroot : ∀ k ∈ F, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (roots k) = decide (∃ i ∈ sets k, x i = true))
    (U R : Finset (Fin n))
    (hcover : ∀ u ∈ U, ∃ r ∈ R,
      Relation.EqvGen (fun a b => ∃ k ∈ F, a ∈ sets k ∧ b ∈ sets k) u r) :
    U.card ≤ (goodOrWires n C S).card + R.card := by
  classical
  have hsets : ∀ k ∈ F, ∀ u ∈ sets k, ∀ v ∈ sets k,
      (supportGraph n C S).Reachable u v := by
    intro k hk u hu v hv
    have hfalse : val C (List.ofFn fun i => decide (i ∉ S)) (roots k) = false := by
      rw [hroot k hk]
      apply decide_eq_false
      rintro ⟨i, hi, hni⟩
      have his := hsub k hk hi
      simp [his] at hni
    have hsupport : wireSupport n C (roots k) = sets k := by
      ext i
      simp [wireSupport, singletonSupport, hroot k hk]
    have hmask : maskedSupport n C S (roots k) = sets k := by
      rw [maskedSupport, if_pos hfalse, hsupport]
    rw [← hmask] at hu hv
    exact maskedSupport_connected n C hC S (roots k) u hu v hv
  have hgraphCover : ∀ u ∈ U, ∃ r ∈ R, (supportGraph n C S).Reachable u r := by
    intro u hu
    obtain ⟨r, hr, hpath⟩ := hcover u hu
    refine ⟨r, hr, ?_⟩
    clear hu hr
    induction hpath with
    | rel a b hab =>
      obtain ⟨k, hk, ha, hb⟩ := hab
      exact hsets k hk a ha b hb
    | refl a => exact SimpleGraph.Reachable.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  have hcard := connected_cover_card_le (supportGraph n C S) U R hgraphCover
  exact hcard.trans (Nat.add_le_add_right (supportGraph_edges_le n C S) R.card)

namespace Global

lemma clean_and_cross_relation {V : Type} [DecidableEq V]
    (R : V → V → Prop) (hirr : ∀ a, ¬ R a a)
    (hsymm : ∀ a b, R a b → R b a)
    (f g : (V → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hclean : ∀ x, f x = true → g x = true →
      ∃ u v, R u v ∧ x u = true ∧ x v = true)
    (A B : Finset V)
    (hA : ∀ a ∈ A, f (fun i => decide (i = a)) = true)
    (hB : ∀ b ∈ B, g (fun i => decide (i = b)) = true) :
    ∀ a ∈ A, ∀ b ∈ B, R a b := by
  intro a ha b hb
  let x : V → Bool := fun i => decide (i = a ∨ i = b)
  have hax : f x = true := hf _ _ (by
    intro i hi
    have hi' : i = a := by simpa using hi
    subst i
    simp [x]) (hA a ha)
  have hbx : g x = true := hg _ _ (by
    intro i hi
    have hi' : i = b := by simpa using hi
    subst i
    simp [x]) (hB b hb)
  obtain ⟨u, v, huv, hu, hv⟩ := hclean x hax hbx
  have hu' : u = a ∨ u = b := by simpa [x] using hu
  have hv' : v = a ∨ v = b := by simpa [x] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact False.elim (hirr _ huv)
  · exact huv
  · exact hsymm _ _ huv
  · exact False.elim (hirr _ huv)

lemma complete_rectangle_has_singleton {V : Type} [DecidableEq V]
    (R : V → V → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, R a b) :
    (∃ a, A = {a} ∧ ∀ b ∈ B, R a b) ∨
      (∃ b, B = {b} ∧ ∀ a ∈ A, R a b) := by
  by_cases ha : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp ha
    exact Or.inl ⟨a, rfl, fun b hb => hcross a (Finset.mem_singleton_self a) b hb⟩
  · have ha2 : 1 < A.card := by
      have hpos := Finset.card_pos.mpr hA
      omega
    have hb1 : B.card = 1 := by
      by_contra hb
      have hb2 : 1 < B.card := by
        have hpos := Finset.card_pos.mpr hB
        omega
      obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp ha2
      obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp hb2
      exact hfour a a' b b' haa' hbb'
        ⟨hcross a ha b hb, hcross a ha b' hb', hcross a' ha' b hb,
          hcross a' ha' b' hb'⟩
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hb1
    exact Or.inr ⟨b, rfl, fun a ha => hcross a ha b (Finset.mem_singleton_self b)⟩

lemma clean_and_support_star {V : Type} [DecidableEq V]
    (R : V → V → Prop) (hirr : ∀ a, ¬ R a a)
    (hsymm : ∀ a b, R a b → R b a)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (f g : (V → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hclean : ∀ x, f x = true → g x = true →
      ∃ u v, R u v ∧ x u = true ∧ x v = true)
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hfA : ∀ a ∈ A, f (fun i => decide (i = a)) = true)
    (hgB : ∀ b ∈ B, g (fun i => decide (i = b)) = true) :
    (∃ a, A = {a} ∧ ∀ b ∈ B, R a b) ∨
      (∃ b, B = {b} ∧ ∀ a ∈ A, R a b) := by
  exact complete_rectangle_has_singleton R hfour A B hA hB
    (clean_and_cross_relation R hirr hsymm f g hf hg hclean A B hfA hgB)

end Global

end PEqualNP.Outside.L_meta_4970
