import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Basic
import PEqualNP.Defs

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

end PEqualNP.Outside.L_meta_4970
