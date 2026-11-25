import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshBudget

open PEqualNP.CircuitLowerBounds

def HasEdge {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

def SignalMono {V : Type*} (s : Set V → Prop) : Prop :=
  ∀ ⦃X Y : Set V⦄, X ⊆ Y → s X → s Y

def ContextMono {V : Type*} (K : Set V → Prop → Prop) : Prop :=
  ∀ ⦃X Y : Set V⦄ ⦃p q : Prop⦄, X ⊆ Y → (p → q) → K X p → K Y q

def Exact {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (s : Set V → Prop) : Prop :=
  ∀ X, K X (s X) ↔ HasEdge G X

def Pivotal {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (u v : V) : Prop :=
  G.Adj u v ∧ ¬ K {u, v} False

def Required {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    (X : Set V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, Pivotal G K u v

lemma hasEdge_pair {V : Type*} (G : SimpleGraph V) {u v : V} (he : G.Adj u v) :
    HasEdge G {u, v} :=
  ⟨u, by simp, v, by simp, he⟩

lemma required_sound {V : Type*} (G : SimpleGraph V) (K : Set V → Prop → Prop)
    {X : Set V} (hX : Required G K X) : HasEdge G X := by
  obtain ⟨u, hu, v, hv, he⟩ := hX
  exact ⟨u, hu, v, hv, he.1⟩

lemma cofactor_decomposition {V : Type*} {G : SimpleGraph V} {K : Set V → Prop → Prop}
    {s : Set V → Prop} (hK : ContextMono K) (hold : Exact G K s) (X : Set V) :
    HasEdge G X ↔ K X False ∨ Required G K X := by
  classical
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    by_cases hp : K {u, v} False
    · exact Or.inl (hK (Set.pair_subset hu hv) id hp)
    · exact Or.inr ⟨u, hu, v, hv, he, hp⟩
  · rintro (h | h)
    · exact (hold X).1 (hK Set.Subset.rfl False.elim h)
    · exact required_sound G K h

def selectedLe (x y : List Bool) : Prop :=
  List.Forall₂ (fun a b => a = true → b = true) x y

lemma selectedLe_get {x y : List Bool} (h : selectedLe x y) (i : ℕ) :
    x.getD i false = true → y.getD i false = true := by
  induction h generalizing i with
  | nil => cases i <;> simp
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ j => exact ih j

def selectedValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def selectedStep (w : List Bool) (g : Gate) : List Bool := w ++ [selectedValue g w]

lemma selectedValue_mono {g : Gate} (hgate : g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (h : selectedLe x y) :
    selectedValue g x = true → selectedValue g y = true := by
  rcases hgate with hop | hop
  · simp only [selectedValue, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq]
    intro hx i hi
    exact selectedLe_get h i (hx i hi)
  · simp only [selectedValue, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, selectedLe_get h i hx⟩

lemma selectedFold_mono (s : List Gate)
    (hgate : ∀ g ∈ s, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (h : selectedLe x y) :
    selectedLe (s.foldl selectedStep x) (s.foldl selectedStep y) := by
  induction s generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun i hi => hgate i (List.mem_cons_of_mem _ hi))
      (List.rel_append h (.cons (selectedValue_mono (hgate g (by simp)) h) .nil))

noncomputable def selectedInput {n : ℕ} (X : Set (Fin n)) : List Bool := by
  classical
  exact List.ofFn (fun i : Fin n => decide (i ∈ X))

lemma selectedInput_mono {n : ℕ} {X Y : Set (Fin n)} (h : X ⊆ Y) :
    selectedLe (selectedInput X) (selectedInput Y) := by
  classical
  apply List.forall₂_of_length_eq_of_get
  · simp [selectedInput]
  · intro i hi hj
    simp only [selectedInput, List.get_eq_getElem, List.getElem_ofFn,
      decide_eq_true_eq]
    exact fun hx => h hx

def selectedCircuit (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ) :
    Circuit := ⟨pre ++ g :: post, out⟩

noncomputable def selectedSignal {n : ℕ} (pre : List Gate) (g : Gate)
    (X : Set (Fin n)) : Prop :=
  selectedValue g (pre.foldl selectedStep (selectedInput X)) = true

noncomputable def selectedContext {n : ℕ} (pre post : List Gate) (out : ℕ)
    (X : Set (Fin n)) (p : Prop) : Prop := by
  classical
  exact (post.foldl selectedStep
    (pre.foldl selectedStep (selectedInput X) ++ [decide p])).getD out false = true

lemma selectedContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
    (hp : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or)
    (hs : ∀ a ∈ post, a.op = GateOp.and ∨ a.op = GateOp.or) :
    ContextMono (selectedContext (n := n) pre post out) := by
  classical
  intro X Y p q hXY hpq
  apply selectedLe_get (i := out)
  apply selectedFold_mono post hs
  apply List.rel_append (selectedFold_mono pre hp (selectedInput_mono hXY))
  apply List.Forall₂.cons _ .nil
  simpa using hpq

lemma selected_eval {n : ℕ} (pre post : List Gate) (out : ℕ) (g : Gate)
    (X : Set (Fin n)) :
    (selectedCircuit pre g post out).eval (selectedInput X) = true ↔
      selectedContext pre post out X (selectedSignal pre g X) := by
  classical
  let w := pre.foldl selectedStep (selectedInput X)
  let b := selectedValue g w
  change ((pre ++ g :: post).foldl selectedStep (selectedInput X)).getD out false = true ↔ _
  rw [List.foldl_append, List.foldl_cons]
  change (post.foldl selectedStep (w ++ [b])).getD out false = true ↔
    (post.foldl selectedStep (w ++ [@decide (b = true) (Classical.propDecidable _)] )).getD
      out false = true
  have hdec : @decide (b = true) (Classical.propDecidable _) = b := by
    cases b <;> simp
  rw [hdec]

lemma selectedInput_support {n : ℕ} (x : Fin n → Bool) :
    selectedInput {i | x i = true} = List.ofFn x := by
  classical
  unfold selectedInput
  congr 1
  funext i
  change @decide (x i = true) (Classical.propDecidable _) = x i
  cases x i <;> simp

lemma selected_computes_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (out : ℕ) (g : Gate) :
    (∀ x : Fin n → Bool, (selectedCircuit pre g post out).eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ↔
    ∀ X : Set (Fin n), selectedContext pre post out X (selectedSignal pre g X) ↔
      ∃ u ∈ X, ∃ v ∈ X, G.Adj u v := by
  classical
  constructor
  · intro h X
    rw [← selected_eval]
    unfold selectedInput
    rw [h]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, hu, v, hv, he⟩
    · rintro ⟨u, hu, v, hv, he⟩
      exact ⟨u, v, he, hu, hv⟩
  · intro h x
    specialize h {i | x i = true}
    rw [← selected_eval, selectedInput_support] at h
    rw [Bool.eq_iff_iff, h, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, v, hv, he⟩
      exact ⟨u, v, he, hu, hv⟩
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, hu, v, hv, he⟩

lemma selected_lookup_ne (pre post : List Gate) (out : ℕ) (g h : Gate) {k : ℕ}
    (hk : k ≠ pre.length) :
    (selectedCircuit pre g post out).gates[k]? = (selectedCircuit pre h post out).gates[k]? := by
  change (pre ++ g :: post)[k]? = (pre ++ h :: post)[k]?
  by_cases hlt : k < pre.length
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · obtain ⟨r, hr⟩ : ∃ r, k - pre.length = r+1 := ⟨k - pre.length - 1, by omega⟩
    rw [List.getElem?_append_right (Nat.le_of_not_gt hlt),
      List.getElem?_append_right (Nat.le_of_not_gt hlt), hr]
    rfl

namespace FanoutBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

theorem u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, ite_eq_left h]

theorem u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left h]

theorem u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_left hA, dite_eq_left ha, dite_eq_left hb]

theorem u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_right (by simp [hA]), dite_eq_left ha,
    dite_eq_left hb]
end

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (_hs : s < n + gs.length) (_ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

theorem chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [ite_eq_right (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
theorem build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [ite_eq_left hpd, ite_eq_right hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [ite_eq_right (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

theorem veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

theorem gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl

def ReadsCut (n T : ℕ) (a b : ℕ → ℕ) (j : ℕ) : Prop :=
  a j = n + T ∨ b j = n + T

noncomputable def Readers (n N T : ℕ) (a b : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (ReadsCut n T a b)

noncomputable def DeadAnds (n N T : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) : Finset ℕ := by
  classical
  exact insert T ((Readers n N T a b).filter (fun j => A j = true))

noncomputable def AliasOrs (n N T : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Readers n N T a b).filter (fun j => A j = false)

lemma cut_card (n N T : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (hT : T < N)
    (hab : ∀ j < N, a j < n+j ∧ b j < n+j) :
    (DeadAnds n N T A a b).card + (AliasOrs n N T A a b).card =
      (Readers n N T a b).card + 1 := by
  classical
  have hnr : T ∉ Readers n N T a b := by
    simp only [Readers, Finset.mem_filter, Finset.mem_range, ReadsCut, not_and]
    have := hab T hT
    omega
  have hnr' : T ∉ (Readers n N T a b).filter (fun j => A j = true) := by
    exact fun h => hnr (Finset.mem_filter.mp h).1
  have hF : (Readers n N T a b).filter (fun j => A j = false) =
      (Readers n N T a b).filter (fun j => ¬ A j = true) := by simp
  rw [DeadAnds, AliasOrs, Finset.card_insert_of_notMem hnr', hF]
  have h := Finset.card_filter_add_card_filter_not (fun j => A j = true) (s := Readers n N T a b)
  omega

def ZeroGate : Gate := ⟨GateOp.or, []⟩

lemma revised_gates_length (pre post : List Gate) (g h : Gate) :
    (pre ++ g :: post).length = (pre ++ h :: post).length := by simp

lemma forced_rec {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (h2 : TopForm.IsAO2 n (selectedCircuit pre g post out)) :
    let C := selectedCircuit pre g post out
    let a := fun j => TopForm.opnd C j 0
    let b := fun j => TopForm.opnd C j 1
    let A := fun j => @decide ((gateAt C j).op = GateOp.and) (Classical.propDecidable _)
    let N := C.gates.length
    let T := pre.length
    let Del := DeadAnds n N T A a b
    ∀ (x : Fin n → Bool) w, w < n+N →
      u n A a b Del (fun _ => []) (List.ofFn x) w =
      (run (pre ++ ZeroGate :: post) (List.ofFn x)).getD w false := by
  classical
  dsimp only
  let C := selectedCircuit pre g post out
  let a := fun j => TopForm.opnd C j 0
  let b := fun j => TopForm.opnd C j 1
  let A := fun j => @decide ((gateAt C j).op = GateOp.and) (Classical.propDecidable _)
  let N := C.gates.length
  let T := pre.length
  let Del := DeadAnds n N T A a b
  let Z := selectedCircuit pre ZeroGate post out
  change ∀ x w, w < n+N → u n A a b Del (fun _ => []) (List.ofFn x) w =
    (run Z.gates (List.ofFn x)).getD w false
  have hNT : T < N := by simp [N,T,C,selectedCircuit]
  have hZlen : Z.gates.length = N := by simp [Z,N,C,selectedCircuit]
  have hdt : T ∈ Del := by simp [Del,DeadAnds]
  intro x w
  have hzero : (run Z.gates (List.ofFn x)).getD (n+T) false = false := by
    have hTz : T < Z.gates.length := by omega
    have hz := run_gate Z.gates (List.ofFn x) T hTz
    have hget : Z.gates[T] = ZeroGate := by simp [Z,T,selectedCircuit]
    simpa [hget,ZeroGate,GateOp.eval] using hz
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < N := by omega
    by_cases hJT : j = T
    · subst j
      rw [u_del hdt,hzero]
    obtain ⟨hgat,hinps,haj,hbj,handor⟩ := gate2 h2 (j := j) hj
    change a j < n+j at haj
    change b j < n+j at hbj
    have hZg : Z.gates[j]'(by omega) = gateAt C j := by
      have heq := selected_lookup_ne pre post out ZeroGate g hJT
      rw [List.getElem?_eq_getElem (by omega : j < Z.gates.length),
        List.getElem?_eq_getElem hj] at heq
      exact (Option.some.inj heq).trans hgat
    have hg : Z.gates[j]'(by omega) = ⟨(gateAt C j).op,[a j,b j]⟩ :=
      hZg.trans (gate_eta rfl hinps)
    have hz := veq n Z.gates x j (by omega) _ (a j) (b j) hg haj hbj
    have hahi := ih (a j) haj (by omega)
    have hbhi := ih (b j) hbj (by omega)
    by_cases hd : j ∈ Del
    · have hh : j ∈ Readers n N T a b ∧ A j = true := by
        simpa [Del,DeadAnds,hJT] using hd
      have hr := (Finset.mem_filter.mp hh.1).2
      have hopen : (gateAt C j).op = GateOp.and := of_decide_eq_true hh.2
      rw [u_del hd,hz,hopen]
      rcases hr with h|h <;> rw [h,hzero] <;> simp [GateOp.eval]
    · rcases handor with hA|hO
      · have hAt : A j = true := by simp [A,C] at *; exact hA
        rw [u_and hd hAt haj hbj,hz,hA,hahi,hbhi]
        simp [GateOp.eval]
      · have hAf : A j = false := by simp [A,C,hO]
        rw [u_or hd hAf haj hbj,hz,hO,hahi,hbhi]
        simp [GateOp.eval]

lemma selectedLe_refl (w : List Bool) : selectedLe w w := by
  induction w with
  | nil => exact .nil
  | cons _ _ ih => exact .cons id ih

lemma zero_wire_le (pre post : List Gate) (g : Gate)
    (hp : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or) (x : List Bool) (w : ℕ) :
    (run (pre ++ ZeroGate :: post) x).getD w false = true →
      (run (pre ++ g :: post) x).getD w false = true := by
  change ((pre ++ ZeroGate :: post).foldl selectedStep x).getD w false = true →
    ((pre ++ g :: post).foldl selectedStep x).getD w false = true
  rw [List.foldl_append,List.foldl_cons,List.foldl_append,List.foldl_cons]
  apply selectedLe_get (selectedFold_mono post hp _) w
  apply List.rel_append (selectedLe_refl _)
  apply List.Forall₂.cons _ .nil
  simp [selectedValue,ZeroGate,GateOp.eval]

noncomputable def DirtySet (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : Finset ℕ := by
  classical
  exact (Finset.range gs.length).filter fun j => (gs.getD j ⟨GateOp.or,[]⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n+j) false = true ∧ F x = false

noncomputable def CircuitReaders (n : ℕ) (C : Circuit) (T : ℕ) : Finset ℕ :=
  Readers n C.gates.length T (fun j => TopForm.opnd C j 0) (fun j => TopForm.opnd C j 1)

lemma compile_zero {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (h2 : TopForm.IsAO2 n (selectedCircuit pre g post out))
    (hOut : out < n + (selectedCircuit pre g post out).gates.length)
    (F : (Fin n → Bool) → Bool) :
    ∃ (gs : List Gate) (o : Option ℕ), Ok n gs ∧ (∀ w, o = some w → w < n+gs.length) ∧
      gs.length + (CircuitReaders n (selectedCircuit pre g post out) pre.length).card + 1 ≤
        (selectedCircuit pre g post out).size ∧
      (∀ x : Fin n → Bool, ov gs (List.ofFn x) o =
        (selectedCircuit pre ZeroGate post out).eval (List.ofFn x)) ∧
      dc n F gs ≤ ((DirtySet n F (selectedCircuit pre g post out).gates).erase pre.length).card := by
  classical
  let C := selectedCircuit pre g post out
  let Z := selectedCircuit pre ZeroGate post out
  let a := fun j => TopForm.opnd C j 0
  let b := fun j => TopForm.opnd C j 1
  let A := fun j => @decide ((gateAt C j).op = GateOp.and) (Classical.propDecidable _)
  let N := C.gates.length
  let T := pre.length
  let Del := DeadAnds n N T A a b
  let R := AliasOrs n N T A a b
  have hNT : T < N := by simp [N,T,C,selectedCircuit]
  have hab (j) (hj : j < N) : a j < n+j ∧ b j < n+j := by
    obtain ⟨_,_,ha,hb,_⟩ := gate2 h2 hj
    exact ⟨ha,hb⟩
  have hrRange {j} (h : j ∈ Readers n N T a b) : j < N :=
    Finset.mem_range.mp (Finset.mem_filter.mp h).1
  have hr_gt {j} (h : j ∈ Readers n N T a b) : T < j := by
    obtain ⟨hA,hB⟩ := hab j (hrRange h)
    have hp := (Finset.mem_filter.mp h).2
    rcases hp with h|h <;> omega
  have hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n+d ∨ b j = n+d) := by
    intro j hj
    obtain ⟨hr,hf⟩ := Finset.mem_filter.mp hj
    have hgt := hr_gt hr
    refine ⟨hf,?_,T,by simp [Del,DeadAnds],hgt,(Finset.mem_filter.mp hr).2⟩
    simp [Del,DeadAnds,show j ≠ T by omega,hf]
  obtain ⟨gs,m,hOk,hm,_,hcost,hdc⟩ :=
    build n A a b Del R (fun _ => []) F (by simp) hR N hab
  have hsubD : Del ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_insert.mp hj with rfl|h
    · exact hNT
    · exact hrRange (Finset.mem_filter.mp h).1
  have hsubR : R ⊆ Finset.range N := fun j h => Finset.mem_range.mpr (hrRange (Finset.mem_filter.mp h).1)
  have hdEq : (Finset.range N).filter (· ∈ Del) = Del := by
    ext j
    exact ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => Finset.mem_filter.mpr ⟨hsubD hj,hj⟩⟩
  have hrEq : (Finset.range N).filter (· ∈ R) = R := by
    ext j
    exact ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => Finset.mem_filter.mpr ⟨hsubR hj,hj⟩⟩
  rw [hdEq,hrEq] at hcost
  have hc := cut_card n N T A a b hNT hab
  change Del.card + R.card = _ at hc
  have hctx (x : Fin n → Bool) (w : ℕ) (hw : w < n + N) :
      u n A a b Del (fun _ => []) (List.ofFn x) w = (run Z.gates (List.ofFn x)).getD w false :=
    forced_rec pre post g out h2 x w hw
  refine ⟨gs,m out,hOk,(hm out hOut).1,?_,?_,?_⟩
  · change gs.length + (Readers n N T a b).card + 1 ≤ N
    simp at hcost
    omega
  · intro x
    exact ((hm out hOut).2 x).trans (hctx x out hOut)
  · apply hdc.trans
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hjR,hjA,hjD,x,hx,hFx⟩ := Finset.mem_filter.mp hj
    have hjN := Finset.mem_range.mp hjR
    have hTDel : T ∈ Del := by simp [Del,DeadAnds]
    apply Finset.mem_erase.mpr
    refine ⟨(fun h => hjD (h ▸ hTDel)), Finset.mem_filter.mpr ⟨hjR,of_decide_eq_true hjA,x,?_,hFx⟩⟩
    rw [hctx x _ (by omega)] at hx
    exact zero_wire_le pre post g (fun z hz => h2.1 z (List.mem_append_right _ (List.mem_cons_of_mem _ hz)))
      (List.ofFn x) _ hx

abbrev StarTriple (n : ℕ) := Fin n × Fin n × List (Fin n)

def starSignal {n : ℕ} (s : StarTriple n) (x : Fin n → Bool) : Bool :=
  x s.1 && (x s.2.1 || s.2.2.any x)

def starBudget {n : ℕ} (s : StarTriple n) : ℕ := s.2.2.length + 2

lemma append_raw {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    (List.ofFn x).getD v.val false = x v := by
  simp [List.getD_eq_getElem?_getD]

lemma append_literal {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    ov gs (List.ofFn x) (some v.val) = x v := by
  change (run gs (List.ofFn x)).getD v.val false = x v
  rw [run_input _ _ _ (by simp), append_raw]

lemma star_append_gate {n : ℕ} (F : (Fin n → Bool) → Bool)
    (s : StarTriple n) (hs : ∀ x, starSignal s x = true → F x = true)
    (gs : List Gate) (hgs : Ok n gs) :
    ∃ (tail : List Gate) (o : ℕ), Ok n (gs ++ tail) ∧ tail.length ≤ s.2.2.length + 1 ∧
      dc n F (gs ++ tail) ≤ dc n F gs ∧ o < n+(gs++tail).length ∧
      ∀ x : Fin n → Bool, ov (gs++tail) (List.ofFn x) (some o) = starSignal s x := by
  classical
  obtain ⟨h, o, hok, hlen, hdc, hbound, hval⟩ := chain n F (s.2.2.map Fin.val) (by
    intro t ht
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    exact v.isLt) gs hgs (some s.2.1.val) (by
      intro w hw
      cases hw
      have := s.2.1.isLt
      omega)
  have hv (x : Fin n → Bool) :
      ov (gs++h) (List.ofFn x) o = (x s.2.1 || s.2.2.any x) := by
    rw [hval x, append_literal]
    simp only [List.any_map, Function.comp_def, append_raw]
  obtain ⟨w,rfl⟩ : ∃ w, o = some w := by
    cases o with
    | some w => exact ⟨w,rfl⟩
    | none =>
      have hz := hv (fun _ => true)
      simp [ov] at hz
  let prior := gs ++ h
  let a : Gate := ⟨GateOp.and, [s.1.val,w]⟩
  have hw : w < n+prior.length := hbound w rfl
  have hc : s.1.val < n+prior.length := by have := s.1.isLt; omega
  have hvalA (x : Fin n → Bool) : ov (prior++[a]) (List.ofFn x) (some (n+prior.length)) =
      starSignal s x := by
    rw [show prior++[a] = prior++[⟨GateOp.and,[s.1.val,w]⟩] from rfl,
      ov_new prior n _ (by simp) GateOp.and _ _ hc hw]
    change ((run prior (List.ofFn x)).getD s.1.val false &&
      ((run prior (List.ofFn x)).getD w false && true)) = _
    rw [show (run prior (List.ofFn x)).getD s.1.val false = x s.1 from append_literal prior x s.1,
      show (run prior (List.ofFn x)).getD w false = _ from hv x]
    simp [starSignal]
  have hclean : dc n F (prior++[a]) ≤ dc n F prior := by
    have hd := dc_snoc n F prior a
    rw [ite_eq_right (by
      rintro ⟨_,x,hx,hf⟩
      have ht : starSignal s x = true := (hvalA x).symm.trans hx
      exact Bool.noConfusion ((hs x ht).symm.trans hf))] at hd
    simpa using hd
  refine ⟨h++[a],n+prior.length,?_,?_,?_,?_,?_⟩
  · rw [← List.append_assoc]
    exact ok_snoc hok (Or.inl rfl) hc hw
  · simp only [List.length_append, List.length_singleton]
    simpa only [List.length_map] using Nat.add_le_add_right hlen 1
  · rw [← List.append_assoc]
    exact hclean.trans hdc
  · dsimp [prior]
    simp
  · rw [← List.append_assoc]
    exact hvalA

lemma star_append_one {n : ℕ} (F : (Fin n → Bool) → Bool)
    (s : StarTriple n) (hs : ∀ x, starSignal s x = true → F x = true)
    (gs : List Gate) (hgs : Ok n gs) (old : Option ℕ)
    (hb : ∀ w, old = some w → w < n + gs.length) :
    ∃ (tail : List Gate) (o : Option ℕ), Ok n (gs ++ tail) ∧ tail.length ≤ starBudget s ∧
      dc n F (gs ++ tail) ≤ dc n F gs ∧ (∀ w, o = some w → w < n+(gs++tail).length) ∧
      ∀ x : Fin n → Bool, ov (gs++tail) (List.ofFn x) o =
        (ov gs (List.ofFn x) old || starSignal s x) := by
  classical
  obtain ⟨h,t,hok,hlen,hdc,ht,hstar⟩ := star_append_gate F s hs gs hgs
  cases old with
  | none =>
    refine ⟨h, some t, hok, by unfold starBudget; omega, hdc, ?_, ?_⟩
    · intro w he
      cases he
      exact ht
    · intro x
      simp [ov, ← hstar x]
  | some w =>
    let prior := gs ++ h
    let g : Gate := ⟨GateOp.or,[w,t]⟩
    have hw := hb w rfl
    have hw' : w < n+prior.length := by dsimp [prior]; simp; omega
    refine ⟨h++[g], some (n+prior.length), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]
      exact ok_snoc hok (Or.inr rfl) hw' ht
    · simp [starBudget]
      omega
    · rw [← List.append_assoc]
      have hd := dc_snoc n F prior g
      rw [ite_eq_right (by simp [g])] at hd
      exact (Nat.add_zero _ ▸ hd).trans hdc
    · intro v he
      cases he
      dsimp [prior]
      simp
    · intro x
      rw [← List.append_assoc]
      change ov (prior++[⟨GateOp.or,[w,t]⟩]) _ _ = _
      rw [ov_new prior n _ (by simp) _ _ _ hw' ht]
      change ((run prior (List.ofFn x)).getD w false ||
        ((run prior (List.ofFn x)).getD t false || false)) = _
      rw [show (run prior (List.ofFn x)).getD w false = _ from
        run_prefix gs h _ w (by simpa using hw)]
      rw [show (run prior (List.ofFn x)).getD t false = _ from hstar x]
      simp [ov]

lemma stars_append {n : ℕ} (F : (Fin n → Bool) → Bool) (stars : List (StarTriple n))
    (hs : ∀ s ∈ stars, ∀ x, starSignal s x = true → F x = true)
    (gs : List Gate) (hgs : Ok n gs) (old : Option ℕ)
    (hb : ∀ w, old = some w → w < n+gs.length) :
    ∃ (tail : List Gate) (o : Option ℕ), Ok n (gs ++ tail) ∧
      tail.length ≤ (stars.map starBudget).sum ∧ dc n F (gs ++ tail) ≤ dc n F gs ∧
      (∀ w, o = some w → w < n+(gs++tail).length) ∧
      ∀ x : Fin n → Bool, ov (gs++tail) (List.ofFn x) o =
        (ov gs (List.ofFn x) old || stars.any (fun s => starSignal s x)) := by
  induction stars generalizing gs old with
  | nil =>
    exact ⟨[],old,by simpa using hgs,by simp,by simp,by simpa using hb,by simp⟩
  | cons s stars ih =>
    obtain ⟨h,t,hok,hlen,hdc,ht,hval⟩ := star_append_one F s (hs s (by simp)) gs hgs old hb
    obtain ⟨h',o,hok',hlen',hdc',ht',hval'⟩ := ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))
      (gs++h) hok t ht
    refine ⟨h++h',o,?_,?_,?_,?_,?_⟩
    · simpa only [List.append_assoc] using hok'
    · simp only [List.map_cons, List.sum_cons, List.length_append]
      omega
    · simpa only [List.append_assoc] using hdc'.trans hdc
    · simpa only [List.append_assoc] using ht'
    · intro x
      rw [← List.append_assoc, hval' x,hval x]
      simp [Bool.or_assoc]

def StarEdge {n : ℕ} (s : StarTriple n) (u v : Fin n) : Prop :=
  (u = s.1 ∧ v ∈ s.2.1 :: s.2.2) ∨ (v = s.1 ∧ u ∈ s.2.1 :: s.2.2)

lemma star_truth {n : ℕ} (s : StarTriple n) (x : Fin n → Bool) :
    starSignal s x = true ↔ x s.1 = true ∧ ∃ v ∈ s.2.1 :: s.2.2, x v = true := by
  simp [starSignal]

lemma graph_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ HasEdge G {i | x i = true} := by
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_eq,HasEdge,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨a,ha,b,hb,hab⟩
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ⟨a,b,hab,ha,hb⟩

lemma zero_context_iff {n : ℕ} (pre post : List Gate) (out : ℕ) (x : Fin n → Bool) :
    (selectedCircuit pre ZeroGate post out).eval (List.ofFn x) = true ↔
      selectedContext pre post out {i | x i = true} False := by
  have h := selected_eval pre post out ZeroGate {i | x i = true}
  rw [selectedInput_support] at h
  simpa only [selectedSignal,selectedValue,ZeroGate,List.map_nil,GateOp.eval,List.any_nil,
    Bool.false_eq_true] using h

lemma repair_formula {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ) (stars : List (StarTriple n))
    (h2 : TopForm.IsAO2 n (selectedCircuit pre g post out))
    (hF : circuitFun n (selectedCircuit pre g post out) = graphFun G ∅)
    (hSafe : ∀ s ∈ stars, ∀ v ∈ s.2.1 :: s.2.2, G.Adj s.1 v)
    (hCover : ∀ u v, Pivotal G (selectedContext pre post out) u v →
      ∃ s ∈ stars, StarEdge s u v) (x : Fin n → Bool) :
    ((selectedCircuit pre ZeroGate post out).eval (List.ofFn x) ||
      stars.any (fun s => starSignal s x)) = graphFun G ∅ x := by
  classical
  have hS : Exact G (selectedContext pre post out) (selectedSignal pre g) := by
    apply (selected_computes_iff G pre post out g).1
    intro y
    have hy := congrFun hF y
    change (selectedCircuit pre g post out).eval (List.ofFn y) = graphFun G ∅ y at hy
    simpa [graphFun] using hy
  have hK := selectedContext_mono (n := n) pre post out
    (fun z hz => h2.1 z (List.mem_append_left _ hz))
    (fun z hz => h2.1 z (List.mem_append_right _ (List.mem_cons_of_mem _ hz)))
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true,List.any_eq_true,graph_support,zero_context_iff]
  constructor
  · rintro (hz|⟨s,hs,hx⟩)
    · exact (cofactor_decomposition hK hS _).2 (Or.inl hz)
    · obtain ⟨hc,v,hv,hxv⟩ := (star_truth s x).1 hx
      exact ⟨s.1,hc,v,hxv,hSafe s hs v hv⟩
  · intro he
    rcases (cofactor_decomposition hK hS _).1 he with hz|⟨u,hu,v,hv,huv⟩
    · exact Or.inl hz
    · obtain ⟨s,hs,hse⟩ := hCover _ _ huv
      apply Or.inr
      refine ⟨s,hs,(star_truth s x).2 ?_⟩
      rcases hse with ⟨hc,hm⟩|⟨hc,hm⟩
      · subst u
        exact ⟨hu,v,hm,hv⟩
      · subst v
        exact ⟨hv,u,hm,hu⟩

lemma ok_ao {n : ℕ} (gs : List Gate) (o : ℕ) (hok : Ok n gs) :
    TopForm.IsAO2 n ⟨gs,o⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro q hq
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o',s,t,h1,h2,_⟩ := hok i hi
    rw [h1]
    exact h2
  · intro j hj i hi
    obtain ⟨o',s,t,h1,_,h3,h4⟩ := hok j hj
    have e : gateAt ⟨gs,o⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e,h1] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl <;> assumption
  · intro q hq
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o',s,t,h1,_⟩ := hok i hi
    rw [h1]
    rfl

lemma dirty_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    DirtySet n (graphFun G ∅) C.gates = TopForm.junk G C := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨hr,hop,h⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hr,hop,Finset.mem_range.mp hr,h⟩
  · intro hj
    obtain ⟨hr,hop,_,h⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hr,hop,h⟩

lemma readers_eq {n : ℕ} (C : Circuit) (T : ℕ) (h2 : TopForm.IsAO2 n C) :
    CircuitReaders n C T = TopForm.readers n C T := by
  classical
  unfold CircuitReaders Readers TopForm.readers
  apply Finset.filter_congr
  intro j hj
  obtain ⟨_,h,_,_,_⟩ := gate2 h2 (Finset.mem_range.mp hj)
  rw [h]
  simp [ReadsCut,eq_comm]

lemma fanout_exchange {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ) (stars : List (StarTriple n))
    (h2 : TopForm.IsAO2 n (selectedCircuit pre g post out))
    (hOut : out < n + (selectedCircuit pre g post out).gates.length)
    (hF : circuitFun n (selectedCircuit pre g post out) = graphFun G ∅)
    (hSafe : ∀ s ∈ stars, ∀ v ∈ s.2.1 :: s.2.2, G.Adj s.1 v)
    (hCover : ∀ u v, Pivotal G (selectedContext pre post out) u v →
      ∃ s ∈ stars, StarEdge s u v) :
    let C := selectedCircuit pre g post out
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + (TopForm.readers n C pre.length).card + 1 ≤ C.size + (stars.map starBudget).sum ∧
      (TopForm.junk G D).card ≤ ((TopForm.junk G C).erase pre.length).card := by
  classical
  let C := selectedCircuit pre g post out
  let F := graphFun G ∅
  obtain ⟨gs,o,hOk,ho,hcost,hval,hdc⟩ := compile_zero pre post g out h2 hOut F
  have hsafe' (s) (hs : s ∈ stars) (x : Fin n → Bool) (hx : starSignal s x = true) : F x = true := by
    obtain ⟨hc,v,hv,hxv⟩ := (star_truth s x).1 hx
    exact (graph_support G x).2 ⟨s.1,hc,v,hxv,hSafe s hs v hv⟩
  obtain ⟨tail,o',hOk',hcost',hdc',_,hval'⟩ := stars_append F stars hsafe' gs hOk o ho
  let zs := gs ++ tail
  let D : Circuit := ⟨zs,o'.getD (n+zs.length)⟩
  have hD (x : Fin n → Bool) : D.eval (List.ofFn x) = ov zs (List.ofFn x) o' := by
    cases h : o' with
    | none =>
      change (run zs (List.ofFn x)).getD (o'.getD _) false = _
      rw [h]
      exact List.getD_eq_default _ _ (by simp [run_length])
    | some w => simp [D,Circuit.eval,Circuit.wires,h,ov,run]
  refine ⟨D,ok_ao _ _ hOk',?_,?_,?_⟩
  · funext x
    change D.eval (List.ofFn x) = _
    rw [hD,hval',hval,repair_formula G pre post g out stars h2 hF hSafe hCover x]
  · rw [← readers_eq _ _ h2]
    change (gs ++ tail).length + _ + 1 ≤ _ + _
    rw [List.length_append]
    omega
  · rw [← dirty_eq_junk G D,← dirty_eq_junk G C]
    exact hdc'.trans hdc

lemma selected_split {C : Circuit} {t : ℕ} {g : Gate} (ht : C.gates[t]? = some g) :
    selectedCircuit (C.gates.take t) g (C.gates.drop (t + 1)) C.output = C := by
  obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp ht
  have hlist : C.gates.take t ++ g :: C.gates.drop (t + 1) = C.gates := by
    rw [← hg, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  cases C
  simp only [selectedCircuit, hlist]

noncomputable def gateContext {n : ℕ} (C : Circuit) (t : ℕ) : Set (Fin n) → Prop → Prop :=
  selectedContext (C.gates.take t) (C.gates.drop (t+1)) C.output

lemma circuit_fanout_exchange {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (t : ℕ) (ht : t < C.gates.length) (stars : List (StarTriple n))
    (h2 : TopForm.IsAO2 n C) (hOut : C.output < n+C.gates.length)
    (hF : circuitFun n C = graphFun G ∅)
    (hSafe : ∀ s ∈ stars, ∀ v ∈ s.2.1 :: s.2.2, G.Adj s.1 v)
    (hCover : ∀ u v, Pivotal G (gateContext C t) u v → ∃ s ∈ stars, StarEdge s u v) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      D.size + (TopForm.readers n C t).card + 1 ≤ C.size + (stars.map starBudget).sum ∧
      (TopForm.junk G D).card ≤ ((TopForm.junk G C).erase t).card := by
  let pre := C.gates.take t
  let post := C.gates.drop (t+1)
  let g := C.gates[t]
  have hs : selectedCircuit pre g post C.output = C := selected_split (List.getElem?_eq_getElem ht)
  have hlen : pre.length = t := by simp [pre,Nat.min_eq_left ht.le]
  simpa only [hs,hlen] using fanout_exchange G pre post g C.output stars
    (hs ▸ h2) (hs ▸ hOut) (hs ▸ hF) hSafe hCover

lemma least_output_in_range {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : TopForm.IsLeastAO G C) (hne : 0 < C.gates.length) :
    C.output < n+C.gates.length := by
  by_contra! hout
  let D : Circuit := ⟨[],n⟩
  have hd : TopForm.IsAO2 n D := ok_ao [] n (by intro j hj; simp at hj)
  have hf : circuitFun n D = graphFun G ∅ := by
    rw [← hC.2.1]
    funext x
    change (List.ofFn x).getD n false = (run C.gates (List.ofFn x)).getD C.output false
    rw [List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simpa [run_length] using hout)]
  have hsmall := hC.2.2 D hd hf
  change C.gates.length ≤ 0 at hsmall
  omega

lemma least_fanout_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (t : ℕ) (ht : t < C.gates.length) (stars : List (StarTriple n))
    (hC : TopForm.IsLeastAO G C)
    (hSafe : ∀ s ∈ stars, ∀ v ∈ s.2.1 :: s.2.2, G.Adj s.1 v)
    (hCover : ∀ u v, Pivotal G (gateContext C t) u v → ∃ s ∈ stars, StarEdge s u v) :
    (TopForm.readers n C t).card + 1 ≤ (stars.map starBudget).sum := by
  obtain ⟨D,h2D,hFD,hsize,_⟩ := circuit_fanout_exchange G C t ht stars hC.1
    (least_output_in_range G C hC (by omega)) hC.2.1 hSafe hCover
  have hsmall := hC.2.2 D h2D hFD
  omega

lemma junk_min_fanout_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (t : ℕ) (ht : t ∈ TopForm.junk G C) (stars : List (StarTriple n))
    (hC : TopForm.IsLeastAO G C)
    (hMin : ∀ D, TopForm.IsLeastAO G D → (TopForm.junk G C).card ≤ (TopForm.junk G D).card)
    (hSafe : ∀ s ∈ stars, ∀ v ∈ s.2.1 :: s.2.2, G.Adj s.1 v)
    (hCover : ∀ u v, Pivotal G (gateContext C t) u v → ∃ s ∈ stars, StarEdge s u v) :
    (TopForm.readers n C t).card + 1 < (stars.map starBudget).sum := by
  classical
  have ht' : t < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  obtain ⟨D,h2D,hFD,hsize,hjunk⟩ := circuit_fanout_exchange G C t ht' stars hC.1
    (least_output_in_range G C hC (by omega)) hC.2.1 hSafe hCover
  by_contra! hbudget
  have hsz : D.size ≤ C.size := by omega
  have hleast : TopForm.IsLeastAO G D := ⟨h2D,hFD,fun E h2E hFE => hsz.trans (hC.2.2 E h2E hFE)⟩
  have hh := hMin D hleast
  have he := Finset.card_erase_lt_of_mem ht
  omega

end FanoutBudget
end PEqualNP.Outside.L_meta_1031.FreshBudget
