import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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
    rw [this, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

def appendOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.size⟩

lemma appendOr_size (n : ℕ) (C : Circuit) (a b : ℕ) :
    (appendOr n C a b).size = C.size + 1 := by
  simp [appendOr, Circuit.size]

lemma appendOr_fanInTwo (n : ℕ) (C : Circuit) (a b : ℕ) (h : FanInTwo C) :
    FanInTwo (appendOr n C a b) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · obtain rfl := List.mem_singleton.mp hg
    simp

lemma appendOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) :
    (appendOr n C a b).eval (List.ofFn x) =
      ((C.wires (List.ofFn x)).getD a false ||
        (C.wires (List.ofFn x)).getD b false) := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    exact (length_wiresFrom C.gates (List.ofFn x)).trans (by simp [Circuit.size])
  change ((C.gates ++ [(⟨GateOp.or, [a, b]⟩ : Gate)]).foldl _ (List.ofFn x)).getD
    (n + C.size) false = _
  rw [List.foldl_append]
  change (C.wires (List.ofFn x) ++
    [GateOp.or.eval ([a, b].map fun i => (C.wires (List.ofFn x)).getD i false)]).getD
      (n + C.size) false = _
  rw [← hlen, getD_snoc_eq]
  simp [GateOp.eval]

lemma wire_lt_of_true (n : ℕ) (C : Circuit) (a : ℕ)
    (htrue : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD a false = true) :
    a < n + C.size := by
  obtain ⟨x, hx⟩ := htrue
  by_contra h
  have hlen : (C.wires (List.ofFn x)).length ≤ a := by
    change (wiresFrom C.gates (List.ofFn x)).length ≤ a
    rw [length_wiresFrom]
    simpa [Circuit.size] using (show n + C.size ≤ a by omega)
  rw [List.getD_eq_default _ _ hlen] at hx
  contradiction

lemma wire_internal_of_singletons (n : ℕ) (C : Circuit) (a : ℕ)
    (htrue : ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD a false = true)
    (hsingle : ∀ i : Fin n,
      (C.wires (List.ofFn (fun j : Fin n => decide (j = i)))).getD a false = false) :
    n ≤ a ∧ a < n + C.size := by
  constructor
  · by_contra h
    have ha : a < n := by omega
    have hs := hsingle ⟨a, ha⟩
    change (wiresFrom C.gates _).getD a false = false at hs
    rw [getD_wiresFrom C.gates _ a (by simpa)] at hs
    simp [ha] at hs
  · exact wire_lt_of_true n C a htrue

lemma incomparable_wires_internal (n : ℕ) (C : Circuit) (a b : ℕ)
    (ha : ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = true ∧
      (C.wires (List.ofFn x)).getD b false = false)
    (hb : ∃ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = false ∧
      (C.wires (List.ofFn x)).getD b false = true)
    (hsingle : ∀ i : Fin n,
      ((C.wires (List.ofFn (fun j : Fin n => decide (j = i)))).getD a false ||
        (C.wires (List.ofFn (fun j : Fin n => decide (j = i)))).getD b false) = false) :
    n ≤ a ∧ a < n + C.size ∧ n ≤ b ∧ b < n + C.size ∧ a ≠ b := by
  have hA := wire_internal_of_singletons n C a
    (ha.imp fun _ h => h.1) (fun i => (Bool.or_eq_false_iff.mp (hsingle i)).1)
  have hB := wire_internal_of_singletons n C b
    (hb.imp fun _ h => h.2) (fun i => (Bool.or_eq_false_iff.mp (hsingle i)).2)
  refine ⟨hA.1, hA.2, hB.1, hB.2, ?_⟩
  intro heq
  obtain ⟨x, hx, hy⟩ := ha
  rw [heq, hy] at hx
  contradiction

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this


def eraseLast (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) : Fin n :=
  if h : i.val < n then ⟨i.val, h⟩ else ⟨0, hn⟩

lemma update_relabel_eq_lastCases (n : ℕ) (hn : 0 < n)
    (σ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1))
    (hp : σ p = Fin.last n) (b : Bool) (y : Fin n → Bool) :
    Function.update (y ∘ (eraseLast n hn ∘ σ)) p b =
      (Fin.lastCases b y : Fin (n + 1) → Bool) ∘ σ := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [hp]
  · have hne : σ i ≠ Fin.last n := by
      intro he
      exact hi (σ.injective (he.trans hp.symm))
    have hlt : (σ i).val < n := by
      have := (σ i).isLt
      have hneval : (σ i).val ≠ n := by
        intro he
        apply hne
        exact Fin.ext he
      omega
    rw [Function.update_of_ne hi]
    simp only [Function.comp_apply, eraseLast, dite_eq_left hlt]
    exact (Fin.lastCases_castSucc (motive := fun _ => Bool)
      (last := b) (cast := y) ⟨(σ i).val, hlt⟩).symm

lemma restriction_transport (n : ℕ) (hn : 0 < n)
    (f : (Fin (n + 1) → Bool) → Bool) (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (hp : σ p = Fin.last n) (b : Bool) (s : ℕ)
    (h : HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s) :
    HasCircuitSize n
      (fun y => f ((Fin.lastCases b y : Fin (n + 1) → Bool) ∘ σ)) s := by
  have ht := relabel_size (eraseLast n hn ∘ σ) _ s h
  have he : (fun y : Fin n → Bool =>
      f (Function.update (y ∘ (eraseLast n hn ∘ σ)) p b)) =
      (fun y => f ((Fin.lastCases b y : Fin (n + 1) → Bool) ∘ σ)) := by
    funext y
    rw [update_relabel_eq_lastCases n hn σ p hp]
  rwa [he] at ht

lemma restrict_or_of_simulation (n m : ℕ) (C D : Circuit) (a b a' b' : ℕ)
    (ρ : (Fin n → Bool) → (Fin m → Bool)) (s : ℕ)
    (hD : FanInTwo D) (hsize : D.size + 1 ≤ s)
    (ha : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD a' false =
      (C.wires (List.ofFn (ρ x))).getD a false)
    (hb : ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD b' false =
      (C.wires (List.ofFn (ρ x))).getD b false) :
    HasCircuitSize n (fun x =>
      (C.wires (List.ofFn (ρ x))).getD a false ||
        (C.wires (List.ofFn (ρ x))).getD b false) s := by
  refine ⟨appendOr n D a' b', appendOr_fanInTwo n D a' b' hD, ?_, ?_⟩
  · simpa [appendOr_size] using hsize
  · intro x
    rw [appendOr_eval, ha, hb]

def statusValue (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr i => w.getD i false

def statusOrCost : Bool ⊕ ℕ → Bool ⊕ ℕ → ℕ
  | .inr i, .inr j => if i = j then 0 else 1
  | _, _ => 0

lemma or_statuses_nonconstant (n : ℕ) (D : Circuit) (s t : Bool ⊕ ℕ)
    (hD : FanInTwo D)
    (hnc : ∃ x y : Fin n → Bool,
      (statusValue (D.wires (List.ofFn x)) s || statusValue (D.wires (List.ofFn x)) t) ≠
      (statusValue (D.wires (List.ofFn y)) s || statusValue (D.wires (List.ofFn y)) t)) :
    HasCircuitSize n
      (fun x => statusValue (D.wires (List.ofFn x)) s ||
        statusValue (D.wires (List.ofFn x)) t)
      (D.size + statusOrCost s t) := by
  cases s with
  | inl a =>
    cases t with
    | inl b =>
      obtain ⟨x, y, hxy⟩ := hnc
      exact False.elim (hxy rfl)
    | inr j =>
      cases a with
      | false =>
        refine ⟨⟨D.gates, j⟩, hD, ?_, ?_⟩
        · simp [Circuit.size, statusOrCost]
        · intro x
          simp [Circuit.eval, Circuit.wires, statusValue]
      | true =>
        obtain ⟨x, y, hxy⟩ := hnc
        simp [statusValue] at hxy
  | inr i =>
    cases t with
    | inl b =>
      cases b with
      | false =>
        refine ⟨⟨D.gates, i⟩, hD, ?_, ?_⟩
        · simp [Circuit.size, statusOrCost]
        · intro x
          simp [Circuit.eval, Circuit.wires, statusValue]
      | true =>
        obtain ⟨x, y, hxy⟩ := hnc
        simp [statusValue] at hxy
    | inr j =>
      by_cases hij : i = j
      · subst j
        refine ⟨⟨D.gates, i⟩, hD, ?_, ?_⟩
        · simp [Circuit.size, statusOrCost]
        · intro x
          simp [Circuit.eval, Circuit.wires, statusValue]
      · refine ⟨appendOr n D i j, appendOr_fanInTwo n D i j hD, ?_, ?_⟩
        · simp [appendOr_size, statusOrCost, hij]
        · intro x
          exact appendOr_eval n D i j x

lemma restriction_exists_of_coordinate_bound
    (G U : (Fin 10 → Bool) → Bool)
    (hsym : ∀ p : Fin 10, ∃ σ : Equiv.Perm (Fin 10),
      σ p = Fin.last 9 ∧ ∀ x : Fin 10 → Bool, G (x ∘ σ) = G x)
    (hbound : ∃ (p : Fin 10) (b : Bool),
      HasCircuitSize 10 (fun x => U (Function.update x p b))
        (if b = true then 10 else 15)) :
    ∃ (σ : Equiv.Perm (Fin 10)) (b : Bool) (C : Circuit),
      (∀ x : Fin 10 → Bool, G (x ∘ σ) = G x) ∧ FanInTwo C ∧
        C.size ≤ (if b = true then 10 else 15) ∧
          ∀ y : Fin 9 → Bool,
            C.eval (List.ofFn y) = U ((Fin.lastCases b y : Fin 10 → Bool) ∘ σ) := by
  obtain ⟨p, b, hbound⟩ := hbound
  obtain ⟨σ, hp, hσ⟩ := hsym p
  obtain ⟨C, hC, hsize, heval⟩ := restriction_transport 9 (by decide) U σ p hp b _ hbound
  exact ⟨σ, b, C, hσ, hC, hsize, heval⟩

lemma lastCases_relabel_eq_update (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1))
    (hp : σ p = Fin.last n) (b : Bool) (x : Fin (n + 1) → Bool) :
    (Fin.lastCases b (x ∘ fun j : Fin n => σ.symm j.castSucc) :
      Fin (n + 1) → Bool) ∘ σ = Function.update x p b := by
  funext i
  by_cases hi : i = p
  · subst i
    simp [hp]
  · have hne : σ i ≠ Fin.last n := by
      intro he
      exact hi (σ.injective (he.trans hp.symm))
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hne
    simp only [Function.comp_apply]
    rw [Function.update_of_ne hi, ← hj, Fin.lastCases_castSucc]
    simp only [Function.comp_apply]
    rw [hj, σ.symm_apply_apply]

lemma restriction_transport_iff (n : ℕ) (hn : 0 < n)
    (f : (Fin (n + 1) → Bool) → Bool) (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) (hp : σ p = Fin.last n) (b : Bool) (s : ℕ) :
    HasCircuitSize n
      (fun y => f ((Fin.lastCases b y : Fin (n + 1) → Bool) ∘ σ)) s ↔
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  constructor
  · intro h
    have hr := relabel_size (fun j : Fin n => σ.symm j.castSucc) _ s h
    have he : (fun x : Fin (n + 1) → Bool =>
      f ((Fin.lastCases b (x ∘ fun j : Fin n => σ.symm j.castSucc) :
        Fin (n + 1) → Bool) ∘ σ)) =
      (fun x => f (Function.update x p b)) := by
      funext x
      rw [lastCases_relabel_eq_update n σ p hp b x]
    rwa [he] at hr
  · exact restriction_transport n hn f σ p hp b s

lemma no_two_wins (wins : Fin 10 → Finset (Fin 3))
    (edge : Fin 10 → Fin 3 → Fin 15)
    (hmany : ∀ v : Fin 10, 2 ≤ (wins v).card)
    (hinj : ∀ (v w : Fin 10) (i j : Fin 3), i ∈ wins v → j ∈ wins w →
      edge v i = edge w j → v = w ∧ i = j) : False := by
  classical
  let Winning := Σ v : Fin 10, {i : Fin 3 // i ∈ wins v}
  let label : Winning → Fin 15 := fun a => edge a.1 a.2.val
  have hi : Function.Injective label := by
    intro a b hab
    obtain ⟨v, i, hi⟩ := a
    obtain ⟨w, j, hj⟩ := b
    obtain ⟨rfl, rfl⟩ := hinj v w i j hi hj hab
    rfl
  have hcard : Fintype.card Winning ≤ 15 := by
    simpa using Fintype.card_le_of_injective label hi
  have hsum : Fintype.card Winning = ∑ v : Fin 10, (wins v).card := by
    simp [Winning, Fintype.card_sigma]
  have hlow : 20 ≤ ∑ v : Fin 10, (wins v).card := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 10)))
      (fun v _ => hmany v)
    simpa using hh
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 4096 in
lemma two_disjoint_rectangles_diagonal :
    ∀ A B C D : Finset (Fin 3),
      Disjoint (A ×ˢ B) (C ×ˢ D) →
      (∀ i j : Fin 3, i ≠ j → (i ∈ A ∧ j ∈ B) ∨ (i ∈ C ∧ j ∈ D)) →
      2 ≤ ((A ∩ B) ∪ (C ∩ D)).card := by
  decide


lemma no_two_rectangle_labeling {X Y : Type}
    (negative : Fin 10 → Fin 3 → X) (positive : Fin 10 → Fin 3 → Y)
    (edge : Fin 10 → Fin 3 → Fin 15) (label : Y → X → Fin 10)
    (hedge : ∀ (v w : Fin 10) (i j : Fin 3), edge v i = edge w j →
      negative v i = negative w j ∧ positive v i = positive w j)
    (hinj : ∀ v, Function.Injective (edge v))
    (hoff : ∀ (v : Fin 10) (i j : Fin 3), i ≠ j →
      label (positive v j) (negative v i) = v)
    (hrect : ∀ v : Fin 10, ∃ A B C D : Finset (Fin 3),
      Disjoint (A ×ˢ B) (C ×ˢ D) ∧
      ∀ i j : Fin 3, label (positive v j) (negative v i) = v ↔
        (i ∈ A ∧ j ∈ B) ∨ (i ∈ C ∧ j ∈ D)) : False := by
  classical
  let wins (v : Fin 10) : Finset (Fin 3) :=
    Finset.univ.filter fun i => label (positive v i) (negative v i) = v
  apply no_two_wins wins edge
  · intro v
    obtain ⟨A, B, C, D, hd, he⟩ := hrect v
    have hcover : ∀ i j : Fin 3, i ≠ j →
        (i ∈ A ∧ j ∈ B) ∨ (i ∈ C ∧ j ∈ D) := by
      intro i j hij
      exact (he i j).mp (hoff v i j hij)
    have hcount := two_disjoint_rectangles_diagonal A B C D hd hcover
    have hsub : (A ∩ B) ∪ (C ∩ D) ⊆ wins v := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (he i i).mpr ?_⟩
      simpa only [Finset.mem_union, Finset.mem_inter] using hi
    exact hcount.trans (Finset.card_le_card hsub)
  · intro v w i j hi hj he
    have hvi := (Finset.mem_filter.mp hi).2
    have hwj := (Finset.mem_filter.mp hj).2
    obtain ⟨hn, hp⟩ := hedge v w i j he
    have hvw : v = w := calc
      v = label (positive v i) (negative v i) := hvi.symm
      _ = label (positive w j) (negative w j) := by rw [hn, hp]
      _ = w := hwj
    subst w
    exact ⟨rfl, hinj v he⟩

end PEqualNP.Outside.L_meta_3821
