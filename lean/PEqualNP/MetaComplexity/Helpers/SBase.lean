import Mathlib
import PEqualNP.Defs.CircuitLowerBounds

/-!
# Theorem S-BASE (row L-meta-1032)

Sets `S i` of `q + 1` points meeting pairwise in exactly one point, a base `y`, and a list of
AND/OR gates of fan-in at most two whose outputs equal the set-ANDs on every input containing
`y` with at most `K` more points. The proof is the descent of specific gates: for each output
it runs a descent on a finite set of wires (always the largest), keeping a set `P` of points
whose growth is controlled by the exactly-one intersections.
-/

namespace PEqualNP.MetaComplexity.SBase

open PEqualNP.CircuitLowerBounds

/-- The value of wire `k` on the point set `X`: input wires read membership, gate wires apply
their operation to the wires they read (a wire not yet existing reads false), and a wire past
the end reads false. -/
def val (n : ℕ) (gs : List Gate) (X : Finset (Fin n)) (k : ℕ) : Bool :=
  if h : k < n then decide (⟨k, h⟩ ∈ X)
  else if h2 : k - n < gs.length then
    (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if hj : j < k then val n gs X j else false))
  else false
termination_by k
decreasing_by exact hj

theorem val_input {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : k < n) :
    val n gs X k = decide (⟨k, h⟩ ∈ X) := by
  rw [val]; simp [h]

theorem val_gate {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : ¬ k < n)
    (h2 : k - n < gs.length) :
    val n gs X k = (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if j < k then val n gs X j else false)) := by
  rw [val]; simp only [h, h2, dite_false, dite_true]
  congr 2

theorem val_past {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ}
    (h : n + gs.length ≤ k) : val n gs X k = false := by
  rw [val]
  have h1 : ¬ k < n := by omega
  have h2 : ¬ k - n < gs.length := by omega
  simp [h1, h2]

/-- The gate-by-gate fold of `Circuit.wires`, after `j` gates, lists the values `val`. -/
theorem foldl_take {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) :
    ∀ j, j ≤ gs.length →
    (gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (fun v : Fin n => decide (v ∈ X)))
      = List.ofFn (fun k : Fin (n + j) => val n gs X k) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [List.take_zero, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_ofFn] at h1
      simp [val_input h1]
  | succ j ih =>
    intro hj
    have hj' : j < gs.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.foldl_append,
      ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at h1
      by_cases hk : k < n + j
      · rw [List.getElem_append_left (by simpa using hk)]
        simp only [List.getElem_ofFn]
      · have hk' : k = n + j := by omega
        subst hk'
        rw [List.getElem_append_right (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton, List.getElem_ofFn]
        rw [val_gate (by omega) (by omega)]
        have : n + j - n = j := by omega
        simp only [this]
        congr 2
        funext i
        by_cases hi : i < n + j
        · simp [List.getD_eq_getElem?_getD, hi]
        · simp [List.getD_eq_getElem?_getD, hi]

theorem eval_eq {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) (o : ℕ) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn fun v : Fin n => decide (v ∈ X)) = val n gs X o := by
  unfold Circuit.eval Circuit.wires
  simp only
  have := foldl_take gs X gs.length le_rfl
  rw [List.take_length] at this
  rw [this]
  by_cases ho : o < n + gs.length
  · simp [List.getD_eq_getElem?_getD, ho]
  · rw [val_past (by omega)]
    simp [List.getD_eq_getElem?_getD, ho]

theorem op_eval_mono {op : GateOp} (hop : op = .and ∨ op = .or) (l : List ℕ) (f f' : ℕ → Bool)
    (hff : ∀ a ∈ l, f a = true → f' a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at h ⊢
    intro a ha; exact hff a ha (h a ha)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at h ⊢
    obtain ⟨a, ha, hfa⟩ := h
    exact ⟨a, ha, hff a ha hfa⟩

theorem val_mono {n : ℕ} {gs : List Gate} (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {X X' : Finset (Fin n)} (hXX : X ⊆ X') :
    ∀ k, val n gs X k = true → val n gs X' k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : k < n
    · rw [val_input h] at hk ⊢
      simp only [decide_eq_true_eq] at hk ⊢
      exact hXX hk
    · by_cases h2 : k - n < gs.length
      · rw [val_gate h h2] at hk ⊢
        refine op_eval_mono (hgs _ (List.getElem_mem _)) _ _ _ ?_ hk
        intro a _ ha
        by_cases hak : a < k
        · simp only [hak, ite_true] at ha ⊢
          exact ih a hak ha
        · simp [hak] at ha
      · rw [val_past (by omega)] at hk
        exact absurd hk (by simp)

section Main

variable {n m q K : ℕ} {S : Fin m → Finset (Fin n)} {y : Finset (Fin n)} {gs : List Gate}

/-- The gate wires specific to `i`: true on `y + S i`, false on every `y + S j`, `j ≠ i`. -/
def spec (n : ℕ) (gs : List Gate) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (i : Fin m) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter
    (fun g => val n gs (y ∪ S i) g = true ∧ ∀ j, j ≠ i → val n gs (y ∪ S j) g = false)

/-- The growth invariant of the point set `P` after `R` removals. -/
def Good (q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (i : Fin m)
    (P : Finset (Fin n)) (R : ℕ) : Prop :=
  ((S i \ y) ∩ P).card ≤ R ∧ (P.card ≤ R ∨ ∃ j0, S j0 \ y ⊆ P ∧ P.card ≤ q * R + 1)

theorem good_zero (i : Fin m) : Good q S y i ∅ 0 := by
  simp [Good]

theorem good_single {i : Fin m} {P : Finset (Fin n)} {R : ℕ} (hq : 1 ≤ q)
    (h : Good q S y i P R) (r : Fin n) : Good q S y i (insert r P) (R + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · calc ((S i \ y) ∩ insert r P).card ≤ (insert r ((S i \ y) ∩ P)).card := by
          apply Finset.card_le_card
          intro a; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
      _ ≤ ((S i \ y) ∩ P).card + 1 := Finset.card_insert_le _ _
      _ ≤ R + 1 := by omega
  · have hc := Finset.card_insert_le r P
    rcases h2 with h2 | ⟨j0, hj0, h2⟩
    · left; omega
    · right; refine ⟨j0, hj0.trans (Finset.subset_insert _ _), ?_⟩
      have : q * (R + 1) = q * R + q := by ring
      omega

theorem good_trace (hq : 1 ≤ q) (hS : ∀ i, (S i).card = q + 1)
    (hSS : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    {i : Fin m} {P : Finset (Fin n)} {R : ℕ}
    (h : Good q S y i P R) (j : Fin m) (hji : j ≠ i) :
    Good q S y i (P ∪ (S j \ y)) (R + 1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have e : (S i \ y) ∩ (P ∪ (S j \ y)) ⊆ ((S i \ y) ∩ P) ∪ (S i ∩ S j) := by
      intro a; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
    have := (Finset.card_le_card e).trans (Finset.card_union_le _ _)
    have := hSS i j (Ne.symm hji)
    omega
  · have hsd : (P ∪ (S j \ y)).card ≤ P.card + ((S j \ y) \ P).card := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff]
      apply Finset.card_le_card
      intro a; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rcases h2 with h2 | ⟨j0, hj0, h2⟩
    · right
      refine ⟨j, Finset.subset_union_right, ?_⟩
      have : ((S j \ y) \ P).card ≤ q + 1 :=
        (Finset.card_le_card (fun a ha => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 ha).1).1)).trans
          (hS j).le
      have hqR : R ≤ q * R := Nat.le_mul_of_pos_left _ hq
      have : q * (R + 1) = q * R + q := by ring
      omega
    · right
      refine ⟨j0, hj0.trans Finset.subset_union_left, ?_⟩
      have key : ((S j \ y) \ P).card ≤ q := by
        by_cases hjj : j = j0
        · subst hjj
          have : (S j \ y) \ P = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hj0
          simp [this]
        · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (hSS j j0 hjj)
          have hpj : p ∈ S j := (Finset.mem_inter.1 (hp ▸ Finset.mem_singleton_self p)).1
          have hpj0 : p ∈ S j0 := (Finset.mem_inter.1 (hp ▸ Finset.mem_singleton_self p)).2
          have sub : (S j \ y) \ P ⊆ (S j).erase p := by
            intro a ha
            simp only [Finset.mem_sdiff] at ha
            refine Finset.mem_erase.2 ⟨?_, ha.1.1⟩
            rintro rfl
            exact ha.2 (hj0 (Finset.mem_sdiff.2 ⟨hpj0, ha.1.2⟩))
          have := Finset.card_le_card sub
          rw [Finset.card_erase_of_mem hpj, hS j] at this
          omega
      have : q * (R + 1) = q * R + q := by ring
      omega

/-- The descent. -/
theorem descent (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hq : 1 ≤ q) (hS : ∀ i, (S i).card = q + 1)
    (hSS : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (i : Fin m) :
    ∀ N, ∀ (F : Finset ℕ) (P : Finset (Fin n)) (R : ℕ), (∑ g ∈ F, 2 ^ g) < N →
      Good q S y i P R →
      (∀ g ∈ F, val n gs (y ∪ S i) g = true) →
      (∀ X : Finset (Fin n), y ∪ P ⊆ X → (X \ y).card ≤ K → ¬ S i ⊆ X →
        ∃ g ∈ F, val n gs X g = false) →
      ∃ P' R', Good q S y i P' R' ∧
        R' ≤ R + ((spec n gs S y i).filter (· < F.sup (· + 1))).card + F.card ∧
        ∀ X : Finset (Fin n), y ∪ P' ⊆ X → (X \ y).card ≤ K → S i ⊆ X := by
  have hgs' : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := fun g hg => (hgs g hg).1
  intro N
  induction N with
  | zero => intro F P R hN; omega
  | succ N ih =>
  intro F P R hN hP hF hinv
  by_cases hFe : F = ∅
  · subst hFe
    refine ⟨P, R, hP, by simp, ?_⟩
    intro X hX hK
    by_contra hS'
    obtain ⟨g, hg, _⟩ := hinv X hX hK hS'
    simp at hg
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.2 hFe
  set g := F.max' hFne with hgdef
  have hgF : g ∈ F := F.max'_mem hFne
  have hlt : ∀ g' ∈ F, g' ≠ g → g' < g := fun g' hg' hne =>
    lt_of_le_of_ne (F.le_max' g' hg') hne
  have hgtrue := hF g hgF
  have hsum_erase : ∑ x ∈ F.erase g, 2 ^ x + 2 ^ g = ∑ x ∈ F, 2 ^ x :=
    Finset.sum_erase_add F _ hgF
  have hpow : 0 < 2 ^ g := by positivity
  have hcard_erase : (F.erase g).card + 1 = F.card := Finset.card_erase_add_one hgF
  have hsup_erase : (F.erase g).sup (· + 1) ≤ F.sup (· + 1) :=
    Finset.sup_mono (Finset.erase_subset g F)
  have hfilt_mono : ∀ a b, a ≤ b → ((spec n gs S y i).filter (· < a)).card ≤
      ((spec n gs S y i).filter (· < b)).card := by
    intro a b hab
    apply Finset.card_le_card
    intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  have hg_lt_sup : g < F.sup (· + 1) := by
    have := Finset.le_sup (f := (· + 1)) hgF
    simpa using this
  -- removal: remove g and enlarge P
  have removal : ∀ (P2 : Finset (Fin n)), Good q S y i P2 (R + 1) →
      (∀ X : Finset (Fin n), y ∪ P2 ⊆ X → y ∪ P ⊆ X ∧ val n gs X g = true) →
      ∃ P' R', Good q S y i P' R' ∧
        R' ≤ R + ((spec n gs S y i).filter (· < F.sup (· + 1))).card + F.card ∧
        ∀ X : Finset (Fin n), y ∪ P' ⊆ X → (X \ y).card ≤ K → S i ⊆ X := by
    intro P2 hP2 hX2
    obtain ⟨P', R', h1, h2, h3⟩ := ih (F.erase g) P2 (R + 1) (by omega) hP2
      (fun g' hg' => hF g' (Finset.mem_of_mem_erase hg'))
      (by
        intro X hX hK hSX
        obtain ⟨hXP, hXg⟩ := hX2 X hX
        obtain ⟨g', hg', hf⟩ := hinv X hXP hK hSX
        refine ⟨g', Finset.mem_erase.2 ⟨?_, hg'⟩, hf⟩
        rintro rfl; rw [hXg] at hf; exact absurd hf (by simp))
    refine ⟨P', R', h1, ?_, h3⟩
    have := hfilt_mono _ _ hsup_erase
    omega
  by_cases hns : ∃ j, j ≠ i ∧ val n gs (y ∪ S j) g = true
  · -- (b') a non-specific wire: add the trace of S j
    obtain ⟨j, hji, hj⟩ := hns
    apply removal (P ∪ (S j \ y)) (good_trace hq hS hSS hP j hji)
    intro X hX
    refine ⟨fun a ha => hX ?_, ?_⟩
    · simp only [Finset.mem_union] at ha ⊢; tauto
    · apply val_mono hgs' _ g hj
      intro a ha
      apply hX
      simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
      tauto
  push Not at hns
  by_cases hin : g < n
  · -- (a'), (b') an input wire: add its point
    apply removal (insert ⟨g, hin⟩ P) (good_single hq hP _)
    intro X hX
    refine ⟨fun a ha => hX ?_, ?_⟩
    · simp only [Finset.mem_union, Finset.mem_insert] at ha ⊢; tauto
    · rw [val_input hin]
      simp only [decide_eq_true_eq]
      apply hX
      simp
  by_cases hend : g - n < gs.length
  swap
  · rw [val_past (by omega)] at hgtrue; exact absurd hgtrue (by simp)
  -- g is a specific gate
  have hspec : g ∈ spec n gs S y i := by
    simp only [spec, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, hgtrue, fun j hj => ?_⟩
    have := hns j hj
    simpa using this
  have hstrict : ((spec n gs S y i).filter (· < g)).card <
      ((spec n gs S y i).filter (· < F.sup (· + 1))).card := by
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
    · intro hsub
      have := hsub (Finset.mem_filter.2 ⟨hspec, hg_lt_sup⟩)
      simp at this
  set G := gs[g - n] with hG
  have hGop := (hgs G (List.getElem_mem _)).1
  have hGlen := (hgs G (List.getElem_mem _)).2
  have hval := val_gate (X := y ∪ S i) hin hend
  rw [hval] at hgtrue
  rcases hGop with hand | hor
  · -- (d) a specific AND: replace g by its inputs
    rw [← hG, hand] at hgtrue
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hgtrue
    have hch : ∀ k ∈ G.inputs, k < g ∧ val n gs (y ∪ S i) k = true := by
      intro k hk
      have := hgtrue k hk
      by_cases hkg : k < g
      · simp only [hkg, ite_true] at this; exact ⟨hkg, this⟩
      · simp [hkg] at this
    set C := G.inputs.toFinset with hC
    have hCcard : C.card ≤ 2 := (List.toFinset_card_le _).trans hGlen
    have hClt : ∀ k ∈ C, k < g := fun k hk => (hch k (List.mem_toFinset.1 hk)).1
    obtain ⟨P', R', h1, h2, h3⟩ := ih ((F.erase g) ∪ C) P R
      (by
        have h1 := Finset.sum_union_inter (f := fun x => 2 ^ x) (s₁ := F.erase g) (s₂ := C)
        have h2 : ∑ k ∈ C, 2 ^ k < 2 ^ g := Nat.geomSum_lt le_rfl hClt
        omega)
      hP
      (by
        intro g' hg'
        rcases Finset.mem_union.1 hg' with hg' | hg'
        · exact hF g' (Finset.mem_of_mem_erase hg')
        · exact (hch g' (List.mem_toFinset.1 hg')).2)
      (by
        intro X hX hK hSX
        obtain ⟨g', hg', hf⟩ := hinv X hX hK hSX
        by_cases hgg : g' = g
        · subst hgg
          rw [val_gate hin hend, ← hG, hand] at hf
          simp only [GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id] at hf
          obtain ⟨k, hk, hkf⟩ := hf
          have hkg := (hch k hk).1
          simp only [hkg, ite_true] at hkf
          exact ⟨k, Finset.mem_union_right _ (List.mem_toFinset.2 hk), by simpa using hkf⟩
        · exact ⟨g', Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hgg, hg'⟩), hf⟩)
    refine ⟨P', R', h1, ?_, h3⟩
    have hsup : ((F.erase g) ∪ C).sup (· + 1) ≤ g := by
      apply Finset.sup_le
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hlt x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
      · exact hClt x hx
    have := hfilt_mono _ _ hsup
    have := Finset.card_union_le (F.erase g) C
    omega
  · -- (c) a specific OR: replace g by an input true on y + S i
    rw [← hG, hor] at hgtrue
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hgtrue
    obtain ⟨k, hk, hkt⟩ := hgtrue
    have hkg : k < g := by
      by_contra hkg; simp [hkg] at hkt
    simp only [hkg, ite_true] at hkt
    obtain ⟨P', R', h1, h2, h3⟩ := ih (insert k (F.erase g)) P R
      (by
        have h1 := Finset.sum_union_inter (f := fun x => 2 ^ x) (s₁ := {k}) (s₂ := F.erase g)
        rw [← Finset.insert_eq, Finset.sum_singleton] at h1
        have h2 : 2 ^ k < 2 ^ g := Nat.pow_lt_pow_right (by norm_num) hkg
        omega)
      hP
      (by
        intro g' hg'
        rcases Finset.mem_insert.1 hg' with rfl | hg'
        · exact hkt
        · exact hF g' (Finset.mem_of_mem_erase hg'))
      (by
        intro X hX hK hSX
        obtain ⟨g', hg', hf⟩ := hinv X hX hK hSX
        by_cases hgg : g' = g
        · subst hgg
          rw [val_gate hin hend, ← hG, hor] at hf
          simp only [GateOp.eval, List.any_map, List.any_eq_false, Function.comp_apply, id] at hf
          have := hf k hk
          simp only [hkg, ite_true] at this
          exact ⟨k, Finset.mem_insert_self _ _, by simpa using this⟩
        · exact ⟨g', Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hgg, hg'⟩), hf⟩)
    refine ⟨P', R', h1, ?_, h3⟩
    have hsup : (insert k (F.erase g)).sup (· + 1) ≤ g := by
      apply Finset.sup_le
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hkg
      · exact hlt x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    have := hfilt_mono _ _ hsup
    have := Finset.card_insert_le k (F.erase g)
    omega

theorem card_sdiff_le_compl (A y : Finset (Fin n)) : (A \ y).card ≤ n - y.card := by
  have := Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ A) (le_refl y))
  rw [Finset.card_univ_sdiff, Fintype.card_fin] at this
  exact this

/-- The count for one output: `min (c + 1) |S i \ y|` is at most the number of gates specific
to `i`, plus one. -/
theorem per_output (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hq : 1 ≤ q) (hS : ∀ i, (S i).card = q + 1)
    (hSS : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (out : Fin m → ℕ)
    (hout : ∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) →
      ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (i : Fin m) (c : ℕ) (hc : c * q < K ∨ n ≤ y.card + K) :
    min (c + 1) (S i \ y).card ≤ (spec n gs S y i).card + 1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · have := min_le_left 1 (S i \ y).card
    omega
  have hrow : ∀ X : Finset (Fin n), y ⊆ X → (X \ y).card ≤ K →
      val n gs X (out i) = decide (S i ⊆ X) := by
    intro X hyX hK
    have := hout i (fun v => decide (v ∈ X)) (by intro v hv; simpa using hyX hv)
      (by simpa using hK)
    rw [eval_eq] at this
    rw [this]
    simp [Finset.subset_iff]
  have htK : (S i \ y).card ≤ K := by
    rcases hc with hc | hc
    · have h1 : (S i \ y).card ≤ (S i).card := Finset.card_le_card Finset.sdiff_subset
      have h2 : q ≤ c * q := Nat.le_mul_of_pos_left q hc0
      rw [hS i] at h1
      omega
    · have := card_sdiff_le_compl (S i) y
      omega
  have htrue : val n gs (y ∪ S i) (out i) = true := by
    rw [hrow _ Finset.subset_union_left (by rw [Finset.union_sdiff_left]; exact htK)]
    simp
  obtain ⟨P', R', hG, hR, hend⟩ := descent (K := K) (y := y) hgs hq hS hSS i (2 ^ (out i) + 1) {out i} ∅ 0
    (by simp) (good_zero i) (by simpa using htrue)
    (by
      intro X hX hK hSX
      refine ⟨out i, by simp, ?_⟩
      rw [hrow X (Finset.subset_union_left.trans hX) hK]
      simpa using hSX)
  have hR' : R' ≤ (spec n gs S y i).card + 1 := by
    have := Finset.card_filter_le (spec n gs S y i) (· < ({out i} : Finset ℕ).sup (· + 1))
    simp only [Finset.card_singleton, zero_add] at hR
    omega
  obtain ⟨hG1, hG2⟩ := hG
  by_cases hP : (P' \ y).card ≤ K
  · have hsub := hend (y ∪ P') subset_rfl (by rw [Finset.union_sdiff_left]; exact hP)
    have hsub' : S i \ y ⊆ P' := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have := hsub ha.1
      rw [Finset.mem_union] at this
      tauto
    rw [Finset.inter_eq_left.2 hsub'] at hG1
    have := min_le_right (c + 1) (S i \ y).card
    omega
  · push Not at hP
    have hm := min_le_left (c + 1) (S i \ y).card
    rcases hc with hc | hc
    · have hPc : (P' \ y).card ≤ P'.card := Finset.card_le_card Finset.sdiff_subset
      have hcq : c ≤ c * q := Nat.le_mul_of_pos_right c hq
      rcases hG2 with h | ⟨j0, _, h⟩
      · omega
      · have h' : c * q < R' * q := by rw [mul_comm R' q]; omega
        have := Nat.lt_of_mul_lt_mul_right h'
        omega
    · have := card_sdiff_le_compl P' y
      omega

end Main

/-- Theorem S-BASE (row L-meta-1032). -/
theorem sbase : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) → ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → (c * q < K ∨ n ≤ y.card + K) → ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), min (c + 1) (S i \ y).card ≤ gates.length + (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
  intro q n m K S y hq hS hSS gates out hgs hout c _ hc
  set T := Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card) with hT
  have hdisj : (T : Set (Fin m)).PairwiseDisjoint (spec n gates S y) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    simp only [spec, Finset.mem_filter] at hgi hgj
    have := hgi.2.2 j (Ne.symm hij)
    rw [hgj.2.1] at this
    exact absurd this (by simp)
  have hsub : T.biUnion (spec n gates S y) ⊆ Finset.Ico n (n + gates.length) := by
    intro g hg
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hg
    exact (Finset.mem_filter.1 hi).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico] at hcard
  calc ∑ i ∈ T, min (c + 1) (S i \ y).card
      ≤ ∑ i ∈ T, ((spec n gates S y i).card + 1) :=
        Finset.sum_le_sum (fun i _ => per_output (K := K) hgs (by omega) hS hSS out hout i c hc)
    _ = ∑ i ∈ T, (spec n gates S y i).card + T.card := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ gates.length + T.card := by omega

end PEqualNP.MetaComplexity.SBase
