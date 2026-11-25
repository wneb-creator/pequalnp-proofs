import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_670_aux.Cases

def fP (x3 : Fin 9 → Bool) : Bool := x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))

def AUT : Fin 12 → Fin 9 → Fin 9 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![0, 5, 8, 3, 4, 1, 7, 6, 2], ![1, 0, 5, 8, 6, 2, 4, 7, 3],
    ![1, 2, 3, 8, 6, 0, 7, 4, 5], ![2, 1, 0, 5, 7, 3, 6, 4, 8], ![2, 3, 8, 5, 7, 1, 4, 6, 0],
    ![3, 2, 1, 0, 4, 8, 7, 6, 5], ![3, 8, 5, 0, 4, 2, 6, 7, 1], ![5, 0, 1, 2, 7, 8, 4, 6, 3],
    ![5, 8, 3, 2, 7, 0, 6, 4, 1], ![8, 3, 2, 1, 6, 5, 4, 7, 0], ![8, 5, 0, 1, 6, 3, 7, 4, 2]]

def RP : List (Fin 9 × Fin 9) := [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))]

lemma cov1 : ∀ i : Fin 9, ∃ a : Fin 12, AUT a i = 0 ∨ AUT a i = 4 := by decide

lemma cov2 : ∀ i j : Fin 9, i ≠ j → ∃ a : Fin 12,
    (AUT a i, AUT a j) ∈ RP ∨ (AUT a j, AUT a i) ∈ RP := by
  decide

lemma aut_b : ∀ a : Fin 12, ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    fP (![b0, b1, b2, b3, b4, b5, b6, b7, b8] ∘ AUT a) = fP ![b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
  decide

lemma aut (a : Fin 12) (x : Fin 9 → Bool) : fP (x ∘ AUT a) = fP x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
    funext k
    fin_cases k <;> rfl
  rw [hx]
  exact aut_b a _ _ _ _ _ _ _ _ _

lemma fP_single : ∀ i : Fin 9, fP (fun k => decide (k = i)) = false := by decide

lemma fP_true : fP (fun _ => true) = true := by decide

lemma fP_false : fP (fun _ => false) = false := by decide

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (z : List Bool) : C.wires z = C.gates.foldl F z := rfl

lemma getD_snoc (w : List Bool) (v : Bool) (k : ℕ) :
    (w ++ [v]).getD k false =
      if k < w.length then w.getD k false else if k = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (a : ℕ) :
    (List.ofFn x).getD a false = if h : a < n then x ⟨a, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [F]
    omega

lemma fold_pre (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl F w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [F]; omega)]
    unfold F
    rw [getD_snoc, if_pos hk]

lemma fold_sim (Inv : List Bool → List Bool → Prop) (G : Gate → Gate) :
    ∀ (gs : List Gate) (w' w : List Bool), Inv w' w →
    (∀ g ∈ gs, ∀ w' w, Inv w' w → Inv (F w' (G g)) (F w g)) →
    Inv ((gs.map G).foldl F w') (gs.foldl F w) := by
  intro gs
  induction gs with
  | nil => intro w' w h _; exact h
  | cons g gs ih =>
    intro w' w h hs
    exact ih _ _ (hs g (List.mem_cons_self ..) w' w h)
      (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg'))

def v0 (g : Gate) (x : Fin 9 → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)

lemma classify (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    (∃ c : Bool, ∀ x, v0 g x = c) ∨ (∃ i : Fin 9, ∀ x, v0 g x = x i) ∨
    (∃ i : Fin 9, ∀ x, v0 g x = !x i) ∨
    (∃ i j : Fin 9, i ≠ j ∧ ∃ b : Bool, ∀ x,
      v0 g x = if b = true then x i && x j else x i || x j) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inl ⟨true, fun x => rfl⟩
    · exact Or.inl ⟨false, fun x => rfl⟩
    · exact Or.inl ⟨true, fun x => rfl⟩
  · by_cases ha : a < 9
    · rcases hop with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩)
      · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩))
    · rcases hop with rfl | rfl | rfl
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inl ⟨true, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩
  · by_cases ha : a < 9 <;> by_cases hb : b < 9
    · by_cases hab : a = b
      · subst hab
        rcases hop with rfl | rfl | rfl
        · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩)
        · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by
            simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩))
      · have hne : (⟨a, ha⟩ : Fin 9) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
        rcases hop with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, hne, true, fun x => by
            simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, hne, false, fun x => by
            simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by
            simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩))
    · rcases hop with rfl | rfl | rfl
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨a, ha⟩, fun x => by
          simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩))
    · rcases hop with rfl | rfl | rfl
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inr (Or.inl ⟨⟨b, hb⟩, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩)
      · exact Or.inl ⟨true, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩
    · rcases hop with rfl | rfl | rfl
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inl ⟨false, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, hb, ↓reduceDIte]; simp [GateOp.eval]⟩
      · exact Or.inl ⟨true, fun x => by simp only [v0, List.map_cons, List.map_nil, getD_ofFn, ha, ↓reduceDIte]; simp [GateOp.eval]⟩
  · simp only [List.length_cons] at hl
    omega

def piT (τ : Fin 9 → Fin 9) (k : ℕ) : ℕ := if h : k < 9 then (τ ⟨k, h⟩).val else k

def rl (τ : Fin 9 → Fin 9) (g : Gate) : Gate := ⟨g.op, g.inputs.map (piT τ)⟩

def InvR (τ : Fin 9 → Fin 9) (w' w : List Bool) : Prop :=
  w'.length = w.length ∧ 9 ≤ w.length ∧ ∀ k, w'.getD (piT τ k) false = w.getD k false

lemma stepR (τ : Fin 9 → Fin 9) (g : Gate) (w' w : List Bool) (h : InvR τ w' w) :
    InvR τ (F w' (rl τ g)) (F w g) := by
  obtain ⟨hl, h9, hk⟩ := h
  have hv : (rl τ g).op.eval ((rl τ g).inputs.map fun j => w'.getD j false) =
      g.op.eval (g.inputs.map fun j => w.getD j false) := by
    simp only [rl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hk k
  refine ⟨by simp [F, hl], by simp [F]; omega, ?_⟩
  intro k
  unfold F
  rw [getD_snoc, getD_snoc, hv, hl]
  by_cases hk9 : k < 9
  · have hp : piT τ k < 9 := by
      simp only [piT, hk9, ↓reduceDIte]
      exact (τ _).isLt
    rw [if_pos (by omega), if_pos (by omega)]
    exact hk k
  · have hp : piT τ k = k := by simp only [piT, hk9, ↓reduceDIte]
    have := hk k
    rw [hp] at this ⊢
    split_ifs
    · exact this
    · rfl
    · rfl

lemma permw (gs : List Gate) (τ : Fin 9 → Fin 9) (x : Fin 9 → Bool) (k : ℕ) :
    ((gs.map (rl τ)).foldl F (List.ofFn x)).getD (piT τ k) false =
      (gs.foldl F (List.ofFn (x ∘ τ))).getD k false := by
  have h0 : InvR τ (List.ofFn x) (List.ofFn (x ∘ τ)) := by
    refine ⟨by simp, by simp, ?_⟩
    intro k
    by_cases hk : k < 9
    · simp only [piT, hk, ↓reduceDIte]
      rw [getD_ofFn, getD_ofFn, dif_pos (τ ⟨k, hk⟩).isLt, dif_pos hk]
      rfl
    · simp only [piT, hk, ↓reduceDIte]
      rw [getD_ofFn, getD_ofFn, dif_neg hk, dif_neg hk]
  exact (fold_sim (InvR τ) (rl τ) gs _ _ h0 (fun g _ w' w h => stepR τ g w' w h)).2.2 k

def sw (i : ℕ) (k : ℕ) : ℕ := if k = 9 then i else k

def rs (i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sw i)⟩

def InvS (i : ℕ) (w' w : List Bool) : Prop :=
  w'.length = w.length ∧ 10 ≤ w.length ∧ w.getD 9 false = w.getD i false ∧
    ∀ k, k ≠ 9 → w'.getD k false = w.getD k false

lemma stepS (i : ℕ) (hi : i < 9) (g : Gate) (w' w : List Bool) (h : InvS i w' w) :
    InvS i (F w' (rs i g)) (F w g) := by
  obtain ⟨hl, h10, h9, hk⟩ := h
  have hv : (rs i g).op.eval ((rs i g).inputs.map fun j => w'.getD j false) =
      g.op.eval (g.inputs.map fun j => w.getD j false) := by
    simp only [rs, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, sw]
    split_ifs with hk9
    · rw [hk9, h9]
      exact hk i (by omega)
    · exact hk k hk9
  refine ⟨by simp [F, hl], by simp [F]; omega, ?_, ?_⟩
  · unfold F
    rw [getD_snoc, getD_snoc, if_pos (by omega), if_pos (by omega)]
    exact h9
  · intro k hk9
    unfold F
    rw [getD_snoc, getD_snoc, hv, hl]
    split_ifs
    · exact hk k hk9
    · rfl
    · rfl

def fixT (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, g.inputs.filter (fun k => k != 9)⟩
  | GateOp.or => if 9 ∈ g.inputs then ⟨GateOp.and, []⟩ else g
  | GateOp.not => if g.inputs.head? = some 9 then ⟨GateOp.or, []⟩ else g
  | GateOp.mod _ => g
  | GateOp.maj => g

def fixF (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if 9 ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun k => k != 9)⟩
  | GateOp.not => if g.inputs.head? = some 9 then ⟨GateOp.and, []⟩ else g
  | GateOp.mod _ => g
  | GateOp.maj => g

def fixC : Bool → Gate → Gate
  | true, g => fixT g
  | false, g => fixF g

lemma all_filt (l : List ℕ) (f f' : ℕ → Bool) (h9 : f 9 = true)
    (hk : ∀ k, k ≠ 9 → f' k = f k) :
    ((l.filter (fun k => k != 9)).map f').all id = (l.map f).all id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = 9
    · subst ha
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.all_cons, id_eq, h9, Bool.true_and]
      exact ih
    · have hb : (a != 9) = true := by simpa using ha
      simp only [List.filter_cons, hb, ↓reduceIte, List.map_cons, List.all_cons, id_eq, hk a ha]
      rw [ih]

lemma any_filt (l : List ℕ) (f f' : ℕ → Bool) (h9 : f 9 = false)
    (hk : ∀ k, k ≠ 9 → f' k = f k) :
    ((l.filter (fun k => k != 9)).map f').any id = (l.map f).any id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = 9
    · subst ha
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.any_cons, id_eq, h9, Bool.false_or]
      exact ih
    · have hb : (a != 9) = true := by simpa using ha
      simp only [List.filter_cons, hb, ↓reduceIte, List.map_cons, List.any_cons, id_eq, hk a ha]
      rw [ih]

lemma valT (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (f f' : ℕ → Bool) (h9 : f 9 = true) (hk : ∀ k, k ≠ 9 → f' k = f k) :
    (fixT g).op.eval ((fixT g).inputs.map f') = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · exact all_filt l f f' h9 hk
  · dsimp only [fixT]
    split_ifs with h
    · symm
      exact List.any_eq_true.mpr ⟨f 9, List.mem_map.mpr ⟨9, h, rfl⟩, h9⟩
    · show (l.map f').any id = (l.map f).any id
      congr 1
      apply List.map_congr_left
      intro k hk'
      exact hk k (fun e => h (e ▸ hk'))
  · dsimp only [fixT]
    split_ifs with h
    · cases l with
      | nil => simp at h
      | cons a t =>
        simp at h
        subst h
        show false = !(f 9)
        rw [h9]
        rfl
    · cases l with
      | nil => rfl
      | cons a t =>
        have ha : a ≠ 9 := fun e => h (by rw [e]; rfl)
        show (!(f' a)) = !(f a)
        rw [hk a ha]

lemma valF (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (f f' : ℕ → Bool) (h9 : f 9 = false) (hk : ∀ k, k ≠ 9 → f' k = f k) :
    (fixF g).op.eval ((fixF g).inputs.map f') = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · dsimp only [fixF]
    split_ifs with h
    · symm
      apply Bool.eq_false_iff.mpr
      intro h'
      have := List.all_eq_true.mp h' (f 9) (List.mem_map.mpr ⟨9, h, rfl⟩)
      simp [h9] at this
    · show (l.map f').all id = (l.map f).all id
      congr 1
      apply List.map_congr_left
      intro k hk'
      exact hk k (fun e => h (e ▸ hk'))
  · exact any_filt l f f' h9 hk
  · dsimp only [fixF]
    split_ifs with h
    · cases l with
      | nil => simp at h
      | cons a t =>
        simp at h
        subst h
        show true = !(f 9)
        rw [h9]
        rfl
    · cases l with
      | nil => rfl
      | cons a t =>
        have ha : a ≠ 9 := fun e => h (by rw [e]; rfl)
        show (!(f' a)) = !(f a)
        rw [hk a ha]

lemma fan_fix (c : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    (fixC c g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (fixC c g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases c <;> rcases hop with rfl | rfl | rfl <;> dsimp only [fixC, fixT, fixF] <;>
    (try split_ifs) <;>
    refine ⟨by simp, ?_⟩ <;>
    first
    | exact (List.length_filter_le _ _).trans hl
    | simpa using hl
    | simp

def InvC (c : Bool) (w' w : List Bool) : Prop :=
  w'.length = w.length ∧ 10 ≤ w.length ∧ w.getD 9 false = c ∧
    ∀ k, k ≠ 9 → w'.getD k false = w.getD k false

lemma stepC (c : Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (w' w : List Bool) (h : InvC c w' w) : InvC c (F w' (fixC c g)) (F w g) := by
  obtain ⟨hl, h10, h9, hk⟩ := h
  have hv : (fixC c g).op.eval ((fixC c g).inputs.map fun j => w'.getD j false) =
      g.op.eval (g.inputs.map fun j => w.getD j false) := by
    cases c
    · exact valF g hop _ _ h9 hk
    · exact valT g hop _ _ h9 hk
  refine ⟨by simp [F, hl], by simp [F]; omega, ?_, ?_⟩
  · unfold F
    rw [getD_snoc, if_pos (by omega)]
    exact h9
  · intro k hk9
    unfold F
    rw [getD_snoc, getD_snoc, hv, hl]
    split_ifs
    · exact hk k hk9
    · rfl
    · rfl

def Form (D : Circuit) : Prop :=
  (∃ r ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))], ∀ x : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD 9 false = !x r) ∨
    ∃ p ∈ RP, ∃ b : Bool, ∀ x : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD 9 false = if b = true then x p.1 && x p.2 else x p.1 || x p.2

lemma noconst (c : Bool) (h : ∀ x : Fin 9 → Bool, c = fP x) : False := by
  have h1 := h (fun _ => true)
  have h2 := h (fun _ => false)
  rw [fP_true] at h1
  rw [fP_false, h1] at h2
  exact Bool.noConfusion h2

lemma novar (i : Fin 9) (h : ∀ x : Fin 9 → Bool, x i = fP x) : False := by
  have := h (fun k => decide (k = i))
  rw [fP_single] at this
  simp at this

lemma andv (x : Fin 9 → Bool) :
    GateOp.and.eval ([0, 1].map fun j => (List.ofFn x).getD j false) = (x 0 && x 1) := by
  rw [List.map_cons, List.map_cons, List.map_nil, getD_ofFn, getD_ofFn,
    dif_pos (by norm_num), dif_pos (by norm_num)]
  show (x 0 && (x 1 && true)) = (x 0 && x 1)
  rw [Bool.and_true]

lemma fan_mem (gs : List Gate) (o : ℕ) (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩)
    (g : Gate) (hg : g ∈ gs) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
  hF g hg

lemma main (gs : List Gate) (o : ℕ) (hF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩)
    (hfx : ∀ x : Fin 9 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = fP x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ (⟨gs, o⟩ : Circuit).size ∧
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = fP x) ∧ Form D := by
  cases gs with
  | nil =>
    exfalso
    by_cases ho : o < 9
    · apply novar ⟨o, ho⟩
      intro x
      rw [← hfx x]
      show x ⟨o, ho⟩ = (List.ofFn x).getD o false
      rw [getD_ofFn, dif_pos ho]
    · apply noconst false
      intro x
      rw [← hfx x]
      show false = (List.ofFn x).getD o false
      rw [getD_ofFn, dif_neg ho]
  | cons g0 rest =>
    have hg0 := fan_mem _ _ hF g0 (List.mem_cons_self ..)
    have hrest : ∀ g ∈ rest,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => fan_mem _ _ hF g (List.mem_cons_of_mem _ hg)
    have hw9 : ∀ (gs' : List Gate) (g : Gate) (x : Fin 9 → Bool),
        (gs'.foldl F (F (List.ofFn x) g)).getD 9 false = v0 g x := by
      intro gs' g x
      rw [fold_pre _ _ _ (by simp [F])]
      unfold F
      rw [getD_snoc, if_neg (by simp), if_pos (by simp)]
      rfl
    have hev : ∀ x : Fin 9 → Bool, Circuit.eval ⟨g0 :: rest, o⟩ (List.ofFn x) =
        (rest.foldl F (F (List.ofFn x) g0)).getD o false := fun x => rfl
    have hsnd : ∀ (x : Fin 9 → Bool) (k : ℕ), k ≠ 9 →
        (F (List.ofFn x) ⟨GateOp.and, [0, 1]⟩).getD k false = (F (List.ofFn x) g0).getD k false := by
      intro x k hk9
      unfold F
      rw [getD_snoc, getD_snoc]
      split_ifs with h1 h2
      · rfl
      · simp at h2
        exact absurd h2 hk9
      · rfl
    have hw9n : ∀ (gs' : List Gate) (x : Fin 9 → Bool),
        (gs'.foldl F (F (List.ofFn x) ⟨GateOp.and, [0, 1]⟩)).getD 9 false = (x 0 && x 1) := by
      intro gs' x
      rw [fold_pre _ _ _ (by simp [F])]
      unfold F
      rw [getD_snoc, if_neg (by simp), if_pos (by simp)]
      exact andv x
    have hfan_new : ∀ (G : Gate → Gate),
        (∀ g ∈ rest, (G g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          (G g).inputs.length ≤ 2) →
        PEqualNP.MetaComplexity.FanInTwo ⟨⟨GateOp.and, [0, 1]⟩ :: rest.map G, o⟩ := by
      intro G hG g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hG g' hg'
    have hform_new : ∀ (G : Gate → Gate), Form ⟨⟨GateOp.and, [0, 1]⟩ :: rest.map G, o⟩ := by
      intro G
      right
      refine ⟨((0 : Fin 9), (1 : Fin 9)), by simp [RP], true, fun x => ?_⟩
      exact hw9n _ x
    rcases classify g0 hg0.1 hg0.2 with ⟨c, hc⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, b, hb⟩
    · have ho : o ≠ 9 := by
        rintro rfl
        apply noconst c
        intro x
        rw [← hfx x, hev, hw9, hc]
      refine ⟨⟨⟨GateOp.and, [0, 1]⟩ :: rest.map (fixC c), o⟩,
        hfan_new _ (fun g hg => fan_fix c g (hrest g hg).1 (hrest g hg).2), ?_, ?_,
        hform_new _⟩
      · simp [Circuit.size]
      · intro x
        rw [← hfx x, hev]
        have h0 : InvC c (F (List.ofFn x) ⟨GateOp.and, [0, 1]⟩) (F (List.ofFn x) g0) := by
          refine ⟨by simp [F], by simp [F], ?_, fun k hk9 => hsnd x k hk9⟩
          have := hw9 [] g0 x
          rw [hc] at this
          exact this
        exact (fold_sim (InvC c) (fixC c) rest _ _ h0
          (fun g hg w' w h => stepC c g (hrest g hg).1 w' w h)).2.2.2 o ho
    · have ho : o ≠ 9 := by
        rintro rfl
        apply novar i
        intro x
        rw [← hfx x, hev, hw9, hi]
      refine ⟨⟨⟨GateOp.and, [0, 1]⟩ :: rest.map (rs i.val), o⟩,
        hfan_new _ (fun g hg => ⟨(hrest g hg).1, by simpa [rs] using (hrest g hg).2⟩), ?_, ?_,
        hform_new _⟩
      · simp [Circuit.size]
      · intro x
        rw [← hfx x, hev]
        have h0 : InvS i.val (F (List.ofFn x) ⟨GateOp.and, [0, 1]⟩) (F (List.ofFn x) g0) := by
          refine ⟨by simp [F], by simp [F], ?_, fun k hk9 => hsnd x k hk9⟩
          have := hw9 [] g0 x
          rw [hi] at this
          change (F (List.ofFn x) g0).getD 9 false = x i at this
          rw [this]
          unfold F
          rw [getD_snoc, if_pos (by simp), getD_ofFn, dif_pos i.isLt]
        exact (fold_sim (InvS i.val) (rs i.val) rest _ _ h0
          (fun g _ w' w h => stepS i.val i.isLt g w' w h)).2.2.2 o ho
    · obtain ⟨a, ha⟩ := cov1 i
      refine ⟨⟨(g0 :: rest).map (rl (AUT a)), piT (AUT a) o⟩, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact ⟨(fan_mem _ _ hF g' hg').1, by simpa [rl] using (fan_mem _ _ hF g' hg').2⟩
      · simp [Circuit.size]
      · intro x
        show (((g0 :: rest).map (rl (AUT a))).foldl F (List.ofFn x)).getD
          (piT (AUT a) o) false = _
        rw [permw]
        exact (hfx (x ∘ AUT a)).trans (aut a x)
      · left
        refine ⟨AUT a i, by rcases ha with h | h <;> simp [h], fun x => ?_⟩
        have h := permw (g0 :: rest) (AUT a) x 9
        rw [show piT (AUT a) 9 = 9 by simp [piT]] at h
        show (((g0 :: rest).map (rl (AUT a))).foldl F (List.ofFn x)).getD 9 false = _
        rw [h, List.foldl_cons, hw9, hi]
        rfl
    · obtain ⟨a, ha⟩ := cov2 i j hij
      refine ⟨⟨(g0 :: rest).map (rl (AUT a)), piT (AUT a) o⟩, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact ⟨(fan_mem _ _ hF g' hg').1, by simpa [rl] using (fan_mem _ _ hF g' hg').2⟩
      · simp [Circuit.size]
      · intro x
        show (((g0 :: rest).map (rl (AUT a))).foldl F (List.ofFn x)).getD
          (piT (AUT a) o) false = _
        rw [permw]
        exact (hfx (x ∘ AUT a)).trans (aut a x)
      · right
        have hw : ∀ x : Fin 9 → Bool,
            (Circuit.wires ⟨(g0 :: rest).map (rl (AUT a)), piT (AUT a) o⟩ (List.ofFn x)).getD 9
              false = if b = true then x (AUT a i) && x (AUT a j) else x (AUT a i) || x (AUT a j) := by
          intro x
          have h := permw (g0 :: rest) (AUT a) x 9
          rw [show piT (AUT a) 9 = 9 by simp [piT]] at h
          show (((g0 :: rest).map (rl (AUT a))).foldl F (List.ofFn x)).getD 9 false = _
          rw [h, List.foldl_cons, hw9, hb]
          rfl
        rcases ha with h | h
        · exact ⟨(AUT a i, AUT a j), h, b, hw⟩
        · refine ⟨(AUT a j, AUT a i), h, b, fun x => ?_⟩
          rw [hw x]
          cases b
          · exact Bool.or_comm _ _
          · exact Bool.and_comm _ _

end PEqualNP.Outside.L_meta_670_aux.Cases

theorem PEqualNP.Outside.L_meta_670_aux.Cases : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size ≤ x1.size ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧ ((∃ x5 ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))], ∀ (x6 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = !x6 x5) ∨ ∃ x5 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∃ (x6 : Bool), ∀ (x7 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = if x6 = Bool.true then x7 x5.1 && x7 x5.2 else x7 x5.1 || x7 x5.2) := by
  intro C hF hf
  obtain ⟨gs, o⟩ := C
  have hfx : ∀ x : Fin 9 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      PEqualNP.Outside.L_meta_670_aux.Cases.fP x := fun x => congrFun hf x
  obtain ⟨D, hFD, hs, hD, hform⟩ := PEqualNP.Outside.L_meta_670_aux.Cases.main gs o hF hfx
  exact ⟨D, hFD, hs, funext fun x => (hD x).trans (hfx x).symm, hform⟩
