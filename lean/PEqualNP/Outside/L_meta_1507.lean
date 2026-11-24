import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1507_aux

def mkInput (l : List (Fin 10)) (i : Fin 10) : Bool :=
  l.contains i

def edges : List (Fin 10 → Bool) :=
  [ mkInput [0, 1], mkInput [1, 2], mkInput [2, 3], mkInput [3, 4], mkInput [4, 0],
    mkInput [0, 5], mkInput [1, 6], mkInput [2, 7], mkInput [3, 8], mkInput [4, 9],
    mkInput [5, 7], mkInput [7, 9], mkInput [9, 6], mkInput [6, 8], mkInput [8, 5] ]

def ind4 : List (Fin 10 → Bool) :=
  [ mkInput [0, 2, 8, 9], mkInput [1, 3, 9, 5], mkInput [2, 4, 5, 6],
    mkInput [3, 0, 6, 7], mkInput [4, 1, 7, 8] ]

def eCnt (f : (Fin 10 → Bool) → Bool) : ℕ :=
  edges.countP (fun x => f x)

def bCnt (f : (Fin 10 → Bool) → Bool) : ℕ :=
  ind4.countP (fun x => !f x)

def boundM : ℕ → ℕ → ℕ
  | 0, b => if b ≤ 3 then 3 else 0
  | 1, b => if b ≤ 2 then 6 else if b = 3 then 3 else 1
  | 2, b => if b ≤ 2 then 12 else if b ≤ 4 then 6 else 3
  | 3, b => if b ≤ 2 then 15 else if b ≤ 4 then 12 else 6
  | _, b => if b ≤ 4 then 15 else 12

def family : ℕ → Set ((Fin 10 → Bool) → Bool)
  | 0 => { f | ∃ i : Fin 10, f = fun x => x i }
  | 1 => { f | eCnt f ≤ boundM 1 (bCnt f) }
  | 2 => { f | eCnt f ≤ boundM 2 (bCnt f) }
  | 3 => { f | eCnt f ≤ boundM 3 (bCnt f) }
  | 4 => { f | eCnt f ≤ boundM 4 (bCnt f) }
  | _ => Set.univ

lemma countP_and_le_left {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x && q x) ≤ l.countP p := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

lemma countP_and_le_right {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x && q x) ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

lemma countP_or_le_add {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x || q x) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

lemma eCnt_le_15 (f : (Fin 10 → Bool) → Bool) : eCnt f ≤ 15 := by
  simpa [eCnt, edges] using List.countP_le_length (l := edges) (p := fun x => f x)

lemma eCnt_and_le_left (f g : (Fin 10 → Bool) → Bool) :
    eCnt (fun y => f y && g y) ≤ eCnt f :=
  countP_and_le_left edges f g

lemma eCnt_and_le_right (f g : (Fin 10 → Bool) → Bool) :
    eCnt (fun y => f y && g y) ≤ eCnt g :=
  countP_and_le_right edges f g

lemma eCnt_or_le_add (f g : (Fin 10 → Bool) → Bool) :
    eCnt (fun y => f y || g y) ≤ eCnt f + eCnt g :=
  countP_or_le_add edges f g

lemma bCnt_and_le_add (f g : (Fin 10 → Bool) → Bool) :
    bCnt (fun y => f y && g y) ≤ bCnt f + bCnt g := by
  unfold bCnt
  have h : (fun x => !(f x && g x)) = (fun x => !f x || !g x) := by
    funext x
    exact Bool.not_and (f x) (g x)
  rw [h]
  exact countP_or_le_add ind4 (fun x => !f x) (fun x => !g x)

lemma bCnt_or_le_left (f g : (Fin 10 → Bool) → Bool) :
    bCnt (fun y => f y || g y) ≤ bCnt f := by
  unfold bCnt
  have h : (fun x => !(f x || g x)) = (fun x => !f x && !g x) := by
    funext x
    exact Bool.not_or (f x) (g x)
  rw [h]
  exact countP_and_le_left ind4 (fun x => !f x) (fun x => !g x)

lemma bCnt_or_le_right (f g : (Fin 10 → Bool) → Bool) :
    bCnt (fun y => f y || g y) ≤ bCnt g := by
  unfold bCnt
  have h : (fun x => !(f x || g x)) = (fun x => !f x && !g x) := by
    funext x
    exact Bool.not_or (f x) (g x)
  rw [h]
  exact countP_and_le_right ind4 (fun x => !f x) (fun x => !g x)

lemma base_mono (i : Fin 10) : eCnt (fun x => x i) ≤ boundM 1 (bCnt (fun x => x i)) := by
  fin_cases i <;> decide

lemma base_and (i j : Fin 10) :
    eCnt (fun y => y i && y j) ≤ boundM 1 (bCnt (fun y => y i && y j)) := by
  fin_cases i <;> fin_cases j <;> decide

lemma base_or (i j : Fin 10) :
    eCnt (fun y => y i || y j) ≤ boundM 1 (bCnt (fun y => y i || y j)) := by
  fin_cases i <;> fin_cases j <;> decide

lemma step_mono (k : ℕ) (f : (Fin 10 → Bool) → Bool) (hf : f ∈ family k) :
    f ∈ family (k + 1) := by
  match k with
  | 0 =>
    rcases hf with ⟨i, rfl⟩
    exact base_mono i
  | 1 =>
    change eCnt f ≤ boundM 1 (bCnt f) at hf
    change eCnt f ≤ boundM 2 (bCnt f)
    simp only [boundM] at hf ⊢
    split_ifs at hf ⊢ <;> omega
  | 2 =>
    change eCnt f ≤ boundM 2 (bCnt f) at hf
    change eCnt f ≤ boundM 3 (bCnt f)
    simp only [boundM] at hf ⊢
    split_ifs at hf ⊢ <;> omega
  | 3 =>
    change eCnt f ≤ boundM 3 (bCnt f) at hf
    change eCnt f ≤ boundM 4 (bCnt f)
    simp only [boundM] at hf ⊢
    split_ifs at hf ⊢ <;> omega
  | k + 4 =>
    exact trivial

lemma step_comb (k : ℕ) (f g : (Fin 10 → Bool) → Bool)
    (hf : f ∈ family k) (hg : g ∈ family k) :
    (fun y => f y && g y) ∈ family (k + 1) ∧ (fun y => f y || g y) ∈ family (k + 1) := by
  match k with
  | 0 =>
    rcases hf with ⟨i, rfl⟩
    rcases hg with ⟨j, rfl⟩
    exact ⟨base_and i j, base_or i j⟩
  | 1 =>
    change eCnt f ≤ boundM 1 (bCnt f) at hf
    change eCnt g ≤ boundM 1 (bCnt g) at hg
    have hal := eCnt_and_le_left f g
    have har := eCnt_and_le_right f g
    have hba := bCnt_and_le_add f g
    have hoa := eCnt_or_le_add f g
    have hbl := bCnt_or_le_left f g
    have hbr := bCnt_or_le_right f g
    have he1 := eCnt_le_15 (fun y => f y && g y)
    have he2 := eCnt_le_15 (fun y => f y || g y)
    constructor
    · change eCnt (fun y => f y && g y) ≤ boundM 2 (bCnt (fun y => f y && g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
    · change eCnt (fun y => f y || g y) ≤ boundM 2 (bCnt (fun y => f y || g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
  | 2 =>
    change eCnt f ≤ boundM 2 (bCnt f) at hf
    change eCnt g ≤ boundM 2 (bCnt g) at hg
    have hal := eCnt_and_le_left f g
    have har := eCnt_and_le_right f g
    have hba := bCnt_and_le_add f g
    have hoa := eCnt_or_le_add f g
    have hbl := bCnt_or_le_left f g
    have hbr := bCnt_or_le_right f g
    have he1 := eCnt_le_15 (fun y => f y && g y)
    have he2 := eCnt_le_15 (fun y => f y || g y)
    constructor
    · change eCnt (fun y => f y && g y) ≤ boundM 3 (bCnt (fun y => f y && g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
    · change eCnt (fun y => f y || g y) ≤ boundM 3 (bCnt (fun y => f y || g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
  | 3 =>
    change eCnt f ≤ boundM 3 (bCnt f) at hf
    change eCnt g ≤ boundM 3 (bCnt g) at hg
    have hal := eCnt_and_le_left f g
    have har := eCnt_and_le_right f g
    have hba := bCnt_and_le_add f g
    have hoa := eCnt_or_le_add f g
    have hbl := bCnt_or_le_left f g
    have hbr := bCnt_or_le_right f g
    have he1 := eCnt_le_15 (fun y => f y && g y)
    have he2 := eCnt_le_15 (fun y => f y || g y)
    constructor
    · change eCnt (fun y => f y && g y) ≤ boundM 4 (bCnt (fun y => f y && g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
    · change eCnt (fun y => f y || g y) ≤ boundM 4 (bCnt (fun y => f y || g y))
      simp only [boundM] at hf hg ⊢
      split_ifs at hf hg ⊢ <;> omega
  | k + 4 =>
    exact ⟨trivial, trivial⟩

def petersen (z : Fin 10 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0) ||
  (z 0 && z 5) || (z 1 && z 6) || (z 2 && z 7) || (z 3 && z 8) || (z 4 && z 9) ||
  (z 5 && z 7) || (z 7 && z 9) || (z 9 && z 6) || (z 6 && z 8) || (z 8 && z 5)

lemma petersen_eCnt : eCnt petersen = 15 := by decide

lemma petersen_bCnt : bCnt petersen = 5 := by decide

lemma petersen_not_mem_4 : petersen ∉ family 4 := by
  intro h
  change eCnt petersen ≤ boundM 4 (bCnt petersen) at h
  rw [petersen_eCnt, petersen_bCnt] at h
  simp [boundM] at h

end PEqualNP.Outside.L_meta_1507_aux

theorem PEqualNP.Outside.L_meta_1507 : ¬ (∀ T : ℕ → Set ((Fin 10 → Bool) → Bool), (∀ i : Fin 10, (fun x : Fin 10 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 10 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 10 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 10 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 10 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 10 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0) || (z 0 && z 5) || (z 1 && z 6) || (z 2 && z 7) || (z 3 && z 8) || (z 4 && z 9) || (z 5 && z 7) || (z 7 && z 9) || (z 9 && z 6) || (z 6 && z 8) || (z 8 && z 5)) ∈ T 4) := by
  intro h
  have h4 := h PEqualNP.Outside.L_meta_1507_aux.family
    (fun i => ⟨i, rfl⟩)
    PEqualNP.Outside.L_meta_1507_aux.step_mono
    PEqualNP.Outside.L_meta_1507_aux.step_comb
  exact PEqualNP.Outside.L_meta_1507_aux.petersen_not_mem_4 h4
