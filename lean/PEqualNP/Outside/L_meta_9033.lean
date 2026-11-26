import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_9033_aux

def readerOp (op x y : Bool) : Bool := if op then x && y else x || y

theorem agreement_away_from_cut
    {n m : Nat} (a b : Fin m → Nat) (op : Fin m → Bool)
    (f g : Nat → Bool) (bad : Nat → Prop)
    (ha : ∀ i, a i < n + i.val) (hb : ∀ i, b i < n + i.val)
    (hf : ∀ i, f (n + i.val) = readerOp (op i) (f (a i)) (f (b i)))
    (hg : ∀ i, g (n + i.val) = readerOp (op i) (g (a i)) (g (b i)))
    (hbase : ∀ w, w < n → ¬ bad w → f w = g w)
    (hstep : ∀ i, ¬ bad (n + i.val) →
      f (n + i.val) = g (n + i.val) ∨ (¬ bad (a i) ∧ ¬ bad (b i))) :
    ∀ w, w < n + m → ¬ bad w → f w = g w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hn
    by_cases hraw : w < n
    · exact hbase w hraw hn
    · let i : Fin m := ⟨w - n, by omega⟩
      have hi : n + i.val = w := by dsimp [i]; omega
      rcases hstep i (by simpa only [hi] using hn) with he | ⟨hla, hlb⟩
      · simpa only [hi] using he
      · have hla_lt : a i < w := by simpa only [hi] using ha i
        have hlb_lt : b i < w := by simpa only [hi] using hb i
        have hea := ih (a i) hla_lt (by omega) hla
        have heb := ih (b i) hlb_lt (by omega) hlb
        rw [← hi, hf i, hg i, hea, heb]

theorem two_raw_merged_reader_agreement
    {n m : Nat} (a b : Fin m → Nat) (op : Fin m → Bool)
    (f g : Nat → Bool) (v w : Nat) (p q : Fin m)
    (ha : ∀ i, a i < n + i.val) (hb : ∀ i, b i < n + i.val)
    (hf : ∀ i, f (n + i.val) = readerOp (op i) (f (a i)) (f (b i)))
    (hg : ∀ i, g (n + i.val) = readerOp (op i) (g (a i)) (g (b i)))
    (hbase : ∀ u, u < n → u ≠ v → u ≠ w → f u = g u)
    (hv : ∀ i, a i = v ∨ b i = v → i = p)
    (hw : ∀ i, a i = w ∨ b i = w → i = q)
    (hp : ∀ i, a i = n + p.val ∨ b i = n + p.val → i = q)
    (hq : f (n + q.val) = g (n + q.val)) :
    ∀ u, u < n + m → u ≠ v → u ≠ w → u ≠ n + p.val → f u = g u := by
  let bad : Nat → Prop := fun u => u = v ∨ u = w ∨ u = n + p.val
  have base : ∀ u, u < n → ¬ bad u → f u = g u := by
    intro u hu hn
    exact hbase u hu (fun h => hn (Or.inl h)) (fun h => hn (Or.inr (Or.inl h)))
  have step : ∀ i, ¬ bad (n + i.val) →
      f (n + i.val) = g (n + i.val) ∨ (¬ bad (a i) ∧ ¬ bad (b i)) := by
    intro i hn
    by_cases hiq : i = q
    · exact Or.inl (by simpa only [hiq] using hq)
    · right
      have avoid (u : Nat) (hs : u = a i ∨ u = b i) : ¬ bad u := by
        intro hbad
        rcases hbad with hvu | hwu | hpu
        · have hip : i = p := hv i (by
            rcases hs with hs | hs
            · exact Or.inl (hs.symm.trans hvu)
            · exact Or.inr (hs.symm.trans hvu))
          exact hn (Or.inr (Or.inr (by simp only [hip])))
        · apply hiq
          apply hw i
          rcases hs with hs | hs
          · exact Or.inl (hs.symm.trans hwu)
          · exact Or.inr (hs.symm.trans hwu)
        · apply hiq
          apply hp i
          rcases hs with hs | hs
          · exact Or.inl (hs.symm.trans hpu)
          · exact Or.inr (hs.symm.trans hpu)
      exact ⟨avoid (a i) (Or.inl rfl), avoid (b i) (Or.inr rfl)⟩
  intro u hu huv huw hup
  apply agreement_away_from_cut a b op f g bad ha hb hf hg base step u hu
  intro hbad
  rcases hbad with h | h | h
  · exact huv h
  · exact huw h
  · exact hup h

theorem merged_reader_cannot_separate
    {n m : Nat} (a b : Fin m → Nat) (op : Fin m → Bool)
    (f g : Nat → Bool) (v w out : Nat) (p q : Fin m)
    (ha : ∀ i, a i < n + i.val) (hb : ∀ i, b i < n + i.val)
    (hf : ∀ i, f (n + i.val) = readerOp (op i) (f (a i)) (f (b i)))
    (hg : ∀ i, g (n + i.val) = readerOp (op i) (g (a i)) (g (b i)))
    (hbase : ∀ u, u < n → u ≠ v → u ≠ w → f u = g u)
    (hv : ∀ i, a i = v ∨ b i = v → i = p)
    (hw : ∀ i, a i = w ∨ b i = w → i = q)
    (hp : ∀ i, a i = n + p.val ∨ b i = n + p.val → i = q)
    (hoq : op q = false)
    (hqa : a q = w) (hqb : b q = n + p.val)
    (hfp : f (n + p.val) = true) (hgw : g w = true)
    (hout : out < n + m) (hov : out ≠ v) (how : out ≠ w)
    (hop : out ≠ n + p.val) : f out = g out := by
  have hq : f (n + q.val) = g (n + q.val) := by
    rw [hf q, hg q]
    simp only [readerOp, hoq, Bool.false_eq_true, ↓reduceIte, hqa, hqb,
      hfp, hgw, Bool.or_true, Bool.true_or]
  exact two_raw_merged_reader_agreement a b op f g v w p q ha hb hf hg
    hbase hv hw hp hq out hout hov how hop

def readerGraph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 3) || (x 1 && x 5) ||
  (x 2 && x 4) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 7) ||
  (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)

def readerABC (v : Fin 3) : Fin 8 := ⟨v.val, by omega⟩

theorem abc_separating_pair : ∀ v w : Fin 3, v ≠ w → ∃ z : Fin 8,
    readerGraph (fun u => decide (u = readerABC v ∨ u = z)) = true ∧
    readerGraph (fun u => decide (u = readerABC w ∨ u = z)) = false := by
  decide +kernel


lemma nonatom_values_le_or_wires {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (value : α → β) (orValue : γ → β)
    (required : Finset α) (orWires : Finset γ) (atoms : Finset β)
    (cover : ∀ i ∈ required, value i ∈ atoms ∨
      ∃ j ∈ orWires, orValue j = value i) :
    ((required.image value) \ atoms).card ≤ orWires.card := by
  have subset : (required.image value) \ atoms ⊆ orWires.image orValue := by
    intro x hx
    obtain ⟨himage, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp himage
    rcases cover i hi with hatom | ⟨j, hj, hji⟩
    · exact False.elim (hnot (hix ▸ hatom))
    · exact Finset.mem_image.mpr ⟨j, hj, hji.trans hix⟩
  exact (Finset.card_le_card subset).trans (Finset.card_image_le)

lemma causal_values_covered {n : Nat} {β : Type*} [DecidableEq β]
    (value : Fin n → β) (atoms : Finset β) (representatives : Finset (Fin n))
    (step : ∀ i, value i ∈ atoms ∨ i ∈ representatives ∨
      ∃ j, j.val < i.val ∧ value j = value i) :
    ∀ i, value i ∈ atoms ∨ ∃ j ∈ representatives, value j = value i := by
  have cover : ∀ m, ∀ i : Fin n, i.val = m →
      value i ∈ atoms ∨ ∃ j ∈ representatives, value j = value i := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro i hi
      rcases step i with hatom | hrep | ⟨j, hj, heq⟩
      · exact Or.inl hatom
      · exact Or.inr ⟨i, hrep, rfl⟩
      · rcases ih j.val (by omega) j rfl with hatom | ⟨k, hk, hki⟩
        · exact Or.inl (heq ▸ hatom)
        · exact Or.inr ⟨k, hk, hki.trans heq⟩
  intro i
  exact cover i.val i rfl

lemma causal_values_le_representatives {n : Nat} {β : Type*} [DecidableEq β]
    (value : Fin n → β) (atoms : Finset β)
    (required representatives : Finset (Fin n))
    (step : ∀ i, value i ∈ atoms ∨ i ∈ representatives ∨
      ∃ j, j.val < i.val ∧ value j = value i) :
    ((required.image value) \ atoms).card ≤ representatives.card := by
  apply nonatom_values_le_or_wires value value required representatives atoms
  intro i _
  exact causal_values_covered value atoms representatives step i

def readerMaximalIndependentMasks : List Nat :=
  [7, 13, 19, 25, 37, 70, 76, 146, 160, 194]

def avoidingNegativeCount (support : Nat) : Nat :=
  readerMaximalIndependentMasks.countP (fun m => support &&& m == 0)

def singletonSupportSize (support : Nat) : Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128].countP (fun b => support &&& b != 0)

theorem two_avoiding_negatives_support_size : ∀ support : Fin 256,
    2 ≤ avoidingNegativeCount support.val → singletonSupportSize support.val ≤ 4 := by
  decide +kernel

theorem core_two_avoiding_negatives_exclusions : ∀ support : Fin 256,
    support.val &&& 7 = 0 → 2 ≤ avoidingNegativeCount support.val →
    support.val ≠ 120 ∧ support.val ≠ 248 := by
  decide +kernel

namespace BcofactorClassification

def coreUnion (s g : Nat) : Nat :=
  (if s.testBit 0 then 2863311530 else 0) |||
  (if s.testBit 1 then 3435973836 else 0) |||
  (if s.testBit 2 then 4042322160 else 0) |||
  (if s.testBit 3 then 4278255360 else 0) |||
  (if s.testBit 4 then 4294901760 else 0) |||
  (if s.testBit 5 then g else 0)

def singletonMask (value : Nat) : Nat :=
  (if value.testBit 1 then 1 else 0) |||
  (if value.testBit 2 then 2 else 0) |||
  (if value.testBit 4 then 4 else 0) |||
  (if value.testBit 8 then 8 else 0) |||
  (if value.testBit 16 then 16 else 0)

def upperTarget : Nat := 4277862138
def coreTarget : Nat := 4276813024
def exceptionalF : Nat := 4243651824

def sevenShapes : List Nat :=
  [4004179626, 4008373994, 4243651824, 4244176120,
    4272619178, 4277206768, 4277862138]

def rawAnd (p q : Nat) : Nat := coreUnion p 0 &&& coreUnion q 0

theorem raw_and_seven_shapes : ∀ p q : Fin 32,
    rawAnd p.val q.val &&& upperTarget = rawAnd p.val q.val →
    (rawAnd p.val q.val).testBit 10 = true →
    singletonMask (rawAnd p.val q.val) ≠ 0 →
    rawAnd p.val q.val ∈ sevenShapes := by
  decide +kernel

def HClassification (g : Nat) : Prop := ∀ p q : Fin 64,
  let l := coreUnion p.val g
  let r := coreUnion q.val g
  (l &&& r) &&& upperTarget = coreTarget →
  singletonMask (l &&& r) = 0 →
  g = exceptionalF ∧
    ((singletonMask l = 11 ∧ singletonMask r = 20) ∨
      (singletonMask l = 20 ∧ singletonMask r = 11))

theorem h_classification_0 : HClassification 4004179626 := by
  unfold HClassification
  decide +kernel
theorem h_classification_1 : HClassification 4008373994 := by
  unfold HClassification
  decide +kernel
theorem h_classification_2 : HClassification 4243651824 := by
  unfold HClassification
  decide +kernel
theorem h_classification_3 : HClassification 4244176120 := by
  unfold HClassification
  decide +kernel
theorem h_classification_4 : HClassification 4272619178 := by
  unfold HClassification
  decide +kernel
theorem h_classification_5 : HClassification 4277206768 := by
  unfold HClassification
  decide +kernel
theorem h_classification_6 : HClassification 4277862138 := by
  unfold HClassification
  decide +kernel

theorem h_classification (g : Nat) (hg : g ∈ sevenShapes) : HClassification g := by
  simp [sevenShapes] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_classification_0
  · exact h_classification_1
  · exact h_classification_2
  · exact h_classification_3
  · exact h_classification_4
  · exact h_classification_5
  · exact h_classification_6

theorem exceptionalF_raw_ports : ∀ p q : Fin 32,
    rawAnd p.val q.val = exceptionalF →
    (p.val = 6 ∧ q.val = 12) ∨ (p.val = 12 ∧ q.val = 6) := by
  decide +kernel

theorem seven_required_nonatom_masks :
    ({5, 6, 11, 12, 18, 20, 24} : Finset Nat).card = 7 ∧
    Disjoint ({5, 6, 11, 12, 18, 20, 24} : Finset Nat)
      ({0, 1, 2, 4, 8, 16, 32} : Finset Nat) := by
  decide +kernel

theorem no_six_mask_budget (p q : Fin 32) (u w : Fin 64)
    (hbelow : rawAnd p.val q.val &&& upperTarget = rawAnd p.val q.val)
    (hedge : (rawAnd p.val q.val).testBit 10 = true)
    (hnonzero : singletonMask (rawAnd p.val q.val) ≠ 0)
    (htarget : (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) &&& upperTarget = coreTarget)
    (hzero : singletonMask (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) = 0)
    (hbudget : (({p.val, q.val, singletonMask (coreUnion u.val (rawAnd p.val q.val)),
        singletonMask (coreUnion w.val (rawAnd p.val q.val)), 5, 18, 24} : Finset Nat) \
      {0, 1, 2, 4, 8, 16, 32, singletonMask (rawAnd p.val q.val)}).card ≤ 6) : False := by
  have hgmem := raw_and_seven_shapes p q hbelow hedge hnonzero
  obtain ⟨hg, hports⟩ := h_classification (rawAnd p.val q.val) hgmem u w htarget hzero
  have hraw := exceptionalF_raw_ports p q hg
  have hsing : singletonMask (rawAnd p.val q.val) = 4 := by
    rw [hg]
    decide +kernel
  rcases hraw with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    rcases hports with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    rw [hl, hr, hsing, hp, hq] at hbudget <;>
    exact absurd hbudget (by decide +kernel)

theorem no_six_shared_reader_mask_budget (p q : Fin 32) (u w : Fin 64)
    (hbelow : rawAnd p.val q.val &&& upperTarget = rawAnd p.val q.val)
    (hedge : (rawAnd p.val q.val).testBit 10 = true)
    (hnonzero : singletonMask (rawAnd p.val q.val) ≠ 0)
    (htarget : (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) &&& upperTarget = coreTarget)
    (hzero : singletonMask (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) = 0)
    (hbudget : (({p.val, q.val, singletonMask (coreUnion u.val (rawAnd p.val q.val)),
        singletonMask (coreUnion w.val (rawAnd p.val q.val)), 5, 22, 28} : Finset Nat) \
      {0, 1, 2, 4, 8, 16, 32, singletonMask (rawAnd p.val q.val)}).card ≤ 6) : False := by
  have hgmem := raw_and_seven_shapes p q hbelow hedge hnonzero
  obtain ⟨hg, hports⟩ := h_classification (rawAnd p.val q.val) hgmem u w htarget hzero
  have hraw := exceptionalF_raw_ports p q hg
  have hsing : singletonMask (rawAnd p.val q.val) = 4 := by
    rw [hg]
    decide +kernel
  rcases hraw with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;>
    rcases hports with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    rw [hl, hr, hsing, hp, hq] at hbudget <;>
    exact absurd hbudget (by decide +kernel)

end BcofactorClassification

namespace ACcofactorClassification

def coreUnion (s g : Nat) : Nat :=
  (if s.testBit 0 then 2863311530 else 0) |||
  (if s.testBit 1 then 3435973836 else 0) |||
  (if s.testBit 2 then 4042322160 else 0) |||
  (if s.testBit 3 then 4278255360 else 0) |||
  (if s.testBit 4 then 4294901760 else 0) |||
  (if s.testBit 5 then g else 0)

def singletonMask (value : Nat) : Nat :=
  (if value.testBit 1 then 1 else 0) |||
  (if value.testBit 2 then 2 else 0) |||
  (if value.testBit 4 then 4 else 0) |||
  (if value.testBit 8 then 8 else 0) |||
  (if value.testBit 16 then 16 else 0)

def coreTarget : Nat := 4276813024

def rawAnd (p q : Nat) : Nat := coreUnion p 0 &&& coreUnion q 0

def HImpossible (upper g : Nat) : Prop := ∀ p q : Fin 64,
  let l := coreUnion p.val g
  let r := coreUnion q.val g
  (l &&& r) &&& upper = coreTarget →
  singletonMask (l &&& r) = 0 → False

def upperA : Nat := 4294967264

def shapesA : List Nat :=
  [4292935648, 4293853152, 4293984224, 4294959328, 4294962912, 4294963424, 4294967264]

theorem raw_and_shapes_A : ∀ p q : Fin 32,
    rawAnd p.val q.val &&& upperA = rawAnd p.val q.val →
    (rawAnd p.val q.val).testBit 5 = true →
    (rawAnd p.val q.val).testBit 6 = true →
    singletonMask (rawAnd p.val q.val) ≠ 0 →
    rawAnd p.val q.val ∈ shapesA := by
  decide +kernel

theorem h_impossible_A_0 : HImpossible upperA 4292935648 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_1 : HImpossible upperA 4293853152 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_2 : HImpossible upperA 4293984224 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_3 : HImpossible upperA 4294959328 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_4 : HImpossible upperA 4294962912 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_5 : HImpossible upperA 4294963424 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A_6 : HImpossible upperA 4294967264 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_A (g : Nat) (hg : g ∈ shapesA) :
    HImpossible upperA g := by
  simp [shapesA] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_impossible_A_0
  · exact h_impossible_A_1
  · exact h_impossible_A_2
  · exact h_impossible_A_3
  · exact h_impossible_A_4
  · exact h_impossible_A_5
  · exact h_impossible_A_6

theorem no_A_gfirst (p q : Fin 32) (u w : Fin 64)
    (hbelow : rawAnd p.val q.val &&& upperA = rawAnd p.val q.val)
    (hedge1 : (rawAnd p.val q.val).testBit 5 = true)
    (hedge2 : (rawAnd p.val q.val).testBit 6 = true)
    (hnonzero : singletonMask (rawAnd p.val q.val) ≠ 0)
    (htarget : (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) &&& upperA = coreTarget)
    (hzero : singletonMask (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) = 0) : False := by
  have hmem := raw_and_shapes_A p q hbelow hedge1 hedge2 hnonzero
  exact h_impossible_A (rawAnd p.val q.val) hmem u w htarget hzero

def upperC : Nat := 4294966508

def shapesC : List Nat :=
  [4243389676, 4244438252, 4293852396, 4294963360, 4294963424, 4294966440, 4294966508]

theorem raw_and_shapes_C : ∀ p q : Fin 32,
    rawAnd p.val q.val &&& upperC = rawAnd p.val q.val →
    (rawAnd p.val q.val).testBit 5 = true →
    (rawAnd p.val q.val).testBit 12 = true →
    singletonMask (rawAnd p.val q.val) ≠ 0 →
    rawAnd p.val q.val ∈ shapesC := by
  decide +kernel

theorem h_impossible_C_0 : HImpossible upperC 4243389676 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_1 : HImpossible upperC 4244438252 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_2 : HImpossible upperC 4293852396 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_3 : HImpossible upperC 4294963360 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_4 : HImpossible upperC 4294963424 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_5 : HImpossible upperC 4294966440 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C_6 : HImpossible upperC 4294966508 := by
  unfold HImpossible
  decide +kernel

theorem h_impossible_C (g : Nat) (hg : g ∈ shapesC) :
    HImpossible upperC g := by
  simp [shapesC] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_impossible_C_0
  · exact h_impossible_C_1
  · exact h_impossible_C_2
  · exact h_impossible_C_3
  · exact h_impossible_C_4
  · exact h_impossible_C_5
  · exact h_impossible_C_6

theorem no_C_gfirst (p q : Fin 32) (u w : Fin 64)
    (hbelow : rawAnd p.val q.val &&& upperC = rawAnd p.val q.val)
    (hedge1 : (rawAnd p.val q.val).testBit 5 = true)
    (hedge2 : (rawAnd p.val q.val).testBit 12 = true)
    (hnonzero : singletonMask (rawAnd p.val q.val) ≠ 0)
    (htarget : (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) &&& upperC = coreTarget)
    (hzero : singletonMask (coreUnion u.val (rawAnd p.val q.val) &&&
      coreUnion w.val (rawAnd p.val q.val)) = 0) : False := by
  have hmem := raw_and_shapes_C p q hbelow hedge1 hedge2 hnonzero
  exact h_impossible_C (rawAnd p.val q.val) hmem u w htarget hzero

end ACcofactorClassification

end PEqualNP.Outside.L_meta_9033_aux
