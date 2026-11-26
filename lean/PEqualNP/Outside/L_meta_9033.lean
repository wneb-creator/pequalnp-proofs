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


namespace PEqualNP.Outside.L_meta_9033_aux.HFirst

def raw (p x : Fin 32) : Bool := p.val &&& x.val != 0

def core (x : Fin 32) : Bool := (4276813024 : Nat).testBit x.val

def neighbors (v : Fin 3) : Fin 32 :=
  if v.val = 0 then 24 else if v.val = 1 then 5 else 18

def upper (v : Fin 3) (x : Fin 32) : Bool := raw (neighbors v) x || core x

def unit (i : Fin 5) : Fin 32 := ⟨2 ^ i.val, by
  have h : ∀ j : Fin 5, 2 ^ j.val < 32 := by decide +kernel
  exact h i⟩

def pair (i j : Fin 5) : Fin 32 := ⟨(unit i).val ||| (unit j).val, by
  have h : ∀ a b : Fin 5, (unit a).val ||| (unit b).val < 32 := by decide +kernel
  exact h i j⟩

theorem raw_zero : ∀ p : Fin 32, raw p 0 = false := by decide +kernel

theorem zero_raw : ∀ x : Fin 32, raw 0 x = false := by decide +kernel

theorem core_zero : core 0 = false := by decide +kernel

theorem raw_unit : ∀ (p : Fin 32) (i : Fin 5),
    raw p (unit i) = p.val.testBit i.val := by decide +kernel

theorem raw_pair : ∀ (p : Fin 32) (i j : Fin 5),
    raw p (pair i j) = (raw p (unit i) || raw p (unit j)) := by decide +kernel

theorem unit_raw : ∀ (i : Fin 5) (x : Fin 32),
    raw (unit i) x = x.val.testBit i.val := by decide +kernel

theorem unit_self : ∀ i : Fin 5, raw (unit i) (unit i) = true := by decide +kernel

theorem raw_singleton_force : ∀ (p x : Fin 32) (i : Fin 5),
    raw p (unit i) = true → raw (unit i) x = true → raw p x = true := by
  decide +kernel

theorem raw_singleton_inclusion : ∀ p q : Fin 32,
    (∀ i : Fin 5, raw p (unit i) = true → raw q (unit i) = true) →
    ∀ x : Fin 32, raw p x = true → raw q x = true := by decide +kernel

theorem core_unit : ∀ i : Fin 5, core (unit i) = false := by decide +kernel

theorem upper_zero : ∀ v : Fin 3, upper v 0 = false := by decide +kernel

theorem upper_unit : ∀ (v : Fin 3) (i : Fin 5),
    upper v (unit i) = raw (neighbors v) (unit i) := by decide +kernel

theorem core_le_upper : ∀ (v : Fin 3) (x : Fin 32),
    core x = true → upper v x = true := by decide +kernel

theorem raw_le_upper_neighbors (v : Fin 3) (p : Fin 32)
    (h : ∀ x : Fin 32, raw p x = true → upper v x = true) :
    ∀ x : Fin 32, raw p x = true → raw (neighbors v) x = true := by
  apply raw_singleton_inclusion p (neighbors v)
  intro i hi
  have hx := h (unit i) hi
  rw [upper_unit] at hx
  exact hx

theorem core_outside_neighbors : ∀ v : Fin 3, ∃ i j : Fin 5,
    i ≠ j ∧ core (pair i j) = true ∧ raw (neighbors v) (pair i j) = false := by
  decide +kernel

theorem raw_ne_upper : ∀ (v : Fin 3) (p : Fin 32),
    ¬ (∀ x : Fin 32, raw p x = upper v x) := by decide +kernel

theorem raw_or_not_upper : ∀ (v : Fin 3) (p q : Fin 32),
    ¬ (∀ x : Fin 32, (raw p x || raw q x) = upper v x) := by decide +kernel

theorem no_common_core_neighbor : ∀ (v : Fin 3) (z : Fin 5), ∃ n : Fin 5,
    raw (neighbors v) (unit n) = true ∧ core (pair z n) = false := by
  decide +kernel

theorem common_neighbor_counterexample : ∀ (v : Fin 3) (z : Fin 5), ∃ x : Fin 32,
    raw (unit z) x = true ∧ raw (neighbors v) x = true ∧ core x = false := by
  decide +kernel

theorem raw_extras_zero : ∀ (v : Fin 3) (p : Fin 32),
    (∀ x : Fin 32, (upper v x && raw p x) = true → core x = true) → p = 0 := by
  decide +kernel

theorem raw_addition_forbidden (v : Fin 3) (p : Fin 32)
    (h : ∀ x : Fin 32, (upper v x && raw p x) = true → core x = true) :
    ∀ x : Fin 32, raw p x = false := by
  have hp := raw_extras_zero v p h
  subst p
  exact zero_raw

theorem raw_and_no_triangle : ∀ p q : Fin 32,
    (∀ i : Fin 5, (raw p (unit i) && raw q (unit i)) = false) →
    ¬ ((raw p 6 && raw q 6) = true ∧
      (raw p 10 && raw q 10) = true ∧ (raw p 12 && raw q 12) = true) := by
  decide +kernel

theorem raw_and_not_cover_core : ∀ p q : Fin 32,
    (∀ i : Fin 5, (raw p (unit i) && raw q (unit i)) = false) →
    ¬ (∀ x : Fin 32, core x = true → (raw p x && raw q x) = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_9033_aux.HFirst

namespace PEqualNP.Outside.L_meta_9033_aux.HFirst

lemma and_true_parts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

def first (p q : Fin 32) (x : Fin 32) : Bool := raw p x && raw q x

def side (p : Fin 32) (takeH takeQ : Bool)
    (h : Fin 32 → Bool) (q : Bool) (x : Fin 32) : Bool :=
  raw p x || (takeH && h x) || (takeQ && q)

def secondZero (lp rp : Fin 32) (lh lq rh rq : Bool)
    (h : Fin 32 → Bool) (x : Fin 32) : Bool :=
  side lp lh lq h (h x) x && side rp rh rq h (h x) x

def secondOne (lp rp : Fin 32) (lh lq rh rq : Bool)
    (h : Fin 32 → Bool) (x : Fin 32) : Bool :=
  side lp lh lq h true x && side rp rh rq h true x

theorem canonical_hfirst_impossible
    (v : Fin 3) (hp hq lp rp xp yp : Fin 32) (lh lq rh rq : Bool)
    (hzero : ∀ i : Fin 5, first hp hq (unit i) = false)
    (hdirty : ∃ x : Fin 32, first hp hq x = true ∧ core x = false)
    (hat0 : ∀ x : Fin 32,
      ((secondZero lp rp lh lq rh rq (first hp hq) x || raw xp x) &&
        (first hp hq x || raw yp x)) = core x)
    (hat1 : ∀ x : Fin 32,
      (secondOne lp rp lh lq rh rq (first hp hq) x || raw xp x) = upper v x) : False := by
  cases lq <;> cases rq
  · have hleft : ∀ x : Fin 32,
        (secondZero lp rp lh false rh false (first hp hq) x || raw xp x) = upper v x := by
      intro x
      simpa [secondZero, secondOne, side] using hat1 x
    have hyfalse : ∀ x : Fin 32, raw yp x = false := by
      apply raw_addition_forbidden v yp
      intro x hx
      obtain ⟨hu, hy⟩ := and_true_parts hx
      have ht := hat0 x
      rw [hleft x, hu, hy] at ht
      simpa using ht.symm
    apply raw_and_not_cover_core hp hq hzero
    intro x hx
    have ht := hat0 x
    simp only [hyfalse x, Bool.or_false, hx] at ht
    exact (and_true_parts ht).2
  · cases lh
    · apply raw_or_not_upper v lp xp
      intro x
      simpa [secondOne, side] using hat1 x
    · obtain ⟨x, hx, hn⟩ := hdirty
      have ht := hat0 x
      simp [secondZero, side, hx, hn] at ht
  · cases rh
    · apply raw_or_not_upper v rp xp
      intro x
      simpa [secondOne, side] using hat1 x
    · obtain ⟨x, hx, hn⟩ := hdirty
      have ht := hat0 x
      simp [secondZero, side, hx, hn] at ht
  · have ht := hat1 0
    simp [secondOne, side, upper_zero] at ht

def finalSide (p : Fin 32) (takeH takeG takeQ : Bool)
    (h g q : Bool) (x : Fin 32) : Bool :=
  raw p x || (takeH && h) || (takeG && g) || (takeQ && q)

lemma second_v_dominance (lp rp : Fin 32) (lh lq rh rq : Bool)
    (h : Fin 32 → Bool) (hz : h 0 = false)
    (hv : secondOne lp rp lh lq rh rq h 0 = true) :
    (∀ x, secondOne lp rp lh lq rh rq h x = true) ∧
    (∀ x, h x = true → secondZero lp rp lh lq rh rq h x = true) := by
  have hq : (lq && rq) = true := by
    simpa [secondOne, side, raw_zero, hz] using hv
  obtain ⟨hl, hr⟩ := and_true_parts hq
  constructor
  · intro x
    simp [secondOne, side, hl, hr]
  · intro x hx
    simp [secondZero, side, hl, hr, hx]

lemma second_core_dominance (lp rp : Fin 32) (lh lq rh rq : Bool)
    (h : Fin 32 → Bool) (hz : ∀ i : Fin 5, h (unit i) = false)
    (i : Fin 5) (x : Fin 32)
    (hi : secondZero lp rp lh lq rh rq h (unit i) = true)
    (hx : raw (unit i) x = true) : secondZero lp rp lh lq rh rq h x = true := by
  have hr : (raw lp (unit i) && raw rp (unit i)) = true := by
    simpa [secondZero, side, hz i] using hi
  obtain ⟨hl, hr⟩ := and_true_parts hr
  have hlx := raw_singleton_force lp x i hl hx
  have hrx := raw_singleton_force rp x i hr hx
  simp [secondZero, side, hlx, hrx]

theorem oriented_final_ports (v : Fin 3) (xp yp : Fin 32)
    (lh lq rh rq : Bool) (h g0 g1 : Fin 32 → Bool)
    (hz : h 0 = false) (hs : ∀ i : Fin 5, h (unit i) = false)
    (hd : ∃ x, h x = true ∧ core x = false)
    (gs : (∃ i : Fin 5, g0 (unit i) = true) ∨ g1 0 = true)
    (gv : g1 0 = true → (∀ x, g1 x = true) ∧ (∀ x, h x = true → g0 x = true))
    (gc : ∀ (i : Fin 5) (x : Fin 32),
      g0 (unit i) = true → raw (unit i) x = true → g0 x = true)
    (out0 : ∀ x, (finalSide xp lh true lq (h x) (g0 x) (h x) x &&
      finalSide yp rh false rq (h x) (g0 x) (h x) x) = core x)
    (out1 : ∀ x, (finalSide xp lh true lq (h x) (g1 x) true x &&
      finalSide yp rh false rq (h x) (g1 x) true x) = upper v x) :
    (∀ x, ((g0 x || raw xp x) && (h x || raw yp x)) = core x) ∧
    (∀ x, (g1 x || raw xp x) = upper v x) := by
  have hgv : g1 0 = false := by
    cases hv : g1 0
    · rfl
    · exfalso
      obtain ⟨gall, gh⟩ := gv hv
      have hrq : rq = false := by
        have ht := out1 0
        simpa [finalSide, raw_zero, hz, hv, upper_zero] using ht
      cases rh
      · apply raw_ne_upper v yp
        intro x
        simpa [finalSide, gall x, hrq] using out1 x
      · obtain ⟨x, hx, hn⟩ := hd
        have ht := out0 x
        simp [finalSide, hx, gh x hx, hn, hrq] at ht
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, g0 (unit i) = true := by
    rcases gs with hcore | hv
    · exact hcore
    · simp [hgv] at hv
  have hrq : rq = true := by
    cases he : rq
    · exfalso
      have cover : ∀ j : Fin 5,
          raw (neighbors v) (unit j) = true → raw yp (unit j) = true := by
        intro j hj
        have hu : upper v (unit j) = true := (upper_unit v j).trans hj
        have ht := (and_true_parts ((out1 (unit j)).trans hu)).2
        simpa [finalSide, he, hs j] using ht
      have includeRaw := raw_singleton_inclusion (neighbors v) yp cover
      obtain ⟨x, hx, hnbr, hn⟩ := common_neighbor_counterexample v i
      have hgx := gc i x hi hx
      have hyp := includeRaw x hnbr
      have ht := out0 x
      simp [finalSide, hgx, hyp, hn] at ht
    · rfl
  have hlq : lq = false := by
    have ht := out1 0
    simpa [finalSide, raw_zero, hz, hgv, hrq, upper_zero] using ht
  have hlh : lh = false := by
    cases he : lh
    · rfl
    · exfalso
      obtain ⟨x, hx, hn⟩ := hd
      have ht := out0 x
      simp [finalSide, he, hrq, hx, hn] at ht
  constructor
  · intro x
    have ht := out0 x
    cases rh <;>
      simpa [finalSide, hlh, hlq, hrq, Bool.or_comm, Bool.or_assoc] using ht
  · intro x
    have ht := out1 x
    cases rh <;>
      simpa [finalSide, hlh, hlq, hrq, Bool.or_comm, Bool.or_assoc] using ht

lemma upper_has_singleton : ∀ v : Fin 3, ∃ i : Fin 5, upper v (unit i) = true := by
  decide +kernel

theorem no_g_final_ports (v : Fin 3) (xp yp : Fin 32)
    (lh lq rh rq : Bool) (h : Fin 32 → Bool)
    (hd : ∃ x, h x = true ∧ core x = false)
    (out0 : ∀ x, (side xp lh lq h (h x) x && side yp rh rq h (h x) x) = core x)
    (out1 : ∀ x, (side xp lh lq h true x && side yp rh rq h true x) = upper v x) : False := by
  cases lq <;> cases rq
  · obtain ⟨i, hi⟩ := upper_has_singleton v
    have he : core (unit i) = upper v (unit i) :=
      (out0 (unit i)).symm.trans (by simpa [side] using out1 (unit i))
    simp [core_unit, hi] at he
  · cases lh
    · apply raw_ne_upper v xp
      intro x
      simpa [side] using out1 x
    · obtain ⟨x, hx, hn⟩ := hd
      have ht := out0 x
      simp [side, hx, hn] at ht
  · cases rh
    · apply raw_ne_upper v yp
      intro x
      simpa [side] using out1 x
    · obtain ⟨x, hx, hn⟩ := hd
      have ht := out0 x
      simp [side, hx, hn] at ht
  · have ht := out1 0
    simp [side, upper_zero] at ht

theorem hfirst_model_impossible
    (v : Fin 3) (hp hq lp rp xp yp : Fin 32)
    (lh lq rh rq xh xg xq yh yg yq : Bool) :
    let h := first hp hq
    let g0 := secondZero lp rp lh lq rh rq h
    let g1 := secondOne lp rp lh lq rh rq h
    (∀ i : Fin 5, h (unit i) = false) →
    ((∃ x, h x = true ∧ core x = false) ∨
      (∃ x, h x = true ∧ upper v x = false)) →
    ((∃ i : Fin 5, g0 (unit i) = true) ∨ g1 0 = true) →
    ((∃ x, g0 x = true ∧ core x = false) ∨
      (∃ x, g1 x = true ∧ upper v x = false)) →
    (∀ x, (finalSide xp xh xg xq (h x) (g0 x) (h x) x &&
      finalSide yp yh yg yq (h x) (g0 x) (h x) x) = core x) →
    (∀ x, (finalSide xp xh xg xq (h x) (g1 x) true x &&
      finalSide yp yh yg yq (h x) (g1 x) true x) = upper v x) → False := by
  dsimp only
  intro hs hdirty gs gd out0 out1
  have hd : ∃ x, first hp hq x = true ∧ core x = false := by
    rcases hdirty with hd | ⟨x, hx, hn⟩
    · exact hd
    · refine ⟨x, hx, ?_⟩
      cases hc : core x
      · rfl
      · have hu := core_le_upper v x hc
        simp [hu] at hn
  have hz : first hp hq 0 = false := by simp [first, raw_zero]
  have gv := second_v_dominance lp rp lh lq rh rq (first hp hq) hz
  have gc := second_core_dominance lp rp lh lq rh rq (first hp hq) hs
  cases xg <;> cases yg
  · apply no_g_final_ports v xp yp xh xq yh yq (first hp hq) hd
    · intro x
      simpa [finalSide, side] using out0 x
    · intro x
      simpa [finalSide, side] using out1 x
  · have hr := oriented_final_ports v yp xp yh yq xh xq (first hp hq)
      (secondZero lp rp lh lq rh rq (first hp hq))
      (secondOne lp rp lh lq rh rq (first hp hq)) hz hs hd gs gv gc
      (fun x => by simpa only [Bool.and_comm] using out0 x)
      (fun x => by simpa only [Bool.and_comm] using out1 x)
    exact canonical_hfirst_impossible v hp hq lp rp yp xp lh lq rh rq hs hd hr.1 hr.2
  · have hr := oriented_final_ports v xp yp xh xq yh yq (first hp hq)
      (secondZero lp rp lh lq rh rq (first hp hq))
      (secondOne lp rp lh lq rh rq (first hp hq)) hz hs hd gs gv gc out0 out1
    exact canonical_hfirst_impossible v hp hq lp rp xp yp lh lq rh rq hs hd hr.1 hr.2
  · rcases gd with ⟨x, hx, hn⟩ | ⟨x, hx, hn⟩
    · have ht := out0 x
      simp [finalSide, hx, hn] at ht
    · have ht := out1 x
      simp [finalSide, hx, hn] at ht

end PEqualNP.Outside.L_meta_9033_aux.HFirst
namespace PEqualNP.Outside.L_meta_9033_aux.GFirst

open PEqualNP.Outside.L_meta_9033_aux.HFirst

def port (p : Fin 32) (useH useG useQ : Bool)
    (h g : Fin 32 → Bool) (b : Bool) (x : Fin 32) : Bool :=
  raw p x || (useH && h x) || (useG && g x) || (useQ && (b || h x))

def target (v : Fin 3) (b : Bool) (x : Fin 32) : Bool :=
  (b && raw (neighbors v) x) || core x

theorem neighbors_nonempty : ∀ v : Fin 3, ∃ i : Fin 5,
    raw (neighbors v) (unit i) = true := by
  decide +kernel

theorem canonical_qleft (v : Fin 3) (l r : Fin 32)
    (lh lg rh rg : Bool) (h g : Fin 32 → Bool)
    (hdirty : ∃ x, h x = true ∧ core x = false)
    (gnonzero : ∃ i : Fin 5, g (unit i) = true)
    (htarget : ∀ b x,
      (port l lh lg true h g b x && port r rh rg false h g b x) = target v b x) :
    l = 0 ∧ lg = false ∧ rh = false ∧ rg = true ∧
    (∀ x, (raw r x || g x) = upper v x) ∧
    (∀ b x, port l lh lg true h g b x = (b || h x)) := by
  have right_upper (b : Bool) (x : Fin 32) :
      port r rh rg false h g b x = upper v x := by
    have hx := htarget true x
    simpa [port, target, upper] using hx
  have hrh : rh = false := by
    cases heq : rh
    · rfl
    · obtain ⟨x, hx, hc⟩ := hdirty
      have bad := htarget false x
      simp [port, target, heq, hx, hc] at bad
  have hrg : rg = true := by
    cases heq : rg
    · exfalso
      apply raw_ne_upper v r
      intro x
      simpa [port, hrh, heq] using right_upper false x
    · rfl
  have hlg : lg = false := by
    cases heq : lg
    · rfl
    · obtain ⟨i, hi⟩ := gnonzero
      have bad := htarget false (unit i)
      simp [port, target, heq, hrg, hi, core_unit] at bad
  have hrawzero : l = 0 := by
    apply raw_extras_zero v l
    intro x hx
    have hu : upper v x = true := by
      cases heq : upper v x
      · simp [heq] at hx
      · rfl
    have hl : raw l x = true := by
      cases heq : raw l x
      · simp [heq] at hx
      · rfl
    have hp : port l lh lg true h g false x = true := by simp [port, hl]
    have hq : port r rh rg false h g false x = true := by
      rw [right_upper false x]
      exact hu
    have heq := htarget false x
    simpa [target, hp, hq] using heq.symm
  refine ⟨hrawzero, hlg, hrh, hrg, ?_, ?_⟩
  · intro x
    simpa [port, hrh, hrg] using right_upper false x
  · intro b x
    rw [hrawzero, hlg]
    cases lh <;> cases b <;> cases hh : h x <;> simp [port, zero_raw, hh]

def Canonical (v : Fin 3) (h g : Fin 32 → Bool)
    (left right : Bool → Fin 32 → Bool) : Prop :=
  ∃ y : Fin 32, (∀ x, (raw y x || g x) = upper v x) ∧
    (((∀ b x, left b x = (b || h x)) ∧
      (∀ b x, right b x = (raw y x || g x))) ∨
     ((∀ b x, right b x = (b || h x)) ∧
      (∀ b x, left b x = (raw y x || g x))))

theorem canonical_final_ports (v : Fin 3) (l r : Fin 32)
    (lh lg lq rh rg rq : Bool) (h g : Fin 32 → Bool)
    (hdirty : ∃ x, h x = true ∧ core x = false)
    (gnonzero : ∃ i : Fin 5, g (unit i) = true)
    (htarget : ∀ b x,
      (port l lh lg lq h g b x && port r rh rg rq h g b x) = target v b x) :
    Canonical v h g (port l lh lg lq h g) (port r rh rg rq h g) := by
  cases hlq : lq <;> cases hrq : rq
  · obtain ⟨i, hi⟩ := neighbors_nonempty v
    have hfalse : (port l lh lg false h g false (unit i) &&
        port r rh rg false h g false (unit i)) = false := by
      simpa only [hlq, hrq, target, Bool.false_and, Bool.false_or, core_unit]
        using htarget false (unit i)
    have htrue : (port l lh lg false h g false (unit i) &&
        port r rh rg false h g false (unit i)) = true := by
      simpa only [hlq, hrq, port, target, Bool.false_and, Bool.or_false,
        Bool.true_and, hi, Bool.true_or] using htarget true (unit i)
    rw [hfalse] at htrue
    contradiction
  · have hswap : ∀ b x,
        (port r rh rg true h g b x && port l lh lg false h g b x) = target v b x := by
      intro b x
      simpa [hlq, hrq, Bool.and_comm] using htarget b x
    obtain ⟨_, hrg, hlh, hlg, hup, hexact⟩ :=
      canonical_qleft v r l rh rg lh lg h g hdirty gnonzero hswap
    refine ⟨l, hup, Or.inr ⟨?_, ?_⟩⟩
    · simpa [hlq, hrq] using hexact
    · intro b x
      simp [port, hlh, hlg]
  · have hstraight : ∀ b x,
        (port l lh lg true h g b x && port r rh rg false h g b x) = target v b x := by
      intro b x
      simpa [hlq, hrq] using htarget b x
    obtain ⟨_, hlg, hrh, hrg, hup, hexact⟩ :=
      canonical_qleft v l r lh lg rh rg h g hdirty gnonzero hstraight
    refine ⟨r, hup, Or.inl ⟨?_, ?_⟩⟩
    · simpa [hlq, hrq] using hexact
    · intro b x
      simp [port, hrh, hrg]
  · have bad := htarget true 0
    simp [port, target, hlq, hrq, raw_zero, core_zero] at bad

theorem canonical_consequences (v : Fin 3) (h g : Fin 32 → Bool)
    (left right : Bool → Fin 32 → Bool)
    (hcanonical : Canonical v h g left right)
    (htarget : ∀ b x, (left b x && right b x) = target v b x) :
    (∀ x, (h x && upper v x) = core x) ∧
    (∀ x, g x = true → upper v x = true) ∧
    (∀ x, core x = true → raw (neighbors v) x = false → g x = true) := by
  obtain ⟨y, hupper, horient⟩ := hcanonical
  have hbelow (x : Fin 32) : g x = true → upper v x = true := by
    intro hg
    rw [← hupper x]
    simp [hg]
  have hrawbelow : ∀ x, raw y x = true → raw (neighbors v) x = true := by
    apply raw_le_upper_neighbors v y
    intro x hy
    rw [← hupper x]
    simp [hy]
  have hedge (x : Fin 32) (hc : core x = true)
      (hn : raw (neighbors v) x = false) : g x = true := by
    have hu := core_le_upper v x hc
    have hy : raw y x = false := by
      cases heq : raw y x
      · rfl
      · have bad := hrawbelow x heq
        simp [hn] at bad
    rw [← hupper x, hy] at hu
    simpa using hu
  refine ⟨?_, hbelow, hedge⟩
  intro x
  have ht := htarget false x
  rcases horient with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rw [hl, hr, hupper] at ht
    simpa [target] using ht
  · rw [hr, hl, hupper] at ht
    simpa [target, Bool.and_comm] using ht

theorem gfirst_final_consequences (v : Fin 3) (l r : Fin 32)
    (lh lg lq rh rg rq : Bool) (h g : Fin 32 → Bool)
    (hdirty : ∃ x, h x = true ∧ core x = false)
    (gnonzero : ∃ i : Fin 5, g (unit i) = true)
    (htarget : ∀ b x,
      (port l lh lg lq h g b x && port r rh rg rq h g b x) = target v b x) :
    (∀ x, (h x && upper v x) = core x) ∧
    (∀ x, g x = true → upper v x = true) ∧
    (∀ x, core x = true → raw (neighbors v) x = false → g x = true) := by
  apply canonical_consequences v h g (port l lh lg lq h g) (port r rh rg rq h g)
  · exact canonical_final_ports v l r lh lg lq rh rg rq h g hdirty gnonzero htarget
  · exact htarget

end PEqualNP.Outside.L_meta_9033_aux.GFirst

namespace PEqualNP.Outside.L_meta_9033_aux.PackedCofactorBridge

def low5 (s : Fin 64) : Fin 32 := ⟨s.val % 32, Nat.mod_lt _ (by decide)⟩

def upperPacked (v : Fin 3) : Nat :=
  if v.val = 0 then 4294967264 else if v.val = 1 then 4277862138 else 4294966508

theorem coreUnion_split (s g : Nat) :
    BcofactorClassification.coreUnion s g =
      BcofactorClassification.coreUnion s 0 ||| (if s.testBit 5 then g else 0) := by
  simp [BcofactorClassification.coreUnion]

theorem rawMask_testBit : ∀ (p x : Fin 32),
    (BcofactorClassification.coreUnion p.val 0).testBit x.val = HFirst.raw p x := by
  decide +kernel

theorem low5_testBit : ∀ (s : Fin 64) (x : Fin 32),
    (BcofactorClassification.coreUnion s.val 0).testBit x.val = HFirst.raw (low5 s) x := by
  decide +kernel

theorem coreUnion_testBit (s : Fin 64) (g : Nat) (x : Fin 32) :
    (BcofactorClassification.coreUnion s.val g).testBit x.val =
      (HFirst.raw (low5 s) x || (s.val.testBit 5 && g.testBit x.val)) := by
  rw [coreUnion_split, Nat.testBit_or, low5_testBit]
  cases s.val.testBit 5 <;> simp

theorem rawAnd_testBit (p q x : Fin 32) :
    (BcofactorClassification.rawAnd p.val q.val).testBit x.val =
      (HFirst.raw p x && HFirst.raw q x) := by
  rw [BcofactorClassification.rawAnd, Nat.testBit_and, rawMask_testBit, rawMask_testBit]

theorem ac_coreUnion_eq (s g : Nat) :
    ACcofactorClassification.coreUnion s g = BcofactorClassification.coreUnion s g := rfl

theorem ac_rawAnd_eq (p q : Nat) :
    ACcofactorClassification.rawAnd p q = BcofactorClassification.rawAnd p q := rfl

theorem ac_singletonMask_eq (g : Nat) :
    ACcofactorClassification.singletonMask g = BcofactorClassification.singletonMask g := rfl

theorem upperPacked_testBit : ∀ (v : Fin 3) (x : Fin 32),
    (upperPacked v).testBit x.val = HFirst.upper v x := by decide +kernel

theorem coreTarget_testBit (x : Fin 32) :
    BcofactorClassification.coreTarget.testBit x.val = HFirst.core x := rfl

theorem rawMask_bound : ∀ s : Fin 64,
    BcofactorClassification.coreUnion s.val 0 < 2 ^ 32 := by decide +kernel

theorem coreUnion_bound (s : Fin 64) (g : Nat) (hg : g < 2 ^ 32) :
    BcofactorClassification.coreUnion s.val g < 2 ^ 32 := by
  rw [coreUnion_split]
  apply Nat.or_lt_two_pow (rawMask_bound s)
  cases s.val.testBit 5 <;> simp [hg]

theorem rawAnd_bound (p q : Fin 32) :
    BcofactorClassification.rawAnd p.val q.val < 2 ^ 32 := by
  have hp : BcofactorClassification.coreUnion p.val 0 < 2 ^ 32 :=
    rawMask_bound ⟨p.val, by omega⟩
  exact lt_of_le_of_lt Nat.and_le_left hp

theorem hAnd_bound (p q : Fin 64) (g : Nat) (hg : g < 2 ^ 32) :
    (BcofactorClassification.coreUnion p.val g &&&
      BcofactorClassification.coreUnion q.val g) < 2 ^ 32 := by
  exact lt_of_le_of_lt Nat.and_le_left (coreUnion_bound p g hg)

theorem upperPacked_bound : ∀ v : Fin 3, upperPacked v < 2 ^ 32 := by decide +kernel

theorem coreTarget_bound : BcofactorClassification.coreTarget < 2 ^ 32 := by decide +kernel

theorem packed_eq_of_low_bits (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hbits : ∀ x : Fin 32, a.testBit x.val = b.testBit x.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · exact hbits ⟨i, hi⟩
  · have hp : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

theorem land_upper_eq_self (v : Fin 3) (g : Nat) (hg : g < 2 ^ 32)
    (hbelow : ∀ x : Fin 32, g.testBit x.val = true → HFirst.upper v x = true) :
    g &&& upperPacked v = g := by
  apply packed_eq_of_low_bits _ _ (lt_of_le_of_lt Nat.and_le_left hg) hg
  intro x
  rw [Nat.testBit_and, upperPacked_testBit]
  cases hx : g.testBit x.val <;> simp [hx, hbelow x]

theorem land_upper_eq_core (v : Fin 3) (h : Nat)
    (htarget : ∀ x : Fin 32, (h.testBit x.val && HFirst.upper v x) = HFirst.core x) :
    h &&& upperPacked v = BcofactorClassification.coreTarget := by
  apply packed_eq_of_low_bits _ _
    (lt_of_le_of_lt Nat.and_le_right (upperPacked_bound v)) coreTarget_bound
  intro x
  rw [Nat.testBit_and, upperPacked_testBit, coreTarget_testBit]
  exact htarget x

theorem singletonMask_zero_iff (g : Nat) :
    BcofactorClassification.singletonMask g = 0 ↔
      g.testBit 1 = false ∧ g.testBit 2 = false ∧ g.testBit 4 = false ∧
      g.testBit 8 = false ∧ g.testBit 16 = false := by
  unfold BcofactorClassification.singletonMask
  cases h0 : g.testBit 1 <;> cases h1 : g.testBit 2 <;>
    cases h2 : g.testBit 4 <;> cases h3 : g.testBit 8 <;>
    cases h4 : g.testBit 16 <;> simp

theorem singletonMask_zero_iff_units (g : Nat) :
    BcofactorClassification.singletonMask g = 0 ↔
      ∀ i : Fin 5, g.testBit (HFirst.unit i).val = false := by
  rw [singletonMask_zero_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩ i
    have hi : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide +kernel
    rcases hi i with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩

theorem singletonMask_nonzero_of_unit (g : Nat)
    (h : ∃ i : Fin 5, g.testBit (HFirst.unit i).val = true) :
    BcofactorClassification.singletonMask g ≠ 0 := by
  intro hz
  obtain ⟨i, hi⟩ := h
  have hf := (singletonMask_zero_iff_units g).mp hz i
  simp_all

def sourceOr (s : Fin 64) (f : Fin 32 → Bool) (x : Fin 32) : Bool :=
  HFirst.raw (low5 s) x || (s.val.testBit 5 && f x)

def sourceAnd (s t : Fin 64) (f : Fin 32 → Bool) (x : Fin 32) : Bool :=
  sourceOr s f x && sourceOr t f x

theorem sourceOr_testBit (s : Fin 64) (g : Nat) (x : Fin 32) :
    (BcofactorClassification.coreUnion s.val g).testBit x.val =
      sourceOr s (fun y => g.testBit y.val) x := coreUnion_testBit s g x

theorem sourceAnd_testBit (s t : Fin 64) (g : Nat) (x : Fin 32) :
    (BcofactorClassification.coreUnion s.val g &&&
      BcofactorClassification.coreUnion t.val g).testBit x.val =
      sourceAnd s t (fun y => g.testBit y.val) x := by
  rw [Nat.testBit_and, sourceOr_testBit, sourceOr_testBit]
  rfl

theorem sourceAnd_raw_testBit (p q : Fin 32) (s t : Fin 64) (x : Fin 32) :
    (BcofactorClassification.coreUnion s.val (BcofactorClassification.rawAnd p.val q.val) &&&
      BcofactorClassification.coreUnion t.val (BcofactorClassification.rawAnd p.val q.val)).testBit x.val =
      sourceAnd s t (fun y => HFirst.raw p y && HFirst.raw q y) x := by
  rw [sourceAnd_testBit]
  simp only [sourceAnd, sourceOr, rawAnd_testBit]

theorem rawAnd_below_upper (v : Fin 3) (p q : Fin 32)
    (hbelow : ∀ x : Fin 32, (HFirst.raw p x && HFirst.raw q x) = true →
      HFirst.upper v x = true) :
    BcofactorClassification.rawAnd p.val q.val &&& upperPacked v =
      BcofactorClassification.rawAnd p.val q.val := by
  apply land_upper_eq_self v _ (rawAnd_bound p q)
  intro x hx
  rw [rawAnd_testBit] at hx
  exact hbelow x hx

theorem sourceAnd_raw_target (v : Fin 3) (p q : Fin 32) (s t : Fin 64)
    (htarget : ∀ x : Fin 32,
      (sourceAnd s t (fun y => HFirst.raw p y && HFirst.raw q y) x && HFirst.upper v x) =
        HFirst.core x) :
    (BcofactorClassification.coreUnion s.val (BcofactorClassification.rawAnd p.val q.val) &&&
      BcofactorClassification.coreUnion t.val (BcofactorClassification.rawAnd p.val q.val)) &&&
        upperPacked v = BcofactorClassification.coreTarget := by
  apply land_upper_eq_core
  intro x
  rw [sourceAnd_raw_testBit]
  exact htarget x

theorem sourceAnd_raw_singletons_zero (p q : Fin 32) (s t : Fin 64)
    (hzero : ∀ i : Fin 5,
      sourceAnd s t (fun y => HFirst.raw p y && HFirst.raw q y) (HFirst.unit i) = false) :
    BcofactorClassification.singletonMask
      (BcofactorClassification.coreUnion s.val (BcofactorClassification.rawAnd p.val q.val) &&&
        BcofactorClassification.coreUnion t.val (BcofactorClassification.rawAnd p.val q.val)) = 0 := by
  apply (singletonMask_zero_iff_units _).mpr
  intro i
  rw [sourceAnd_raw_testBit]
  exact hzero i

theorem rawAnd_singletons_nonzero (p q : Fin 32)
    (hnonzero : ∃ i : Fin 5, (HFirst.raw p (HFirst.unit i) && HFirst.raw q (HFirst.unit i)) = true) :
    BcofactorClassification.singletonMask (BcofactorClassification.rawAnd p.val q.val) ≠ 0 := by
  apply singletonMask_nonzero_of_unit
  obtain ⟨i, hi⟩ := hnonzero
  refine ⟨i, ?_⟩
  rw [rawAnd_testBit]
  exact hi

theorem upperPacked_A : upperPacked 0 = ACcofactorClassification.upperA := rfl
theorem upperPacked_B : upperPacked 1 = BcofactorClassification.upperTarget := rfl
theorem upperPacked_C : upperPacked 2 = ACcofactorClassification.upperC := rfl
theorem ac_coreTarget_eq : ACcofactorClassification.coreTarget = BcofactorClassification.coreTarget := rfl

end PEqualNP.Outside.L_meta_9033_aux.PackedCofactorBridge

namespace PEqualNP.Outside.L_meta_9033_aux.GFirstModel

open PEqualNP.Outside.L_meta_9033_aux.HFirst
open PEqualNP.Outside.L_meta_9033_aux.PackedCofactorBridge

def gValue (p q : Fin 32) : Nat := BcofactorClassification.rawAnd p.val q.val

def hValue (p q : Fin 32) (u w : Fin 64) : Nat :=
  BcofactorClassification.coreUnion u.val (gValue p q) &&&
    BcofactorClassification.coreUnion w.val (gValue p q)

def maskCount (p q : Fin 32) (u w : Fin 64) (a b : Nat) : Nat :=
  (({p.val, q.val,
      BcofactorClassification.singletonMask (BcofactorClassification.coreUnion u.val (gValue p q)),
      BcofactorClassification.singletonMask (BcofactorClassification.coreUnion w.val (gValue p q)),
      5, a, b} : Finset Nat) \
    {0, 1, 2, 4, 8, 16, 32, BcofactorClassification.singletonMask (gValue p q)}).card

theorem gfirst_model_impossible (v : Fin 3)
    (p q l r : Fin 32) (u w : Fin 64) (lh lg lq rh rg rq : Bool)
    (hzero : ∀ i : Fin 5, (hValue p q u w).testBit (unit i).val = false)
    (hdirty : (∃ x : Fin 32, (hValue p q u w).testBit x.val = true ∧ core x = false) ∨
      (∃ x : Fin 32, (hValue p q u w).testBit x.val = true ∧ upper v x = false))
    (gnonzero : ∃ i : Fin 5, (gValue p q).testBit (unit i).val = true)
    (htarget : ∀ b x,
      (GFirst.port l lh lg lq
          (fun x => (hValue p q u w).testBit x.val) (fun x => (gValue p q).testBit x.val) b x &&
        GFirst.port r rh rg rq
          (fun x => (hValue p q u w).testBit x.val) (fun x => (gValue p q).testBit x.val) b x) =
        GFirst.target v b x)
    (hbudget : v.val = 1 → maskCount p q u w 18 24 ≤ 6 ∨ maskCount p q u w 22 28 ≤ 6) :
    False := by
  have hd : ∃ x : Fin 32, (hValue p q u w).testBit x.val = true ∧ core x = false := by
    rcases hdirty with hd | ⟨x, hx, hn⟩
    · exact hd
    · refine ⟨x, hx, ?_⟩
      cases hc : core x
      · rfl
      · have hu := core_le_upper v x hc
        simp [hu] at hn
  obtain ⟨ht, hb, he⟩ := GFirst.gfirst_final_consequences v l r lh lg lq rh rg rq
    (fun x => (hValue p q u w).testBit x.val) (fun x => (gValue p q).testBit x.val)
    hd gnonzero htarget
  have hbelow := land_upper_eq_self v (gValue p q) (rawAnd_bound p q) hb
  have hcore := land_upper_eq_core v (hValue p q u w) ht
  have hz := (singletonMask_zero_iff_units (hValue p q u w)).mpr hzero
  have hn := singletonMask_nonzero_of_unit (gValue p q) gnonzero
  have cases_v : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide +kernel
  rcases cases_v v with rfl | rfl | rfl
  · have he1 : (gValue p q).testBit 5 = true :=
      he 5 (by decide +kernel) (by decide +kernel)
    have he2 : (gValue p q).testBit 6 = true :=
      he 6 (by decide +kernel) (by decide +kernel)
    exact ACcofactorClassification.no_A_gfirst p q u w hbelow he1 he2 hn hcore hz
  · have he1 : (gValue p q).testBit 10 = true :=
      he 10 (by decide +kernel) (by decide +kernel)
    rcases hbudget rfl with ho | hs
    · exact BcofactorClassification.no_six_mask_budget p q u w hbelow he1 hn hcore hz ho
    · exact BcofactorClassification.no_six_shared_reader_mask_budget p q u w hbelow he1 hn hcore hz hs
  · have he1 : (gValue p q).testBit 5 = true :=
      he 5 (by decide +kernel) (by decide +kernel)
    have he2 : (gValue p q).testBit 12 = true :=
      he 12 (by decide +kernel) (by decide +kernel)
    exact ACcofactorClassification.no_C_gfirst p q u w hbelow he1 he2 hn hcore hz

theorem gfirst_source_model_impossible (v : Fin 3)
    (p q l r : Fin 32) (u w : Fin 64) (lh lg lq rh rg rq : Bool) :
    let g : Fin 32 → Bool := fun x => raw p x && raw q x
    let h : Fin 32 → Bool := sourceAnd u w g
    (∀ i : Fin 5, h (unit i) = false) →
    ((∃ x : Fin 32, h x = true ∧ core x = false) ∨
      (∃ x : Fin 32, h x = true ∧ upper v x = false)) →
    (∃ i : Fin 5, g (unit i) = true) →
    (∀ b x, (GFirst.port l lh lg lq h g b x && GFirst.port r rh rg rq h g b x) =
      GFirst.target v b x) →
    (v.val = 1 → maskCount p q u w 18 24 ≤ 6 ∨ maskCount p q u w 22 28 ≤ 6) → False := by
  dsimp only
  intro hs hd gs ht budget
  apply gfirst_model_impossible v p q l r u w lh lg lq rh rg rq
  · simpa only [hValue, gValue, sourceAnd_raw_testBit] using hs
  · simpa only [hValue, gValue, sourceAnd_raw_testBit] using hd
  · simpa only [gValue, rawAnd_testBit] using gs
  · simpa only [hValue, gValue, sourceAnd_raw_testBit, rawAnd_testBit] using ht
  · exact budget

end PEqualNP.Outside.L_meta_9033_aux.GFirstModel

namespace PEqualNP.Outside.L_meta_9033_aux.ReaderCofactorBridge

def abcIndex (i : Fin 3) : Fin 8 := ⟨i.val, by omega⟩
def coreIndex (i : Fin 5) : Fin 8 := ⟨i.val + 3, by omega⟩

def embed (v : Fin 3) (b : Bool) (x : Fin 32) (i : Fin 8) : Bool :=
  if i.val < 3 then decide (i.val = v.val) && b
  else x.val.testBit (i.val - 3)

theorem embed_abc : ∀ (v : Fin 3) (b : Bool) (x : Fin 32) (i : Fin 3),
    embed v b x (abcIndex i) = (decide (i = v) && b) := by
  decide +kernel

theorem embed_other_abc_zero : ∀ (v i : Fin 3) (b : Bool) (x : Fin 32),
    i ≠ v → embed v b x (abcIndex i) = false := by
  decide +kernel

theorem embed_core : ∀ (v : Fin 3) (b : Bool) (x : Fin 32) (i : Fin 5),
    embed v b x (coreIndex i) = x.val.testBit i.val := by
  decide +kernel

theorem embed_core_singleton : ∀ (v : Fin 3) (i : Fin 5) (j : Fin 8),
    embed v false (HFirst.unit i) j = decide (j.val = i.val + 3) := by
  decide +kernel

theorem embed_distinguished_singleton : ∀ (v : Fin 3) (j : Fin 8),
    embed v true 0 j = decide (j.val = v.val) := by
  decide +kernel

theorem core_formula : ∀ x : Fin 32,
    HFirst.core x =
      ((x.val.testBit 0 && x.val.testBit 2) ||
       (x.val.testBit 0 && x.val.testBit 4) ||
       (x.val.testBit 1 && x.val.testBit 2) ||
       (x.val.testBit 1 && x.val.testBit 3) ||
       (x.val.testBit 2 && x.val.testBit 3)) := by
  decide +kernel

theorem readerGraph_embed : ∀ (v : Fin 3) (b : Bool) (x : Fin 32),
    readerGraph (embed v b x) = GFirst.target v b x := by
  decide +kernel

theorem readerGraph_pin_false (v : Fin 3) (x : Fin 32) :
    readerGraph (embed v false x) = HFirst.core x := by
  simpa [GFirst.target] using readerGraph_embed v false x

theorem readerGraph_pin_true (v : Fin 3) (x : Fin 32) :
    readerGraph (embed v true x) = HFirst.upper v x := by
  simpa [GFirst.target, HFirst.upper] using readerGraph_embed v true x

end PEqualNP.Outside.L_meta_9033_aux.ReaderCofactorBridge
