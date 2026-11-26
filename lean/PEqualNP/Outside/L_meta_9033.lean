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


namespace PEqualNP.Outside.L_meta_9033_aux.MaskProjection

theorem nonatom_image_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (project : α → β) (required globalAtoms : Finset α) (localAtoms : Finset β)
    (atom_map : ∀ a ∈ globalAtoms, project a ∈ localAtoms) :
    ((required.image project) \ localAtoms).card ≤ (required \ globalAtoms).card := by
  have subset : (required.image project) \ localAtoms ⊆
      (required \ globalAtoms).image project := by
    intro x hx
    obtain ⟨himage, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp himage
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_sdiff.mpr ⟨ha, ?_⟩, rfl⟩
    intro hatom
    exact hnot (atom_map a hatom)
  exact (Finset.card_le_card subset).trans Finset.card_image_le

theorem nonatom_image_budget {α β : Type*} [DecidableEq α] [DecidableEq β]
    (project : α → β) (required globalAtoms : Finset α) (localAtoms : Finset β)
    (atom_map : ∀ a ∈ globalAtoms, project a ∈ localAtoms) (n : Nat)
    (hbudget : (required \ globalAtoms).card ≤ n) :
    ((required.image project) \ localAtoms).card ≤ n := by
  exact (nonatom_image_card_le project required globalAtoms localAtoms atom_map).trans hbudget

def projectNat (v : Fin 3) (mask : Nat) : Nat :=
  (mask / 8 % 32) ||| (if mask.testBit v.val then 32 else 0)

theorem projectNat_lt64 (v : Fin 3) (mask : Nat) : projectNat v mask < 64 := by
  have hc : mask / 8 % 32 < 2 ^ 6 := by
    have hm := Nat.mod_lt (mask / 8) (by decide : 0 < 32)
    omega
  have hv : (if mask.testBit v.val then 32 else 0) < 2 ^ 6 := by
    split <;> decide
  exact Nat.or_lt_two_pow hc hv

def projectMask (v : Fin 3) (mask : Fin 256) : Fin 64 :=
  ⟨projectNat v mask.val, projectNat_lt64 v mask.val⟩

def globalRawAtoms : Finset Nat := {0, 1, 2, 4, 8, 16, 32, 64, 128}
def localRawAtoms : Finset Nat := {0, 1, 2, 4, 8, 16, 32}

theorem projectNat_zero : ∀ v : Fin 3, projectNat v 0 = 0 := by decide +kernel

theorem projectNat_singleton : ∀ (v : Fin 3) (i : Fin 8),
    projectNat v (2 ^ i.val) =
      if i.val < 3 then (if i.val = v.val then 32 else 0) else 2 ^ (i.val - 3) := by
  decide +kernel

theorem raw_atoms_map : ∀ v : Fin 3, ∀ a ∈ globalRawAtoms,
    projectNat v a ∈ localRawAtoms := by
  decide +kernel

theorem exceptional_atoms_map (v : Fin 3) (exceptional : Nat) :
    ∀ a ∈ insert exceptional globalRawAtoms,
      projectNat v a ∈ insert (projectNat v exceptional) localRawAtoms := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (raw_atoms_map v a ha)

theorem projected_mask_card_le (v : Fin 3) (required : Finset Nat) (exceptional : Nat) :
    ((required.image (projectNat v)) \ insert (projectNat v exceptional) localRawAtoms).card ≤
      (required \ insert exceptional globalRawAtoms).card := by
  exact nonatom_image_card_le (projectNat v) required (insert exceptional globalRawAtoms)
    (insert (projectNat v exceptional) localRawAtoms) (exceptional_atoms_map v exceptional)

theorem projected_mask_budget (v : Fin 3) (required : Finset Nat) (exceptional n : Nat)
    (hbudget : (required \ insert exceptional globalRawAtoms).card ≤ n) :
    ((required.image (projectNat v)) \ insert (projectNat v exceptional) localRawAtoms).card ≤ n := by
  exact (projected_mask_card_le v required exceptional).trans hbudget

def globalRawAtoms256 : Finset (Fin 256) := {0, 1, 2, 4, 8, 16, 32, 64, 128}
def localRawAtoms64 : Finset (Fin 64) := {0, 1, 2, 4, 8, 16, 32}

theorem bounded_raw_atoms_map : ∀ v : Fin 3, ∀ a ∈ globalRawAtoms256,
    projectMask v a ∈ localRawAtoms64 := by
  decide +kernel

theorem bounded_exceptional_atoms_map (v : Fin 3) (exceptional : Fin 256) :
    ∀ a ∈ insert exceptional globalRawAtoms256,
      projectMask v a ∈ insert (projectMask v exceptional) localRawAtoms64 := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (bounded_raw_atoms_map v a ha)

theorem bounded_projected_mask_budget (v : Fin 3) (required : Finset (Fin 256))
    (exceptional : Fin 256) (n : Nat)
    (hbudget : (required \ insert exceptional globalRawAtoms256).card ≤ n) :
    ((required.image (projectMask v)) \
      insert (projectMask v exceptional) localRawAtoms64).card ≤ n := by
  exact nonatom_image_budget (projectMask v) required (insert exceptional globalRawAtoms256)
    (insert (projectMask v exceptional) localRawAtoms64)
    (bounded_exceptional_atoms_map v exceptional) n hbudget

end PEqualNP.Outside.L_meta_9033_aux.MaskProjection

namespace PEqualNP.Outside.L_meta_9033_aux.MaskSignatureTransport

def signature8 (f : Fin 8 → Bool) : Nat :=
  (if f 0 then 1 else 0) + (if f 1 then 2 else 0) +
  (if f 2 then 4 else 0) + (if f 3 then 8 else 0) +
  (if f 4 then 16 else 0) + (if f 5 then 32 else 0) +
  (if f 6 then 64 else 0) + (if f 7 then 128 else 0)

def signature6 (core : Fin 5 → Bool) (retained : Bool) : Nat :=
  (if core 0 then 1 else 0) + (if core 1 then 2 else 0) +
  (if core 2 then 4 else 0) + (if core 3 then 8 else 0) +
  (if core 4 then 16 else 0) + (if retained then 32 else 0)

theorem project_signature_values : ∀ (v : Fin 3) (a b c d e f g h : Bool),
    MaskProjection.projectNat v
      ((if a then 1 else 0) + (if b then 2 else 0) +
       (if c then 4 else 0) + (if d then 8 else 0) +
       (if e then 16 else 0) + (if f then 32 else 0) +
       (if g then 64 else 0) + (if h then 128 else 0)) =
      ((if d then 1 else 0) + (if e then 2 else 0) +
       (if f then 4 else 0) + (if g then 8 else 0) + (if h then 16 else 0) +
       (if (if v.val = 0 then a else if v.val = 1 then b else c) then 32 else 0)) := by
  decide +kernel

theorem project_signature8 : ∀ (v : Fin 3) (f : Fin 8 → Bool),
    MaskProjection.projectNat v (signature8 f) =
      signature6 (fun i => f (ReaderCofactorBridge.coreIndex i))
        (f (ReaderCofactorBridge.abcIndex v)) := by
  intro v f
  have hp := project_signature_values v (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  have cases_v : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide +kernel
  have hv : f (ReaderCofactorBridge.abcIndex v) =
      (if v.val = 0 then f 0 else if v.val = 1 then f 1 else f 2) := by
    rcases cases_v v with rfl | rfl | rfl <;> rfl
  have h0 : f (ReaderCofactorBridge.coreIndex 0) = f 3 := rfl
  have h1 : f (ReaderCofactorBridge.coreIndex 1) = f 4 := rfl
  have h2 : f (ReaderCofactorBridge.coreIndex 2) = f 5 := rfl
  have h3 : f (ReaderCofactorBridge.coreIndex 3) = f 6 := rfl
  have h4 : f (ReaderCofactorBridge.coreIndex 4) = f 7 := rfl
  simpa only [signature8, signature6, h0, h1, h2, h3, h4, hv] using hp

def globalUnit (i j : Fin 8) : Bool := decide (j = i)

def globalMask (truth : (Fin 8 → Bool) → Bool) : Nat :=
  signature8 (fun i => truth (globalUnit i))

def localMask (v : Fin 3) (truth : (Fin 8 → Bool) → Bool) : Nat :=
  signature6 (fun i => truth (ReaderCofactorBridge.embed v false (HFirst.unit i)))
    (truth (ReaderCofactorBridge.embed v true 0))

theorem embed_core_as_globalUnit (v : Fin 3) (i : Fin 5) :
    ReaderCofactorBridge.embed v false (HFirst.unit i) =
      globalUnit (ReaderCofactorBridge.coreIndex i) := by
  funext j
  simpa only [globalUnit, ReaderCofactorBridge.coreIndex, Fin.ext_iff]
    using ReaderCofactorBridge.embed_core_singleton v i j

theorem embed_retained_as_globalUnit (v : Fin 3) :
    ReaderCofactorBridge.embed v true 0 = globalUnit (ReaderCofactorBridge.abcIndex v) := by
  funext j
  simpa only [globalUnit, ReaderCofactorBridge.abcIndex, Fin.ext_iff]
    using ReaderCofactorBridge.embed_distinguished_singleton v j

theorem localMask_eq_projection (v : Fin 3) (truth : (Fin 8 → Bool) → Bool) :
    localMask v truth = MaskProjection.projectNat v (globalMask truth) := by
  unfold localMask globalMask
  rw [project_signature8]
  simp only [embed_core_as_globalUnit, embed_retained_as_globalUnit]

theorem cofactor_signature_budget {α : Type*} [DecidableEq α]
    (v : Fin 3) (truth : α → (Fin 8 → Bool) → Bool) (required : Finset α)
    (exceptional : (Fin 8 → Bool) → Bool) (n : Nat)
    (hbudget : ((required.image (fun i => globalMask (truth i))) \
      insert (globalMask exceptional) MaskProjection.globalRawAtoms).card ≤ n) :
    ((required.image (fun i => localMask v (truth i))) \
      insert (localMask v exceptional) MaskProjection.localRawAtoms).card ≤ n := by
  have hp := MaskProjection.projected_mask_budget v
    (required.image (fun i => globalMask (truth i))) (globalMask exceptional) n hbudget
  simpa only [Finset.image_image, Function.comp_def, localMask_eq_projection] using hp

end PEqualNP.Outside.L_meta_9033_aux.MaskSignatureTransport

namespace PEqualNP.Outside.L_meta_9033_aux.CausalOrFlattening

def basisOr {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (support : Finset β) (x : α) : Bool :=
  decide (∃ b ∈ support, basis b x = true)

lemma basisOr_true {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (support : Finset β) (x : α) :
    basisOr basis support x = true ↔ ∃ b ∈ support, basis b x = true := by
  simp [basisOr]

lemma basisOr_empty {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (x : α) : basisOr basis ∅ x = false := by
  simp [basisOr]

lemma basisOr_singleton {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (b : β) (x : α) :
    basisOr basis {b} x = basis b x := by
  cases hb : basis b x <;> simp [basisOr, hb]

lemma bool_or_true {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

lemma bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma basisOr_union {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (s t : Finset β) (x : α) :
    basisOr basis (s ∪ t) x = (basisOr basis s x || basisOr basis t x) := by
  apply bool_eq_of_true_iff
  rw [basisOr_true, bool_or_true, basisOr_true, basisOr_true]
  constructor
  · rintro ⟨b, hb, hx⟩
    rcases Finset.mem_union.mp hb with hs | ht
    · exact Or.inl ⟨b, hs, hx⟩
    · exact Or.inr ⟨b, ht, hx⟩
  · rintro (⟨b, hb, hx⟩ | ⟨b, hb, hx⟩)
    · exact ⟨b, Finset.mem_union.mpr (Or.inl hb), hx⟩
    · exact ⟨b, Finset.mem_union.mpr (Or.inr hb), hx⟩

theorem causal_or_flatten_allowed {n : Nat} {α β : Type*}
    [DecidableEq β]
    (value : Fin n → α → Bool) (basis : β → α → Bool) (allowed : Finset β)
    (step : ∀ i,
      (∀ x, value i x = false) ∨
      (∃ b ∈ allowed, ∀ x, value i x = basis b x) ∨
      (∃ j k : Fin n, j.val < i.val ∧ k.val < i.val ∧
        ∀ x, value i x = (value j x || value k x))) :
    ∀ i, ∃ support : Finset β, support ⊆ allowed ∧
      ∀ x, value i x = basisOr basis support x := by
  have cover : ∀ m, ∀ i : Fin n, i.val = m →
      ∃ support : Finset β, support ⊆ allowed ∧
        ∀ x, value i x = basisOr basis support x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro i hi
      rcases step i with hz | ⟨b, hb, heq⟩ | ⟨j, k, hj, hk, heq⟩
      · refine ⟨∅, Finset.empty_subset allowed, ?_⟩
        intro x
        rw [hz x, basisOr_empty]
      · refine ⟨{b}, ?_, ?_⟩
        · intro c hc
          have hcb : c = b := Finset.mem_singleton.mp hc
          simpa only [hcb] using hb
        · intro x
          rw [basisOr_singleton]
          exact heq x
      · obtain ⟨sj, hsj, hej⟩ := ih j.val (by omega) j rfl
        obtain ⟨sk, hsk, hek⟩ := ih k.val (by omega) k rfl
        refine ⟨sj ∪ sk, ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_union.mp hb with hb | hb
          · exact hsj hb
          · exact hsk hb
        · intro x
          rw [heq x, hej x, hek x, basisOr_union]
  intro i
  exact cover i.val i rfl

theorem causal_or_flatten {n : Nat} {α β : Type*}
    [Fintype β] [DecidableEq β]
    (value : Fin n → α → Bool) (basis : β → α → Bool)
    (step : ∀ i,
      (∀ x, value i x = false) ∨
      (∃ b, ∀ x, value i x = basis b x) ∨
      (∃ j k : Fin n, j.val < i.val ∧ k.val < i.val ∧
        ∀ x, value i x = (value j x || value k x))) :
    ∀ i, ∃ support : Finset β, ∀ x, value i x = basisOr basis support x := by
  have hstep : ∀ i,
      (∀ x, value i x = false) ∨
      (∃ b ∈ (Finset.univ : Finset β), ∀ x, value i x = basis b x) ∨
      (∃ j k : Fin n, j.val < i.val ∧ k.val < i.val ∧
        ∀ x, value i x = (value j x || value k x)) := by
    intro i
    rcases step i with hz | ⟨b, hb⟩ | hor
    · exact Or.inl hz
    · exact Or.inr (Or.inl ⟨b, Finset.mem_univ b, hb⟩)
    · exact Or.inr (Or.inr hor)
  intro i
  obtain ⟨support, _, hsupport⟩ :=
    causal_or_flatten_allowed value basis Finset.univ hstep i
  exact ⟨support, hsupport⟩

theorem selected_basis_below {α β : Type*} [DecidableEq β]
    (basis : β → α → Bool) (support : Finset β) (b : β) (hb : b ∈ support) :
    ∀ x, basis b x = true → basisOr basis support x = true := by
  intro x hx
  exact (basisOr_true basis support x).mpr ⟨b, hb, hx⟩

theorem causal_or_flatten_good {n : Nat} {α β : Type*}
    [DecidableEq β]
    (value : Fin n → α → Bool) (basis : β → α → Bool)
    (good : Fin n → Prop) (allowed : Finset β)
    (step : ∀ i, good i →
      (∀ x, value i x = false) ∨
      (∃ b ∈ allowed, ∀ x, value i x = basis b x) ∨
      (∃ j k : Fin n, j.val < i.val ∧ k.val < i.val ∧ good j ∧ good k ∧
        ∀ x, value i x = (value j x || value k x))) :
    ∀ i, good i → ∃ support : Finset β, support ⊆ allowed ∧
      ∀ x, value i x = basisOr basis support x := by
  have cover : ∀ m, ∀ i : Fin n, i.val = m → good i →
      ∃ support : Finset β, support ⊆ allowed ∧
        ∀ x, value i x = basisOr basis support x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro i hi hgood
      rcases step i hgood with hz | ⟨b, hb, heq⟩ | ⟨j, k, hj, hk, hgj, hgk, heq⟩
      · refine ⟨∅, Finset.empty_subset allowed, ?_⟩
        intro x
        rw [hz x, basisOr_empty]
      · refine ⟨{b}, ?_, ?_⟩
        · intro c hc
          have hcb : c = b := Finset.mem_singleton.mp hc
          simpa only [hcb] using hb
        · intro x
          rw [basisOr_singleton]
          exact heq x
      · obtain ⟨sj, hsj, hej⟩ := ih j.val (by omega) j rfl hgj
        obtain ⟨sk, hsk, hek⟩ := ih k.val (by omega) k rfl hgk
        refine ⟨sj ∪ sk, ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_union.mp hb with hb | hb
          · exact hsj hb
          · exact hsk hb
        · intro x
          rw [heq x, hej x, hek x, basisOr_union]
  intro i hgood
  exact cover i.val i rfl hgood

end PEqualNP.Outside.L_meta_9033_aux.CausalOrFlattening

namespace PEqualNP.Outside.L_meta_9033_aux.ConcreteOrPorts

open CausalOrFlattening

def rawMask (a b c d e : Bool) : Fin 32 :=
  ⟨(if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
    (if d then 8 else 0) + (if e then 16 else 0), by
    have h : ∀ a b c d e : Bool,
        (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
          (if d then 8 else 0) + (if e then 16 else 0) < 32 := by decide +kernel
    exact h a b c d e⟩

theorem rawMask_eval : ∀ (a b c d e : Bool) (x : Fin 32),
    HFirst.raw (rawMask a b c d e) x =
      ((a && x.val.testBit 0) || (b && x.val.testBit 1) ||
        (c && x.val.testBit 2) || (d && x.val.testBit 3) || (e && x.val.testBit 4)) := by
  decide +kernel

def supportRawMask (support : Finset (Fin 8)) : Fin 32 :=
  rawMask (decide (0 ∈ support)) (decide (1 ∈ support)) (decide (2 ∈ support))
    (decide (3 ∈ support)) (decide (4 ∈ support))

def portBasis {α : Type*} (row : α → Fin 32) (h g q : α → Bool)
    (i : Fin 8) (x : α) : Bool :=
  if i.val < 5 then (row x).val.testBit i.val
  else if i.val = 5 then h x else if i.val = 6 then g x else q x

lemma fin8_exists (P : Fin 8 → Prop) :
    (∃ i, P i) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 := by
  constructor
  · rintro ⟨i, hi⟩
    have hc : ∀ i : Fin 8,
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      decide +kernel
    rcases hc i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩

theorem basisOr_fin8 {α : Type*} (basis : Fin 8 → α → Bool)
    (support : Finset (Fin 8)) (x : α) :
    basisOr basis support x =
      ((decide (0 ∈ support) && basis 0 x) || (decide (1 ∈ support) && basis 1 x) ||
       (decide (2 ∈ support) && basis 2 x) || (decide (3 ∈ support) && basis 3 x) ||
       (decide (4 ∈ support) && basis 4 x) || (decide (5 ∈ support) && basis 5 x) ||
       (decide (6 ∈ support) && basis 6 x) || (decide (7 ∈ support) && basis 7 x)) := by
  apply bool_eq_of_true_iff
  rw [basisOr_true, fin8_exists]
  simp [or_assoc]

theorem basisOr_portBasis {α : Type*} (row : α → Fin 32) (h g q : α → Bool)
    (support : Finset (Fin 8)) (x : α) :
    basisOr (portBasis row h g q) support x =
      HFirst.finalSide (supportRawMask support)
        (decide (5 ∈ support)) (decide (6 ∈ support)) (decide (7 ∈ support))
        (h x) (g x) (q x) (row x) := by
  rw [basisOr_fin8]
  simp [portBasis, HFirst.finalSide, supportRawMask, rawMask_eval]

theorem exists_final_port {α : Type*} (row : α → Fin 32) (h g q : α → Bool)
    (support : Finset (Fin 8)) :
    ∃ p : Fin 32, ∃ takeH takeG takeQ : Bool, ∀ x,
      basisOr (portBasis row h g q) support x =
        HFirst.finalSide p takeH takeG takeQ (h x) (g x) (q x) (row x) := by
  exact ⟨supportRawMask support, decide (5 ∈ support), decide (6 ∈ support),
    decide (7 ∈ support), basisOr_portBasis row h g q support⟩

theorem basisOr_portBasis_no_g {α : Type*} (row : α → Fin 32) (h g q : α → Bool)
    (support : Finset (Fin 8)) (hno : (6 : Fin 8) ∉ support) (x : α) :
    basisOr (portBasis row h g q) support x =
      (HFirst.raw (supportRawMask support) (row x) ||
        (decide (5 ∈ support) && h x) || (decide (7 ∈ support) && q x)) := by
  rw [basisOr_portBasis]
  simp [HFirst.finalSide, hno]

theorem basisOr_portBasis_raw_only {α : Type*} (row : α → Fin 32) (h g q : α → Bool)
    (support : Finset (Fin 8))
    (h5 : (5 : Fin 8) ∉ support) (h6 : (6 : Fin 8) ∉ support) (h7 : (7 : Fin 8) ∉ support)
    (x : α) : basisOr (portBasis row h g q) support x =
      HFirst.raw (supportRawMask support) (row x) := by
  rw [basisOr_portBasis]
  simp [HFirst.finalSide, h5, h6, h7]

def sourceSelector (p : Fin 32) (takeG : Bool) : Fin 64 :=
  ⟨p.val + (if takeG then 32 else 0), by cases takeG <;> simp <;> omega⟩

theorem sourceSelector_low5 : ∀ (p : Fin 32) (takeG : Bool),
    PackedCofactorBridge.low5 (sourceSelector p takeG) = p := by
  decide +kernel

theorem sourceSelector_bit5 : ∀ (p : Fin 32) (takeG : Bool),
    (sourceSelector p takeG).val.testBit 5 = takeG := by
  decide +kernel

theorem sourceOr_selector (p : Fin 32) (takeG : Bool) (g : Fin 32 → Bool) (x : Fin 32) :
    PackedCofactorBridge.sourceOr (sourceSelector p takeG) g x =
      (HFirst.raw p x || (takeG && g x)) := by
  simp [PackedCofactorBridge.sourceOr, sourceSelector_low5, sourceSelector_bit5]

theorem basisOr_portBasis_g_only (h g q : Fin 32 → Bool)
    (support : Finset (Fin 8))
    (h5 : (5 : Fin 8) ∉ support) (h7 : (7 : Fin 8) ∉ support) (x : Fin 32) :
    basisOr (portBasis (fun z => z) h g q) support x =
      PackedCofactorBridge.sourceOr
        (sourceSelector (supportRawMask support) (decide (6 ∈ support))) g x := by
  rw [basisOr_portBasis, sourceOr_selector]
  simp [HFirst.finalSide, h5, h7]

theorem causal_final_port {n : Nat} {α : Type*}
    (value : Fin n → α → Bool) (row : α → Fin 32) (h g q : α → Bool)
    (good : Fin n → Prop) (allowed : Finset (Fin 8))
    (step : ∀ i, good i →
      (∀ x, value i x = false) ∨
      (∃ b ∈ allowed, ∀ x, value i x = portBasis row h g q b x) ∨
      (∃ j k : Fin n, j.val < i.val ∧ k.val < i.val ∧ good j ∧ good k ∧
        ∀ x, value i x = (value j x || value k x))) :
    ∀ i, good i → ∃ support : Finset (Fin 8), support ⊆ allowed ∧
      ∀ x, value i x = HFirst.finalSide (supportRawMask support)
        (decide (5 ∈ support)) (decide (6 ∈ support)) (decide (7 ∈ support))
        (h x) (g x) (q x) (row x) := by
  intro i hi
  obtain ⟨support, hallowed, hvalue⟩ :=
    causal_or_flatten_good value (portBasis row h g q) good allowed step i hi
  refine ⟨support, hallowed, ?_⟩
  intro x
  exact (hvalue x).trans (basisOr_portBasis row h g q support x)

end PEqualNP.Outside.L_meta_9033_aux.ConcreteOrPorts

namespace PEqualNP.Outside.L_meta_9033_aux.QMateExtraction

open PEqualNP.Outside.L_meta_9033_aux.HFirst

def mate (p : Fin 32) (takeH takeG : Bool)
    (h g : Bool → Fin 32 → Bool) (b : Bool) (x : Fin 32) : Bool :=
  raw p x || (takeH && h b x) || (takeG && g b x)

theorem raw_zero_of_singletons : ∀ p : Fin 32,
    (∀ i : Fin 5, raw p (unit i) = false) → p = 0 := by
  decide +kernel

theorem mate_exact_h (p : Fin 32) (takeH takeG : Bool)
    (h g : Bool → Fin 32 → Bool)
    (hcore : ∀ i : Fin 5, mate p takeH takeG h g false (unit i) = false)
    (hretained : mate p takeH takeG h g true 0 = false)
    (hgsingleton : (∃ i : Fin 5, g false (unit i) = true) ∨ g true 0 = true)
    (hpositive : ∃ b x, mate p takeH takeG h g b x = true) :
    p = 0 ∧ takeG = false ∧ takeH = true ∧
      ∀ b x, mate p takeH takeG h g b x = h b x := by
  have hp : p = 0 := by
    apply raw_zero_of_singletons p
    intro i
    have hi := hcore i
    cases hr : raw p (unit i)
    · rfl
    · simp [mate, hr] at hi
  have hg : takeG = false := by
    cases he : takeG
    · rfl
    · exfalso
      rcases hgsingleton with ⟨i, hi⟩ | hi
      · have hz := hcore i
        simp [mate, he, hi] at hz
      · simp [mate, he, hi] at hretained
  have hh : takeH = true := by
    cases he : takeH
    · obtain ⟨b, x, hx⟩ := hpositive
      simp [mate, hp, hg, he, zero_raw] at hx
    · rfl
  refine ⟨hp, hg, hh, ?_⟩
  intro b x
  simp [mate, hp, hg, hh, zero_raw]

theorem q_eq_of_mate_eq (q h m : Bool → Fin 32 → Bool)
    (hq : ∀ b x, q b x = (b || m b x))
    (hm : ∀ b x, m b x = h b x) :
    ∀ b x, q b x = (b || h b x) := by
  intro b x
  rw [hq, hm]

end PEqualNP.Outside.L_meta_9033_aux.QMateExtraction

namespace PEqualNP.Outside.L_meta_9033_aux.PhysicalOrPorts

def rawIndex (i : Fin 8) : Nat :=
  if i.val < 3 then i.val else if i.val = 3 then 4 else if i.val = 4 then 5
  else if i.val = 5 then 8 else if i.val = 6 then 9 else 10

def rawSlots : Finset Nat := {0, 1, 2, 4, 5, 8, 9, 10}

theorem rawSlots_iff : ∀ w : Fin 11,
    w.val ∈ rawSlots ↔ ∃ i : Fin 8, rawIndex i = w.val := by
  decide +kernel

def usable (v : Fin 3) (w : Nat) : Prop :=
  w ≠ v.val ∧ (11 ≤ w ∨ w ∈ rawSlots)

def sourceIndex {m : Nat} (h g q : Fin m) (b : Fin 8) : Nat :=
  if hb : b.val < 5 then rawIndex ⟨b.val + 3, by omega⟩
  else if b.val = 5 then 11 + h.val else if b.val = 6 then 11 + g.val else 11 + q.val

def basisLabels : Finset (Fin 8) := {0, 1, 2, 3, 4, 5, 6, 7}

theorem basisLabels_complete : ∀ b : Fin 8, b ∈ basisLabels := by decide +kernel

def allowedSources {m : Nat} (h g q : Fin m) (limit : Nat) : Finset (Fin 8) :=
  basisLabels.filter (fun b => sourceIndex h g q b < 11 + limit)

theorem trace_prefix_final_port {m : Nat} (v : Fin 3) (limit : Nat)
    (hlimit : limit ≤ m) (a b : Fin m → Nat) (op : Fin m → Bool)
    (h g q : Fin m) (value : Nat → (Bool × Fin 32) → Bool)
    (ha : ∀ i, a i < 11 + i.val) (hb : ∀ i, b i < 11 + i.val)
    (hav : ∀ i, a i < 11 → a i ∈ rawSlots)
    (hbv : ∀ i, b i < 11 → b i ∈ rawSlots)
    (hraw : ∀ (i : Fin 8) (s : Bool × Fin 32),
      value (rawIndex i) s = ReaderCofactorBridge.embed v s.1 s.2 i)
    (hgate : ∀ (i : Fin m) (s : Bool × Fin 32),
      value (11 + i.val) s =
        if op i then (value (a i) s && value (b i) s)
        else (value (a i) s || value (b i) s))
    (hand : ∀ i, i.val < limit → op i = true →
      i = h ∨ i = g ∨ ∀ s : Bool × Fin 32, value (11 + i.val) s = false)
    (hsole : ∀ i, a i = v.val ∨ b i = v.val → i = q) :
    ∀ w : Fin (11 + limit), usable v w.val →
      ∃ support : Finset (Fin 8), support ⊆ allowedSources h g q limit ∧
        ∀ s : Bool × Fin 32,
          value w.val s = HFirst.finalSide (ConcreteOrPorts.supportRawMask support)
            (decide (5 ∈ support)) (decide (6 ∈ support)) (decide (7 ∈ support))
            (value (11 + h.val) s) (value (11 + g.val) s)
            (value (11 + q.val) s) s.2 := by
  let basis := ConcreteOrPorts.portBasis (fun s : Bool × Fin 32 => s.2)
    (value (11 + h.val)) (value (11 + g.val)) (value (11 + q.val))
  have step : ∀ w : Fin (11 + limit), usable v w.val →
      (∀ s, value w.val s = false) ∨
      (∃ c ∈ allowedSources h g q limit, ∀ s, value w.val s = basis c s) ∨
      (∃ j k : Fin (11 + limit), j.val < w.val ∧ k.val < w.val ∧
        usable v j.val ∧ usable v k.val ∧
        ∀ s, value w.val s = (value j.val s || value k.val s)) := by
    intro w hw
    have cutoff (c : Fin 8) (hc : sourceIndex h g q c = w.val) :
        c ∈ allowedSources h g q limit := by
      unfold allowedSources
      apply Finset.mem_filter.mpr
      refine ⟨basisLabels_complete c, ?_⟩
      rw [hc]
      exact w.isLt
    by_cases hwr : w.val < 11
    · have hslot : w.val ∈ rawSlots := by
        rcases hw.2 with hlarge | hslot
        · omega
        · exact hslot
      obtain ⟨r, hr⟩ := (rawSlots_iff ⟨w.val, hwr⟩).mp hslot
      by_cases habc : r.val < 3
      · left
        have hridx : rawIndex r = r.val := by simp [rawIndex, habc]
        have hrv : r.val ≠ v.val := by
          intro heq
          apply hw.1
          exact hr.symm.trans (hridx.trans heq)
        intro s
        have hx := hraw r s
        rw [hr] at hx
        simpa [ReaderCofactorBridge.embed, habc, hrv] using hx
      · let c : Fin 8 := ⟨r.val - 3, by omega⟩
        have hc : c.val < 5 := by dsimp [c]; omega
        have hcr : (⟨c.val + 3, by omega⟩ : Fin 8) = r := by
          apply Fin.ext
          dsimp [c]
          omega
        have hsource : sourceIndex h g q c = w.val := by
          simp only [sourceIndex, hc, dite_eq_left]
          rw [hcr]
          exact hr
        right
        left
        refine ⟨c, cutoff c hsource, ?_⟩
        intro s
        have hx := hraw r s
        rw [hr] at hx
        rw [hx]
        simp [basis, ConcreteOrPorts.portBasis, ReaderCofactorBridge.embed, habc, hc, c]
    · let i : Fin m := ⟨w.val - 11, by omega⟩
      have hi : 11 + i.val = w.val := by dsimp [i]; omega
      have hilimit : i.val < limit := by dsimp [i]; omega
      by_cases hih : i = h
      · right
        left
        refine ⟨5, cutoff 5 ?_, ?_⟩
        · simpa [sourceIndex, hih] using hi
        · intro s
          simp only [basis, ConcreteOrPorts.portBasis]
          simpa [hih] using congrArg (fun z => value z s) hi.symm
      · by_cases hig : i = g
        · right
          left
          refine ⟨6, cutoff 6 ?_, ?_⟩
          · simpa [sourceIndex, hig] using hi
          · intro s
            simp only [basis, ConcreteOrPorts.portBasis]
            simpa [hig] using congrArg (fun z => value z s) hi.symm
        · by_cases hiq : i = q
          · right
            left
            refine ⟨7, cutoff 7 ?_, ?_⟩
            · simpa [sourceIndex, hiq] using hi
            · intro s
              simp only [basis, ConcreteOrPorts.portBasis]
              simpa [hiq] using congrArg (fun z => value z s) hi.symm
          · by_cases hand_i : op i = true
            · left
              rcases hand i hilimit hand_i with he | he | hz
              · exact False.elim (hih he)
              · exact False.elim (hig he)
              · intro s
                simpa only [hi] using hz s
            · have hop : op i = false := by
                cases he : op i
                · rfl
                · exact False.elim (hand_i he)
              have hja : a i < w.val := by simpa only [hi] using ha i
              have hjb : b i < w.val := by simpa only [hi] using hb i
              let j : Fin (11 + limit) := ⟨a i, by omega⟩
              let k : Fin (11 + limit) := ⟨b i, by omega⟩
              have hjgood : usable v j.val := by
                constructor
                · intro he
                  exact hiq (hsole i (Or.inl he))
                · by_cases he : 11 ≤ a i
                  · exact Or.inl he
                  · exact Or.inr (hav i (by omega))
              have hkgood : usable v k.val := by
                constructor
                · intro he
                  exact hiq (hsole i (Or.inr he))
                · by_cases he : 11 ≤ b i
                  · exact Or.inl he
                  · exact Or.inr (hbv i (by omega))
              right
              right
              refine ⟨j, k, hja, hjb, hjgood, hkgood, ?_⟩
              intro s
              have hx := hgate i s
              simpa [hop, hi, j, k] using hx
  exact ConcreteOrPorts.causal_final_port
    (fun w : Fin (11 + limit) => value w.val) (fun s : Bool × Fin 32 => s.2)
    (value (11 + h.val)) (value (11 + g.val)) (value (11 + q.val))
    (fun w => usable v w.val) (allowedSources h g q limit) step

end PEqualNP.Outside.L_meta_9033_aux.PhysicalOrPorts

namespace PEqualNP.Outside.L_meta_9033_aux.PhysicalQMateExtraction

open PhysicalOrPorts

theorem raw_retained_value (v : Fin 3) (value : Nat → (Bool × Fin 32) → Bool)
    (hraw : ∀ (i : Fin 8) (s : Bool × Fin 32),
      value (rawIndex i) s = ReaderCofactorBridge.embed v s.1 s.2 i)
    (s : Bool × Fin 32) : value v.val s = s.1 := by
  have hi : rawIndex (ReaderCofactorBridge.abcIndex v) = v.val := by
    simp [rawIndex, ReaderCofactorBridge.abcIndex, v.isLt]
  have hv := hraw (ReaderCofactorBridge.abcIndex v) s
  rw [hi, ReaderCofactorBridge.embed_abc] at hv
  simpa using hv

theorem sole_or_reader_exact_h {m : Nat} (v : Fin 3)
    (a b : Fin m → Nat) (op : Fin m → Bool) (h g q : Fin m)
    (value : Nat → (Bool × Fin 32) → Bool)
    (ha : ∀ i, a i < 11 + i.val) (hb : ∀ i, b i < 11 + i.val)
    (hav : ∀ i, a i < 11 → a i ∈ rawSlots)
    (hbv : ∀ i, b i < 11 → b i ∈ rawSlots)
    (hraw : ∀ (i : Fin 8) (s : Bool × Fin 32),
      value (rawIndex i) s = ReaderCofactorBridge.embed v s.1 s.2 i)
    (hgate : ∀ (i : Fin m) (s : Bool × Fin 32),
      value (11 + i.val) s =
        if op i then (value (a i) s && value (b i) s)
        else (value (a i) s || value (b i) s))
    (hand : ∀ i, i.val < q.val → op i = true →
      i = h ∨ i = g ∨ ∀ s : Bool × Fin 32, value (11 + i.val) s = false)
    (hsole : ∀ i, a i = v.val ∨ b i = v.val → i = q)
    (hopq : op q = false) (haq : a q = v.val)
    (hcore : ∀ i : Fin 5, value (b q) (false, HFirst.unit i) = false)
    (hretained : value (b q) (true, 0) = false)
    (hgsingleton : (∃ i : Fin 5, value (11 + g.val) (false, HFirst.unit i) = true) ∨
      value (11 + g.val) (true, 0) = true)
    (hpositive : ∃ s : Bool × Fin 32, value (b q) s = true) :
    h.val < q.val ∧
      (∀ s : Bool × Fin 32, value (b q) s = value (11 + h.val) s) ∧
      ∀ s : Bool × Fin 32, value (11 + q.val) s = (s.1 || value (11 + h.val) s) := by
  have hbq_ne : b q ≠ v.val := by
    intro he
    have hz := hretained
    rw [he, raw_retained_value v value hraw] at hz
    contradiction
  have hbq_usable : usable v (b q) := by
    refine ⟨hbq_ne, ?_⟩
    by_cases hl : 11 ≤ b q
    · exact Or.inl hl
    · exact Or.inr (hbv q (by omega))
  obtain ⟨support, hallowed, hrepr⟩ :=
    trace_prefix_final_port v q.val (by omega) a b op h g q value
      ha hb hav hbv hraw hgate hand hsole ⟨b q, hb q⟩ hbq_usable
  have hqnot : (7 : Fin 8) ∉ support := by
    intro hmem
    have hbirth := (Finset.mem_filter.mp (hallowed hmem)).2
    simp [sourceIndex] at hbirth
  let hf : Bool → Fin 32 → Bool := fun c x => value (11 + h.val) (c, x)
  let gf : Bool → Fin 32 → Bool := fun c x => value (11 + g.val) (c, x)
  have hmate : ∀ c x, value (b q) (c, x) =
      QMateExtraction.mate (ConcreteOrPorts.supportRawMask support)
        (decide (5 ∈ support)) (decide (6 ∈ support)) hf gf c x := by
    intro c x
    have hr := hrepr (c, x)
    simpa [HFirst.finalSide, QMateExtraction.mate, hqnot, hf, gf] using hr
  have hmate_core : ∀ i : Fin 5,
      QMateExtraction.mate (ConcreteOrPorts.supportRawMask support)
        (decide (5 ∈ support)) (decide (6 ∈ support)) hf gf false (HFirst.unit i) = false := by
    intro i
    rw [← hmate]
    exact hcore i
  have hmate_retained : QMateExtraction.mate (ConcreteOrPorts.supportRawMask support)
      (decide (5 ∈ support)) (decide (6 ∈ support)) hf gf true 0 = false := by
    rw [← hmate]
    exact hretained
  have hmate_positive : ∃ c x, QMateExtraction.mate (ConcreteOrPorts.supportRawMask support)
      (decide (5 ∈ support)) (decide (6 ∈ support)) hf gf c x = true := by
    obtain ⟨⟨c, x⟩, hx⟩ := hpositive
    refine ⟨c, x, ?_⟩
    rw [← hmate]
    exact hx
  obtain ⟨_, _, hhflag, hexact⟩ :=
    QMateExtraction.mate_exact_h (ConcreteOrPorts.supportRawMask support)
      (decide (5 ∈ support)) (decide (6 ∈ support)) hf gf
      hmate_core hmate_retained hgsingleton hmate_positive
  have hhmem : (5 : Fin 8) ∈ support := of_decide_eq_true hhflag
  have hbirth := (Finset.mem_filter.mp (hallowed hhmem)).2
  have hhbefore : h.val < q.val := by
    simpa [sourceIndex] using hbirth
  have hmate_exact : ∀ s : Bool × Fin 32, value (b q) s = value (11 + h.val) s := by
    rintro ⟨c, x⟩
    exact (hmate c x).trans (hexact c x)
  refine ⟨hhbefore, hmate_exact, ?_⟩
  intro s
  calc
    value (11 + q.val) s = (value (a q) s || value (b q) s) := by
      simpa [hopq] using hgate q s
    _ = (s.1 || value (11 + h.val) s) := by
      rw [haq, raw_retained_value v value hraw, hmate_exact]

end PEqualNP.Outside.L_meta_9033_aux.PhysicalQMateExtraction

namespace PEqualNP.Outside.L_meta_9033_aux.GlobalMaskCostTransport

open MaskSignatureTransport
open PackedCofactorBridge

lemma signature5_eq_or : ∀ a b c d e : Bool,
    (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
      (if d then 8 else 0) + (if e then 16 else 0) =
    ((if a then 1 else 0) ||| (if b then 2 else 0) ||| (if c then 4 else 0) |||
      (if d then 8 else 0) ||| (if e then 16 else 0)) := by
  decide +kernel

theorem localMask_of_packed_cofactor (v : Fin 3)
    (truth : (Fin 8 → Bool) → Bool) (packed : Nat)
    (hcofactor : ∀ b x, truth (ReaderCofactorBridge.embed v b x) = packed.testBit x.val)
    (hzero : packed.testBit 0 = false) :
    localMask v truth = BcofactorClassification.singletonMask packed := by
  simpa [localMask, signature6, hcofactor, hzero, HFirst.unit,
    BcofactorClassification.singletonMask] using
    signature5_eq_or (packed.testBit 1) (packed.testBit 2) (packed.testBit 4)
      (packed.testBit 8) (packed.testBit 16)

lemma raw_singletonMask : ∀ p : Fin 32,
    BcofactorClassification.singletonMask (BcofactorClassification.coreUnion p.val 0) = p.val := by
  decide +kernel

lemma upper_singletonMask : BcofactorClassification.singletonMask
    BcofactorClassification.upperTarget = 5 := by decide +kernel

lemma raw_zero_bit (p : Fin 32) :
    (BcofactorClassification.coreUnion p.val 0).testBit 0 = false := by
  exact (rawMask_testBit p 0).trans (HFirst.raw_zero p)

lemma g_zero_bit (p q : Fin 32) : (GFirstModel.gValue p q).testBit 0 = false := by
  simpa [GFirstModel.gValue, HFirst.raw_zero] using rawAnd_testBit p q 0

lemma source_zero_bit (s : Fin 64) (g : Nat) (hzero : g.testBit 0 = false) :
    (BcofactorClassification.coreUnion s.val g).testBit 0 = false := by
  simpa [HFirst.raw_zero, hzero] using coreUnion_testBit s g 0

def requiredLabels : Finset (Fin 7) := {0, 1, 2, 3, 4, 5, 6}

def packedPort (p q : Fin 32) (u w : Fin 64) (a b : Fin 32) (i : Fin 7) : Nat :=
  if i = 0 then BcofactorClassification.coreUnion p.val 0
  else if i = 1 then BcofactorClassification.coreUnion q.val 0
  else if i = 2 then BcofactorClassification.coreUnion u.val (GFirstModel.gValue p q)
  else if i = 3 then BcofactorClassification.coreUnion w.val (GFirstModel.gValue p q)
  else if i = 4 then BcofactorClassification.upperTarget
  else if i = 5 then BcofactorClassification.coreUnion a.val 0
  else BcofactorClassification.coreUnion b.val 0

lemma packedPort_zero_bit (p q : Fin 32) (u w : Fin 64) (a b : Fin 32) (i : Fin 7) :
    (packedPort p q u w a b i).testBit 0 = false := by
  unfold packedPort
  split
  · exact raw_zero_bit p
  split
  · exact raw_zero_bit q
  split
  · exact source_zero_bit u _ (g_zero_bit p q)
  split
  · exact source_zero_bit w _ (g_zero_bit p q)
  split
  · decide +kernel
  split
  · exact raw_zero_bit a
  · exact raw_zero_bit b

theorem global_budget_to_maskCount_of_local_masks
    (v : Fin 3) (p q : Fin 32) (u w : Fin 64) (a b : Fin 32)
    (truth : Fin 7 → (Fin 8 → Bool) → Bool) (exceptional : (Fin 8 → Bool) → Bool)
    (hi : ∀ i, localMask v (truth i) =
      BcofactorClassification.singletonMask (packedPort p q u w a b i))
    (he : localMask v exceptional = BcofactorClassification.singletonMask (GFirstModel.gValue p q))
    (hbudget : ((requiredLabels.image (fun i => globalMask (truth i))) \
      insert (globalMask exceptional) MaskProjection.globalRawAtoms).card ≤ 6) :
    GFirstModel.maskCount p q u w a.val b.val ≤ 6 := by
  have hp := cofactor_signature_budget v truth requiredLabels exceptional 6 hbudget
  simp only [he, hi] at hp
  have hatoms : insert (BcofactorClassification.singletonMask (GFirstModel.gValue p q))
      MaskProjection.localRawAtoms =
      {0, 1, 2, 4, 8, 16, 32, BcofactorClassification.singletonMask (GFirstModel.gValue p q)} := by
    ext z
    simp [MaskProjection.localRawAtoms, or_comm, or_assoc]
  rw [hatoms] at hp
  simpa [requiredLabels, packedPort, raw_singletonMask, upper_singletonMask,
    GFirstModel.maskCount] using hp

theorem global_function_budget_to_maskCount
    (v : Fin 3) (p q : Fin 32) (u w : Fin 64) (a b : Fin 32)
    (truth : Fin 7 → (Fin 8 → Bool) → Bool) (exceptional : (Fin 8 → Bool) → Bool)
    (hports : ∀ i retained x, truth i (ReaderCofactorBridge.embed v retained x) =
      (packedPort p q u w a b i).testBit x.val)
    (hexceptional : ∀ retained x, exceptional (ReaderCofactorBridge.embed v retained x) =
      (GFirstModel.gValue p q).testBit x.val)
    (hbudget : ((requiredLabels.image (fun i => globalMask (truth i))) \
      insert (globalMask exceptional) MaskProjection.globalRawAtoms).card ≤ 6) :
    GFirstModel.maskCount p q u w a.val b.val ≤ 6 := by
  apply global_budget_to_maskCount_of_local_masks v p q u w a b truth exceptional
  · intro i
    exact localMask_of_packed_cofactor v (truth i) _ (hports i)
      (packedPort_zero_bit p q u w a b i)
  · exact localMask_of_packed_cofactor v exceptional _ hexceptional (g_zero_bit p q)
  · exact hbudget

theorem global_cofactor_budget_to_maskCount
    (v : Fin 3) (p q : Fin 32) (u w : Fin 64) (a b : Fin 32)
    (truth : Fin 7 → (Fin 8 → Bool) → Bool) (exceptional : (Fin 8 → Bool) → Bool)
    (hports : ∀ i, i.val < 5 → ∀ retained x,
      truth i (ReaderCofactorBridge.embed v retained x) =
        (packedPort p q u w a b i).testBit x.val)
    (hstarA : localMask v (truth 5) = a.val)
    (hstarB : localMask v (truth 6) = b.val)
    (hexceptional : ∀ retained x, exceptional (ReaderCofactorBridge.embed v retained x) =
      (GFirstModel.gValue p q).testBit x.val)
    (hbudget : ((requiredLabels.image (fun i => globalMask (truth i))) \
      insert (globalMask exceptional) MaskProjection.globalRawAtoms).card ≤ 6) :
    GFirstModel.maskCount p q u w a.val b.val ≤ 6 := by
  apply global_budget_to_maskCount_of_local_masks v p q u w a b truth exceptional
  · intro i
    by_cases hi : i.val < 5
    · exact localMask_of_packed_cofactor v (truth i) _ (hports i hi)
        (packedPort_zero_bit p q u w a b i)
    · have hc : i = 5 ∨ i = 6 := by
        have hiv := i.isLt
        have hival : i.val = 5 ∨ i.val = 6 := by omega
        rcases hival with hv | hv
        · left; exact Fin.ext hv
        · right; exact Fin.ext hv
      rcases hc with rfl | rfl
      · simpa [packedPort, raw_singletonMask] using hstarA
      · simpa [packedPort, raw_singletonMask] using hstarB
  · exact localMask_of_packed_cofactor v exceptional _ hexceptional (g_zero_bit p q)
  · exact hbudget

lemma project_core_mask : ∀ (v : Fin 3) (a : Fin 32),
    MaskProjection.projectNat v (8 * a.val) = a.val := by decide +kernel

lemma localMask_of_core_globalMask (v : Fin 3) (a : Fin 32)
    (truth : (Fin 8 → Bool) → Bool) (hmask : globalMask truth = 8 * a.val) :
    localMask v truth = a.val := by
  rw [localMask_eq_projection, hmask, project_core_mask]

theorem global_cofactor_and_star_budget_to_maskCount
    (v : Fin 3) (p q : Fin 32) (u w : Fin 64) (a b : Fin 32)
    (truth : Fin 7 → (Fin 8 → Bool) → Bool) (exceptional : (Fin 8 → Bool) → Bool)
    (hports : ∀ i, i.val < 5 → ∀ retained x,
      truth i (ReaderCofactorBridge.embed v retained x) =
        (packedPort p q u w a b i).testBit x.val)
    (hstarA : globalMask (truth 5) = 8 * a.val)
    (hstarB : globalMask (truth 6) = 8 * b.val)
    (hexceptional : ∀ retained x, exceptional (ReaderCofactorBridge.embed v retained x) =
      (GFirstModel.gValue p q).testBit x.val)
    (hbudget : ((requiredLabels.image (fun i => globalMask (truth i))) \
      insert (globalMask exceptional) MaskProjection.globalRawAtoms).card ≤ 6) :
    GFirstModel.maskCount p q u w a.val b.val ≤ 6 := by
  exact global_cofactor_budget_to_maskCount v p q u w a b truth exceptional hports
    (localMask_of_core_globalMask v a (truth 5) hstarA)
    (localMask_of_core_globalMask v b (truth 6) hstarB) hexceptional hbudget

end PEqualNP.Outside.L_meta_9033_aux.GlobalMaskCostTransport
