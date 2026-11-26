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

end PEqualNP.Outside.L_meta_9033_aux
