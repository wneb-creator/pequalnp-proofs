import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1512
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

/-- Collapsing one colour loses at most one colour. -/
theorem merge_card {n : ℕ} (A : Finset (Fin n)) (c : Fin n → Fin n) (x y : Fin n) :
    (A.image c).card ≤ (A.image fun p => if c p = y then x else c p).card + 1 := by
  classical
  have h1 : ((A.image c).erase y) ⊆ A.image fun p => if c p = y then x else c p := by
    intro v hv
    rw [Finset.mem_erase] at hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv.2
    exact Finset.mem_image.2 ⟨p, hp, by simp [hv.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := A.image c) (a := y)
  omega

theorem two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab

theorem main (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hAM : A ⊆ M) (htau : ∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
        val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ M)) = false ∧
        ∃ (w1 w2 : ℕ), (gates.get g).inputs = [w1, w2] ∧ ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates w1 (tau p) = true ∧ val gates w2 (tau p') = true) → g ∈ I) :
    ∀ k, k ≤ gates.length → ∃ c : Fin n → Fin n,
      A.card ≤ (A.image c).card + (I.filter fun g => g.val < k).card ∧
      ∀ w < n + k, val gates w (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
          c p = c p' := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro w hw hz p hp p' hp' h1 h2
    have hw' : w < n := by omega
    rw [val_input gates _ w hw'] at hz h1 h2
    have hM : (⟨w, hw'⟩ : Fin n) ∈ M := by simpa using hz
    have e1 := (htau p hp _ hM).1 h1
    have e2 := (htau p' hp' _ hM).1 h2
    exact e1.symm.trans e2
  | succ k ih =>
    intro hk
    have hk' : k < gates.length := hk
    obtain ⟨c, hcard, hc⟩ := ih (Nat.le_of_lt hk')
    have hmono : (I.filter fun g => g.val < k).card ≤ (I.filter fun g => g.val < k + 1).card :=
      Finset.card_le_card (fun g hg => by
        rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩)
    -- the old colouring works whenever the new wire needs nothing new
    have keep : (val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
        ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true → val gates (n + k) (tau p') = true →
          c p = c p') →
        ∃ c : Fin n → Fin n,
          A.card ≤ (A.image c).card + (I.filter fun g => g.val < k + 1).card ∧
          ∀ w < n + (k + 1), val gates w (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates w (tau p) = true → val gates w (tau p') = true →
              c p = c p' := by
      intro hnew
      refine ⟨c, by omega, ?_⟩
      intro w hw hz p hp p' hp' h1 h2
      by_cases hwk : w = n + k
      · subst hwk; exact hnew hz p hp p' hp' h1 h2
      · exact hc w (by omega) hz p hp p' hp' h1 h2
    have hlegk := hleg gates[k] (List.getElem_mem hk')
    rcases hlegk.1 with hop | hop
    · -- an AND gate false off M has an input false off M
      apply keep
      intro hz p hp p' hp' h1 h2
      have hz' : ¬ ∀ i ∈ gates[k].inputs, i < n + k ∧
          val gates i (fun v : Fin n => decide (v ∉ M)) = true := by
        intro h; rw [(val_and gates _ k hk' hop).2 h] at hz; exact absurd hz (by simp)
      push_neg at hz'
      obtain ⟨i, hi, hiz⟩ := hz'
      have a1 := (val_and gates (tau p) k hk' hop).1 h1 i hi
      have a2 := (val_and gates (tau p') k hk' hop).1 h2 i hi
      have hzi : val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
        simpa using hiz a1.1
      exact hc i a1.1 hzi p hp p' hp' a1.2 a2.2
    · -- an OR gate
      by_cases hkI : (⟨k, hk'⟩ : Fin gates.length) ∈ I
      · -- a gate of `I`: merge two colours if needed
        by_cases hsame : val gates (n + k) (fun v : Fin n => decide (v ∉ M)) = false →
            ∀ p ∈ A, ∀ p' ∈ A, val gates (n + k) (tau p) = true →
              val gates (n + k) (tau p') = true → c p = c p'
        · exact keep hsame
        · push_neg at hsame
          obtain ⟨hz, a, ha, b, hb, hva, hvb, hne⟩ := hsame
          obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau a) k hk' hop).1 hva
          obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau b) k hk' hop).1 hvb
          have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
              val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
            intro i hi hlt
            by_contra hcon
            have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
            rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
            exact absurd hz (by simp)
          have hiab : ia ≠ ib := by
            intro h; subst h
            exact hne (hc ia hia1 (hzall ia hia hia1) a ha b hb hia2 hib2)
          have hcount : (I.filter fun g => g.val < k).card + 1 ≤
              (I.filter fun g => g.val < k + 1).card := by
            have hsub : insert (⟨k, hk'⟩ : Fin gates.length) (I.filter fun g => g.val < k) ⊆
                I.filter fun g => g.val < k + 1 := by
              intro g hg
              rw [Finset.mem_insert] at hg
              rcases hg with rfl | hg
              · exact Finset.mem_filter.2 ⟨hkI, by simp⟩
              · rw [Finset.mem_filter] at hg ⊢; exact ⟨hg.1, by omega⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp)] at this
            exact this
          refine ⟨fun p => if c p = c b then c a else c p, ?_, ?_⟩
          · have := merge_card A c (c a) (c b)
            omega
          · intro w hw hzw p hp p' hp' h1 h2
            by_cases hwk : w = n + k
            · subst hwk
              have col : ∀ q ∈ A, val gates (n + k) (tau q) = true → c q = c a ∨ c q = c b := by
                intro q hq hvq
                obtain ⟨iq, hiq, hiq1, hiq2⟩ := (val_or gates (tau q) k hk' hop).1 hvq
                rcases two_list _ hlegk.2 ia ib hia hib hiab with hl | hl
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                · rw [hl] at hiq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hiq
                  rcases hiq with rfl | rfl
                  · exact Or.inr (hc _ hiq1 (hzall _ hib hiq1) q hq b hb hiq2 hib2)
                  · exact Or.inl (hc _ hiq1 (hzall _ hia hiq1) q hq a ha hiq2 hia2)
              have fin : ∀ q ∈ A, val gates (n + k) (tau q) = true →
                  (if c q = c b then c a else c q) = c a := by
                intro q hq hvq
                rcases col q hq hvq with h | h
                · rw [h]; split_ifs <;> rfl
                · rw [if_pos h]
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [fin p hp h1, fin p' hp' h2]
            · have := hc w (by omega) hzw p hp p' hp' h1 h2
              show (if c p = c b then c a else c p) = (if c p' = c b then c a else c p')
              rw [this]
      · -- not in `I`: the gate does not join two different points
        apply keep
        intro hz p hp p' hp' h1 h2
        obtain ⟨ia, hia, hia1, hia2⟩ := (val_or gates (tau p) k hk' hop).1 h1
        obtain ⟨ib, hib, hib1, hib2⟩ := (val_or gates (tau p') k hk' hop).1 h2
        have hzall : ∀ i ∈ gates[k].inputs, i < n + k →
            val gates i (fun v : Fin n => decide (v ∉ M)) = false := by
          intro i hi hlt
          by_contra hcon
          have : val gates i (fun v : Fin n => decide (v ∉ M)) = true := by simpa using hcon
          rw [(val_or gates _ k hk' hop).2 ⟨i, hi, hlt, this⟩] at hz
          exact absurd hz (by simp)
        by_cases hiab : ia = ib
        · subst hiab
          exact hc ia hia1 (hzall ia hia hia1) p hp p' hp' hia2 hib2
        · by_contra hcne
          have hpp : p ≠ p' := fun h => hcne (by rw [h])
          apply hkI
          apply hI ⟨k, hk'⟩
          refine ⟨hop, hz, ?_⟩
          rcases two_list _ hlegk.2 ia ib hia hib hiab with hl | hl
          · exact ⟨ia, ib, hl, p, hp, p', hp', hpp, hia2, hib2⟩
          · exact ⟨ib, ia, hl, p', hp', p, hp, Ne.symm hpp, hib2, hia2⟩

end PEqualNP.Outside.L_meta_1512

open PEqualNP.Outside.L_meta_1512 in
theorem PEqualNP.Outside.L_meta_1512 : ∀ (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    A ⊆ M →
    (∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    (∀ p ∈ A, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (tau p)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ (w1 w2 : ℕ), (gates.get g).inputs = [w1, w2] ∧ ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (tau p)) = true ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (tau p')) = true) → g ∈ I) →
      A.card ≤ 1 + I.card := by
  classical
  intro n M A tau gates o hleg hAM htau hout htrue I hI
  obtain ⟨c, hcard, hc⟩ := main n M A tau gates hleg hAM htau I hI gates.length le_rfl
  have hJ : (I.filter fun g => g.val < gates.length).card ≤ I.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rcases A.eq_empty_or_nonempty with hA | ⟨p0, hp0⟩
  · subst hA; simp
  · have ho : o < n + gates.length := by
      by_contra hcon
      have := htrue p0 hp0
      rw [eval_eq] at this
      have h2 := val_big gates (tau p0) o (by omega)
      rw [val] at h2
      rw [h2] at this
      exact absurd this (by simp)
    have hconst : ∀ p ∈ A, c p = c p0 := fun p hp =>
      hc o ho hout p hp p0 hp0 (htrue p hp) (htrue p0 hp0)
    have himg : (A.image c).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [hconst p hp, hconst q hq]
    omega
