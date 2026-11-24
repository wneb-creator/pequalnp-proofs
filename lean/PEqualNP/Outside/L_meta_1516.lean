import Mathlib
import PEqualNP.Defs

-- The colour-merging proof is adapted from public PR3043, L-meta-1512.
-- This file strengthens its local charge test to two active output rows.
namespace PEqualNP.Outside.L_meta_1516
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

-- The value of wire `w` on input `x`.
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

-- Collapsing one colour loses at most one colour.
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
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          val gates (n + (g : ℕ)) (tau p) = true ∧ val gates (n + (g : ℕ)) (tau p') = true) → g ∈ I) :
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
          exact ⟨hop, hz, p, hp, p', hp', hpp, h1, h2⟩




lemma row_bound : ∀ (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    A ⊆ M →
    (∀ p ∈ A, ∀ v ∈ M, tau p v = true ↔ v = p) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    (∀ p ∈ A, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (tau p)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ p ∈ A, ∃ p' ∈ A, p ≠ p' ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p)) = true ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (tau p')) = true) → g ∈ I) →
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



lemma val_mono {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · simpa only [val_input gs _ w hw] using hxy ⟨w,hw⟩
    by_cases hg : w < n + gs.length
    · have hi : w - n < gs.length := by omega
      have he : n + (w-n) = w := by omega
      rcases (legal gs[w-n] (List.getElem_mem hi)).1 with ha | ho
      · intro h
        have hs := (val_and gs x (w-n) hi ha).mp (by simpa only [he] using h)
        rw [← he]
        apply (val_and gs y (w-n) hi ha).mpr
        intro r hr
        obtain ⟨hlt,hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) hit⟩
      · intro h
        obtain ⟨r,hr,hlt,hit⟩ := (val_or gs x (w-n) hi ho).mp (by simpa only [he] using h)
        rw [← he]
        exact (val_or gs y (w-n) hi ho).mpr ⟨r,hr,hlt,ih r (by omega) hit⟩
    · simp [val_big gs x w (by omega)]

def lines (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma geometry : (∀ t, (lines t).card = 4) ∧
    (∀ t u, t ≠ u → (lines t ∩ lines u).card ≤ 1) ∧
    (∀ t u, t ≠ u → (lines t \ lines u).Nonempty) ∧
    (∀ t v, ∃ s, v ∈ lines s ∧ (lines t \ lines s).Nonempty) := by
  decide +kernel

lemma final_bound :
∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  classical
  intro L hL D hup hd gates o legal computes Lam B hB hsep I hI
  have hLeq : L = lines := funext hL
  subst L
  obtain ⟨hcard,hthin,hdiff,hpoint⟩ := geometry
  let neg (t : Fin 13) (v : Fin 13) : Bool := decide (v ∉ lines t)
  let tau (t p v : Fin 13) : Bool := decide (v = p ∨ v ∈ B t p)
  have low (t : Fin 13) : val gates (o t) (neg t) = false := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg t)) = false
    rw [computes t _ (hd t)]
    simp [neg]
  have high (t : Fin 13) (ht : t ∈ Lam) (p : Fin 13) (hp : p ∈ lines t) :
      val gates (o t) (tau t p) = true := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (tau t p)) = true
    rw [computes t _ (hB t ht p hp).2]
    exact decide_eq_true ⟨p,hp,by simp [tau]⟩
  have spec (t : Fin 13) (ht : t ∈ Lam) (p : Fin 13) (hp : p ∈ lines t)
      (v : Fin 13) (hv : v ∈ lines t) : tau t p v = true ↔ v = p := by
    simp only [tau,decide_eq_true_eq]
    constructor
    · rintro (h|h)
      · exact h
      · have hi := Finset.mem_inter.mpr ⟨h,hv⟩
        rw [(hB t ht p hp).1] at hi
        exact False.elim (Finset.notMem_empty v hi)
    · exact Or.inl
  let pay (t : Fin 13) := Finset.univ.filter (fun g : Fin gates.length =>
    (gates.get g).op = GateOp.or ∧ val gates (13+g.val) (neg t) = false ∧
      ∃ p ∈ lines t, ∃ p' ∈ lines t, p ≠ p' ∧
        val gates (13+g.val) (tau t p) = true ∧ val gates (13+g.val) (tau t p') = true)
  have props (t : Fin 13) (g : Fin gates.length) (hg : g ∈ pay t) :
    (gates.get g).op = GateOp.or ∧ val gates (13+g.val) (neg t) = false ∧
      ∃ p ∈ lines t, ∃ p' ∈ lines t, p ≠ p' ∧
        val gates (13+g.val) (tau t p) = true ∧ val gates (13+g.val) (tau t p') = true :=
    (Finset.mem_filter.mp hg).2
  have many (t : Fin 13) (ht : t ∈ Lam) : 3 ≤ (pay t).card := by
    have hb := row_bound 13 (lines t) (lines t) (tau t) gates (o t) legal
      (Finset.Subset.refl _) (spec t ht) (low t) (high t ht) (pay t)
      (fun g hg => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩)
    rw [hcard t] at hb
    omega
  have pointing (t u : Fin 13) (hne : t ≠ u) (g : Fin gates.length)
      (ht : g ∈ pay t) (hu : g ∈ pay u) :
      ∃ p ∈ lines t \ lines u, (B t p ∩ lines u).Nonempty := by
    obtain ⟨p,hp,p',hp',hpp,hit,hit'⟩ := (props t g ht).2.2
    have out : ∃ p ∈ lines t, p ∉ lines u ∧ val gates (13+g.val) (tau t p) = true := by
      by_cases hpu : p ∈ lines u
      · have hp'u : p' ∉ lines u := by
          intro hp'u
          exact hpp (Finset.card_le_one.mp (hthin t u hne) p
            (Finset.mem_inter.mpr ⟨hp,hpu⟩) p' (Finset.mem_inter.mpr ⟨hp',hp'u⟩))
        exact ⟨p',hp',hp'u,hit'⟩
      · exact ⟨p,hp,hpu,hit⟩
    obtain ⟨r,hr,hru,hit⟩ := out
    refine ⟨r,Finset.mem_sdiff.mpr ⟨hr,hru⟩,?_⟩
    by_contra none
    have le (v : Fin 13) (hv : tau t r v = true) : neg u v = true := by
      apply decide_eq_true
      intro hvu
      rcases of_decide_eq_true hv with e | hb
      · subst v; exact hru hvu
      · exact none ⟨v,Finset.mem_inter.mpr ⟨hb,hvu⟩⟩
    have h := val_mono gates legal (tau t r) (neg u) le (13+g.val) hit
    rw [(props u g hu).2.1] at h
    contradiction
  have dis (t : Fin 13) (ht : t ∈ Lam) (u : Fin 13) (hu : u ∈ Lam) (hne : t ≠ u) :
      Disjoint (pay t) (pay u) := by
    apply Finset.disjoint_left.mpr
    intro g hgt hgu
    exact hsep t ht u hu hne ⟨pointing t u hne g hgt hgu,pointing u t hne.symm g hgu hgt⟩
  let paid := Lam.biUnion pay
  have paidmany : 3 * Lam.card ≤ paid.card := by
    dsimp [paid]
    rw [Finset.card_biUnion dis]
    calc
      3 * Lam.card = ∑ t ∈ Lam, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ t ∈ Lam, (pay t).card := Finset.sum_le_sum many
  have disI : Disjoint paid I := by
    apply Finset.disjoint_left.mpr
    intro g hg hi
    obtain ⟨t,ht,hgt⟩ := Finset.mem_biUnion.mp hg
    have op := (props t g hgt).1
    rw [hI g hi] at op
    contradiction
  have boundI : paid.card + I.card ≤ gates.length := by
    have h := Finset.card_le_univ (paid ∪ I)
    rw [Finset.card_union_of_disjoint disI,Fintype.card_fin] at h
    exact h
  have output_high (t s : Fin 13) (hne : t ≠ s) : val gates (o t) (neg s) = true := by
    obtain ⟨p,hp⟩ := hdiff t s hne
    obtain ⟨hpt,hps⟩ := Finset.mem_sdiff.mp hp
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
    rw [computes t _ (hd s)]
    exact decide_eq_true ⟨p,hpt,decide_eq_true hps⟩
  have bounds (t : Fin 13) : 13 ≤ o t ∧ o t < 13 + gates.length := by
    constructor
    · by_contra! small
      let v : Fin 13 := ⟨o t,small⟩
      obtain ⟨s,hvs,p,hp⟩ := hpoint t v
      have hit : val gates (o t) (neg s) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
        rw [computes t _ (hd s)]
        exact decide_eq_true ⟨p,(Finset.mem_sdiff.mp hp).1,decide_eq_true (Finset.mem_sdiff.mp hp).2⟩
      rw [val_input gates _ _ small] at hit
      exact (of_decide_eq_true hit) hvs
    · have hall : D (fun _ => true) := hup (neg 0) (fun _ => true) (hd 0) (by simp)
      have hit : val gates (o t) (fun _ : Fin 13 => true) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (fun _ : Fin 13 => true)) = true
        rw [computes t _ hall]
        exact decide_eq_true ⟨t,by simp [lines],rfl⟩
      by_contra! big
      rw [val_big gates _ _ big] at hit
      contradiction
  let idx (t : Fin 13) : Fin gates.length := ⟨o t-13,by have := bounds t;omega⟩
  have idxeq (t : Fin 13) : 13+(idx t).val = o t := by have := bounds t;dsimp [idx];omega
  have idxinj : Function.Injective idx := by
    intro t u heq
    by_contra hne
    have eqo : o t = o u := by rw [← idxeq t,← idxeq u,heq]
    have hit := output_high u t (Ne.symm hne)
    rw [← eqo,low t] at hit
    contradiction
  let free := (Finset.univ \ Lam).image idx
  have freecard : free.card = 13 - Lam.card := by
    dsimp [free]
    rw [Finset.card_image_of_injective _ idxinj,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]
  have disfree : Disjoint paid free := by
    apply Finset.disjoint_left.mpr
    intro g hg hf
    obtain ⟨t,ht,hgt⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hf
    have hut : u ≠ t := by intro h;subst u;exact (Finset.mem_sdiff.mp hu).2 ht
    have hit := output_high u t hut
    have zero := (props t (idx u) hgt).2.1
    rw [idxeq u] at zero
    rw [zero] at hit
    contradiction
  have boundfree : paid.card + free.card ≤ gates.length := by
    have h := Finset.card_le_univ (paid ∪ free)
    rw [Finset.card_union_of_disjoint disfree,Fintype.card_fin] at h
    exact h
  rw [freecard] at boundfree
  omega

end PEqualNP.Outside.L_meta_1516

theorem PEqualNP.Outside.L_meta_1516 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length :=
  PEqualNP.Outside.L_meta_1516.final_bound
