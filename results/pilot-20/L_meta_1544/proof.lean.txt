import Mathlib
import PEqualNP.Defs

-- The circuit and colour-counting lemmas follow checked L-meta-1516.
namespace PEqualNP.Outside.L_meta_1544
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
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

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

-- Collapsing one colour loses at most one colour.
lemma merge_card {n : ℕ} (A : Finset (Fin n)) (c : Fin n → Fin n) (x y : Fin n) :
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

lemma two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
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

lemma main (n : ℕ) (M A : Finset (Fin n)) (tau : Fin n → Fin n → Bool)
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

lemma geometry (q N : ℕ) (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ t : Fin N, (L t).card = q + 1)
    (hmeet : ∀ t u : Fin N, t ≠ u → (L t ∩ L u).card = 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) :
    (∀ t u : Fin N, t ≠ u → (L t ∩ L u).card ≤ 1) ∧
    (∀ t u : Fin N, t ≠ u → (L t \ L u).Nonempty) ∧
    (∀ t v : Fin N, ∃ s : Fin N, v ∈ L s ∧ (L t \ L s).Nonempty) := by
  classical
  have hdiff (t u : Fin N) (hne : t ≠ u) : (L t \ L u).Nonempty := by
    by_contra h
    have hs : L t ⊆ L u := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.not_nonempty_iff_eq_empty.mp h)
    have hi : L t ∩ L u = L t := Finset.inter_eq_left.mpr hs
    have hc := hmeet t u hne
    rw [hi, hcard t] at hc
    omega
  have hpos (t : Fin N) : (L t).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard t]
    omega
  have hout (t : Fin N) : ∃ u : Fin N, u ∉ L t := by
    have hlt : (L t).card < N := by
      rw [hcard t, hN]
      nlinarith
    by_contra! h
    have he : L t = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [he, Finset.card_univ, Fintype.card_fin] at hlt
    omega
  refine ⟨fun t u h => le_of_eq (hmeet t u h), hdiff, ?_⟩
  intro t v
  by_cases hv : v ∈ L t
  · obtain ⟨u, hu⟩ := hout t
    have hne : v ≠ u := by
      intro e
      subst u
      exact hu hv
    obtain ⟨s, hvs, hus⟩ := hpair v u hne
    have hts : t ≠ s := by
      intro e
      subst s
      exact hu hus
    exact ⟨s, hvs, hdiff t s hts⟩
  · obtain ⟨p, hp⟩ := hpos t
    have hne : v ≠ p := by
      intro e
      subst p
      exact hv hp
    obtain ⟨s, hvs, _⟩ := hpair v p hne
    have hts : t ≠ s := by
      intro e
      subst s
      exact hv hvs
    exact ⟨s, hvs, hdiff t s hts⟩

end PEqualNP.Outside.L_meta_1544

open PEqualNP.Outside.L_meta_1544 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1544 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ D : (Fin N → Bool) → Prop,
    (∀ x y : Fin N → Bool, D x → (∀ v : Fin N, x v = true → y v = true) → D y) →
    (∀ t : Fin N, D (fun v : Fin N => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), D x → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v : Fin N => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧ (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      q * Lam.card + max (N - Lam.card) I.card ≤ gates.length := by
  classical
  intro q N L hq hN hcard hmeet hpair D hup hd gates o legal computes Lam B hB hsep I hI
  obtain ⟨hthin,hdiff,hpoint⟩ := geometry q N L hq hN hcard hmeet hpair
  let neg (t : Fin N) (v : Fin N) : Bool := decide (v ∉ L t)
  let tau (t p v : Fin N) : Bool := decide (v = p ∨ v ∈ B t p)
  have low (t : Fin N) : val gates (o t) (neg t) = false := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg t)) = false
    rw [computes t _ (hd t)]
    simp [neg]
  have high (t : Fin N) (ht : t ∈ Lam) (p : Fin N) (hp : p ∈ L t) :
      val gates (o t) (tau t p) = true := by
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (tau t p)) = true
    rw [computes t _ (hB t ht p hp).2]
    exact decide_eq_true ⟨p,hp,by simp [tau]⟩
  have spec (t : Fin N) (ht : t ∈ Lam) (p : Fin N) (hp : p ∈ L t)
      (v : Fin N) (hv : v ∈ L t) : tau t p v = true ↔ v = p := by
    simp only [tau,decide_eq_true_eq]
    constructor
    · rintro (h|h)
      · exact h
      · have hi := Finset.mem_inter.mpr ⟨h,hv⟩
        rw [(hB t ht p hp).1] at hi
        exact False.elim (Finset.notMem_empty v hi)
    · exact Or.inl
  let pay (t : Fin N) := Finset.univ.filter (fun g : Fin gates.length =>
    (gates.get g).op = GateOp.or ∧ val gates (N+g.val) (neg t) = false ∧
      ∃ p ∈ L t, ∃ p' ∈ L t, p ≠ p' ∧
        val gates (N+g.val) (tau t p) = true ∧ val gates (N+g.val) (tau t p') = true)
  have props (t : Fin N) (g : Fin gates.length) (hg : g ∈ pay t) :
    (gates.get g).op = GateOp.or ∧ val gates (N+g.val) (neg t) = false ∧
      ∃ p ∈ L t, ∃ p' ∈ L t, p ≠ p' ∧
        val gates (N+g.val) (tau t p) = true ∧ val gates (N+g.val) (tau t p') = true :=
    (Finset.mem_filter.mp hg).2
  have many (t : Fin N) (ht : t ∈ Lam) : q ≤ (pay t).card := by
    have hb := row_bound N (L t) (L t) (tau t) gates (o t) legal
      (Finset.Subset.refl _) (spec t ht) (low t) (high t ht) (pay t)
      (fun g hg => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩)
    rw [hcard t] at hb
    omega
  have pointing (t u : Fin N) (hne : t ≠ u) (g : Fin gates.length)
      (ht : g ∈ pay t) (hu : g ∈ pay u) :
      ∃ p ∈ L t \ L u, (B t p ∩ L u).Nonempty := by
    obtain ⟨p,hp,p',hp',hpp,hit,hit'⟩ := (props t g ht).2.2
    have out : ∃ p ∈ L t, p ∉ L u ∧ val gates (N+g.val) (tau t p) = true := by
      by_cases hpu : p ∈ L u
      · have hp'u : p' ∉ L u := by
          intro hp'u
          exact hpp (Finset.card_le_one.mp (hthin t u hne) p
            (Finset.mem_inter.mpr ⟨hp,hpu⟩) p' (Finset.mem_inter.mpr ⟨hp',hp'u⟩))
        exact ⟨p',hp',hp'u,hit'⟩
      · exact ⟨p,hp,hpu,hit⟩
    obtain ⟨r,hr,hru,hit⟩ := out
    refine ⟨r,Finset.mem_sdiff.mpr ⟨hr,hru⟩,?_⟩
    by_contra none
    have le (v : Fin N) (hv : tau t r v = true) : neg u v = true := by
      apply decide_eq_true
      intro hvu
      rcases of_decide_eq_true hv with e | hb
      · subst v; exact hru hvu
      · exact none ⟨v,Finset.mem_inter.mpr ⟨hb,hvu⟩⟩
    have h := val_mono gates legal (tau t r) (neg u) le (N+g.val) hit
    rw [(props u g hu).2.1] at h
    contradiction
  have dis (t : Fin N) (ht : t ∈ Lam) (u : Fin N) (hu : u ∈ Lam) (hne : t ≠ u) :
      Disjoint (pay t) (pay u) := by
    apply Finset.disjoint_left.mpr
    intro g hgt hgu
    exact hsep t ht u hu hne ⟨pointing t u hne g hgt hgu,pointing u t hne.symm g hgu hgt⟩
  let paid := Lam.biUnion pay
  have paidmany : q * Lam.card ≤ paid.card := by
    dsimp [paid]
    rw [Finset.card_biUnion dis]
    calc
      q * Lam.card = ∑ t ∈ Lam, q := by simp [Nat.mul_comm]
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
  have output_high (t s : Fin N) (hne : t ≠ s) : val gates (o t) (neg s) = true := by
    obtain ⟨p,hp⟩ := hdiff t s hne
    obtain ⟨hpt,hps⟩ := Finset.mem_sdiff.mp hp
    change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
    rw [computes t _ (hd s)]
    exact decide_eq_true ⟨p,hpt,decide_eq_true hps⟩
  have bounds (t : Fin N) : N ≤ o t ∧ o t < N + gates.length := by
    constructor
    · by_contra! small
      let v : Fin N := ⟨o t,small⟩
      obtain ⟨s,hvs,p,hp⟩ := hpoint t v
      have hit : val gates (o t) (neg s) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (neg s)) = true
        rw [computes t _ (hd s)]
        exact decide_eq_true ⟨p,(Finset.mem_sdiff.mp hp).1,decide_eq_true (Finset.mem_sdiff.mp hp).2⟩
      rw [val_input gates _ _ small] at hit
      exact (of_decide_eq_true hit) hvs
    · have hall : D (fun _ => true) := hup (neg t) (fun _ => true) (hd t) (by simp)
      have hit : val gates (o t) (fun _ : Fin N => true) = true := by
        change Circuit.eval ⟨gates,o t⟩ (List.ofFn (fun _ : Fin N => true)) = true
        rw [computes t _ hall]
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (L t).card by rw [hcard t]; omega)
        exact decide_eq_true ⟨p,hp,rfl⟩
      by_contra! big
      rw [val_big gates _ _ big] at hit
      contradiction
  let idx (t : Fin N) : Fin gates.length := ⟨o t-N,by have := bounds t;omega⟩
  have idxeq (t : Fin N) : N+(idx t).val = o t := by have := bounds t;dsimp [idx];omega
  have idxinj : Function.Injective idx := by
    intro t u heq
    by_contra hne
    have eqo : o t = o u := by rw [← idxeq t,← idxeq u,heq]
    have hit := output_high u t (Ne.symm hne)
    rw [← eqo,low t] at hit
    contradiction
  let free := (Finset.univ \ Lam).image idx
  have freecard : free.card = N - Lam.card := by
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
