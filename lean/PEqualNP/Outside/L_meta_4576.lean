import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4576
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def I (p l : Fin 13) : Bool := decide (p = l) || decide (p = l + 1) || decide (p = l + 3) || decide (p = l + 9)

def L13 : List (Fin 13) := List.finRange 13

lemma gB : L13.all (fun a => L13.all fun b => L13.all fun c => L13.all fun r =>
  (decide (r = a) || decide (r = b) || decide (r = c)) || L13.any fun l => I r l && !I a l && !I b l && !I c l) = true := by decide +kernel

lemma gD : L13.all (fun a => L13.all fun b => L13.all fun c => L13.all fun s =>
  (L13.any fun l => I a l && I b l && I c l) || L13.any fun l => !I s l && !I a l && !I b l && !I c l) = true := by decide +kernel

lemma gE : L13.all (fun p => L13.all fun q => L13.all fun l => L13.all fun m =>
  (I p l || I p m || I q l || I q m) || L13.any fun r => !I r l && !I r m && !decide (r = p) && (decide (p = q) || !L13.any fun k => I p k && I q k && I r k)) = true := by decide +kernel

lemma gP : L13.all (fun l => L13.all fun m => L13.any fun p => !I p l && !I p m) = true := by decide +kernel

lemma gL : L13.all (fun p => L13.all fun q => L13.any fun l => !I p l && !I q l) = true := by decide +kernel

lemma pB (a b c r : Fin 13) (h : r ≠ a ∧ r ≠ b ∧ r ≠ c) : ∃ l, I r l = true ∧ I a l = false ∧ I b l = false ∧ I c l = false := by
  have := gB
  simp only [L13, List.all_eq_true, List.mem_finRange, forall_const, List.any_eq_true, true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
  have h0 := this a b c r
  clear this
  rcases h0 with h1 | ⟨l, hl⟩
  · rcases h1 with (h1 | h1) | h1
    · exact absurd h1 h.1
    · exact absurd h1 h.2.1
    · exact absurd h1 h.2.2
  · exact ⟨l, hl.1.1.1, hl.1.1.2, hl.1.2, hl.2⟩

lemma pD (a b c s : Fin 13) (h : ¬ ∃ l, I a l = true ∧ I b l = true ∧ I c l = true) : ∃ l, I s l = false ∧ I a l = false ∧ I b l = false ∧ I c l = false := by
  have := gD
  simp only [L13, List.all_eq_true, List.mem_finRange, forall_const, List.any_eq_true, true_and, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
  have h0 := this a b c s
  clear this
  rcases h0 with ⟨l, hl⟩ | ⟨l, hl⟩
  · exact absurd ⟨l, hl.1.1, hl.1.2, hl.2⟩ h
  · exact ⟨l, hl.1.1.1, hl.1.1.2, hl.1.2, hl.2⟩

lemma pE (p q l m : Fin 13) (h : I p l = false ∧ I p m = false ∧ I q l = false ∧ I q m = false) : ∃ r, I r l = false ∧ I r m = false ∧ r ≠ p ∧ (p = q ∨ ¬ ∃ k, I p k = true ∧ I q k = true ∧ I r k = true) := by
  have := gE
  simp only [L13, List.all_eq_true, List.mem_finRange, forall_const, List.any_eq_true, true_and, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
  have h0 := this p q l m
  clear this
  rcases h0 with h1 | ⟨r, hr⟩
  · rcases h with ⟨h2, h3, h4, h5⟩
    rw [h2, h3, h4, h5] at h1
    simp at h1
  · refine ⟨r, hr.1.1.1, hr.1.1.2, hr.1.2, ?_⟩
    rcases hr.2 with h1 | h1
    · exact Or.inl h1
    · right
      rintro ⟨k, hk⟩
      rw [List.any_eq_false] at h1
      exact h1 k (List.mem_finRange k) (by simp [hk.1, hk.2.1, hk.2.2])

lemma pP (l m : Fin 13) : ∃ p, I p l = false ∧ I p m = false := by
  have := gP
  simp only [L13, List.all_eq_true, List.mem_finRange, forall_const, List.any_eq_true, true_and, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this l m

lemma pL (p q : Fin 13) : ∃ l, I p l = false ∧ I q l = false := by
  have := gL
  simp only [L13, List.all_eq_true, List.mem_finRange, forall_const, List.any_eq_true, true_and, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this p q

lemma pT (p q l m : Fin 13) (h : I p l = false ∧ I p m = false ∧ I q l = false ∧ I q m = false) : ∃ a b c, (p = a ∨ p = b ∨ p = c) ∧ (q = a ∨ q = b ∨ q = c) ∧ (¬ ∃ k, I a k = true ∧ I b k = true ∧ I c k = true) ∧ I a l = false ∧ I b l = false ∧ I c l = false ∧ I a m = false ∧ I b m = false ∧ I c m = false := by
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := pE p q l m h
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := pE p r l m ⟨h.1, h.2.1, hr1, hr2⟩
    rcases hs4 with hs4 | hs4
    · exact absurd hs4.symm hr3
    · exact ⟨p, r, s, Or.inl rfl, Or.inl rfl, hs4, h.1, hr1, hs1, h.2.1, hr2, hs2⟩
  · rcases hr4 with hr4 | hr4
    · exact absurd hr4 hpq
    · exact ⟨p, q, r, Or.inl rfl, Or.inr (Or.inl rfl), hr4, h.1, h.2.2.1, hr1, h.2.1, h.2.2.2, hr2⟩

lemma pick {α : Type} [DecidableEq α] (s : Finset α) (h : s.card ≤ 2) (P : α → Prop) (hs : ∀ x ∈ s, P x) (hex : ∃ x, P x) : ∃ a b, P a ∧ P b ∧ s ⊆ {a, b} := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ := hex
    exact ⟨x, x, hx, hx, by simp⟩
  · have hc : (s.erase x).card ≤ 1 := by
      rw [Finset.card_erase_of_mem hx]
      omega
    rcases (s.erase x).eq_empty_or_nonempty with he | ⟨y, hy⟩
    · refine ⟨x, x, hs x hx, hs x hx, ?_⟩
      intro z hz
      by_cases hzx : z = x
      · simp [hzx]
      · have : z ∈ s.erase x := Finset.mem_erase.mpr ⟨hzx, hz⟩
        rw [he] at this
        simp at this
    · refine ⟨x, y, hs x hx, hs y (Finset.mem_of_mem_erase hy), ?_⟩
      intro z hz
      by_cases hzx : z = x
      · simp [hzx]
      · have hz2 : z ∈ s.erase x := Finset.mem_erase.mpr ⟨hzx, hz⟩
        have := Finset.card_le_one.mp hc z hz2 y hy
        simp [this]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def DG (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) ((List.range n).map fun i => if i ∈ marked then 1 else 0)

def inp (n : ℕ) (z : ℕ → Bool) : List Bool := (List.range n).map z

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma DG_snoc (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (g : Gate) : DG n marked (gs ++ [g]) = DG n marked gs ++ [g.lineDegree (DG n marked gs)] := by
  simp [DG, List.foldl_append]

lemma W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma DG_len (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : (DG n marked gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [DG]
  | append_singleton gs g ih => rw [DG_snoc]; simp [ih]; omega

def Cert (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (k : ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  ∃ S : Finset ℕ, S.card ≤ k ∧ (∀ i ∈ S, i < n ∧ i ∈ marked ∧ z i = true) ∧
    ∀ z' : ℕ → Bool, (∀ i ∈ S, z' i = true) → (∀ i, i < n → i ∉ marked → z i = true → z' i = true) → P z'

lemma Cert.mono {n : ℕ} {marked : Finset ℕ} {z : ℕ → Bool} {k k' : ℕ} {P Q : (ℕ → Bool) → Prop} (h : Cert n marked z k P) (hk : k ≤ k') (hPQ : ∀ z', P z' → Q z') : Cert n marked z k' Q := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1.trans hk, h2, fun z' a b => hPQ z' (h3 z' a b)⟩

lemma Cert.and {n : ℕ} {marked : Finset ℕ} {z : ℕ → Bool} {k k' : ℕ} {P Q : (ℕ → Bool) → Prop} (h : Cert n marked z k P) (h' : Cert n marked z k' Q) : Cert n marked z (k + k') (fun z' => P z' ∧ Q z') := by
  obtain ⟨S, h1, h2, h3⟩ := h
  obtain ⟨T, g1, g2, g3⟩ := h'
  refine ⟨S ∪ T, (Finset.card_union_le S T).trans (by omega), ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h2 i hi
    · exact g2 i hi
  · intro z' a b
    exact ⟨h3 z' (fun i hi => a i (Finset.mem_union_left _ hi)) b, g3 z' (fun i hi => a i (Finset.mem_union_right _ hi)) b⟩

lemma Cert.true (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) : Cert n marked z 0 (fun _ => True) :=
  ⟨∅, by simp, by simp, fun _ _ _ => trivial⟩

lemma certAll (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (d : ℕ → ℕ) (R : ℕ → (ℕ → Bool) → Prop) (is : List ℕ) (h : ∀ i ∈ is, Cert n marked z (d i) (R i)) : Cert n marked z (is.map d).sum (fun z' => ∀ i ∈ is, R i z') := by
  induction is with
  | nil => exact (Cert.true n marked z).mono (by simp) (by simp)
  | cons a is ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun i hi => h i (by simp [hi]))
    exact (h1.and h2).mono (by simp) (by
      intro z' hz i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hz.1
      · exact hz.2 i hi)

lemma le_foldr_max (d : ℕ → ℕ) (is : List ℕ) (i : ℕ) (hi : i ∈ is) : d i ≤ (is.map d).foldr max 0 := by
  induction is with
  | nil => simp at hi
  | cons a is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · have := ih hi
      simp only [List.map_cons, List.foldr_cons]
      omega

lemma key (n : ℕ) (marked : Finset ℕ) (z : ℕ → Bool) (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : ∀ t, (W gs (inp n z)).getD t false = true → Cert n marked z ((DG n marked gs).getD t 0) (fun z' => (W gs (inp n z')).getD t false = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    have htn : t < n := by
      by_contra hc
      simp [W, inp, List.getD_eq_getElem?_getD, List.getElem?_eq_none (l := (List.range n).map z) (i := t) (by simp; omega)] at ht
    have hz : z t = true := by
      simpa [W, inp, List.getD_eq_getElem?_getD, htn] using ht
    by_cases hmk : t ∈ marked
    · refine ⟨{t}, ?_, ?_, ?_⟩
      · simp [DG, List.getD_eq_getElem?_getD, htn, hmk]
      · simp [htn, hmk, hz]
      · intro z' a _
        simpa [W, inp, List.getD_eq_getElem?_getD, htn] using a t (by simp)
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro z' _ b
      simpa [W, inp, List.getD_eq_getElem?_getD, htn] using b t htn hmk hz
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : ∀ z'', (W gs (inp n z'')).length = n + gs.length := by
      intro z''
      rw [W_len]
      simp [inp]
    have hdl := DG_len n marked gs
    rcases Nat.lt_trichotomy t (n + gs.length) with hlt | heq | hgt
    · have e1 : ∀ z'', (W (gs ++ [g]) (inp n z'')).getD t false = (W gs (inp n z'')).getD t false := by
        intro z''
        rw [W_snoc, List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      have e2 : (DG n marked (gs ++ [g])).getD t 0 = (DG n marked gs).getD t 0 := by
        rw [DG_snoc, List.getD_append _ _ _ _ (by rw [hdl]; exact hlt)]
      rw [e1] at ht
      rw [e2]
      exact (ih' t ht).mono le_rfl (fun z' h => by rw [e1]; exact h)
    · subst heq
      have e1 : ∀ z'', (W (gs ++ [g]) (inp n z'')).getD (n + gs.length) false = g.op.eval (g.inputs.map fun i => (W gs (inp n z'')).getD i false) := by
        intro z''
        rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [hlen])]
        simp [hlen]
      have e2 : (DG n marked (gs ++ [g])).getD (n + gs.length) 0 = g.lineDegree (DG n marked gs) := by
        rw [DG_snoc, List.getD_append_right _ _ _ _ (by rw [hdl])]
        simp [hdl]
      rw [e1] at ht
      rw [e2]
      rcases hm g (by simp) with hop | hop
      · rw [hop] at ht
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at ht
        have hc := certAll n marked z (fun i => (DG n marked gs).getD i 0) (fun i z' => (W gs (inp n z')).getD i false = true) g.inputs (fun i hi => ih' i (ht i hi))
        refine hc.mono ?_ ?_
        · unfold Gate.lineDegree
          rw [if_pos hop]
        · intro z' hz
          rw [e1, hop]
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
          exact hz
      · rw [hop] at ht
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at ht
        obtain ⟨i, hi, hti⟩ := ht
        refine (ih' i hti).mono ?_ ?_
        · unfold Gate.lineDegree
          rw [if_neg (by rw [hop]; intro h; cases h)]
          exact le_foldr_max (fun i => (DG n marked gs).getD i 0) g.inputs i hi
        · intro z' hz
          rw [e1, hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          exact ⟨i, hi, hz⟩
    · exfalso
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_len]; simp [inp]; omega)] at ht
      simp at ht

def zf (X Y : Finset (Fin 13)) : ℕ → Bool := fun i =>
  if h : i < 13 then decide ((⟨i, h⟩ : Fin 13) ∈ X) else if h2 : i - 13 < 13 then decide ((⟨i - 13, h2⟩ : Fin 13) ∈ Y) else false

lemma ofFn_zf (X Y : Finset (Fin 13)) : (List.ofFn fun x5 : Fin 26 => Fin.addCases (fun x6 : Fin 13 => decide (x6 ∈ X)) (fun x6 : Fin 13 => decide (x6 ∈ Y)) x5) = inp 26 (zf X Y) := by
  apply List.ext_getElem
  · simp [inp]
  · intro i h1 h2
    have hi : i < 26 := by simpa using h1
    simp only [List.getElem_ofFn, inp, List.getElem_map, List.getElem_range, zf]
    by_cases h : i < 13
    · rw [dif_pos h]
      have : (⟨i, hi⟩ : Fin 26) = Fin.castAdd 13 (⟨i, h⟩ : Fin 13) := rfl
      rw [this, Fin.addCases_left]
    · rw [dif_neg h, dif_pos (by omega : i - 13 < 13)]
      have : (⟨i, hi⟩ : Fin 26) = Fin.natAdd 13 (⟨i - 13, by omega⟩ : Fin 13) := by
        ext
        simp
        omega
      rw [this, Fin.addCases_right]

lemma cf_eq (C : Circuit) (X Y : Finset (Fin 13)) : circuitFun 26 C (fun x5 : Fin 26 => Fin.addCases (fun x6 : Fin 13 => decide (x6 ∈ X)) (fun x6 : Fin 13 => decide (x6 ∈ Y)) x5) = (W C.gates (inp 26 (zf X Y))).getD C.output false := by
  rw [← ofFn_zf]
  rfl

lemma Inc_iff (p l : Fin 13) : (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔ I p l = true := by
  simp [I, or_assoc]

lemma main (C : Circuit) (hM : Monotone2 C) (hd1 : HasLineDegree 26 (Finset.range 13) C 2) (hd2 : HasLineDegree 26 (Finset.Ico 13 26) C 2) (X Y : Finset (Fin 13)) (hT : (W C.gates (inp 26 (zf X Y))).getD C.output false = true) (hno : ∀ p ∈ X, ∀ l ∈ Y, I p l = false) : ∃ a b c : Fin 13, (¬ ∃ k, I a k = true ∧ I b k = true ∧ I c k = true) ∧ ∀ Y' : Finset (Fin 13), (∀ l, I a l = false → I b l = false → I c l = false → l ∈ Y') → (W C.gates (inp 26 (zf {a, b, c} Y'))).getD C.output false = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  obtain ⟨S1, hS1c, hS1, hS1z⟩ := key 26 (Finset.Ico 13 26) (zf X Y) C.gates hm C.output hT
  have hS1c' : S1.card ≤ 2 := hS1c.trans hd2
  let Y0 : Finset (Fin 13) := Finset.univ.filter (fun l => 13 + l.val ∈ S1)
  have hY0c : Y0.card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun l : Fin 13 => 13 + l.val) ?_ ?_) hS1c'
    · intro l hl
      simpa [Y0] using hl
    · intro a _ b _ hab
      apply Fin.ext
      simpa using hab
  have hY0Y : ∀ l ∈ Y0, l ∈ Y := by
    intro l hl
    have h1 : 13 + l.val ∈ S1 := by simpa [Y0] using hl
    have h2 := (hS1 _ h1).2.2
    have h3 : ¬ (13 + l.val < 13) := by omega
    have h4 : 13 + l.val - 13 < 13 := by omega
    simp only [zf, dif_neg h3, dif_pos h4, decide_eq_true_eq] at h2
    have : (⟨13 + l.val - 13, h4⟩ : Fin 13) = l := by
      apply Fin.ext
      simp
    rwa [this] at h2
  have hT1 : (W C.gates (inp 26 (zf X Y0))).getD C.output false = true := by
    apply hS1z
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hS1 i hi
      rw [Finset.mem_Ico] at h2
      have h4 : ¬ (i < 13) := by omega
      have h5 : i - 13 < 13 := by omega
      simp only [zf, dif_neg h4, dif_pos h5, decide_eq_true_eq]
      have : 13 + (i - 13) = i := by omega
      simp [Y0, this, hi]
    · intro i h1 h2 h3
      rw [Finset.mem_Ico] at h2
      have h4 : i < 13 := by omega
      simp only [zf, dif_pos h4] at h3 ⊢
      exact h3
  obtain ⟨S2, hS2c, hS2, hS2z⟩ := key 26 (Finset.range 13) (zf X Y0) C.gates hm C.output hT1
  have hS2c' : S2.card ≤ 2 := hS2c.trans hd1
  let X0 : Finset (Fin 13) := Finset.univ.filter (fun p => p.val ∈ S2)
  have hX0c : X0.card ≤ 2 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun p : Fin 13 => p.val) ?_ ?_) hS2c'
    · intro p hp
      simpa [X0] using hp
    · intro a _ b _ hab
      exact Fin.ext hab
  have hX0X : ∀ p ∈ X0, p ∈ X := by
    intro p hp
    have h1 : p.val ∈ S2 := by simpa [X0] using hp
    have h2 := (hS2 _ h1).2.2
    simp only [zf, dif_pos p.isLt, decide_eq_true_eq] at h2
    exact h2
  have hfin : ∀ X' Y' : Finset (Fin 13), (∀ p ∈ X0, p ∈ X') → (∀ l ∈ Y0, l ∈ Y') → (W C.gates (inp 26 (zf X' Y'))).getD C.output false = true := by
    intro X' Y' hX' hY'
    apply hS2z
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hS2 i hi
      rw [Finset.mem_range] at h2
      simp only [zf, dif_pos h2, decide_eq_true_eq]
      apply hX'
      simp [X0, hi]
    · intro i h1 h2 h3
      rw [Finset.mem_range] at h2
      have h5 : i - 13 < 13 := by omega
      simp only [zf, dif_neg h2, dif_pos h5, decide_eq_true_eq] at h3 ⊢
      exact hY' _ h3
  obtain ⟨l0, m0, -, -, hY0s⟩ := pick Y0 hY0c (fun _ => True) (fun _ _ => trivial) ⟨0, trivial⟩
  obtain ⟨p, q, hp, hq, hX0s⟩ := pick X0 hX0c (fun p => ∀ l ∈ Y0, I p l = false) (fun p hp l hl => hno p (hX0X p hp) l (hY0Y l hl)) (by
    obtain ⟨p, hp1, hp2⟩ := pP l0 m0
    refine ⟨p, fun l hl => ?_⟩
    have := hY0s hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact hp1
    · exact hp2)
  obtain ⟨l, m, hl, hm', hY0s'⟩ := pick Y0 hY0c (fun l => I p l = false ∧ I q l = false) (fun l hl => ⟨hp l hl, hq l hl⟩) (pL p q)
  obtain ⟨a, b, c, hpa, hqa, hnc, h1, h2, h3, h4, h5, h6⟩ := pT p q l m ⟨hl.1, hm'.1, hl.2, hm'.2⟩
  refine ⟨a, b, c, hnc, ?_⟩
  intro Y' hY'
  apply hfin
  · intro x hx
    have := hX0s hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with rfl | rfl
    · exact hpa
    · exact hqa
  · intro k hk
    have := hY0s' hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact hY' _ h1 h2 h3
    · exact hY' _ h4 h5 h6

end PEqualNP.Outside.L_meta_4576

open PEqualNP.Outside.L_meta_4576 in
theorem PEqualNP.Outside.L_meta_4576 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => (∀ (x5 : Fin (13 : ℕ)), x5 ∈ x4 ↔ ∀ x6 ∈ x3, ¬x1 x6 x5) ∧ (∀ x5 ∉ x3, ∃ x7 ∈ x4, x1 x5 x7) ∧ (¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, x1 x6 x5) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x4, x1 x5 x6; have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x4 x5 : Finset (Fin (13 : ℕ))) => ∃ x6 ∈ x4, ∃ x7 ∈ x5, x1 x6 x7; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (2 : ℕ) ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (2 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x5 x6 → (∀ (x9 x10 : Finset (Fin (13 : ℕ))), x3 x9 x10 → x2 x6 x9 x10 = Bool.false) → ∀ (x10 x11 : Finset (Fin (13 : ℕ))), x2 x6 x10 x11 = Bool.true → x4 x10 x11 := by
  intro x1 x2 x3 x4 x5 C hM hd hF X Y hT
  by_contra hcon
  have hno : ∀ p ∈ X, ∀ l ∈ Y, I p l = false := by
    intro p hp l hl
    by_contra h
    rw [Bool.not_eq_false, ← Inc_iff] at h
    exact hcon ⟨p, hp, l, hl, h⟩
  have hT' : (W C.gates (inp 26 (zf X Y))).getD C.output false = true := by
    rw [← cf_eq]
    exact hT
  obtain ⟨a, b, c, hnc, hall⟩ := main C hM hd.1 hd.2 X Y hT' hno
  let Y' : Finset (Fin 13) := Finset.univ.filter (fun l => I a l = false ∧ I b l = false ∧ I c l = false)
  have hY' : ∀ l, l ∈ Y' ↔ (I a l = false ∧ I b l = false ∧ I c l = false) := by
    intro l
    simp [Y']
  have ht := hall Y' (fun l h1 h2 h3 => (hY' l).mpr ⟨h1, h2, h3⟩)
  have hf := hF {a, b, c} Y' ?_
  · have : x2 C {a, b, c} Y' = (W C.gates (inp 26 (zf {a, b, c} Y'))).getD C.output false := cf_eq C {a, b, c} Y'
    rw [this, ht] at hf
    exact Bool.noConfusion hf
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro l
      rw [hY']
      constructor
      · intro h x hx
        show ¬ (x = l ∨ x = l + 1 ∨ x = l + 3 ∨ x = l + 9)
        rw [Inc_iff]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simp [h.1]
        · simp [h.2.1]
        · simp [h.2.2]
      · intro h
        have ha := h a (by simp)
        have hb := h b (by simp)
        have hc := h c (by simp)
        change ¬ (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) at ha
        change ¬ (b = l ∨ b = l + 1 ∨ b = l + 3 ∨ b = l + 9) at hb
        change ¬ (c = l ∨ c = l + 1 ∨ c = l + 3 ∨ c = l + 9) at hc
        rw [Inc_iff, Bool.not_eq_true] at ha hb hc
        exact ⟨ha, hb, hc⟩
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
      obtain ⟨l, h1, h2⟩ := pB a b c r hr
      refine ⟨l, (hY' l).mpr h2, ?_⟩
      show (r = l ∨ r = l + 1 ∨ r = l + 3 ∨ r = l + 9)
      rw [Inc_iff]
      exact h1
    · rintro ⟨l, hl⟩
      apply hnc
      have ha := hl a (by simp)
      have hb := hl b (by simp)
      have hc := hl c (by simp)
      change (a = l ∨ a = l + 1 ∨ a = l + 3 ∨ a = l + 9) at ha
      change (b = l ∨ b = l + 1 ∨ b = l + 3 ∨ b = l + 9) at hb
      change (c = l ∨ c = l + 1 ∨ c = l + 3 ∨ c = l + 9) at hc
      rw [Inc_iff] at ha hb hc
      exact ⟨l, ha, hb, hc⟩
    · rintro ⟨s, hs⟩
      obtain ⟨l, h1, h2⟩ := pD a b c s hnc
      have := hs l ((hY' l).mpr h2)
      change (s = l ∨ s = l + 1 ∨ s = l + 3 ∨ s = l + 9) at this
      rw [Inc_iff, h1] at this
      exact Bool.noConfusion this
