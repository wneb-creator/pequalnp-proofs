import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1519

def ev (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def wr (gs : List Gate) (l : List Bool) : List Bool := gs.foldl (fun w g => w ++ [ev w g]) l

lemma wr_snoc (gs : List Gate) (g : Gate) (l : List Bool) :
    wr (gs ++ [g]) l = wr gs l ++ [ev (wr gs l) g] := by
  simp [wr]

lemma wr_length (gs : List Gate) (l : List Bool) : (wr gs l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr]
  | append_singleton gs g ih => rw [wr_snoc]; simp [ih]; omega

lemma wr_prefix (gs hs : List Gate) (l : List Bool) : ∃ r, wr (gs ++ hs) l = wr gs l ++ r := by
  induction hs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton hs g ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ [ev (wr (gs ++ hs) l) g], ?_⟩
    rw [← List.append_assoc, wr_snoc, hr, List.append_assoc]

lemma getD_left (a b : List Bool) (i : ℕ) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  rw [List.getD_append _ _ _ _ h]

lemma getD_big (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false :=
  List.getD_eq_default _ _ h

section

variable {n : ℕ} (gates : List Gate)

def v (x : Fin n → Bool) (w : ℕ) : Bool := (wr gates (List.ofFn x)).getD w false

def u (k : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool := if i < n + k then v gates x i else false

lemma v_input (x : Fin n → Bool) (a : Fin n) : v gates x a = x a := by
  obtain ⟨r, hr⟩ := wr_prefix [] gates (List.ofFn x)
  have h : wr gates (List.ofFn x) = List.ofFn x ++ r := hr
  rw [v, h, getD_left _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma v_big (x : Fin n → Bool) (w : ℕ) (h : n + gates.length ≤ w) : v gates x w = false := by
  apply getD_big
  rw [wr_length]; simpa using h

lemma take_getD (x : Fin n → Bool) (k i : ℕ) (hk : k ≤ gates.length) :
    (wr (gates.take k) (List.ofFn x)).getD i false = u gates k x i := by
  have hl : (wr (gates.take k) (List.ofFn x)).length = n + k := by
    rw [wr_length]; simp [hk]
  unfold u
  split_ifs with h
  · obtain ⟨r, hr⟩ := wr_prefix (gates.take k) (gates.drop k) (List.ofFn x)
    rw [List.take_append_drop] at hr
    rw [v, hr, getD_left _ _ _ (by omega)]
  · exact getD_big _ _ (by omega)

lemma v_gate (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length) :
    v gates x (n + k) = (gates[k]).op.eval ((gates[k]).inputs.map (u gates k x)) := by
  have h1 : u gates (k + 1) x (n + k) = v gates x (n + k) := by
    unfold u; rw [if_pos (by omega)]
  rw [← h1, ← take_getD gates x (k + 1) (n + k) (by omega)]
  have h2 : gates.take (k + 1) = gates.take k ++ [gates[k]] := by
    rw [List.take_append_getElem hk]
  have hl : (wr (gates.take k) (List.ofFn x)).length = n + k := by
    rw [wr_length]; simp; omega
  rw [h2, wr_snoc, List.getD_append_right _ _ _ _ (by omega), hl]
  simp only [Nat.sub_self, List.getD_cons_zero, ev]
  congr 1
  apply List.map_congr_left
  intro i _
  exact take_getD gates x k i (by omega)

end

def zr {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun a => decide (a ∉ S)
def rw2 {n : ℕ} (f : Finset (Fin n)) (p : Fin n) : Fin n → Bool := fun a => decide (a = p ∨ a ∈ f)

def rd (n : ℕ) (gates : List Gate) (j : ℕ) (k : Fin gates.length) : Prop :=
  j < k.val ∧ n + j ∈ (gates[k.val]).inputs

def chg {n : ℕ} (gates : List Gate) (j : ℕ) (S f : Finset (Fin n)) (k : Fin gates.length) : Prop :=
  (gates[k.val]).op = GateOp.or ∧ v gates (zr S) (n + k.val) = false ∧ ¬ rd n gates j k ∧
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ v gates (rw2 f p) (n + k.val) = true ∧
      v gates (rw2 f q) (n + k.val) = true

open Classical in
noncomputable def Ch {n : ℕ} (gates : List Gate) (j : ℕ) (S f : Finset (Fin n)) :
    Finset (Fin gates.length) :=
  Finset.univ.filter (chg gates j S f)

section

variable {n : ℕ} (gates : List Gate) (j : ℕ)
  (hop : ∀ (k : ℕ) (hk : k < gates.length),
    ((gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or ∨ k = j) ∧ (gates[k]).inputs.length ≤ 2)

include hop in
lemma mono (x y : Fin n → Bool) (hx : v gates x (n + j) = false) (hxy : ∀ a, x a = true → y a = true) :
    ∀ w : ℕ, v gates x w = true → v gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < n
    · have e1 := v_input gates x ⟨w, h1⟩
      have e2 := v_input gates y ⟨w, h1⟩
      simp only at e1 e2
      rw [e1] at h
      rw [e2]; exact hxy _ h
    · by_cases h2 : w < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gates.length := by omega
        have hu : ∀ i, u gates k x i = true → u gates k y i = true := by
          intro i hi
          unfold u at hi ⊢
          split_ifs at hi ⊢ with hlt
          · exact ih i hlt hi
        rcases (hop k hk).1 with ho | ho | ho
        · rw [v_gate _ _ _ hk, ho] at h ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h ⊢
          intro i hi; exact hu i (h i hi)
        · rw [v_gate _ _ _ hk, ho] at h ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at h ⊢
          obtain ⟨i, hi, h'⟩ := h
          exact ⟨i, hi, hu i h'⟩
        · subst ho
          rw [hx] at h; exact absurd h (by simp)
      · rw [v_big gates x w (by omega)] at h; exact absurd h (by simp)

lemma u_v (k : ℕ) (x : Fin n → Bool) (i : ℕ) (h : u gates k x i = true) :
    v gates x i = true ∧ i < n + k := by
  unfold u at h
  split_ifs at h with hlt
  exact ⟨h, hlt⟩

open Classical in
include hop in
lemma merge (S f : Finset (Fin n)) (hf : Disjoint f S)
    (wpos : ∀ p ∈ S, v gates (rw2 f p) (n + j) = false) :
    ∀ k : ℕ, k ≤ gates.length → ∃ r : Fin n → Fin n,
      (∀ w, w < n + k → v gates (zr S) w = false → ∀ p ∈ S, ∀ q ∈ S,
        v gates (rw2 f p) w = true → v gates (rw2 f q) w = true → r p = r q) ∧
      S.card ≤ (S.image r).card + ((Ch gates j S f).filter (fun c => c.val < k)).card := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, ?_, by simp⟩
    intro w hw hzero p hp q hq h1 h2
    have hw' : w < n := by omega
    have e0 := v_input gates (zr S) ⟨w, hw'⟩
    have e1 := v_input gates (rw2 f p) ⟨w, hw'⟩
    have e2 := v_input gates (rw2 f q) ⟨w, hw'⟩
    simp only at e0 e1 e2
    rw [e0] at hzero; rw [e1] at h1; rw [e2] at h2
    simp only [zr, rw2, decide_eq_false_iff_not, not_not, decide_eq_true_eq] at hzero h1 h2
    have hne : (⟨w, hw'⟩ : Fin n) ∉ f := fun e => Finset.disjoint_left.mp hf e hzero
    have a1 := h1.resolve_right hne
    have a2 := h2.resolve_right hne
    simp only [id]; rw [← a1, ← a2]
  | succ k ih =>
    intro hk1
    have hk : k < gates.length := by omega
    obtain ⟨r, hr, hcard⟩ := ih (by omega)
    have hsub : (Ch gates j S f).filter (fun c => c.val < k) ⊆
        (Ch gates j S f).filter (fun c => c.val < k + 1) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, by omega⟩
    have hIH : ∀ i, u gates k (zr S) i = false → ∀ p ∈ S, ∀ q ∈ S,
        u gates k (rw2 f p) i = true → u gates k (rw2 f q) i = true → r p = r q := by
      intro i h0 p hp q hq h1 h2
      obtain ⟨h1', hlt⟩ := u_v gates k _ i h1
      have h2' := (u_v gates k _ i h2).1
      refine hr i hlt ?_ p hp q hq h1' h2'
      unfold u at h0; rwa [if_pos hlt] at h0
    have keep : (v gates (zr S) (n + k) = false → ∀ p ∈ S, ∀ q ∈ S,
        v gates (rw2 f p) (n + k) = true → v gates (rw2 f q) (n + k) = true → r p = r q) →
        ∃ r : Fin n → Fin n,
        (∀ w, w < n + (k + 1) → v gates (zr S) w = false → ∀ p ∈ S, ∀ q ∈ S,
          v gates (rw2 f p) w = true → v gates (rw2 f q) w = true → r p = r q) ∧
        S.card ≤ (S.image r).card + ((Ch gates j S f).filter (fun c => c.val < k + 1)).card := by
      intro hnew
      refine ⟨r, ?_, hcard.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _)⟩
      intro w hw
      by_cases hwk : w < n + k
      · exact hr w hwk
      · have : w = n + k := by omega
        subst this; exact hnew
    rcases (hop k hk).1 with ho | ho | ho
    · apply keep
      intro h0 p hp q hq h1 h2
      rw [v_gate _ _ _ hk, ho] at h0 h1 h2
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h1 h2
      have h0' : ∃ i ∈ (gates[k]).inputs, u gates k (zr S) i = false := by
        by_contra hcon
        push Not at hcon
        have : (GateOp.and.eval ((gates[k]).inputs.map (u gates k (zr S)))) = true := by
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
          intro i hi
          simpa using hcon i hi
        rw [this] at h0; exact absurd h0 (by simp)
      obtain ⟨i, hi, h0i⟩ := h0'
      exact hIH i h0i p hp q hq (h1 i hi) (h2 i hi)
    · have hlen := (hop k hk).2
      have orv : ∀ x : Fin n → Bool, v gates x (n + k) = true ↔
          ∃ i ∈ (gates[k]).inputs, u gates k x i = true := by
        intro x
        rw [v_gate _ _ _ hk, ho]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
      by_cases hgood : v gates (zr S) (n + k) = false → ∀ p ∈ S, ∀ q ∈ S,
        v gates (rw2 f p) (n + k) = true → v gates (rw2 f q) (n + k) = true → r p = r q
      · exact keep hgood
      · push Not at hgood
        obtain ⟨h0, p0, hp0, q0, hq0, hv1, hv2, hne⟩ := hgood
        obtain ⟨a, ha, hua⟩ := (orv _).mp hv1
        obtain ⟨b, hb, hub⟩ := (orv _).mp hv2
        have h0i : ∀ i ∈ (gates[k]).inputs, u gates k (zr S) i = false := by
          intro i hi
          by_contra hcon
          have : v gates (zr S) (n + k) = true := (orv _).mpr ⟨i, hi, by simpa using hcon⟩
          rw [this] at h0; exact absurd h0 (by simp)
        have hab : a ≠ b := by
          intro e; subst e
          exact hne (hIH a (h0i a ha) p0 hp0 q0 hq0 hua hub)
        have hinp : ∀ i ∈ (gates[k]).inputs, i = a ∨ i = b := by
          intro i hi
          by_contra hcon
          push Not at hcon
          have hnd : ([a, b, i] : List ℕ).Nodup := by
            simp [hab, hcon.1.symm, hcon.2.symm]
          have hss : ([a, b, i] : List ℕ) ⊆ (gates[k]).inputs := by
            intro z hz'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
            rcases hz' with rfl | rfl | rfl <;> assumption
          have := (hnd.subperm hss).length_le
          simp at this; omega
        have hnrd : ¬ rd n gates j ⟨k, hk⟩ := by
          rintro ⟨_, hmem⟩
          rcases hinp _ hmem with e | e
          · rw [← e] at hua
            have := (u_v gates k _ _ hua).1
            rw [wpos p0 hp0] at this; exact absurd this (by simp)
          · rw [← e] at hub
            have := (u_v gates k _ _ hub).1
            rw [wpos q0 hq0] at this; exact absurd this (by simp)
        have hp0q0 : p0 ≠ q0 := fun e => hne (by rw [e])
        have hch : (⟨k, hk⟩ : Fin gates.length) ∈ Ch gates j S f := by
          rw [Ch, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ho, h0, hnrd, p0, hp0, q0, hq0, hp0q0, hv1, hv2⟩
        refine ⟨fun x => if r x = r q0 then r p0 else r x, ?_, ?_⟩
        · intro w hw h0w p hp q hq h1 h2
          by_cases hwk : w < n + k
          · simp only [hr w hwk h0w p hp q hq h1 h2]
          · have : w = n + k := by omega
            subst this
            have key : ∀ p ∈ S, v gates (rw2 f p) (n + k) = true →
                (if r p = r q0 then r p0 else r p) = r p0 := by
              intro p hp h
              obtain ⟨i, hi, hui⟩ := (orv _).mp h
              rcases hinp i hi with rfl | rfl
              · have := hIH i (h0i i hi) p hp p0 hp0 hui hua
                rw [this, if_neg hne]
              · have := hIH i (h0i i hi) p hp q0 hq0 hui hub
                rw [if_pos this]
            simp only
            rw [key p hp h1, key q hq h2]
        · have c1 : ((S.image r).erase (r q0)).card ≤
              (S.image (fun x => if r x = r q0 then r p0 else r x)).card := by
            apply Finset.card_le_card
            intro z hz'
            rw [Finset.mem_erase, Finset.mem_image] at hz'
            obtain ⟨hzne, x, hx, rfl⟩ := hz'
            rw [Finset.mem_image]
            exact ⟨x, hx, by rw [if_neg hzne]⟩
          have c2 : (S.image r).card ≤ ((S.image r).erase (r q0)).card + 1 := by
            have := Finset.pred_card_le_card_erase (s := S.image r) (a := r q0)
            omega
          have c3 : ((Ch gates j S f).filter (fun c => c.val < k)).card + 1 ≤
              ((Ch gates j S f).filter (fun c => c.val < k + 1)).card := by
            apply Finset.card_lt_card
            refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨⟨k, hk⟩, ?_, ?_⟩
            · rw [Finset.mem_filter]; exact ⟨hch, by simp⟩
            · rw [Finset.mem_filter]; simp
          omega
    · apply keep
      intro _ p hp q hq h1 _
      subst ho
      rw [wpos p hp] at h1; exact absurd h1 (by simp)

end



lemma line_facts : (∀ i i' : Fin 13, i ≠ i' →
      ((({i, i + 1, i + 3, i + 9} : Finset (Fin 13)) ∩ {i', i' + 1, i' + 3, i' + 9}).card ≤ 1)) ∧
    (∀ i : Fin 13, ({i, i + 1, i + 3, i + 9} : Finset (Fin 13)).card = 4) ∧
    (∀ t : Fin 13, (Finset.univ.filter
      (fun i : Fin 13 => t ∉ ({i, i + 1, i + 3, i + 9} : Finset (Fin 13)))).card = 9) ∧
    (∀ t : Fin 13, (Finset.univ.filter
      (fun i : Fin 13 => t ∈ ({i, i + 1, i + 3, i + 9} : Finset (Fin 13)))).card = 4) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1519

theorem PEqualNP.Outside.L_meta_1519 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    ∀ t : Fin 13,
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun y : Fin 13 => decide (y = t))) = true →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          13 + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      29 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + max 4 I.card ≤ gates.length := by
  classical
  intro L hL gates o j h hg hjn hju hhj hin hout hco t ht I hI
  obtain ⟨f1, f2, f3, f4⟩ := L_meta_1519.line_facts
  have hLL : ∀ i i' : Fin 13, i ≠ i' → (L i ∩ L i').card ≤ 1 := by
    intro i i' hii; rw [hL, hL]; exact f1 i i' hii
  have hLc : ∀ i, (L i).card = 4 := by intro i; rw [hL]; exact f2 i
  have hJ : (Finset.univ.filter (fun i : Fin 13 => t ∉ L i)).card = 9 := by
    have := f3 t; simpa only [← hL] using this
  have hJ' : (Finset.univ.filter (fun i : Fin 13 => t ∈ L i)).card = 4 := by
    have := f4 t; simpa only [← hL] using this
  have hout' : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      L_meta_1519.v gates x (o w) = decide (∃ a ∈ L w, x a = true) := fun w x => hout w x
  have hop : ∀ (k : ℕ) (hk : k < gates.length),
      ((gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or ∨ k = j.val) ∧
        (gates[k]).inputs.length ≤ 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := hg gates[k] (List.getElem_mem hk)
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (congrArg Fin.val (hju ⟨k, hk⟩ h)))
  -- the NOT gate carries the negation of h
  have hnot : ∀ x : Fin 13 → Bool,
      L_meta_1519.v gates x (13 + j.val) = !(L_meta_1519.v gates x (13 + h.val)) := by
    intro x
    obtain ⟨r, hr⟩ := hin
    have hr' : (gates[j.val]).inputs = (13 + h.val) :: r := hr
    have hjn' : (gates[j.val]).op = GateOp.not := hjn
    have hlt : h.val < j.val := hhj
    rw [L_meta_1519.v_gate gates x j.val j.isLt, hjn', hr']
    simp only [List.map_cons, GateOp.eval, List.headD_cons, L_meta_1519.u]
    rw [if_pos (by omega)]
  have hco' : ∀ i, L_meta_1519.v gates (L_meta_1519.zr (L i)) (13 + h.val) = true := fun i => hco i
  have hzz : ∀ i, L_meta_1519.v gates (L_meta_1519.zr (L i)) (13 + j.val) = false := by
    intro i; rw [hnot, hco' i]; rfl
  have ht1 : L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) (13 + h.val) = true := ht
  have ht0 : L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) (13 + j.val) = false := by
    rw [hnot, ht1]; rfl
  have hmt : ∀ (x : Fin 13 → Bool), x t = true → ∀ w,
      L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) w = true → L_meta_1519.v gates x w = true := by
    intro x hx
    exact L_meta_1519.mono gates j.val hop _ x ht0 (by
      intro a ha
      have : a = t := of_decide_eq_true ha
      rw [this]; exact hx)
  have hwt : ∀ x : Fin 13 → Bool, x t = true → L_meta_1519.v gates x (13 + j.val) = false := by
    intro x hx; rw [hnot, hmt x hx _ ht1]; rfl
  have hzr : ∀ i, ∀ p ∈ L i, L_meta_1519.v gates (L_meta_1519.rw2 {t} p) (13 + j.val) = false := by
    intro i p _; exact hwt _ (by simp [L_meta_1519.rw2])
  have hlow : ∀ i, t ∉ L i → 3 ≤ (L_meta_1519.Ch gates j.val (L i) {t}).card := by
    intro i hti
    obtain ⟨r, hr, hc⟩ := L_meta_1519.merge gates j.val hop (L i) {t} (by simpa using hti) (hzr i)
      gates.length le_rfl
    have hfil : (L_meta_1519.Ch gates j.val (L i) {t}).filter (fun c => c.val < gates.length) =
        L_meta_1519.Ch gates j.val (L i) {t} := by
      apply Finset.filter_true_of_mem
      intro c _; exact c.isLt
    rw [hfil, hLc i] at hc
    have htrue : ∀ p ∈ L i, L_meta_1519.v gates (L_meta_1519.rw2 {t} p) (o i) = true := by
      intro p hp
      rw [hout']
      exact decide_eq_true ⟨p, hp, by simp [L_meta_1519.rw2]⟩
    have hzero : L_meta_1519.v gates (L_meta_1519.zr (L i)) (o i) = false := by
      rw [hout']
      apply decide_eq_false
      rintro ⟨a, ha, h⟩
      simp [L_meta_1519.zr, ha] at h
    have himg : ((L i).image r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨p', hp', rfl⟩ := hb
      have hlt : o i < 13 + gates.length := by
        by_contra hcon
        have := htrue p hp
        rw [L_meta_1519.v_big gates _ _ (by omega)] at this
        exact absurd this (by simp)
      exact hr (o i) hlt hzero p hp p' hp' (htrue p hp) (htrue p' hp')
    omega
  set J := Finset.univ.filter (fun i : Fin 13 => t ∉ L i) with hJdef
  have hit : ∀ i', t ∉ L i' → ∀ (k : Fin gates.length) p,
      L_meta_1519.v gates (L_meta_1519.rw2 {t} p) (13 + k.val) = true →
      L_meta_1519.v gates (L_meta_1519.zr (L i')) (13 + k.val) = false → p ∈ L i' := by
    intro i' hti k p h1 h0
    by_contra hcon
    have := L_meta_1519.mono gates j.val hop (L_meta_1519.rw2 {t} p) (L_meta_1519.zr (L i'))
      (hwt _ (by simp [L_meta_1519.rw2])) (by
        intro a ha
        simp only [L_meta_1519.rw2, L_meta_1519.zr, decide_eq_true_eq, Finset.mem_singleton] at ha ⊢
        rcases ha with rfl | rfl
        · exact hcon
        · exact hti) _ h1
    rw [this] at h0; exact absurd h0 (by simp)
  have hdisj : ∀ i ∈ J, ∀ i' ∈ J, i ≠ i' →
      Disjoint (L_meta_1519.Ch gates j.val (L i) {t}) (L_meta_1519.Ch gates j.val (L i') {t}) := by
    intro i _ i' hi' hii
    have hti' : t ∉ L i' := (Finset.mem_filter.mp hi').2
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨_, _, _, p, hp, p', hp', hne, hv, hv'⟩ := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    have a1 := hit i' hti' k p hv h2'.2.1
    have a2 := hit i' hti' k p' hv' h2'.2.1
    have : 1 < (L i ∩ L i').card := Finset.one_lt_card.mpr
      ⟨p, Finset.mem_inter.mpr ⟨hp, a1⟩, p', Finset.mem_inter.mpr ⟨hp', a2⟩, hne⟩
    have := hLL i i' hii
    omega
  set U := J.biUnion (fun i => L_meta_1519.Ch gates j.val (L i) {t}) with hUdef
  have hU : 27 ≤ U.card := by
    rw [hUdef, Finset.card_biUnion hdisj]
    calc 27 = ∑ _i ∈ J, 3 := by rw [Finset.sum_const, hJ]; rfl
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hlow i (Finset.mem_filter.mp hi).2)
  have hUchg : ∀ k ∈ U, ∃ i, t ∉ L i ∧ L_meta_1519.chg gates j.val (L i) {t} k := by
    intro k hk
    rw [hUdef, Finset.mem_biUnion] at hk
    obtain ⟨i, hi, hk⟩ := hk
    exact ⟨i, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hk).2⟩
  have hUt : ∀ k ∈ U, L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) (13 + k.val) = false := by
    intro k hk
    obtain ⟨i, hti, hch⟩ := hUchg k hk
    by_contra hcon
    have h1 : L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) (13 + k.val) = true := by
      simpa using hcon
    have := hmt (L_meta_1519.zr (L i)) (by simp [L_meta_1519.zr, hti]) _ h1
    rw [hch.2.1] at this; exact absurd this (by simp)
  set R := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs) with hR
  have d1 : Disjoint U R := by
    rw [Finset.disjoint_left]
    intro k hk hk2
    obtain ⟨i, _, hi⟩ := hUchg k hk
    have := (Finset.mem_filter.mp hk2).2
    exact hi.2.2.1 ⟨this.1, this.2⟩
  have d2 : Disjoint (U ∪ R) {j, h} := by
    rw [Finset.disjoint_left]
    intro k hk hk2
    rw [Finset.mem_insert, Finset.mem_singleton] at hk2
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases hk2 with rfl | rfl
      · obtain ⟨i, _, _, _, _, p, hp, _, _, _, hv, _⟩ := hUchg k hk
        rw [hzr i p hp] at hv; exact absurd hv (by simp)
      · rw [hUt k hk] at ht1; exact absurd ht1 (by simp)
    · have hjk := (Finset.mem_filter.mp hk).2.1
      rcases hk2 with rfl | rfl
      · exact absurd hjk (lt_irrefl _)
      · exact absurd hjk (not_lt.mpr hhj.le)
  -- any further set of gates off these adds its size
  have fin : ∀ X : Finset (Fin gates.length), Disjoint ((U ∪ R) ∪ {j, h}) X →
      29 + R.card + X.card ≤ gates.length := by
    intro X hX
    have hc : (((U ∪ R) ∪ {j, h}) ∪ X).card ≤ gates.length := by
      have := Finset.card_le_univ (((U ∪ R) ∪ {j, h}) ∪ X)
      simpa using this
    rw [Finset.card_union_of_disjoint hX, Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d1, Finset.card_pair (ne_of_gt hhj)] at hc
    omega
  have caseI : 29 + R.card + I.card ≤ gates.length := by
    apply fin
    rw [Finset.disjoint_left]
    intro k hk hkI
    obtain ⟨hand, hcl⟩ := hI k hkI
    have hkh : k < h := by
      have := hcl (Finset.univ.filter (fun i => i < h)) (by
        intro i g' hi _ hg'
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hi with rfl | hi
        · exact hg'
        · exact lt_trans hg' (Finset.mem_filter.mp hi).2)
      exact (Finset.mem_filter.mp this).2
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨i, _, hch⟩ := hUchg k hk
        have e : (gates[k.val]).op = GateOp.and := hand
        rw [hch.1] at e
        exact absurd e (by simp)
      · exact absurd ((Finset.mem_filter.mp hk).2.1) (not_lt.mpr (hkh.le.trans hhj.le))
    · rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact absurd (hkh.trans hhj) (lt_irrefl _)
      · exact absurd hkh (lt_irrefl _)
  have case4 : 29 + R.card + 4 ≤ gates.length := by
    -- the first wire computing each line through t
    have hex : ∀ i : Fin 13, ∃ w, ∀ x, L_meta_1519.v gates x w = decide (∃ a ∈ L i, x a = true) :=
      fun i => ⟨o i, hout' i⟩
    let m : Fin 13 → ℕ := fun i => Nat.find (hex i)
    have hm : ∀ i x, L_meta_1519.v gates x (m i) = decide (∃ a ∈ L i, x a = true) :=
      fun i => Nat.find_spec (hex i)
    have hmin : ∀ i w, w < m i → ¬ ∀ x, L_meta_1519.v gates x w = decide (∃ a ∈ L i, x a = true) :=
      fun i w hw => Nat.find_min (hex i) hw
    have hmt1 : ∀ i, t ∈ L i →
        L_meta_1519.v gates (fun y : Fin 13 => decide (y = t)) (m i) = true := by
      intro i hti
      rw [hm]; exact decide_eq_true ⟨t, hti, by simp⟩
    have hmz : ∀ i, L_meta_1519.v gates (L_meta_1519.zr (L i)) (m i) = false := by
      intro i
      rw [hm]
      apply decide_eq_false
      rintro ⟨a, ha, h⟩
      simp [L_meta_1519.zr, ha] at h
    have hm0 : ∀ i, L_meta_1519.v gates (fun _ : Fin 13 => false) (m i) = false := by
      intro i; rw [hm]; simp
    have hlt : ∀ i, t ∈ L i → m i < 13 + gates.length := by
      intro i hti
      by_contra hcon
      have := hmt1 i hti
      rw [L_meta_1519.v_big gates _ _ (by omega)] at this
      exact absurd this (by simp)
    have hge : ∀ i, 13 ≤ m i := by
      intro i
      by_contra hcon
      have hlt : m i < 13 := by omega
      have hc : 1 < (L i).card := by rw [hLc]; norm_num
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
      have key : ∀ c ∈ L i, c = ⟨m i, hlt⟩ := by
        intro c hc
        have h1 := hm i (fun y => decide (y = c))
        have h2 := L_meta_1519.v_input gates (fun y => decide (y = c)) ⟨m i, hlt⟩
        simp only at h2
        rw [h1] at h2
        have h3 : decide (∃ a ∈ L i, (fun y => decide (y = c)) a = true) = true :=
          decide_eq_true ⟨c, hc, by simp⟩
        rw [h3] at h2
        exact (of_decide_eq_true h2.symm).symm
      exact hab ((key a ha).trans (key b hb).symm)
    have hinj : ∀ i i', m i = m i' → i = i' := by
      intro i i' he
      by_contra hne
      have hsub : L i ⊆ L i ∩ L i' := by
        intro c hc
        refine Finset.mem_inter.mpr ⟨hc, ?_⟩
        have h1 := hm i (fun y => decide (y = c))
        have h2 := hm i' (fun y => decide (y = c))
        rw [he] at h1
        rw [h1] at h2
        have h3 : decide (∃ a ∈ L i, (fun y => decide (y = c)) a = true) = true :=
          decide_eq_true ⟨c, hc, by simp⟩
        rw [h3] at h2
        obtain ⟨a, ha, hac⟩ := of_decide_eq_true h2.symm
        have : a = c := of_decide_eq_true hac
        rw [← this]; exact ha
      have := (Finset.card_le_card hsub).trans (hLL i i' hne)
      rw [hLc] at this; omega
    let X : Finset (Fin gates.length) := Finset.univ.filter (fun k => ∃ i, t ∈ L i ∧ m i = 13 + k.val)
    have hX : 4 ≤ X.card := by
      rw [← hJ']
      apply Finset.card_le_card_of_surjOn
        (fun k : Fin gates.length => if hk : ∃ i, t ∈ L i ∧ m i = 13 + k.val then hk.choose else t)
      intro i hi
      have hti : t ∈ L i := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      have h1 := hge i
      have h2 := hlt i hti
      have hk : ∃ i', t ∈ L i' ∧ m i' = 13 + (⟨m i - 13, by omega⟩ : Fin gates.length).val :=
        ⟨i, hti, by simp only; omega⟩
      refine ⟨⟨m i - 13, by omega⟩, ?_, ?_⟩
      · simp only [X, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        exact hk
      · simp only
        rw [dif_pos hk]
        apply hinj
        have := hk.choose_spec.2
        simp only at this
        omega
    have hd : Disjoint ((U ∪ R) ∪ {j, h}) X := by
      rw [Finset.disjoint_left]
      intro k hk hkX
      obtain ⟨i, hti, hmi⟩ := (Finset.mem_filter.mp hkX).2
      have k1 := hmt1 i hti
      rw [hmi] at k1
      rcases Finset.mem_union.mp hk with hk | hk
      · rcases Finset.mem_union.mp hk with hk | hk
        · rw [hUt k hk] at k1; exact absurd k1 (by simp)
        · obtain ⟨hjk, hmem⟩ := (Finset.mem_filter.mp hk).2
          have hjk' : j.val < k.val := hjk
          have hmem' : 13 + j.val ∈ (gates[k.val]).inputs := hmem
          have huj : ∀ x : Fin 13 → Bool, L_meta_1519.u gates k.val x (13 + j.val) = L_meta_1519.v gates x (13 + j.val) := by
            intro x; unfold L_meta_1519.u; rw [if_pos (by omega)]
          rcases (hop k.val k.isLt).1 with ho | ho | ho
          · rw [L_meta_1519.v_gate _ _ _ k.isLt, ho] at k1
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at k1
            have := k1 _ hmem'
            rw [huj, ht0] at this; exact absurd this (by simp)
          · have orv : ∀ x : Fin 13 → Bool, L_meta_1519.v gates x (13 + k.val) = true ↔
                ∃ a ∈ (gates[k.val]).inputs, L_meta_1519.u gates k.val x a = true := by
              intro x
              rw [L_meta_1519.v_gate _ _ _ k.isLt, ho]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
            -- at the zero input the NOT gate is false, so h is constantly true
            have hz0 : L_meta_1519.v gates (fun _ : Fin 13 => false) (13 + j.val) = false := by
              by_contra hcon
              have : L_meta_1519.v gates (fun _ : Fin 13 => false) (13 + k.val) = true :=
                (orv _).mpr ⟨_, hmem', by rw [huj]; simpa using hcon⟩
              rw [← hmi, hm0] at this; exact absurd this (by simp)
            have hh0 : L_meta_1519.v gates (fun _ : Fin 13 => false) (13 + h.val) = true := by
              have := hnot (fun _ : Fin 13 => false)
              rw [hz0] at this; simpa using this.symm
            have hw0 : ∀ x : Fin 13 → Bool, L_meta_1519.v gates x (13 + j.val) = false := by
              intro x
              rw [hnot, L_meta_1519.mono gates j.val hop (fun _ => false) x hz0 (by simp) _ hh0]; rfl
            obtain ⟨b, hb, hub⟩ := (orv _).mp k1
            have hbj : b ≠ 13 + j.val := by
              intro e; rw [e, huj, hw0] at hub; exact absurd hub (by simp)
            have hblt := (L_meta_1519.u_v gates k.val _ b hub).2
            have hinp : ∀ a ∈ (gates[k.val]).inputs, a = b ∨ a = 13 + j.val := by
              intro a ha
              by_contra hcon
              push Not at hcon
              have hnd : ([b, 13 + j.val, a] : List ℕ).Nodup := by
                simp [hbj, hcon.1.symm, hcon.2.symm]
              have hss : ([b, 13 + j.val, a] : List ℕ) ⊆ (gates[k.val]).inputs := by
                intro z hz'
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
                rcases hz' with rfl | rfl | rfl <;> assumption
              have hle := (hnd.subperm hss).length_le
              have := (hop k.val k.isLt).2
              simp at hle; omega
            refine hmin i b (by omega) (fun x => ?_)
            rw [← hm i x, hmi]
            have hub' : L_meta_1519.u gates k.val x b = L_meta_1519.v gates x b := by
              unfold L_meta_1519.u; rw [if_pos hblt]
            rw [Bool.eq_iff_iff, orv]
            constructor
            · intro hx; exact ⟨b, hb, by rw [hub']; exact hx⟩
            · rintro ⟨a, ha, hua⟩
              rcases hinp a ha with e | e
              · rw [e, hub'] at hua; exact hua
              · rw [e, huj, hw0] at hua; exact absurd hua (by simp)
          · exact absurd ho (by omega)
      · rw [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · rw [ht0] at k1; exact absurd k1 (by simp)
        · have := hmz i
          rw [hmi, hco' i] at this; exact absurd this (by simp)
    have := fin X hd
    omega
  rcases le_total 4 I.card with h4 | h4
  · rw [max_eq_right h4]; exact caseI
  · rw [max_eq_left h4]; exact case4
