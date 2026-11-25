import PEqualNP.Defs
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_4970.H9RedTeam

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def hiddenMixed : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.and, [1, 1]⟩, ⟨.or, [2, 3]⟩], 4⟩

lemma hiddenMixed_model : IsAO2 2 hiddenMixed := by decide +kernel

lemma hiddenMixed_tCount : tCount 2 hiddenMixed (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma hiddenMixed_function :
    ∀ x : Fin 2 → Bool, circuitFun 2 hiddenMixed x = (x 0 || x 1) := by
  decide +kernel

lemma hiddenMixed_reach : orIn 2 hiddenMixed 4 = ∅ := by decide +kernel

def hiddenMixedBypass : Circuit := ⟨[⟨.or, [0, 1]⟩], 2⟩

lemma hiddenMixedBypass_same :
    ∀ x : Fin 2 → Bool, circuitFun 2 hiddenMixedBypass x = circuitFun 2 hiddenMixed x := by
  decide +kernel

lemma hiddenMixedBypass_tCount :
    tCount 2 hiddenMixedBypass (fun i => decide (1 ≤ i)) = 1 := by decide +kernel

def deadStar : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [1, 2]⟩], 5⟩

lemma deadStar_model : IsAO2 3 deadStar := by decide +kernel

lemma deadStar_tCount : tCount 3 deadStar (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma deadStar_no_four_cycle :
    ∀ (a a' : Fin 1) (b b' : Fin 2), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a', b) ∈ (Finset.univ : Finset (Fin 1 × Fin 2)) ∧
        (a', b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) := by decide +kernel

lemma deadStar_function :
    ∀ x : Fin 3 → Bool, circuitFun 3 deadStar x =
      decide (∃ (a : Fin 1) (b : Fin 2), x (Fin.castAdd 2 a) = true ∧
        x (Fin.natAdd 1 b) = true) := by
  decide +kernel

lemma deadStar_served :
    ∀ (a : Fin 1) (b : Fin 2),
      ∃ (j : ℕ) (Q : Finset (Fin 2)),
        j < deadStar.gates.length ∧ (gateAt deadStar j).op = .or ∧
        2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) ∧
        ∀ x : Fin 3 → Bool,
          (deadStar.wires (List.ofFn x)).getD (3 + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  intro a b
  refine ⟨3, Finset.univ, by decide, rfl, by decide, Finset.mem_univ b, ?_, ?_⟩
  · intro b' hb'
    exact Finset.mem_univ (a, b')
  · decide +kernel

lemma deadStar_not_read : ∀ g ∈ deadStar.gates, 6 ∉ g.inputs := by decide +kernel

lemma deadStar_topOperand_not_pure :
    ∀ Q : Finset (Fin 3),
      ¬ (∀ x : Fin 3 → Bool,
        (deadStar.wires (List.ofFn x)).getD 4 false =
          decide (∃ i ∈ Q, x i = true)) := by
  decide +kernel

def disconnectedStars : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [0, 6]⟩, ⟨.or, [7, 8]⟩], 9⟩

lemma disconnectedStars_model : IsAO2 5 disconnectedStars := by decide +kernel

lemma disconnectedStars_tCount :
    tCount 5 disconnectedStars (fun i => decide (1 ≤ i)) = 0 := by decide +kernel

lemma disconnectedStars_function :
    ∀ x : Fin 5 → Bool, circuitFun 5 disconnectedStars x =
      (x 0 && (x 1 || x 2 || x 3 || x 4)) := by decide +kernel

lemma disconnectedStars_no_full_witness :
    ∀ j : Fin disconnectedStars.gates.length,
      ¬ (∀ x : Fin 5 → Bool,
        (disconnectedStars.wires (List.ofFn x)).getD (5 + j) false =
          (x 1 || x 2 || x 3 || x 4)) := by decide +kernel

lemma disconnectedStars_served :
    ∀ b : Fin 4, ∃ (j : Fin 2) (Q : Finset (Fin 4)),
      2 ≤ Q.card ∧ b ∈ Q ∧
      ∀ x : Fin 5 → Bool,
        (disconnectedStars.wires (List.ofFn x)).getD (5 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by decide +kernel

def mixedFanout : Circuit :=
  ⟨[⟨.and, [0, 0]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [4, 3]⟩,
    ⟨.or, [5, 6]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 3]⟩,
    ⟨.and, [0, 11]⟩, ⟨.and, [12, 9]⟩], 13⟩

lemma mixedFanout_model : IsAO2 4 mixedFanout := by decide +kernel

lemma mixedFanout_tCount : tCount 4 mixedFanout (fun i => decide (1 ≤ i)) = 0 := by
  decide +kernel

lemma mixedFanout_function :
    ∀ x : Fin 4 → Bool, circuitFun 4 mixedFanout x =
      (x 0 && (x 1 || x 2 || x 3)) := by decide +kernel

lemma mixedFanout_serving_star :
    ∀ x : Fin 4 → Bool, (mixedFanout.wires (List.ofFn x)).getD 11 false =
      (x 1 || x 2 || x 3) := by decide +kernel

lemma mixedFanout_edge_active :
    ∀ j : Fin mixedFanout.gates.length, ∃ b : Fin 3,
      (mixedFanout.wires (List.ofFn fun i : Fin 4 =>
        decide (i = 0 ∨ i = Fin.natAdd 1 b))).getD (4 + j) false = true := by
  decide +kernel

lemma mixedFanout_five_semantically_mixed :
    ∀ j : Fin 5,
      (mixedFanout.wires (List.ofFn fun i : Fin 4 => decide (i = 0))).getD
        (5 + j) false = true ∧
      ∃ b : Fin 3,
        (mixedFanout.wires (List.ofFn fun i : Fin 4 => decide (i = Fin.natAdd 1 b))).getD
          (5 + j) false = true := by decide +kernel

lemma mixedFanout_three_and :
    (mixedFanout.gates.filter fun g => match g.op with
      | .and => true
      | _ => false).length = 3 := by decide +kernel

def cycleSixCnf : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 6]⟩, ⟨.or, [3, 9]⟩,
    ⟨.and, [6, 6]⟩, ⟨.and, [7, 7]⟩, ⟨.and, [8, 8]⟩,
    ⟨.or, [14, 9]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [16, 11]⟩,
    ⟨.and, [12, 13]⟩, ⟨.and, [20, 17]⟩,
    ⟨.and, [21, 18]⟩, ⟨.and, [22, 19]⟩], 23⟩

lemma cycleSixCnf_model : IsAO2 6 cycleSixCnf := by decide +kernel

lemma cycleSixCnf_tCount :
    tCount 6 cycleSixCnf (fun i => decide (3 ≤ i)) = 0 := by decide +kernel

lemma cycleSixCnf_function : ∀ x : Fin 6 → Bool,
    circuitFun 6 cycleSixCnf x = decide (∃ (a b : Fin 3),
      a ≠ b ∧ x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true) := by
  decide +kernel

lemma cycleSixCnf_served :
    ∀ (a b : Fin 3), a ≠ b →
      ∃ (j : ℕ) (Q : Finset (Fin 3)),
        j < cycleSixCnf.gates.length ∧ (gateAt cycleSixCnf j).op = .or ∧
        2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, a ≠ b') ∧
        ∀ x : Fin 6 → Bool,
          (cycleSixCnf.wires (List.ofFn x)).getD (6 + j) false =
            decide (∃ b' ∈ Q, x (Fin.natAdd 3 b') = true) := by
  intro a b hab
  refine ⟨3 + a, Finset.univ.erase a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ha := a.isLt
    change 3 + a.val < 18
    omega
  · fin_cases a <;> rfl
  · simp
  · simp [Ne.symm hab]
  · intro b' hb'
    exact Ne.symm (Finset.mem_erase.mp hb').1
  · fin_cases a <;> decide +kernel

lemma cycleSixCnf_no_four_cycle :
    ∀ (a a' b b' : Fin 3), a ≠ a' → b ≠ b' →
      ¬ (a ≠ b ∧ a ≠ b' ∧ a' ≠ b ∧ a' ≠ b') := by decide +kernel

lemma cycleSixCnf_all_gates_true_on_cosingletons :
    ∀ (v : Fin 6) (j : Fin cycleSixCnf.gates.length),
      (cycleSixCnf.wires (List.ofFn fun i : Fin 6 => decide (i ≠ v))).getD
        (6 + j) false = true := by decide +kernel

lemma cycleSixCnf_and_operands_true_on_cosingletons :
    ∀ (v : Fin 6) (j : Fin cycleSixCnf.gates.length),
      match (gateAt cycleSixCnf j).op with
      | .and => ∀ w ∈ (gateAt cycleSixCnf j).inputs,
          (cycleSixCnf.wires (List.ofFn fun i : Fin 6 => decide (i ≠ v))).getD
            w false = true
      | _ => True := by
  intro v j
  fin_cases j <;> simp [cycleSixCnf, gateAt] <;> revert v <;> decide +kernel

lemma cycleSixCnf_edge_active :
    ∀ j : Fin cycleSixCnf.gates.length, ∃ (a b : Fin 3), a ≠ b ∧
      (cycleSixCnf.wires (List.ofFn fun i : Fin 6 =>
        decide (i = Fin.castAdd 3 a ∨ i = Fin.natAdd 3 b))).getD
          (6 + j) false = true := by decide +kernel

lemma cycleSixCnf_safe_iff_final :
    ∀ j : Fin cycleSixCnf.gates.length,
      (∀ x : Fin 6 → Bool,
        (cycleSixCnf.wires (List.ofFn x)).getD (6 + j) false = true →
          decide (∃ (a b : Fin 3), a ≠ b ∧
            x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 3 b) = true) = true) ↔ j.val = 17 := by
  decide +kernel

lemma cycleSixCnf_previous_diagonal :
    ∀ j : Fin 17, ∃ a : Fin 3,
      (cycleSixCnf.wires (List.ofFn fun i : Fin 6 =>
        decide (i = Fin.castAdd 3 a ∨ i = Fin.natAdd 3 a))).getD (6 + j) false = true := by
  decide +kernel

namespace MixedSupport

variable {α : Type*} [DecidableEq α]

def unit (u : α) : α → Bool := fun i => decide (i = u)

def pair (u v : α) : α → Bool := fun i => decide (i = u ∨ i = v)

def Mono (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma unit_le_pair_left (u v : α) : ∀ i, unit u i = true → pair u v i = true := by
  intro i hi
  simp only [unit, decide_eq_true_eq] at hi
  simp [pair, hi]

lemma unit_le_pair_right (u v : α) : ∀ i, unit v i = true → pair u v i = true := by
  intro i hi
  simp only [unit, decide_eq_true_eq] at hi
  simp [pair, hi]

lemma mixed_context_singleton_false
    (colour : α → Bool) (Adj : α → α → Prop)
    (hcross : ∀ u v, Adj u v → colour u ≠ colour v)
    (g h : (α → Bool) → Bool) (hgm : Mono g) (hhm : Mono h)
    (hsafe : ∀ u v, (g (pair u v) && h (pair u v)) = true → Adj u v)
    (a b : α) (ha : colour a = false) (hb : colour b = true)
    (hga : g (unit a) = true) (hgb : g (unit b) = true) :
    ∀ w, h (unit w) = false := by
  intro w
  cases hw : h (unit w) with
  | false => rfl
  | true =>
    have hadj (v : α) (hgv : g (unit v) = true) : Adj w v := by
      apply hsafe w v
      exact Bool.and_eq_true_iff.mpr
        ⟨hgm _ _ (unit_le_pair_right w v) hgv,
          hhm _ _ (unit_le_pair_left w v) hw⟩
    have hwa := hcross w a (hadj a hga)
    have hwb := hcross w b (hadj b hgb)
    cases hcw : colour w
    · exact False.elim (hwa (hcw.trans ha.symm))
    · exact False.elim (hwb (hcw.trans hb.symm))

lemma mixed_context_pair_inherited
    (colour : α → Bool) (Adj : α → α → Prop)
    (hcross : ∀ u v, Adj u v → colour u ≠ colour v)
    (g h : (α → Bool) → Bool) (hgm : Mono g) (hhm : Mono h)
    (hsafe : ∀ u v, (g (pair u v) && h (pair u v)) = true → Adj u v)
    (a b : α) (ha : colour a = false) (hb : colour b = true)
    (hga : g (unit a) = true) (hgb : g (unit b) = true)
    (u v : α) (hp : (g (pair u v) && h (pair u v)) = true) :
    h (pair u v) = true ∧ h (unit u) = false ∧ h (unit v) = false := by
  have hz := mixed_context_singleton_false colour Adj hcross g h hgm hhm hsafe a b ha hb hga hgb
  exact ⟨(Bool.and_eq_true_iff.mp hp).2, hz u, hz v⟩

end MixedSupport

namespace ProductiveOr

variable {n : ℕ}

def single (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def pair (a b : Fin n) : Fin n → Bool := fun j => decide (j = a ∨ j = b)

def Depends (colour : Fin n → Bool) (g : (Fin n → Bool) → Bool) (c : Bool) : Prop :=
  ∀ x y, (∀ i, colour i = c → x i = y i) → g x = g y

def Rectangular (colour : Fin n → Bool) (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : Fin n,
    colour a₁ = false → colour a₂ = false → colour b₁ = true → colour b₂ = true →
    g (pair a₁ b₁) = true → g (pair a₂ b₂) = true →
    g (pair a₁ b₂) = true ∧ g (pair a₂ b₁) = true

lemma pair_agrees_left (colour : Fin n → Bool) (a b₁ b₂ : Fin n)
    (hb₁ : colour b₁ = true) (hb₂ : colour b₂ = true) :
    ∀ j, colour j = false → pair a b₁ j = pair a b₂ j := by
  intro j hj
  have h₁ : j ≠ b₁ := by intro he; subst j; simp_all
  have h₂ : j ≠ b₂ := by intro he; subst j; simp_all
  simp [pair, h₁, h₂]

lemma pair_agrees_right (colour : Fin n → Bool) (a₁ a₂ b : Fin n)
    (ha₁ : colour a₁ = false) (ha₂ : colour a₂ = false) :
    ∀ j, colour j = true → pair a₁ b j = pair a₂ b j := by
  intro j hj
  have h₁ : j ≠ a₁ := by intro he; subst j; simp_all
  have h₂ : j ≠ a₂ := by intro he; subst j; simp_all
  simp [pair, h₁, h₂]

lemma depends_rectangular (colour : Fin n → Bool) (g : (Fin n → Bool) → Bool)
    (c : Bool) (hdep : Depends colour g c) : Rectangular colour g := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h₁ h₂
  cases c with
  | false =>
    have e₁ := hdep (pair a₁ b₁) (pair a₁ b₂) (pair_agrees_left colour a₁ b₁ b₂ hb₁ hb₂)
    have e₂ := hdep (pair a₂ b₂) (pair a₂ b₁) (pair_agrees_left colour a₂ b₂ b₁ hb₂ hb₁)
    exact ⟨e₁.symm.trans h₁, e₂.symm.trans h₂⟩
  | true =>
    have e₁ := hdep (pair a₂ b₂) (pair a₁ b₂) (pair_agrees_right colour a₂ a₁ b₂ ha₂ ha₁)
    have e₂ := hdep (pair a₁ b₁) (pair a₂ b₁) (pair_agrees_right colour a₁ a₂ b₁ ha₁ ha₂)
    exact ⟨e₁.symm.trans h₂, e₂.symm.trans h₁⟩

lemma singleton_colour_dependence
    (N : ℕ) (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ)
    (isAnd : ℕ → Bool) (colour : Fin n → Bool)
    (hinput : ∀ w (hw : w < n), f w = fun x => x ⟨w, hw⟩)
    (hgate : ∀ w, n ≤ w → w < N → a w < w ∧ b w < w ∧
      ∀ x, f w x = if isAnd w then f (a w) x && f (b w) x else f (a w) x || f (b w) x)
    (hproductive : ∀ w, n ≤ w → w < N → isAnd w = false →
      (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
    (hmono : ∀ w, n ≤ w → w < N → isAnd w = false →
      ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j) :
    ∀ w, w < N → ∀ i, f w (single i) = true → Depends colour (f w) (colour i) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw i hi
    by_cases hn : w < n
    · have he : (⟨w, hn⟩ : Fin n) = i := by
        simpa [hinput w hn, single] using hi
      intro x y hxy
      rw [hinput w hn]
      exact hxy ⟨w, hn⟩ (by rw [he])
    · have hng : n ≤ w := by omega
      obtain ⟨ha, hb, heval⟩ := hgate w hng hw
      cases hop : isAnd w with
      | false =>
        obtain ⟨⟨ia, hia⟩, ⟨ib, hib⟩⟩ := hproductive w hng hw hop
        have hwa : f w (single ia) = true := by simp [heval, hop, hia]
        have hwb : f w (single ib) = true := by simp [heval, hop, hib]
        have hca : colour ia = colour i := hmono w hng hw hop ia i hwa hi
        have hcb : colour ib = colour i := hmono w hng hw hop ib i hwb hi
        have hda := ih (a w) ha (lt_trans ha hw) ia hia
        have hdb := ih (b w) hb (lt_trans hb hw) ib hib
        intro x y hxy
        have ea := hda x y (fun j hj => hxy j (hj.trans hca))
        have eb := hdb x y (fun j hj => hxy j (hj.trans hcb))
        simp only [heval, hop, Bool.false_eq_true, ite_false, ea, eb]
      | true =>
        have hc : f (a w) (single i) = true ∧ f (b w) (single i) = true := by
          simpa [heval, hop] using hi
        have hda := ih (a w) ha (lt_trans ha hw) i hc.1
        have hdb := ih (b w) hb (lt_trans hb hw) i hc.2
        intro x y hxy
        have ea := hda x y hxy
        have eb := hdb x y hxy
        simp [heval, hop, ea, eb]

lemma all_wires_rectangular
    (N : ℕ) (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ)
    (isAnd : ℕ → Bool) (colour : Fin n → Bool)
    (hinput : ∀ w (hw : w < n), f w = fun x => x ⟨w, hw⟩)
    (hgate : ∀ w, n ≤ w → w < N → a w < w ∧ b w < w ∧
      ∀ x, f w x = if isAnd w then f (a w) x && f (b w) x else f (a w) x || f (b w) x)
    (hproductive : ∀ w, n ≤ w → w < N → isAnd w = false →
      (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
    (hmono : ∀ w, n ≤ w → w < N → isAnd w = false →
      ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j) :
    ∀ w, w < N → Rectangular colour (f w) := by
  have hdepends := singleton_colour_dependence N f a b isAnd colour hinput hgate hproductive hmono
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · have hs : f w (single ⟨w, hn⟩) = true := by simp [hinput w hn, single]
      exact depends_rectangular colour (f w) (colour ⟨w, hn⟩) (hdepends w hw ⟨w, hn⟩ hs)
    · have hng : n ≤ w := by omega
      obtain ⟨ha, hb, heval⟩ := hgate w hng hw
      cases hop : isAnd w with
      | false =>
        obtain ⟨⟨i, hi⟩, _⟩ := hproductive w hng hw hop
        have hs : f w (single i) = true := by simp [heval, hop, hi]
        exact depends_rectangular colour (f w) (colour i) (hdepends w hw i hs)
      | true =>
        have hra := ih (a w) ha (lt_trans ha hw)
        have hrb := ih (b w) hb (lt_trans hb hw)
        intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h₁ h₂
        have h₁' : f (a w) (pair a₁ b₁) = true ∧ f (b w) (pair a₁ b₁) = true := by
          simpa [heval, hop] using h₁
        have h₂' : f (a w) (pair a₂ b₂) = true ∧ f (b w) (pair a₂ b₂) = true := by
          simpa [heval, hop] using h₂
        have ra := hra a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h₁'.1 h₂'.1
        have rb := hrb a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h₁'.2 h₂'.2
        constructor
        · simp [heval, hop, ra.1, rb.1]
        · simp [heval, hop, ra.2, rb.2]

lemma rectangular_and (colour : Fin n → Bool) (f g : (Fin n → Bool) → Bool)
    (hf : Rectangular colour f) (hg : Rectangular colour g) :
    Rectangular colour (fun x => f x && g x) := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ h₁ h₂
  obtain ⟨hf₁, hg₁⟩ := Bool.and_eq_true_iff.mp h₁
  obtain ⟨hf₂, hg₂⟩ := Bool.and_eq_true_iff.mp h₂
  obtain ⟨hf₃, hf₄⟩ := hf a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hf₁ hf₂
  obtain ⟨hg₃, hg₄⟩ := hg a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hg₁ hg₂
  exact ⟨Bool.and_eq_true_iff.mpr ⟨hf₃, hg₃⟩, Bool.and_eq_true_iff.mpr ⟨hf₄, hg₄⟩⟩

def RelationRectangular {α β : Type*} (R : α → β → Prop) : Prop :=
  ∀ a₁ a₂ b₁ b₂, R a₁ b₁ → R a₂ b₂ → R a₁ b₂ ∧ R a₂ b₁

lemma rectangular_pullback {α β : Type*} (colour : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (hf : Rectangular colour f)
    (left : α → Fin n) (right : β → Fin n)
    (hl : ∀ a, colour (left a) = false) (hr : ∀ b, colour (right b) = true) :
    RelationRectangular (fun a b => f (pair (left a) (right b)) = true) := by
  intro a₁ a₂ b₁ b₂ h₁ h₂
  exact hf _ _ _ _ (hl a₁) (hl a₂) (hr b₁) (hr b₂) h₁ h₂

lemma rectangular_relation_star {α β : Type*} (R : α → β → Prop)
    (hrect : RelationRectangular R)
    (hno : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (a₀ : α) (b₀ : β) (h₀ : R a₀ b₀) :
    (∀ a b, R a b → a = a₀) ∨ (∀ a b, R a b → b = b₀) := by
  by_cases hleft : ∀ a b, R a b → a = a₀
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨a₁, b₁, h₁, ha₁⟩ := hleft
    right
    intro a b hab
    by_contra hbb
    have h₀b : R a₀ b := (hrect a₀ a b₀ b h₀ hab).1
    have h₁₀ : R a₁ b₀ := (hrect a₁ a₀ b₁ b₀ h₁ h₀).1
    have h₁b : R a₁ b := (hrect a₁ a b₁ b h₁ hab).1
    exact hno a₀ a₁ b₀ b (Ne.symm ha₁) (Ne.symm hbb) ⟨h₀, h₀b, h₁₀, h₁b⟩

lemma safe_rectangular_product_star {α β : Type*}
    (colour : Fin n → Bool) (f g : (Fin n → Bool) → Bool)
    (hf : Rectangular colour f) (hg : Rectangular colour g)
    (left : α → Fin n) (right : β → Fin n)
    (hl : ∀ a, colour (left a) = false) (hr : ∀ b, colour (right b) = true)
    (E : α → β → Prop)
    (hno : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (E a b ∧ E a b' ∧ E a' b ∧ E a' b'))
    (hsafe : ∀ a b, (f (pair (left a) (right b)) && g (pair (left a) (right b))) = true → E a b)
    (a₀ : α) (b₀ : β)
    (h₀ : (f (pair (left a₀) (right b₀)) && g (pair (left a₀) (right b₀))) = true) :
    (∀ a b, (f (pair (left a) (right b)) && g (pair (left a) (right b))) = true → a = a₀) ∨
    (∀ a b, (f (pair (left a) (right b)) && g (pair (left a) (right b))) = true → b = b₀) := by
  apply rectangular_relation_star _
    (rectangular_pullback colour _ (rectangular_and colour f g hf hg) left right hl hr) _ a₀ b₀ h₀
  intro a a' b b' haa hbb h
  exact hno a a' b b' haa hbb
    ⟨hsafe a b h.1, hsafe a b' h.2.1, hsafe a' b h.2.2.1, hsafe a' b' h.2.2.2⟩

end ProductiveOr

namespace Hall

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def C : Circuit :=
  ⟨[⟨.or, [2,3]⟩, ⟨.or, [4,5]⟩, ⟨.and, [0,0]⟩, ⟨.and, [1,1]⟩,
    ⟨.or, [9,6]⟩, ⟨.or, [8,7]⟩, ⟨.and, [10,11]⟩, ⟨.or, [0,1]⟩,
    ⟨.or, [6,7]⟩, ⟨.and, [13,14]⟩, ⟨.and, [12,15]⟩], 16⟩

abbrev neighbour (a : Fin 2) (b : Fin 4) : Prop := a.val = b.val / 2

def edge (a : Fin 2) (b : Fin 4) : Fin 6 → Bool :=
  fun i => decide (i = Fin.castAdd 4 a ∨ i = Fin.natAdd 2 b)

def bad (a : Fin 2) : Fin 6 → Bool :=
  fun i => decide (i = Fin.castAdd 4 a ∨ ∃ b : Fin 4, i = Fin.natAdd 2 b ∧ ¬ neighbour a b)

def eligible (a : Fin 2) (b : Fin 4) (j : Fin 11) : Prop :=
  (gateAt C j).op = .and ∧
  (C.wires (List.ofFn (edge a b))).getD (6+j) false = true ∧
  ∃ k : Fin 2,
    (C.wires (List.ofFn (bad a))).getD (opnd C j k) false = false ∧
    Fin.natAdd 2 b ∈ orIn 6 C (opnd C j k) ∧
    ∀ i ∈ orIn 6 C (opnd C j k), ∃ b' : Fin 4, i = Fin.natAdd 2 b' ∧ neighbour a b'

lemma model : IsAO2 6 C := by decide +kernel +revert

lemma count_zero : tCount 6 C (fun i => decide (2 ≤ i)) = 0 := by decide +kernel +revert

lemma computes : ∀ x : Fin 6 → Bool,
    circuitFun 6 C x = decide (∃ (a : Fin 2) (b : Fin 4), neighbour a b ∧
      x (Fin.castAdd 4 a) = true ∧ x (Fin.natAdd 2 b) = true) := by decide +kernel +revert

lemma no_four_cycle : ∀ (a a' : Fin 2) (b b' : Fin 4), a ≠ a' → b ≠ b' →
    ¬ (neighbour a b ∧ neighbour a b' ∧ neighbour a' b ∧ neighbour a' b') := by decide +kernel +revert

lemma served : ∀ (a : Fin 2) (b : Fin 4), neighbour a b →
    ∃ (j : Fin 11) (Q : Finset (Fin 4)), (gateAt C j).op = .or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, neighbour a b') ∧
      ∀ x : Fin 6 → Bool,
        (C.wires (List.ofFn x)).getD (6+j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true) := by
  intro a b hab
  let Q := Finset.univ.filter (neighbour a)
  refine ⟨⟨a.val, by have := a.isLt; omega⟩, Q, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases a <;> rfl
  · fin_cases a <;> decide +kernel +revert
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ b,hab⟩
  · intro b' hb'
    exact (Finset.mem_filter.mp hb').2
  · fin_cases a <;> decide +kernel +revert

lemma edge_active : ∀ j : Fin 11, ∃ (a : Fin 2) (b : Fin 4), neighbour a b ∧
    (C.wires (List.ofFn (edge a b))).getD (6+j) false = true := by decide +kernel +revert

lemma first_eligible : ∀ j : Fin 11, eligible 0 0 j ↔ j.val = 6 := by
  intro j
  fin_cases j <;> simp [eligible, C, gateAt, opnd] <;> decide +kernel +revert

lemma second_eligible : ∀ j : Fin 11, eligible 1 2 j ↔ j.val = 6 := by
  intro j
  fin_cases j <;> simp [eligible, C, gateAt, opnd] <;> decide +kernel +revert

lemma no_injective_assignment :
    ¬ ∃ f : Fin 2 → Fin 11, Function.Injective f ∧ eligible 0 0 (f 0) ∧ eligible 1 2 (f 1) := by
  rintro ⟨f, hi, h0, h1⟩
  have e0 := (first_eligible (f 0)).mp h0
  have e1 := (second_eligible (f 1)).mp h1
  have he : f 0 = f 1 := Fin.ext (e0.trans e1.symm)
  have hc := hi he
  exact (by decide : (0 : Fin 2) ≠ 1) hc

end Hall

namespace CrossRectangleCover

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def NoFour (R : α → β → Prop) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' → ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b')

def Cross (U0 U A : Finset α) (V0 V B : Finset β) (a : α) (b : β) : Prop :=
  (a ∈ U0 ∧ b ∈ V0) ∨ (a ∈ A ∧ b ∈ V) ∨ (a ∈ U ∧ b ∈ B)

lemma rectangle_cover (R : α → β → Prop) (hno : NoFour R)
    (U : Finset α) (V : Finset β)
    (hr : ∀ a ∈ U, ∀ b ∈ V, R a b) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a ∈ U, ∀ b ∈ V, a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 1 := by
  by_cases hu : U.card ≤ 1
  · exact ⟨U, ∅, fun a ha b hb => Or.inl ha, by simpa using hu⟩
  · have hv : V.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b hb b' hb'
      by_contra hbb
      obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
      exact hno a a' b b' haa hbb ⟨hr a ha b hb, hr a ha b' hb', hr a' ha' b hb, hr a' ha' b' hb'⟩
    exact ⟨∅, V, fun a ha b hb => Or.inr hb, by simpa using hv⟩

lemma two_rectangles_cover (R : α → β → Prop) (hno : NoFour R)
    (U0 U1 : Finset α) (V0 V1 : Finset β)
    (hr0 : ∀ a ∈ U0, ∀ b ∈ V0, R a b)
    (hr1 : ∀ a ∈ U1, ∀ b ∈ V1, R a b)
    (hcover : ∀ a b, R a b → (a ∈ U0 ∧ b ∈ V0) ∨ (a ∈ U1 ∧ b ∈ V1)) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, R a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨P0, Q0, hc0, hb0⟩ := rectangle_cover R hno U0 V0 hr0
  obtain ⟨P1, Q1, hc1, hb1⟩ := rectangle_cover R hno U1 V1 hr1
  refine ⟨P0 ∪ P1, Q0 ∪ Q1, ?_, ?_⟩
  · intro a b hab
    rcases hcover a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hc0 a ha b hb with hp | hq
      · exact Or.inl (Finset.mem_union_left P1 hp)
      · exact Or.inr (Finset.mem_union_left Q1 hq)
    · rcases hc1 a ha b hb with hp | hq
      · exact Or.inl (Finset.mem_union_right P0 hp)
      · exact Or.inr (Finset.mem_union_right Q0 hq)
  · have hp := Finset.card_union_le P0 P1
    have hq := Finset.card_union_le Q0 Q1
    omega

lemma cross_baseline_cover (U0 U A : Finset α) (V0 V B : Finset β)
    (hu0 : U0 ⊆ U) (hv0 : V0 ⊆ V) (haU : A ⊆ U) (hbV : B ⊆ V)
    (hno : NoFour (Cross U0 U A V0 V B)) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, Cross U0 U A V0 V B a b → a ∈ P ∨ b ∈ Q) ∧
      P.card + Q.card ≤ 2 := by
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      refine ⟨{a}, {b}, ?_, by simp⟩
      intro u v huv
      by_cases hua : u = a
      · exact Or.inl (by simp [hua])
      by_cases hvb : v = b
      · exact Or.inr (by simp [hvb])
      have huv' : u ∈ U ∧ v ∈ V := by
        rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
        · exact ⟨hu0 hu, hv0 hv⟩
        · exact ⟨haU hu, hv⟩
        · exact ⟨hu, hbV hv⟩
      exact False.elim (hno a u b v (Ne.symm hua) (Ne.symm hvb)
        ⟨Or.inr (Or.inl ⟨ha, hbV hb⟩), Or.inr (Or.inl ⟨ha, huv'.2⟩),
          Or.inr (Or.inr ⟨huv'.1, hb⟩), huv⟩)
    · apply two_rectangles_cover (Cross U0 U A V0 V B) hno U0 A V0 V
      · intro a ha b hb
        exact Or.inl ⟨ha, hb⟩
      · intro a ha b hb
        exact Or.inr (Or.inl ⟨ha, hb⟩)
      · intro a b hab
        rcases hab with h0 | hA | hB
        · exact Or.inl h0
        · exact Or.inr hA
        · exact (hb ⟨b, hB.2⟩).elim
  · apply two_rectangles_cover (Cross U0 U A V0 V B) hno U0 U V0 B
    · intro a ha b hb
      exact Or.inl ⟨ha, hb⟩
    · intro a ha b hb
      exact Or.inr (Or.inr ⟨ha, hb⟩)
    · intro a b hab
      rcases hab with h0 | hA | hB
      · exact Or.inl h0
      · exact (ha ⟨a, hA.1⟩).elim
      · exact Or.inr hB

lemma cross_baseline_cover_of_subrelation (R : α → β → Prop) (hno : NoFour R)
    (U0 U A : Finset α) (V0 V B : Finset β)
    (hu0 : U0 ⊆ U) (hv0 : V0 ⊆ V) (haU : A ⊆ U) (hbV : B ⊆ V)
    (hsub : ∀ a b, Cross U0 U A V0 V B a b → R a b) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, Cross U0 U A V0 V B a b → a ∈ P ∨ b ∈ Q) ∧
      P.card + Q.card ≤ 2 := by
  apply cross_baseline_cover U0 U A V0 V B hu0 hv0 haU hbV
  intro a a' b b' haa hbb h
  exact hno a a' b b' haa hbb
    ⟨hsub a b h.1, hsub a b' h.2.1, hsub a' b h.2.2.1, hsub a' b' h.2.2.2⟩

end CrossRectangleCover

namespace BooleanFactorCover

open CrossRectangleCover

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def support (f : α → Bool) : Finset α := Finset.univ.filter (fun a => f a = true)

lemma mixed_factor_cover (R : α → β → Prop) (hno : NoFour R)
    (g : α → Bool → Bool) (h : β → Bool → Bool) (u : α → Bool) (v : β → Bool)
    (hg : ∀ a, g a false = true → g a true = true)
    (hh : ∀ b, h b false = true → h b true = true)
    (hr : ∀ a b, R a b ↔ g a (u a || v b) && h b (u a || v b) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, R a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  let U0 := support (fun a => g a false)
  let U := support (fun a => g a true)
  let A := support (fun a => u a && g a true)
  let V0 := support (fun b => h b false)
  let V := support (fun b => h b true)
  let B := support (fun b => v b && h b true)
  have hu0 : U0 ⊆ U := by simpa [U0, U, support, Finset.subset_iff] using hg
  have hv0 : V0 ⊆ V := by simpa [V0, V, support, Finset.subset_iff] using hh
  have haU : A ⊆ U := by simp [A, U, support, Finset.subset_iff]
  have hbV : B ⊆ V := by simp [B, V, support, Finset.subset_iff]
  have heq : ∀ a b, R a b ↔ Cross U0 U A V0 V B a b := by
    intro a b
    rw [hr]
    simp only [Cross, U0, U, A, V0, V, B, support, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true]
    have hga := hg a
    have hhb := hh b
    cases hu : u a <;> cases hv : v b <;> simp [hu, hv] <;> tauto
  obtain ⟨P, Q, hc, hcard⟩ := cross_baseline_cover U0 U A V0 V B hu0 hv0 haU hbV
    (by intro a a' b b' haa hbb hfour
        exact hno a a' b b' haa hbb
          ⟨(heq a b).mpr hfour.1, (heq a b').mpr hfour.2.1,
           (heq a' b).mpr hfour.2.2.1, (heq a' b').mpr hfour.2.2.2⟩)
  exact ⟨P, Q, fun a b hab => hc a b ((heq a b).mp hab), hcard⟩

lemma one_sided_factor_cover (R : α → β → Prop) (hno : NoFour R)
    (g : α → Bool → Bool) (h : β → Bool)
    (u v : α → Bool) (w : β → Bool)
    (hg : ∀ a, g a false = true → g a true = true)
    (hr : ∀ a b, R a b ↔ g a (u a || (v a && w b)) && h b = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, R a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  let U0 := support (fun a => g a false || (u a && g a true))
  let U1 := support (fun a => v a && g a true)
  let V0 := support h
  let V1 := support (fun b => w b && h b)
  have heq : ∀ a b, R a b ↔ (a ∈ U0 ∧ b ∈ V0) ∨ (a ∈ U1 ∧ b ∈ V1) := by
    intro a b
    rw [hr]
    simp only [U0, U1, V0, V1, support, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, Bool.or_eq_true]
    have hga := hg a
    cases hu : u a <;> cases hv : v a <;> cases hw : w b <;>
      simp [hu, hv, hw] <;> tauto
  exact two_rectangles_cover R hno U0 U1 V0 V1
    (fun a ha b hb => (heq a b).mpr (Or.inl ⟨ha, hb⟩))
    (fun a ha b hb => (heq a b).mpr (Or.inr ⟨ha, hb⟩))
    (fun a b hab => (heq a b).mp hab)

lemma empty_support_factor_cover (R : α → β → Prop) (hno : NoFour R)
    (g u v : α → Bool) (h s t : β → Bool)
    (hr : ∀ a b, R a b ↔ ((u a && s b) || (v a && t b)) && g a && h b = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, R a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  let U0 := support (fun a => u a && g a)
  let U1 := support (fun a => v a && g a)
  let V0 := support (fun b => s b && h b)
  let V1 := support (fun b => t b && h b)
  have heq : ∀ a b, R a b ↔ (a ∈ U0 ∧ b ∈ V0) ∨ (a ∈ U1 ∧ b ∈ V1) := by
    intro a b
    rw [hr]
    simp only [U0, U1, V0, V1, support, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, Bool.or_eq_true]
    tauto
  exact two_rectangles_cover R hno U0 U1 V0 V1
    (fun a ha b hb => (heq a b).mpr (Or.inl ⟨ha, hb⟩))
    (fun a ha b hb => (heq a b).mpr (Or.inr ⟨ha, hb⟩))
    (fun a b hab => (heq a b).mp hab)

end BooleanFactorCover

end PEqualNP.Outside.L_meta_4970.H9RedTeam
