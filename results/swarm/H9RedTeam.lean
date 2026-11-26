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


namespace CutPolicy

variable {n : ℕ}

def single (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def PolicyDepends (colour : Fin n → Bool) (allow : Bool → Bool)
    (f : (Fin n → Bool) → Bool → Bool) (c : Bool) : Prop :=
  ∀ x y z z', (∀ i, colour i = c → x i = y i) →
    (allow c = true → z = z') → f x z = f y z'

def SeedMonotone (f : (Fin n → Bool) → Bool → Bool) : Prop :=
  ∀ x, f x false = true → f x true = true

def Separated (colour : Fin n → Bool) (allow : Bool → Bool)
    (f : (Fin n → Bool) → Bool → Bool) : Prop :=
  ∃ g h : (Fin n → Bool) → Bool → Bool,
    PolicyDepends colour allow g false ∧ PolicyDepends colour allow h true ∧
    SeedMonotone g ∧ SeedMonotone h ∧ ∀ x z, f x z = (g x z && h x z)

lemma separated_of_dep (colour : Fin n → Bool) (allow : Bool → Bool)
    (f : (Fin n → Bool) → Bool → Bool) (c : Bool)
    (hd : PolicyDepends colour allow f c) (hm : SeedMonotone f) :
    Separated colour allow f := by
  cases c with
  | false =>
    refine ⟨f, fun _ _ => true, hd, ?_, hm, ?_, ?_⟩
    · intro x y z z' hxy hzz; rfl
    · intro x hx; rfl
    · intro x z; simp
  | true =>
    refine ⟨fun _ _ => true, f, ?_, hd, ?_, hm, ?_⟩
    · intro x y z z' hxy hzz; rfl
    · intro x hx; rfl
    · intro x z; simp

lemma separated_and (colour : Fin n → Bool) (allow : Bool → Bool)
    (f k : (Fin n → Bool) → Bool → Bool)
    (hf : Separated colour allow f) (hk : Separated colour allow k) :
    Separated colour allow (fun x z => f x z && k x z) := by
  obtain ⟨g₁,h₁,dg₁,dh₁,mg₁,mh₁,e₁⟩ := hf
  obtain ⟨g₂,h₂,dg₂,dh₂,mg₂,mh₂,e₂⟩ := hk
  refine ⟨fun x z => g₁ x z && g₂ x z, fun x z => h₁ x z && h₂ x z, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z z' hxy hzz
    dsimp only
    rw [dg₁ x y z z' hxy hzz, dg₂ x y z z' hxy hzz]
  · intro x y z z' hxy hzz
    dsimp only
    rw [dh₁ x y z z' hxy hzz, dh₂ x y z z' hxy hzz]
  · intro x hx
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨mg₁ x ha,mg₂ x hb⟩
  · intro x hx
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hx
    exact Bool.and_eq_true_iff.mpr ⟨mh₁ x ha,mh₂ x hb⟩
  · intro x z
    dsimp only
    rw [e₁,e₂]
    simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

section Wire

variable (N cut : ℕ) (F : ℕ → (Fin n → Bool) → Bool → Bool)
  (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
  (colour : Fin n → Bool) (seed : (Fin n → Bool) → Bool)
  (hinput : ∀ w (hw : w < n) x z, F w x z = x ⟨w,hw⟩)
  (hcut : ∀ x z, F cut x z = z)
  (hgate : ∀ w, n ≤ w → w < N → w ≠ cut → a w < w ∧ b w < w ∧
    ∀ x z, F w x z = if isAnd w then F (a w) x z && F (b w) x z
      else F (a w) x z || F (b w) x z)
  (hactual : ∀ w, w < N → ∀ x, f w x = F w x (seed x))
  (hproductive : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
    (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
  (hmono : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
    ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j)

include hinput hcut hgate hactual hproductive hmono

lemma cut_singleton_dependence (allow : Bool → Bool)
    (hsupport : ∀ i, seed (single i) = true → allow (colour i) = true) :
    ∀ w, w < N → ∀ i, f w (single i) = true → PolicyDepends colour allow (F w) (colour i) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw i hi
    by_cases hc : w = cut
    · subst w
      have ht : seed (single i) = true := by simpa only [hactual cut hw, hcut] using hi
      intro x y z z' hxy hzz
      rw [hcut,hcut]
      exact hzz (hsupport i ht)
    · by_cases hn : w < n
      · have he : (⟨w,hn⟩ : Fin n) = i := by
          simpa [hactual w hw,hinput w hn,single] using hi
        intro x y z z' hxy hzz
        rw [hinput w hn,hinput w hn]
        exact hxy ⟨w,hn⟩ (by rw [he])
      · have hng : n ≤ w := by omega
        obtain ⟨ha,hb,heval⟩ := hgate w hng hw hc
        have hsem (x : Fin n → Bool) : f w x =
            if isAnd w then f (a w) x && f (b w) x else f (a w) x || f (b w) x := by
          simpa only [← hactual w hw, ← hactual (a w) (lt_trans ha hw),
            ← hactual (b w) (lt_trans hb hw)] using heval x (seed x)
        cases hop : isAnd w with
        | false =>
          obtain ⟨⟨ia,hia⟩,⟨ib,hib⟩⟩ := hproductive w hng hw hc hop
          have hwa : f w (single ia) = true := by simp [hsem,hop,hia]
          have hwb : f w (single ib) = true := by simp [hsem,hop,hib]
          have hca := hmono w hng hw hc hop ia i hwa hi
          have hcb := hmono w hng hw hc hop ib i hwb hi
          have hda : PolicyDepends colour allow (F (a w)) (colour i) := by
            simpa only [hca] using ih (a w) ha (lt_trans ha hw) ia hia
          have hdb : PolicyDepends colour allow (F (b w)) (colour i) := by
            simpa only [hcb] using ih (b w) hb (lt_trans hb hw) ib hib
          intro x y z z' hxy hzz
          have ea := hda x y z z' hxy hzz
          have eb := hdb x y z z' hxy hzz
          simp [heval,hop,ea,eb]
        | true =>
          have hh : f (a w) (single i) = true ∧ f (b w) (single i) = true := by
            simpa [hsem,hop] using hi
          have hda := ih (a w) ha (lt_trans ha hw) i hh.1
          have hdb := ih (b w) hb (lt_trans hb hw) i hh.2
          intro x y z z' hxy hzz
          have ea := hda x y z z' hxy hzz
          have eb := hdb x y z z' hxy hzz
          simp [heval,hop,ea,eb]

omit hactual hproductive hmono in
lemma cut_seed_monotone : ∀ w, w < N → SeedMonotone (F w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hc : w = cut
    · subst w
      simp [hcut]
    · by_cases hn : w < n
      · simpa only [hinput w hn] using hx
      · have hng : n ≤ w := by omega
        obtain ⟨ha,hb,heval⟩ := hgate w hng hw hc
        have hma := ih (a w) ha (lt_trans ha hw) x
        have hmb := ih (b w) hb (lt_trans hb hw) x
        cases hop : isAnd w with
        | false =>
          have hh : F (a w) x false = true ∨ F (b w) x false = true := by simpa [heval,hop] using hx
          rcases hh with hh | hh
          · simp [heval,hop,hma hh]
          · simp [heval,hop,hmb hh]
        | true =>
          have hh : F (a w) x false = true ∧ F (b w) x false = true := by simpa [heval,hop] using hx
          simp [heval,hop,hma hh.1,hmb hh.2]

lemma cut_separated (allow : Bool → Bool)
    (hsupport : ∀ i, seed (single i) = true → allow (colour i) = true)
    (hallow : allow false = true ∨ allow true = true) :
    ∀ w, w < N → Separated colour allow (F w) := by
  have hdep := cut_singleton_dependence N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono allow hsupport
  have hmon := cut_seed_monotone N cut F a b isAnd hinput hcut hgate
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hc : w = cut
    · subst w
      rcases hallow with hallow | hallow
      · apply separated_of_dep colour allow (F cut) false _ (hmon cut hw)
        intro x y z z' hxy hzz
        rw [hcut,hcut]
        exact hzz hallow
      · apply separated_of_dep colour allow (F cut) true _ (hmon cut hw)
        intro x y z z' hxy hzz
        rw [hcut,hcut]
        exact hzz hallow
    · by_cases hn : w < n
      · have hi : f w (single ⟨w,hn⟩) = true := by simp [hactual w hw,hinput w hn,single]
        exact separated_of_dep colour allow (F w) (colour ⟨w,hn⟩) (hdep w hw ⟨w,hn⟩ hi) (hmon w hw)
      · have hng : n ≤ w := by omega
        obtain ⟨ha,hb,heval⟩ := hgate w hng hw hc
        cases hop : isAnd w with
        | false =>
          obtain ⟨⟨i,hi⟩,_⟩ := hproductive w hng hw hc hop
          have hi' : F (a w) (single i) (seed (single i)) = true := by
            simpa only [← hactual (a w) (lt_trans ha hw)] using hi
          have hw' : f w (single i) = true := by simp [hactual w hw,heval,hop,hi']
          exact separated_of_dep colour allow (F w) (colour i) (hdep w hw i hw') (hmon w hw)
        | true =>
          have he : F w = fun x z => F (a w) x z && F (b w) x z := by funext x z; simp [heval,hop]
          rw [he]
          exact separated_and colour allow _ _ (ih (a w) ha (lt_trans ha hw)) (ih (b w) hb (lt_trans hb hw))

omit hcut hactual hproductive hmono in
lemma cut_independent_before : ∀ w, w < cut → w < N → ∀ x z z', F w x z = F w x z' := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hc hw x z z'
    by_cases hn : w < n
    · rw [hinput w hn,hinput w hn]
    · obtain ⟨ha,hb,heval⟩ := hgate w (by omega) hw (by omega)
      have ea := ih (a w) ha (lt_trans ha hc) (lt_trans ha hw) x z z'
      have eb := ih (b w) hb (lt_trans hb hc) (lt_trans hb hw) x z z'
      simp only [heval,ea,eb]

lemma cut_separated_before : ∀ w, w < cut → w < N →
    Separated colour (fun _ => false) (F w) := by
  intro w hc hw
  have hs := cut_separated N cut F f a b isAnd colour seed hinput hcut hgate
    hactual hproductive hmono (fun _ => true) (fun _ _ => rfl) (Or.inl rfl) w hw
  obtain ⟨g,h,dg,dh,mg,mh,he⟩ := hs
  have hind := cut_independent_before N cut F a b isAnd hinput hgate w hc hw
  refine ⟨fun x _ => g x false, fun x _ => h x false, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z z' hxy hzz
    exact dg x y false false hxy (fun _ => rfl)
  · intro x y z z' hxy hzz
    exact dh x y false false hxy (fun _ => rfl)
  · intro x hx; exact hx
  · intro x hx; exact hx
  · intro x z
    exact (hind x z false).trans (he x false)

lemma actual_singleton_dependence_before : ∀ w, w < cut → w < N → ∀ i,
    f w (single i) = true →
      PolicyDepends colour (fun _ => false) (fun x _ => f w x) (colour i) := by
  intro w hc hw i hi
  have hd := cut_singleton_dependence N cut F f a b isAnd colour seed hinput hcut hgate
    hactual hproductive hmono (fun _ => true) (fun _ _ => rfl) w hw i hi
  have hind := cut_independent_before N cut F a b isAnd hinput hgate w hc hw
  intro x y z z' hxy hzz
  change f w x = f w y
  rw [hactual w hw,hactual w hw]
  exact (hind x (seed x) (seed y)).trans (hd x y (seed y) (seed y) hxy (fun _ => rfl))

omit hactual hproductive hmono in
lemma cut_zero_false : ∀ w, w < N → F w (fun _ => false) false = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hc : w = cut
    · subst w; exact hcut _ false
    · by_cases hn : w < n
      · exact hinput w hn _ false
      · obtain ⟨ha,hb,heval⟩ := hgate w (by omega) hw hc
        have ea := ih (a w) ha (lt_trans ha hw)
        have eb := ih (b w) hb (lt_trans hb hw)
        simp [heval,ea,eb]

omit hproductive hmono in
lemma actual_zero_false_before : ∀ w, w < cut → w < N → f w (fun _ => false) = false := by
  intro w hc hw
  rw [hactual w hw]
  exact (cut_independent_before N cut F a b isAnd hinput hgate w hc hw _ _ false).trans
    (cut_zero_false N cut F a b isAnd hinput hcut hgate w hw)

end Wire

end CutPolicy

namespace CutPolicy

variable {n : ℕ}

def EmptySeparated (colour : Fin n → Bool)
    (f : (Fin n → Bool) → Bool → Bool) : Prop :=
  ∃ g h : (Fin n → Bool) → Bool, ∃ useSeed : Bool,
    PolicyDepends colour (fun _ => false) (fun x _ => g x) false ∧
    PolicyDepends colour (fun _ => false) (fun x _ => h x) true ∧
    ∀ x z, f x z = ((g x && h x) && if useSeed then z else true)

lemma empty_separated_of_separated (colour : Fin n → Bool)
    (f : (Fin n → Bool) → Bool → Bool)
    (hf : Separated colour (fun _ => false) f) : EmptySeparated colour f := by
  obtain ⟨g,h,dg,dh,mg,mh,he⟩ := hf
  refine ⟨fun x => g x true, fun x => h x true, false, ?_, ?_, ?_⟩
  · intro x y z z' hxy hzz
    exact dg x y true true hxy (by simp)
  · intro x y z z' hxy hzz
    exact dh x y true true hxy (by simp)
  · intro x z
    have eg := dg x x z true (fun _ _ => rfl) (by simp)
    have eh := dh x x z true (fun _ _ => rfl) (by simp)
    simp [he, eg, eh]

lemma empty_separated_and (colour : Fin n → Bool)
    (f k : (Fin n → Bool) → Bool → Bool)
    (hf : EmptySeparated colour f) (hk : EmptySeparated colour k) :
    EmptySeparated colour (fun x z => f x z && k x z) := by
  obtain ⟨g₁,h₁,u₁,dg₁,dh₁,e₁⟩ := hf
  obtain ⟨g₂,h₂,u₂,dg₂,dh₂,e₂⟩ := hk
  refine ⟨fun x => g₁ x && g₂ x, fun x => h₁ x && h₂ x, u₁ || u₂, ?_, ?_, ?_⟩
  · intro x y z z' hxy hzz
    dsimp only
    exact congrArg₂ Bool.and (dg₁ x y z z' hxy hzz) (dg₂ x y z z' hxy hzz)
  · intro x y z z' hxy hzz
    dsimp only
    exact congrArg₂ Bool.and (dh₁ x y z z' hxy hzz) (dh₂ x y z z' hxy hzz)
  · intro x z
    dsimp only
    rw [e₁,e₂]
    cases u₁ <;> cases u₂ <;> cases z <;> simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

lemma empty_cut_factorization
    (N cut : ℕ) (F : ℕ → (Fin n → Bool) → Bool → Bool)
    (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (colour : Fin n → Bool) (seed : (Fin n → Bool) → Bool)
    (hinput : ∀ w (hw : w < n) x z, F w x z = x ⟨w,hw⟩)
    (hcut : ∀ x z, F cut x z = z)
    (hgate : ∀ w, n ≤ w → w < N → w ≠ cut → a w < w ∧ b w < w ∧
      ∀ x z, F w x z = if isAnd w then F (a w) x z && F (b w) x z
        else F (a w) x z || F (b w) x z)
    (hactual : ∀ w, w < N → ∀ x, f w x = F w x (seed x))
    (hproductive : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
    (hmono : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j)
    (hempty : ∀ i, seed (single i) = false) :
    ∀ w, w < N → EmptySeparated colour (F w) := by
  have hdep := cut_singleton_dependence N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono (fun _ => false)
    (by intro i hi; simp [hempty i] at hi)
  have hmon := cut_seed_monotone N cut F a b isAnd hinput hcut hgate
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hc : w = cut
    · subst w
      refine ⟨fun _ => true, fun _ => true, true, ?_, ?_, ?_⟩
      · intro x y z z' hxy hzz; rfl
      · intro x y z z' hxy hzz; rfl
      · intro x z; simp [hcut]
    · by_cases hn : w < n
      · have hi : f w (single ⟨w,hn⟩) = true := by simp [hactual w hw,hinput w hn,single]
        exact empty_separated_of_separated colour (F w)
          (separated_of_dep colour (fun _ => false) (F w) (colour ⟨w,hn⟩)
            (hdep w hw ⟨w,hn⟩ hi) (hmon w hw))
      · have hng : n ≤ w := by omega
        obtain ⟨ha,hb,heval⟩ := hgate w hng hw hc
        cases hop : isAnd w with
        | false =>
          obtain ⟨⟨i,hi⟩,_⟩ := hproductive w hng hw hc hop
          have hi' : F (a w) (single i) (seed (single i)) = true := by
            simpa only [← hactual (a w) (lt_trans ha hw)] using hi
          have hw' : f w (single i) = true := by simp [hactual w hw,heval,hop,hi']
          exact empty_separated_of_separated colour (F w)
            (separated_of_dep colour (fun _ => false) (F w) (colour i)
              (hdep w hw i hw') (hmon w hw))
        | true =>
          have he : F w = fun x z => F (a w) x z && F (b w) x z := by
            funext x z; simp [heval,hop]
          rw [he]
          exact empty_separated_and colour _ _
            (ih (a w) ha (lt_trans ha hw)) (ih (b w) hb (lt_trans hb hw))

end CutPolicy

namespace CutPolicy

variable {n : ℕ}

def Pure (colour : Fin n → Bool) (f : (Fin n → Bool) → Bool) (c : Bool) : Prop :=
  ∀ x y, (∀ i, colour i = c → x i = y i) → f x = f y

def PlainSeparated (colour : Fin n → Bool) (c : Bool)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ g h : (Fin n → Bool) → Bool,
    Pure colour g c ∧ Pure colour h (!c) ∧ ∀ x, f x = (g x && h x)

lemma pure_opposite_singleton (colour : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (c : Bool) (i : Fin n)
    (hcolour : colour i ≠ c) (hpure : Pure colour f c)
    (hzero : f (fun _ => false) = false) : f (single i) = false := by
  rw [hpure (single i) (fun _ => false) ?_, hzero]
  intro j hj
  have hji : j ≠ i := by intro he; subst j; exact hcolour hj
  simp [single, hji]

lemma mixed_seed_decomposition (colour : Fin n → Bool)
    (u v seed : (Fin n → Bool) → Bool)
    (hseed : ∀ x, seed x = (u x || v x))
    (hup : ∀ i, u (single i) = true → Pure colour u (colour i))
    (hvp : ∀ i, v (single i) = true → Pure colour v (colour i))
    (hu0 : u (fun _ => false) = false) (hv0 : v (fun _ => false) = false)
    (hleft : ∃ i, colour i = false ∧ seed (single i) = true)
    (hright : ∃ i, colour i = true ∧ seed (single i) = true) :
    ∃ g h : (Fin n → Bool) → Bool,
      Pure colour g false ∧ Pure colour h true ∧ ∀ x, seed x = (g x || h x) := by
  obtain ⟨i, hi, hsi⟩ := hleft
  obtain ⟨j, hj, hsj⟩ := hright
  have hsi' : u (single i) = true ∨ v (single i) = true := by simpa [hseed] using hsi
  have hsj' : u (single j) = true ∨ v (single j) = true := by simpa [hseed] using hsj
  rcases hsi' with hui | hvi
  · have hp : Pure colour u false := by simpa [hi] using hup i hui
    rcases hsj' with huj | hvj
    · have hz := pure_opposite_singleton colour u false j (by simp [hj]) hp hu0
      simp [hz] at huj
    · exact ⟨u,v,hp,by simpa [hj] using hvp j hvj,hseed⟩
  · have hp : Pure colour v false := by simpa [hi] using hvp i hvi
    rcases hsj' with huj | hvj
    · exact ⟨v,u,hp,by simpa [hj] using hup j huj,fun x => by rw [hseed]; exact Bool.or_comm _ _⟩
    · have hz := pure_opposite_singleton colour v false j (by simp [hj]) hp hv0
      simp [hz] at hvj

lemma one_colour_seed_decomposition (colour : Fin n → Bool) (c : Bool)
    (u v seed : (Fin n → Bool) → Bool)
    (hseed : ∀ x, seed x = (u x || v x))
    (hup : ∀ i, u (single i) = true → Pure colour u (colour i))
    (hvp : ∀ i, v (single i) = true → Pure colour v (colour i))
    (hus : PlainSeparated colour c u) (hvs : PlainSeparated colour c v)
    (hpos : ∃ i, colour i = c ∧ seed (single i) = true) :
    ∃ g h k : (Fin n → Bool) → Bool,
      Pure colour g c ∧ Pure colour h c ∧ Pure colour k (!c) ∧
      ∀ x, seed x = (g x || (h x && k x)) := by
  obtain ⟨i,hi,hsi⟩ := hpos
  have hsi' : u (single i) = true ∨ v (single i) = true := by simpa [hseed] using hsi
  rcases hsi' with hui | hvi
  · obtain ⟨h,k,hh,hk,he⟩ := hvs
    exact ⟨u,h,k,by simpa [hi] using hup i hui,hh,hk,fun x => by rw [hseed,he]⟩
  · obtain ⟨h,k,hh,hk,he⟩ := hus
    refine ⟨v,h,k,by simpa [hi] using hvp i hvi,hh,hk,?_⟩
    intro x
    rw [hseed,he]
    exact Bool.or_comm _ _

lemma separated_seed_decomposition (colour : Fin n → Bool)
    (u v seed : (Fin n → Bool) → Bool)
    (hseed : ∀ x, seed x = (u x || v x))
    (hus : PlainSeparated colour false u) (hvs : PlainSeparated colour false v) :
    ∃ g h k m : (Fin n → Bool) → Bool,
      Pure colour g false ∧ Pure colour h true ∧
      Pure colour k false ∧ Pure colour m true ∧
      ∀ x, seed x = ((g x && h x) || (k x && m x)) := by
  obtain ⟨g,h,hg,hh,hu⟩ := hus
  obtain ⟨k,m,hk,hm,hv⟩ := hvs
  exact ⟨g,h,k,m,hg,hh,hk,hm,fun x => by rw [hseed,hu,hv]⟩

end CutPolicy

namespace CutPolicy

variable {n : ℕ}

variable (N cut : ℕ) (F : ℕ → (Fin n → Bool) → Bool → Bool)
  (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
  (colour : Fin n → Bool) (seed : (Fin n → Bool) → Bool)
  (hinput : ∀ w (hw : w < n) x z, F w x z = x ⟨w,hw⟩)
  (hcut : ∀ x z, F cut x z = z)
  (hgate : ∀ w, n ≤ w → w < N → w ≠ cut → a w < w ∧ b w < w ∧
    ∀ x z, F w x z = if isAnd w then F (a w) x z && F (b w) x z
      else F (a w) x z || F (b w) x z)
  (hactual : ∀ w, w < N → ∀ x, f w x = F w x (seed x))
  (hproductive : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
    (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
  (hmono : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
    ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j)

include hinput hcut hgate hactual hproductive hmono

lemma actual_plain_separated_before (w : ℕ) (hc : w < cut) (hw : w < N) :
    PlainSeparated colour false (f w) := by
  obtain ⟨g,h,dg,dh,mg,mh,he⟩ := cut_separated_before N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono w hc hw
  have hind := cut_independent_before N cut F a b isAnd hinput hgate w hc hw
  refine ⟨fun x => g x false, fun x => h x false, ?_, ?_, ?_⟩
  · intro x y hxy
    exact dg x y false false hxy (fun _ => rfl)
  · intro x y hxy
    exact dh x y false false hxy (fun _ => rfl)
  · intro x
    rw [hactual w hw]
    exact (hind x (seed x) false).trans (he x false)

lemma actual_plain_separated_before_colour (c : Bool) (w : ℕ) (hc : w < cut) (hw : w < N) :
    PlainSeparated colour c (f w) := by
  have hs := actual_plain_separated_before N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono w hc hw
  cases c with
  | false => exact hs
  | true =>
    obtain ⟨g,h,hg,hh,he⟩ := hs
    refine ⟨h,g,hh,hg,?_⟩
    intro x
    rw [he]
    exact Bool.and_comm _ _

lemma actual_pure_before (w : ℕ) (hc : w < cut) (hw : w < N)
    (i : Fin n) (hi : f w (single i) = true) : Pure colour (f w) (colour i) := by
  have hd := actual_singleton_dependence_before N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono w hc hw i hi
  intro x y hxy
  exact hd x y false false hxy (fun _ => rfl)

end CutPolicy

namespace PairFactorCover

open CutPolicy CrossRectangleCover

variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def pair (i j : Fin n) : Fin n → Bool := fun k => decide (k = i ∨ k = j)

section Pairs

variable (colour : Fin n → Bool) (L : α → Fin n) (R : β → Fin n)
  (hL : ∀ a, colour (L a) = false) (hR : ∀ b, colour (R b) = true)

include hR in
lemma pair_agrees_left (a : α) (b : β) :
    ∀ i, colour i = false → pair (L a) (R b) i = single (L a) i := by
  intro i hi
  have hne : i ≠ R b := by
    intro he
    subst i
    simpa [hR b] using hi
  simp [pair, single, hne]

include hL in
lemma pair_agrees_right (a : α) (b : β) :
    ∀ i, colour i = true → pair (L a) (R b) i = single (R b) i := by
  intro i hi
  have hne : i ≠ L a := by
    intro he
    subst i
    simpa [hL a] using hi
  simp [pair, single, hne]

include hR in
lemma pure_pair_left (u : (Fin n → Bool) → Bool) (hu : Pure colour u false) (a : α) (b : β) :
    u (pair (L a) (R b)) = u (single (L a)) :=
  hu _ _ (pair_agrees_left colour L R hR a b)

include hL in
lemma pure_pair_right (v : (Fin n → Bool) → Bool) (hv : Pure colour v true) (a : α) (b : β) :
    v (pair (L a) (R b)) = v (single (R b)) :=
  hv _ _ (pair_agrees_right colour L R hL a b)

include hL hR in
lemma separated_pairs (allow : Bool → Bool) (F : (Fin n → Bool) → Bool → Bool)
    (hf : Separated colour allow F) :
    ∃ g : α → Bool → Bool, ∃ h : β → Bool → Bool,
      (∀ a, g a false = true → g a true = true) ∧
      (∀ b, h b false = true → h b true = true) ∧
      (∀ a b z, F (pair (L a) (R b)) z = (g a z && h b z)) ∧
      (allow false = false → ∀ a z, g a z = g a false) ∧
      (allow true = false → ∀ b z, h b z = h b false) := by
  obtain ⟨g,h,dg,dh,mg,mh,he⟩ := hf
  refine ⟨fun a => g (single (L a)), fun b => h (single (R b)),
    fun a => mg _, fun b => mh _, ?_, ?_, ?_⟩
  · intro a b z
    rw [he, dg _ _ z z (pair_agrees_left colour L R hR a b) (fun _ => rfl),
      dh _ _ z z (pair_agrees_right colour L R hL a b) (fun _ => rfl)]
  · intro ha a z
    exact dg _ _ z false (fun _ _ => rfl) (by simp [ha])
  · intro ha b z
    exact dh _ _ z false (fun _ _ => rfl) (by simp [ha])

include hL hR in
lemma mixed_pair_cover (E : α → β → Prop) (hno : NoFour E)
    (F : (Fin n → Bool) → Bool → Bool) (hf : Separated colour (fun _ => true) F)
    (seed u v : (Fin n → Bool) → Bool)
    (hu : Pure colour u false) (hv : Pure colour v true)
    (hseed : ∀ x, seed x = (u x || v x))
    (hrel : ∀ a b, E a b ↔ F (pair (L a) (R b)) (seed (pair (L a) (R b))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, E a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨g,h,mg,mh,he,_,_⟩ := separated_pairs colour L R hL hR _ F hf
  apply BooleanFactorCover.mixed_factor_cover E hno g h
    (fun a => u (single (L a))) (fun b => v (single (R b))) mg mh
  intro a b
  rw [hrel, hseed, he, pure_pair_left colour L R hR u hu a b,
    pure_pair_right colour L R hL v hv a b]
  simp

include hL hR in
lemma left_pair_cover (E : α → β → Prop) (hno : NoFour E)
    (F : (Fin n → Bool) → Bool → Bool) (hf : Separated colour (fun c => !c) F)
    (seed u v w : (Fin n → Bool) → Bool)
    (hu : Pure colour u false) (hv : Pure colour v false) (hw : Pure colour w true)
    (hseed : ∀ x, seed x = (u x || (v x && w x)))
    (hrel : ∀ a b, E a b ↔ F (pair (L a) (R b)) (seed (pair (L a) (R b))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, E a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨g,h,mg,mh,he,ig,ih⟩ := separated_pairs colour L R hL hR _ F hf
  apply BooleanFactorCover.one_sided_factor_cover E hno g (fun b => h b false)
    (fun a => u (single (L a))) (fun a => v (single (L a))) (fun b => w (single (R b))) mg
  intro a b
  rw [hrel, hseed, he, pure_pair_left colour L R hR u hu a b,
    pure_pair_left colour L R hR v hv a b, pure_pair_right colour L R hL w hw a b,
    ih rfl b]
  simp

include hL hR in
lemma right_pair_cover (E : α → β → Prop) (hno : NoFour E)
    (F : (Fin n → Bool) → Bool → Bool) (hf : Separated colour (fun c => c) F)
    (seed u v w : (Fin n → Bool) → Bool)
    (hu : Pure colour u true) (hv : Pure colour v true) (hw : Pure colour w false)
    (hseed : ∀ x, seed x = (u x || (v x && w x)))
    (hrel : ∀ a b, E a b ↔ F (pair (L a) (R b)) (seed (pair (L a) (R b))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, E a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨g,h,mg,mh,he,ig,ih⟩ := separated_pairs colour L R hL hR _ F hf
  have hn : NoFour (fun b a => E a b) := by
    intro b b' a a' hbb haa he
    exact hno a a' b b' haa hbb ⟨he.1,he.2.2.1,he.2.1,he.2.2.2⟩
  obtain ⟨Q,P,hcover,hcard⟩ := BooleanFactorCover.one_sided_factor_cover (fun b a => E a b) hn
    h (fun a => g a false) (fun b => u (single (R b))) (fun b => v (single (R b)))
    (fun a => w (single (L a))) mh (by
      intro b a
      rw [hrel, hseed, he, pure_pair_right colour L R hL u hu a b,
        pure_pair_right colour L R hL v hv a b, pure_pair_left colour L R hR w hw a b,
        ig rfl a, Bool.and_comm]
      simp)
  exact ⟨P,Q,fun a b hab => (hcover b a hab).symm, by omega⟩

lemma rectangle_pair_cover (E : α → β → Prop) (hno : NoFour E) (g : α → Bool) (h : β → Bool)
    (he : ∀ a b, E a b ↔ (g a && h b) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, E a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 1 := by
  let U := BooleanFactorCover.support g
  let V := BooleanFactorCover.support h
  have hm : ∀ a b, E a b ↔ a ∈ U ∧ b ∈ V := by
    intro a b
    simp [he,U,V,BooleanFactorCover.support]
  obtain ⟨P,Q,hcover,hcard⟩ := rectangle_cover E hno U V
    (fun a ha b hb => (hm a b).mpr ⟨ha,hb⟩)
  exact ⟨P,Q,fun a b hab => hcover a ((hm a b).mp hab).1 b ((hm a b).mp hab).2,hcard⟩

include hL hR in
lemma empty_pair_cover (E : α → β → Prop) (hno : NoFour E)
    (F : (Fin n → Bool) → Bool → Bool) (hf : EmptySeparated colour F)
    (seed u v s t : (Fin n → Bool) → Bool)
    (hu : Pure colour u false) (hv : Pure colour v false)
    (hs : Pure colour s true) (ht : Pure colour t true)
    (hseed : ∀ x, seed x = ((u x && s x) || (v x && t x)))

    (hrel : ∀ a b, E a b ↔ F (pair (L a) (R b)) (seed (pair (L a) (R b))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ a b, E a b → a ∈ P ∨ b ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨g,h,useSeed,dg,dh,he⟩ := hf
  have eg (a : α) (b : β) : g (pair (L a) (R b)) = g (single (L a)) :=
    dg _ _ false false (pair_agrees_left colour L R hR a b) (by simp)
  have eh (a : α) (b : β) : h (pair (L a) (R b)) = h (single (R b)) :=
    dh _ _ false false (pair_agrees_right colour L R hL a b) (by simp)
  cases useSeed with
  | false =>
    have hr : ∀ a b, E a b ↔ (g (single (L a)) && h (single (R b))) = true := by
      intro a b
      simp only [hrel,he,eg,eh,Bool.false_eq_true,ite_false,Bool.and_true]
    obtain ⟨P,Q,hcover,hcard⟩ := rectangle_pair_cover E hno _ _ hr
    exact ⟨P,Q,hcover,by omega⟩
  | true =>
    apply BooleanFactorCover.empty_support_factor_cover E hno
      (fun a => g (single (L a))) (fun a => u (single (L a))) (fun a => v (single (L a)))
      (fun b => h (single (R b))) (fun b => s (single (R b))) (fun b => t (single (R b)))
    intro a b
    rw [hrel,he,eg,eh,hseed,pure_pair_left colour L R hR u hu a b,
      pure_pair_left colour L R hR v hv a b,pure_pair_right colour L R hL s hs a b,
      pure_pair_right colour L R hL t ht a b]
    simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

end Pairs

end PairFactorCover

namespace OneExceptional

open CutPolicy PairFactorCover CrossRectangleCover

variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma one_exceptional_or_cover
    (N cut output : ℕ) (F : ℕ → (Fin n → Bool) → Bool → Bool)
    (f : ℕ → (Fin n → Bool) → Bool) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (colour : Fin n → Bool) (seed : (Fin n → Bool) → Bool)
    (hinput : ∀ w (hw : w < n) x z, F w x z = x ⟨w,hw⟩)
    (hcut : ∀ x z, F cut x z = z)
    (hgate : ∀ w, n ≤ w → w < N → w ≠ cut → a w < w ∧ b w < w ∧
      ∀ x z, F w x z = if isAnd w then F (a w) x z && F (b w) x z
        else F (a w) x z || F (b w) x z)
    (hactual : ∀ w, w < N → ∀ x, f w x = F w x (seed x))
    (hproductive : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
    (hmono : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j)
    (hcutlt : cut < N) (ha : a cut < cut) (hb : b cut < cut)
    (hseed : ∀ x, seed x = (f (a cut) x || f (b cut) x))
    (hout : output < N)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ f output (pair (L i) (R j)) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  classical
  have hau : a cut < N := lt_trans ha hcutlt
  have hbu : b cut < N := lt_trans hb hcutlt
  have hup := actual_pure_before N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono (a cut) ha hau
  have hvp := actual_pure_before N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono (b cut) hb hbu
  have hus (c : Bool) := actual_plain_separated_before_colour N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono c (a cut) ha hau
  have hvs (c : Bool) := actual_plain_separated_before_colour N cut F f a b isAnd colour seed
    hinput hcut hgate hactual hproductive hmono c (b cut) hb hbu
  have hu0 := actual_zero_false_before N cut F f a b isAnd seed hinput hcut hgate hactual
    (a cut) ha hau
  have hv0 := actual_zero_false_before N cut F f a b isAnd seed hinput hcut hgate hactual
    (b cut) hb hbu
  have hrel' : ∀ i j, E i j ↔
      F output (pair (L i) (R j)) (seed (pair (L i) (R j))) = true := by
    intro i j
    rw [hrel, hactual output hout]
  have hsep (allow : Bool → Bool)
      (hs : ∀ i, seed (single i) = true → allow (colour i) = true)
      (hal : allow false = true ∨ allow true = true) :=
    cut_separated N cut F f a b isAnd colour seed hinput hcut hgate hactual hproductive hmono
      allow hs hal output hout
  by_cases hl : ∃ i, colour i = false ∧ seed (single i) = true
  · by_cases hr : ∃ i, colour i = true ∧ seed (single i) = true
    · obtain ⟨u,v,hu,hv,hs⟩ := mixed_seed_decomposition colour (f (a cut)) (f (b cut)) seed
        hseed hup hvp hu0 hv0 hl hr
      exact mixed_pair_cover colour L R hL hR E hno (F output)
        (hsep (fun _ => true) (fun _ _ => rfl) (Or.inl rfl)) seed u v hu hv hs hrel'
    · have hsupport : ∀ i, seed (single i) = true → (!colour i) = true := by
        intro i hi
        cases hc : colour i with
        | false => rfl
        | true => exact (hr ⟨i,hc,hi⟩).elim
      obtain ⟨u,v,w,hu,hv,hw,hs⟩ := one_colour_seed_decomposition colour false
        (f (a cut)) (f (b cut)) seed hseed hup hvp (hus false) (hvs false) hl
      exact left_pair_cover colour L R hL hR E hno (F output)
        (hsep (fun c => !c) hsupport (Or.inl rfl)) seed u v w hu hv hw hs hrel'
  · by_cases hr : ∃ i, colour i = true ∧ seed (single i) = true
    · have hsupport : ∀ i, seed (single i) = true → colour i = true := by
        intro i hi
        cases hc : colour i with
        | false => exact (hl ⟨i,hc,hi⟩).elim
        | true => rfl
      obtain ⟨u,v,w,hu,hv,hw,hs⟩ := one_colour_seed_decomposition colour true
        (f (a cut)) (f (b cut)) seed hseed hup hvp (hus true) (hvs true) hr
      exact right_pair_cover colour L R hL hR E hno (F output)
        (hsep (fun c => c) hsupport (Or.inr rfl)) seed u v w hu hv hw hs hrel'
    · have hempty : ∀ i, seed (single i) = false := by
        intro i
        cases hs : seed (single i) with
        | false => rfl
        | true =>
          cases hc : colour i with
          | false => exact (hl ⟨i,hc,hs⟩).elim
          | true => exact (hr ⟨i,hc,hs⟩).elim
      obtain ⟨u,s,v,t,hu,hs,hv,ht,hshape⟩ := separated_seed_decomposition colour
        (f (a cut)) (f (b cut)) seed hseed (hus false) (hvs false)
      have he := empty_cut_factorization N cut F f a b isAnd colour seed
        hinput hcut hgate hactual hproductive hmono hempty output hout
      exact empty_pair_cover colour L R hL hR E hno (F output) he seed u v s t
        hu hv hs ht hshape hrel'

end OneExceptional

namespace CutConstruction

open CutPolicy OneExceptional CrossRectangleCover PairFactorCover

def cutValue (n cut : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (x : Fin n → Bool) (z : Bool) (w : ℕ) : Bool :=
  if w = cut then z
  else if hw : w < n then x ⟨w,hw⟩
  else if hr : a w < w ∧ b w < w then
    if isAnd w then cutValue n cut a b isAnd x z (a w) && cutValue n cut a b isAnd x z (b w)
    else cutValue n cut a b isAnd x z (a w) || cutValue n cut a b isAnd x z (b w)
  else false
termination_by w

variable {n : ℕ}

lemma cutValue_input (cut : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool) (hcut : n ≤ cut)
    (w : ℕ) (hw : w < n) (x : Fin n → Bool) (z : Bool) :
    cutValue n cut a b isAnd x z w = x ⟨w,hw⟩ := by
  have hne : w ≠ cut := by omega
  rw [cutValue]
  simp [hne,hw]

lemma cutValue_cut (cut : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (x : Fin n → Bool) (z : Bool) : cutValue n cut a b isAnd x z cut = z := by
  rw [cutValue]
  simp

lemma cutValue_gate (cut : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (w : ℕ) (hw : n ≤ w) (hc : w ≠ cut) (ha : a w < w) (hb : b w < w)
    (x : Fin n → Bool) (z : Bool) :
    cutValue n cut a b isAnd x z w =
      if isAnd w then cutValue n cut a b isAnd x z (a w) && cutValue n cut a b isAnd x z (b w)
      else cutValue n cut a b isAnd x z (a w) || cutValue n cut a b isAnd x z (b w) := by
  rw [cutValue]
  simp [hc,show ¬w < n by omega,ha,hb]

lemma cutValue_actual
    (N cut : ℕ) (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (f : ℕ → (Fin n → Bool) → Bool) (hcut : n ≤ cut)
    (hinput : ∀ w (hw : w < n) x, f w x = x ⟨w,hw⟩)
    (hgate : ∀ w, n ≤ w → w < N → a w < w ∧ b w < w ∧
      ∀ x, f w x = if isAnd w then f (a w) x && f (b w) x else f (a w) x || f (b w) x) :
    ∀ w, w < N → ∀ x, f w x = cutValue n cut a b isAnd x (f cut x) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x
    by_cases hc : w = cut
    · subst w
      rw [cutValue_cut]
    · by_cases hn : w < n
      · rw [hinput w hn,cutValue_input cut a b isAnd hcut w hn]
      · have hng : n ≤ w := by omega
        obtain ⟨ha,hb,he⟩ := hgate w hng hw
        rw [he,cutValue_gate cut a b isAnd w hng hc ha hb,
          ih (a w) ha (lt_trans ha hw) x,ih (b w) hb (lt_trans hb hw) x]

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma indexed_one_exceptional_or_cover
    (N cut output : ℕ) (f : ℕ → (Fin n → Bool) → Bool)
    (a b : ℕ → ℕ) (isAnd : ℕ → Bool) (colour : Fin n → Bool)
    (hinput : ∀ w (hw : w < n) x, f w x = x ⟨w,hw⟩)
    (hgate : ∀ w, n ≤ w → w < N → a w < w ∧ b w < w ∧
      ∀ x, f w x = if isAnd w then f (a w) x && f (b w) x else f (a w) x || f (b w) x)
    (hproductive : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      (∃ i, f (a w) (single i) = true) ∧ (∃ i, f (b w) (single i) = true))
    (hmono : ∀ w, n ≤ w → w < N → w ≠ cut → isAnd w = false →
      ∀ i j, f w (single i) = true → f w (single j) = true → colour i = colour j)
    (hcutlo : n ≤ cut) (hcutlt : cut < N) (hcutop : isAnd cut = false)
    (hout : output < N)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ f output (pair (L i) (R j)) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  obtain ⟨ha,hb,he⟩ := hgate cut hcutlo hcutlt
  apply one_exceptional_or_cover N cut output
    (fun w x z => cutValue n cut a b isAnd x z w) f a b isAnd colour (f cut)
    (cutValue_input cut a b isAnd hcutlo)
    (cutValue_cut cut a b isAnd)
    (by
      intro w hw hn hc
      obtain ⟨ha,hb,_⟩ := hgate w hw hn
      exact ⟨ha,hb,cutValue_gate cut a b isAnd w hw hc ha hb⟩)
    (cutValue_actual N cut a b isAnd f hcutlo hinput hgate)
    hproductive hmono hcutlt ha hb
    (by intro x; simpa [hcutop] using he x)
    hout L R hL hR E hno hrel

end CutConstruction

namespace ActualOneBad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open CutPolicy PairFactorCover CrossRectangleCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

def wireFn (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireFn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireFn n C w x = x ⟨w, hw⟩ := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma binary_gate (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < n + j ∧ b < n + j ∧
      (gateAt C j).inputs = [a, b] ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ x, wireFn n C (n + j) x =
        (gateAt C j).op.eval [wireFn n C a x, wireFn n C b x] := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_get C j hj]
    exact List.getElem_mem hj
  have hlen := hC.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a < n + j := hC.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hC.2.1 j hj b (by simp [hab])
  refine ⟨a, b, ha, hb, hab, hC.1 _ hmem, ?_⟩
  intro x
  unfold wireFn
  change (wiresFrom C.gates (List.ofFn x)).getD (n + j) false = _
  have he := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at he
  rw [he, ← gateAt_get C j hj, hab]
  simp [ha, hb, wiresFrom, Circuit.wires]


def leftWire (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (gateAt C (w - n)).inputs.getD 0 0

def rightWire (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (gateAt C (w - n)).inputs.getD 1 0

lemma binary_wire_data (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hge : n ≤ w) (hw : w < n + C.gates.length) :
    leftWire n C w < w ∧ rightWire n C w < w ∧
      ((gateAt C (w - n)).op = GateOp.and ∨ (gateAt C (w - n)).op = GateOp.or) ∧
      ∀ x, wireFn n C w x = (gateAt C (w - n)).op.eval
        [wireFn n C (leftWire n C w) x, wireFn n C (rightWire n C w) x] := by
  have hj : w - n < C.gates.length := by omega
  obtain ⟨a, b, ha, hb, hab, hop, hv⟩ := binary_gate n C hC (w - n) hj
  have hsum : n + (w - n) = w := by omega
  simpa [leftWire, rightWire, hab, hsum] using And.intro ha (And.intro hb (And.intro hop hv))

def isAndWire (n : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  match (gateAt C (w - n)).op with
  | GateOp.and => true
  | _ => false

lemma binary_wire_recurrence (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hge : n ≤ w) (hw : w < n + C.gates.length) :
    leftWire n C w < w ∧ rightWire n C w < w ∧
      ∀ x, wireFn n C w x =
        if isAndWire n C w then wireFn n C (leftWire n C w) x && wireFn n C (rightWire n C w) x
        else wireFn n C (leftWire n C w) x || wireFn n C (rightWire n C w) x := by
  obtain ⟨ha,hb,hop,he⟩ := binary_wire_data n C hC w hge hw
  refine ⟨ha,hb,?_⟩
  intro x
  rw [he]
  rcases hop with hop | hop <;> simp [isAndWire,hop,GateOp.eval]

lemma isAndWire_false_iff (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (w : ℕ) (hge : n ≤ w) (hw : w < n + C.gates.length) :
    isAndWire n C w = false ↔ (gateAt C (w - n)).op = GateOp.or := by
  obtain ⟨_,_,hop,_⟩ := binary_wire_data n C hC w hge hw
  rcases hop with hop | hop <;> simp [isAndWire,hop]

-- A semantic condition on an actual OR gate: each operand accepts some singleton,
-- and all singletons accepted by the gate have one colour.
def ProductiveMonochrome (n : ℕ) (C : Circuit) (colour : Fin n → Bool) (j : ℕ) : Prop :=
  (∃ i, wireFn n C (opnd C j 0) (single i) = true) ∧
  (∃ i, wireFn n C (opnd C j 1) (single i) = true) ∧
  ∀ i k, wireFn n C (n + j) (single i) = true →
    wireFn n C (n + j) (single k) = true → colour i = colour k

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

-- An AO2 circuit with at most one OR failing the semantic productive-monochrome
-- condition has a cross-pair output relation of vertex-cover number at most two,
-- whenever that relation is C4-free. No syntactic two-colour count is assumed.
lemma circuit_one_exceptional_or_cover
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (exception : ℕ) (hex : exception < C.gates.length)
    (hexop : (gateAt C exception).op = GateOp.or)
    (hgood : ∀ j, j < C.gates.length → j ≠ exception →
      (gateAt C j).op = GateOp.or → ProductiveMonochrome n C colour j)
    (hout : C.output < n + C.gates.length)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ C.eval (List.ofFn (pair (L i) (R j))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  have hg (w : ℕ) (hw : n ≤ w) (hn : w < n + C.gates.length)
      (hc : w ≠ n + exception) (ho : isAndWire n C w = false) :
      ProductiveMonochrome n C colour (w - n) := by
    apply hgood (w - n) (by omega) (by omega)
    exact (isAndWire_false_iff n C hC w hw hn).mp ho
  apply CutConstruction.indexed_one_exceptional_or_cover
    (n + C.gates.length) (n + exception) C.output (wireFn n C)
    (leftWire n C) (rightWire n C) (isAndWire n C) colour
    (wireFn_input n C) (binary_wire_recurrence n C hC)
    (by
      intro w hw hn hc ho
      have h := hg w hw hn hc ho
      exact ⟨by simpa [leftWire,opnd] using h.1,
        by simpa [rightWire,opnd] using h.2.1⟩)
    (by
      intro w hw hn hc ho i j hi hj
      have h := (hg w hw hn hc ho).2.2
      have he : n + (w - n) = w := by omega
      exact h i j (by simpa [he] using hi) (by simpa [he] using hj))
    (by omega) (by omega) (by simp [isAndWire,hexop])
    hout L R hL hR E hno hrel

end ActualOneBad

namespace ActualOneBad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open CutPolicy PairFactorCover CrossRectangleCover

lemma wireFn_invalid (n : ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) : wireFn n C w x = false := by
  unfold wireFn Circuit.wires
  change (wiresFrom C.gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  simpa [length_wiresFrom] using hw

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma circuit_one_exceptional_or_cover_total
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (exception : ℕ) (hex : exception < C.gates.length)
    (hexop : (gateAt C exception).op = GateOp.or)
    (hgood : ∀ j, j < C.gates.length → j ≠ exception →
      (gateAt C j).op = GateOp.or → ProductiveMonochrome n C colour j)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ C.eval (List.ofFn (pair (L i) (R j))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  by_cases hout : C.output < n + C.gates.length
  · exact circuit_one_exceptional_or_cover n C hC colour exception hex hexop hgood
      hout L R hL hR E hno hrel
  · refine ⟨∅,∅,?_,by simp⟩
    intro i j hij
    have he := (hrel i j).mp hij
    change wireFn n C C.output (pair (L i) (R j)) = true at he
    rw [wireFn_invalid n C C.output (by omega)] at he
    cases he

end ActualOneBad

namespace ActualOneBad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open CutPolicy PairFactorCover CrossRectangleCover

lemma actual_good_plain_separated
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (hgood : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or →
      ProductiveMonochrome n C colour j)
    (w : ℕ) (hw : w < n + C.gates.length) :
    PlainSeparated colour false (wireFn n C w) := by
  let N := n + C.gates.length
  let a := leftWire n C
  let b := rightWire n C
  let op := isAndWire n C
  have hN : n ≤ N := by dsimp [N]; omega
  have hg (v : ℕ) (hv : n ≤ v) (hn : v < N) (ho : op v = false) :
      ProductiveMonochrome n C colour (v - n) := by
    apply hgood (v - n) (by dsimp [N] at hn; omega)
    exact (isAndWire_false_iff n C hC v hv hn).mp ho
  apply actual_plain_separated_before N N
    (fun v x z => CutConstruction.cutValue n N a b op x z v)
    (wireFn n C) a b op colour (wireFn n C N)
    (CutConstruction.cutValue_input N a b op hN)
    (CutConstruction.cutValue_cut N a b op)
    (by
      intro v hv hn hc
      obtain ⟨ha,hb,_⟩ := binary_wire_recurrence n C hC v hv hn
      exact ⟨ha,hb,CutConstruction.cutValue_gate N a b op v hv hc ha hb⟩)
    (CutConstruction.cutValue_actual N N a b op (wireFn n C) hN
      (wireFn_input n C) (binary_wire_recurrence n C hC))
    (by
      intro v hv hn hc ho
      have h := hg v hv hn ho
      exact ⟨by simpa [a,leftWire,opnd] using h.1,
        by simpa [b,rightWire,opnd] using h.2.1⟩)
    (by
      intro v hv hn hc ho i j hi hj
      have h := (hg v hv hn ho).2.2
      have he : n + (v - n) = v := by omega
      exact h i j (by simpa [he] using hi) (by simpa [he] using hj))
    w hw hw

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma circuit_productive_or_cover
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (hgood : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or →
      ProductiveMonochrome n C colour j)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ C.eval (List.ofFn (pair (L i) (R j))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 1 := by
  by_cases hout : C.output < n + C.gates.length
  · obtain ⟨g,h,hg,hh,he⟩ := actual_good_plain_separated n C hC colour hgood C.output hout
    apply rectangle_pair_cover E hno (fun i => g (single (L i))) (fun j => h (single (R j)))
    intro i j
    calc
      E i j ↔ wireFn n C C.output (pair (L i) (R j)) = true := hrel i j
      _ ↔ (g (single (L i)) && h (single (R j))) = true := by
        rw [he,pure_pair_left colour L R hR g hg i j,pure_pair_right colour L R hL h hh i j]
  · refine ⟨∅,∅,?_,by simp⟩
    intro i j hij
    have he := (hrel i j).mp hij
    change wireFn n C C.output (pair (L i) (R j)) = true at he
    rw [wireFn_invalid n C C.output (by omega)] at he
    cases he

lemma circuit_at_most_one_exceptional_or_cover
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (exception : ℕ)
    (hgood : ∀ j, j < C.gates.length → j ≠ exception →
      (gateAt C j).op = GateOp.or → ProductiveMonochrome n C colour j)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ C.eval (List.ofFn (pair (L i) (R j))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧ P.card + Q.card ≤ 2 := by
  by_cases hex : exception < C.gates.length ∧ (gateAt C exception).op = GateOp.or
  · exact circuit_one_exceptional_or_cover_total n C hC colour exception hex.1 hex.2 hgood
      L R hL hR E hno hrel
  · have hg : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or →
        ProductiveMonochrome n C colour j := by
      intro j hj hop
      apply hgood j hj _ hop
      intro he
      subst j
      exact hex ⟨hj,hop⟩
    obtain ⟨P,Q,hcover,hcard⟩ := circuit_productive_or_cover n C hC colour hg L R hL hR E hno hrel
    exact ⟨P,Q,hcover,by omega⟩

end ActualOneBad

namespace ActualOneBad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open CutPolicy PairFactorCover CrossRectangleCover

noncomputable def badOrGates (n : ℕ) (C : Circuit) (colour : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ ¬ ProductiveMonochrome n C colour j

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma circuit_bad_or_count_cover
    (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (colour : Fin n → Bool)
    (hcount : (badOrGates n C colour).card ≤ 1)
    (L : α → Fin n) (R : β → Fin n)
    (hL : ∀ i, colour (L i) = false) (hR : ∀ j, colour (R j) = true)
    (E : α → β → Prop) (hno : NoFour E)
    (hrel : ∀ i j, E i j ↔ C.eval (List.ofFn (pair (L i) (R j))) = true) :
    ∃ P : Finset α, ∃ Q : Finset β,
      (∀ i j, E i j → i ∈ P ∨ j ∈ Q) ∧
      P.card + Q.card ≤ (badOrGates n C colour).card + 1 := by
  classical
  by_cases hne : (badOrGates n C colour).Nonempty
  · obtain ⟨k,hk⟩ := hne
    have hg : ∀ j, j < C.gates.length → j ≠ k →
        (gateAt C j).op = GateOp.or → ProductiveMonochrome n C colour j := by
      intro j hj hneq hop
      by_contra hbad
      have hm : j ∈ badOrGates n C colour := by simp [badOrGates,hj,hop,hbad]
      exact hneq ((Finset.card_le_one.mp hcount) _ hm _ hk)
    obtain ⟨P,Q,hcover,hcard⟩ := circuit_at_most_one_exceptional_or_cover
      n C hC colour k hg L R hL hR E hno hrel
    have hpos : 0 < (badOrGates n C colour).card := Finset.card_pos.mpr ⟨k,hk⟩
    exact ⟨P,Q,hcover,by omega⟩
  · have hg : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.or →
        ProductiveMonochrome n C colour j := by
      intro j hj hop
      by_contra hbad
      exact hne ⟨j,by simp [badOrGates,hj,hop,hbad]⟩
    obtain ⟨P,Q,hcover,hcard⟩ := circuit_productive_or_cover n C hC colour hg L R hL hR E hno hrel
    exact ⟨P,Q,hcover,by omega⟩

end ActualOneBad


namespace FullProductNesting

variable {α β : Type*}

def HasEdge (R : α → β → Prop) (X : α → Prop) (Y : β → Prop) : Prop :=
  ∃ a b, R a b ∧ X a ∧ Y b

def FullIntersection (R S : α → β → Prop) : Prop :=
  ∀ X Y, HasEdge (fun a b => R a b ∧ S a b) X Y ↔ HasEdge R X Y ∧ HasEdge S X Y

lemma full_product_pair_relation (E R S : α → β → Prop)
    (hfull : ∀ X Y, HasEdge E X Y ↔ HasEdge R X Y ∧ HasEdge S X Y) :
    ∀ a b, E a b ↔ R a b ∧ S a b := by
  intro a b
  simpa [HasEdge] using hfull (fun i => i = a) (fun j => j = b)

lemma full_product_intersection (E R S : α → β → Prop)
    (hfull : ∀ X Y, HasEdge E X Y ↔ HasEdge R X Y ∧ HasEdge S X Y) :
    FullIntersection R S := by
  have hp := full_product_pair_relation E R S hfull
  intro X Y
  simpa only [HasEdge, hp] using hfull X Y

lemma full_intersection_columns_nested (R S : α → β → Prop)
    (hfull : FullIntersection R S) (b : β) :
    (∀ a, R a b → S a b) ∨ (∀ a, S a b → R a b) := by
  classical
  by_cases hsub : ∀ a, R a b → S a b
  · exact Or.inl hsub
  · right
    push Not at hsub
    obtain ⟨a,ha,has⟩ := hsub
    intro c hcs
    by_contra hcr
    have hh : HasEdge (fun i j => R i j ∧ S i j)
        (fun i => i = a ∨ i = c) (fun j => j = b) := by
      apply (hfull _ _).mpr
      exact ⟨⟨a,b,ha,Or.inl rfl,rfl⟩,⟨c,b,hcs,Or.inr rfl,rfl⟩⟩
    obtain ⟨i,j,⟨hir,his⟩,hi,hj⟩ := hh
    subst j
    rcases hi with hi | hi
    · subst i
      exact has his
    · subst i
      exact hcr hir

lemma full_intersection_rows_nested (R S : α → β → Prop)
    (hfull : FullIntersection R S) (a : α) :
    (∀ b, R a b → S a b) ∨ (∀ b, S a b → R a b) := by
  classical
  by_cases hsub : ∀ b, R a b → S a b
  · exact Or.inl hsub
  · right
    push Not at hsub
    obtain ⟨b,hb,hbs⟩ := hsub
    intro c hcs
    by_contra hcr
    have hh : HasEdge (fun i j => R i j ∧ S i j)
        (fun i => i = a) (fun j => j = b ∨ j = c) := by
      apply (hfull _ _).mpr
      exact ⟨⟨a,b,hb,rfl,Or.inl rfl⟩,⟨a,c,hcs,rfl,Or.inr rfl⟩⟩
    obtain ⟨i,j,⟨hir,his⟩,hi,hj⟩ := hh
    subst i
    rcases hj with hj | hj
    · subst j
      exact hbs his
    · subst j
      exact hcr hir

end FullProductNesting

namespace FullProductNesting

variable {α β ι : Type*}

lemma exists_column_controller (E : α → β → Prop)
    (f : ι → (α → Prop) → (β → Prop) → Prop)
    (hmono : ∀ i X X' Y, (∀ a, X a → X' a) → f i X Y → f i X' Y)
    (hfull : ∀ X Y, HasEdge E X Y ↔ ∀ i, f i X Y) (b : β) :
    ∃ i, ∀ X, f i X (fun j => j = b) ↔ ∃ a, E a b ∧ X a := by
  classical
  have hneg : ¬ ∀ i, f i (fun a => ¬ E a b) (fun j => j = b) := by
    intro hf
    obtain ⟨a,j,he,ha,hj⟩ := (hfull _ _).mpr hf
    subst j
    exact ha he
  push Not at hneg
  obtain ⟨i,hi⟩ := hneg
  refine ⟨i,?_⟩
  intro X
  constructor
  · intro hx
    by_contra hnone
    have hsub : ∀ a, X a → ¬ E a b := by
      intro a ha he
      exact hnone ⟨a,he,ha⟩
    exact hi (hmono i X (fun a => ¬ E a b) (fun j => j = b) hsub hx)
  · rintro ⟨a,he,ha⟩
    exact (hfull X (fun j => j = b)).mp ⟨a,b,he,ha,rfl⟩ i

lemma exists_row_controller (E : α → β → Prop)
    (f : ι → (α → Prop) → (β → Prop) → Prop)
    (hmono : ∀ i X Y Y', (∀ b, Y b → Y' b) → f i X Y → f i X Y')
    (hfull : ∀ X Y, HasEdge E X Y ↔ ∀ i, f i X Y) (a : α) :
    ∃ i, ∀ Y, f i (fun j => j = a) Y ↔ ∃ b, E a b ∧ Y b := by
  classical
  have hneg : ¬ ∀ i, f i (fun j => j = a) (fun b => ¬ E a b) := by
    intro hf
    obtain ⟨j,b,he,hj,hb⟩ := (hfull _ _).mpr hf
    subst j
    exact hb he
  push Not at hneg
  obtain ⟨i,hi⟩ := hneg
  refine ⟨i,?_⟩
  intro Y
  constructor
  · intro hy
    by_contra hnone
    have hsub : ∀ b, Y b → ¬ E a b := by
      intro b hb he
      exact hnone ⟨b,he,hb⟩
    exact hi (hmono i (fun j => j = a) Y (fun b => ¬ E a b) hsub hy)
  · rintro ⟨b,he,hb⟩
    exact (hfull (fun j => j = a) Y).mp ⟨a,b,he,rfl,hb⟩ i

end FullProductNesting


namespace OwnerStrictness

variable {M K : Type*} [Fintype M] [Fintype K] [Nonempty M]

lemma owner_strictness
    (A B : K → M → Prop) (E : M → M → Prop) (tag : K → Bool) (r c : M → K)
    (hrowMem : ∀ p, A (r p) p ∧ B (r p) p)
    (hcolMem : ∀ p, A (c p) p ∧ B (c p) p)
    (hrowCtrl : ∀ p q, A (r p) p → B (r p) q → E p q)
    (hcolCtrl : ∀ p q, A (c q) p → B (c q) q → E p q)
    (hcover : ∀ p q, E p q → ∀ t : Bool, ∃ k, tag k = t ∧ A k p ∧ B k q)
    (hno : ∀ p a q b, p ≠ a → q ≠ b → ¬ (E p q ∧ E p b ∧ E a q ∧ E a b)) :
    Fintype.card M + 1 ≤ Fintype.card K := by
  classical
  have hr : Function.Injective r := by
    intro p q he
    by_contra hpq
    have epq : E p q := hrowCtrl p q (hrowMem p).1 (by rw [he]; exact (hrowMem q).2)
    have eqp : E q p := hrowCtrl q p (hrowMem q).1 (by rw [← he]; exact (hrowMem p).2)
    exact hno p q p q hpq hpq
      ⟨hrowCtrl p p (hrowMem p).1 (hrowMem p).2,epq,eqp,
        hrowCtrl q q (hrowMem q).1 (hrowMem q).2⟩
  have hc : Function.Injective c := by
    intro p q he
    by_contra hpq
    have epq : E p q := hcolCtrl p q (by rw [← he]; exact (hcolMem p).1) (hcolMem q).2
    have eqp : E q p := hcolCtrl q p (by rw [he]; exact (hcolMem q).1) (hcolMem p).2
    exact hno p q p q hpq hpq
      ⟨hcolCtrl p p (hcolMem p).1 (hcolMem p).2,epq,eqp,
        hcolCtrl q q (hcolMem q).1 (hcolMem q).2⟩
  have hle := Fintype.card_le_of_injective r hr
  by_contra hbound
  have heq : Fintype.card M = Fintype.card K := by omega
  have hrs : Function.Surjective r := by
    by_contra hn
    have ht := Fintype.card_lt_of_injective_not_surjective r hr hn
    omega
  have hcs : Function.Surjective c := by
    by_contra hn
    have ht := Fintype.card_lt_of_injective_not_surjective c hc hn
    omega
  let p : M := Classical.arbitrary M
  obtain ⟨q,hq⟩ := hcs (r p)
  have hpq : E p q := hrowCtrl p q (hrowMem p).1 (by
    rw [← hq]
    exact (hcolMem q).2)
  obtain ⟨k,hkt,hkp,hkq⟩ := hcover p q hpq (!(tag (r p)))
  have hktne : tag k ≠ tag (r p) := by
    rw [hkt]
    cases tag (r p) <;> decide
  obtain ⟨a,ha⟩ := hrs k
  obtain ⟨b,hb⟩ := hcs k
  have hap : a ≠ p := by
    intro he
    apply hktne
    rw [← ha,he]
  have hbq : b ≠ q := by
    intro he
    apply hktne
    rw [← hb,he,hq]
  have haq : E a q := hrowCtrl a q (hrowMem a).1 (by rw [ha]; exact hkq)
  have hab : E a b := hrowCtrl a b (hrowMem a).1 (by rw [ha,← hb]; exact (hcolMem b).2)
  have hpb : E p b := hcolCtrl p b (by rw [hb]; exact hkp) (hcolMem b).2
  exact hno p a q b (Ne.symm hap) (Ne.symm hbq) ⟨hpq,hpb,haq,hab⟩

end OwnerStrictness

namespace IndependentFactors

open FullProductNesting

variable {M K : Type*} [Fintype M] [Fintype K] [Nonempty M]

-- Only the pair restrictions of the terms must be rectangles.
-- The monotone factors have exact conjunction output.
lemma two_factor_matching_bound
    (E : M → M → Prop)
    (f : Bool → (M → Prop) → (M → Prop) → Prop)
    (A B : K → M → Prop) (tag : K → Bool)
    (hmonoX : ∀ t X X' Y, (∀ p, X p → X' p) → f t X Y → f t X' Y)
    (hmonoY : ∀ t X Y Y', (∀ q, Y q → Y' q) → f t X Y → f t X Y')
    (hfull : ∀ X Y, HasEdge E X Y ↔ ∀ t, f t X Y)
    (hpair : ∀ t p q, f t (fun x => x = p) (fun y => y = q) ↔
      ∃ k, tag k = t ∧ A k p ∧ B k q)
    (hdiag : ∀ p, E p p)
    (hno : ∀ p a q b, p ≠ a → q ≠ b → ¬ (E p q ∧ E p b ∧ E a q ∧ E a b)) :
    Fintype.card M + 1 ≤ Fintype.card K := by
  classical
  have hrow : ∀ p, ∃ k, (A k p ∧ B k p) ∧ ∀ q, B k q → E p q := by
    intro p
    obtain ⟨t,ht⟩ := exists_row_controller E f hmonoY hfull p
    have hf : f t (fun x => x = p) (fun y => y = p) :=
      (ht _).mpr ⟨p,hdiag p,rfl⟩
    obtain ⟨k,hkt,hkp,hkq⟩ := (hpair t p p).mp hf
    refine ⟨k,⟨hkp,hkq⟩,?_⟩
    intro q hq
    have hfq := (hpair t p q).mpr ⟨k,hkt,hkp,hq⟩
    obtain ⟨b,heb,hb⟩ := (ht _).mp hfq
    simpa only [hb] using heb
  have hcol : ∀ q, ∃ k, (A k q ∧ B k q) ∧ ∀ p, A k p → E p q := by
    intro q
    obtain ⟨t,ht⟩ := exists_column_controller E f hmonoX hfull q
    have hf : f t (fun x => x = q) (fun y => y = q) :=
      (ht _).mpr ⟨q,hdiag q,rfl⟩
    obtain ⟨k,hkt,hkp,hkq⟩ := (hpair t q q).mp hf
    refine ⟨k,⟨hkp,hkq⟩,?_⟩
    intro p hp
    have hfp := (hpair t p q).mpr ⟨k,hkt,hp,hkq⟩
    obtain ⟨a,hea,ha⟩ := (ht _).mp hfp
    simpa only [ha] using hea
  choose r hrMem hrCtrl using hrow
  choose c hcMem hcCtrl using hcol
  apply OwnerStrictness.owner_strictness A B E tag r c hrMem hcMem
  · intro p q _ hq
    exact hrCtrl p q hq
  · intro p q hp _
    exact hcCtrl q p hp
  · intro p q he t
    exact (hpair t p q).mp
      ((hfull (fun x => x = p) (fun y => y = q)).mp ⟨p,q,he,rfl,rfl⟩ t)
  · exact hno

end IndependentFactors

end PEqualNP.Outside.L_meta_4970.H9RedTeam
