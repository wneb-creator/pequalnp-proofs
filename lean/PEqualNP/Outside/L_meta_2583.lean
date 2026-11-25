import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

namespace SingleUse

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hC : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hC j hj i hi)]

lemma wv_missing (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (hw : n + C.gates.length ≤ w) : wv n C x w = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_eq, foldl_len, List.length_ofFn]
  unfold wv
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl


end SingleUse

namespace MintermCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

lemma inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gate_mem C k hk))
  simp [opnd, hin]

lemma opnd_back (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) : opnd C k b < n + k := by
  apply hAO.2.1 k hk
  rw [inputs_two n C hAO k hk]
  fin_cases b <;> simp


end MintermCircuit

namespace AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

def isAnd (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def andPrefix (C : Circuit) (r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun k => isAnd C k = true)

lemma false_join_of_signature_eq (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (x y : Fin n → Bool)
    (hsig : ∀ k < r, (gateAt C k).op = GateOp.and →
      wv n C x (opnd C k 0) = wv n C y (opnd C k 0)) :
    ∀ w, w < n + r → wv n C x w = false → wv n C y w = false →
      wv n C (fun i => x i || y i) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hx
      rw [wv_input n C y w hwn] at hy
      rw [wv_input n C _ w hwn]
      simp [hx, hy]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkr : k < r := by omega
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have heq := hsig k hkr hop
        cases hl : wv n C x (opnd C k 0) with
        | false =>
          have hly : wv n C y (opnd C k 0) = false := heq.symm.trans hl
          have hj := ih _ ha (by omega) hl hly
          simp [hop, GateOp.eval, hj]
        | true =>
          have hly : wv n C y (opnd C k 0) = true := heq.symm.trans hl
          have hxr : wv n C x (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hl] using hx
          have hyr : wv n C y (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hly] using hy
          have hj := ih _ hb (by omega) hxr hyr
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (by omega) hxx.1 hyy.1
        have hj1 := ih _ hb (by omega) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma false_family_card_le_signatures {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    Fintype.card α ≤ 2 ^ (andPrefix C r).card := by
  classical
  let sig : α → ((andPrefix C r) → Bool) := fun a k => wv n C (f a) (opnd C k.val 0)
  have hinj : Function.Injective sig := by
    intro a b hab
    by_contra hne
    have heq : ∀ k < r, (gateAt C k).op = GateOp.and →
        wv n C (f a) (opnd C k 0) = wv n C (f b) (opnd C k 0) := by
      intro k hk hop
      have hkA : k ∈ andPrefix C r := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
      exact congrFun hab ⟨k, hkA⟩
    have hf := false_join_of_signature_eq n C hAO r hr (f a) (f b) heq w hw
      (hfalse a) (hfalse b)
    rw [hjoin a b hne] at hf
    cases hf
  have hcard := Fintype.card_le_of_injective sig hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hcard

lemma false_cube_le_and_count (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (d : ℕ) (f : (Fin d → Bool) → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    d ≤ (andPrefix C r).card := by
  have hc := false_family_card_le_signatures n C hAO r hr w hw f hfalse hjoin
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end AndSignature

namespace AndPairSeparation
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit
  PEqualNP.Outside.L_meta_2583.AndSignature

def crossedAt (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (k : ℕ) : Prop :=
  (wv n C x (opnd C k 0) = false ∧ wv n C x (opnd C k 1) = true ∧
   wv n C y (opnd C k 0) = true ∧ wv n C y (opnd C k 1) = false) ∨
  (wv n C x (opnd C k 0) = true ∧ wv n C x (opnd C k 1) = false ∧
   wv n C y (opnd C k 0) = false ∧ wv n C y (opnd C k 1) = true)

lemma false_join_of_no_crossed_and (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (x y : Fin n → Bool)
    (hnocross : ∀ k < r, (gateAt C k).op = .and → ¬ crossedAt n C x y k) :
    ∀ w, w < n + r → wv n C x w = false → wv n C y w = false →
      wv n C (fun i => x i || y i) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx hy
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn] at hx
      rw [wv_input n C y w hwn] at hy
      rw [wv_input n C _ w hwn]
      simp [hx, hy]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkr : k < r := by omega
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · by_cases hl : wv n C x (opnd C k 0) = false ∧
            wv n C y (opnd C k 0) = false
        · have hj := ih _ ha (by omega) hl.1 hl.2
          simp [hop, GateOp.eval, hj]
        · have hright : wv n C x (opnd C k 1) = false ∧
              wv n C y (opnd C k 1) = false := by
            have hn := hnocross k hkr hop
            unfold crossedAt at hn
            cases hxl : wv n C x (opnd C k 0) <;>
              cases hxr : wv n C x (opnd C k 1) <;>
              cases hyl : wv n C y (opnd C k 0) <;>
              cases hyr : wv n C y (opnd C k 1) <;>
              simp_all [GateOp.eval]
          have hj := ih _ hb (by omega) hright.1 hright.2
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (by omega) hxx.1 hyy.1
        have hj1 := ih _ hb (by omega) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma exists_crossed_and_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (w : ℕ) (hw : w < n + r)
    (x y : Fin n → Bool) (hx : wv n C x w = false) (hy : wv n C y w = false)
    (hj : wv n C (fun i => x i || y i) w = true) :
    ∃ k < r, (gateAt C k).op = .and ∧ crossedAt n C x y k := by
  by_contra hn
  have hnocross : ∀ k < r, (gateAt C k).op = .and → ¬ crossedAt n C x y k := by
    intro k hk hop hcross
    exact hn ⟨k, hk, hop, hcross⟩
  have hf := false_join_of_no_crossed_and n C hAO r hr x y hnocross w hw hx hy
  rw [hj] at hf
  cases hf

lemma exists_crossed_and (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = false) (hy : C.eval (List.ofFn y) = false)
    (hj : C.eval (List.ofFn (fun i => x i || y i)) = true) :
    ∃ k < C.gates.length, (gateAt C k).op = .and ∧ crossedAt n C x y k := by
  have hw : C.output < n + C.gates.length := by
    by_contra hbad
    have hf := wv_missing n C (fun i => x i || y i) C.output (by omega)
    change C.eval (List.ofFn _) = false at hf
    rw [hj] at hf
    cases hf
  exact exists_crossed_and_prefix n C hAO C.gates.length le_rfl C.output hw x y hx hy hj

def choiceAt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) : Option Bool :=
  match wv n C x (opnd C k 0), wv n C x (opnd C k 1) with
  | false, true => some false
  | true, false => some true
  | _, _ => none

lemma choiceAt_forced_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) :
    choiceAt n C x k ≠ none ↔
      wv n C x (opnd C k 0) ≠ wv n C x (opnd C k 1) := by
  unfold choiceAt
  cases wv n C x (opnd C k 0) <;> cases wv n C x (opnd C k 1) <;> simp

lemma crossed_choices (n : ℕ) (C : Circuit) (x y : Fin n → Bool) (k : ℕ)
    (hc : crossedAt n C x y k) :
    ∃ b c : Bool, choiceAt n C x k = some b ∧ choiceAt n C y k = some c ∧ b ≠ c := by
  rcases hc with ⟨hxl, hxr, hyl, hyr⟩ | ⟨hxl, hxr, hyl, hyr⟩
  · exact ⟨false, true, by simp [choiceAt, hxl, hxr], by simp [choiceAt, hyl, hyr], by decide⟩
  · exact ⟨true, false, by simp [choiceAt, hxl, hxr], by simp [choiceAt, hyl, hyr], by decide⟩

end AndPairSeparation

namespace AndChoiceBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.AndPairSeparation

def gateChoices (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (andPrefix C C.gates.length) → Option Bool :=
  fun k => choiceAt n C x k.val

lemma family_choices_separate {α : Type} (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, C.eval (List.ofFn (f a)) = false)
    (hjoin : ∀ a b, a ≠ b → C.eval (List.ofFn (fun i => f a i || f b i)) = true) :
    ∀ a b, a ≠ b → ∃ k u v,
      gateChoices n C (f a) k = some u ∧ gateChoices n C (f b) k = some v ∧ u ≠ v := by
  intro a b hab
  obtain ⟨k, hk, hop, hc⟩ := exists_crossed_and n C hAO (f a) (f b)
    (hfalse a) (hfalse b) (hjoin a b hab)
  have hkA : k ∈ andPrefix C C.gates.length := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
  obtain ⟨u, v, hu, hv, huv⟩ := crossed_choices n C (f a) (f b) k hc
  exact ⟨⟨k, hkA⟩, u, v, hu, hv, huv⟩

end AndChoiceBridge

namespace ChoiceSubcube

variable {α K : Type*}

def Compatible (p : K → Option Bool) (s : K → Bool) : Prop :=
  ∀ k b, p k = some b → s k = b

noncomputable def choiceSet [Fintype K] (p : K → Option Bool) : Finset (K → Bool) := by
  classical
  exact Finset.univ.filter (Compatible p)

noncomputable def forcedCount [Fintype K] (p : K → Option Bool) : Nat := by
  classical
  exact Fintype.card {k : K // p k ≠ none}

noncomputable def compatibleEquiv (p : K → Option Bool) :
    {s : K → Bool // Compatible p s} ≃ ({k : K // p k = none} → Bool) := by
  classical
  refine {
    toFun := fun s k => s.val k.val
    invFun := fun t => ⟨fun k => if h : p k = none then t ⟨k, h⟩ else (p k).getD false, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro k b hb
    simp [hb]
  · intro s
    apply Subtype.ext
    funext k
    cases hp : p k with
    | none => simp [hp]
    | some b => simpa [hp] using (s.property k b hp).symm
  · intro t
    funext k
    simp [k.property]

lemma choiceSet_card [Fintype K] (p : K → Option Bool) :
    (choiceSet p).card = 2 ^ (Fintype.card K - forcedCount p) := by
  classical
  have hm (s : K → Bool) : s ∈ choiceSet p ↔ Compatible p s := by
    simp [choiceSet]
  let e : (choiceSet p : Set (K → Bool)) ≃ {s : K → Bool // Compatible p s} :=
    Equiv.subtypeEquivRight hm
  have hfree : Fintype.card {k : K // p k = none} =
      Fintype.card K - forcedCount p := by
    simpa only [not_not, forcedCount] using
      (Fintype.card_subtype_compl (fun k : K => p k ≠ none))
  calc
    (choiceSet p).card = Fintype.card {s : K → Bool // Compatible p s} := by
      rw [← Fintype.card_coe (choiceSet p)]
      exact Fintype.card_congr e
    _ = Fintype.card ({k : K // p k = none} → Bool) :=
      Fintype.card_congr (compatibleEquiv p)
    _ = 2 ^ (Fintype.card K - forcedCount p) := by
      rw [Fintype.card_fun, Fintype.card_bool, hfree]

lemma disjoint_of_opposite [Fintype K] (p q : K → Option Bool)
    (h : ∃ k x y, p k = some x ∧ q k = some y ∧ x ≠ y) :
    Disjoint (choiceSet p) (choiceSet q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hs ht
  have hp : Compatible p s := by simpa [choiceSet] using hs
  have hq : Compatible q s := by simpa [choiceSet] using ht
  obtain ⟨k, x, y, hx, hy, hxy⟩ := h
  exact hxy ((hp k x hx).symm.trans (hq k y hy))

lemma sum_choiceSet_card [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, (choiceSet (p a)).card ≤ 2 ^ Fintype.card K := by
  classical
  have hd : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
      (fun a => choiceSet (p a)) := by
    intro a ha b hb hab
    exact disjoint_of_opposite (p a) (p b) (hsep a b hab)
  calc
    (∑ a, (choiceSet (p a)).card) =
        ((Finset.univ : Finset α).biUnion (fun a => choiceSet (p a))).card := by
      simpa using (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card (K → Bool) := by
      simpa using Finset.card_le_card
        (Finset.subset_univ ((Finset.univ : Finset α).biUnion (fun a => choiceSet (p a))))
    _ = 2 ^ Fintype.card K := by rw [Fintype.card_fun, Fintype.card_bool]

lemma sum_capacity [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, 2 ^ (Fintype.card K - forcedCount (p a)) ≤ 2 ^ Fintype.card K := by
  simpa only [choiceSet_card] using sum_choiceSet_card p hsep

def forcedSet [Fintype K] (p : K → Option Bool) : Finset K :=
  Finset.univ.filter (fun k => p k ≠ none)

lemma forcedCount_eq_card [Fintype K] (p : K → Option Bool) :
    forcedCount p = (forcedSet p).card := by
  classical
  let e : (forcedSet p : Set K) ≃ {k : K // p k ≠ none} :=
    Equiv.subtypeEquivRight (fun k => by simp [forcedSet])
  calc
    forcedCount p = Fintype.card (forcedSet p : Set K) :=
      (Fintype.card_congr e).symm
    _ = (forcedSet p).card := Fintype.card_coe _

lemma sum_forcedSet_capacity [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y) :
    ∑ a, 2 ^ (Fintype.card K - (forcedSet (p a)).card) ≤ 2 ^ Fintype.card K := by
  simpa only [forcedCount_eq_card] using sum_capacity p hsep

lemma forcedCount_eq_card_filter [Fintype K] (p : K → Option Bool) :
    forcedCount p = (Finset.univ.filter (fun k => p k ≠ none)).card := by
  simpa only [forcedSet] using forcedCount_eq_card p

end ChoiceSubcube

namespace AndChoiceKraft
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.AndPairSeparation
open PEqualNP.Outside.L_meta_2583.AndChoiceBridge
open PEqualNP.Outside.L_meta_2583.ChoiceSubcube
open scoped BigOperators

def oppositeAnds (n : ℕ) (C : Circuit) (x : Fin n → Bool) : Finset ℕ :=
  (andPrefix C C.gates.length).filter (fun k =>
    wv n C x (opnd C k 0) ≠ wv n C x (opnd C k 1))

lemma forcedCount_gateChoices (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    forcedCount (gateChoices n C x) = (oppositeAnds n C x).card := by
  classical
  rw [forcedCount_eq_card]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    have hchoice : choiceAt n C x k.val ≠ none := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨k.property, (choiceAt_forced_iff n C x k.val).mp hchoice⟩
  · intro k hk l hl hkl
    exact Subtype.ext hkl
  · intro k hk
    have hkA := (Finset.mem_filter.mp hk).1
    refine ⟨⟨k, hkA⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (choiceAt_forced_iff n C x k).mpr (Finset.mem_filter.mp hk).2⟩

lemma false_family_capacity {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (f : α → Fin n → Bool)
    (hfalse : ∀ a, C.eval (List.ofFn (f a)) = false)
    (hjoin : ∀ a b, a ≠ b → C.eval (List.ofFn (fun i => f a i || f b i)) = true) :
    ∑ a : α, 2 ^ ((andPrefix C C.gates.length).card - (oppositeAnds n C (f a)).card) ≤
      2 ^ (andPrefix C C.gates.length).card := by
  have h := sum_capacity (fun a => gateChoices n C (f a))
    (family_choices_separate n C hAO f hfalse hjoin)
  simpa only [Fintype.card_coe, forcedCount_gateChoices] using h

end AndChoiceKraft

namespace ChoiceSaturation

open ChoiceSubcube

variable {α K : Type*}

lemma choiceSet_nonempty [Fintype K] (p : K → Option Bool) : (choiceSet p).Nonempty := by
  apply Finset.card_pos.mp
  rw [choiceSet_card]
  exact pow_pos (by decide) _

lemma choiceSet_card_one_forced [Fintype K] (p : K → Option Bool)
    (hcard : (choiceSet p).card = 1) : ∀ k, p k ≠ none := by
  classical
  have hp : 2 ^ (Fintype.card K - forcedCount p) = 1 :=
    (choiceSet_card p).symm.trans hcard
  have hz : Fintype.card K - forcedCount p = 0 :=
    (Nat.pow_eq_one.mp hp).resolve_left (by decide)
  have hle : forcedCount p ≤ Fintype.card K :=
    Fintype.card_subtype_le (fun k : K => p k ≠ none)
  have hfull : (forcedSet p).card = Fintype.card K := by
    rw [← forcedCount_eq_card]
    omega
  have hs : forcedSet p = Finset.univ := Finset.eq_univ_of_card _ hfull
  intro k
  have hm : k ∈ forcedSet p := by rw [hs]; exact Finset.mem_univ _
  simpa [forcedSet] using hm

lemma none_coordinate_two_le_card [Fintype K] (p : K → Option Bool) (k : K)
    (hk : p k = none) : 2 ≤ (choiceSet p).card := by
  have hp : 1 ≤ (choiceSet p).card := Finset.one_le_card.mpr (choiceSet_nonempty p)
  have hn : (choiceSet p).card ≠ 1 := fun h => choiceSet_card_one_forced p h k hk
  omega

lemma family_singletons [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) :
    ∀ a, (choiceSet (p a)).card = 1 := by
  classical
  have hle : ∀ a ∈ (Finset.univ : Finset α), (1 : Nat) ≤ (choiceSet (p a)).card := by
    intro a ha
    exact Finset.one_le_card.mpr (choiceSet_nonempty (p a))
  have heq : (∑ a : α, (1 : Nat)) = ∑ a, (choiceSet (p a)).card := by
    apply le_antisymm
    · exact Finset.sum_le_sum hle
    · simpa [hfull] using sum_choiceSet_card p hsep
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro a
  exact (hpoint a (Finset.mem_univ _)).symm

lemma family_cover [Fintype α] [Fintype K] [DecidableEq K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) :
    (Finset.univ.biUnion (fun a => choiceSet (p a))) = Finset.univ := by
  classical
  have hd : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint
      (fun a => choiceSet (p a)) := by
    intro a ha b hb hab
    exact disjoint_of_opposite (p a) (p b) (hsep a b hab)
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion hd]
  simp [family_singletons p hsep hfull, hfull]

lemma exists_family_of_saturation [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) (s : K → Bool) :
    ∃ a, s ∈ choiceSet (p a) := by
  classical
  have hs : s ∈ Finset.univ.biUnion (fun a => choiceSet (p a)) := by
    rw [family_cover p hsep hfull]
    exact Finset.mem_univ _
  obtain ⟨a, ha, hm⟩ := Finset.mem_biUnion.mp hs
  exact ⟨a, hm⟩

lemma isolated_choiceSet_eq [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) (a : α) (q : K → Option Bool)
    (hdisj : ∀ b, b ≠ a → Disjoint (choiceSet q) (choiceSet (p b))) :
    choiceSet q = choiceSet (p a) := by
  classical
  have hsub : choiceSet q ⊆ choiceSet (p a) := by
    intro s hs
    obtain ⟨b, hb⟩ := exists_family_of_saturation p hsep hfull s
    by_cases hba : b = a
    · simpa [hba] using hb
    · exact False.elim (Finset.disjoint_left.mp (hdisj b hba) hs hb)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [family_singletons p hsep hfull a]
  exact Finset.one_le_card.mpr (choiceSet_nonempty q)

lemma isolated_choiceSet_card [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) (a : α) (q : K → Option Bool)
    (hdisj : ∀ b, b ≠ a → Disjoint (choiceSet q) (choiceSet (p b))) :
    (choiceSet q).card = 1 := by
  rw [isolated_choiceSet_eq p hsep hfull a q hdisj]
  exact family_singletons p hsep hfull a

lemma isolated_forced [Fintype α] [Fintype K] (p : α → K → Option Bool)
    (hsep : ∀ a b, a ≠ b → ∃ k x y, p a k = some x ∧ p b k = some y ∧ x ≠ y)
    (hfull : Fintype.card α = 2 ^ Fintype.card K) (a : α) (q : K → Option Bool)
    (hdisj : ∀ b, b ≠ a → Disjoint (choiceSet q) (choiceSet (p b))) :
    ∀ k, q k ≠ none :=
  choiceSet_card_one_forced q (isolated_choiceSet_card p hsep hfull a q hdisj)

end ChoiceSaturation

namespace AndChoiceRigidity
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse
open PEqualNP.Outside.L_meta_2583.MintermCircuit
open PEqualNP.Outside.L_meta_2583.AndSignature
open PEqualNP.Outside.L_meta_2583.AndPairSeparation
open PEqualNP.Outside.L_meta_2583.AndChoiceBridge
open PEqualNP.Outside.L_meta_2583.ChoiceSubcube

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wv_mono (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (hC : ReadsBack n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w : ℕ, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn, wv_input n C y w hwn]
      exact hxy ⟨w, hwn⟩
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n C x w hwg]
      intro h
      cases h
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hnw : n + k = w := by dsimp [k]; omega
      have hmem : gateAt C k ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        exact List.getElem_mem hk
      rw [← hnw, wv_rec n C x hC k hk, wv_rec n C y hC k hk]
      apply gateOp_mono _ (hAO _ hmem)
      intro u hu hux
      exact ih u (by have := hC k hk u hu; omega) hux


lemma common_choice_false_union (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = false) (hy : C.eval (List.ofFn y) = false)
    (s : (andPrefix C C.gates.length) → Bool)
    (hsx : Compatible (gateChoices n C x) s)
    (hsy : Compatible (gateChoices n C y) s) :
    C.eval (List.ofFn (fun i => x i || y i)) = false := by
  cases hj : C.eval (List.ofFn (fun i => x i || y i)) with
  | false => rfl
  | true =>
    obtain ⟨k, hk, hop, hc⟩ := exists_crossed_and n C hAO x y hx hy hj
    have hkA : k ∈ andPrefix C C.gates.length := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hk, by simp [isAnd, hop]⟩
    obtain ⟨b, c, hb, hc, hbc⟩ := crossed_choices n C x y k hc
    have heq : b = c := (hsx ⟨k, hkA⟩ b hb).symm.trans (hsy ⟨k, hkA⟩ c hc)
    exact (hbc heq).elim

lemma common_choiceSet_false_union (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool)
    (hx : C.eval (List.ofFn x) = false) (hy : C.eval (List.ofFn y) = false)
    (s : (andPrefix C C.gates.length) → Bool)
    (hsx : s ∈ choiceSet (gateChoices n C x))
    (hsy : s ∈ choiceSet (gateChoices n C y)) :
    C.eval (List.ofFn (fun i => x i || y i)) = false := by
  classical
  exact common_choice_false_union n C hAO x y hx hy s
    (by simpa [choiceSet] using hsx) (by simpa [choiceSet] using hsy)

lemma and_true_choice_none (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = .and)
    (ht : wv n C x (n + g) = true) : choiceAt n C x g = none := by
  rw [wv_rec n C x hAO.2.1 g hg, inputs_two n C hAO g hg] at ht
  have hh : wv n C x (opnd C g 0) = true ∧ wv n C x (opnd C g 1) = true := by
    simpa [hop, GateOp.eval] using ht
  simp [choiceAt, hh.1, hh.2]

open PEqualNP.Outside.L_meta_2583.ChoiceSaturation

lemma saturated_family_and_below_output {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (f : α → Fin n → Bool)
    (hfalse : ∀ a, C.eval (List.ofFn (f a)) = false)
    (hjoin : ∀ a b, a ≠ b → C.eval (List.ofFn (fun i => f a i || f b i)) = true)
    (hfull : Fintype.card α = 2 ^ (andPrefix C C.gates.length).card) :
    ∀ g < C.gates.length, (gateAt C g).op = .and →
      ∀ z : Fin n → Bool, wv n C z (n + g) = true → C.eval (List.ofFn z) = true := by
  classical
  intro g hg hop z hgz
  by_contra hn
  have hz : C.eval (List.ofFn z) = false := by
    cases h : C.eval (List.ofFn z) <;> simp_all
  let p : α → (andPrefix C C.gates.length) → Option Bool :=
    fun a => gateChoices n C (f a)
  have hsep := family_choices_separate n C hAO f hfalse hjoin
  have hfull' : Fintype.card α = 2 ^ Fintype.card (andPrefix C C.gates.length) := by
    simpa only [Fintype.card_coe] using hfull
  have hpos : 0 < (choiceSet (gateChoices n C z)).card := by
    rw [choiceSet_card]
    exact pow_pos (by decide) _
  obtain ⟨s, hsz⟩ := Finset.card_pos.mp hpos
  obtain ⟨a, hsa⟩ := exists_family_of_saturation p hsep hfull' s
  let M : Fin n → Bool := fun i => z i || f a i
  have hM : C.eval (List.ofFn M) = false :=
    common_choiceSet_false_union n C hAO z (f a) hz (hfalse a) s hsz hsa
  have hdisj : ∀ b, b ≠ a →
      Disjoint (choiceSet (gateChoices n C M)) (choiceSet (p b)) := by
    intro b hba
    apply Finset.disjoint_left.mpr
    intro t htM htb
    have hf := common_choiceSet_false_union n C hAO M (f b) hM (hfalse b) t htM htb
    have ht : C.eval (List.ofFn (fun i => M i || f b i)) = true := by
      apply wv_mono n C hAO.1 hAO.2.1 (fun i => f a i || f b i)
        (fun i => M i || f b i) ?_ C.output (hjoin a b (Ne.symm hba))
      intro i hi
      cases ha : f a i with
      | false =>
        have hb : f b i = true := by simpa [ha] using hi
        simp [hb]
      | true => simp [M, ha]
    rw [hf] at ht
    cases ht
  have hcard : (choiceSet (gateChoices n C M)).card = 1 :=
    isolated_choiceSet_card p hsep hfull' a (gateChoices n C M) hdisj
  have hgA : g ∈ andPrefix C C.gates.length := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hg, by simp [isAnd, hop]⟩
  have hforced := choiceSet_card_one_forced (gateChoices n C M) hcard ⟨g, hgA⟩
  have hgM : wv n C M (n + g) = true :=
    wv_mono n C hAO.1 hAO.2.1 z M (by intro i hi; simp [M, hi]) (n + g) hgz
  exact hforced (and_true_choice_none n C hAO M g hg hop hgM)

end AndChoiceRigidity

end PEqualNP.Outside.L_meta_2583
