import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Masking

lemma neighbor_count_le_cover
    {P L : Type} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) [DecidableRel I] (p : P) (S : Finset P)
    (hp : p ∉ S)
    (hunique : ∀ r : P, r ≠ p → ∀ l l' : L,
      I p l → I r l → I p l' → I r l' → l = l')
    (hcover : ∀ l : L, I p l → ∃ r ∈ S, I r l) :
    (Finset.univ.filter (fun l => I p l)).card ≤ S.card := by
  classical
  let f : L → P := fun l => if hl : I p l then (hcover l hl).choose else p
  have hf (l : L) (hl : I p l) : f l ∈ S ∧ I (f l) l := by
    simpa only [f, dite_eq_left hl] using (hcover l hl).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    exact (hf l (Finset.mem_filter.mp hl).2).1
  · intro l hl l' hl' heq
    have ha := (Finset.mem_filter.mp hl).2
    have hb := (Finset.mem_filter.mp hl').2
    have hne : f l ≠ p := by
      intro h
      exact hp (h ▸ (hf l ha).1)
    exact hunique (f l) hne l l' ha (hf l ha).2 hb (by rw [heq]; exact (hf l' hb).2)

lemma independent_line_extension_count
    {P L : Type} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
    (I : P → L → Prop) [DecidableRel I] (p : P)
    (X : P → Bool) (Y : L → Bool) (hp : X p = false)
    (hunique : ∀ r : P, r ≠ p → ∀ l l' : L,
      I p l → I r l → I p l' → I r l' → l = l')
    (hindependent : ¬ ∃ r k, I r k ∧ X r = true ∧ Y k = true)
    (hextend : ∀ l : L, I p l →
      ∃ r k, I r k ∧ X r = true ∧ Function.update Y l true k = true) :
    (Finset.univ.filter (fun l => I p l)).card ≤
      (Finset.univ.filter (fun r => X r = true)).card := by
  apply neighbor_count_le_cover I p (Finset.univ.filter (fun r => X r = true))
  · simp [hp]
  · exact hunique
  · intro l hl
    obtain ⟨r, k, hrk, hr, hk⟩ := hextend l hl
    have hkl : k = l := by
      by_contra hne
      exact hindependent ⟨r, k, hrk, hr, by simpa [Function.update_of_ne hne] using hk⟩
    exact ⟨r, by simp [hr], hkl ▸ hrk⟩

lemma plane_independent_line_extension_count
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p : Fin N) (X Y : Fin N → Bool) (hp : X p = false)
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (hindependent : ¬ ∃ r k, I r k ∧ X r = true ∧ Y k = true)
    (hextend : ∀ l : Fin N, I p l →
      ∃ r k, I r k ∧ X r = true ∧ Function.update Y l true k = true) :
    q + 1 ≤ (Finset.univ.filter (fun r => X r = true)).card := by
  rw [← hdegree]
  apply independent_line_extension_count I p X Y hp ?_ hindependent hextend
  intro r hr l l' hpl hrl hpl' hrl'
  obtain ⟨a, ha, hua⟩ := hunique p r (Ne.symm hr)
  exact (hua l ⟨hpl, hrl⟩).trans (hua l' ⟨hpl', hrl'⟩).symm

end PEqualNP.Outside.L_meta_2583.Masking

namespace PEqualNP.Outside.L_meta_2583.SingleUse

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

lemma unique_read_mask (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (j w : ℕ) (hj : j < C.gates.length)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (b : Bool) (hm : ∀ t : Bool, (gateAt C j).op.eval [t, wv n C x w] = b) :
    ∀ v : ℕ, v ≠ p.val → wv n C x v = wv n C y v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hvp
    by_cases hvn : v < n
    · rw [wv_input n C x v hvn, wv_input n C y v hvn]
      exact hxy ⟨v, hvn⟩ (fun h => hvp (congrArg Fin.val h))
    by_cases hvg : v < n + C.gates.length
    · let k := v - n
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hnv : n + k = v := by dsimp [k]; omega
      rw [← hnv, wv_rec n C x hC k hk, wv_rec n C y hC k hk]
      by_cases hkj : k = j
      · rw [hkj]
        have hwm : w ∈ (gateAt C j).inputs := by rw [hin]; simp
        have hwl : w < v := by have := hC j hj w hwm; omega
        have hwe := ih w hwl hwp
        rw [hin]
        simp only [List.map_cons, List.map_nil]
        rw [← hwe, hm, hm]
      · congr 1
        apply List.map_congr_left
        intro u hu
        have hup : u ≠ p.val := by
          intro hup
          subst u
          exact hkj (hsole k hk hu)
        exact ih u (by have := hC k hk u hu; omega) hup
    · rw [wv_missing n C x v (by omega), wv_missing n C y v (by omega)]

lemma unique_or_mask (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (hw : wv n C x w = true) (hout : C.output ≠ p.val) :
    circuitFun n C x = circuitFun n C y := by
  apply unique_read_mask n C hC p j w hj hin hwp hsole x y hxy true _ C.output hout
  intro t
  simp [hop, GateOp.eval, hw]

lemma unique_and_mask (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (hw : wv n C x w = false) (hout : C.output ≠ p.val) :
    circuitFun n C x = circuitFun n C y := by
  apply unique_read_mask n C hC p j w hj hin hwp hsole x y hxy false _ C.output hout
  intro t
  simp [hop, GateOp.eval, hw]

lemma unique_read_prefix_eq (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (j : ℕ) (hj : j < C.gates.length)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i) :
    ∀ v : ℕ, v < n + j → v ≠ p.val → wv n C x v = wv n C y v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv hvp
    by_cases hvn : v < n
    · rw [wv_input n C x v hvn, wv_input n C y v hvn]
      exact hxy ⟨v, hvn⟩ (fun h => hvp (congrArg Fin.val h))
    · let k := v - n
      have hkj : k < j := by dsimp [k]; omega
      have hk : k < C.gates.length := by omega
      have hnv : n + k = v := by dsimp [k]; omega
      rw [← hnv, wv_rec n C x hC k hk, wv_rec n C y hC k hk]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hul : u < v := by have := hC k hk u hu; omega
      have hup : u ≠ p.val := by
        intro hup
        subst u
        have := hsole k hk hu
        omega
      exact ih u hul (by omega) hup

lemma unique_and_required (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (hdiff : circuitFun n C x ≠ circuitFun n C y) (hout : C.output ≠ p.val) :
    wv n C x w = true := by
  cases hw : wv n C x w with
  | false => exact False.elim (hdiff (unique_and_mask n C hC p j w hj hop hin hwp hsole x y hxy hw hout))
  | true => rfl

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

end PEqualNP.Outside.L_meta_2583.SingleUse
namespace PEqualNP.Outside.L_meta_2583.PlaneSingleUse

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse

lemma point_ne_line {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma line_update_point {N : ℕ} (z : Fin (N + N) → Bool) (l p : Fin N) :
    Function.update z (Fin.natAdd N l) true (Fin.castAdd N p) = z (Fin.castAdd N p) := by
  exact Function.update_of_ne (point_ne_line p l) true z

lemma line_update_line {N : ℕ} (z : Fin (N + N) → Bool) (l k : Fin N) :
    Function.update z (Fin.natAdd N l) true (Fin.natAdd N k) =
      Function.update (fun a => z (Fin.natAdd N a)) l true k := by
  by_cases h : k = l
  · subst k
    simp
  · have hne : Fin.natAdd N k ≠ Fin.natAdd N l := by
      intro heq
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp only [Fin.val_natAdd] at hv
      omega
    rw [Function.update_of_ne hne, Function.update_of_ne h]

lemma point_or_sibling_count
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (hout : C.output ≠ p.val)
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (z : Fin (N + N) → Bool) (hzp : z (Fin.castAdd N p) = false)
    (hfalse : circuitFun (N + N) C z = false)
    (hw : wv (N + N) C z w = true) :
    q + 1 ≤ (Finset.univ.filter (fun r => z (Fin.castAdd N r) = true)).card := by
  apply Masking.plane_independent_line_extension_count q N I p
    (fun r => z (Fin.castAdd N r)) (fun l => z (Fin.natAdd N l)) hzp hdegree hunique
  · intro h
    have ht : circuitFun (N + N) C z = true := by
      rw [hfun]
      exact decide_eq_true h
    simp [hfalse] at ht
  · intro l hl
    let z' : Fin (N + N) → Bool := Function.update z (Fin.natAdd N l) true
    let z'' : Fin (N + N) → Bool := Function.update z' (Fin.castAdd N p) true
    have hmono : ∀ i, z i = true → z' i = true := by
      intro i hi
      by_cases heq : i = Fin.natAdd N l
      · subst i
        simp [z']
      · change Function.update z (Fin.natAdd N l) true i = true
        rw [Function.update_of_ne heq]
        exact hi
    have hw' : wv (N + N) C z' w = true :=
      wv_mono (N + N) C hC.1 hC.2.1 z z' hmono w hw
    have hxy : ∀ i : Fin (N + N), i ≠ Fin.castAdd N p → z' i = z'' i := by
      intro i hi
      simp [z'', Function.update_of_ne hi]
    have hmask : circuitFun (N + N) C z' = circuitFun (N + N) C z'' :=
      unique_or_mask (N + N) C hC.2.1 (Fin.castAdd N p) j w hj hop hin hwp
        hsole z' z'' hxy hw' hout
    have ht : circuitFun (N + N) C z'' = true := by
      rw [hfun]
      apply decide_eq_true
      refine ⟨p, l, hl, ?_, ?_⟩
      · simp [z'']
      · simp only [z'', Function.update_of_ne (Ne.symm (point_ne_line p l)), z', Function.update_self]
    have hresult := hmask.trans ht
    rw [hfun] at hresult
    obtain ⟨r, k, hrk, hr, hk⟩ := of_decide_eq_true hresult
    refine ⟨r, k, hrk, ?_, ?_⟩
    · exact (line_update_point z l r) ▸ hr
    · exact (line_update_line z l k) ▸ hk

lemma point_or_sibling_count_general
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (hout : C.output ≠ p.val)
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (z : Fin (N + N) → Bool) (hfalse : circuitFun (N + N) C z = false)
    (hw : wv (N + N) C z w = true) :
    q + 1 ≤ (Finset.univ.filter (fun r => z (Fin.castAdd N r) = true)).card := by
  let x : Fin (N + N) → Bool := Function.update z (Fin.castAdd N p) false
  have hx : x (Fin.castAdd N p) = false := by simp [x]
  have hxz : ∀ i : Fin (N + N), x i = true → z i = true := by
    intro i hi
    by_cases heq : i = Fin.castAdd N p
    · subst i
      simp [x] at hi
    · exact (Function.update_of_ne heq false z) ▸ hi
  have hxy : ∀ i : Fin (N + N), i ≠ Fin.castAdd N p → x i = z i := by
    intro i hi
    exact Function.update_of_ne hi false z
  have hwl : w < N + N + j := hC.2.1 j hj w (by rw [hin]; simp)
  have hwx : wv (N + N) C x w = true := by
    rw [unique_read_prefix_eq (N + N) C hC.2.1 (Fin.castAdd N p) j hj
      hsole x z hxy w hwl hwp]
    exact hw
  have hfalsex : circuitFun (N + N) C x = false := by
    cases heq : circuitFun (N + N) C x with
    | false => rfl
    | true =>
      have ht : circuitFun (N + N) C z = true :=
        wv_mono (N + N) C hC.1 hC.2.1 x z hxz C.output heq
      simp [hfalse] at ht
  have hcount := point_or_sibling_count q N I C hC hfun p j w hj hop hin hwp
    hsole hout hdegree hunique x hx hfalsex hwx
  apply hcount.trans
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,
    hxz (Fin.castAdd N r) (Finset.mem_filter.mp hr).2⟩

lemma point_or_sibling_sparse_sound
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (hout : C.output ≠ p.val)
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (z : Fin (N + N) → Bool)
    (hsparse : (Finset.univ.filter (fun r => z (Fin.castAdd N r) = true)).card ≤ q)
    (hw : wv (N + N) C z w = true) : circuitFun (N + N) C z = true := by
  cases hz : circuitFun (N + N) C z with
  | false =>
    have := point_or_sibling_count_general q N I C hC hfun p j w hj hop hin hwp
      hsole hout hdegree hunique z hz hw
    omega
  | true => rfl

end PEqualNP.Outside.L_meta_2583.PlaneSingleUse


namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

abbrev p4incidence (p l : Fin 2) : Prop := p = 1 ∨ l = 0

def p4Circuit : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [6, 5]⟩], 7⟩

def p4ReadOneCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

lemma p4_no_four_cycle : ∀ p p' l l' : Fin 2, p ≠ p' → l ≠ l' →
    ¬ (p4incidence p l ∧ p4incidence p l' ∧ p4incidence p' l ∧ p4incidence p' l') := by
  decide

lemma p4_ao2 : IsAO2 4 p4Circuit := by decide

lemma p4_size : p4Circuit.size = 4 := rfl

lemma p4_function : ∀ z : Fin (2 + 2) → Bool,
    circuitFun (2 + 2) p4Circuit z = decide (∃ p l : Fin 2,
      p4incidence p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
  decide

lemma p4_bad_pair_prime : IsPrimeImplicant 4 p4Circuit {1, 3} := by decide

lemma p4_bad_pair_vectors :
    (readVectors p4Circuit 4 [1, 3] 1).getD p4Circuit.output [] = [[2, 1]] := by decide

lemma p4_not_read_one : ¬ IsReadK 4 p4Circuit 1 := by decide

lemma p4_replacement_ao2 : IsAO2 4 p4ReadOneCircuit := by decide

lemma p4_replacement_size : p4ReadOneCircuit.size = 4 := rfl

lemma p4_replacement_function : ∀ z : Fin (2 + 2) → Bool,
    circuitFun (2 + 2) p4ReadOneCircuit z = decide (∃ p l : Fin 2,
      p4incidence p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
  decide

lemma p4_replacement_read_one : IsReadK 4 p4ReadOneCircuit 1 := by decide

end PEqualNP.Outside.L_meta_2583_aux


namespace PEqualNP.Outside.L_meta_2583_aux

lemma singleton_star_product_clean {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hno4 : ∀ a c : Fin P, ∀ u v : Fin L, a ≠ c → u ≠ v →
      ¬ (I a u ∧ I a v ∧ I c u ∧ I c v))
    (a c : Fin P) (hac : a ≠ c) (S T : Finset (Fin L))
    (hT : 2 ≤ T.card) (hstar : ∀ y ∈ T, I a y)
    (hcross : ∀ x ∈ S, ∀ y ∈ T, I c x ∨ I c y) :
    ∀ x ∈ S, I c x := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  intro x hx
  by_contra hcx
  have hcu : I c u := (hcross x hx u hu).resolve_left hcx
  have hcv : I c v := (hcross x hx v hv).resolve_left hcx
  exact hno4 a c u v hac huv ⟨hstar u hu, hstar v hv, hcu, hcv⟩

end PEqualNP.Outside.L_meta_2583_aux
