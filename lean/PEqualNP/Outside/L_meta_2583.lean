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

namespace PEqualNP.Outside.L_meta_2583.Masking

lemma point_degree_of_plane
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let A := Finset.univ.filter (fun l => I p l)
  let B := fun l => (Finset.univ.filter (fun r => I r l)).erase p
  have hB : ∀ l ∈ A, (B l).card = q := by
    intro l hl
    have hp : p ∈ Finset.univ.filter (fun r => I r l) := by
      simpa [A] using hl
    simp only [B, Finset.card_erase_of_mem hp, hcols]
    omega
  have hdisj : (A : Set (Fin N)).PairwiseDisjoint B := by
    intro l hl k hk hne
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrl := Finset.mem_erase.mp hr
    have hrk := Finset.mem_erase.mp hr'
    obtain ⟨a, ha, hua⟩ := hunique p r (Ne.symm hrl.1)
    apply hne
    exact (hua l ⟨(Finset.mem_filter.mp hl).2,
      (Finset.mem_filter.mp hrl.2).2⟩).trans
      (hua k ⟨(Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hrk.2).2⟩).symm
  have hcover : A.biUnion B = Finset.univ.erase p := by
    ext r
    constructor
    · intro hr
      obtain ⟨l, hl, hrl⟩ := Finset.mem_biUnion.mp hr
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hrl).1, Finset.mem_univ r⟩
    · intro hr
      have hrp := (Finset.mem_erase.mp hr).1
      obtain ⟨l, hl, hu⟩ := hunique p r (Ne.symm hrp)
      apply Finset.mem_biUnion.mpr
      refine ⟨l, ?_, ?_⟩
      · simp [A, hl.1]
      · simp [B, hrp, hl.2]
  have hcard : (A.biUnion B).card = A.card * q := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ l ∈ A, (B l).card = ∑ _l ∈ A, q := Finset.sum_congr rfl hB
      _ = A.card * q := by simp
  have hcount : N - 1 = A.card * q := by simpa [hcover] using hcard
  have hNpos : 1 ≤ N := by omega
  have hNm : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  have hmul : q * A.card = q * (q + 1) := by nlinarith
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

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


lemma incidence_output_ne_point
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true)) (p : Fin N) : C.output ≠ p.val := by
  intro hout
  let z : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p)
  have hp : p.val < N + N := by omega
  have ht : circuitFun (N + N) C z = true := by
    change wv (N + N) C z C.output = true
    rw [hout, wv_input (N + N) C z p.val hp]
    exact decide_eq_true (Fin.ext rfl)
  rw [hfun] at ht
  obtain ⟨r, l, _, _, hl⟩ := of_decide_eq_true ht
  exact point_ne_line p l (of_decide_eq_true hl).symm

lemma point_or_sibling_sparse_sound_of_plane
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (z : Fin (N + N) → Bool)
    (hsparse : (Finset.univ.filter (fun r => z (Fin.castAdd N r) = true)).card ≤ q)
    (hw : wv (N + N) C z w = true) : circuitFun (N + N) C z = true := by
  exact point_or_sibling_sparse_sound q N I C hC hfun p j w hj hop hin hwp hsole
    (incidence_output_ne_point N I C hfun p)
    (Masking.point_degree_of_plane q N I hq hN hcols hunique p) hunique z hsparse hw


lemma point_and_sibling_singletons
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j) :
    ∀ l : Fin N, I p l → wv (N + N) C
      (fun i => decide (i = Fin.natAdd N l)) w = true := by
  intro l hl
  let x : Fin (N + N) → Bool := fun i => decide (i = Fin.natAdd N l)
  let y : Fin (N + N) → Bool := Function.update x (Fin.castAdd N p) true
  have hxy : ∀ i : Fin (N + N), i ≠ Fin.castAdd N p → x i = y i := by
    intro i hi
    exact (Function.update_of_ne hi true x).symm
  have hf : circuitFun (N + N) C x = false := by
    rw [hfun]
    apply decide_eq_false
    rintro ⟨r, k, _, hr, _⟩
    exact point_ne_line r l (of_decide_eq_true hr)
  have ht : circuitFun (N + N) C y = true := by
    rw [hfun]
    apply decide_eq_true
    refine ⟨p, l, hl, ?_, ?_⟩
    · simp only [y, Function.update_self]
    · simp only [y, Function.update_of_ne (Ne.symm (point_ne_line p l)), x,
        decide_true]
  exact unique_and_required (N + N) C hC.2.1 (Fin.castAdd N p) j w hj hop hin hwp
    hsole x y hxy (by rw [hf, ht]; decide) (incidence_output_ne_point N I C hfun p)

end PEqualNP.Outside.L_meta_2583.PlaneSingleUse

namespace PEqualNP.Outside.L_meta_2583.Minterm

lemma support_family_bound {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost + t.card := by
  induction m with
  | zero =>
    intro t ht
    have h1 := Finset.card_biUnion_le (s := t) (t := s)
    have h2 : ∑ i ∈ t, (s i).card ≤ t.card := by
      calc
        ∑ i ∈ t, (s i).card ≤ ∑ i ∈ t, 1 := Finset.sum_le_sum fun i hi =>
          hinput i (by have := ht hi; simpa using this)
        _ = t.card := by simp
    simpa using h1.trans h2
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Finset.mem_biUnion.mp hx
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hxj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hxi⟩
      have huc : u.card ≤ t.card + cost m := by
        have h1 := Finset.card_union_le (t.erase (n + m)) (a m)
        have h2 := Finset.card_erase_add_one hm
        have h3 := hcost m (by omega)
        dsimp only [u]
        omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega

def pickedSupport (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) : Finset (Fin n) :=
  if hw : w < n then {⟨w, hw⟩}
  else if _hg : w < n + m then
    if both (w - n) then
      pickedSupport n m a b both left ha hb (a (w - n)) ∪
      pickedSupport n m a b both left ha hb (b (w - n))
    else if left (w - n) then
      pickedSupport n m a b both left ha hb (a (w - n))
    else pickedSupport n m a b both left ha hb (b (w - n))
  else ∅
termination_by w
decreasing_by
  all_goals have hk : w - n < m := by omega
  · have := ha (w - n) hk; omega
  · have := hb (w - n) hk; omega
  · have := ha (w - n) hk; omega
  · have := hb (w - n) hk; omega

lemma pickedSupport_input (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) (hw : w < n) :
    pickedSupport n m a b both left ha hb w = {⟨w, hw⟩} := by
  rw [pickedSupport, dite_eq_left hw]

lemma pickedSupport_gate (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (k : ℕ) (hk : k < m) :
    pickedSupport n m a b both left ha hb (n + k) =
      if both k then
        pickedSupport n m a b both left ha hb (a k) ∪
        pickedSupport n m a b both left ha hb (b k)
      else if left k then pickedSupport n m a b both left ha hb (a k)
      else pickedSupport n m a b both left ha hb (b k) := by
  rw [pickedSupport, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp only [Nat.add_sub_cancel_left]

lemma pickedSupport_bound (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (w : ℕ) (hw : w < n + m) :
    (pickedSupport n m a b both left ha hb w).card ≤
      ((Finset.range m).filter fun k => both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let parents : ℕ → Finset ℕ := fun k =>
    if both k then {a k, b k} else if left k then {a k} else {b k}
  let cost : ℕ → ℕ := fun k => if both k then 1 else 0
  have hinput : ∀ i < n, (s i).card ≤ 1 := by
    intro i hi
    simp [s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k hk)
      · exact Finset.mem_range.mpr (hb k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k hk)
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k _
    simp only [parents, cost]
    split_ifs <;> first | exact Finset.card_le_two | simp
  have hv : ∀ k < m, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    dsimp only [s, parents]
    rw [pickedSupport_gate n m a b both left ha hb k hk]
    split_ifs <;> simp
  have hmain := support_family_bound n m s parents cost hinput hp hc hv {w}
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact Finset.mem_range.mpr hw)
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [s, hsum] using hmain

lemma pickedSupport_bound_prefix (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (r : ℕ) (hr : r ≤ m) (w : ℕ) (hw : w < n + r) :
    (pickedSupport n m a b both left ha hb w).card ≤
      ((Finset.range r).filter fun k => both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let parents : ℕ → Finset ℕ := fun k =>
    if both k then {a k, b k} else if left k then {a k} else {b k}
  let cost : ℕ → ℕ := fun k => if both k then 1 else 0
  have hinput : ∀ i < n, (s i).card ≤ 1 := by
    intro i hi
    simp [s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < r, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
      · exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
  have hc : ∀ k < r, (parents k).card ≤ cost k + 1 := by
    intro k _
    simp only [parents, cost]
    split_ifs <;> first | exact Finset.card_le_two | simp
  have hv : ∀ k < r, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    dsimp only [s, parents]
    rw [pickedSupport_gate n m a b both left ha hb k (lt_of_lt_of_le hk hr)]
    split_ifs <;> simp
  have hmain := support_family_bound n r s parents cost hinput hp hc hv {w}
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact Finset.mem_range.mpr hw)
  have hsum : (Finset.range r).sum cost =
      ((Finset.range r).filter fun k => both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [s, hsum] using hmain

lemma pickedSupport_bound_closed (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (R : Finset ℕ)
    (hRa : ∀ k ∈ R, k < m → a k < n ∨ a k - n ∈ R)
    (hRb : ∀ k ∈ R, k < m → b k < n ∨ b k - n ∈ R)
    (w : ℕ) (hw : w < n + m) (hwR : w < n ∨ w - n ∈ R) :
    (pickedSupport n m a b both left ha hb w).card ≤
      ((Finset.range m).filter fun k => k ∈ R ∧ both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let ss : ℕ → Finset (Fin n) := fun v => if v < n ∨ v - n ∈ R then s v else ∅
  let parents : ℕ → Finset ℕ := fun k => if k ∈ R then
    if both k then {a k, b k} else if left k then {a k} else {b k}
    else ∅
  let cost : ℕ → ℕ := fun k => if k ∈ R ∧ both k = true then 1 else 0
  have hinput : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hi
    simp [ss, hi, s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with hR h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k hk)
      · exact Finset.mem_range.mpr (hb k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k hk)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k hk)
    · exact False.elim (Finset.notMem_empty _ hi)
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k _
    dsimp only [parents, cost]
    split_ifs <;> simp_all
    exact Finset.card_le_two
  have hv : ∀ k < m, ss (n + k) ⊆ (parents k).biUnion ss := by
    intro k hk
    by_cases hkR : k ∈ R
    · have hs0 : ss (n + k) = s (n + k) := by simp [ss, hkR]
      have hsa : ss (a k) = s (a k) := by rw [show ss (a k) = if a k < n ∨ a k - n ∈ R then s (a k) else ∅ from rfl, ite_eq_left (hRa k hkR hk)]
      have hsb : ss (b k) = s (b k) := by rw [show ss (b k) = if b k < n ∨ b k - n ∈ R then s (b k) else ∅ from rfl, ite_eq_left (hRb k hkR hk)]
      rw [hs0]
      change pickedSupport n m a b both left ha hb (n + k) ⊆ _
      rw [pickedSupport_gate n m a b both left ha hb k hk]
      simp only [parents, hkR, ↓reduceIte]
      split_ifs <;> simp [hsa, hsb, s]
    · have hs0 : ss (n + k) = ∅ := by simp [ss, hkR]
      rw [hs0]
      exact Finset.empty_subset _
  have hmain := support_family_bound n m ss parents cost hinput hp hc hv {w}
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact Finset.mem_range.mpr hw)
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => k ∈ R ∧ both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [ss, hwR, s, hsum] using hmain

end PEqualNP.Outside.L_meta_2583.Minterm
namespace PEqualNP.Outside.L_meta_2583.MintermCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm

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

def pickedBoth (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => wv n C x (n + k)
  | _ => false

def circuitSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (pickedBoth n C x) (fun k => wv n C x (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

lemma circuitSupport_input (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    circuitSupport n C hAO x w = {⟨w, hw⟩} := by
  exact pickedSupport_input _ _ _ _ _ _ _ _ _ hw

lemma circuitSupport_gate (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    circuitSupport n C hAO x (n + k) =
      if pickedBoth n C x k then
        circuitSupport n C hAO x (opnd C k 0) ∪ circuitSupport n C hAO x (opnd C k 1)
      else if wv n C x (opnd C k 0) then circuitSupport n C hAO x (opnd C k 0)
      else circuitSupport n C hAO x (opnd C k 1) := by
  exact pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

lemma support_sound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (S : Finset (Fin n)) :
    ∀ w : ℕ, wv n C (setInput S) w = true →
      circuitSupport n C hAO (setInput S) w ⊆ S ∧
      wv n C (setInput (circuitSupport n C hAO (setInput S) w)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwtrue
    by_cases hwn : w < n
    · rw [circuitSupport_input n C hAO (setInput S) w hwn]
      rw [wv_input n C (setInput S) w hwn] at hwtrue
      constructor
      · simp only [Finset.singleton_subset_iff]
        exact of_decide_eq_true hwtrue
      · rw [wv_input n C _ w hwn]
        simp [setInput]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n C (setInput S) w hwg] at hwtrue
      cases hwtrue
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha : opnd C k 0 < n + k := opnd_back n C hAO k hk 0
      have hb : opnd C k 1 < n + k := opnd_back n C hAO k hk 1
      have hgate := wv_rec n C (setInput S) hAO.2.1 k hk
      rw [inputs_two n C hAO k hk] at hgate
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hbits : wv n C (setInput S) (opnd C k 0) = true ∧
            wv n C (setInput S) (opnd C k 1) = true := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hwtrue
        have hsa := ih _ ha hbits.1
        have hsb := ih _ hb hbits.2
        rw [circuitSupport_gate n C hAO (setInput S) k hk]
        simp only [pickedBoth, hop, hwtrue, ↓reduceIte]
        change circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
            circuitSupport n C hAO (setInput S) (opnd C k 1) ⊆ S ∧ _
        constructor
        · exact Finset.union_subset hsa.1 hsb.1
        · have hma := wv_mono n C hAO.1 hAO.2.1 _
              (setInput (circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
                circuitSupport n C hAO (setInput S) (opnd C k 1)))
              (fun i hi => by
                simp only [setInput, decide_eq_true_eq] at hi ⊢
                exact Finset.mem_union_left _ hi) _ hsa.2
          have hmb := wv_mono n C hAO.1 hAO.2.1 _
              (setInput (circuitSupport n C hAO (setInput S) (opnd C k 0) ∪
                circuitSupport n C hAO (setInput S) (opnd C k 1)))
              (fun i hi => by
                simp only [setInput, decide_eq_true_eq] at hi ⊢
                exact Finset.mem_union_right _ hi) _ hsb.2
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simpa [hop, GateOp.eval] using And.intro hma hmb
      · have hbits : wv n C (setInput S) (opnd C k 0) = true ∨
            wv n C (setInput S) (opnd C k 1) = true := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hwtrue
        rw [circuitSupport_gate n C hAO (setInput S) k hk]
        simp only [pickedBoth, hop, Bool.false_eq_true, ↓reduceIte]
        by_cases hat : wv n C (setInput S) (opnd C k 0) = true
        · rw [ite_eq_left hat]
          have hsa := ih _ ha hat
          refine ⟨hsa.1, ?_⟩
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hsa.2]
        · rw [ite_eq_right hat]
          have hsb := ih _ hb (hbits.resolve_left hat)
          refine ⟨hsb.1, ?_⟩
          rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hsb.2]

lemma minimal_support_card_le_true_ands (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hw : wv n C (setInput S) w = true)
    (hmin : ∀ T ⊆ S, wv n C (setInput T) w = true → S ⊆ T) :
    S.card ≤ ((Finset.range C.gates.length).filter fun k =>
      pickedBoth n C (setInput S) k = true).card + 1 := by
  classical
  have hvalid : w < n + C.gates.length := by
    by_contra h
    rw [wv_missing n C (setInput S) w (by omega)] at hw
    cases hw
  have hsound := support_sound n C hAO S w hw
  have hS : S = circuitSupport n C hAO (setInput S) w :=
    Finset.Subset.antisymm (hmin _ hsound.1 hsound.2) hsound.1
  have hbound := pickedSupport_bound n C.gates.length (fun k => opnd C k 0)
    (fun k => opnd C k 1) (pickedBoth n C (setInput S))
    (fun k => wv n C (setInput S) (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w hvalid
  calc
    S.card = (circuitSupport n C hAO (setInput S) w).card := congrArg Finset.card hS
    _ ≤ _ := hbound

lemma true_ands_subset_junk (n : ℕ) (C : Circuit)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool)
    (hx : graphFun G ∅ x = false) :
    ((Finset.range C.gates.length).filter fun k => pickedBoth n C x k = true) ⊆ junk G C := by
  intro k hk
  obtain ⟨hk, hboth⟩ := Finset.mem_filter.mp hk
  have hop : (gateAt C k).op = GateOp.and := by
    cases h : (gateAt C k).op <;> simp [pickedBoth, h] at hboth ⊢
  have hval : wv n C x (n + k) = true := by simpa [pickedBoth, hop] using hboth
  apply Finset.mem_filter.mpr
  refine ⟨hk, hop, Finset.mem_range.mp hk, x, ?_, hx⟩
  exact hval

lemma exists_small_accepting_support (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hw : wv n C (setInput S) w = true) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ wv n C (setInput T) w = true ∧
      T.card ≤ ((Finset.range C.gates.length).filter fun k =>
        pickedBoth n C (setInput S) k = true).card + 1 := by
  have hvalid : w < n + C.gates.length := by
    by_contra h
    rw [wv_missing n C (setInput S) w (by omega)] at hw
    cases hw
  have hsound := support_sound n C hAO S w hw
  refine ⟨circuitSupport n C hAO (setInput S) w, hsound.1, hsound.2, ?_⟩
  exact pickedSupport_bound n C.gates.length (fun k => opnd C k 0)
    (fun k => opnd C k 1) (pickedBoth n C (setInput S))
    (fun k => wv n C (setInput S) (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w hvalid

lemma dirty_wire_small_support (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : graphFun G ∅ (setInput S) = false)
    (w : ℕ) (hw : wv n C (setInput S) w = true) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ wv n C (setInput T) w = true ∧
      T.card ≤ (junk G C).card + 1 := by
  obtain ⟨T, hT, hTw, hbound⟩ := exists_small_accepting_support n C hAO S w hw
  refine ⟨T, hT, hTw, ?_⟩
  exact hbound.trans (Nat.add_le_add_right
    (Finset.card_le_card (true_ands_subset_junk n C G (setInput S) hS)) 1)

lemma exists_small_accepting_support_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hw : wv n C (setInput S) w = true)
    (r : ℕ) (hr : r ≤ C.gates.length) (hwr : w < n + r) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ wv n C (setInput T) w = true ∧
      T.card ≤ ((Finset.range r).filter fun k => pickedBoth n C (setInput S) k = true).card + 1 := by
  have hsound := support_sound n C hAO S w hw
  refine ⟨circuitSupport n C hAO (setInput S) w, hsound.1, hsound.2, ?_⟩
  exact pickedSupport_bound_prefix n C.gates.length (fun k => opnd C k 0)
    (fun k => opnd C k 1) (pickedBoth n C (setInput S))
    (fun k => wv n C (setInput S) (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) r hr w hwr

lemma dirty_wire_small_support_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : graphFun G ∅ (setInput S) = false)
    (w : ℕ) (hw : wv n C (setInput S) w = true)
    (r : ℕ) (hr : r ≤ C.gates.length) (hwr : w < n + r) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ wv n C (setInput T) w = true ∧
      T.card ≤ (junk G C ∩ Finset.range r).card + 1 := by
  obtain ⟨T, hT, hTw, hbound⟩ := exists_small_accepting_support_prefix n C hAO S w hw r hr hwr
  refine ⟨T, hT, hTw, hbound.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)⟩
  intro k hk
  obtain ⟨hkr, hboth⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_inter.mpr
  refine ⟨true_ands_subset_junk n C G (setInput S) hS ?_, hkr⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hkr) hr), hboth⟩

lemma dirty_wire_small_support_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : graphFun G ∅ (setInput S) = false)
    (R : Finset ℕ)
    (hR : ∀ k ∈ R, k < C.gates.length → ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : ℕ) (hw : wv n C (setInput S) w = true) (hwR : w < n ∨ w - n ∈ R) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ wv n C (setInput T) w = true ∧
      T.card ≤ (junk G C ∩ R).card + 1 := by
  have hvalid : w < n + C.gates.length := by
    by_contra h
    rw [wv_missing n C (setInput S) w (by omega)] at hw
    cases hw
  have hsound := support_sound n C hAO S w hw
  refine ⟨circuitSupport n C hAO (setInput S) w, hsound.1, hsound.2, ?_⟩
  have hbound := pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
    (fun k => opnd C k 1) (pickedBoth n C (setInput S))
    (fun k => wv n C (setInput S) (opnd C k 0))
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) R
    (fun k hk hkl => hR k hk hkl 0) (fun k hk hkl => hR k hk hkl 1) w hvalid hwR
  refine hbound.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
  intro k hk
  obtain ⟨hkr, hkR, hboth⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_inter.mpr
  exact ⟨true_ands_subset_junk n C G (setInput S) hS
    (Finset.mem_filter.mpr ⟨hkr, hboth⟩), hkR⟩

end PEqualNP.Outside.L_meta_2583.MintermCircuit
namespace PEqualNP.Outside.L_meta_2583.PlaneSingleUse

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma point_support_card_le {N : ℕ} (S : Finset (Fin (N + N))) :
    (Finset.univ.filter (fun r : Fin N => setInput S (Fin.castAdd N r) = true)).card ≤
      S.card := by
  apply Finset.card_le_card_of_injOn (Fin.castAdd N)
  · intro r hr
    exact of_decide_eq_true (Finset.mem_filter.mp hr).2
  · intro a ha b hb hab
    apply Fin.ext
    exact congrArg (fun i : Fin (N + N) => i.val) hab

lemma point_or_dirty_sibling_needs_junk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z, circuitFun (N + N) C z = graphFun G ∅ z)
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (S : Finset (Fin (N + N))) (hS : circuitFun (N + N) C (setInput S) = false)
    (hw : wv (N + N) C (setInput S) w = true) :
    q ≤ (junk G C ∩ Finset.range j).card := by
  have hSG : graphFun G ∅ (setInput S) = false := (hgraph _).symm.trans hS
  obtain ⟨T, hTS, hTw, hcard⟩ :=
    MintermCircuit.dirty_wire_small_support_prefix (N + N) C hC G S hSG w hw j
      (Nat.le_of_lt hj) (hC.2.1 j hj w (by rw [hin]; simp))
  have hT : circuitFun (N + N) C (setInput T) = false := by
    cases ht : circuitFun (N + N) C (setInput T) with
    | false => rfl
    | true =>
      have hs : circuitFun (N + N) C (setInput S) = true :=
        wv_mono (N + N) C hC.1 hC.2.1 (setInput T) (setInput S)
          (fun i hi => decide_eq_true (hTS (of_decide_eq_true hi))) C.output ht
      simp [hS] at hs
  have hcount := point_or_sibling_count_general q N I C hC hfun p j w hj hop hin hwp
    hsole (incidence_output_ne_point N I C hfun p) hdegree hunique (setInput T) hT hTw
  have hle := point_support_card_le T
  omega

lemma point_or_sibling_clean_of_few_junk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z, circuitFun (N + N) C z = graphFun G ∅ z)
    (p : Fin N) (j w : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [p.val, w]) (hwp : w ≠ p.val)
    (hsole : ∀ k < C.gates.length, p.val ∈ (gateAt C k).inputs → k = j)
    (hfew : (junk G C).card < q) :
    ∀ z : Fin (N + N) → Bool, wv (N + N) C z w = true → circuitFun (N + N) C z = true := by
  intro z hz
  cases hval : circuitFun (N + N) C z with
  | true => rfl
  | false =>
    let S : Finset (Fin (N + N)) := Finset.univ.filter (fun i => z i = true)
    have hset : setInput S = z := by
      funext i
      cases hi : z i <;> simp [setInput, S, hi]
    have hS : circuitFun (N + N) C (setInput S) = false := by simpa [hset] using hval
    have hw : wv (N + N) C (setInput S) w = true := by simpa [hset] using hz
    have hbound := point_or_dirty_sibling_needs_junk q N I C hC hfun G hgraph p j w
      hj hop hin hwp hsole (Masking.point_degree_of_plane q N I hq hN hcols hunique p)
      hunique S hS hw
    have hle : (junk G C ∩ Finset.range j).card ≤ (junk G C).card :=
      Finset.card_le_card Finset.inter_subset_left
    omega

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

lemma rectangle_branch_clean {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hno4 : ∀ a c : Fin P, ∀ u v : Fin L, a ≠ c → u ≠ v →
      ¬ (I a u ∧ I a v ∧ I c u ∧ I c v))
    (a : Fin P) (A : Finset (Fin P)) (S T : Finset (Fin L))
    (hT : 2 ≤ T.card) (hstar : ∀ y ∈ T, I a y)
    (hcross : ∀ c ∈ A, ∀ x ∈ S, ∀ y ∈ T, I c x ∨ I c y) :
    ∀ c ∈ A.erase a, ∀ x ∈ S, I c x := by
  intro c hc
  obtain ⟨hca, hcA⟩ := Finset.mem_erase.mp hc
  exact singleton_star_product_clean I hno4 a c hca.symm S T hT hstar (hcross c hcA)

lemma rectangle_branch_clean_of_below {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hno4 : ∀ a c : Fin P, ∀ u v : Fin L, a ≠ c → u ≠ v →
      ¬ (I a u ∧ I a v ∧ I c u ∧ I c v))
    (a : Fin P) (A : Finset (Fin P)) (S T : Finset (Fin L))
    (hT : 2 ≤ T.card) (hstar : ∀ y ∈ T, I a y)
    (hbelow : ∀ X : Finset (Fin P), ∀ Y : Finset (Fin L),
      (A ∩ X).Nonempty → (S ∩ Y).Nonempty → (T ∩ Y).Nonempty →
      ∃ p ∈ X, ∃ l ∈ Y, I p l) :
    ∀ c ∈ A.erase a, ∀ x ∈ S, I c x := by
  apply rectangle_branch_clean I hno4 a A S T hT hstar
  intro c hc x hx y hy
  obtain ⟨p, hp, l, hl, hpl⟩ := hbelow {c} {x, y}
    ⟨c, Finset.mem_inter.mpr ⟨hc, Finset.mem_singleton_self c⟩⟩
    ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_insert_self x {y}⟩⟩
    ⟨y, Finset.mem_inter.mpr ⟨hy, Finset.mem_insert_of_mem (Finset.mem_singleton_self y)⟩⟩
  have hpc : p = c := Finset.mem_singleton.mp hp
  subst p
  rcases Finset.mem_insert.mp hl with hl | hl
  · exact Or.inl (hl ▸ hpl)
  · exact Or.inr ((Finset.mem_singleton.mp hl) ▸ hpl)

lemma exists_nonincident_in_star {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hno4 : ∀ a c : Fin P, ∀ u v : Fin L, a ≠ c → u ≠ v →
      ¬ (I a u ∧ I a v ∧ I c u ∧ I c v))
    (a c : Fin P) (hac : a ≠ c) (T : Finset (Fin L))
    (hT : 2 ≤ T.card) (hstar : ∀ y ∈ T, I a y) :
    ∃ t ∈ T, ¬ I c t := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  by_cases hcu : I c u
  · refine ⟨v, hv, ?_⟩
    intro hcv
    exact hno4 a c u v hac huv ⟨hstar u hu, hstar v hv, hcu, hcv⟩
  · exact ⟨u, hu, hcu⟩

lemma star_guard_elimination {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hno4 : ∀ a c : Fin P, ∀ u v : Fin L, a ≠ c → u ≠ v →
      ¬ (I a u ∧ I a v ∧ I c u ∧ I c v))
    (a c : Fin P) (hac : a ≠ c) (T : Finset (Fin L))
    (hT : 2 ≤ T.card) (hstar : ∀ y ∈ T, I a y)
    (H : Finset (Fin L) → Prop) (hmono : Monotone H)
    (hbelow : ∀ Y, H Y → (T ∩ Y).Nonempty → ∃ l ∈ Y, I c l) :
    ∀ Y, H Y → ∃ l ∈ Y, I c l := by
  obtain ⟨t, ht, hct⟩ := exists_nonincident_in_star I hno4 a c hac T hT hstar
  intro Y hY
  obtain ⟨l, hl, hcl⟩ := hbelow (insert t Y)
    (hmono (Finset.subset_insert t Y) hY)
    ⟨t, Finset.mem_inter.mpr ⟨ht, Finset.mem_insert_self t Y⟩⟩
  rcases Finset.mem_insert.mp hl with hlt | hlY
  · exact (hct (hlt ▸ hcl)).elim
  · exact ⟨l, hlY, hcl⟩

end PEqualNP.Outside.L_meta_2583_aux

namespace PEqualNP.Outside.L_meta_2583.GateRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse

def orReplace (C : Circuit) (g a b : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨GateOp.or, [a, b]⟩, C.output⟩

lemma replace_length (C : Circuit) (g a b : ℕ) :
    (orReplace C g a b).gates.length = C.gates.length := by simp [orReplace]

lemma replace_size (C : Circuit) (g a b : ℕ) :
    (orReplace C g a b).size = C.size := by simp [Circuit.size, orReplace]

lemma replace_gateAt (C : Circuit) (g a b k : ℕ) (hg : g < C.gates.length) :
    gateAt (orReplace C g a b) k =
      if k = g then ⟨GateOp.or, [a, b]⟩ else gateAt C k := by
  by_cases hkg : k = g
  · subst k
    simp [gateAt, orReplace, List.getD_eq_getElem?_getD, hg]
  · simp [gateAt, orReplace, List.getD_eq_getElem?_getD, hkg, Ne.symm hkg]

lemma gateAt_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma replace_ao2 (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n) :
    IsAO2 n (orReplace C g a.val b.val) := by
  let D := orReplace C g a.val b.val
  have hlen : D.gates.length = C.gates.length := replace_length C g a.val b.val
  have hrule : ∀ k < D.gates.length,
      ((gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or) ∧
      (∀ i ∈ (gateAt D k).inputs, i < n + k) ∧ (gateAt D k).inputs.length = 2 := by
    intro k hk
    have hkC : k < C.gates.length := by omega
    have hmem : gateAt C k ∈ C.gates := by
      rw [gateAt_getElem C k hkC]
      exact List.getElem_mem hkC
    change ((gateAt (orReplace C g a.val b.val) k).op = GateOp.and ∨ _) ∧ _
    rw [replace_gateAt C g a.val b.val k hg]
    split_ifs with hkg
    · refine ⟨Or.inr rfl, ?_, rfl⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · exact ⟨hAO.1 _ hmem, hAO.2.1 k hkC, hAO.2.2 _ hmem⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [← gateAt_getElem D k hk]
    exact (hrule k hk).1
  · intro k hk
    exact (hrule k hk).2.1
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [← gateAt_getElem D k hk]
    exact (hrule k hk).2.2

lemma replace_wire_le (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n)
    (hle : ∀ x : Fin n → Bool, (x a || x b) = true → gateVal n C g x = true)
    (x : Fin n → Bool) :
    ∀ w : ℕ, wv n (orReplace C g a.val b.val) x w = true → wv n C x w = true := by
  let D := orReplace C g a.val b.val
  have hD : IsAO2 n D := replace_ao2 n C hAO g hg a b
  have hlen : D.gates.length = C.gates.length := replace_length C g a.val b.val
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wv_input n D x w hwn] at hw
      rwa [wv_input n C x w hwn]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n D x w (by omega)] at hw
      cases hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      by_cases hkg : k = g
      · subst k
        have hgate := wv_rec n D x hD.2.1 g hkD
        rw [replace_gateAt C g a.val b.val g hg, ite_eq_left rfl] at hgate
        simp only [List.map_cons, List.map_nil, GateOp.eval] at hgate
        rw [wv_input n D x a.val a.isLt, wv_input n D x b.val b.isLt] at hgate
        apply hle x
        simpa using hgate.symm.trans hw
      · rw [wv_rec n D x hD.2.1 k hkD,
          replace_gateAt C g a.val b.val k hg, ite_eq_right hkg] at hw
        rw [wv_rec n C x hAO.2.1 k hk]
        have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_getElem C k hk]; exact List.getElem_mem hk
        exact gateOp_mono _ (hAO.1 _ hmem) _ _ _
          (fun i hi => ih i (hAO.2.1 k hk i hi)) hw

lemma replace_wire_agree (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n) (x : Fin n → Bool)
    (heq : (x a || x b) = gateVal n C g x) :
    ∀ w : ℕ, wv n (orReplace C g a.val b.val) x w = wv n C x w := by
  let D := orReplace C g a.val b.val
  have hD : IsAO2 n D := replace_ao2 n C hAO g hg a b
  have hlen : D.gates.length = C.gates.length := replace_length C g a.val b.val
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wv_input n D x w hwn, wv_input n C x w hwn]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n D x w (by omega), wv_missing n C x w hwg]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      by_cases hkg : k = g
      · subst k
        rw [wv_rec n D x hD.2.1 g hkD,
          replace_gateAt C g a.val b.val g hg, ite_eq_left rfl]
        simp only [List.map_cons, List.map_nil, GateOp.eval]
        rw [wv_input n D x a.val a.isLt, wv_input n D x b.val b.isLt]
        simpa [wv, gateVal] using heq
      · rw [wv_rec n D x hD.2.1 k hkD,
          replace_gateAt C g a.val b.val k hg, ite_eq_right hkg,
          wv_rec n C x hAO.2.1 k hk]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i (hAO.2.1 k hk i hi)

lemma graph_pair_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  right
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma replace_graph_fun (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n)
    (hle : ∀ x : Fin n → Bool, (x a || x b) = true → gateVal n C g x = true)
    (hpairs : ∀ u v : Fin n, G.Adj u v →
      (pairInput u v a || pairInput u v b) = gateVal n C g (pairInput u v)) :
    circuitFun n (orReplace C g a.val b.val) = graphFun G ∅ := by
  let D := orReplace C g a.val b.val
  have hD : IsAO2 n D := replace_ao2 n C hAO g hg a b
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have h := replace_wire_le n C hAO g hg a b hle x C.output hx
    exact (congrFun hfun x).symm.trans h
  · intro hx
    have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := he
    have hp : circuitFun n D (pairInput u v) = true := by
      have h := replace_wire_agree n C hAO g hg a b (pairInput u v) (hpairs u v huv) C.output
      exact h.trans ((congrFun hfun (pairInput u v)).trans (graph_pair_true n G u v huv))
    exact wv_mono n D hD.1 hD.2.1 (pairInput u v) x
      (fun i hi => by
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact hxu
        · exact hxv) C.output hp

lemma replace_junk_subset (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n)
    (hle : ∀ x : Fin n → Bool, (x a || x b) = true → gateVal n C g x = true) :
    junk G (orReplace C g a.val b.val) ⊆ (junk G C).erase g := by
  intro k hk
  obtain ⟨hk, hop, hreal, x, hx, hFx⟩ := Finset.mem_filter.mp hk
  have hkg : k ≠ g := by
    intro hkg
    subst k
    rw [replace_gateAt C g a.val b.val g hg, ite_eq_left rfl] at hop
    cases hop
  apply Finset.mem_erase.mpr
  refine ⟨hkg, Finset.mem_filter.mpr ?_⟩
  have hkC : k < C.gates.length := by
    have h := Finset.mem_range.mp hk
    rwa [replace_length] at h
  refine ⟨Finset.mem_range.mpr hkC, ?_, hkC, x, ?_, hFx⟩
  · simpa [replace_gateAt C g a.val b.val k hg, hkg] using hop
  · exact replace_wire_le n C hAO g hg a b hle x (n + k) hx

lemma replace_dirty_and (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hg : g ∈ junk G C) (a b : Fin n)
    (hle : ∀ x : Fin n → Bool, (x a || x b) = true → gateVal n C g x = true)
    (hpairs : ∀ u v : Fin n, G.Adj u v →
      (pairInput u v a || pairInput u v b) = gateVal n C g (pairInput u v)) :
    IsAO2 n (orReplace C g a.val b.val) ∧
    (orReplace C g a.val b.val).size = C.size ∧
    circuitFun n (orReplace C g a.val b.val) = graphFun G ∅ ∧
    (junk G (orReplace C g a.val b.val)).card < (junk G C).card := by
  have hreal : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  refine ⟨replace_ao2 n C hAO g hreal a b, replace_size C g a.val b.val,
    replace_graph_fun n C hAO G hfun g hreal a b hle hpairs, ?_⟩
  have hbound := Finset.card_le_card (replace_junk_subset n C hAO G g hreal a b hle)
  have hcard := Finset.card_erase_add_one hg
  omega

end PEqualNP.Outside.L_meta_2583.GateRewrite

namespace PEqualNP.Outside.L_meta_2583.GateRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma replace_same_color_intersection (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B : Finset (Fin n)) (c : Bool)
    (hAc : ∀ r ∈ A, color r = c) (hBc : ∀ r ∈ B, color r = c)
    (a b : Fin n) (hinter : A ∩ B = {a, b})
    (g : ℕ) (hg : g ∈ junk G C)
    (hgate : ∀ x : Fin n → Bool, wv n C x (n + g) = true ↔
      (∃ r ∈ A, x r = true) ∧ (∃ r ∈ B, x r = true)) :
    IsAO2 n (orReplace C g a.val b.val) ∧
    (orReplace C g a.val b.val).size = C.size ∧
    circuitFun n (orReplace C g a.val b.val) = graphFun G ∅ ∧
    (junk G (orReplace C g a.val b.val)).card < (junk G C).card := by
  have haAB : a ∈ A ∧ a ∈ B := by
    apply Finset.mem_inter.mp
    rw [hinter]
    simp
  have hbAB : b ∈ A ∧ b ∈ B := by
    apply Finset.mem_inter.mp
    rw [hinter]
    simp
  have hle : ∀ x : Fin n → Bool, (x a || x b) = true → gateVal n C g x = true := by
    intro x hx
    apply (hgate x).mpr
    simp only [Bool.or_eq_true] at hx
    rcases hx with ha | hb
    · exact ⟨⟨a, haAB.1, ha⟩, ⟨a, haAB.2, ha⟩⟩
    · exact ⟨⟨b, hbAB.1, hb⟩, ⟨b, hbAB.2, hb⟩⟩
  have hpairs : ∀ u v : Fin n, G.Adj u v →
      (pairInput u v a || pairInput u v b) = gateVal n C g (pairInput u v) := by
    intro u v huv
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hle (pairInput u v)
    · intro hval
      obtain ⟨⟨r, hrA, hrx⟩, ⟨t, htB, htx⟩⟩ := (hgate (pairInput u v)).mp hval
      have hr : r = u ∨ r = v := of_decide_eq_true hrx
      have ht : t = u ∨ t = v := of_decide_eq_true htx
      have hrt : r = t := by
        have hc : color r = color t := (hAc r hrA).trans (hBc t htB).symm
        rcases hr with rfl | rfl <;> rcases ht with rfl | rfl
        · rfl
        · exact False.elim (hbip _ _ huv hc)
        · exact False.elim (hbip _ _ huv.symm hc)
        · rfl
      have hrI : r ∈ A ∩ B := Finset.mem_inter.mpr ⟨hrA, hrt.symm ▸ htB⟩
      rw [hinter] at hrI
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrI
      simp only [Bool.or_eq_true]
      rcases hrI with rfl | rfl
      · exact Or.inl hrx
      · exact Or.inr hrx
  exact replace_dirty_and n C hAO G hfun g hg a b hle hpairs

end PEqualNP.Outside.L_meta_2583.GateRewrite

namespace PEqualNP.Outside.L_meta_2583.WireGateRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.GateRewrite

lemma replace_ao2_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g) :
    IsAO2 n (orReplace C g a b) := by
  let D := orReplace C g a b
  have hlen : D.gates.length = C.gates.length := replace_length C g a b
  have hrule : ∀ k < D.gates.length,
      ((gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or) ∧
      (∀ i ∈ (gateAt D k).inputs, i < n + k) ∧ (gateAt D k).inputs.length = 2 := by
    intro k hk
    have hkC : k < C.gates.length := by omega
    have hmem : gateAt C k ∈ C.gates := by
      rw [gateAt_getElem C k hkC]
      exact List.getElem_mem hkC
    change ((gateAt (orReplace C g a b) k).op = GateOp.and ∨ _) ∧ _
    rw [replace_gateAt C g a b k hg]
    split_ifs with hkg
    · refine ⟨Or.inr rfl, ?_, rfl⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · exact ⟨hAO.1 _ hmem, hAO.2.1 k hkC, hAO.2.2 _ hmem⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [← gateAt_getElem D k hk]
    exact (hrule k hk).1
  · intro k hk
    exact (hrule k hk).2.1
  · intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    rw [← gateAt_getElem D k hk]
    exact (hrule k hk).2.2

lemma replace_prefix_agree (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (x : Fin n → Bool) :
    ∀ w < n + g, wv n (orReplace C g a b) x w = wv n C x w := by
  let D := orReplace C g a b
  have hD : IsAO2 n D := replace_ao2_wires n C hAO g hg a b ha hb
  have hlen : D.gates.length = C.gates.length := replace_length C g a b
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wv_input n D x w hwn, wv_input n C x w hwn]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkg : k < g := by omega
      have hk : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      rw [wv_rec n D x hD.2.1 k hkD,
        replace_gateAt C g a b k hg, ite_eq_right (by omega),
        wv_rec n C x hAO.2.1 k hk]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil := hAO.2.1 k hk i hi
      exact ih i hil (by omega)

lemma replace_wire_le_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hle : ∀ x : Fin n → Bool, (wv n C x a || wv n C x b) = true → gateVal n C g x = true)
    (x : Fin n → Bool) :
    ∀ w : ℕ, wv n (orReplace C g a b) x w = true → wv n C x w = true := by
  let D := orReplace C g a b
  have hD : IsAO2 n D := replace_ao2_wires n C hAO g hg a b ha hb
  have hlen : D.gates.length = C.gates.length := replace_length C g a b
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wv_input n D x w hwn] at hw
      rwa [wv_input n C x w hwn]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n D x w (by omega)] at hw
      cases hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      by_cases hkg : k = g
      · subst k
        have hgate := wv_rec n D x hD.2.1 g hkD
        rw [replace_gateAt C g a b g hg, ite_eq_left rfl] at hgate
        simp only [List.map_cons, List.map_nil, GateOp.eval] at hgate
        rw [replace_prefix_agree n C hAO g hg a b ha hb x a ha,
          replace_prefix_agree n C hAO g hg a b ha hb x b hb] at hgate
        apply hle x
        simpa using hgate.symm.trans hw
      · rw [wv_rec n D x hD.2.1 k hkD,
          replace_gateAt C g a b k hg, ite_eq_right hkg] at hw
        rw [wv_rec n C x hAO.2.1 k hk]
        have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_getElem C k hk]; exact List.getElem_mem hk
        exact gateOp_mono _ (hAO.1 _ hmem) _ _ _
          (fun i hi => ih i (hAO.2.1 k hk i hi)) hw

lemma replace_wire_agree_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (x : Fin n → Bool) (heq : (wv n C x a || wv n C x b) = gateVal n C g x) :
    ∀ w : ℕ, wv n (orReplace C g a b) x w = wv n C x w := by
  let D := orReplace C g a b
  have hD : IsAO2 n D := replace_ao2_wires n C hAO g hg a b ha hb
  have hlen : D.gates.length = C.gates.length := replace_length C g a b
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [wv_input n D x w hwn, wv_input n C x w hwn]
    by_cases hwg : n + C.gates.length ≤ w
    · rw [wv_missing n D x w (by omega), wv_missing n C x w hwg]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkD : k < D.gates.length := by omega
      by_cases hkg : k = g
      · subst k
        rw [wv_rec n D x hD.2.1 g hkD,
          replace_gateAt C g a b g hg, ite_eq_left rfl]
        simp only [List.map_cons, List.map_nil, GateOp.eval]
        rw [replace_prefix_agree n C hAO g hg a b ha hb x a ha,
          replace_prefix_agree n C hAO g hg a b ha hb x b hb]
        simpa [wv, gateVal] using heq
      · rw [wv_rec n D x hD.2.1 k hkD,
          replace_gateAt C g a b k hg, ite_eq_right hkg,
          wv_rec n C x hAO.2.1 k hk]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i (hAO.2.1 k hk i hi)

lemma replace_graph_fun_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hle : ∀ x : Fin n → Bool, (wv n C x a || wv n C x b) = true → gateVal n C g x = true)
    (hpairs : ∀ u v : Fin n, G.Adj u v →
      (wv n C (pairInput u v) a || wv n C (pairInput u v) b) = gateVal n C g (pairInput u v)) :
    circuitFun n (orReplace C g a b) = graphFun G ∅ := by
  let D := orReplace C g a b
  have hD : IsAO2 n D := replace_ao2_wires n C hAO g hg a b ha hb
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have h := replace_wire_le_wires n C hAO g hg a b ha hb hle x C.output hx
    exact (congrFun hfun x).symm.trans h
  · intro hx
    have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := he
    have hp : circuitFun n D (pairInput u v) = true := by
      have h := replace_wire_agree_wires n C hAO g hg a b ha hb (pairInput u v)
        (hpairs u v huv) C.output
      exact h.trans ((congrFun hfun (pairInput u v)).trans (graph_pair_true n G u v huv))
    exact wv_mono n D hD.1 hD.2.1 (pairInput u v) x
      (fun i hi => by
        simp only [pairInput, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact hxu
        · exact hxv) C.output hp

lemma replace_junk_subset_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : ℕ) (hg : g < C.gates.length) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hle : ∀ x : Fin n → Bool, (wv n C x a || wv n C x b) = true → gateVal n C g x = true) :
    junk G (orReplace C g a b) ⊆ (junk G C).erase g := by
  intro k hk
  obtain ⟨hk, hop, hreal, x, hx, hFx⟩ := Finset.mem_filter.mp hk
  have hkg : k ≠ g := by
    intro hkg
    subst k
    rw [replace_gateAt C g a b g hg, ite_eq_left rfl] at hop
    cases hop
  apply Finset.mem_erase.mpr
  refine ⟨hkg, Finset.mem_filter.mpr ?_⟩
  have hkC : k < C.gates.length := by
    have h := Finset.mem_range.mp hk
    rwa [replace_length] at h
  refine ⟨Finset.mem_range.mpr hkC, ?_, hkC, x, ?_, hFx⟩
  · simpa [replace_gateAt C g a b k hg, hkg] using hop
  · exact replace_wire_le_wires n C hAO g hg a b ha hb hle x (n + k) hx

lemma replace_dirty_and_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hg : g ∈ junk G C) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hle : ∀ x : Fin n → Bool, (wv n C x a || wv n C x b) = true → gateVal n C g x = true)
    (hpairs : ∀ u v : Fin n, G.Adj u v →
      (wv n C (pairInput u v) a || wv n C (pairInput u v) b) = gateVal n C g (pairInput u v)) :
    IsAO2 n (orReplace C g a b) ∧ (orReplace C g a b).size = C.size ∧
    circuitFun n (orReplace C g a b) = graphFun G ∅ ∧
    (junk G (orReplace C g a b)).card < (junk G C).card := by
  have hreal : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  refine ⟨replace_ao2_wires n C hAO g hreal a b ha hb, replace_size C g a b,
    replace_graph_fun_wires n C hAO G hfun g hreal a b ha hb hle hpairs, ?_⟩
  have hbound := Finset.card_le_card (replace_junk_subset_wires n C hAO G g hreal a b ha hb hle)
  have hcard := Finset.card_erase_add_one hg
  omega

end PEqualNP.Outside.L_meta_2583.WireGateRewrite

namespace PEqualNP.Outside.L_meta_2583.WireGateRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.GateRewrite

lemma replace_intersection_covered_by_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B S T : Finset (Fin n)) (c : Bool)
    (hAc : ∀ r ∈ A, color r = c) (hBc : ∀ r ∈ B, color r = c)
    (hcover : S ∪ T = A ∩ B)
    (g : ℕ) (hg : g ∈ junk G C) (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hwa : ∀ x : Fin n → Bool, wv n C x a = true ↔ ∃ r ∈ S, x r = true)
    (hwb : ∀ x : Fin n → Bool, wv n C x b = true ↔ ∃ r ∈ T, x r = true)
    (hgate : ∀ x : Fin n → Bool, wv n C x (n + g) = true ↔
      (∃ r ∈ A, x r = true) ∧ (∃ r ∈ B, x r = true)) :
    IsAO2 n (orReplace C g a b) ∧ (orReplace C g a b).size = C.size ∧
    circuitFun n (orReplace C g a b) = graphFun G ∅ ∧
    (junk G (orReplace C g a b)).card < (junk G C).card := by
  have hunion : ∀ x : Fin n → Bool,
      (wv n C x a || wv n C x b) = true ↔ ∃ r ∈ A ∩ B, x r = true := by
    intro x
    simp only [Bool.or_eq_true]
    constructor
    · intro hx
      rcases hx with hax | hbx
      · obtain ⟨r, hr, hrx⟩ := (hwa x).mp hax
        refine ⟨r, ?_, hrx⟩
        rw [← hcover]
        exact Finset.mem_union_left _ hr
      · obtain ⟨r, hr, hrx⟩ := (hwb x).mp hbx
        refine ⟨r, ?_, hrx⟩
        rw [← hcover]
        exact Finset.mem_union_right _ hr
    · rintro ⟨r, hr, hrx⟩
      rw [← hcover] at hr
      rcases Finset.mem_union.mp hr with hrS | hrT
      · exact Or.inl ((hwa x).mpr ⟨r, hrS, hrx⟩)
      · exact Or.inr ((hwb x).mpr ⟨r, hrT, hrx⟩)
  have hle : ∀ x : Fin n → Bool,
      (wv n C x a || wv n C x b) = true → gateVal n C g x = true := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (hunion x).mp hx
    obtain ⟨hrA, hrB⟩ := Finset.mem_inter.mp hr
    exact (hgate x).mpr ⟨⟨r, hrA, hrx⟩, ⟨r, hrB, hrx⟩⟩
  have hpairs : ∀ u v : Fin n, G.Adj u v →
      (wv n C (pairInput u v) a || wv n C (pairInput u v) b) = gateVal n C g (pairInput u v) := by
    intro u v huv
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hle (pairInput u v)
    · intro hval
      obtain ⟨⟨r, hrA, hrx⟩, ⟨t, htB, htx⟩⟩ := (hgate (pairInput u v)).mp hval
      have hr : r = u ∨ r = v := of_decide_eq_true hrx
      have ht : t = u ∨ t = v := of_decide_eq_true htx
      have hrt : r = t := by
        have hc : color r = color t := (hAc r hrA).trans (hBc t htB).symm
        rcases hr with rfl | rfl <;> rcases ht with rfl | rfl
        · rfl
        · exact False.elim (hbip _ _ huv hc)
        · exact False.elim (hbip _ _ huv.symm hc)
        · rfl
      apply (hunion (pairInput u v)).mpr
      exact ⟨r, Finset.mem_inter.mpr ⟨hrA, hrt.symm ▸ htB⟩, hrx⟩
  exact replace_dirty_and_wires n C hAO G hfun g hg a b ha hb hle hpairs

end PEqualNP.Outside.L_meta_2583.WireGateRewrite

namespace PEqualNP.Outside.L_meta_2583.ShadowGateRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.GateRewrite
  PEqualNP.Outside.L_meta_2583.WireGateRewrite

lemma one_color_pair_acceptance (n : ℕ) (f : (Fin n → Bool) → Bool)
    (color : Fin n → Bool) (c : Bool)
    (hdep : ∀ x, f x = f (fun r => if color r = c then x r else false))
    (hzero : f (fun _ => false) = false)
    (u v : Fin n) (hcol : color u ≠ color v) (hf : f (pairInput u v) = true) :
    f (pairInput u u) = true ∨ f (pairInput v v) = true := by
  have hp := (hdep (pairInput u v)).symm.trans hf
  by_cases hu : color u = c
  · have hv : color v ≠ c := fun hv => hcol (hu.trans hv.symm)
    have heq : (fun r => if color r = c then pairInput u v r else false) = pairInput u u := by
      funext r
      by_cases hru : r = u
      · subst r; simp [pairInput, hu]
      by_cases hrv : r = v
      · subst r; simp [pairInput, hv, hru]
      · simp [pairInput, hru, hrv]
    exact Or.inl (heq ▸ hp)
  · by_cases hv : color v = c
    · have heq : (fun r => if color r = c then pairInput u v r else false) = pairInput v v := by
        funext r
        by_cases hrv : r = v
        · subst r; simp [pairInput, hv]
        by_cases hru : r = u
        · subst r; simp [pairInput, hu, hrv]
        · simp [pairInput, hru, hrv]
      exact Or.inr (heq ▸ hp)
    · have heq : (fun r => if color r = c then pairInput u v r else false) = fun _ => false := by
        funext r
        by_cases hru : r = u
        · subst r; simp [hu]
        by_cases hrv : r = v
        · subst r; simp [hv]
        · simp [pairInput, hru, hrv]
      rw [heq, hzero] at hp
      cases hp

lemma replace_one_color_shadow_wires (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : Bool) (R : Finset (Fin n)) (g : ℕ) (hg : g ∈ junk G C)
    (hdep : ∀ x : Fin n → Bool, wv n C x (n + g) =
      wv n C (fun r => if color r = c then x r else false) (n + g))
    (hzero : wv n C (fun _ => false) (n + g) = false)
    (hshadow : ∀ r : Fin n, wv n C (pairInput r r) (n + g) = true ↔ r ∈ R)
    (a b : ℕ) (ha : a < n + g) (hb : b < n + g)
    (hnew : ∀ x : Fin n → Bool,
      (wv n C x a || wv n C x b) = true ↔ ∃ r ∈ R, x r = true) :
    IsAO2 n (orReplace C g a b) ∧ (orReplace C g a b).size = C.size ∧
    circuitFun n (orReplace C g a b) = graphFun G ∅ ∧
    (junk G (orReplace C g a b)).card < (junk G C).card := by
  have hle : ∀ x : Fin n → Bool,
      (wv n C x a || wv n C x b) = true → gateVal n C g x = true := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (hnew x).mp hx
    have hs := (hshadow r).mpr hr
    exact wv_mono n C hAO.1 hAO.2.1 (pairInput r r) x
      (fun i hi => by
        have hir : i = r := by simpa [pairInput] using hi
        simpa [hir] using hrx) (n + g) hs
  have hpairs : ∀ u v : Fin n, G.Adj u v →
      (wv n C (pairInput u v) a || wv n C (pairInput u v) b) = gateVal n C g (pairInput u v) := by
    intro u v huv
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hle (pairInput u v)
    · intro hval
      have hs := one_color_pair_acceptance n (fun x => wv n C x (n + g))
        color c hdep hzero u v (hbip u v huv) hval
      apply (hnew (pairInput u v)).mpr
      rcases hs with hu | hv
      · exact ⟨u, (hshadow u).mp hu, by simp [pairInput]⟩
      · exact ⟨v, (hshadow v).mp hv, by simp [pairInput]⟩
  exact replace_dirty_and_wires n C hAO G hfun g hg a b ha hb hle hpairs

lemma replace_two_point_color_shadow (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : Bool) (g : ℕ) (hg : g ∈ junk G C) (a b : Fin n)
    (hdep : ∀ x : Fin n → Bool, wv n C x (n + g) =
      wv n C (fun r => if color r = c then x r else false) (n + g))
    (hzero : wv n C (fun _ => false) (n + g) = false)
    (hshadow : ∀ r : Fin n, wv n C (pairInput r r) (n + g) = true ↔ r = a ∨ r = b) :
    IsAO2 n (orReplace C g a.val b.val) ∧ (orReplace C g a.val b.val).size = C.size ∧
    circuitFun n (orReplace C g a.val b.val) = graphFun G ∅ ∧
    (junk G (orReplace C g a.val b.val)).card < (junk G C).card := by
  apply replace_one_color_shadow_wires n C hAO G hfun color hbip c {a, b} g hg hdep hzero
    (fun r => by simpa using hshadow r) a.val b.val (by omega) (by omega)
  intro x
  rw [wv_input n C x a.val a.isLt, wv_input n C x b.val b.isLt]
  simp only [Bool.or_eq_true, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (ha | hb)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr rfl, hb⟩
  · rintro ⟨r, hr, hrx⟩
    rcases hr with rfl | rfl
    · exact Or.inl hrx
    · exact Or.inr hrx

end PEqualNP.Outside.L_meta_2583.ShadowGateRewrite

namespace PEqualNP.Outside.L_meta_2583.MinJunkNormal

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.GateRewrite
  PEqualNP.Outside.L_meta_2583.ShadowGateRewrite

lemma exists_budget_min_junk (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ E : Circuit, IsAO2 n E → E.size ≤ C.size → circuitFun n E = graphFun G ∅ →
        (junk G D).card ≤ (junk G E).card := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
    circuitFun n D = graphFun G ∅ ∧ (junk G D).card = k
  have hex : ∃ k, P k := ⟨(junk G C).card, C, hAO, le_rfl, hfun, rfl⟩
  obtain ⟨D, hD, hsize, hDf, hcard⟩ := Nat.find_spec hex
  refine ⟨D, hD, hsize, hDf, ?_⟩
  intro E hE hEsize hEf
  rw [hcard]
  exact Nat.find_le ⟨E, hE, hEsize, hEf, rfl⟩

lemma exists_color_shadow_normal_form (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, IsAO2 n E → E.size ≤ C.size → circuitFun n E = graphFun G ∅ →
        (junk G D).card ≤ (junk G E).card) ∧
      (∀ (c : Bool) (R : Finset (Fin n)), R.Nonempty → ∀ g ∈ junk G D,
        (∀ x : Fin n → Bool, wv n D x (n + g) =
          wv n D (fun r => if color r = c then x r else false) (n + g)) →
        wv n D (fun _ => false) (n + g) = false →
        (∀ r : Fin n, wv n D (pairInput r r) (n + g) = true ↔ r ∈ R) →
        ∀ a b : ℕ, a < n + g → b < n + g →
          (∀ x : Fin n → Bool, (wv n D x a || wv n D x b) = true ↔ ∃ r ∈ R, x r = true) →
          False) := by
  obtain ⟨D, hD, hsize, hDf, hmin⟩ := exists_budget_min_junk n C hAO G hfun
  refine ⟨D, hD, hsize, hDf, hmin, ?_⟩
  intro c R _ g hg hdep hzero hshadow a b ha hb hnew
  obtain ⟨hE, hEsize, hEf, hless⟩ := replace_one_color_shadow_wires n D hD G hDf color hbip
    c R g hg hdep hzero hshadow a b ha hb hnew
  have hbound := hmin (orReplace D g a b) hE (hEsize.trans_le hsize) hEf
  omega

lemma budget_min_junk_no_two_point_shadow (n : ℕ) (C D : Circuit)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : IsAO2 n D) (hsize : D.size ≤ C.size) (hDf : circuitFun n D = graphFun G ∅)
    (hmin : ∀ E : Circuit, IsAO2 n E → E.size ≤ C.size → circuitFun n E = graphFun G ∅ →
      (junk G D).card ≤ (junk G E).card)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : Bool) (g : ℕ) (hg : g ∈ junk G D) (a b : Fin n)
    (hdep : ∀ x : Fin n → Bool, wv n D x (n + g) =
      wv n D (fun r => if color r = c then x r else false) (n + g))
    (hzero : wv n D (fun _ => false) (n + g) = false)
    (hshadow : ∀ r : Fin n, wv n D (pairInput r r) (n + g) = true ↔ r = a ∨ r = b) : False := by
  obtain ⟨hE, hEsize, hEf, hless⟩ := replace_two_point_color_shadow n D hD G hDf color hbip
    c g hg a b hdep hzero hshadow
  have hbound := hmin (orReplace D g a.val b.val) hE (hEsize.trans_le hsize) hEf
  omega

end PEqualNP.Outside.L_meta_2583.MinJunkNormal

namespace PEqualNP.Outside.L_meta_2583.MultiRootSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma pickedSupport_family_prefix (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (r : ℕ) (hr : r ≤ m) (W : Finset ℕ) (hW : ∀ w ∈ W, w < n + r) :
    (W.biUnion (pickedSupport n m a b both left ha hb)).card ≤
      ((Finset.range r).filter fun k => both k = true).card + W.card := by
  let s := pickedSupport n m a b both left ha hb
  let parents : ℕ → Finset ℕ := fun k =>
    if both k then {a k, b k} else if left k then {a k} else {b k}
  let cost : ℕ → ℕ := fun k => if both k then 1 else 0
  have hinput : ∀ i < n, (s i).card ≤ 1 := by
    intro i hi
    simp [s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < r, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
      · exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
  have hc : ∀ k < r, (parents k).card ≤ cost k + 1 := by
    intro k _
    simp only [parents, cost]
    split_ifs <;> first | exact Finset.card_le_two | simp
  have hv : ∀ k < r, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    dsimp only [s, parents]
    rw [pickedSupport_gate n m a b both left ha hb k (lt_of_lt_of_le hk hr)]
    split_ifs <;> simp
  have hmain := support_family_bound n r s parents cost hinput hp hc hv W
    (fun w hw => Finset.mem_range.mpr (hW w hw))
  have hsum : (Finset.range r).sum cost =
      ((Finset.range r).filter fun k => both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  simpa [s, hsum] using hmain

lemma dirty_roots_small_support_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : graphFun G ∅ (setInput S) = false)
    (r : ℕ) (hr : r ≤ C.gates.length) (W : Finset ℕ)
    (hvalid : ∀ w ∈ W, w < n + r)
    (htrue : ∀ w ∈ W, wv n C (setInput S) w = true) :
    ∃ T : Finset (Fin n), T ⊆ S ∧
      (∀ w ∈ W, wv n C (setInput T) w = true) ∧
      T.card ≤ (junk G C ∩ Finset.range r).card + W.card := by
  classical
  let T := W.biUnion (circuitSupport n C hAO (setInput S))
  have hsub : T ⊆ S := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    exact (support_sound n C hAO S w (htrue w hw)).1 hiw
  refine ⟨T, hsub, ?_, ?_⟩
  · intro w hw
    have hs := support_sound n C hAO S w (htrue w hw)
    exact wv_mono n C hAO.1 hAO.2.1
      (setInput (circuitSupport n C hAO (setInput S) w)) (setInput T)
      (fun i hi => by
        simp only [setInput, decide_eq_true_eq] at hi ⊢
        exact Finset.mem_biUnion.mpr ⟨w, hw, hi⟩) w hs.2
  · have hbound := pickedSupport_family_prefix n C.gates.length
      (fun k => opnd C k 0) (fun k => opnd C k 1) (pickedBoth n C (setInput S))
      (fun k => wv n C (setInput S) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) r hr W hvalid
    change T.card ≤ _ at hbound
    refine hbound.trans (Nat.add_le_add_right (Finset.card_le_card ?_) W.card)
    intro k hk
    obtain ⟨hkr, hboth⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_inter.mpr
    refine ⟨true_ands_subset_junk n C G (setInput S) hS ?_, hkr⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hkr) hr), hboth⟩

end PEqualNP.Outside.L_meta_2583.MultiRootSupport

namespace PEqualNP.Outside.L_meta_2583.MultiOrMask

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.SingleUse
open PEqualNP.Outside.L_meta_2583.PlaneSingleUse

lemma all_or_read_mask (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (hw : ∀ w ∈ W, wv n C x w = true) :
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
      by_cases hkp : p.val ∈ (gateAt C k).inputs
      · obtain ⟨w, hwW, hwp, hop, hin⟩ := hread k hk hkp
        have hwm : w ∈ (gateAt C k).inputs := by rcases hin with hin | hin <;> simp [hin]
        have hwl : w < v := by have := hC k hk w hwm; omega
        have hwe := ih w hwl hwp
        have hwt := hw w hwW
        rcases hin with hin | hin <;> simp [hin, hop, GateOp.eval, ← hwe, hwt]
      · congr 1
        apply List.map_congr_left
        intro u hu
        have hup : u ≠ p.val := by intro he; exact hkp (he ▸ hu)
        exact ih u (by have := hC k hk u hu; omega) hup
    · rw [wv_missing n C x v (by omega), wv_missing n C y v (by omega)]

lemma all_or_output_mask (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (p : Fin n) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ p → x i = y i)
    (hw : ∀ w ∈ W, wv n C x w = true) (hout : C.output ≠ p.val) :
    circuitFun n C x = circuitFun n C y :=
  all_or_read_mask n C hC p W hread x y hxy hw C.output hout

lemma point_or_siblings_count
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (z : Fin (N + N) → Bool) (hzp : z (Fin.castAdd N p) = false)
    (hfalse : circuitFun (N + N) C z = false)
    (hw : ∀ w ∈ W, wv (N + N) C z w = true) :
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
    have hw' : ∀ w ∈ W, wv (N + N) C z' w = true := by
      intro w hwW
      exact wv_mono (N + N) C hC.1 hC.2.1 z z' hmono w (hw w hwW)
    have hxy : ∀ i : Fin (N + N), i ≠ Fin.castAdd N p → z' i = z'' i := by
      intro i hi
      simp [z'', Function.update_of_ne hi]
    have hmask : circuitFun (N + N) C z' = circuitFun (N + N) C z'' :=
      all_or_output_mask (N + N) C hC.2.1 (Fin.castAdd N p) W hread z' z'' hxy hw'
        (incidence_output_ne_point N I C hfun p)
    have ht : circuitFun (N + N) C z'' = true := by
      rw [hfun]
      apply decide_eq_true
      refine ⟨p, l, hl, ?_, ?_⟩
      · simp [z'']
      · simp only [z'', Function.update_of_ne (Ne.symm (point_ne_line p l)), z', Function.update_self]
    have hresult := hmask.trans ht
    rw [hfun] at hresult
    obtain ⟨r, k, hrk, hr, hk⟩ := of_decide_eq_true hresult
    exact ⟨r, k, hrk, (line_update_point z l r) ▸ hr, (line_update_line z l k) ▸ hk⟩

lemma point_or_siblings_count_general
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (p : Fin N) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (z : Fin (N + N) → Bool) (hfalse : circuitFun (N + N) C z = false)
    (hw : ∀ w ∈ W, wv (N + N) C z w = true) :
    q + 1 ≤ (Finset.univ.filter (fun r => z (Fin.castAdd N r) = true)).card := by
  let x : Fin (N + N) → Bool := Function.update z (Fin.castAdd N p) false
  have hx : x (Fin.castAdd N p) = false := by simp [x]
  have hzx : ∀ i : Fin (N + N), i ≠ Fin.castAdd N p → z i = x i := by
    intro i hi
    exact (Function.update_of_ne hi false z).symm
  have hmask := all_or_read_mask (N + N) C hC.2.1 (Fin.castAdd N p) W hread z x hzx hw
  have hwx : ∀ w ∈ W.erase p.val, wv (N + N) C x w = true := by
    intro w hwW
    rw [← hmask w (Finset.mem_erase.mp hwW).1]
    exact hw w (Finset.mem_erase.mp hwW).2
  have hread' : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W.erase p.val, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]) := by
    intro j hj hp
    obtain ⟨w, hwW, hwp, hop, hin⟩ := hread j hj hp
    exact ⟨w, Finset.mem_erase.mpr ⟨hwp, hwW⟩, hwp, hop, hin⟩
  have hfalsex : circuitFun (N + N) C x = false := by
    change wv (N + N) C x C.output = false
    rw [← hmask C.output (incidence_output_ne_point N I C hfun p)]
    exact hfalse
  have hcount := point_or_siblings_count q N I C hC hfun p (W.erase p.val) hread'
    hdegree hunique x hx hfalsex hwx
  apply hcount.trans
  apply Finset.card_le_card
  intro r hr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
  have ht := (Finset.mem_filter.mp hr).2
  by_cases heq : Fin.castAdd N r = Fin.castAdd N p
  · simp [x, heq] at ht
  · exact (Function.update_of_ne heq false z) ▸ ht

end PEqualNP.Outside.L_meta_2583.MultiOrMask

namespace PEqualNP.Outside.L_meta_2583.MultiOrMask

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.PlaneSingleUse
  PEqualNP.Outside.L_meta_2583.MultiRootSupport

lemma point_or_siblings_need_junk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z, circuitFun (N + N) C z = graphFun G ∅ z)
    (p : Fin N) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (S : Finset (Fin (N + N))) (hS : circuitFun (N + N) C (setInput S) = false)
    (hw : ∀ w ∈ W, wv (N + N) C (setInput S) w = true)
    (r : ℕ) (hr : r ≤ C.gates.length) (hvalid : ∀ w ∈ W, w < N + N + r) :
    q + 1 ≤ (junk G C ∩ Finset.range r).card + W.card := by
  have hSG : graphFun G ∅ (setInput S) = false := (hgraph _).symm.trans hS
  obtain ⟨T, hTS, hTw, hcard⟩ :=
    dirty_roots_small_support_prefix (N + N) C hC G S hSG r hr W hvalid hw
  have hT : circuitFun (N + N) C (setInput T) = false := by
    cases ht : circuitFun (N + N) C (setInput T) with
    | false => rfl
    | true =>
      have hs : circuitFun (N + N) C (setInput S) = true :=
        wv_mono (N + N) C hC.1 hC.2.1 (setInput T) (setInput S)
          (fun i hi => decide_eq_true (hTS (of_decide_eq_true hi))) C.output ht
      simp [hS] at hs
  have hcount := point_or_siblings_count_general q N I C hC hfun p W hread
    hdegree hunique (setInput T) hT hTw
  exact hcount.trans ((point_support_card_le T).trans hcard)

end PEqualNP.Outside.L_meta_2583.MultiOrMask


namespace PEqualNP.Outside.L_meta_2583.TopNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end PEqualNP.Outside.L_meta_2583.TopNormal

namespace PEqualNP.Outside.L_meta_2583

theorem TopNormal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧ PEqualNP.TopForm.TopForm G C' := by
  intro n G _ C hG hC
  exact PEqualNP.Outside.L_meta_2583.TopNormal.main_ind n G hG _ C hC rfl

end PEqualNP.Outside.L_meta_2583


namespace PEqualNP.Outside.L_meta_2583.TopFormBridge

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.GateRewrite
  PEqualNP.Outside.L_meta_2583.ShadowGateRewrite PEqualNP.Outside.L_meta_2583.MinJunkNormal

lemma exists_least_topform_shadow_normal (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty)
    (hfun : circuitFun n C = graphFun G ∅)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v) :
    ∃ T : Circuit, IsLeastAO G T ∧ T.size ≤ C.size ∧ TopForm G T ∧
      (∀ E : Circuit, IsAO2 n E → E.size ≤ T.size → circuitFun n E = graphFun G ∅ →
        (junk G T).card ≤ (junk G E).card) ∧
      (∀ (c : Bool) (R : Finset (Fin n)), R.Nonempty → ∀ g ∈ junk G T,
        (∀ x : Fin n → Bool, wv n T x (n + g) =
          wv n T (fun r => if color r = c then x r else false) (n + g)) →
        wv n T (fun _ => false) (n + g) = false →
        (∀ r : Fin n, wv n T (pairInput r r) (n + g) = true ↔ r ∈ R) →
        ∀ a b : ℕ, a < n + g → b < n + g →
          (∀ x : Fin n → Bool, (wv n T x a || wv n T x b) = true ↔ ∃ r ∈ R, x r = true) →
          False) := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ D.size = k ∧ circuitFun n D = graphFun G ∅
  have hex : ∃ k, P k := ⟨C.size, C, hAO, rfl, hfun⟩
  obtain ⟨C₀, h₀, h₀size, h₀fun⟩ := Nat.find_spec hex
  have h₀min : ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → C₀.size ≤ E.size := by
    intro E hE hEf
    rw [h₀size]
    exact Nat.find_le ⟨E, hE, rfl, hEf⟩
  have h₀budget : C₀.size ≤ C.size := h₀min C hAO hfun
  obtain ⟨D, hD, hDsize, hDf, hDmin⟩ := exists_budget_min_junk n C₀ h₀ G h₀fun
  have hDleast : IsLeastAO G D := ⟨hD, hDf,
    fun E hE hEf => hDsize.trans (h₀min E hE hEf)⟩
  obtain ⟨T, hTleast, hTsize, hTjunk, hTtop⟩ := PEqualNP.Outside.L_meta_2583.TopNormal n G D hG hDleast
  have hTbudget : T.size ≤ C.size := hTsize.trans_le (hDsize.trans h₀budget)
  have hTmin : ∀ E : Circuit, IsAO2 n E → E.size ≤ T.size → circuitFun n E = graphFun G ∅ →
      (junk G T).card ≤ (junk G E).card := by
    intro E hE hEsize hEf
    rw [hTjunk]
    exact hDmin E hE (hEsize.trans (hTsize.trans_le hDsize)) hEf
  refine ⟨T, hTleast, hTbudget, hTtop, hTmin, ?_⟩
  intro c R _ g hg hdep hzero hshadow a b ha hb hnew
  obtain ⟨hE, hEsize, hEf, hless⟩ := replace_one_color_shadow_wires n T hTleast.1 G hTleast.2.1
    color hbip c R g hg hdep hzero hshadow a b ha hb hnew
  have hbound := hTmin (orReplace T g a b) hE hEsize.le hEf
  omega

end PEqualNP.Outside.L_meta_2583.TopFormBridge

namespace PEqualNP.Outside.L_meta_2583.WmaxJunk

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_2583.SingleUse

lemma graph_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by simp [graphFun]

lemma false_support_safe_neighbor_count
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : ℕ)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, gateVal n C g x = true → x v = true → graphFun G ∅ x = true)
    (p : Fin n) (hp : p ∈ W) (X : Finset (Fin n))
    (hX : ∀ v ∈ X, v ∈ W ∧ G.Adj p v)
    (T : Finset (Fin n)) (hT : graphFun G ∅ (setInput T) = false)
    (hgate : gateVal n C g (setInput T) = true) : X.card + 1 ≤ T.card := by
  classical
  have hind : ∀ a ∈ T, ∀ b ∈ T, ¬G.Adj a b := by
    intro a ha b hb hab
    have ht : graphFun G ∅ (setInput T) = true := by
      rw [graph_true_iff]
      exact ⟨a, b, hab, decide_eq_true ha, decide_eq_true hb⟩
    simp [hT] at ht
  have hpT : p ∉ T := by
    intro hpT
    have ht := hsafe p hp (setInput T) hgate (decide_eq_true hpT)
    simp [hT] at ht
  have hcover : ∀ v ∈ W, ∃ t ∈ T, G.Adj v t := by
    intro v hv
    have hmono : ∀ i, setInput T i = true → setInput (insert v T) i = true := by
      intro i hi
      exact decide_eq_true (Finset.mem_insert_of_mem (of_decide_eq_true hi))
    have hg : gateVal n C g (setInput (insert v T)) = true :=
      wv_mono n C hAO.1 hAO.2.1 (setInput T) (setInput (insert v T)) hmono (n + g) hgate
    have ht := hsafe v hv (setInput (insert v T)) hg (by simp [setInput])
    rw [graph_true_iff] at ht
    obtain ⟨a, b, hab, ha, hb⟩ := ht
    have ha' : a ∈ insert v T := of_decide_eq_true ha
    have hb' : b ∈ insert v T := of_decide_eq_true hb
    rcases Finset.mem_insert.mp ha' with rfl | haT
    · rcases Finset.mem_insert.mp hb' with rfl | hbT
      · exact False.elim (G.irrefl hab)
      · exact ⟨b, hbT, hab⟩
    · rcases Finset.mem_insert.mp hb' with rfl | hbT
      · exact ⟨a, haT, hab.symm⟩
      · exact False.elim (hind a haT b hbT hab)
  obtain ⟨t₀, ht₀, hpt₀⟩ := hcover p hp
  have hchoose : ∀ v ∈ X, ∃ t ∈ T, G.Adj v t := fun v hv => hcover v (hX v hv).1
  let f : Fin n → Fin n := fun v => if hv : v ∈ X then (hchoose v hv).choose else p
  have hf : ∀ v ∈ X, f v ∈ T ∧ G.Adj v (f v) := by
    intro v hv
    simpa only [f, dite_eq_left hv] using (hchoose v hv).choose_spec
  have hbound : X.card ≤ (T.erase t₀).card := by
    apply Finset.card_le_card_of_injOn f
    · intro v hv
      refine Finset.mem_erase.mpr ⟨?_, (hf v hv).1⟩
      intro heq
      have h₁ := hbip p v (hX v hv).2
      have h₂ := hbip v t₀ (heq ▸ (hf v hv).2)
      have h₃ := hbip p t₀ hpt₀
      cases hc₁ : color p <;> cases hc₂ : color v <;> cases hc₃ : color t₀ <;>
        simp_all
    · intro v hv u hu heq
      have hpf : p ≠ f v := by
        intro h
        exact hpT (h ▸ (hf v hv).1)
      apply Finset.card_le_one.mp (h4 p (f v) hpf)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (hX v hv).2, (hf v hv).2.symm⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, (hX u hu).2,
          by rw [heq]; exact (hf u hu).2.symm⟩
  have herase : (T.erase t₀).card + 1 = T.card := Finset.card_erase_add_one ht₀
  omega

lemma dirty_safe_neighbors_need_junk_prefix
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : ℕ)
    (hdirty : IsDirty n G C g)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, gateVal n C g x = true → x v = true → graphFun G ∅ x = true)
    (p : Fin n) (hp : p ∈ W) (X : Finset (Fin n))
    (hX : ∀ v ∈ X, v ∈ W ∧ G.Adj p v) :
    X.card ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  classical
  obtain ⟨hg, x, hgx, hx⟩ := hdirty
  let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
  have hSx : setInput S = x := by
    funext i
    cases hi : x i <;> simp [setInput, S, hi]
  have hS : graphFun G ∅ (setInput S) = false := by rw [hSx]; exact hx
  have hSg : wv n C (setInput S) (n + g) = true := by rw [hSx]; exact hgx
  obtain ⟨T, hTS, hTg, hcard⟩ :=
    MintermCircuit.dirty_wire_small_support_prefix n C hAO G S hS (n + g) hSg
      (g + 1) (by omega) (by omega)
  have hT : graphFun G ∅ (setInput T) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    rw [graph_true_iff] at ht
    obtain ⟨a, b, hab, ha, hb⟩ := ht
    have hs : graphFun G ∅ (setInput S) = true := by
      rw [graph_true_iff]
      exact ⟨a, b, hab, decide_eq_true (hTS (of_decide_eq_true ha)),
        decide_eq_true (hTS (of_decide_eq_true hb))⟩
    simp [hS] at hs
  have hcount := false_support_safe_neighbor_count n G color hbip h4 C hAO g W hsafe
    p hp X hX T hT hTg
  omega

lemma dirty_wmax_neighbors_need_junk_prefix
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : ℕ)
    (hdirty : IsDirty n G C g) (p : Fin n) (hp : p ∈ wmax G C g) :
    ((wmax G C g).filter (G.Adj p)).card ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  apply dirty_safe_neighbors_need_junk_prefix n G color hbip h4 C hAO g hdirty
    (wmax G C g) (fun v hv => (Finset.mem_filter.mp hv).2) p hp
  intro v hv
  exact Finset.mem_filter.mp hv

end PEqualNP.Outside.L_meta_2583.WmaxJunk

namespace PEqualNP.Outside.L_meta_2583.SharedSupport

lemma support_family_bound_anchor {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) (x : α) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost +
        (t.filter (fun i => x ∉ s i)).card + 1 := by
  induction m with
  | zero =>
    intro t ht
    have hinput' : ∀ i ∈ t, (s i).card ≤ 1 := by
      intro i hi
      exact hinput i (by have := ht hi; simpa using this)
    have hsub : t.biUnion s ⊆ insert x ((t.filter (fun i => x ∉ s i)).biUnion s) := by
      intro y hy
      obtain ⟨i, hit, hyi⟩ := Finset.mem_biUnion.mp hy
      by_cases hyx : y = x
      · exact Finset.mem_insert.mpr (Or.inl hyx)
      · apply Finset.mem_insert.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hit, ?_⟩, hyi⟩
        intro hxi
        exact hyx (Finset.card_le_one.mp (hinput' i hit) y hyi x hxi)
    have h1 := Finset.card_biUnion_le (s := t.filter (fun i => x ∉ s i)) (t := s)
    have h2 : ∑ i ∈ t.filter (fun i => x ∉ s i), (s i).card ≤
        (t.filter (fun i => x ∉ s i)).card := by
      calc
        _ ≤ ∑ i ∈ t.filter (fun i => x ∉ s i), 1 :=
          Finset.sum_le_sum fun i hi => hinput' i (Finset.mem_filter.mp hi).1
        _ = _ := by simp
    have h3 := Finset.card_insert_le x ((t.filter (fun i => x ∉ s i)).biUnion s)
    have h4 := Finset.card_le_card hsub
    simpa using (show (t.biUnion s).card ≤ (t.filter (fun i => x ∉ s i)).card + 1 by omega)
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro y hy
        obtain ⟨i, hit, hyi⟩ := Finset.mem_biUnion.mp hy
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hyj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hyi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hyj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hyi⟩
      have huc : (u.filter (fun i => x ∉ s i)).card ≤
          (t.filter (fun i => x ∉ s i)).card + cost m := by
        have heq : u.filter (fun i => x ∉ s i) =
            (t.filter (fun i => x ∉ s i)).erase (n + m) ∪
              (a m).filter (fun i => x ∉ s i) := by
          ext i
          simp only [u, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
          tauto
        rw [heq]
        have h1 := Finset.card_union_le
          ((t.filter (fun i => x ∉ s i)).erase (n + m)) ((a m).filter (fun i => x ∉ s i))
        have h3 := hcost m (by omega)
        by_cases hxm : x ∈ s (n + m)
        · obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxm)
          have hjsub : (a m).filter (fun i => x ∉ s i) ⊆ (a m).erase j := by
            intro i hi
            obtain ⟨hia, hxi⟩ := Finset.mem_filter.mp hi
            refine Finset.mem_erase.mpr ⟨?_, hia⟩
            intro heq
            exact hxi (heq.symm ▸ hxj)
          have h2 := Finset.card_erase_add_one hja
          have h4 := Finset.card_le_card hjsub
          have h5 := Finset.card_le_card (Finset.erase_subset (n + m)
            (t.filter (fun i => x ∉ s i)))
          omega
        · have hmem : n + m ∈ t.filter (fun i => x ∉ s i) := Finset.mem_filter.mpr ⟨hm, hxm⟩
          have h2 := Finset.card_erase_add_one hmem
          have h4 := Finset.card_filter_le (a m) (fun i => x ∉ s i)
          omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m +
        (t.filter (fun i => x ∉ s i)).card + 1
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m +
        (t.filter (fun i => x ∉ s i)).card + 1
      omega



lemma support_family_bound_anchor_closed {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s)
    (R : Finset ℕ)
    (hR : ∀ k ∈ R, k < m → ∀ j ∈ a k, j < n ∨ j - n ∈ R)
    (W : Finset ℕ) (hW : W ⊆ Finset.range (n + m))
    (hWR : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (x : α) (hshare : ∀ w ∈ W, x ∈ s w) :
    (W.biUnion s).card ≤ ((Finset.range m).filter (fun k => k ∈ R)).sum cost + 1 := by
  let ss : ℕ → Finset α := fun v => if v < n ∨ v - n ∈ R then s v else ∅
  let aa : ℕ → Finset ℕ := fun k => if k ∈ R then a k else ∅
  let cc : ℕ → ℕ := fun k => if k ∈ R then cost k else 0
  have hi : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hi
    simpa only [ss, ite_eq_left (Or.inl hi)] using hinput i hi
  have hb : ∀ k < m, aa k ⊆ Finset.range (n + k) := by
    intro k hk
    by_cases hkR : k ∈ R
    · simpa only [aa, ite_eq_left hkR] using hback k hk
    · simp [aa, hkR]
  have hc : ∀ k < m, (aa k).card ≤ cc k + 1 := by
    intro k hk
    by_cases hkR : k ∈ R
    · simpa only [aa, cc, ite_eq_left hkR] using hcost k hk
    · simp [aa, cc, hkR]
  have hv : ∀ k < m, ss (n + k) ⊆ (aa k).biUnion ss := by
    intro k hk y hy
    by_cases hkR : k ∈ R
    · have hs : ss (n + k) = s (n + k) := by simp [ss, hkR]
      obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp (hcover k hk (hs ▸ hy))
      have hsj : ss j = s j := by simp only [ss, ite_eq_left (hR k hkR hk j hj)]
      exact Finset.mem_biUnion.mpr ⟨j, by simpa [aa, hkR] using hj, hsj.symm ▸ hyj⟩
    · simp [ss, hkR] at hy
  have heq : W.biUnion ss = W.biUnion s := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hWR w hw)
  have hzero : W.filter (fun w => x ∉ ss w) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw hnot
    apply hnot
    simpa only [ss, ite_eq_left (hWR w hw)] using hshare w hw
  have hbound := support_family_bound_anchor n m ss aa cc hi hb hc hv x W hW
  have hsum : (Finset.range m).sum cc =
      ((Finset.range m).filter (fun k => k ∈ R)).sum cost := by
    simp only [cc, Finset.sum_filter]
  simpa only [heq, hzero, Finset.card_empty, Nat.add_zero, hsum] using hbound


open PEqualNP.Outside.L_meta_2583.Minterm

lemma pickedSupport_family_anchor_prefix (n m : ℕ) (a b : ℕ → ℕ) (both left : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (r : ℕ) (hr : r ≤ m) (W : Finset ℕ) (hW : ∀ w ∈ W, w < n + r)
    (x : Fin n) (hshare : ∀ w ∈ W, x ∈ pickedSupport n m a b both left ha hb w) :
    (W.biUnion (pickedSupport n m a b both left ha hb)).card ≤
      ((Finset.range r).filter fun k => both k = true).card + 1 := by
  let s := pickedSupport n m a b both left ha hb
  let parents : ℕ → Finset ℕ := fun k =>
    if both k then {a k, b k} else if left k then {a k} else {b k}
  let cost : ℕ → ℕ := fun k => if both k then 1 else 0
  have hinput : ∀ i < n, (s i).card ≤ 1 := by
    intro i hi
    simp [s, pickedSupport_input n m a b both left ha hb i hi]
  have hp : ∀ k < r, parents k ⊆ Finset.range (n + k) := by
    intro k hk i hi
    simp only [parents] at hi
    split_ifs at hi with h1 h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
      · exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (ha k (lt_of_lt_of_le hk hr))
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_range.mpr (hb k (lt_of_lt_of_le hk hr))
  have hc : ∀ k < r, (parents k).card ≤ cost k + 1 := by
    intro k _
    simp only [parents, cost]
    split_ifs <;> first | exact Finset.card_le_two | simp
  have hv : ∀ k < r, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    dsimp only [s, parents]
    rw [pickedSupport_gate n m a b both left ha hb k (lt_of_lt_of_le hk hr)]
    split_ifs <;> simp
  have hmain := support_family_bound_anchor n r s parents cost hinput hp hc hv x W
    (fun w hw => Finset.mem_range.mpr (hW w hw))
  have hsum : (Finset.range r).sum cost =
      ((Finset.range r).filter fun k => both k = true).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  have hzero : W.filter (fun i => x ∉ s i) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not.mpr (hshare i hi)
  simpa [hsum, hzero, s] using hmain

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma dirty_shared_roots_small_support_prefix (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : graphFun G ∅ (setInput S) = false)
    (r : ℕ) (hr : r ≤ C.gates.length) (W : Finset ℕ)
    (hvalid : ∀ w ∈ W, w < n + r)
    (htrue : ∀ w ∈ W, wv n C (setInput S) w = true)
    (x : Fin n) (hshare : ∀ w ∈ W, x ∈ circuitSupport n C hAO (setInput S) w) :
    ∃ T : Finset (Fin n), T ⊆ S ∧
      (∀ w ∈ W, wv n C (setInput T) w = true) ∧
      T.card ≤ (junk G C ∩ Finset.range r).card + 1 := by
  classical
  let T := W.biUnion (circuitSupport n C hAO (setInput S))
  have hsub : T ⊆ S := by
    intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    exact (support_sound n C hAO S w (htrue w hw)).1 hiw
  refine ⟨T, hsub, ?_, ?_⟩
  · intro w hw
    have hs := support_sound n C hAO S w (htrue w hw)
    exact wv_mono n C hAO.1 hAO.2.1
      (setInput (circuitSupport n C hAO (setInput S) w)) (setInput T)
      (fun i hi => by
        simp only [setInput, decide_eq_true_eq] at hi ⊢
        exact Finset.mem_biUnion.mpr ⟨w, hw, hi⟩) w hs.2
  · have hbound := pickedSupport_family_anchor_prefix n C.gates.length
      (fun k => opnd C k 0) (fun k => opnd C k 1) (pickedBoth n C (setInput S))
      (fun k => wv n C (setInput S) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) r hr W hvalid x hshare
    change T.card ≤ _ at hbound
    refine hbound.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
    intro k hk
    obtain ⟨hkr, hboth⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_inter.mpr
    refine ⟨true_ands_subset_junk n C G (setInput S) hS ?_, hkr⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hkr) hr), hboth⟩

open PEqualNP.Outside.L_meta_2583.MultiOrMask PEqualNP.Outside.L_meta_2583.PlaneSingleUse

lemma point_or_shared_siblings_need_junk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hgraph : ∀ z, circuitFun (N + N) C z = graphFun G ∅ z)
    (p : Fin N) (W : Finset ℕ)
    (hread : ∀ j < C.gates.length, p.val ∈ (gateAt C j).inputs →
      ∃ w ∈ W, w ≠ p.val ∧ (gateAt C j).op = GateOp.or ∧
        ((gateAt C j).inputs = [p.val, w] ∨ (gateAt C j).inputs = [w, p.val]))
    (hdegree : (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (hunique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (S : Finset (Fin (N + N))) (hS : circuitFun (N + N) C (setInput S) = false)
    (hw : ∀ w ∈ W, wv (N + N) C (setInput S) w = true)
    (r : ℕ) (hr : r ≤ C.gates.length) (hvalid : ∀ w ∈ W, w < N + N + r)
    (x : Fin (N + N))
    (hshare : ∀ w ∈ W, x ∈ circuitSupport (N + N) C hC (setInput S) w) :
    q ≤ (junk G C ∩ Finset.range r).card := by
  have hSG : graphFun G ∅ (setInput S) = false := (hgraph _).symm.trans hS
  obtain ⟨T, hTS, hTw, hcard⟩ :=
    dirty_shared_roots_small_support_prefix (N + N) C hC G S hSG r hr W hvalid hw x hshare
  have hT : circuitFun (N + N) C (setInput T) = false := by
    cases ht : circuitFun (N + N) C (setInput T) with
    | false => rfl
    | true =>
      have hs : circuitFun (N + N) C (setInput S) = true :=
        wv_mono (N + N) C hC.1 hC.2.1 (setInput T) (setInput S)
          (fun i hi => decide_eq_true (hTS (of_decide_eq_true hi))) C.output ht
      simp [hS] at hs
  have hcount := point_or_siblings_count_general q N I C hC hfun p W hread
    hdegree hunique (setInput T) hT hTw
  have hle := hcount.trans ((point_support_card_le T).trans hcard)
  omega


end PEqualNP.Outside.L_meta_2583.SharedSupport

namespace PEqualNP.Outside.L_meta_2583.BiasedSupport

open PEqualNP.Outside.L_meta_2583.Minterm

lemma pickedSupport_bias_contains
    (n m : ℕ) (a b : ℕ → ℕ) (both : ℕ → Bool)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (x : Fin n) :
    ∀ w, x ∈ pickedSupport n m a b (fun _ => true) (fun _ => true) ha hb w →
      x ∈ pickedSupport n m a b both
        (fun k => decide (x ∈ pickedSupport n m a b (fun _ => true) (fun _ => true) ha hb (a k)))
        ha hb w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hwn : w < n
    · simpa only [pickedSupport_input n m a b _ _ ha hb w hwn] using hx
    by_cases hwg : w < n + m
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      rw [pickedSupport_gate n m a b _ _ ha hb k hk] at hx ⊢
      simp only [↓reduceIte] at hx
      by_cases hkBoth : both k = true
      · rw [ite_eq_left hkBoth]
        rcases Finset.mem_union.mp hx with hxa | hxb
        · exact Finset.mem_union_left _ (ih (a k) (ha k hk) hxa)
        · exact Finset.mem_union_right _ (ih (b k) (hb k hk) hxb)
      · rw [ite_eq_right hkBoth]
        simp only [decide_eq_true_eq]
        split_ifs with hxa
        · exact ih (a k) (ha k hk) hxa
        · exact ih (b k) (hb k hk) ((Finset.mem_union.mp hx).resolve_left hxa)
    · rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg] at hx
      exact False.elim (Finset.notMem_empty _ hx)

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

def andSelector (C : Circuit) (k : ℕ) : Bool :=
  match (gateAt C k).op with
  | GateOp.and => true
  | _ => false

def selectedSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (left : ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (andSelector C) left
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

lemma selectedSupport_sound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (left : ℕ → Bool) :
    ∀ w, w < n + C.gates.length →
      wv n C (setInput (selectedSupport n C hAO left w)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [show selectedSupport n C hAO left w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      rw [wv_input n C _ w hwn]
      simp [setInput]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      have hval (v : ℕ) (hv : v < n + k)
          (hsub : selectedSupport n C hAO left v ⊆ selectedSupport n C hAO left (n + k)) :
          wv n C (setInput (selectedSupport n C hAO left (n + k))) v = true :=
        wv_mono n C hAO.1 hAO.2.1 _ _
          (fun i hi => decide_eq_true (hsub (of_decide_eq_true hi))) v
          (ih v hv (by omega))
      have hrec : selectedSupport n C hAO left (n + k) =
          if andSelector C k then
            selectedSupport n C hAO left (opnd C k 0) ∪ selectedSupport n C hAO left (opnd C k 1)
          else if left k then selectedSupport n C hAO left (opnd C k 0)
          else selectedSupport n C hAO left (opnd C k 1) :=
        pickedSupport_gate _ _ _ _ _ _ _ _ _ hk
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hs : andSelector C k = true := by simp [andSelector, hop]
        rw [hs] at hrec
        simp only [↓reduceIte] at hrec
        have hv0 := hval _ ha (by rw [hrec]; exact Finset.subset_union_left)
        have hv1 := hval _ hb (by rw [hrec]; exact Finset.subset_union_right)
        simp [hop, GateOp.eval, hv0, hv1]
      · have hs : andSelector C k = false := by simp [andSelector, hop]
        rw [hs] at hrec
        simp only [Bool.false_eq_true, ↓reduceIte] at hrec
        by_cases hl : left k = true
        · have hv0 := hval _ ha (by rw [hrec, ite_eq_left hl])
          simp [hop, GateOp.eval, hv0]
        · have hv1 := hval _ hb (by rw [hrec, ite_eq_right hl])
          simp [hop, GateOp.eval, hv1]


def fullSupport (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) : Finset (Fin n) :=
  pickedSupport n C.gates.length (fun k => opnd C k 0) (fun k => opnd C k 1)
    (fun _ => true) (fun _ => true)
    (fun k hk => opnd_back n C hAO k hk 0)
    (fun k hk => opnd_back n C hAO k hk 1) w

lemma syntactic_shared_roots_support_bound (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (r : ℕ) (hr : r ≤ C.gates.length) (W : Finset ℕ)
    (hvalid : ∀ w ∈ W, w < n + r)
    (x : Fin n) (hfull : ∀ w ∈ W, x ∈ fullSupport n C hAO w) :
    ∃ T : Finset (Fin n), (∀ w ∈ W, wv n C (setInput T) w = true) ∧
      T.card ≤ ((Finset.range r).filter (fun k => andSelector C k = true)).card + 1 := by
  let left : ℕ → Bool := fun k => decide (x ∈ fullSupport n C hAO (opnd C k 0))
  let T : Finset (Fin n) := W.biUnion (selectedSupport n C hAO left)
  have hshare : ∀ w ∈ W, x ∈ selectedSupport n C hAO left w := by
    intro w hw
    exact pickedSupport_bias_contains n C.gates.length
      (fun k => opnd C k 0) (fun k => opnd C k 1) (andSelector C)
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) x w (hfull w hw)
  refine ⟨T, ?_, ?_⟩
  · intro w hw
    have hv : w < n + C.gates.length := by have := hvalid w hw; omega
    have hs := selectedSupport_sound n C hAO left w hv
    exact wv_mono n C hAO.1 hAO.2.1
      (setInput (selectedSupport n C hAO left w)) (setInput T)
      (fun i hi => decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hw, of_decide_eq_true hi⟩)) w hs
  · have hb := SharedSupport.pickedSupport_family_anchor_prefix n C.gates.length
      (fun k => opnd C k 0) (fun k => opnd C k 1) (andSelector C) left
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) r hr W hvalid x hshare
    exact hb

end PEqualNP.Outside.L_meta_2583.BiasedSupport

namespace PEqualNP.Outside.L_meta_2583.LineEntryForest

/-- A finite forest potential. `children` have no shared child; AND nodes
  conserve a cost at most one across two children. All ordinary nodes have cost
  one. An entry node is allowed to lose cost. No circuit extraction is assumed. -/
lemma forest_and_le_entries {n : Nat}
    (children : Fin n → Finset (Fin n))
    (andNodes entryNodes : Finset (Fin n)) (cost : Fin n → Nat)
    (hdisjoint : Disjoint andNodes entryNodes)
    (hchildren : ∀ i j, i ≠ j → Disjoint (children i) (children j))
    (hcost : ∀ v, cost v ≤ 1)
    (hand : ∀ v ∈ andNodes,
      (children v).card = 2 ∧ cost v = ∑ w ∈ children v, cost w)
    (hleaf : ∀ v, v ∉ andNodes → v ∉ entryNodes → cost v = 1) :
    andNodes.card ≤ entryNodes.card := by
  classical
  let deficit : Fin n → Nat := fun v => 1 - cost v
  have hbalance (v : Fin n) : cost v + deficit v = 1 := by
    dsimp [deficit]
    have hv := hcost v
    omega
  have hsum (v : Fin n) :
      (∑ w ∈ children v, cost w) + (∑ w ∈ children v, deficit w) =
        (children v).card := by
    calc
      _ = ∑ w ∈ children v, (cost w + deficit w) :=
        (Finset.sum_add_distrib).symm
      _ = ∑ _w ∈ children v, (1 : Nat) :=
        Finset.sum_congr rfl (fun w _ => hbalance w)
      _ = _ := by simp
  have hlocal (v : Fin n) :
      (if v ∈ andNodes then 1 else 0) + deficit v ≤
        (if v ∈ entryNodes then 1 else 0) + ∑ w ∈ children v, deficit w := by
    by_cases ha : v ∈ andNodes
    · have he : v ∉ entryNodes := fun he => Finset.disjoint_left.mp hdisjoint ha he
      obtain ⟨hcard, hc⟩ := hand v ha
      have hb := hbalance v
      have hs := hsum v
      simp only [ite_eq_left ha, ite_eq_right he, zero_add]
      omega
    · by_cases he : v ∈ entryNodes
      · simp only [ite_eq_right ha, ite_eq_left he, zero_add]
        dsimp [deficit]
        omega
      · have hc := hleaf v ha he
        simp only [ite_eq_right ha, ite_eq_right he, zero_add]
        simp [deficit, hc]
  have hpair :
      (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint children := by
    intro i _ j _ hij
    exact hchildren i j hij
  have hflow : (∑ v, ∑ w ∈ children v, deficit w) ≤ ∑ v, deficit v := by
    rw [← Finset.sum_biUnion hpair]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have htotal := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun v _ => hlocal v)
  simp only [Finset.sum_add_distrib] at htotal
  have ha : (∑ v : Fin n, if v ∈ andNodes then (1 : Nat) else 0) =
      andNodes.card := by simp
  have he : (∑ v : Fin n, if v ∈ entryNodes then (1 : Nat) else 0) =
      entryNodes.card := by simp
  rw [ha, he] at htotal
  omega

end PEqualNP.Outside.L_meta_2583.LineEntryForest

namespace PEqualNP.Outside.L_meta_2583.AndSignature

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

end PEqualNP.Outside.L_meta_2583.AndSignature

namespace PEqualNP.Outside.L_meta_2583.AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma false_join_of_cone_signature_eq (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (x y : Fin n → Bool)
    (hsig : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C x (opnd C k 0) = wv n C y (opnd C k 0)) :
    ∀ w, (w < n ∨ w - n ∈ R) → wv n C x w = false → wv n C y w = false →
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
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hw.resolve_left hwn
      have hk : k < C.gates.length := Finset.mem_range.mp (hRreal hkR)
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk] at hx
      rw [wv_rec n C y hAO.2.1 k hk, inputs_two n C hAO k hk] at hy
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have heq := hsig k hkR hop
        cases hl : wv n C x (opnd C k 0) with
        | false =>
          have hly : wv n C y (opnd C k 0) = false := heq.symm.trans hl
          have hj := ih _ ha (hRclosed k hkR 0) hl hly
          simp [hop, GateOp.eval, hj]
        | true =>
          have hly : wv n C y (opnd C k 0) = true := heq.symm.trans hl
          have hxr : wv n C x (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hl] using hx
          have hyr : wv n C y (opnd C k 1) = false := by
            simpa [hop, GateOp.eval, hly] using hy
          have hj := ih _ hb (hRclosed k hkR 1) hxr hyr
          simp [hop, GateOp.eval, hj]
      · have hxx : wv n C x (opnd C k 0) = false ∧
            wv n C x (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hx
        have hyy : wv n C y (opnd C k 0) = false ∧
            wv n C y (opnd C k 1) = false := by simpa [hop, GateOp.eval] using hy
        have hj0 := ih _ ha (hRclosed k hkR 0) hxx.1 hyy.1
        have hj1 := ih _ hb (hRclosed k hkR 1) hxx.2 hyy.2
        simp [hop, GateOp.eval, hj0, hj1]

lemma false_family_card_le_cone_signatures {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : ℕ) (hw : w < n ∨ w - n ∈ R)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    Fintype.card α ≤ 2 ^ (R.filter (fun k => isAnd C k = true)).card := by
  classical
  let sig : α → ((R.filter (fun k => isAnd C k = true)) → Bool) := fun a k => wv n C (f a) (opnd C k.val 0)
  have hinj : Function.Injective sig := by
    intro a b hab
    by_contra hne
    have heq : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
        wv n C (f a) (opnd C k 0) = wv n C (f b) (opnd C k 0) := by
      intro k hk hop
      have hkA : k ∈ R.filter (fun k => isAnd C k = true) := by
        apply Finset.mem_filter.mpr
        exact ⟨hk, by simp [isAnd, hop]⟩
      exact congrFun hab ⟨k, hkA⟩
    have hf := false_join_of_cone_signature_eq n C hAO R hRreal hRclosed (f a) (f b) heq w hw
      (hfalse a) (hfalse b)
    rw [hjoin a b hne] at hf
    cases hf
  have hcard := Fintype.card_le_of_injective sig hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hcard

lemma false_cube_le_cone_and_count (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : ℕ) (hw : w < n ∨ w - n ∈ R)
    (d : ℕ) (f : (Fin d → Bool) → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → wv n C (fun i => f a i || f b i) w = true) :
    d ≤ (R.filter (fun k => isAnd C k = true)).card := by
  have hc := false_family_card_le_cone_signatures n C hAO R hRreal hRclosed w hw f hfalse hjoin
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end PEqualNP.Outside.L_meta_2583.AndSignature

namespace PEqualNP.Outside.L_meta_2583.ProductivePair

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

lemma safe_guards_hit_pair {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (a d : Fin n) (hnon : ¬ G.Adj a d)
    (hpair : f (setInput {a, d}) = true) :
    ∀ v ∈ W, G.Adj a v ∨ G.Adj d v := by
  classical
  have hind : ∀ u ∈ ({a, d} : Finset (Fin n)), ∀ v ∈ ({a, d} : Finset (Fin n)),
      ¬ G.Adj u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.irrefl
    · exact hnon
    · exact fun h => hnon h.symm
    · exact G.irrefl
  intro v hv
  have hf : f (setInput (insert v {a, d})) = true :=
    hmono _ _ (fun i hi => decide_eq_true
      (Finset.mem_insert_of_mem (of_decide_eq_true hi))) hpair
  have hg := hsafe v hv (setInput (insert v {a, d})) hf (by simp [setInput])
  have hgraph : ∃ u w, G.Adj u w ∧
      setInput (insert v {a, d}) u = true ∧ setInput (insert v {a, d}) w = true := by
    simpa [graphFun] using hg
  obtain ⟨u, w, huw, hu, hw⟩ := hgraph
  have hu' : u ∈ insert v ({a, d} : Finset (Fin n)) := of_decide_eq_true hu
  have hw' : w ∈ insert v ({a, d} : Finset (Fin n)) := of_decide_eq_true hw
  have hhit : ∃ t ∈ ({a, d} : Finset (Fin n)), G.Adj v t := by
    rcases Finset.mem_insert.mp hu' with rfl | huT
    · rcases Finset.mem_insert.mp hw' with rfl | hwT
      · exact False.elim (G.irrefl huw)
      · exact ⟨w, hwT, huw⟩
    · rcases Finset.mem_insert.mp hw' with rfl | hwT
      · exact ⟨u, huT, huw.symm⟩
      · exact False.elim (hind u huT w hwT huw)
  obtain ⟨t, ht, hvt⟩ := hhit
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact Or.inl hvt.symm
  · exact Or.inr hvt.symm

lemma nonedge_neighbor_union_matching {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (a d : Fin n) (hnon : ¬ G.Adj a d)
    (W : Finset (Fin n)) (hW : ∀ v ∈ W, G.Adj a v ∨ G.Adj d v) :
    ∀ v ∈ W, ∀ u ∈ W, ∀ w ∈ W, G.Adj v u → G.Adj v w → u = w := by
  classical
  have hsame (x y z : Fin n) (hxy : G.Adj x y) (hxz : G.Adj x z) :
      ¬ G.Adj y z := by
    intro hyz
    have h1 := hbip x y hxy
    have h2 := hbip x z hxz
    have h3 := hbip y z hyz
    cases hx : color x <;> cases hy : color y <;> cases hz : color z <;> simp_all
  intro v hv u hu w hw hvu hvw
  rcases hW v hv with hav | hdv
  · have hdne : d ≠ v := by intro h; exact hnon (h ▸ hav)
    have hdu : G.Adj d u := (hW u hu).resolve_left (fun hau => hsame a v u hav hau hvu)
    have hdw : G.Adj d w := (hW w hw).resolve_left (fun haw => hsame a v w hav haw hvw)
    apply Finset.card_le_one.mp (h4 d v hdne)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hdu, hvu⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hdw, hvw⟩
  · have hane : a ≠ v := by intro h; exact hnon (h ▸ hdv).symm
    have hau : G.Adj a u := (hW u hu).resolve_right (fun hdu => hsame d v u hdv hdu hvu)
    have haw : G.Adj a w := (hW w hw).resolve_right (fun hdw => hsame d v w hdv hdw hvw)
    apply Finset.card_le_one.mp (h4 a v hane)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hau, hvu⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, haw, hvw⟩

lemma productive_endpoints_accept_all_edges {n : Nat} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (W V : Finset (Fin n)) (hVW : V ⊆ W)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ w ∈ W,
      G.Adj v u → G.Adj v w → u = w)
    (hlive : ∀ v ∈ V, ∃ w ∈ V, G.Adj v w ∧ f (setInput {v, w}) = true) :
    ∀ u ∈ V, ∀ v ∈ V, G.Adj u v → f (setInput {u, v}) = true := by
  intro u hu v hv huv
  obtain ⟨w, hw, huw, hf⟩ := hlive u hu
  have heq := hmatching u (hVW hu) v (hVW hv) w (hVW hw) huv huw
  simpa [heq] using hf

lemma restricted_productive_matching_exact {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hzero : f (fun _ => false) = false)
    (W V : Finset (Fin n)) (hVW : V ⊆ W)
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ w ∈ W,
      G.Adj v u → G.Adj v w → u = w)
    (hlive : ∀ v ∈ V, ∃ w ∈ V, G.Adj v w ∧ f (setInput {v, w}) = true)
    (x : Fin n → Bool) (hx : ∀ v, x v = true → v ∈ V) :
    f x = graphFun G ∅ x := by
  classical
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hf
    have hex : ∃ v, x v = true := by
      by_contra hn
      push Not at hn
      have heq : x = fun _ => false := by
        funext v
        exact Bool.eq_false_iff.mpr (hn v)
      rw [heq, hzero] at hf
      contradiction
    obtain ⟨v, hv⟩ := hex
    exact hsafe v (hVW (hx v hv)) x hf hv
  · intro hg
    have hgraph : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hg
    obtain ⟨u, v, huv, hu, hv⟩ := hgraph
    have hp := productive_endpoints_accept_all_edges G f W V hVW hmatching hlive
      u (hx u hu) v (hx v hv) huv
    apply hmono (setInput {u, v}) x ?_ hp
    intro i hi
    have him : i ∈ ({u, v} : Finset (Fin n)) := of_decide_eq_true hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at him
    rcases him with rfl | rfl
    · exact hu
    · exact hv

end PEqualNP.Outside.L_meta_2583.ProductivePair

namespace PEqualNP.Outside.L_meta_2583.ProductiveCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit
  PEqualNP.Outside.L_meta_2583.ProductivePair

lemma wv_zero (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, wv n C (fun _ => false) w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · exact wv_input n C (fun _ => false) w hwn
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have h0 := ih (opnd C k 0) (opnd_back n C hAO k hk 0)
      have h1 := ih (opnd C k 1) (opnd_back n C hAO k hk 1)
      rw [wv_rec n C _ hAO.2.1 k hk, inputs_two n C hAO k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop <;>
        simp [hop, GateOp.eval, h0, h1]
    · exact wv_missing n C _ w (by omega)

lemma wmax_matching_of_false_pair
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : ℕ)
    (a d : Fin n) (hnon : ¬ G.Adj a d)
    (hpair : gateVal n C g (setInput {a, d}) = true) :
    ∀ v ∈ wmax G C g, ∀ u ∈ wmax G C g, ∀ z ∈ wmax G C g,
      G.Adj v u → G.Adj v z → u = z := by
  apply nonedge_neighbor_union_matching G color hbip h4 a d hnon (wmax G C g)
  exact safe_guards_hit_pair G (gateVal n C g)
    (fun x y hxy => wv_mono n C hAO.1 hAO.2.1 x y hxy (n + g))
    (wmax G C g) (fun v hv => (Finset.mem_filter.mp hv).2) a d hnon hpair

lemma productive_wmax_restriction_exact
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : ℕ)
    (a d : Fin n) (hnon : ¬ G.Adj a d)
    (hpair : gateVal n C g (setInput {a, d}) = true)
    (V : Finset (Fin n)) (hVW : V ⊆ wmax G C g)
    (hlive : ∀ v ∈ V, ∃ z ∈ V, G.Adj v z ∧
      gateVal n C g (setInput {v, z}) = true)
    (x : Fin n → Bool) (hx : ∀ v, x v = true → v ∈ V) :
    gateVal n C g x = graphFun G ∅ x := by
  apply restricted_productive_matching_exact G (gateVal n C g)
    (fun x y hxy => wv_mono n C hAO.1 hAO.2.1 x y hxy (n + g))
    (wv_zero n C hAO (n + g)) (wmax G C g) V hVW
    (fun v hv => (Finset.mem_filter.mp hv).2)
    (wmax_matching_of_false_pair n G color hbip h4 C hAO g a d hnon hpair)
    hlive x hx

end PEqualNP.Outside.L_meta_2583.ProductiveCircuit

namespace PEqualNP.Outside.L_meta_2583.ProductivePair

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

def matchingChoiceInput {n d : Nat} (endpt : Fin d → Bool → Fin n)
    (choice : Fin d → Bool) : Fin n → Bool :=
  fun v => decide (∃ i, v = endpt i (choice i))

lemma matchingChoiceInput_chosen {n d : Nat} (endpt : Fin d → Bool → Fin n)
    (choice : Fin d → Bool) (i : Fin d) :
    matchingChoiceInput endpt choice (endpt i (choice i)) = true := by
  exact decide_eq_true ⟨i, rfl⟩

lemma matchingChoiceInput_false {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ w ∈ W,
      G.Adj v u → G.Adj v w → u = w)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (choice : Fin d → Bool) : f (matchingChoiceInput endpt choice) = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro hf
  have hex : ∃ v, matchingChoiceInput endpt choice v = true := by
    by_contra hn
    push Not at hn
    have heq : matchingChoiceInput endpt choice = fun _ => false := by
      funext v
      exact Bool.eq_false_iff.mpr (hn v)
    rw [heq, hzero] at hf
    contradiction
  obtain ⟨v, hv⟩ := hex
  obtain ⟨i, hi⟩ := of_decide_eq_true hv
  have hg := hsafe v (hi ▸ hW i (choice i)) _ hf hv
  have hgraph : ∃ a b, G.Adj a b ∧ matchingChoiceInput endpt choice a = true ∧
      matchingChoiceInput endpt choice b = true := by simpa [graphFun] using hg
  obtain ⟨a, b, hab, ha, hb⟩ := hgraph
  obtain ⟨i, rfl⟩ := of_decide_eq_true ha
  obtain ⟨j, rfl⟩ := of_decide_eq_true hb
  have hop : G.Adj (endpt i (choice i)) (endpt i (!(choice i))) := by
    cases hc : choice i
    · simpa [hc] using (hedge i).symm
    · simpa [hc] using hedge i
  have heq := hmatching (endpt i (choice i)) (hW i _) (endpt j (choice j)) (hW j _)
    (endpt i (!(choice i))) (hW i _) hab hop
  have hp : (j, choice j) = (i, !(choice i)) := hinj heq
  have hij : j = i := congrArg Prod.fst hp
  subst j
  have hb : choice i = !(choice i) := congrArg Prod.snd hp
  cases hc : choice i <;> simp [hc] at hb

lemma matchingChoiceInput_join_true {n d : Nat}
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (endpt : Fin d → Bool → Fin n)
    (haccept : ∀ i, f (setInput {endpt i true, endpt i false}) = true)
    (choice other : Fin d → Bool) (hne : choice ≠ other) :
    f (fun v => matchingChoiceInput endpt choice v || matchingChoiceInput endpt other v) = true := by
  classical
  have hex : ∃ i, choice i ≠ other i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  obtain ⟨i, hi⟩ := hex
  have hboth (b : Bool) :
      (matchingChoiceInput endpt choice (endpt i b) ||
        matchingChoiceInput endpt other (endpt i b)) = true := by
    have hc : choice i = b ∨ other i = b := by
      cases h1 : choice i <;> cases h2 : other i <;> cases b <;> simp_all
    rcases hc with hc | hc
    · have hv : matchingChoiceInput endpt choice (endpt i b) = true :=
        decide_eq_true ⟨i, by rw [hc]⟩
      simp [hv]
    · have hv : matchingChoiceInput endpt other (endpt i b) = true :=
        decide_eq_true ⟨i, by rw [hc]⟩
      simp [hv]
  apply hmono (setInput {endpt i true, endpt i false}) _ ?_ (haccept i)
  intro v hv
  have hm : v ∈ ({endpt i true, endpt i false} : Finset (Fin n)) := of_decide_eq_true hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact hboth true
  · exact hboth false

end PEqualNP.Outside.L_meta_2583.ProductivePair

namespace PEqualNP.Outside.L_meta_2583.ProductivePair

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma productive_matching_le_cone_ands {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : Nat) (hw : w < n ∨ w - n ∈ R)
    (hzero : wv n C (fun _ => false) w = false)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, wv n C (ReadK.setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  apply AndSignature.false_cube_le_cone_and_count n C hAO R hRreal hRclosed w hw d
    (matchingChoiceInput endpt)
  · exact matchingChoiceInput_false G (fun x => wv n C x w) hzero W hsafe hmatching
      endpt hinj hW hedge
  · intro choice other hne
    exact matchingChoiceInput_join_true (fun x => wv n C x w)
      (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy w hx)
      endpt haccept choice other hne

lemma productive_matching_le_cone_junk {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hRjunk : ∀ k ∈ R, AndSignature.isAnd C k = true → k ∈ junk G C)
    (w : Nat) (hw : w < n ∨ w - n ∈ R)
    (hzero : wv n C (fun _ => false) w = false)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, wv n C (ReadK.setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R ∩ junk G C).card := by
  classical
  have hcount := productive_matching_le_cone_ands G C hAO R hRreal hRclosed w hw
    hzero W hsafe hmatching endpt hinj hW hedge haccept
  apply hcount.trans
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkR, hkA⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_inter.mpr ⟨hkR, hRjunk k hkR hkA⟩

end PEqualNP.Outside.L_meta_2583.ProductivePair

namespace PEqualNP.Outside.L_meta_2583.AncestorJunk

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.MintermCircuit

/-- The strict ancestor gates together with the selected gate itself. -/
def gateCone (n : ℕ) (C : Circuit) (g : ℕ) : Finset ℕ :=
  insert g ((Finset.range g).filter (fun k => InCone n C k g))

lemma mem_gateCone (n : ℕ) (C : Circuit) (g k : ℕ) :
    k ∈ gateCone n C g ↔ k = g ∨ InCone n C k g := by
  constructor
  · intro hk
    rcases Finset.mem_insert.mp hk with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2
  · intro hk
    rcases hk with hk | hk
    · exact Finset.mem_insert.mpr (Or.inl hk)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (TopNormal.inCone_lt n C k g hk).1, hk⟩))

lemma gateCone_self (n : ℕ) (C : Circuit) (g : ℕ) : g ∈ gateCone n C g :=
  (mem_gateCone n C g g).mpr (Or.inl rfl)

lemma gateCone_prefix (n : ℕ) (C : Circuit) (g : ℕ) :
    gateCone n C g ⊆ Finset.range (g + 1) := by
  intro k hk
  rcases (mem_gateCone n C g k).mp hk with rfl | hk
  · exact Finset.mem_range.mpr (by omega)
  · exact Finset.mem_range.mpr (by have := (TopNormal.inCone_lt n C k g hk).1; omega)

lemma gateCone_real (n : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    gateCone n C g ⊆ Finset.range C.gates.length := by
  intro k hk
  have hkg := Finset.mem_range.mp (gateCone_prefix n C g hk)
  exact Finset.mem_range.mpr (by omega)

lemma gateCone_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g < C.gates.length) :
    ∀ k ∈ gateCone n C g, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ gateCone n C g := by
  intro k hk b
  have hklen := Finset.mem_range.mp (gateCone_real n C g hg hk)
  by_cases hb : opnd C k b < n
  · exact Or.inl hb
  · right
    have hback := opnd_back n C hAO k hklen b
    have hread : opnd C k b ∈ (gateAt C k).inputs := by
      rw [inputs_two n C hAO k hklen]
      fin_cases b <;> simp
    have hdirect : InCone n C (opnd C k b - n) k := by
      apply (TopNormal.inCone_iff n C _ k).mpr
      refine ⟨hklen, opnd C k b - n, by omega, ?_, Or.inl rfl⟩
      have heq : n + (opnd C k b - n) = opnd C k b := by omega
      exact heq.symm ▸ hread
    apply (mem_gateCone n C g _).mpr
    right
    rcases (mem_gateCone n C g k).mp hk with rfl | hkg
    · exact hdirect
    · exact TopNormal.inCone_trans n C _ k hdirect g hkg

lemma gateCone_ands_subset_junk_prefix
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hTop : TopForm G C) (g : ℕ) (hg : IsDirtyAnd n G C g) :
    (gateCone n C g).filter (fun k => AndSignature.isAnd C k = true) ⊆
      junk G C ∩ Finset.range (g + 1) := by
  classical
  intro k hk
  obtain ⟨hkR, hkAND⟩ := Finset.mem_filter.mp hk
  have hop : (gateAt C k).op = GateOp.and := by
    cases h : (gateAt C k).op <;> simp [AndSignature.isAnd, h] at hkAND ⊢
  have hkreal := Finset.mem_range.mp (gateCone_real n C g hg.2.1 hkR)
  have hkdirty : IsDirtyAnd n G C k := by
    rcases (mem_gateCone n C g k).mp hkR with rfl | hkg
    · exact hg
    · have hnot : ¬BelowF G C k := fun hbelow =>
        hTop k hkreal g hg.2.1 hop hbelow hg.1 hkg
      unfold BelowF at hnot
      push Not at hnot
      obtain ⟨x, hx, hfalse⟩ := hnot
      exact ⟨hop, hkreal, x, hx, Bool.eq_false_iff.mpr hfalse⟩
  exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hkreal, hkdirty⟩, gateCone_prefix n C g hkR⟩

lemma gateCone_and_count_le_junk_prefix
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hTop : TopForm G C) (g : ℕ) (hg : IsDirtyAnd n G C g) :
    ((gateCone n C g).filter (fun k => AndSignature.isAnd C k = true)).card ≤
      (junk G C ∩ Finset.range (g + 1)).card :=
  Finset.card_le_card (gateCone_ands_subset_junk_prefix n G C hTop g hg)

end PEqualNP.Outside.L_meta_2583.AncestorJunk

namespace PEqualNP.Outside.L_meta_2583.ProductiveCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_2583.SingleUse
  PEqualNP.Outside.L_meta_2583.ProductivePair PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma dirty_productive_matching_le_junk_prefix
    (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : ℕ) (hg : IsDirtyAnd n G C g)
    (W : Finset (Fin n)) (hWsub : W ⊆ wmax G C g)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  have hcount := productive_matching_le_cone_ands G C hAO (gateCone n C g)
    (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1)
    (n + g) (Or.inr (by simpa using gateCone_self n C g))
    (wv_zero n C hAO (n + g)) W
    (fun v hv => (Finset.mem_filter.mp (hWsub hv)).2)
    hmatching endpt hinj hW hedge haccept
  exact hcount.trans (gateCone_and_count_le_junk_prefix n G C hTop g hg)

lemma dirty_pair_productive_matching_le_junk_prefix
    (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : ℕ) (hg : IsDirtyAnd n G C g)
    (a b : Fin n) (hnon : ¬ G.Adj a b)
    (hpair : gateVal n C g (setInput {a, b}) = true)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i c, endpt i c ∈ wmax G C g)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  exact dirty_productive_matching_le_junk_prefix n d G C hAO hTop g hg
    (wmax G C g) (fun _ h => h)
    (wmax_matching_of_false_pair n G color hbip h4 C hAO g a b hnon hpair)
    endpt hinj hW hedge haccept

end PEqualNP.Outside.L_meta_2583.ProductiveCircuit

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

lemma safe_guard_hits_support {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true) :
    ∀ v ∈ W, ∃ t ∈ T, G.Adj v t := by
  classical
  have hind : ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b := by
    intro a ha b hb hab
    have ht : graphFun G ∅ (setInput T) = true := by
      simpa [graphFun] using (show ∃ u v, G.Adj u v ∧ setInput T u = true ∧
        setInput T v = true from ⟨a, b, hab, decide_eq_true ha, decide_eq_true hb⟩)
    rw [hT] at ht
    contradiction
  intro v hv
  have hfv : f (setInput (insert v T)) = true :=
    hmono _ _ (fun i hi => decide_eq_true
      (Finset.mem_insert_of_mem (of_decide_eq_true hi))) hf
  have hg := hsafe v hv (setInput (insert v T)) hfv (by simp [setInput])
  have hgraph : ∃ a b, G.Adj a b ∧ setInput (insert v T) a = true ∧
      setInput (insert v T) b = true := by simpa [graphFun] using hg
  obtain ⟨a, b, hab, ha, hb⟩ := hgraph
  have ha' : a ∈ insert v T := of_decide_eq_true ha
  have hb' : b ∈ insert v T := of_decide_eq_true hb
  rcases Finset.mem_insert.mp ha' with rfl | haT
  · rcases Finset.mem_insert.mp hb' with rfl | hbT
    · exact False.elim (G.irrefl hab)
    · exact ⟨b, hbT, hab⟩
  · rcases Finset.mem_insert.mp hb' with rfl | hbT
    · exact ⟨a, haT, hab.symm⟩
    · exact False.elim (hind a haT b hbT hab)

lemma safe_guards_disjoint_support {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true) :
    Disjoint W T := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvW hvT
  have h := hsafe v hvW (setInput T) hf (decide_eq_true hvT)
  rw [hT] at h
  contradiction

lemma thin_support_guard_centers {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true)
    (d : Fin n) (hunique : ∀ t ∈ T, color t = true → t = d) :
    ∀ v ∈ W, color v = false → G.Adj v d := by
  intro v hv hc
  obtain ⟨t, ht, hvt⟩ := safe_guard_hits_support G f hmono W T hsafe hT hf v hv
  have hct : color t = true := by
    have hb := hbip v t hvt
    cases hh : color t <;> simp_all
  simpa [hunique t ht hct] using hvt

lemma thin_support_guard_line_degree {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (h4 : NoFourCycle G)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true)
    (d : Fin n) (hd : d ∈ T)
    (hunique : ∀ t ∈ T, color t = true → t = d) :
    ∀ l ∈ W, color l = true → ∀ u ∈ W, ∀ v ∈ W,
      G.Adj l u → G.Adj l v → u = v := by
  classical
  intro l hlW hl u huW v hvW hlu hlv
  have hld : l ≠ d := by
    intro heq
    exact Finset.disjoint_left.mp (safe_guards_disjoint_support G f W T hsafe hT hf)
      hlW (heq ▸ hd)
  have hu : color u = false := by
    have hb := hbip l u hlu
    cases hh : color u <;> simp_all
  have hv : color v = false := by
    have hb := hbip l v hlv
    cases hh : color v <;> simp_all
  have hdu := (thin_support_guard_centers G color hbip f hmono W T hsafe hT hf d
    hunique u huW hu).symm
  have hdv := (thin_support_guard_centers G color hbip f hmono W T hsafe hT hf d
    hunique v hvW hv).symm
  apply Finset.card_le_one.mp (h4 l d hld)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hlu, hdu⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hlv, hdv⟩

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.TopForm

def starEndpoint {n d : Nat} (point line : Fin d → Fin n)
    (i : Fin d) (b : Bool) : Fin n := if b then line i else point i

def starEndpointSet {n d : Nat} (point line : Fin d → Fin n) : Finset (Fin n) :=
  Finset.univ.image (fun ib : Fin d × Bool => starEndpoint point line ib.1 ib.2)

lemma star_edge_no_cross {n d : Nat} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (W : Finset (Fin n))
    (hdegree : ∀ l ∈ W, color l = true → ∀ u ∈ W, ∀ v ∈ W,
      G.Adj l u → G.Adj l v → u = v)
    (point line : Fin d → Fin n) (hpoint : Function.Injective point)
    (hPW : ∀ i, point i ∈ W) (hLW : ∀ i, line i ∈ W)
    (hLC : ∀ i, color (line i) = true)
    (hedge : ∀ i, G.Adj (point i) (line i)) :
    ∀ i j, G.Adj (point i) (line j) → i = j := by
  intro i j hij
  apply hpoint
  exact hdegree (line j) (hLW j) (hLC j) (point i) (hPW i) (point j) (hPW j)
    hij.symm (hedge j).symm

lemma starEndpointSet_subset {n d : Nat} (W : Finset (Fin n))
    (point line : Fin d → Fin n) (hPW : ∀ i, point i ∈ W) (hLW : ∀ i, line i ∈ W) :
    starEndpointSet point line ⊆ W := by
  intro v hv
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hv
  cases b <;> simp [starEndpoint, hPW, hLW]

lemma starEndpoint_injective {n d : Nat} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (W : Finset (Fin n))
    (hdegree : ∀ l ∈ W, color l = true → ∀ u ∈ W, ∀ v ∈ W,
      G.Adj l u → G.Adj l v → u = v)
    (point line : Fin d → Fin n) (hpoint : Function.Injective point)
    (hPW : ∀ i, point i ∈ W) (hLW : ∀ i, line i ∈ W)
    (hPC : ∀ i, color (point i) = false) (hLC : ∀ i, color (line i) = true)
    (hedge : ∀ i, G.Adj (point i) (line i)) :
    Function.Injective (fun ib : Fin d × Bool => starEndpoint point line ib.1 ib.2) := by
  have hline : Function.Injective line := by
    intro i j hij
    apply star_edge_no_cross G color W hdegree point line hpoint hPW hLW hLC hedge i j
    simpa [← hij] using hedge i
  intro x y hxy
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  have hcolor (i : Fin d) (b : Bool) : color (starEndpoint point line i b) = b := by
    cases b <;> simp [starEndpoint, hPC, hLC]
  have hc : b = c := by
    simpa only [hcolor] using congrArg color hxy
  subst c
  cases b
  · have hij : i = j := hpoint (by simpa [starEndpoint] using hxy)
    simp [hij]
  · have hij : i = j := hline (by simpa [starEndpoint] using hxy)
    simp [hij]

lemma starEndpointSet_matching {n d : Nat} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (W : Finset (Fin n))
    (hdegree : ∀ l ∈ W, color l = true → ∀ u ∈ W, ∀ v ∈ W,
      G.Adj l u → G.Adj l v → u = v)
    (point line : Fin d → Fin n) (hpoint : Function.Injective point)
    (hPW : ∀ i, point i ∈ W) (hLW : ∀ i, line i ∈ W)
    (hPC : ∀ i, color (point i) = false) (hLC : ∀ i, color (line i) = true)
    (hedge : ∀ i, G.Adj (point i) (line i)) :
    ∀ v ∈ starEndpointSet point line, ∀ u ∈ starEndpointSet point line,
      ∀ w ∈ starEndpointSet point line, G.Adj v u → G.Adj v w → u = w := by
  have hcross := star_edge_no_cross G color W hdegree point line hpoint hPW hLW hLC hedge
  have hadj : ∀ i b j c, G.Adj (starEndpoint point line i b) (starEndpoint point line j c) →
      i = j ∧ b ≠ c := by
    intro i b j c h
    cases b <;> cases c
    · have hb := hbip _ _ h
      simp [starEndpoint, hPC] at hb
    · exact ⟨hcross i j (by simpa [starEndpoint] using h), by decide⟩
    · exact ⟨(hcross j i (by simpa [starEndpoint] using h.symm)).symm, by decide⟩
    · have hb := hbip _ _ h
      simp [starEndpoint, hLC] at hb
  intro v hv u hu w hw hvu hvw
  obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨⟨j, c⟩, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨⟨k, e⟩, _, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hij, hbc⟩ := hadj i b j c hvu
  obtain ⟨hik, hbe⟩ := hadj i b k e hvw
  subst j
  subst k
  have hce : c = e := by cases b <;> cases c <;> cases e <;> simp_all
  rw [hce]

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma thin_productive_centers_le_cone_junk {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hRjunk : ∀ k ∈ R, AndSignature.isAnd C k = true → k ∈ junk G C)
    (w : Nat) (hw : w < n ∨ w - n ∈ R)
    (hzero : wv n C (fun _ => false) w = false)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : wv n C (setInput T) w = true)
    (t : Fin n) (ht : t ∈ T) (hunique : ∀ v ∈ T, color v = true → v = t)
    (point line : Fin d → Fin n) (hpoint : Function.Injective point)
    (hPW : ∀ i, point i ∈ W) (hLW : ∀ i, line i ∈ W)
    (hPC : ∀ i, color (point i) = false) (hLC : ∀ i, color (line i) = true)
    (hedge : ∀ i, G.Adj (point i) (line i))
    (haccept : ∀ i, wv n C (setInput {point i, line i}) w = true) :
    d ≤ (R ∩ junk G C).card := by
  classical
  have hdegree := thin_support_guard_line_degree G color hbip h4 (fun x => wv n C x w)
    (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy w hx)
    W T hsafe hT hf t ht hunique
  have hsub := starEndpointSet_subset W point line hPW hLW
  apply ProductivePair.productive_matching_le_cone_junk G C hAO R hRreal hRclosed hRjunk
    w hw hzero (starEndpointSet point line)
    (fun v hv => hsafe v (hsub hv))
    (starEndpointSet_matching G color hbip W hdegree point line hpoint hPW hLW hPC hLC hedge)
    (starEndpoint point line)
    (starEndpoint_injective G color W hdegree point line hpoint hPW hLW hPC hLC hedge)
  · intro i b
    exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩
  · intro i
    simpa [starEndpoint] using (hedge i).symm
  · intro i
    simpa [starEndpoint, Finset.pair_comm] using haccept i

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.ProductiveCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_2583.SingleUse
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.ThinSupport

lemma dirty_thin_productive_centers_le_junk_prefix
    (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : ℕ) (hg : IsDirtyAnd n G C g)
    (T : Finset (Fin n)) (hT : graphFun G ∅ (setInput T) = false)
    (hf : gateVal n C g (setInput T) = true)
    (t : Fin n) (ht : t ∈ T) (hunique : ∀ v ∈ T, color v = true → v = t)
    (point line : Fin d → Fin n) (hpoint : Function.Injective point)
    (hPW : ∀ i, point i ∈ wmax G C g) (hLW : ∀ i, line i ∈ wmax G C g)
    (hPC : ∀ i, color (point i) = false) (hLC : ∀ i, color (line i) = true)
    (hedge : ∀ i, G.Adj (point i) (line i))
    (haccept : ∀ i, gateVal n C g (setInput {point i, line i}) = true) :
    d ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  have hRjunk : ∀ k ∈ gateCone n C g, AndSignature.isAnd C k = true → k ∈ junk G C := by
    intro k hk hka
    exact (Finset.mem_inter.mp (gateCone_ands_subset_junk_prefix n G C hTop g hg
      (Finset.mem_filter.mpr ⟨hk, hka⟩))).1
  have hcount := thin_productive_centers_le_cone_junk G color hbip h4 C hAO
    (gateCone n C g) (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1)
    hRjunk (n + g) (Or.inr (by simpa using gateCone_self n C g))
    (wv_zero n C hAO (n + g)) (wmax G C g) T
    (fun v hv => (Finset.mem_filter.mp hv).2) hT hf t ht hunique
    point line hpoint hPW hLW hPC hLC hedge haccept
  apply hcount.trans
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkR, hkj⟩ := Finset.mem_inter.mp hk
  exact Finset.mem_inter.mpr ⟨hkj, gateCone_prefix n C g hkR⟩

end PEqualNP.Outside.L_meta_2583.ProductiveCircuit

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

lemma safe_neighbors_le_support_color {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (h4 : NoFourCycle G)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true)
    (p : Fin n) (hp : p ∈ W) (X : Finset (Fin n))
    (hX : ∀ v ∈ X, v ∈ W ∧ G.Adj p v) :
    X.card ≤ (T.filter (fun t => color t = color p)).card := by
  classical
  have hpT : p ∉ T := fun ht =>
    Finset.disjoint_left.mp (safe_guards_disjoint_support G f W T hsafe hT hf) hp ht
  have hchoose : ∀ v ∈ X, ∃ t ∈ T, G.Adj v t := fun v hv =>
    safe_guard_hits_support G f hmono W T hsafe hT hf v (hX v hv).1
  let pick : Fin n → Fin n := fun v => if hv : v ∈ X then (hchoose v hv).choose else p
  have hpick : ∀ v ∈ X, pick v ∈ T ∧ G.Adj v (pick v) := by
    intro v hv
    simpa only [pick, dite_eq_left hv] using (hchoose v hv).choose_spec
  apply Finset.card_le_card_of_injOn pick
  · intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨(hpick v hv).1, ?_⟩
    have h1 := hbip p v (hX v hv).2
    have h2 := hbip v (pick v) (hpick v hv).2
    cases hc1 : color p <;> cases hc2 : color v <;> cases hc3 : color (pick v) <;> simp_all
  · intro v hv u hu heq
    have hpt : p ≠ pick v := by
      intro h
      exact hpT (h ▸ (hpick v hv).1)
    apply Finset.card_le_one.mp (h4 p (pick v) hpt)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (hX v hv).2, (hpick v hv).2.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, (hX u hu).2,
        by rw [heq]; exact (hpick u hu).2.symm⟩

lemma safe_guard_degree_le_support_color {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (h4 : NoFourCycle G)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true)
    (p : Fin n) (hp : p ∈ W) :
    (W.filter (G.Adj p)).card ≤ (T.filter (fun t => color t = color p)).card := by
  apply safe_neighbors_le_support_color G color hbip h4 f hmono W T hsafe hT hf p hp
    (W.filter (G.Adj p))
  intro v hv
  exact Finset.mem_filter.mp hv

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

lemma small_support_has_small_color {n : Nat} (color : Fin n → Bool)
    (T : Finset (Fin n)) (hcard : T.card ≤ 3) :
    ∃ c : Bool, (T.filter (fun v => color v = c)).card ≤ 1 := by
  classical
  have hdisj : Disjoint (T.filter (fun v => color v = false))
      (T.filter (fun v => color v = true)) := by
    apply Finset.disjoint_left.mpr
    intro v hf ht
    have hf' := (Finset.mem_filter.mp hf).2
    have ht' := (Finset.mem_filter.mp ht).2
    rw [hf'] at ht'
    contradiction
  have hunion : T.filter (fun v => color v = false) ∪ T.filter (fun v => color v = true) = T := by
    ext v
    cases hc : color v <;> simp [hc]
  have hsum : (T.filter (fun v => color v = false)).card +
      (T.filter (fun v => color v = true)).card = T.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  by_cases hfalse : (T.filter (fun v => color v = false)).card ≤ 1
  · exact ⟨false, hfalse⟩
  · exact ⟨true, by omega⟩

lemma small_support_safe_star_orientation {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (h4 : NoFourCycle G)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (W T : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (hT : graphFun G ∅ (setInput T) = false) (hf : f (setInput T) = true)
    (hcard : T.card ≤ 3) :
    ∃ c : Bool, ∀ p ∈ W, color p = c → (W.filter (G.Adj p)).card ≤ 1 := by
  obtain ⟨c, hc⟩ := small_support_has_small_color color T hcard
  refine ⟨c, ?_⟩
  intro p hp hpc
  have h := safe_guard_degree_le_support_color G color hbip h4 f hmono W T hsafe hT hf p hp
  rw [hpc] at h
  exact h.trans hc

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.ThinSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma dirty_small_junk_wmax_star_orientation
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (g : Nat)
    (hdirty : IsDirty n G C g)
    (hsmall : (junk G C ∩ Finset.range (g + 1)).card ≤ 2) :
    ∃ c : Bool, ∀ p ∈ wmax G C g, color p = c →
      ((wmax G C g).filter (G.Adj p)).card ≤ 1 := by
  classical
  obtain ⟨hg, x, hgx, hx⟩ := hdirty
  let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
  have hSx : setInput S = x := by
    funext i
    cases hi : x i <;> simp [setInput, S, hi]
  have hS : graphFun G ∅ (setInput S) = false := by rw [hSx]; exact hx
  have hSg : wv n C (setInput S) (n + g) = true := by rw [hSx]; exact hgx
  obtain ⟨T, hTS, hTg, hcard⟩ :=
    MintermCircuit.dirty_wire_small_support_prefix n C hAO G S hS (n + g) hSg
      (g + 1) (by omega) (by omega)
  have hT : graphFun G ∅ (setInput T) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    rw [WmaxJunk.graph_true_iff] at ht
    obtain ⟨a, b, hab, ha, hb⟩ := ht
    have hs : graphFun G ∅ (setInput S) = true := by
      rw [WmaxJunk.graph_true_iff]
      exact ⟨a, b, hab, decide_eq_true (hTS (of_decide_eq_true ha)),
        decide_eq_true (hTS (of_decide_eq_true hb))⟩
    rw [hS] at hs
    contradiction
  apply small_support_safe_star_orientation G color hbip h4 (fun y => wv n C y (n + g))
    (fun y z hyz hy => wv_mono n C hAO.1 hAO.2.1 y z hyz (n + g) hy)
    (wmax G C g) T (fun v hv => (Finset.mem_filter.mp hv).2) hT hTg
  omega

end PEqualNP.Outside.L_meta_2583.ThinSupport

namespace PEqualNP.Outside.L_meta_2583.AndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma family_card_le_cone_signatures_multi {α : Type} [Fintype α]
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (W : Finset ℕ) (hW : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, ∀ w ∈ W, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → ∃ w ∈ W, wv n C (fun i => f a i || f b i) w = true) :
    Fintype.card α ≤ 2 ^ (R.filter (fun k => isAnd C k = true)).card := by
  classical
  let sig : α → ((R.filter (fun k => isAnd C k = true)) → Bool) :=
    fun a k => wv n C (f a) (opnd C k.val 0)
  have hinj : Function.Injective sig := by
    intro a b hab
    by_contra hne
    have heq : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
        wv n C (f a) (opnd C k 0) = wv n C (f b) (opnd C k 0) := by
      intro k hk hop
      have hkA : k ∈ R.filter (fun k => isAnd C k = true) :=
        Finset.mem_filter.mpr ⟨hk, by simp [isAnd, hop]⟩
      exact congrFun hab ⟨k, hkA⟩
    obtain ⟨w, hwW, ht⟩ := hjoin a b hne
    have hf := false_join_of_cone_signature_eq n C hAO R hRreal hRclosed
      (f a) (f b) heq w (hW w hwW) (hfalse a w hwW) (hfalse b w hwW)
    rw [ht] at hf
    cases hf
  have hcard := Fintype.card_le_of_injective sig hinj
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hcard

lemma cube_le_cone_and_count_multi (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset ℕ) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (W : Finset ℕ) (hW : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (d : ℕ) (f : (Fin d → Bool) → Fin n → Bool)
    (hfalse : ∀ a, ∀ w ∈ W, wv n C (f a) w = false)
    (hjoin : ∀ a b, a ≠ b → ∃ w ∈ W, wv n C (fun i => f a i || f b i) w = true) :
    d ≤ (R.filter (fun k => isAnd C k = true)).card := by
  have hc := family_card_le_cone_signatures_multi n C hAO R hRreal hRclosed W hW f hfalse hjoin
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

end PEqualNP.Outside.L_meta_2583.AndSignature

namespace PEqualNP.Outside.L_meta_2583.ProductivePair

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma productive_matching_le_cone_ands_multi {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (U : Finset Nat) (hU : ∀ w ∈ U, w < n ∨ w - n ∈ R)
    (hzero : ∀ w ∈ U, wv n C (fun _ => false) w = false)
    (W : Finset (Fin n))
    (hsafe : ∀ w ∈ U, ∀ v ∈ W, ∀ x,
      wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, ∃ w ∈ U,
      wv n C (setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  apply AndSignature.cube_le_cone_and_count_multi n C hAO R hRreal hRclosed U hU d
    (matchingChoiceInput endpt)
  · intro choice w hw
    exact matchingChoiceInput_false G (fun x => wv n C x w) (hzero w hw) W
      (hsafe w hw) hmatching endpt hinj hW hedge choice
  · intro choice other hne
    have hex : ∃ i, choice i ≠ other i := by
      by_contra hn
      push Not at hn
      exact hne (funext hn)
    obtain ⟨i, hi⟩ := hex
    obtain ⟨w, hw, hwt⟩ := haccept i
    refine ⟨w, hw, ?_⟩
    have hboth (b : Bool) :
        (matchingChoiceInput endpt choice (endpt i b) ||
          matchingChoiceInput endpt other (endpt i b)) = true := by
      have hc : choice i = b ∨ other i = b := by
        cases h1 : choice i <;> cases h2 : other i <;> cases b <;> simp_all
      rcases hc with hc | hc
      · have hv : matchingChoiceInput endpt choice (endpt i b) = true :=
          decide_eq_true ⟨i, by rw [hc]⟩
        simp [hv]
      · have hv : matchingChoiceInput endpt other (endpt i b) = true :=
          decide_eq_true ⟨i, by rw [hc]⟩
        simp [hv]
    apply wv_mono n C hAO.1 hAO.2.1 (setInput {endpt i true, endpt i false}) _ ?_ w hwt
    intro v hv
    have hm : v ∈ ({endpt i true, endpt i false} : Finset (Fin n)) := of_decide_eq_true hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hboth true
    · exact hboth false

lemma productive_matching_le_cone_junk_multi {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hRjunk : ∀ k ∈ R, AndSignature.isAnd C k = true → k ∈ junk G C)
    (U : Finset Nat) (hU : ∀ w ∈ U, w < n ∨ w - n ∈ R)
    (hzero : ∀ w ∈ U, wv n C (fun _ => false) w = false)
    (W : Finset (Fin n))
    (hsafe : ∀ w ∈ U, ∀ v ∈ W, ∀ x,
      wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, ∃ w ∈ U,
      wv n C (setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R ∩ junk G C).card := by
  have hcount := productive_matching_le_cone_ands_multi G C hAO R hRreal hRclosed
    U hU hzero W hsafe hmatching endpt hinj hW hedge haccept
  apply hcount.trans
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkR, hkA⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_inter.mpr ⟨hkR, hRjunk k hkR hkA⟩

end PEqualNP.Outside.L_meta_2583.ProductivePair

namespace PEqualNP.Outside.L_meta_2583.ProductivePair

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

def unionGateCone (n : Nat) (C : Circuit) (Roots : Finset Nat) : Finset Nat :=
  Roots.biUnion (gateCone n C)

lemma unionGateCone_real (n : Nat) (C : Circuit) (Roots : Finset Nat)
    (hRoots : ∀ g ∈ Roots, g < C.gates.length) :
    unionGateCone n C Roots ⊆ Finset.range C.gates.length := by
  intro k hk
  obtain ⟨g, hg, hkg⟩ := Finset.mem_biUnion.mp hk
  exact gateCone_real n C g (hRoots g hg) hkg

lemma unionGateCone_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (Roots : Finset Nat) (hRoots : ∀ g ∈ Roots, g < C.gates.length) :
    ∀ k ∈ unionGateCone n C Roots, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ unionGateCone n C Roots := by
  intro k hk b
  obtain ⟨g, hg, hkg⟩ := Finset.mem_biUnion.mp hk
  rcases gateCone_closed n C hAO g (hRoots g hg) k hkg b with hi | hi
  · exact Or.inl hi
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨g, hg, hi⟩)

lemma unionGateCone_ands_junk (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hTop : TopForm G C) (Roots : Finset Nat)
    (hRoots : ∀ g ∈ Roots, IsDirtyAnd n G C g) :
    ∀ k ∈ unionGateCone n C Roots, AndSignature.isAnd C k = true → k ∈ junk G C := by
  intro k hk hkA
  obtain ⟨g, hg, hkg⟩ := Finset.mem_biUnion.mp hk
  have hmem := gateCone_ands_subset_junk_prefix n G C hTop g (hRoots g hg)
    (Finset.mem_filter.mpr ⟨hkg, hkA⟩)
  exact (Finset.mem_inter.mp hmem).1

lemma productive_matching_le_union_dirty_cones {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (Roots : Finset Nat) (hRoots : ∀ g ∈ Roots, IsDirtyAnd n G C g)
    (W : Finset (Fin n)) (hsafe : ∀ g ∈ Roots, W ⊆ wmax G C g)
    (hmatching : ∀ v ∈ W, ∀ u ∈ W, ∀ z ∈ W,
      G.Adj v u → G.Adj v z → u = z)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, ∃ g ∈ Roots,
      gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (unionGateCone n C Roots ∩ junk G C).card := by
  have hreal : ∀ g ∈ Roots, g < C.gates.length := fun g hg => (hRoots g hg).2.1
  apply productive_matching_le_cone_junk_multi G C hAO (unionGateCone n C Roots)
    (unionGateCone_real n C Roots hreal) (unionGateCone_closed n C hAO Roots hreal)
    (unionGateCone_ands_junk n G C hTop Roots hRoots) (Roots.image (fun g => n + g))
    ?_ (fun w _ => ProductiveCircuit.wv_zero n C hAO w) W ?_ hmatching
    endpt hinj hW hedge ?_
  · intro w hw
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
    right
    simp only [Nat.add_sub_cancel_left]
    exact Finset.mem_biUnion.mpr ⟨g, hg, gateCone_self n C g⟩
  · intro w hw v hv x hx hxv
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp (hsafe g hg hv)).2 x hx hxv
  · intro i
    obtain ⟨g, hg, hgt⟩ := haccept i
    exact ⟨n + g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hgt⟩

lemma productive_matching_le_union_dirty_cones_of_pair {n d : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (Roots : Finset Nat) (hRoots : ∀ g ∈ Roots, IsDirtyAnd n G C g)
    (g₀ : Nat) (hg₀ : g₀ ∈ Roots) (a b : Fin n) (hnon : ¬G.Adj a b)
    (hpair : gateVal n C g₀ (setInput {a, b}) = true)
    (W : Finset (Fin n)) (hsafe : ∀ g ∈ Roots, W ⊆ wmax G C g)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hW : ∀ i b, endpt i b ∈ W)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, ∃ g ∈ Roots,
      gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (unionGateCone n C Roots ∩ junk G C).card := by
  apply productive_matching_le_union_dirty_cones G C hAO hTop Roots hRoots W hsafe
    ?_ endpt hinj hW hedge haccept
  intro v hv u hu z hz hvu hvz
  exact ProductiveCircuit.wmax_matching_of_false_pair n G color hbip h4 C hAO g₀
    a b hnon hpair v (hsafe g₀ hg₀ hv) u (hsafe g₀ hg₀ hu) z (hsafe g₀ hg₀ hz) hvu hvz

end PEqualNP.Outside.L_meta_2583.ProductivePair

namespace PEqualNP.Outside.L_meta_2583.ThetaAndSignature

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.AndSignature

def theta (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) ||
  (x 1 && x 5) || (x 1 && x 4) || (x 2 && x 6) ||
  (x 2 && x 4) || (x 3 && x 7) || (x 3 && x 4)

def masks : Fin 9 → Nat := ![15, 17, 44, 74, 104, 134, 164, 194, 240]

def family (a : Fin 9) (v : Fin 8) : Bool := (masks a).testBit v.val

theorem family_false : ∀ a : Fin 9, theta (family a) = false := by decide

theorem family_join_true : ∀ a b : Fin 9, a ≠ b →
    theta (fun i => family a i || family b i) = true := by decide

theorem and_lower (C : Circuit) (hAO : IsAO2 8 C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = theta x) :
    4 ≤ (andPrefix C C.gates.length).card := by
  let z : Fin 8 → Bool := fun i => family 0 i || family 1 i
  have hz : C.eval (List.ofFn z) = true := by
    rw [computes]
    exact family_join_true 0 1 (by decide)
  have hout : C.output < 8 + C.gates.length := by
    by_contra h
    have hlen : (C.wires (List.ofFn z)).length = 8 + C.gates.length := by
      rw [PEqualNP.Outside.L_meta_2583.SingleUse.wires_eq,
        PEqualNP.Outside.L_meta_2583.SingleUse.foldl_len, List.length_ofFn]
    have hf : C.eval (List.ofFn z) = false := by
      change (C.wires (List.ofFn z)).getD C.output false = false
      exact List.getD_eq_default _ _ (by omega)
    rw [hf] at hz
    contradiction
  have hcard := false_family_card_le_signatures 8 C hAO C.gates.length
    (le_refl _) C.output hout family
    (fun a => by
      change C.eval (List.ofFn (family a)) = false
      rw [computes, family_false])
    (fun a b hab => by
      change C.eval (List.ofFn (fun i => family a i || family b i)) = true
      rw [computes, family_join_true a b hab])
  simp only [Fintype.card_fin] at hcard
  by_contra h
  have hk : (andPrefix C C.gates.length).card ≤ 3 := by omega
  have hp : 2 ^ (andPrefix C C.gates.length).card ≤ 2 ^ 3 := by
    exact Nat.pow_le_pow_right (by decide) hk
  norm_num at hp
  omega

end PEqualNP.Outside.L_meta_2583.ThetaAndSignature

namespace PEqualNP.Outside.L_meta_2583.SharedPartner

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair

lemma partner_singleton_shadow_safe {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f partner : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → partner x = true → partner y = true)
    (hguard : ∀ x, f x = true → partner x = true → graphFun G ∅ x = true)
    (v : Fin n) (hv : partner (pairInput v v) = true) :
    ∀ x, f x = true → x v = true → graphFun G ∅ x = true := by
  intro x hfx hxv
  apply hguard x hfx
  apply hmono (pairInput v v) x ?_ hv
  intro i hi
  change decide (i = v ∨ i = v) = true at hi
  rcases of_decide_eq_true hi with rfl | rfl <;> exact hxv

def partnerShadow (n : Nat) (C : Circuit) (a : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun v => wv n C (pairInput v v) a = true)

lemma partnerShadow_subset_wmax {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (g a : Nat)
    (hguard : ∀ x, gateVal n C g x = true → wv n C x a = true → graphFun G ∅ x = true) :
    partnerShadow n C a ⊆ wmax G C g := by
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ v, ?_⟩
  exact partner_singleton_shadow_safe G (gateVal n C g) (fun x => wv n C x a)
    (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy a hx)
    hguard v (Finset.mem_filter.mp hv).2

lemma productive_shared_partner_le_union_junk_of_pair {n d : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (Roots : Finset Nat) (hRoots : ∀ g ∈ Roots, IsDirtyAnd n G C g)
    (a : Nat)
    (hguard : ∀ g ∈ Roots, ∀ x,
      gateVal n C g x = true → wv n C x a = true → graphFun G ∅ x = true)
    (g₀ : Nat) (hg₀ : g₀ ∈ Roots) (u v : Fin n) (hnon : ¬G.Adj u v)
    (hpair : gateVal n C g₀ (setInput {u, v}) = true)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hshadow : ∀ i b, wv n C (pairInput (endpt i b) (endpt i b)) a = true)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (haccept : ∀ i, ∃ g ∈ Roots,
      gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (unionGateCone n C Roots ∩ junk G C).card := by
  apply productive_matching_le_union_dirty_cones_of_pair G color hbip h4 C hAO hTop
    Roots hRoots g₀ hg₀ u v hnon hpair (partnerShadow n C a)
    (fun g hg => partnerShadow_subset_wmax G C hAO g a (hguard g hg))
    endpt hinj ?_ hedge haccept
  intro i b
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshadow i b⟩

end PEqualNP.Outside.L_meta_2583.SharedPartner

namespace PEqualNP.Outside.L_meta_2583.ProductiveCover

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ThinSupport

noncomputable def productiveCenters {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    Finset (Fin n) := by
  classical
  exact W.filter (fun p => color p = false ∧
    ∃ l ∈ W, G.Adj p l ∧ f (setInput {p, l}) = true)

lemma productiveCenters_subset {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool) (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    productiveCenters G color W f ⊆ W := by
  classical
  exact Finset.filter_subset _ _

lemma productiveCenters_cover {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (W : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → f (setInput {u, v}) = true →
      u ∈ productiveCenters G color W f ∨ v ∈ productiveCenters G color W f := by
  classical
  intro u hu v hv huv hf
  by_cases hc : color u = false
  · exact Or.inl (Finset.mem_filter.mpr ⟨hu, hc, v, hv, huv, hf⟩)
  · have hcv : color v = false := by
      have h := hbip u v huv
      cases h1 : color u <;> cases h2 : color v <;> simp_all
    exact Or.inr (Finset.mem_filter.mpr ⟨hv, hcv, u, hu, huv.symm,
      by simpa [Finset.pair_comm] using hf⟩)

lemma productiveCenters_card_le_cone_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hRjunk : ∀ k ∈ R, AndSignature.isAnd C k = true → k ∈ junk G C)
    (w : Nat) (hw : w < n ∨ w - n ∈ R)
    (hzero : wv n C (fun _ => false) w = false)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (hdegree : ∀ l ∈ W, color l = true → ∀ u ∈ W, ∀ v ∈ W,
      G.Adj l u → G.Adj l v → u = v) :
    (productiveCenters G color W (fun x => wv n C x w)).card ≤ (R ∩ junk G C).card := by
  classical
  let P := productiveCenters G color W (fun x => wv n C x w)
  let point : Fin P.card → Fin n := fun i => (P.equivFin.symm i).val
  have hmem (i : Fin P.card) : point i ∈ P := (P.equivFin.symm i).property
  have hpoint : Function.Injective point := by
    intro i j hij
    apply P.equivFin.symm.injective
    exact Subtype.ext hij
  have hdata (i : Fin P.card) : point i ∈ W ∧ color (point i) = false ∧
      ∃ l ∈ W, G.Adj (point i) l ∧ wv n C (setInput {point i, l}) w = true := by
    exact Finset.mem_filter.mp (hmem i)
  let line : Fin P.card → Fin n := fun i => (hdata i).2.2.choose
  have hline (i : Fin P.card) : line i ∈ W ∧ G.Adj (point i) (line i) ∧
      wv n C (setInput {point i, line i}) w = true := (hdata i).2.2.choose_spec
  have hPW : ∀ i, point i ∈ W := fun i => (hdata i).1
  have hLW : ∀ i, line i ∈ W := fun i => (hline i).1
  have hPC : ∀ i, color (point i) = false := fun i => (hdata i).2.1
  have hLC : ∀ i, color (line i) = true := by
    intro i
    have h := hbip (point i) (line i) (hline i).2.1
    have hp := hPC i
    cases hc : color (line i)
    · exact False.elim (h (hp.trans hc.symm))
    · rfl
  have hedge : ∀ i, G.Adj (point i) (line i) := fun i => (hline i).2.1
  have hsub := starEndpointSet_subset W point line hPW hLW
  apply ProductivePair.productive_matching_le_cone_junk G C hAO R hRreal hRclosed hRjunk
    w hw hzero (starEndpointSet point line)
    (fun v hv => hsafe v (hsub hv))
    (starEndpointSet_matching G color hbip W hdegree point line hpoint hPW hLW hPC hLC hedge)
    (starEndpoint point line)
    (starEndpoint_injective G color W hdegree point line hpoint hPW hLW hPC hLC hedge)
  · intro i b
    exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩
  · intro i
    change G.Adj (line i) (point i)
    exact (hedge i).symm
  · intro i
    change wv n C (setInput {line i, point i}) w = true
    rw [Finset.pair_comm]
    exact (hline i).2.2

end PEqualNP.Outside.L_meta_2583.ProductiveCover

namespace PEqualNP.Outside.L_meta_2583.ProductiveCover

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma productiveCenters_card_le_junk_prefix_of_degree
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hdegree : ∀ l ∈ wmax G C g, color l = true → ∀ u ∈ wmax G C g,
      ∀ v ∈ wmax G C g, G.Adj l u → G.Adj l v → u = v) :
    (productiveCenters G color (wmax G C g) (gateVal n C g)).card ≤
      (junk G C ∩ Finset.range (g + 1)).card := by
  have hRjunk : ∀ k ∈ gateCone n C g, AndSignature.isAnd C k = true → k ∈ junk G C := by
    intro k hk hka
    exact (Finset.mem_inter.mp (gateCone_ands_subset_junk_prefix n G C hTop g hg
      (Finset.mem_filter.mpr ⟨hk, hka⟩))).1
  have hcount := productiveCenters_card_le_cone_junk G color hbip C hAO
    (gateCone n C g) (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1)
    hRjunk (n + g) (Or.inr (by simpa using gateCone_self n C g))
    (ProductiveCircuit.wv_zero n C hAO (n + g)) (wmax G C g)
    (fun v hv => (Finset.mem_filter.mp hv).2) hdegree
  apply hcount.trans
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkR, hkj⟩ := Finset.mem_inter.mp hk
  exact Finset.mem_inter.mpr ⟨hkj, gateCone_prefix n C g hkR⟩

lemma exists_productive_cover_of_guard_degree
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hdegree : ∀ l ∈ wmax G C g, color l = true → ∀ u ∈ wmax G C g,
      ∀ v ∈ wmax G C g, G.Adj l u → G.Adj l v → u = v) :
    ∃ P : Finset (Fin n), P ⊆ wmax G C g ∧
      P.card ≤ (junk G C ∩ Finset.range (g + 1)).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g, G.Adj u v →
        gateVal n C g (setInput {u, v}) = true → u ∈ P ∨ v ∈ P := by
  refine ⟨productiveCenters G color (wmax G C g) (gateVal n C g),
    productiveCenters_subset G color _ _, ?_, ?_⟩
  · exact productiveCenters_card_le_junk_prefix_of_degree n G color hbip C hAO hTop g hg hdegree
  · exact productiveCenters_cover G color hbip _ _

lemma dirty_pair_productive_cover
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (a d : Fin n) (hnon : ¬ G.Adj a d) (hpair : gateVal n C g (setInput {a, d}) = true) :
    ∃ P : Finset (Fin n), P ⊆ wmax G C g ∧
      P.card ≤ (junk G C ∩ Finset.range (g + 1)).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g, G.Adj u v →
        gateVal n C g (setInput {u, v}) = true → u ∈ P ∨ v ∈ P := by
  have hW := ProductivePair.safe_guards_hit_pair G (gateVal n C g)
    (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy (n + g) hx)
    (wmax G C g) (fun v hv => (Finset.mem_filter.mp hv).2) a d hnon hpair
  have hm := ProductivePair.nonedge_neighbor_union_matching G color hbip h4 a d hnon
    (wmax G C g) hW
  exact exists_productive_cover_of_guard_degree n G color hbip C hAO hTop g hg
    (fun l hl _ => hm l hl)

lemma dirty_thin_productive_cover
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (T : Finset (Fin n)) (hT : graphFun G ∅ (setInput T) = false)
    (hf : gateVal n C g (setInput T) = true)
    (t : Fin n) (ht : t ∈ T) (hunique : ∀ v ∈ T, color v = true → v = t) :
    ∃ P : Finset (Fin n), P ⊆ wmax G C g ∧
      P.card ≤ (junk G C ∩ Finset.range (g + 1)).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g, G.Adj u v →
        gateVal n C g (setInput {u, v}) = true → u ∈ P ∨ v ∈ P := by
  have hd := ThinSupport.thin_support_guard_line_degree G color hbip h4 (gateVal n C g)
    (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy (n + g) hx)
    (wmax G C g) T (fun v hv => (Finset.mem_filter.mp hv).2) hT hf t ht hunique
  exact exists_productive_cover_of_guard_degree n G color hbip C hAO hTop g hg hd

lemma indicator_color_bipartite {n : Nat} (G : SimpleGraph (Fin n))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b) (c : Bool) :
    ∀ a b, G.Adj a b → decide (color a = c) ≠ decide (color b = c) := by
  intro a b hab
  have h := hbip a b hab
  cases ha : color a <;> cases hb : color b <;> cases c <;> simp_all

lemma dirty_small_junk_productive_cover
    (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (h4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hsmall : (junk G C ∩ Finset.range (g + 1)).card ≤ 2) :
    ∃ P : Finset (Fin n), P ⊆ wmax G C g ∧
      P.card ≤ (junk G C ∩ Finset.range (g + 1)).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g, G.Adj u v →
        gateVal n C g (setInput {u, v}) = true → u ∈ P ∨ v ∈ P := by
  classical
  obtain ⟨c, hc⟩ := ThinSupport.dirty_small_junk_wmax_star_orientation n G color hbip h4 C hAO
    g hg.2 hsmall
  let recolor : Fin n → Bool := fun v => decide (color v = c)
  have hbip' : ∀ a b, G.Adj a b → recolor a ≠ recolor b :=
    indicator_color_bipartite G color hbip c
  apply exists_productive_cover_of_guard_degree n G recolor hbip' C hAO hTop g hg
  intro l hl hcol u hu v hv hlu hlv
  have hcolor : color l = c := of_decide_eq_true hcol
  apply Finset.card_le_one.mp (hc l hl hcolor)
  · exact Finset.mem_filter.mpr ⟨hu, hlu⟩
  · exact Finset.mem_filter.mpr ⟨hv, hlv⟩

end PEqualNP.Outside.L_meta_2583.ProductiveCover

namespace PEqualNP.Outside.L_meta_2583.OneSidedMatching

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair
  PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma matchingChoiceInput_false_of_guard {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (endpt : Fin d → Bool → Fin n)
    (hguard : ∀ i, ∀ x, f x = true → x (endpt i true) = true → graphFun G ∅ x = true)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (choice : Fin d → Bool) (hne : choice ≠ fun _ => false) :
    f (matchingChoiceInput endpt choice) = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro hf
  have hex : ∃ i, choice i = true := by
    by_contra hn
    push Not at hn
    apply hne
    funext i
    exact Bool.eq_false_iff.mpr (hn i)
  obtain ⟨i, hi⟩ := hex
  have hv : matchingChoiceInput endpt choice (endpt i true) = true :=
    decide_eq_true ⟨i, by rw [hi]⟩
  have hG := hguard i _ hf hv
  have hgraph : ∃ a b, G.Adj a b ∧ matchingChoiceInput endpt choice a = true ∧
      matchingChoiceInput endpt choice b = true := by simpa [graphFun] using hG
  obtain ⟨a, b, hab, ha, hb⟩ := hgraph
  obtain ⟨j, rfl⟩ := of_decide_eq_true ha
  obtain ⟨k, rfl⟩ := of_decide_eq_true hb
  by_cases hjk : j = k
  · subst k
    exact G.irrefl hab
  · exact hcross j k hjk _ _ hab

lemma exponent_le_of_two_pow_sub_one_le (d a : Nat) (hd : 2 ≤ d)
    (h : 2 ^ d - 1 ≤ 2 ^ a) : d ≤ a := by
  by_contra hda
  have hpow : 2 ^ (a + 1) ≤ 2 ^ d :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
  have hfour : 2 ^ 2 ≤ 2 ^ d :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr hd
  have hpos : 0 < 2 ^ d := Nat.pow_pos (by decide)
  cases a with
  | zero => norm_num at h; norm_num at hfour; omega
  | succ a =>
    have htwo : 2 ^ 1 ≤ 2 ^ (a + 1) :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
    rw [Nat.pow_succ] at hpow
    norm_num at htwo
    omega

lemma one_sided_induced_matching_le_cone_ands {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : Nat) (hw : w < n ∨ w - n ∈ R) (hd : 2 ≤ d)
    (endpt : Fin d → Bool → Fin n)
    (hguard : ∀ i, ∀ x, wv n C x w = true → x (endpt i true) = true → graphFun G ∅ x = true)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  let choices : Finset (Fin d → Bool) := Finset.univ.erase (fun _ => false)
  have hcount := AndSignature.false_family_card_le_cone_signatures n C hAO R hRreal hRclosed
    w hw (fun choice : choices => matchingChoiceInput endpt choice.val)
    (fun choice => matchingChoiceInput_false_of_guard G (fun x => wv n C x w) endpt hguard hcross
      choice.val (Finset.mem_erase.mp choice.property).1)
    (by
      intro choice other hne
      apply matchingChoiceInput_join_true (fun x => wv n C x w)
        (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy w hx) endpt haccept
      intro heq
      exact hne (Subtype.ext heq))
  have hchoices : choices.card + 1 = 2 ^ d := by
    have heq := Finset.card_erase_add_one
      (Finset.mem_univ (fun _ : Fin d => false))
    simpa only [choices, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using heq
  simp only [Fintype.card_coe] at hcount
  apply exponent_le_of_two_pow_sub_one_le d _ hd
  omega

lemma one_sided_induced_matching_le_dirty_cone {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (endpt : Fin d → Bool → Fin n)
    (hguard : ∀ i, endpt i true ∈ wmax G C g)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (gateCone n C g ∩ junk G C).card := by
  by_cases hd : 2 ≤ d
  · have hc := one_sided_induced_matching_le_cone_ands G C hAO (gateCone n C g)
      (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1) (n + g)
      (Or.inr (by simpa only [Nat.add_sub_cancel_left] using gateCone_self n C g)) hd endpt
      (fun i => (Finset.mem_filter.mp (hguard i)).2) hcross haccept
    apply hc.trans
    apply Finset.card_le_card
    intro k hk
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hk).1,
      (Finset.mem_inter.mp (gateCone_ands_subset_junk_prefix n G C hTop g hg hk)).1⟩
  · have hmem : g ∈ gateCone n C g ∩ junk G C :=
      Finset.mem_inter.mpr ⟨gateCone_self n C g,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2.1, hg⟩⟩
    have hc : 0 < (gateCone n C g ∩ junk G C).card :=
      Finset.card_pos.mpr ⟨g, hmem⟩
    omega

end PEqualNP.Outside.L_meta_2583.OneSidedMatching

namespace PEqualNP.Outside.L_meta_2583.SingletonGuardMatching

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair

lemma singleton_acceptance_guards_adjacent {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (g : Nat)
    (x : Fin n) (hx : gateVal n C g (pairInput x x) = true) :
    ∀ v ∈ wmax G C g, G.Adj x v := by
  have heq : setInput ({x, x} : Finset (Fin n)) = pairInput x x := by
    funext v
    simp [setInput, pairInput]
  have hh := safe_guards_hit_pair G (gateVal n C g)
    (fun u v huv hu => wv_mono n C hAO.1 hAO.2.1 u v huv (n + g) hu)
    (wmax G C g) (fun v hv => (Finset.mem_filter.mp hv).2) x x G.irrefl
    (by rw [heq]; exact hx)
  intro v hv
  exact (hh v hv).elim id id

lemma adjacent_guards_matching_induced {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (x : Fin n) (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hstar : ∀ i, G.Adj x (endpt i true))
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (hleaf : ∀ i, endpt i false ≠ x) :
    ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c) := by
  have hgc : ∀ i, color (endpt i true) = !(color x) := by
    intro i
    have hn := hbip x (endpt i true) (hstar i)
    cases hx : color x <;> cases hi : color (endpt i true) <;> simp_all
  have hlc : ∀ i, color (endpt i false) = color x := by
    intro i
    have hn := hbip _ _ (hedge i)
    rw [hgc i] at hn
    cases hx : color x <;> cases hi : color (endpt i false) <;> simp_all
  have hcross : ∀ i j, i ≠ j → ¬G.Adj (endpt i true) (endpt j false) := by
    intro i j hij hadj
    have heq := Finset.card_le_one.mp (h4 x (endpt j false) (hleaf j).symm)
      (endpt i true) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar i, hadj.symm⟩)
      (endpt j true) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar j, (hedge j).symm⟩)
    have hp : (i, true) = (j, true) := hinj heq
    exact hij (congrArg Prod.fst hp)
  intro i j hij b c
  cases b <;> cases c
  · intro hadj
    exact hbip _ _ hadj (by rw [hlc i, hlc j])
  · intro hadj
    exact hcross j i (Ne.symm hij) hadj.symm
  · exact hcross i j hij
  · intro hadj
    exact hbip _ _ hadj (by rw [hgc i, hgc j])

lemma singleton_guard_matching_le_dirty_cone {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (h4 : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g) (x : Fin n)
    (hx : gateVal n C g (pairInput x x) = true)
    (endpt : Fin d → Bool → Fin n)
    (hinj : Function.Injective (fun ib : Fin d × Bool => endpt ib.1 ib.2))
    (hguard : ∀ i, endpt i true ∈ wmax G C g)
    (hedge : ∀ i, G.Adj (endpt i true) (endpt i false))
    (hleaf : ∀ i, endpt i false ≠ x)
    (haccept : ∀ i, gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (AncestorJunk.gateCone n C g ∩ junk G C).card := by
  apply OneSidedMatching.one_sided_induced_matching_le_dirty_cone G C hAO hTop g hg
    endpt hguard ?_ haccept
  exact adjacent_guards_matching_induced G color hbip h4 x endpt hinj
    (fun i => singleton_acceptance_guards_adjacent G C hAO g x hx _ (hguard i)) hedge hleaf

end PEqualNP.Outside.L_meta_2583.SingletonGuardMatching

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma minimal_support_restriction {n : Nat} (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (x : Fin n → Bool) (hx : ∀ v, x v = true → v ∈ T) :
    wv n C x w = true ↔ ∀ v ∈ T, x v = true := by
  classical
  constructor
  · intro hf
    let S : Finset (Fin n) := Finset.univ.filter (fun v => x v = true)
    have hS : S ⊆ T := by
      intro v hv
      exact hx v (Finset.mem_filter.mp hv).2
    have hSx : setInput S = x := by
      funext v
      cases hv : x v <;> simp [setInput, S, hv]
    have hTS := hmin S hS (by rw [hSx]; exact hf)
    intro v hv
    exact (Finset.mem_filter.mp (hTS hv)).2
  · intro hall
    exact wv_mono n C hAO.1 hAO.2.1 (setInput T) x
      (fun v hv => hall v (of_decide_eq_true hv)) w htrue

lemma picked_true_ands_subset (n : Nat) (C : Circuit) (x : Fin n → Bool) :
    ((Finset.range C.gates.length).filter (fun k => pickedBoth n C x k = true)) ⊆
      AndSignature.andPrefix C C.gates.length := by
  intro k hk
  obtain ⟨hkr, hb⟩ := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨hkr, ?_⟩
  cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hb ⊢

lemma tight_true_ands_eq_all (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ((Finset.range C.gates.length).filter (fun k => pickedBoth n C (setInput T) k = true)) =
      AndSignature.andPrefix C C.gates.length := by
  have hbound := minimal_support_card_le_true_ands n C hAO T w htrue hmin
  apply Finset.eq_of_subset_of_card_le (picked_true_ands_subset n C (setInput T))
  omega

lemma tight_all_ands_true (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true := by
  intro k hk hop
  have hm : k ∈ AndSignature.andPrefix C C.gates.length := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp [AndSignature.isAnd, hop]⟩
  rw [← tight_true_ands_eq_all n C hAO T w htrue hmin htight] at hm
  have hb := (Finset.mem_filter.mp hm).2
  simpa [pickedBoth, hop] using hb

lemma tight_all_ands_in_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (R : Finset Nat)
    (hR : ∀ k ∈ R, k < C.gates.length → ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hwR : w < n ∨ w - n ∈ R) :
    AndSignature.andPrefix C C.gates.length ⊆ R := by
  classical
  have hvalid : w < n + C.gates.length := by
    by_contra h
    rw [wv_missing n C (setInput T) w (by omega)] at htrue
    contradiction
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ R ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) R
      (fun k hk hkl => hR k hk hkl 0) (fun k hk hkl => hR k hk hkl 1) w hvalid hwR
  have hsub : B ⊆ AndSignature.andPrefix C C.gates.length := by
    intro k hk
    obtain ⟨hkr, _, hboth⟩ := Finset.mem_filter.mp hk
    exact picked_true_ands_subset n C (setInput T) (Finset.mem_filter.mpr ⟨hkr, hboth⟩)
  have hBeq : B = AndSignature.andPrefix C C.gates.length :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k hk
  rw [← hBeq] at hk
  exact (Finset.mem_filter.mp hk).2.1

lemma tight_all_ands_in_gateCone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    AndSignature.andPrefix C C.gates.length ⊆ AncestorJunk.gateCone n C g := by
  apply tight_all_ands_in_closed n C hAO T (n + g) htrue hmin htight
    (AncestorJunk.gateCone n C g)
  · intro k hk _ b
    exact AncestorJunk.gateCone_closed n C hAO g hg k hk b
  · exact Or.inr (by simpa using AncestorJunk.gateCone_self n C g)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma true_ands_false_wire_is_outside_or
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C) (T : Finset (Fin n))
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true) :
    ∀ w, wv n C (setInput T) w = false →
      ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
        ∀ x, wv n C x w = true ↔ ∃ i ∈ S, x i = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hnot : (⟨w, hwn⟩ : Fin n) ∉ T := by
        rw [wv_input n C (setInput T) w hwn] at hw
        simpa [setInput] using hw
      refine ⟨{⟨w, hwn⟩}, ?_, ?_⟩
      · intro i hi
        have heq : i = ⟨w, hwn⟩ := Finset.mem_singleton.mp hi
        simpa [heq] using hnot
      · intro x
        rw [wv_input n C x w hwn]
        simp
    by_cases hwg : n + C.gates.length ≤ w
    · refine ⟨∅, by simp, ?_⟩
      intro x
      rw [wv_missing n C x w hwg]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have ha := opnd_back n C hAO k hk 0
      have hb := opnd_back n C hAO k hk 1
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have ht := hactive k hk hop
        rw [hw] at ht
        contradiction
      · have hgate := wv_rec n C (setInput T) hAO.2.1 k hk
        rw [inputs_two n C hAO k hk] at hgate
        have hbits : wv n C (setInput T) (opnd C k 0) = false ∧
            wv n C (setInput T) (opnd C k 1) = false := by
          simpa [hop, GateOp.eval] using hgate.symm.trans hw
        obtain ⟨A, hAT, hA⟩ := ih _ ha hbits.1
        obtain ⟨B, hBT, hB⟩ := ih _ hb hbits.2
        refine ⟨A ∪ B, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact hAT i hi
          · exact hBT i hi
        · intro x
          rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp [hop, GateOp.eval, hA x, hB x, Finset.mem_union, or_and_right, exists_or]

lemma tight_false_wire_is_outside_or
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∀ v, wv n C (setInput T) v = false →
      ∃ S : Finset (Fin n), (∀ i ∈ S, i ∉ T) ∧
        ∀ x, wv n C x v = true ↔ ∃ i ∈ S, x i = true :=
  true_ands_false_wire_is_outside_or n C hAO T
    (tight_all_ands_true n C hAO T w htrue hmin htight)

lemma tight_implying_and_is_last
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (j : Nat) (hj : j < C.gates.length) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ S ⊆ T, wv n C (setInput S) (n + j) = true → wv n C (setInput S) w = true) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≤ j := by
  have hjtrue := tight_all_ands_true n C hAO T w htrue hmin htight j hj hja
  have hjmin : ∀ S ⊆ T, wv n C (setInput S) (n + j) = true → T ⊆ S := by
    intro S hS hSj
    exact hmin S hS (himplies S hS hSj)
  have hcone := tight_all_ands_in_gateCone n C hAO T j hj hjtrue hjmin htight
  intro k hk hka
  have hkA : k ∈ AndSignature.andPrefix C C.gates.length :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp [AndSignature.isAnd, hka]⟩
  have hkle := Finset.mem_range.mp (AncestorJunk.gateCone_prefix n C j (hcone hkA))
  omega

lemma tight_implying_and_unique
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (i j : Nat) (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hia : (gateAt C i).op = GateOp.and) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ S ⊆ T, wv n C (setInput S) (n + i) = true → wv n C (setInput S) w = true)
    (hjimplies : ∀ S ⊆ T, wv n C (setInput S) (n + j) = true → wv n C (setInput S) w = true) :
    i = j := by
  have hji := tight_implying_and_is_last n C hAO T w htrue hmin htight i hi hia himplies j hj hja
  have hij := tight_implying_and_is_last n C hAO T w htrue hmin htight j hj hja hjimplies i hi hia
  omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.OneSidedMatching

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair
  PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma matchingChoiceInput_join_some {n d : Nat} (C : Circuit) (hAO : IsAO2 n C)
    (U : Finset Nat) (endpt : Fin d → Bool → Fin n)
    (haccept : ∀ i, ∃ w ∈ U,
      wv n C (setInput {endpt i true, endpt i false}) w = true)
    (choice other : Fin d → Bool) (hne : choice ≠ other) :
    ∃ w ∈ U, wv n C (fun v => matchingChoiceInput endpt choice v ||
      matchingChoiceInput endpt other v) w = true := by
  classical
  have hex : ∃ i, choice i ≠ other i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨w, hw, hwt⟩ := haccept i
  refine ⟨w, hw, ?_⟩
  have hboth (b : Bool) :
      (matchingChoiceInput endpt choice (endpt i b) ||
        matchingChoiceInput endpt other (endpt i b)) = true := by
    have hc : choice i = b ∨ other i = b := by
      cases h1 : choice i <;> cases h2 : other i <;> cases b <;> simp_all
    rcases hc with hc | hc
    · have hv : matchingChoiceInput endpt choice (endpt i b) = true :=
        decide_eq_true ⟨i, by rw [hc]⟩
      simp [hv]
    · have hv : matchingChoiceInput endpt other (endpt i b) = true :=
        decide_eq_true ⟨i, by rw [hc]⟩
      simp [hv]
  apply wv_mono n C hAO.1 hAO.2.1 (setInput {endpt i true, endpt i false}) _ ?_ w hwt
  intro v hv
  have hm : v ∈ ({endpt i true, endpt i false} : Finset (Fin n)) := of_decide_eq_true hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact hboth true
  · exact hboth false

lemma one_sided_induced_matching_le_cone_ands_multi {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (U : Finset Nat) (hU : ∀ w ∈ U, w < n ∨ w - n ∈ R) (hd : 2 ≤ d)
    (endpt : Fin d → Bool → Fin n)
    (hguard : ∀ w ∈ U, ∀ i, ∀ x,
      wv n C x w = true → x (endpt i true) = true → graphFun G ∅ x = true)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, ∃ w ∈ U,
      wv n C (setInput {endpt i true, endpt i false}) w = true) :
    d ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  let choices : Finset (Fin d → Bool) := Finset.univ.erase (fun _ => false)
  have hcount := AndSignature.family_card_le_cone_signatures_multi n C hAO R hRreal hRclosed
    U hU (fun choice : choices => matchingChoiceInput endpt choice.val)
    (fun choice w hw => matchingChoiceInput_false_of_guard G (fun x => wv n C x w) endpt
      (hguard w hw) hcross choice.val (Finset.mem_erase.mp choice.property).1)
    (fun choice other hne => matchingChoiceInput_join_some C hAO U endpt haccept
      choice.val other.val (fun heq => hne (Subtype.ext heq)))
  have hchoices : choices.card + 1 = 2 ^ d := by
    have heq := Finset.card_erase_add_one (Finset.mem_univ (fun _ : Fin d => false))
    simpa only [choices, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using heq
  simp only [Fintype.card_coe] at hcount
  apply exponent_le_of_two_pow_sub_one_le d _ hd
  omega

lemma one_sided_induced_matching_le_union_dirty_cones {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (Roots : Finset Nat) (hRoots : ∀ g ∈ Roots, IsDirtyAnd n G C g)
    (endpt : Fin d → Bool → Fin n)
    (hguard : ∀ g ∈ Roots, ∀ i, endpt i true ∈ wmax G C g)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, ∃ g ∈ Roots,
      gateVal n C g (setInput {endpt i true, endpt i false}) = true) :
    d ≤ (unionGateCone n C Roots ∩ junk G C).card := by
  classical
  by_cases hd : 2 ≤ d
  · have hreal : ∀ g ∈ Roots, g < C.gates.length := fun g hg => (hRoots g hg).2.1
    have hcount := one_sided_induced_matching_le_cone_ands_multi G C hAO
      (unionGateCone n C Roots) (unionGateCone_real n C Roots hreal)
      (unionGateCone_closed n C hAO Roots hreal) (Roots.image (fun g => n + g))
      (by
        intro w hw
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
        right
        simp only [Nat.add_sub_cancel_left]
        exact Finset.mem_biUnion.mpr ⟨g, hg, gateCone_self n C g⟩) hd endpt
      (by
        intro w hw i x hx hxv
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp (hguard g hg i)).2 x hx hxv) hcross
      (by
        intro i
        obtain ⟨g, hg, hgt⟩ := haccept i
        exact ⟨n + g, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hgt⟩)
    apply hcount.trans
    apply Finset.card_le_card
    intro k hk
    obtain ⟨hkR, hkA⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_inter.mpr ⟨hkR, unionGateCone_ands_junk n G C hTop Roots hRoots k hkR hkA⟩
  · by_cases hz : d = 0
    · simp [hz]
    · obtain ⟨g, hg, _⟩ := haccept ⟨0, by omega⟩
      have hmem : g ∈ unionGateCone n C Roots ∩ junk G C :=
        Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hg, gateCone_self n C g⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hRoots g hg).2.1, hRoots g hg⟩⟩
      have hc := Finset.card_pos.mpr ⟨g, hmem⟩
      omega

end PEqualNP.Outside.L_meta_2583.OneSidedMatching

namespace PEqualNP.Outside.L_meta_2583.SafeProductCapacity

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair

lemma family_card_le_sum_cone_signatures {α : Type} [Fintype α]
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R S : Finset Nat)
    (hRreal : R ⊆ Finset.range C.gates.length)
    (hSreal : S ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (u v : Nat) (hu : u < n ∨ u - n ∈ R) (hv : v < n ∨ v - n ∈ S)
    (f : α → Fin n → Bool)
    (hfalse : ∀ a, wv n C (f a) u = false ∨ wv n C (f a) v = false)
    (hjoin : ∀ a b, a ≠ b →
      wv n C (fun i => f a i || f b i) u = true ∧
      wv n C (fun i => f a i || f b i) v = true) :
    Fintype.card α ≤ 2 ^ (R.filter (fun k => AndSignature.isAnd C k = true)).card +
      2 ^ (S.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  let U : Finset α := Finset.univ.filter (fun a => wv n C (f a) u = false)
  let V : Finset α := Finset.univ.filter (fun a => wv n C (f a) v = false)
  have hU := AndSignature.false_family_card_le_cone_signatures n C hAO R hRreal hRclosed
    u hu (fun a : U => f a.val)
    (fun a => (Finset.mem_filter.mp a.property).2)
    (fun a b hne => (hjoin a.val b.val (fun heq => hne (Subtype.ext heq))).1)
  have hV := AndSignature.false_family_card_le_cone_signatures n C hAO S hSreal hSclosed
    v hv (fun a : V => f a.val)
    (fun a => (Finset.mem_filter.mp a.property).2)
    (fun a b hne => (hjoin a.val b.val (fun heq => hne (Subtype.ext heq))).2)
  have hcover : Finset.univ ⊆ U ∪ V := by
    intro a _
    rcases hfalse a with ha | ha
    · exact Finset.mem_union_left V (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
    · exact Finset.mem_union_right U (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le U V)
  simp only [Finset.card_univ] at hc
  simp only [Fintype.card_coe] at hU hV
  omega

lemma induced_matching_product_capacity {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R S : Finset Nat)
    (hRreal : R ⊆ Finset.range C.gates.length)
    (hSreal : S ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (u v : Nat) (hu : u < n ∨ u - n ∈ R) (hv : v < n ∨ v - n ∈ S)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) u = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true) :
    2 ^ d ≤ 2 ^ (R.filter (fun k => AndSignature.isAnd C k = true)).card +
      2 ^ (S.filter (fun k => AndSignature.isAnd C k = true)).card := by
  have hc := family_card_le_sum_cone_signatures n C hAO R S hRreal hSreal hRclosed hSclosed
    u v hu hv (matchingChoiceInput endpt) ?_ ?_
  · simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hc
  · intro choice
    by_cases hleft : wv n C (matchingChoiceInput endpt choice) u = false
    · exact Or.inl hleft
    · right
      apply Bool.eq_false_iff.mpr
      intro hright
      have htrue : wv n C (matchingChoiceInput endpt choice) u = true := by
        cases hval : wv n C (matchingChoiceInput endpt choice) u <;> simp_all
      have hg := hsafe _ htrue hright
      have hgraph : ∃ a b, G.Adj a b ∧ matchingChoiceInput endpt choice a = true ∧
          matchingChoiceInput endpt choice b = true := by simpa [graphFun] using hg
      obtain ⟨a, b, hab, ha, hb⟩ := hgraph
      obtain ⟨i, rfl⟩ := of_decide_eq_true ha
      obtain ⟨j, rfl⟩ := of_decide_eq_true hb
      by_cases hij : i = j
      · subst j
        exact G.irrefl hab
      · exact hcross i j hij _ _ hab
  · intro choice other hne
    constructor
    · exact matchingChoiceInput_join_true (fun x => wv n C x u)
        (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy u hx)
        endpt (fun i => (haccept i).1) choice other hne
    · exact matchingChoiceInput_join_true (fun x => wv n C x v)
        (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy v hx)
        endpt (fun i => (haccept i).2) choice other hne

lemma exponent_le_of_sum_capacity (d a b A : Nat)
    (ha : a ≤ A) (hb : b < A) (h : 2 ^ d ≤ 2 ^ a + 2 ^ b) : d ≤ A := by
  by_contra hd
  have hlo : 2 ^ (A + 1) ≤ 2 ^ d :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
  have hpa : 2 ^ a ≤ 2 ^ A :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr ha
  have hpb : 2 ^ b < 2 ^ A :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hb
  rw [Nat.pow_succ] at hlo
  omega

lemma induced_matching_le_union_and_count {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R S : Finset Nat)
    (hRreal : R ⊆ Finset.range C.gates.length)
    (hSreal : S ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (u v : Nat) (hu : u < n ∨ u - n ∈ R) (hv : v < n ∨ v - n ∈ S)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) u = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true)
    (hexclusive : ∃ k ∈ R ∪ S, AndSignature.isAnd C k = true ∧ (k ∉ R ∨ k ∉ S)) :
    d ≤ ((R ∪ S).filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  let A := (R ∪ S).filter (fun k => AndSignature.isAnd C k = true)
  let RA := R.filter (fun k => AndSignature.isAnd C k = true)
  let SA := S.filter (fun k => AndSignature.isAnd C k = true)
  have hRsub : RA ⊆ A := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left S (Finset.mem_filter.mp hk).1,
      (Finset.mem_filter.mp hk).2⟩
  have hSsub : SA ⊆ A := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right R (Finset.mem_filter.mp hk).1,
      (Finset.mem_filter.mp hk).2⟩
  have hcap := induced_matching_product_capacity G C hAO R S hRreal hSreal hRclosed hSclosed
    u v hu hv hsafe endpt hcross haccept
  obtain ⟨k, hk, hkAnd, hmiss⟩ := hexclusive
  have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hk, hkAnd⟩
  rcases hmiss with hmiss | hmiss
  · have hstrict : RA ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hRsub, ?_⟩
      intro heq
      have hmem : k ∈ RA := heq.symm ▸ hkA
      exact hmiss (Finset.mem_filter.mp hmem).1
    apply exponent_le_of_sum_capacity d SA.card RA.card A.card (Finset.card_le_card hSsub)
      (Finset.card_lt_card hstrict)
    simpa only [Nat.add_comm] using hcap
  · have hstrict : SA ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hSsub, ?_⟩
      intro heq
      have hmem : k ∈ SA := heq.symm ▸ hkA
      exact hmiss (Finset.mem_filter.mp hmem).1
    exact exponent_le_of_sum_capacity d RA.card SA.card A.card (Finset.card_le_card hRsub)
      (Finset.card_lt_card hstrict) hcap

lemma induced_matching_le_one_of_no_cone_ands {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (R S : Finset Nat)
    (hRreal : R ⊆ Finset.range C.gates.length)
    (hSreal : S ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (u v : Nat) (hu : u < n ∨ u - n ∈ R) (hv : v < n ∨ v - n ∈ S)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) u = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true)
    (hno : ∀ k ∈ R ∪ S, AndSignature.isAnd C k = false) : d ≤ 1 := by
  classical
  have hcap := induced_matching_product_capacity G C hAO R S hRreal hSreal hRclosed hSclosed
    u v hu hv hsafe endpt hcross haccept
  have hR : R.filter (fun k => AndSignature.isAnd C k = true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hm := Finset.mem_filter.mp hk
    have hf := hno k (Finset.mem_union_left S hm.1)
    simp [hf] at hm
  have hS : S.filter (fun k => AndSignature.isAnd C k = true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hm := Finset.mem_filter.mp hk
    have hf := hno k (Finset.mem_union_right R hm.1)
    simp [hf] at hm
  rw [hR, hS] at hcap
  have hh : 2 ^ d ≤ 2 ^ 1 := by simpa using hcap
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh

end PEqualNP.Outside.L_meta_2583.SafeProductCapacity

namespace PEqualNP.Outside.L_meta_2583.SafeProductTopology

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit
  PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma gateCone_mono (n : Nat) (C : Circuit) (k j : Nat) (hk : k ∈ gateCone n C j) :
    gateCone n C k ⊆ gateCone n C j := by
  intro i hi
  rcases (mem_gateCone n C j k).mp hk with rfl | hkj
  · exact hi
  · apply (mem_gateCone n C j i).mpr
    right
    rcases (mem_gateCone n C k i).mp hi with rfl | hik
    · exact hkj
    · exact TopNormal.inCone_trans n C i k hik j hkj

lemma max_and_forces_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C) (g : Nat) :
    ∀ k, k < C.gates.length → g ∈ gateCone n C k →
      (∀ j ∈ gateCone n C k, (gateAt C j).op = GateOp.and → j ≤ g) →
      ∀ x, gateVal n C g x = true → gateVal n C k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hg hmax x hx
    rcases (mem_gateCone n C k g).mp hg with heq | hanc
    · simpa only [heq] using hx
    · have hgk := (TopNormal.inCone_lt n C g k hanc).1
      rcases hAO.1 _ (gate_mem C k hk) with hand | hor
      · have := hmax k (gateCone_self n C k) hand
        omega
      · obtain ⟨_, j, hjk, hjin, hgj⟩ := (TopNormal.inCone_iff n C g k).mp hanc
        have hjcone : j ∈ gateCone n C k := by
          apply (mem_gateCone n C k j).mpr
          right
          exact (TopNormal.inCone_iff n C j k).mpr ⟨hk, j, hjk, hjin, Or.inl rfl⟩
        have hchild : gateVal n C j x = true :=
          ih j hjk (lt_trans hjk hk) ((mem_gateCone n C j g).mpr hgj)
            (fun l hl => hmax l (gateCone_mono n C j k hjcone hl)) x hx
        change wv n C x (n + k) = true
        rw [wv_rec n C x hAO.2.1 k hk, hor]
        change ((gateAt C k).inputs.map (wv n C x)).any id = true
        exact List.any_eq_true.mpr
          ⟨wv n C x (n + j), List.mem_map_of_mem hjin, hchild⟩

def wireCone (n : Nat) (C : Circuit) (w : Nat) : Finset Nat :=
  if w < n then ∅ else gateCone n C (w - n)

lemma wireCone_real (n : Nat) (C : Circuit) (w : Nat) (hw : w < n + C.gates.length) :
    wireCone n C w ⊆ Finset.range C.gates.length := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · simpa only [wireCone, ite_eq_right hwn] using
      gateCone_real n C (w - n) (by omega)

lemma wireCone_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (w : Nat) (hw : w < n + C.gates.length) :
    ∀ k ∈ wireCone n C w, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ wireCone n C w := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · simpa only [wireCone, ite_eq_right hwn] using
      gateCone_closed n C hAO (w - n) (by omega)

lemma wireCone_root (n : Nat) (C : Circuit) (w : Nat) :
    w < n ∨ w - n ∈ wireCone n C w := by
  by_cases hwn : w < n
  · exact Or.inl hwn
  · exact Or.inr (by simpa only [wireCone, ite_eq_right hwn] using gateCone_self n C (w - n))

lemma max_and_forces_wire (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (g w : Nat) (hw : w < n + C.gates.length) (hg : g ∈ wireCone n C w)
    (hmax : ∀ j ∈ wireCone n C w, (gateAt C j).op = GateOp.and → j ≤ g)
    (x : Fin n → Bool) (hx : gateVal n C g x = true) : wv n C x w = true := by
  by_cases hwn : w < n
  · simp [wireCone, hwn] at hg
  · have heq : n + (w - n) = w := by omega
    have ht := max_and_forces_gate n C hAO g (w - n) (by omega)
      (by simpa only [wireCone, ite_eq_right hwn] using hg)
      (by simpa only [wireCone, ite_eq_right hwn] using hmax) x hx
    change wv n C x (n + (w - n)) = true at ht
    exact heq ▸ ht

lemma maximal_dirty_and_not_shared {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (u v : Nat) (hu : u < n + C.gates.length) (hv : v < n + C.gates.length)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hmax : ∀ j ∈ wireCone n C u ∪ wireCone n C v,
      (gateAt C j).op = GateOp.and → j ≤ g) :
    ¬(g ∈ wireCone n C u ∧ g ∈ wireCone n C v) := by
  rintro ⟨hgu, hgv⟩
  obtain ⟨x, hx, hfalse⟩ := hg.2.2
  have hxu := max_and_forces_wire n C hAO g u hu hgu
    (fun j hj => hmax j (Finset.mem_union_left _ hj)) x hx
  have hxv := max_and_forces_wire n C hAO g v hv hgv
    (fun j hj => hmax j (Finset.mem_union_right _ hj)) x hx
  have ht := hsafe x hxu hxv
  rw [hfalse] at ht
  cases ht


lemma exists_exclusive_and_of_nonempty {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (u v : Nat) (hu : u < n + C.gates.length) (hv : v < n + C.gates.length)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (hdirty : ∀ k ∈ wireCone n C u ∪ wireCone n C v,
      AndSignature.isAnd C k = true → IsDirtyAnd n G C k)
    (hA : ((wireCone n C u ∪ wireCone n C v).filter
      (fun k => AndSignature.isAnd C k = true)).Nonempty) :
    ∃ k ∈ wireCone n C u ∪ wireCone n C v,
      AndSignature.isAnd C k = true ∧ (k ∉ wireCone n C u ∨ k ∉ wireCone n C v) := by
  classical
  let A := (wireCone n C u ∪ wireCone n C v).filter (fun k => AndSignature.isAnd C k = true)
  let g := A.max' hA
  have hgA : g ∈ A := Finset.max'_mem A hA
  obtain ⟨hgR, hgAnd⟩ := Finset.mem_filter.mp hgA
  refine ⟨g, hgR, hgAnd, ?_⟩
  have hnot := maximal_dirty_and_not_shared G C hAO u v hu hv hsafe g
    (hdirty g hgR hgAnd) (fun j hj hop => by
      apply Finset.le_max' A j
      exact Finset.mem_filter.mpr ⟨hj, by simp [AndSignature.isAnd, hop]⟩)
  tauto

end PEqualNP.Outside.L_meta_2583.SafeProductTopology

namespace PEqualNP.Outside.L_meta_2583.SafeProductCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.ProductivePair
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductCapacity
  PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma safe_product_induced_matching_le_union_junk {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (u v : Nat) (hu : u < n + C.gates.length) (hv : v < n + C.gates.length)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (hdirty : ∀ k ∈ wireCone n C u ∪ wireCone n C v,
      AndSignature.isAnd C k = true → IsDirtyAnd n G C k)
    (hA : ((wireCone n C u ∪ wireCone n C v).filter
      (fun k => AndSignature.isAnd C k = true)).Nonempty)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) u = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true) :
    d ≤ ((wireCone n C u ∪ wireCone n C v) ∩ junk G C).card := by
  have hcount := induced_matching_le_union_and_count G C hAO
    (wireCone n C u) (wireCone n C v) (wireCone_real n C u hu) (wireCone_real n C v hv)
    (wireCone_closed n C hAO u hu) (wireCone_closed n C hAO v hv)
    u v (wireCone_root n C u) (wireCone_root n C v) hsafe endpt hcross haccept
    (exists_exclusive_and_of_nonempty G C hAO u v hu hv hsafe hdirty hA)
  apply hcount.trans
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkR, hkA⟩ := Finset.mem_filter.mp hk
  have hd := hdirty k hkR hkA
  exact Finset.mem_inter.mpr ⟨hkR, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hd.2.1, hd⟩⟩

lemma safe_product_induced_matching_le_max_union_junk {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (u v : Nat) (hu : u < n + C.gates.length) (hv : v < n + C.gates.length)
    (hsafe : ∀ x, wv n C x u = true → wv n C x v = true → graphFun G ∅ x = true)
    (hdirty : ∀ k ∈ wireCone n C u ∪ wireCone n C v,
      AndSignature.isAnd C k = true → IsDirtyAnd n G C k)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, wv n C (setInput {endpt i true, endpt i false}) u = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true) :
    d ≤ max 1 ((wireCone n C u ∪ wireCone n C v) ∩ junk G C).card := by
  classical
  by_cases hA : ((wireCone n C u ∪ wireCone n C v).filter
      (fun k => AndSignature.isAnd C k = true)).Nonempty
  · exact (safe_product_induced_matching_le_union_junk G C hAO u v hu hv hsafe hdirty hA
      endpt hcross haccept).trans (Nat.le_max_right _ _)
  · have hno : ∀ k ∈ wireCone n C u ∪ wireCone n C v, AndSignature.isAnd C k = false := by
      intro k hk
      apply Bool.eq_false_iff.mpr
      intro hkt
      exact hA ⟨k, Finset.mem_filter.mpr ⟨hk, hkt⟩⟩
    have hc := induced_matching_le_one_of_no_cone_ands G C hAO
      (wireCone n C u) (wireCone n C v) (wireCone_real n C u hu) (wireCone_real n C v hv)
      (wireCone_closed n C hAO u hu) (wireCone_closed n C hAO v hv)
      u v (wireCone_root n C u) (wireCone_root n C v) hsafe endpt hcross haccept hno
    exact hc.trans (Nat.le_max_left _ _)

lemma dirty_gate_safe_product_induced_matching_le_union_junk {n d : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g) (v : Nat) (hv : v < n + C.gates.length)
    (hvdirty : ∀ k ∈ wireCone n C v, AndSignature.isAnd C k = true → IsDirtyAnd n G C k)
    (hsafe : ∀ x, gateVal n C g x = true → wv n C x v = true → graphFun G ∅ x = true)
    (endpt : Fin d → Bool → Fin n)
    (hcross : ∀ i j, i ≠ j → ∀ b c, ¬G.Adj (endpt i b) (endpt j c))
    (haccept : ∀ i, gateVal n C g (setInput {endpt i true, endpt i false}) = true ∧
      wv n C (setInput {endpt i true, endpt i false}) v = true) :
    d ≤ ((gateCone n C g ∪ wireCone n C v) ∩ junk G C).card := by
  have hcone : wireCone n C (n + g) = gateCone n C g := by
    simp [wireCone]
  have hdirty : ∀ k ∈ wireCone n C (n + g) ∪ wireCone n C v,
      AndSignature.isAnd C k = true → IsDirtyAnd n G C k := by
    intro k hk hkA
    rcases Finset.mem_union.mp hk with hk | hk
    · rw [hcone] at hk
      have hm := gateCone_ands_subset_junk_prefix n G C hTop g hg
        (Finset.mem_filter.mpr ⟨hk, hkA⟩)
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hm).1).2
    · exact hvdirty k hk hkA
  have hA : ((wireCone n C (n + g) ∪ wireCone n C v).filter
      (fun k => AndSignature.isAnd C k = true)).Nonempty := by
    refine ⟨g, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_union_left
      rw [hcone]
      exact gateCone_self n C g
    · simp [AndSignature.isAnd, hg.1]
  have hc := safe_product_induced_matching_le_union_junk G C hAO (n + g) v
    (by have hreal := hg.2.1; omega) hv hsafe hdirty hA endpt hcross haccept
  simpa only [hcone] using hc

end PEqualNP.Outside.L_meta_2583.SafeProductCircuit

namespace PEqualNP.Outside.L_meta_2583.TPreservingSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma fullSupport_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (k : Nat) (hk : k < C.gates.length) :
    fullSupport n C hAO (n + k) = fullSupport n C hAO (opnd C k 0) ∪
      fullSupport n C hAO (opnd C k 1) := by
  exact pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

lemma selectedSupport_gate (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (left : Nat → Bool) (k : Nat) (hk : k < C.gates.length) :
    selectedSupport n C hAO left (n + k) =
      if andSelector C k then selectedSupport n C hAO left (opnd C k 0) ∪
        selectedSupport n C hAO left (opnd C k 1)
      else if left k then selectedSupport n C hAO left (opnd C k 0)
      else selectedSupport n C hAO left (opnd C k 1) :=
  pickedSupport_gate _ _ _ _ _ _ _ _ _ hk

lemma fullSupport_true_of_active_ands (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, p ∈ fullSupport n C hAO w → wv n C (setInput T) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hpw
    by_cases hwn : w < n
    · have heq : fullSupport n C hAO w = {⟨w, hwn⟩} :=
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn
      have hpw' := Finset.mem_singleton.mp (heq ▸ hpw)
      rw [wv_input n C (setInput T) w hwn]
      exact decide_eq_true (hpw' ▸ hp)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · exact hactive k hk hop
      · rw [fullSupport_gate n C hAO k hk] at hpw
        rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk]
        rcases Finset.mem_union.mp hpw with hl | hr
        · have ht := ih _ (opnd_back n C hAO k hk 0) hl
          simp [hop, GateOp.eval, ht]
        · have ht := ih _ (opnd_back n C hAO k hk 1) hr
          simp [hop, GateOp.eval, ht]
    · have heq : fullSupport n C hAO w = ∅ := by
        unfold fullSupport
        rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg]
      exact False.elim (Finset.notMem_empty _ (heq ▸ hpw))

def preferredLeft (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (p : Fin n) (k : Nat) : Bool :=
  if p ∈ fullSupport n C hAO (opnd C k 0) then true
  else if p ∈ fullSupport n C hAO (opnd C k 1) then false
  else wv n C (setInput T) (opnd C k 0)

lemma preferredSupport_contains (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (p : Fin n) :
    ∀ w, p ∈ fullSupport n C hAO w →
      p ∈ selectedSupport n C hAO (preferredLeft n C hAO T p) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hpw
    by_cases hwn : w < n
    · simpa only [show fullSupport n C hAO w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn,
        show selectedSupport n C hAO (preferredLeft n C hAO T p) w = {⟨w, hwn⟩} from
          pickedSupport_input _ _ _ _ _ _ _ _ _ hwn] using hpw
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [fullSupport_gate n C hAO k hk] at hpw
      rw [selectedSupport_gate n C hAO _ k hk]
      by_cases hb : andSelector C k = true
      · rw [ite_eq_left hb]
        rcases Finset.mem_union.mp hpw with hl | hr
        · exact Finset.mem_union_left _ (ih _ (opnd_back n C hAO k hk 0) hl)
        · exact Finset.mem_union_right _ (ih _ (opnd_back n C hAO k hk 1) hr)
      · rw [ite_eq_right hb]
        by_cases hl : p ∈ fullSupport n C hAO (opnd C k 0)
        · simp only [preferredLeft, ite_eq_left hl, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 0) hl
        · have hr := (Finset.mem_union.mp hpw).resolve_left hl
          simp only [preferredLeft, ite_eq_right hl, ite_eq_left hr, Bool.false_eq_true, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 1) hr
    · have heq : fullSupport n C hAO w = ∅ := by
        unfold fullSupport
        rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg]
      exact False.elim (Finset.notMem_empty _ (heq ▸ hpw))

lemma preferredSupport_subset (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, wv n C (setInput T) w = true →
      selectedSupport n C hAO (preferredLeft n C hAO T p) w ⊆ T := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [show selectedSupport n C hAO (preferredLeft n C hAO T p) w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      rw [wv_input n C (setInput T) w hwn] at hw
      exact Finset.singleton_subset_iff.mpr (of_decide_eq_true hw)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk] at hw
      rw [selectedSupport_gate n C hAO _ k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hb : andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_left hb]
        have hbits : wv n C (setInput T) (opnd C k 0) = true ∧
            wv n C (setInput T) (opnd C k 1) = true := by simpa [hop, GateOp.eval] using hw
        exact Finset.union_subset (ih _ (opnd_back n C hAO k hk 0) hbits.1)
          (ih _ (opnd_back n C hAO k hk 1) hbits.2)
      · have hb : ¬andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_right hb]
        by_cases hl : p ∈ fullSupport n C hAO (opnd C k 0)
        · simp only [preferredLeft, ite_eq_left hl, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 0)
            (fullSupport_true_of_active_ands n C hAO T hactive p hp _ hl)
        · by_cases hr : p ∈ fullSupport n C hAO (opnd C k 1)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_left hr, Bool.false_eq_true, ↓reduceIte]
            exact ih _ (opnd_back n C hAO k hk 1)
              (fullSupport_true_of_active_ands n C hAO T hactive p hp _ hr)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_right hr]
            by_cases hv0 : wv n C (setInput T) (opnd C k 0) = true
            · rw [ite_eq_left hv0]
              exact ih _ (opnd_back n C hAO k hk 0) hv0
            · rw [ite_eq_right hv0]
              have hv1 : wv n C (setInput T) (opnd C k 1) = true := by
                simpa [hop, GateOp.eval, hv0] using hw
              exact ih _ (opnd_back n C hAO k hk 1) hv1
    · rw [wv_missing n C (setInput T) w (by omega)] at hw
      cases hw

lemma shared_roots_support_within_T (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (r : Nat) (hr : r ≤ C.gates.length) (W : Finset Nat)
    (hvalid : ∀ w ∈ W, w < n + r)
    (htrue : ∀ w ∈ W, wv n C (setInput T) w = true)
    (p : Fin n) (hp : p ∈ T) (hfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ (∀ w ∈ W, wv n C (setInput S) w = true) ∧
      S.card ≤ (AndSignature.andPrefix C r).card + 1 := by
  let left := preferredLeft n C hAO T p
  let S := W.biUnion (selectedSupport n C hAO left)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    exact preferredSupport_subset n C hAO T hactive p hp w (htrue w hw) hiw
  · intro w hw
    have hv : w < n + C.gates.length := by have := hvalid w hw; omega
    have hs := selectedSupport_sound n C hAO left w hv
    exact wv_mono n C hAO.1 hAO.2.1
      (setInput (selectedSupport n C hAO left w)) (setInput S)
      (fun i hi => decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hw, of_decide_eq_true hi⟩)) w hs
  · have hb := SharedSupport.pickedSupport_family_anchor_prefix n C.gates.length
      (fun k => opnd C k 0) (fun k => opnd C k 1) (andSelector C) left
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) r hr W hvalid p
      (fun w hw => preferredSupport_contains n C hAO T p w (hfull w hw))
    exact hb

end PEqualNP.Outside.L_meta_2583.TPreservingSupport

namespace PEqualNP.Outside.L_meta_2583.TPreservingSupport

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma fullSupport_true_of_active_ands_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, (w < n ∨ w - n ∈ R) → p ∈ fullSupport n C hAO w → wv n C (setInput T) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR hpw
    by_cases hwn : w < n
    · have heq : fullSupport n C hAO w = {⟨w, hwn⟩} :=
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn
      have hpw' := Finset.mem_singleton.mp (heq ▸ hpw)
      rw [wv_input n C (setInput T) w hwn]
      exact decide_eq_true (hpw' ▸ hp)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · exact hactive k hkR hop
      · rw [fullSupport_gate n C hAO k hk] at hpw
        rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk]
        rcases Finset.mem_union.mp hpw with hl | hr
        · have ht := ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hl
          simp [hop, GateOp.eval, ht]
        · have ht := ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hr
          simp [hop, GateOp.eval, ht]
    · have heq : fullSupport n C hAO w = ∅ := by
        unfold fullSupport
        rw [pickedSupport, dite_eq_right hwn, dite_eq_right hwg]
      exact False.elim (Finset.notMem_empty _ (heq ▸ hpw))

lemma preferredSupport_subset_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n))
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (p : Fin n) (hp : p ∈ T) :
    ∀ w, (w < n ∨ w - n ∈ R) → wv n C (setInput T) w = true →
      selectedSupport n C hAO (preferredLeft n C hAO T p) w ⊆ T := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR hw
    by_cases hwn : w < n
    · rw [show selectedSupport n C hAO (preferredLeft n C hAO T p) w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      rw [wv_input n C (setInput T) w hwn] at hw
      exact Finset.singleton_subset_iff.mpr (of_decide_eq_true hw)
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk] at hw
      rw [selectedSupport_gate n C hAO _ k hk]
      rcases hAO.1 _ (gate_mem C k hk) with hop | hop
      · have hb : andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_left hb]
        have hbits : wv n C (setInput T) (opnd C k 0) = true ∧
            wv n C (setInput T) (opnd C k 1) = true := by simpa [hop, GateOp.eval] using hw
        exact Finset.union_subset (ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hbits.1)
          (ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hbits.2)
      · have hb : ¬andSelector C k = true := by simp [andSelector, hop]
        rw [ite_eq_right hb]
        by_cases hl : p ∈ fullSupport n C hAO (opnd C k 0)
        · simp only [preferredLeft, ite_eq_left hl, ↓reduceIte]
          exact ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0)
            (fullSupport_true_of_active_ands_closed n C hAO T R hRclosed hactive p hp _ (hRclosed k hkR 0) hl)
        · by_cases hr : p ∈ fullSupport n C hAO (opnd C k 1)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_left hr, Bool.false_eq_true, ↓reduceIte]
            exact ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1)
              (fullSupport_true_of_active_ands_closed n C hAO T R hRclosed hactive p hp _ (hRclosed k hkR 1) hr)
          · simp only [preferredLeft, ite_eq_right hl, ite_eq_right hr]
            by_cases hv0 : wv n C (setInput T) (opnd C k 0) = true
            · rw [ite_eq_left hv0]
              exact ih _ (opnd_back n C hAO k hk 0) (hRclosed k hkR 0) hv0
            · rw [ite_eq_right hv0]
              have hv1 : wv n C (setInput T) (opnd C k 1) = true := by
                simpa [hop, GateOp.eval, hv0] using hw
              exact ih _ (opnd_back n C hAO k hk 1) (hRclosed k hkR 1) hv1
    · rw [wv_missing n C (setInput T) w (by omega)] at hw
      cases hw


lemma shared_roots_support_within_T_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (hactive : ∀ k ∈ R, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true)
    (W : Finset Nat) (hW : ∀ w ∈ W, w < n ∨ w - n ∈ R)
    (htrue : ∀ w ∈ W, wv n C (setInput T) w = true)
    (p : Fin n) (hp : p ∈ T) (hfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w) :
    ∃ S : Finset (Fin n), S ⊆ T ∧ (∀ w ∈ W, wv n C (setInput S) w = true) ∧
      S.card ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1 := by
  let left := preferredLeft n C hAO T p
  let s := selectedSupport n C hAO left
  let S := W.biUnion s
  have hvalid : ∀ w ∈ W, w < n + C.gates.length := by
    intro w hw
    rcases hW w hw with hi | hi
    · omega
    · have := Finset.mem_range.mp (hRreal hi)
      omega
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    exact preferredSupport_subset_closed n C hAO T R hRclosed hactive p hp w
      (hW w hw) (htrue w hw) hiw
  · intro w hw
    have hs := selectedSupport_sound n C hAO left w (hvalid w hw)
    exact wv_mono n C hAO.1 hAO.2.1 (setInput (s w)) (setInput S)
      (fun i hi => decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hw, of_decide_eq_true hi⟩)) w hs
  · let parents : Nat → Finset Nat := fun k =>
      if andSelector C k then {opnd C k 0, opnd C k 1}
      else if left k then {opnd C k 0} else {opnd C k 1}
    let cost : Nat → Nat := fun k => if andSelector C k then 1 else 0
    have hi : ∀ i < n, (s i).card ≤ 1 := by
      intro i hi
      have heq : s i = {⟨i, hi⟩} := pickedSupport_input _ _ _ _ _ _ _ _ _ hi
      rw [heq]
      simp
    have hb : ∀ k < C.gates.length, parents k ⊆ Finset.range (n + k) := by
      intro k hk j hj
      simp only [parents] at hj
      split_ifs at hj with h1 h2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact Finset.mem_range.mpr (opnd_back n C hAO k hk 0)
        · exact Finset.mem_range.mpr (opnd_back n C hAO k hk 1)
      · rw [Finset.mem_singleton] at hj
        subst j
        exact Finset.mem_range.mpr (opnd_back n C hAO k hk 0)
      · rw [Finset.mem_singleton] at hj
        subst j
        exact Finset.mem_range.mpr (opnd_back n C hAO k hk 1)
    have hc : ∀ k < C.gates.length, (parents k).card ≤ cost k + 1 := by
      intro k _
      simp only [parents, cost]
      split_ifs <;> first | exact Finset.card_le_two | simp
    have hv : ∀ k < C.gates.length, s (n + k) ⊆ (parents k).biUnion s := by
      intro k hk
      change selectedSupport n C hAO left (n + k) ⊆ _
      rw [selectedSupport_gate n C hAO left k hk]
      simp only [parents]
      split_ifs <;> simp [s]
    have hRc : ∀ k ∈ R, k < C.gates.length → ∀ j ∈ parents k, j < n ∨ j - n ∈ R := by
      intro k hk _ j hj
      simp only [parents] at hj
      split_ifs at hj with h1 h2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact hRclosed k hk 0
        · exact hRclosed k hk 1
      · rw [Finset.mem_singleton] at hj
        subst j
        exact hRclosed k hk 0
      · rw [Finset.mem_singleton] at hj
        subst j
        exact hRclosed k hk 1
    have hbound := SharedSupport.support_family_bound_anchor_closed n C.gates.length
      s parents cost hi hb hc hv R hRc W (fun w hw => Finset.mem_range.mpr (hvalid w hw))
      hW p (fun w hw => preferredSupport_contains n C hAO T p w (hfull w hw))
    have heq : (Finset.range C.gates.length).filter (fun k => k ∈ R) = R := by
      ext k
      exact ⟨fun hk => (Finset.mem_filter.mp hk).2,
        fun hk => Finset.mem_filter.mpr ⟨hRreal hk, hk⟩⟩
    rw [heq] at hbound
    have hsum : R.sum cost = (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
      simp only [cost, Finset.sum_boole]
      rfl
    simpa only [hsum] using hbound

end PEqualNP.Outside.L_meta_2583.TPreservingSupport

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma closed_tight_all_ands_true (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∀ k ∈ R, (gateAt C k).op = GateOp.and → wv n C (setInput T) (n + k) = true := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have hr := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ R ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) R
      (fun k hk _ => hRclosed k hk 0) (fun k hk _ => hRclosed k hk 1) w hvalid hwR
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkR, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkR, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have hBeq : B = R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k hk hop
  have hmem : k ∈ B := by
    rw [hBeq]
    exact Finset.mem_filter.mpr ⟨hk, by simp [AndSignature.isAnd, hop]⟩
  have hboth := (Finset.mem_filter.mp hmem).2.2
  simpa [pickedBoth, hop] using hboth

lemma last_and_prefix_set (C : Circuit) (g : Nat) (hg : g < C.gates.length)
    (hga : (gateAt C g).op = GateOp.and)
    (hlast : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≤ g) :
    AndSignature.andPrefix C C.gates.length = insert g (AndSignature.andPrefix C g) := by
  ext k
  constructor
  · intro hk
    obtain ⟨hkr, hka⟩ := Finset.mem_filter.mp hk
    have hkop : (gateAt C k).op = GateOp.and := by
      cases hop : (gateAt C k).op <;> simp [AndSignature.isAnd, hop] at hka ⊢
    have hle := hlast k (Finset.mem_range.mp hkr) hkop
    by_cases heq : k = g
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hka⟩))
  · intro hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, by simp [AndSignature.isAnd, hga]⟩
    · obtain ⟨hkr, hka⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hkr) hg), hka⟩

lemma last_and_prefix_card (C : Circuit) (g : Nat) (hg : g < C.gates.length)
    (hga : (gateAt C g).op = GateOp.and)
    (hlast : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≤ g) :
    (AndSignature.andPrefix C C.gates.length).card = (AndSignature.andPrefix C g).card + 1 := by
  rw [last_and_prefix_set C g hg hga hlast]
  apply Finset.card_insert_of_notMem
  intro hm
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma true_wire_has_support_input (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) :
    ∀ w, wv n C (setInput T) w = true →
      ∃ p ∈ T, p ∈ fullSupport n C hAO w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [wv_input n C (setInput T) w hwn] at hw
        exact of_decide_eq_true hw
      · rw [show fullSupport n C hAO w = {⟨w, hwn⟩} from
          pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
        exact Finset.mem_singleton_self _
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [wv_rec n C (setInput T) hAO.2.1 k hk, inputs_two n C hAO k hk] at hw
      have hchild : wv n C (setInput T) (opnd C k 0) = true ∨
          wv n C (setInput T) (opnd C k 1) = true := by
        rcases hAO.1 _ (gate_mem C k hk) with hop | hop
        · have hb : wv n C (setInput T) (opnd C k 0) = true ∧
              wv n C (setInput T) (opnd C k 1) = true := by
            simpa [hop, GateOp.eval] using hw
          exact Or.inl hb.1
        · simpa [hop, GateOp.eval] using hw
      rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
      rcases hchild with hl | hr
      · obtain ⟨p, hp, hfull⟩ := ih _ (opnd_back n C hAO k hk 0) hl
        exact ⟨p, hp, Finset.mem_union_left _ hfull⟩
      · obtain ⟨p, hp, hfull⟩ := ih _ (opnd_back n C hAO k hk 1) hr
        exact ⟨p, hp, Finset.mem_union_right _ hfull⟩
    · rw [wv_missing n C (setInput T) w (by omega)] at hw
      cases hw

lemma tight_and_operands_T_disjoint (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    Disjoint (T ∩ fullSupport n C hAO (opnd C g 0))
      (T ∩ fullSupport n C hAO (opnd C g 1)) := by
  classical
  have hactive := tight_all_ands_true n C hAO T (n + g) htrue hmin htight
  have hlast := tight_implying_and_is_last n C hAO T (n + g) htrue hmin htight
    g hg hga (fun _ _ h => h)
  have hcount := last_and_prefix_card C g hg hga hlast
  have hbits : wv n C (setInput T) (opnd C g 0) = true ∧
      wv n C (setInput T) (opnd C g 1) = true := by
    simpa [wv_rec n C (setInput T) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval] using htrue
  apply Finset.disjoint_left.mpr
  intro p hp0 hp1
  obtain ⟨hpT, hp0⟩ := Finset.mem_inter.mp hp0
  have hp1 := (Finset.mem_inter.mp hp1).2
  let W : Finset Nat := {opnd C g 0, opnd C g 1}
  have hvalid : ∀ w ∈ W, w < n + g := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact opnd_back n C hAO g hg 0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact opnd_back n C hAO g hg 1
  have hWtrue : ∀ w ∈ W, wv n C (setInput T) w = true := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hbits.1
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hbits.2
  have hWfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hp0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hp1
  obtain ⟨S, hST, hSW, hScard⟩ := TPreservingSupport.shared_roots_support_within_T
    n C hAO T hactive g (Nat.le_of_lt hg) W hvalid hWtrue p hpT hWfull
  have hStrue : wv n C (setInput S) (n + g) = true := by
    have hs0 := hSW (opnd C g 0) (by simp [W])
    have hs1 := hSW (opnd C g 1) (by simp [W])
    simp [wv_rec n C (setInput S) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval, hs0, hs1]
  have hTcard := Finset.card_le_card (hmin S hST hStrue)
  omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma closed_tight_and_operands_T_disjoint
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    Disjoint (T ∩ fullSupport n C hAO (opnd C g 0))
      (T ∩ fullSupport n C hAO (opnd C g 1)) := by
  classical
  have hg := Finset.mem_range.mp (hRreal hgR)
  have hactive := closed_tight_all_ands_true n C hAO R hRreal hRclosed T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight
  let P := R ∩ Finset.range g
  have hPreal : P ⊆ Finset.range C.gates.length := fun _ hk =>
    hRreal (Finset.mem_inter.mp hk).1
  have hPclosed : ∀ k ∈ P, ∀ b : Fin 2,
      opnd C k b < n ∨ opnd C k b - n ∈ P := by
    intro k hk b
    obtain ⟨hkR, hkg⟩ := Finset.mem_inter.mp hk
    rcases hRclosed k hkR b with hb | hb
    · exact Or.inl hb
    · right
      refine Finset.mem_inter.mpr ⟨hb, Finset.mem_range.mpr ?_⟩
      have hkb := opnd_back n C hAO k (Finset.mem_range.mp (hRreal hkR)) b
      have hkg := Finset.mem_range.mp hkg
      omega
  have hPactive : ∀ k ∈ P, (gateAt C k).op = GateOp.and →
      wv n C (setInput T) (n + k) = true := fun k hk =>
    hactive k (Finset.mem_inter.mp hk).1
  have hbits : wv n C (setInput T) (opnd C g 0) = true ∧
      wv n C (setInput T) (opnd C g 1) = true := by
    simpa [wv_rec n C (setInput T) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval] using htrue
  apply Finset.disjoint_left.mpr
  intro p hp0 hp1
  obtain ⟨hpT, hp0⟩ := Finset.mem_inter.mp hp0
  have hp1 := (Finset.mem_inter.mp hp1).2
  let W : Finset Nat := {opnd C g 0, opnd C g 1}
  have hopP (b : Fin 2) : opnd C g b < n ∨ opnd C g b - n ∈ P := by
    by_cases hbn : opnd C g b < n
    · exact Or.inl hbn
    rcases hRclosed g hgR b with hb | hb
    · exact False.elim (hbn hb)
    · right
      refine Finset.mem_inter.mpr ⟨hb, Finset.mem_range.mpr ?_⟩
      have hback := opnd_back n C hAO g hg b
      omega
  have hW : ∀ w ∈ W, w < n ∨ w - n ∈ P := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hopP 0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hopP 1
  have hWtrue : ∀ w ∈ W, wv n C (setInput T) w = true := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hbits.1
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hbits.2
  have hWfull : ∀ w ∈ W, p ∈ fullSupport n C hAO w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hp0
    · rw [Finset.mem_singleton] at hw
      subst w
      exact hp1
  obtain ⟨S, hST, hSW, hScard⟩ := TPreservingSupport.shared_roots_support_within_T_closed
    n C hAO T P hPreal hPclosed hPactive W hW hWtrue p hpT hWfull
  have hStrue : wv n C (setInput S) (n + g) = true := by
    have hs0 := hSW (opnd C g 0) (by simp [W])
    have hs1 := hSW (opnd C g 1) (by simp [W])
    simp [wv_rec n C (setInput S) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval, hs0, hs1]
  have hTcard := Finset.card_le_card (hmin S hST hStrue)
  have hsub : insert g (P.filter (fun k => AndSignature.isAnd C k = true)) ⊆
      R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_filter.mpr ⟨hgR, by simp [AndSignature.isAnd, hga]⟩
    · obtain ⟨hkP, hka⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hkP).1, hka⟩
  have hgnot : g ∉ P.filter (fun k => AndSignature.isAnd C k = true) := by
    intro hm
    have hlt := Finset.mem_range.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hm).1).2
    omega
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hgnot] at hcount
  omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport

lemma wv_eq_of_agree_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) :
    ∀ w, (∀ p ∈ fullSupport n C hAO w, x p = y p) → wv n C x w = wv n C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hagree
    by_cases hwn : w < n
    · rw [wv_input n C x w hwn, wv_input n C y w hwn]
      apply hagree
      rw [show fullSupport n C hAO w = {⟨w, hwn⟩} from
        pickedSupport_input _ _ _ _ _ _ _ _ _ hwn]
      exact Finset.mem_singleton_self _
    by_cases hwg : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have h0 : wv n C x (opnd C k 0) = wv n C y (opnd C k 0) := by
        apply ih _ (opnd_back n C hAO k hk 0)
        intro p hp
        apply hagree
        rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
        exact Finset.mem_union_left _ hp
      have h1 : wv n C x (opnd C k 1) = wv n C y (opnd C k 1) := by
        apply ih _ (opnd_back n C hAO k hk 1)
        intro p hp
        apply hagree
        rw [TPreservingSupport.fullSupport_gate n C hAO k hk]
        exact Finset.mem_union_right _ hp
      rw [wv_rec n C x hAO.2.1 k hk, wv_rec n C y hAO.2.1 k hk,
        inputs_two n C hAO k hk]
      simp only [List.map_cons, List.map_nil, h0, h1]
    · rw [wv_missing n C x w (by omega), wv_missing n C y w (by omega)]

lemma wv_inter_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) :
    wv n C (setInput (T ∩ fullSupport n C hAO w)) w = wv n C (setInput T) w := by
  apply wv_eq_of_agree_fullSupport n C hAO
  intro p hp
  simp [setInput, hp]

lemma minimal_support_subset_fullSupport (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S) :
    T ⊆ fullSupport n C hAO w := by
  have hm := hmin (T ∩ fullSupport n C hAO w) Finset.inter_subset_left
    (by rw [wv_inter_fullSupport n C hAO T w]; exact htrue)
  exact fun _ hp => (Finset.mem_inter.mp (hm hp)).2

lemma and_operand_supports_union (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S) :
    (T ∩ fullSupport n C hAO (opnd C g 0)) ∪
      (T ∩ fullSupport n C hAO (opnd C g 1)) = T := by
  have hsub := minimal_support_subset_fullSupport n C hAO T (n + g) htrue hmin
  rw [TPreservingSupport.fullSupport_gate n C hAO g hg] at hsub
  ext p
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hp
    rcases Finset.mem_union.mp (hsub hp) with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩

lemma and_operand_supports_minimal (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (g : Nat) (hg : g < C.gates.length)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (hdis : Disjoint (T ∩ fullSupport n C hAO (opnd C g 0))
      (T ∩ fullSupport n C hAO (opnd C g 1))) :
    ∀ b : Fin 2, let U := T ∩ fullSupport n C hAO (opnd C g b)
      wv n C (setInput U) (opnd C g b) = true ∧
      ∀ S ⊆ U, wv n C (setInput S) (opnd C g b) = true → U ⊆ S := by
  classical
  have hbits : wv n C (setInput T) (opnd C g 0) = true ∧
      wv n C (setInput T) (opnd C g 1) = true := by
    simpa [wv_rec n C (setInput T) hAO.2.1 g hg, inputs_two n C hAO g hg,
      hga, GateOp.eval] using htrue
  have hminimal (b c : Fin 2) (hbc : b ≠ c)
      (hb : wv n C (setInput T) (opnd C g b) = true)
      (hc : wv n C (setInput T) (opnd C g c) = true)
      (hdisbc : Disjoint (T ∩ fullSupport n C hAO (opnd C g b))
        (T ∩ fullSupport n C hAO (opnd C g c))) :
      ∀ S ⊆ T ∩ fullSupport n C hAO (opnd C g b),
        wv n C (setInput S) (opnd C g b) = true →
        T ∩ fullSupport n C hAO (opnd C g b) ⊆ S := by
    intro S hS hSb
    let V := T ∩ fullSupport n C hAO (opnd C g c)
    have hVT : V ⊆ T := Finset.inter_subset_left
    have hST : S ⊆ T := Finset.Subset.trans hS Finset.inter_subset_left
    have hb' : wv n C (setInput (S ∪ V)) (opnd C g b) = true :=
      wv_mono n C hAO.1 hAO.2.1 _ _
        (fun p hp => decide_eq_true (Finset.mem_union_left V (of_decide_eq_true hp))) _ hSb
    have hc' : wv n C (setInput (S ∪ V)) (opnd C g c) = true := by
      apply wv_mono n C hAO.1 hAO.2.1 (setInput V) _
        (fun p hp => decide_eq_true (Finset.mem_union_right S (of_decide_eq_true hp)))
      rw [wv_inter_fullSupport n C hAO T (opnd C g c)]
      exact hc
    have hroot : wv n C (setInput (S ∪ V)) (n + g) = true := by
      fin_cases b <;> fin_cases c <;> simp_all [wv_rec n C (setInput (S ∪ V)) hAO.2.1 g hg,
        inputs_two n C hAO g hg, GateOp.eval]
    have hTU := hmin (S ∪ V) (Finset.union_subset hST hVT) hroot
    intro p hp
    rcases Finset.mem_union.mp (hTU (Finset.mem_inter.mp hp).1) with hs | hv
    · exact hs
    · exact False.elim (Finset.disjoint_left.mp hdisbc hp hv)
  intro b
  dsimp
  fin_cases b
  · exact ⟨by rw [wv_inter_fullSupport]; exact hbits.1,
      hminimal 0 1 (by decide) hbits.1 hbits.2 hdis⟩
  · exact ⟨by rw [wv_inter_fullSupport]; exact hbits.2,
      hminimal 1 0 (by decide) hbits.2 hbits.1 hdis.symm⟩

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma fullSupport_mono_inCone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (i : Nat) : ∀ j, InCone n C i j →
      fullSupport n C hAO (n + i) ⊆ fullSupport n C hAO (n + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hij
    obtain ⟨hj, k, hkj, hinput, hik⟩ := (TopNormal.inCone_iff n C i j).mp hij
    have hsub : fullSupport n C hAO (n + k) ⊆ fullSupport n C hAO (n + j) := by
      rw [TPreservingSupport.fullSupport_gate n C hAO j hj]
      rw [inputs_two n C hAO j hj] at hinput
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hinput
      rcases hinput with hinput | hinput
      · rw [hinput]
        exact Finset.subset_union_left
      · rw [hinput]
        exact Finset.subset_union_right
    rcases hik with rfl | hik
    · exact hsub
    · exact Finset.Subset.trans (ih k hkj hik) hsub

lemma wireCone_fullSupport_subset (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (w k : Nat) (hk : k ∈ wireCone n C w) :
    fullSupport n C hAO (n + k) ⊆ fullSupport n C hAO w := by
  by_cases hwn : w < n
  · simp [wireCone, hwn] at hk
  · have hw : n + (w - n) = w := by omega
    rw [wireCone, ite_eq_right hwn, mem_gateCone] at hk
    rcases hk with rfl | hk
    · rw [hw]
    · have hsub := fullSupport_mono_inCone n C hAO k (w - n) hk
      rwa [hw] at hsub

lemma wireCone_subset_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (w : Nat) (hwR : w < n ∨ w - n ∈ R) : wireCone n C w ⊆ R := by
  have hancestor : ∀ j, j ∈ R → ∀ i, InCone n C i j → i ∈ R := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hjR i hij
      obtain ⟨hj, k, hkj, hinput, hik⟩ := (TopNormal.inCone_iff n C i j).mp hij
      have hkR : k ∈ R := by
        rw [inputs_two n C hAO j hj] at hinput
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hinput
        rcases hinput with hinput | hinput
        · have hc := hRclosed j hjR 0
          rw [← hinput] at hc
          simpa using hc
        · have hc := hRclosed j hjR 1
          rw [← hinput] at hc
          simpa using hc
      rcases hik with rfl | hik
      · exact hkR
      · exact ih k hkj hkR i hik
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · have hwR := hwR.resolve_left hwn
    intro k hk
    rw [wireCone, ite_eq_right hwn, mem_gateCone] at hk
    rcases hk with rfl | hk
    · exact hwR
    · exact hancestor (w - n) hwR k hk

lemma closed_tight_and_cones_disjoint
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    Disjoint ((wireCone n C (opnd C g 0)).filter (fun k => AndSignature.isAnd C k = true))
      ((wireCone n C (opnd C g 1)).filter (fun k => AndSignature.isAnd C k = true)) := by
  have hdis := closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed
    T g hgR hga htrue hmin htight
  have hactive := closed_tight_all_ands_true n C hAO R hRreal hRclosed T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight
  have hc0 := wireCone_subset_closed n C hAO R hRclosed (opnd C g 0) (hRclosed g hgR 0)
  apply Finset.disjoint_left.mpr
  intro k hk0 hk1
  obtain ⟨hk0, hka⟩ := Finset.mem_filter.mp hk0
  have hk1 := (Finset.mem_filter.mp hk1).1
  have hkop : (gateAt C k).op = GateOp.and := by
    cases hop : (gateAt C k).op <;> simp [AndSignature.isAnd, hop] at hka ⊢
  obtain ⟨p, hpT, hpk⟩ := true_wire_has_support_input n C hAO T (n + k)
    (hactive k (hc0 hk0) hkop)
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_inter.mpr ⟨hpT, wireCone_fullSupport_subset n C hAO _ k hk0 hpk⟩)
    (Finset.mem_inter.mpr ⟨hpT, wireCone_fullSupport_subset n C hAO _ k hk1 hpk⟩)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma closed_minimal_support_card_le_ands
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S) :
    T.card ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1 := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have hr := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ R ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) R
      (fun k hk _ => hRclosed k hk 0) (fun k hk _ => hRclosed k hk 1) w hvalid hwR
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkR, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkR, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have := Finset.card_le_card hsub
  omega

lemma wireCone_below (n : Nat) (C : Circuit) (w r : Nat) (hw : w < n + r) :
    wireCone n C w ⊆ Finset.range r := by
  by_cases hwn : w < n
  · simp [wireCone, hwn]
  · intro k hk
    rw [wireCone, ite_eq_right hwn] at hk
    have hk := Finset.mem_range.mp (gateCone_prefix n C (w - n) hk)
    exact Finset.mem_range.mpr (by omega)

lemma closed_tight_and_operand_counts
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (hga : (gateAt C g).op = GateOp.and)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∀ b : Fin 2,
      (T ∩ fullSupport n C hAO (opnd C g b)).card =
        ((wireCone n C (opnd C g b)).filter (fun k => AndSignature.isAnd C k = true)).card + 1 ∧
      ((wireCone n C (opnd C g b)).filter (fun k => AndSignature.isAnd C k = true)).card <
        (R.filter (fun k => AndSignature.isAnd C k = true)).card := by
  classical
  have hg := Finset.mem_range.mp (hRreal hgR)
  let U := fun b : Fin 2 => T ∩ fullSupport n C hAO (opnd C g b)
  let A := fun b : Fin 2 => (wireCone n C (opnd C g b)).filter
    (fun k => AndSignature.isAnd C k = true)
  let B := R.filter (fun k => AndSignature.isAnd C k = true)
  have hdisU : Disjoint (U 0) (U 1) :=
    closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed T g hgR hga htrue hmin htight
  have hdisA : Disjoint (A 0) (A 1) :=
    closed_tight_and_cones_disjoint n C hAO R hRreal hRclosed T g hgR hga htrue hmin htight
  have hunion : U 0 ∪ U 1 = T := and_operand_supports_union n C hAO T g hg htrue hmin
  have hUcard : (U 0).card + (U 1).card = T.card := by
    rw [← Finset.card_union_of_disjoint hdisU, hunion]
  have hminimal := and_operand_supports_minimal n C hAO T g hg hga htrue hmin hdisU
  have hbound (b : Fin 2) : (U b).card ≤ (A b).card + 1 := by
    have hw := opnd_back n C hAO g hg b
    have hwreal : opnd C g b < n + C.gates.length := by omega
    exact closed_minimal_support_card_le_ands n C hAO (wireCone n C (opnd C g b))
      (wireCone_real n C _ hwreal) (wireCone_closed n C hAO _ hwreal) (U b) _
      (wireCone_root n C _) (hminimal b).1 (hminimal b).2
  have hAsub (b : Fin 2) : A b ⊆ B := by
    intro k hk
    obtain ⟨hk, hka⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr
      ⟨wireCone_subset_closed n C hAO R hRclosed _ (hRclosed g hgR b) hk, hka⟩
  have hgnot (b : Fin 2) : g ∉ A b := by
    intro hk
    have hlt := Finset.mem_range.mp
      (wireCone_below n C _ g (opnd_back n C hAO g hg b) (Finset.mem_filter.mp hk).1)
    omega
  have hsub : insert g (A 0 ∪ A 1) ⊆ B := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_filter.mpr ⟨hgR, by simp [AndSignature.isAnd, hga]⟩
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact hAsub 0 hk
      · exact hAsub 1 hk
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_union]; exact not_or.mpr ⟨hgnot 0, hgnot 1⟩),
    Finset.card_union_of_disjoint hdisA] at hcard
  have h0 := hbound 0
  have h1 := hbound 1
  change T.card = B.card + 1 at htight
  intro b
  change (U b).card = (A b).card + 1 ∧ (A b).card < B.card
  fin_cases b
  · change (U 0).card = (A 0).card + 1 ∧ (A 0).card < B.card
    constructor <;> omega
  · change (U 1).card = (A 1).card + 1 ∧ (A 1).card < B.card
    constructor <;> omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.MintermCircuit

lemma exists_or_frontier (n : Nat) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, ∃ I : Finset (Fin n), ∃ A : Finset Nat,
      (∀ k ∈ A, k < C.gates.length ∧ (gateAt C k).op = GateOp.and) ∧
      ∀ x, wv n C x w = true ↔ (∃ i ∈ I, x i = true) ∨
        (∃ k ∈ A, wv n C x (n + k) = true) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · refine ⟨{⟨w, hwn⟩}, ∅, by simp, ?_⟩
      intro x
      rw [wv_input n C x w hwn]
      simp
    by_cases hwg : n + C.gates.length ≤ w
    · refine ⟨∅, ∅, by simp, ?_⟩
      intro x
      rw [wv_missing n C x w hwg]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases hAO.1 _ (gate_mem C k hk) with hand | hor
      · refine ⟨∅, {k}, ?_, ?_⟩
        · intro j hj
          have heq : j = k := Finset.mem_singleton.mp hj
          simpa [heq] using (show k < C.gates.length ∧ (gateAt C k).op = GateOp.and from ⟨hk, hand⟩)
        · intro x
          simp
      · obtain ⟨I₀, A₀, hA₀, h₀⟩ := ih (opnd C k 0) (opnd_back n C hAO k hk 0)
        obtain ⟨I₁, A₁, hA₁, h₁⟩ := ih (opnd C k 1) (opnd_back n C hAO k hk 1)
        refine ⟨I₀ ∪ I₁, A₀ ∪ A₁, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact hA₀ j hj
          · exact hA₁ j hj
        · intro x
          rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp only [hor, GateOp.eval, Finset.mem_union]
          aesop

lemma tight_or_frontier_last_and
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (hpos : 0 < (AndSignature.andPrefix C C.gates.length).card) :
    ∃ g : Nat, ∃ I : Finset (Fin n),
      g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      (∀ i ∈ I, i ∉ T) ∧
      wv n C (setInput T) (n + g) = true ∧
      (∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S) ∧
      AndSignature.andPrefix C C.gates.length ⊆ AncestorJunk.gateCone n C g ∧
      ∀ x, wv n C x w = true ↔ wv n C x (n + g) = true ∨ ∃ i ∈ I, x i = true := by
  classical
  obtain ⟨I, A, hA, hfront⟩ := exists_or_frontier n C hAO w
  have houtside : ∀ i ∈ I, i ∉ T := by
    intro i hi hiT
    have hroot : wv n C (setInput {i}) w = true :=
      (hfront _).mpr (Or.inl ⟨i, hi, by simp [setInput]⟩)
    have hsub := hmin {i} (Finset.singleton_subset_iff.mpr hiT) hroot
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hex : ∃ g ∈ A, wv n C (setInput T) (n + g) = true := by
    rcases (hfront _).mp htrue with ⟨i, hi, hit⟩ | ha
    · exact False.elim (houtside i hi (of_decide_eq_true hit))
    · exact ha
  obtain ⟨g, hgA, hgtrue⟩ := hex
  have hg := hA g hgA
  have himplies (k : Nat) (hk : k ∈ A) :
      ∀ S ⊆ T, wv n C (setInput S) (n + k) = true → wv n C (setInput S) w = true := by
    intro S _ ht
    exact (hfront _).mpr (Or.inr ⟨k, hk, ht⟩)
  have hsingleton : ∀ k ∈ A, k = g := by
    intro k hk
    exact tight_implying_and_unique n C hAO T w htrue hmin htight k g
      (hA k hk).1 hg.1 (hA k hk).2 hg.2 (himplies k hk) (himplies g hgA)
  have hgmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S := by
    intro S hS ht
    exact hmin S hS (himplies g hgA S hS ht)
  refine ⟨g, I, hg.1, hg.2, houtside, hgtrue, hgmin,
    tight_all_ands_in_gateCone n C hAO T g hg.1 hgtrue hgmin htight, ?_⟩
  intro x
  constructor
  · intro hx
    rcases (hfront x).mp hx with hi | ⟨k, hk, hkt⟩
    · exact Or.inr hi
    · exact Or.inl ((hsingleton k hk) ▸ hkt)
  · intro hx
    rcases hx with hgx | hi
    · exact (hfront x).mpr (Or.inr ⟨g, hgA, hgx⟩)
    · exact (hfront x).mpr (Or.inl hi)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma gateCone_subset_of_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R) :
    ∀ k, k < C.gates.length → k ∈ R → gateCone n C k ⊆ R := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hkR i hi
    rcases (mem_gateCone n C k i).mp hi with rfl | hanc
    · exact hkR
    · obtain ⟨_, j, hjk, hjin, hij⟩ := (TopNormal.inCone_iff n C i k).mp hanc
      have hjR : j ∈ R := by
        rw [inputs_two n C hAO k hk] at hjin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hjin
        rcases hjin with hjin | hjin
        · have h := hRclosed k hkR 0
          rw [← hjin] at h
          simpa only [Nat.add_sub_cancel_left, show ¬n + j < n by omega, false_or] using h
        · have h := hRclosed k hkR 1
          rw [← hjin] at h
          simpa only [Nat.add_sub_cancel_left, show ¬n + j < n by omega, false_or] using h
      exact ih j hjk (lt_trans hjk hk) hjR ((mem_gateCone n C j i).mpr hij)

lemma closed_tight_all_ands_in_subcone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (S : Finset Nat) (hSR : S ⊆ R)
    (hSclosed : ∀ k ∈ S, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ S)
    (hwS : w < n ∨ w - n ∈ S) :
    R.filter (fun k => AndSignature.isAnd C k = true) ⊆ S := by
  classical
  have hvalid : w < n + C.gates.length := by
    rcases hwR with hw | hw
    · omega
    · have := Finset.mem_range.mp (hRreal hw)
      omega
  have hs := support_sound n C hAO T w htrue
  have hTeq : T = circuitSupport n C hAO (setInput T) w :=
    Finset.Subset.antisymm (hmin _ hs.1 hs.2) hs.1
  let B : Finset Nat := (Finset.range C.gates.length).filter
    (fun k => k ∈ S ∧ pickedBoth n C (setInput T) k = true)
  have hbound : T.card ≤ B.card + 1 := by
    rw [hTeq]
    exact pickedSupport_bound_closed n C.gates.length (fun k => opnd C k 0)
      (fun k => opnd C k 1) (pickedBoth n C (setInput T))
      (fun k => wv n C (setInput T) (opnd C k 0))
      (fun k hk => opnd_back n C hAO k hk 0)
      (fun k hk => opnd_back n C hAO k hk 1) S
      (fun k hk _ => hSclosed k hk 0) (fun k hk _ => hSclosed k hk 1) w hvalid hwS
  have hsub : B ⊆ R.filter (fun k => AndSignature.isAnd C k = true) := by
    intro k hk
    obtain ⟨_, hkS, hboth⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hSR hkS, ?_⟩
    cases hop : (gateAt C k).op <;> simp [pickedBoth, AndSignature.isAnd, hop] at hboth ⊢
  have hBeq : B = R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro k hk
  rw [← hBeq] at hk
  exact (Finset.mem_filter.mp hk).2.1

lemma closed_tight_all_ands_in_gateCone (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (g : Nat) (hgR : g ∈ R)
    (htrue : wv n C (setInput T) (n + g) = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) (n + g) = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    R.filter (fun k => AndSignature.isAnd C k = true) ⊆ gateCone n C g := by
  have hg := Finset.mem_range.mp (hRreal hgR)
  exact closed_tight_all_ands_in_subcone n C hAO R hRreal T (n + g)
    (Or.inr (by simpa using hgR)) htrue hmin htight (gateCone n C g)
    (gateCone_subset_of_closed n C hAO R hRclosed g hg hgR)
    (gateCone_closed n C hAO g hg)
    (Or.inr (by simpa using gateCone_self n C g))

lemma closed_tight_implying_and_last (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (j : Nat) (hjR : j ∈ R) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → wv n C (setInput U) w = true) :
    ∀ k ∈ R, (gateAt C k).op = GateOp.and → k ≤ j := by
  have hjtrue := closed_tight_all_ands_true n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight j hjR hja
  have hjmin : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → T ⊆ U := by
    intro U hU hUj
    exact hmin U hU (himplies U hU hUj)
  have hcone := closed_tight_all_ands_in_gateCone n C hAO R hRreal hRclosed T j hjR
    hjtrue hjmin htight
  intro k hk hka
  have hmem : k ∈ R.filter (fun k => AndSignature.isAnd C k = true) :=
    Finset.mem_filter.mpr ⟨hk, by simp [AndSignature.isAnd, hka]⟩
  have hkle := Finset.mem_range.mp (gateCone_prefix n C j (hcone hmem))
  omega

lemma closed_tight_implying_and_unique (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ U ⊆ T, wv n C (setInput U) w = true → T ⊆ U)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (i j : Nat) (hiR : i ∈ R) (hjR : j ∈ R)
    (hia : (gateAt C i).op = GateOp.and) (hja : (gateAt C j).op = GateOp.and)
    (himplies : ∀ U ⊆ T, wv n C (setInput U) (n + i) = true → wv n C (setInput U) w = true)
    (hjimplies : ∀ U ⊆ T, wv n C (setInput U) (n + j) = true → wv n C (setInput U) w = true) : i = j := by
  have hji := closed_tight_implying_and_last n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight i hiR hia himplies j hjR hja
  have hij := closed_tight_implying_and_last n C hAO R hRreal hRclosed T w hwR
    htrue hmin htight j hjR hja hjimplies i hiR hia
  omega

lemma exists_or_frontier_closed (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R) :
    ∀ w, (w < n ∨ w - n ∈ R) → ∃ I : Finset (Fin n), ∃ A : Finset Nat,
      (∀ k ∈ A, k ∈ R ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.and) ∧
      ∀ x, wv n C x w = true ↔ (∃ i ∈ I, x i = true) ∨
        (∃ k ∈ A, wv n C x (n + k) = true) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwR
    by_cases hwn : w < n
    · refine ⟨{⟨w, hwn⟩}, ∅, by simp, ?_⟩
      intro x
      rw [wv_input n C x w hwn]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkR : k ∈ R := by simpa only [Nat.add_sub_cancel_left] using hwR.resolve_left hwn
      have hk := Finset.mem_range.mp (hRreal hkR)
      rcases hAO.1 _ (gate_mem C k hk) with hand | hor
      · refine ⟨∅, {k}, ?_, ?_⟩
        · intro j hj
          have heq : j = k := Finset.mem_singleton.mp hj
          simpa only [heq] using ⟨hkR, hk, hand⟩
        · intro x
          simp
      · obtain ⟨I₀, A₀, hA₀, h₀⟩ := ih (opnd C k 0) (opnd_back n C hAO k hk 0) (hRclosed k hkR 0)
        obtain ⟨I₁, A₁, hA₁, h₁⟩ := ih (opnd C k 1) (opnd_back n C hAO k hk 1) (hRclosed k hkR 1)
        refine ⟨I₀ ∪ I₁, A₀ ∪ A₁, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact hA₀ j hj
          · exact hA₁ j hj
        · intro x
          rw [wv_rec n C x hAO.2.1 k hk, inputs_two n C hAO k hk]
          simp only [hor, GateOp.eval, Finset.mem_union]
          aesop

lemma closed_tight_or_frontier_last_and
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (hpos : 0 < (R.filter (fun k => AndSignature.isAnd C k = true)).card) :
    ∃ g : Nat, ∃ I : Finset (Fin n),
      g ∈ R ∧ g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      (∀ i ∈ I, i ∉ T) ∧
      wv n C (setInput T) (n + g) = true ∧
      (∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S) ∧
      R.filter (fun k => AndSignature.isAnd C k = true) ⊆ AncestorJunk.gateCone n C g ∧
      ∀ x, wv n C x w = true ↔ wv n C x (n + g) = true ∨ ∃ i ∈ I, x i = true := by
  classical
  obtain ⟨I, A, hA, hfront⟩ := exists_or_frontier_closed n C hAO R hRreal hRclosed w hwR
  have houtside : ∀ i ∈ I, i ∉ T := by
    intro i hi hiT
    have hroot : wv n C (setInput {i}) w = true :=
      (hfront _).mpr (Or.inl ⟨i, hi, by simp [setInput]⟩)
    have hsub := hmin {i} (Finset.singleton_subset_iff.mpr hiT) hroot
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hex : ∃ g ∈ A, wv n C (setInput T) (n + g) = true := by
    rcases (hfront _).mp htrue with ⟨i, hi, hit⟩ | ha
    · exact False.elim (houtside i hi (of_decide_eq_true hit))
    · exact ha
  obtain ⟨g, hgA, hgtrue⟩ := hex
  have hg := hA g hgA
  have himplies (k : Nat) (hk : k ∈ A) :
      ∀ S ⊆ T, wv n C (setInput S) (n + k) = true → wv n C (setInput S) w = true := by
    intro S _ ht
    exact (hfront _).mpr (Or.inr ⟨k, hk, ht⟩)
  have hsingleton : ∀ k ∈ A, k = g := by
    intro k hk
    exact closed_tight_implying_and_unique n C hAO R hRreal hRclosed T w hwR htrue hmin htight k g
      (hA k hk).1 hg.1 (hA k hk).2.2 hg.2.2 (himplies k hk) (himplies g hgA)
  have hgmin : ∀ S ⊆ T, wv n C (setInput S) (n + g) = true → T ⊆ S := by
    intro S hS ht
    exact hmin S hS (himplies g hgA S hS ht)
  refine ⟨g, I, hg.1, hg.2.1, hg.2.2, houtside, hgtrue, hgmin,
    closed_tight_all_ands_in_gateCone n C hAO R hRreal hRclosed T g hg.1 hgtrue hgmin htight, ?_⟩
  intro x
  constructor
  · intro hx
    rcases (hfront x).mp hx with hi | ⟨k, hk, hkt⟩
    · exact Or.inr hi
    · exact Or.inl ((hsingleton k hk) ▸ hkt)
  · intro hx
    rcases hx with hgx | hi
    · exact (hfront x).mpr (Or.inr ⟨g, hgA, hgx⟩)
    · exact (hfront x).mpr (Or.inl hi)

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

def Holds {n : Nat} (clauses : Finset (Finset (Fin n))) (x : Fin n → Bool) : Prop :=
  ∀ clause ∈ clauses, ∃ v ∈ clause, x v = true

lemma holds_singleton {n : Nat} (I : Finset (Fin n)) (x : Fin n → Bool) :
    Holds {I} x ↔ ∃ v ∈ I, x v = true := by
  simp [Holds]

lemma holds_union {n : Nat} (A B : Finset (Finset (Fin n))) (x : Fin n → Bool) :
    Holds (A ∪ B) x ↔ Holds A x ∧ Holds B x := by
  simp only [Holds, Finset.mem_union]
  aesop

lemma holds_add_outside {n : Nat} (clauses : Finset (Finset (Fin n)))
    (I : Finset (Fin n)) (x : Fin n → Bool) :
    Holds (clauses.image (fun clause => clause ∪ I)) x ↔
      Holds clauses x ∨ ∃ v ∈ I, x v = true := by
  classical
  constructor
  · intro h
    by_cases hi : ∃ v ∈ I, x v = true
    · exact Or.inr hi
    · left
      intro clause hc
      obtain ⟨v, hv, hx⟩ := h (clause ∪ I) (Finset.mem_image.mpr ⟨clause, hc, rfl⟩)
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨v, hv, hx⟩
      · exact False.elim (hi ⟨v, hv, hx⟩)
  · intro h clause hc
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    rcases h with h | ⟨v, hv, hx⟩
    · obtain ⟨v, hv, hx⟩ := h old hold
      exact ⟨v, Finset.mem_union_left I hv, hx⟩
    · exact ⟨v, Finset.mem_union_right old hv, hx⟩

lemma cnf_and_or_compose {n : Nat} (f g h : (Fin n → Bool) → Bool)
    (A B : Finset (Finset (Fin n))) (I : Finset (Fin n))
    (hf : ∀ x, f x = true ↔ Holds A x)
    (hg : ∀ x, g x = true ↔ Holds B x)
    (hh : ∀ x, h x = true ↔ (f x = true ∧ g x = true) ∨ ∃ v ∈ I, x v = true) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ A.card + B.card ∧
      ∀ x, h x = true ↔ Holds clauses x := by
  classical
  refine ⟨(A ∪ B).image (fun clause => clause ∪ I), ?_, ?_⟩
  · exact (Finset.card_image_le).trans (Finset.card_union_le A B)
  · intro x
    rw [holds_add_outside, holds_union, ← hf x, ← hg x]
    exact hh x

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.Minterm
  PEqualNP.Outside.L_meta_2583.MintermCircuit PEqualNP.Outside.L_meta_2583.BiasedSupport
  PEqualNP.Outside.L_meta_2583.AncestorJunk PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma closed_tight_has_short_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ T.card ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  classical
  generalize ha : (R.filter (fun k => AndSignature.isAnd C k = true)).card = a at htight
  induction a using Nat.strong_induction_on generalizing R T w with
  | ind a ih =>
    by_cases hz : a = 0
    · obtain ⟨I, A, hA, hfront⟩ := exists_or_frontier_closed n C hAO R hRreal hRclosed w hwR
      have hAempty : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hkA := hA k hk
        have hm : k ∈ R.filter (fun k => AndSignature.isAnd C k = true) :=
          Finset.mem_filter.mpr ⟨hkA.1, by simp [AndSignature.isAnd, hkA.2.2]⟩
        have hempty : R.filter (fun k => AndSignature.isAnd C k = true) = ∅ :=
          Finset.card_eq_zero.mp (by omega)
        rw [hempty] at hm
        exact Finset.notMem_empty _ hm
      refine ⟨{I}, ?_, ?_⟩
      · simp only [Finset.card_singleton]
        omega
      · intro x
        rw [TightCNF.holds_singleton]
        simpa [hAempty] using hfront x
    · have hpos : 0 < (R.filter (fun k => AndSignature.isAnd C k = true)).card := by omega
      obtain ⟨g, I, hgR, hg, hga, _houtside, hgtrue, hgmin, _hcone, hsem⟩ :=
        closed_tight_or_frontier_last_and n C hAO R hRreal hRclosed T w hwR htrue hmin
          (by omega) hpos
      have hdis := closed_tight_and_operands_T_disjoint n C hAO R hRreal hRclosed
        T g hgR hga hgtrue hgmin (by omega)
      have hminimal := and_operand_supports_minimal n C hAO T g hg hga hgtrue hgmin hdis
      have hcounts := closed_tight_and_operand_counts n C hAO R hRreal hRclosed
        T g hgR hga hgtrue hgmin (by omega)
      have hrec (b : Fin 2) :
          ∃ clauses : Finset (Finset (Fin n)),
            clauses.card ≤ (T ∩ fullSupport n C hAO (opnd C g b)).card ∧
              ∀ x, wv n C x (opnd C g b) = true ↔ TightCNF.Holds clauses x := by
        have hback := opnd_back n C hAO g hg b
        have hvalid : opnd C g b < n + C.gates.length := by omega
        exact ih ((wireCone n C (opnd C g b)).filter
          (fun k => AndSignature.isAnd C k = true)).card
          (by have := (hcounts b).2; omega)
          (wireCone n C (opnd C g b)) (wireCone_real n C _ hvalid)
          (wireCone_closed n C hAO _ hvalid) (T ∩ fullSupport n C hAO (opnd C g b))
          (opnd C g b) (wireCone_root n C _) (hminimal b).1 (hminimal b).2 rfl (hcounts b).1
      obtain ⟨A, hAcard, hAsem⟩ := hrec 0
      obtain ⟨B, hBcard, hBsem⟩ := hrec 1
      have hroot : ∀ x, wv n C x w = true ↔
          (wv n C x (opnd C g 0) = true ∧ wv n C x (opnd C g 1) = true) ∨
            ∃ i ∈ I, x i = true := by
        intro x
        rw [hsem x, wv_rec n C x hAO.2.1 g hg, inputs_two n C hAO g hg]
        simp [hga, GateOp.eval]
      obtain ⟨clauses, hcard, hclauses⟩ := TightCNF.cnf_and_or_compose
        (fun x => wv n C x (opnd C g 0)) (fun x => wv n C x (opnd C g 1))
        (fun x => wv n C x w) A B I hAsem hBsem hroot
      refine ⟨clauses, ?_, hclauses⟩
      have hunion := and_operand_supports_union n C hAO T g hg hgtrue hgmin
      have hsum : (T ∩ fullSupport n C hAO (opnd C g 0)).card +
          (T ∩ fullSupport n C hAO (opnd C g 1)).card = T.card := by
        rw [← Finset.card_union_of_disjoint hdis, hunion]
      omega

lemma tight_has_short_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card ≤ T.card ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  have hvalid : w < n + C.gates.length := by
    by_contra hn
    rw [wv_missing n C (setInput T) w (by omega)] at htrue
    cases htrue
  exact closed_tight_has_short_cnf n C hAO (Finset.range C.gates.length)
    (fun _ h => h)
    (fun k hk b => by
      have hb := opnd_back n C hAO k (Finset.mem_range.mp hk) b
      by_cases hbn : opnd C k b < n
      · exact Or.inl hbn
      · exact Or.inr (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)))
    T w (by
      by_cases hwn : w < n
      · exact Or.inl hwn
      · exact Or.inr (Finset.mem_range.mpr (by omega))) htrue hmin htight

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma minimal_support_clause_witness {n : Nat}
    (clauses : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (htrue : Holds clauses (setInput T))
    (hmin : ∀ S ⊆ T, Holds clauses (setInput S) → T ⊆ S)
    (t : Fin n) (ht : t ∈ T) :
    ∃ clause ∈ clauses, clause ∩ T = {t} := by
  classical
  have hnot : ¬ Holds clauses (setInput (T.erase t)) := by
    intro h
    exact Finset.notMem_erase t T (hmin (T.erase t) (Finset.erase_subset t T) h ht)
  unfold Holds at hnot
  push Not at hnot
  obtain ⟨clause, hc, hno⟩ := hnot
  obtain ⟨v, hv, hvT⟩ := htrue clause hc
  have hvT : v ∈ T := of_decide_eq_true hvT
  have hvt : v = t := by
    by_contra hvn
    exact hno v hv (decide_eq_true (Finset.mem_erase.mpr ⟨hvn, hvT⟩))
  subst v
  refine ⟨clause, hc, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpT⟩ := Finset.mem_inter.mp hp
    apply Finset.mem_singleton.mpr
    by_contra hpn
    exact hno p hpc (decide_eq_true (Finset.mem_erase.mpr ⟨hpn, hpT⟩))
  · intro hp
    have hpt := Finset.mem_singleton.mp hp
    subst p
    exact Finset.mem_inter.mpr ⟨hv, ht⟩

lemma minimal_support_short_clauses_exact {n : Nat}
    (clauses : Finset (Finset (Fin n))) (T : Finset (Fin n))
    (htrue : Holds clauses (setInput T))
    (hmin : ∀ S ⊆ T, Holds clauses (setInput S) → T ⊆ S)
    (hcard : clauses.card ≤ T.card) :
    clauses.card = T.card ∧ ∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t} := by
  classical
  choose f hf using fun t : {t // t ∈ T} =>
    minimal_support_clause_witness clauses T htrue hmin t.val t.property
  have hfinj : Function.Injective f := by
    intro s t hst
    have heq : ({s.val} : Finset (Fin n)) = {t.val} := by
      rw [← (hf s).2, ← (hf t).2, hst]
    apply Subtype.ext
    exact Finset.singleton_injective heq
  let chosen : Finset (Finset (Fin n)) := T.attach.image f
  have hchosen : chosen.card = T.card := by
    rw [Finset.card_image_of_injective _ hfinj]
    exact Finset.card_attach
  have hsub : chosen ⊆ clauses := by
    intro clause hc
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
    exact (hf t).1
  have heq : chosen = clauses := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨by rw [← heq, hchosen], ?_⟩
  intro clause hc
  rw [← heq] at hc
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨t.val, t.property, (hf t).2⟩

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma closed_tight_has_exact_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card = T.card ∧
      (∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t}) ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  obtain ⟨clauses, hcard, hsem⟩ := closed_tight_has_short_cnf n C hAO
    R hRreal hRclosed T w hwR htrue hmin htight
  have hclauses := TightCNF.minimal_support_short_clauses_exact clauses T
    ((hsem _).mp htrue) (fun S hS h => hmin S hS ((hsem _).mpr h)) hcard
  exact ⟨clauses, hclauses.1, hclauses.2, hsem⟩

lemma tight_has_exact_cnf
    (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w : Nat) (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1) :
    ∃ clauses : Finset (Finset (Fin n)), clauses.card = T.card ∧
      (∀ clause ∈ clauses, ∃ t ∈ T, clause ∩ T = {t}) ∧
      ∀ x, wv n C x w = true ↔ TightCNF.Holds clauses x := by
  obtain ⟨clauses, hcard, hsem⟩ := tight_has_short_cnf n C hAO T w htrue hmin htight
  have hclauses := TightCNF.minimal_support_short_clauses_exact clauses T
    ((hsem _).mp htrue) (fun S hS h => hmin S hS ((hsem _).mpr h)) hcard
  exact ⟨clauses, hclauses.1, hclauses.2, hsem⟩

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

lemma tight_false_support_safe_partner_is_or {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w v : Nat) (htrue : wv n C (setInput T) w = true)
    (hfalse : graphFun G ∅ (setInput T) = false)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (hsafe : ∀ x, wv n C x w = true → wv n C x v = true → graphFun G ∅ x = true) :
    ∃ I : Finset (Fin n), (∀ i ∈ I, i ∉ T) ∧
      (∀ x, wv n C x v = true ↔ ∃ i ∈ I, x i = true) ∧
      ∀ i ∈ I, ∀ x, wv n C x w = true → x i = true → graphFun G ∅ x = true := by
  have hvfalse : wv n C (setInput T) v = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    have hf := hsafe (setInput T) htrue hv
    rw [hfalse] at hf
    contradiction
  obtain ⟨I, hIT, hI⟩ := tight_false_wire_is_outside_or n C hAO T w htrue hmin htight v hvfalse
  refine ⟨I, hIT, hI, ?_⟩
  intro i hi x hw hx
  exact hsafe x hw ((hI x).mpr ⟨i, hi, hx⟩)

lemma tight_false_support_partner_has_safe_endpoint {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w v : Nat) (htrue : wv n C (setInput T) w = true)
    (hfalse : graphFun G ∅ (setInput T) = false)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (hsafe : ∀ x, wv n C x w = true → wv n C x v = true → graphFun G ∅ x = true)
    (a b : Fin n) (hpair : wv n C (setInput {a, b}) v = true) :
    ∃ p : Fin n, (p = a ∨ p = b) ∧ p ∉ T ∧
      ∀ x, wv n C x w = true → x p = true → graphFun G ∅ x = true := by
  obtain ⟨I, hIT, hI, hguard⟩ := tight_false_support_safe_partner_is_or G C hAO T w v
    htrue hfalse hmin htight hsafe
  obtain ⟨p, hpI, hpin⟩ := (hI _).mp hpair
  have hp : p ∈ ({a, b} : Finset (Fin n)) := of_decide_eq_true hpin
  refine ⟨p, ?_, hIT p hpI, hguard p hpI⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hp

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.SafeProductTopology

lemma active_ands_false_wire_has_no_and (n : Nat) (C : Circuit) (hAO : IsAO2 n C)
    (x : Fin n → Bool)
    (hactive : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      wv n C x (n + k) = true)
    (v : Nat) (hv : v < n + C.gates.length) (hfalse : wv n C x v = false) :
    ∀ k ∈ wireCone n C v, AndSignature.isAnd C k = false := by
  classical
  intro k hk
  apply Bool.eq_false_iff.mpr
  intro hkA
  let A := (wireCone n C v).filter (fun j => AndSignature.isAnd C j = true)
  have hA : A.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hkA⟩⟩
  let g := A.max' hA
  have hgA : g ∈ A := Finset.max'_mem A hA
  obtain ⟨hgR, hgAnd⟩ := Finset.mem_filter.mp hgA
  have hreal := Finset.mem_range.mp (wireCone_real n C v hv hgR)
  have hop : (gateAt C g).op = GateOp.and := by
    cases hop : (gateAt C g).op <;> simp [AndSignature.isAnd, hop] at hgAnd ⊢
  have ht := max_and_forces_wire n C hAO g v hv hgR
    (fun j hj hjop => by
      apply Finset.le_max' A j
      exact Finset.mem_filter.mpr ⟨hj, by simp [AndSignature.isAnd, hjop]⟩)
    x (hactive g hreal hop)
  rw [hfalse] at ht
  contradiction

lemma tight_false_support_safe_partner_has_no_and {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (T : Finset (Fin n)) (w v : Nat) (hv : v < n + C.gates.length)
    (htrue : wv n C (setInput T) w = true)
    (hfalse : graphFun G ∅ (setInput T) = false)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (AndSignature.andPrefix C C.gates.length).card + 1)
    (hsafe : ∀ x, wv n C x w = true → wv n C x v = true → graphFun G ∅ x = true) :
    ∀ k ∈ wireCone n C v, AndSignature.isAnd C k = false := by
  apply active_ands_false_wire_has_no_and n C hAO (setInput T)
    (tight_all_ands_true n C hAO T w htrue hmin htight) v hv
  apply Bool.eq_false_iff.mpr
  intro hvt
  have ht := hsafe (setInput T) htrue hvt
  rw [hfalse] at ht
  contradiction

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.Outside.L_meta_2583.SingleUse

def restrictTo {n : Nat} (W : Finset (Fin n)) (x : Fin n → Bool) (v : Fin n) : Bool :=
  if v ∈ W then x v else false

lemma restrictTo_le {n : Nat} (W : Finset (Fin n)) (x : Fin n → Bool) :
    ∀ v, restrictTo W x v = true → x v = true := by
  intro v hv
  by_cases hm : v ∈ W <;> simp_all [restrictTo]

lemma restrictTo_setInput {n : Nat} (W T : Finset (Fin n)) (hT : T ⊆ W) :
    restrictTo W (setInput T) = setInput T := by
  funext v
  by_cases hm : v ∈ W
  · simp [restrictTo, hm]
  · have hnot : v ∉ T := fun hv => hm (hT hv)
    simp [restrictTo, hm, setInput, hnot]

lemma holds_restrict {n : Nat} (clauses : Finset (Finset (Fin n)))
    (W : Finset (Fin n)) (x : Fin n → Bool) :
    Holds (clauses.image (fun clause => clause ∩ W)) x ↔ Holds clauses (restrictTo W x) := by
  classical
  constructor
  · intro h clause hc
    obtain ⟨v, hv, hx⟩ := h (clause ∩ W) (Finset.mem_image.mpr ⟨clause, hc, rfl⟩)
    have hm := Finset.mem_inter.mp hv
    exact ⟨v, hm.1, by simpa only [restrictTo, ite_eq_left hm.2] using hx⟩
  · intro h clause hc
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨v, hv, hx⟩ := h old hold
    have hm : v ∈ W := by
      by_contra hn
      simp [restrictTo, hn] at hx
    exact ⟨v, Finset.mem_inter.mpr ⟨hv, hm⟩, restrictTo_le W x v hx⟩

lemma common_safe_restriction_below_graph {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false) (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true) :
    ∀ x, f (restrictTo W x) = true → graphFun G ∅ x = true := by
  intro x hx
  have hex : ∃ v ∈ W, x v = true := by
    by_contra hn
    have heq : restrictTo W x = fun _ => false := by
      funext v
      by_cases hm : v ∈ W
      · have hxf : x v = false := Bool.eq_false_iff.mpr (fun ht => hn ⟨v, hm, ht⟩)
        simp [restrictTo, hm, hxf]
      · simp [restrictTo, hm]
    rw [heq, hzero] at hx
    contradiction
  obtain ⟨v, hv, hvx⟩ := hex
  have hG := hsafe v hv (restrictTo W x) hx (by simpa [restrictTo, hv] using hvx)
  have hgraph : ∃ a b, G.Adj a b ∧ restrictTo W x a = true ∧ restrictTo W x b = true := by
    simpa [graphFun] using hG
  obtain ⟨a, b, hab, ha, hb⟩ := hgraph
  simpa [graphFun] using (show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from
    ⟨a, b, hab, restrictTo_le W x a ha, restrictTo_le W x b hb⟩)

lemma restricted_cnf_safe {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false) (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (clauses : Finset (Finset (Fin n))) (hcnf : ∀ x, f x = true ↔ Holds clauses x) :
    (clauses.image (fun clause => clause ∩ W)).card ≤ clauses.card ∧
      (∀ x, f (restrictTo W x) = true ↔ Holds (clauses.image (fun clause => clause ∩ W)) x) ∧
      ∀ x, Holds (clauses.image (fun clause => clause ∩ W)) x → graphFun G ∅ x = true := by
  refine ⟨Finset.card_image_le, ?_, ?_⟩
  · intro x
    rw [holds_restrict, hcnf]
  · intro x hx
    exact common_safe_restriction_below_graph G f hzero W hsafe x
      ((hcnf _).mpr ((holds_restrict clauses W x).mp hx))

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583

namespace MatchingCNF

lemma separated_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hzero : ∃ c : Fin k, ∀ i : Fin r, ¬ Sp c (p i))
    (hline : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sl c (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp c (p j)) :
    r + 1 ≤ k := by
  classical
  obtain ⟨c0, hc0⟩ := hzero
  choose c hc using hline
  let f : Option (Fin r) → Fin k := fun i => i.elim c0 c
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some i =>
        change c0 = c i at hab
        rcases hcover (c i) i with hp | hl
        · rw [← hab] at hp
          exact False.elim (hc0 i hp)
        · exact False.elim ((hc i).1 hl)
    | some i =>
      cases b with
      | none =>
        change c i = c0 at hab
        rcases hcover (c i) i with hp | hl
        · rw [hab] at hp
          exact False.elim (hc0 i hp)
        · exact False.elim ((hc i).1 hl)
      | some j =>
        change c i = c j at hab
        by_cases hij : i = j
        · subst j
          rfl
        · have hpi : Sp (c i) (p i) := (hcover (c i) i).resolve_right (hc i).1
          have hpj : Sp (c j) (p j) := (hcover (c j) j).resolve_right (hc j).1
          have hsep : ¬ I (p i) (l j) ∨ ¬ I (p j) (l i) := not_and_or.mp (hcross i j hij)
          rcases hsep with hsep | hsep
          · rw [hab] at hpi
            exact False.elim ((hc j).2 i hsep hpi)
          · rw [← hab] at hpj
            exact False.elim ((hc i).2 j hsep hpj)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_option, Fintype.card_fin] using hcard

lemma full_safety_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  classical
  apply separated_clause_count I p l Sp Sl hcross hcover
  · by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (true : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (false : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sp c (p i) := by
        by_contra h
        apply hnone
        exact ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inl ⟨p i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => true) (fun _ => false) hhits
    cases hb
  · intro i
    let x : Fin P → Bool := fun a => decide (¬ I a (l i))
    let y : Fin L → Bool := fun b => decide (b = l i)
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hli : Sl c (l i)
      · exact Or.inr ⟨l i, hli, by simp [y]⟩
      · have hex : ∃ j : Fin r, ¬ I (p j) (l i) ∧ Sp c (p j) := by
          by_contra h
          apply hnone
          exact ⟨c, hli, fun j hj hSp => h ⟨j, hj, hSp⟩⟩
        obtain ⟨j, hj, hSp⟩ := hex
        exact Or.inl ⟨p j, hSp, by simp [x, hj]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
    have heq : b = l i := by simpa only [y, decide_eq_true_eq] using hb
    have hnot : ¬ I a (l i) := by simpa only [x, decide_eq_true_eq] using ha
    exact hnot (heq ▸ hab)

lemma no_four_cycle_full_safety_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  apply full_safety_clause_count I p l Sp Sl ?_ hcover hsafe
  intro i j hij hcross
  have hpp : p i ≠ p j := fun h => hij (hp h)
  have hll : l i = l j := hfour (p i) (p j) hpp (l i) (l j)
    (hdiag i) hcross.2 hcross.1 (hdiag j)
  exact hij (hl hll)

lemma unified_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (S : Fin k → Fin (P + L) → Bool)
    (hcover : ∀ c : Fin k, ∀ i : Fin r,
      S c (Fin.castAdd L (p i)) = true ∨ S c (Fin.natAdd P (l i)) = true)
    (hsafe : ∀ z : Fin (P + L) → Bool,
      (∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true) →
      ∃ a b, I a b ∧ z (Fin.castAdd L a) = true ∧ z (Fin.natAdd P b) = true) :
    r + 1 ≤ k := by
  apply no_four_cycle_full_safety_clause_count I p l hp hl hdiag hfour
    (fun c a => S c (Fin.castAdd L a) = true)
    (fun c b => S c (Fin.natAdd P b) = true) hcover
  intro x y hhits
  let z : Fin (P + L) → Bool := Fin.addCases x y
  have hhits' : ∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true := by
    intro c
    rcases hhits c with ⟨a, ha, hxa⟩ | ⟨b, hb, hyb⟩
    · exact ⟨Fin.castAdd L a, ha, by simpa only [z, Fin.addCases_left] using hxa⟩
    · exact ⟨Fin.natAdd P b, hb, by simpa only [z, Fin.addCases_right] using hyb⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z hhits'
  exact ⟨a, b, hab, by simpa only [z, Fin.addCases_left] using ha,
    by simpa only [z, Fin.addCases_right] using hb⟩

end MatchingCNF

namespace StrictMatchingCNF

lemma selected_clause_injective {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (c0 : Fin k) (hc0 : ∀ i : Fin r, ¬ Sp c0 (p i))
    (c : Fin r → Fin k) (hc : ∀ i : Fin r,
      ¬ Sl (c i) (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp (c i) (p j)) :
    Function.Injective (fun i : Option (Fin r) => i.elim c0 c) := by
  classical
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i =>
      change c0 = c i at hab
      rcases hcover (c i) i with hp | hl
      · rw [← hab] at hp
        exact False.elim (hc0 i hp)
      · exact False.elim ((hc i).1 hl)
  | some i =>
    cases b with
    | none =>
      change c i = c0 at hab
      rcases hcover (c i) i with hp | hl
      · rw [hab] at hp
        exact False.elim (hc0 i hp)
      · exact False.elim ((hc i).1 hl)
    | some j =>
      change c i = c j at hab
      by_cases hij : i = j
      · subst j
        rfl
      · have hpi : Sp (c i) (p i) := (hcover (c i) i).resolve_right (hc i).1
        have hpj : Sp (c j) (p j) := (hcover (c j) j).resolve_right (hc j).1
        have hsep : ¬ I (p i) (l j) ∨ ¬ I (p j) (l i) := not_and_or.mp (hcross i j hij)
        rcases hsep with hsep | hsep
        · rw [hab] at hpi
          exact False.elim ((hc j).2 i hsep hpi)
        · rw [← hab] at hpj
          exact False.elim ((hc i).2 j hsep hpj)

lemma strict_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 3 ≤ r) : r + 2 ≤ k := by
  classical
  have hbase := MatchingCNF.no_four_cycle_full_safety_clause_count
    I p l hp hl hdiag hfour Sp Sl hcover hsafe
  by_contra hsmall
  have hkeq : k = r + 1 := by omega
  have hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)) := by
    intro i j hij hcross
    have hpp : p i ≠ p j := fun h => hij (hp h)
    have hll : l i = l j := hfour (p i) (p j) hpp (l i) (l j)
      (hdiag i) hcross.2 hcross.1 (hdiag j)
    exact hij (hl hll)
  have hzero : ∃ c : Fin k, ∀ i : Fin r, ¬ Sp c (p i) := by
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (true : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (false : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sp c (p i) := by
        by_contra h
        exact hnone ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inl ⟨p i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => true) (fun _ => false) hhits
    cases hb
  have hline : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sl c (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp c (p j) := by
    intro i
    let x : Fin P → Bool := fun a => decide (¬ I a (l i))
    let y : Fin L → Bool := fun b => decide (b = l i)
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hli : Sl c (l i)
      · exact Or.inr ⟨l i, hli, by simp [y]⟩
      · have hex : ∃ j : Fin r, ¬ I (p j) (l i) ∧ Sp c (p j) := by
          by_contra h
          exact hnone ⟨c, hli, fun j hj hSp => h ⟨j, hj, hSp⟩⟩
        obtain ⟨j, hj, hSp⟩ := hex
        exact Or.inl ⟨p j, hSp, by simp [x, hj]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
    have heq : b = l i := by simpa only [y, decide_eq_true_eq] using hb
    have hnot : ¬ I a (l i) := by simpa only [x, decide_eq_true_eq] using ha
    exact hnot (heq ▸ hab)
  have hall : ∃ c : Fin k, ∀ i : Fin r, ¬ Sl c (l i) := by
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (false : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (true : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sl c (l i) := by
        by_contra h
        exact hnone ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inr ⟨l i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => false) (fun _ => true) hhits
    cases ha
  obtain ⟨c0, hc0⟩ := hzero
  choose c hc using hline
  let f : Option (Fin r) → Fin k := fun i => i.elim c0 c
  have hinj : Function.Injective f := selected_clause_injective I p l Sp Sl hcross hcover c0 hc0 c hc
  have hsurj : Function.Surjective f := by
    by_contra hnot
    have hc := Fintype.card_lt_of_injective_not_surjective f hinj hnot
    simp only [Fintype.card_option, Fintype.card_fin] at hc
    omega
  obtain ⟨cl, hcl⟩ := hall
  have hclP : ∀ a : Fin r, Sp cl (p a) := fun a => (hcover cl a).resolve_right (hcl a)
  have hspecial : ∃ i : Fin r, (∀ a : Fin r, Sp (c i) (p a)) ∧
      (∀ a : Fin r, ¬ Sl (c i) (l a)) := by
    obtain ⟨o, ho⟩ := hsurj cl
    cases o with
    | none =>
      change c0 = cl at ho
      let a : Fin r := ⟨0, by omega⟩
      exact False.elim (hc0 a (by rw [ho]; exact hclP a))
    | some i =>
      change c i = cl at ho
      exact ⟨i, by simpa only [ho] using hclP, by simpa only [ho] using hcl⟩
  obtain ⟨i, hiP, hiL⟩ := hspecial
  have hiUniversal : ∀ a : Fin r, I (p a) (l i) := by
    intro a
    by_contra hnot
    exact (hc i).2 a hnot (hiP a)
  have hOtherNonedge : ∀ j : Fin r, j ≠ i → ∀ a : Fin r, a ≠ j → ¬ I (p a) (l j) := by
    intro j hji a haj hcross
    have hpp : p a ≠ p j := fun h => haj (hp h)
    have hll : l i = l j := hfour (p a) (p j) hpp (l i) (l j)
      (hiUniversal a) (hiUniversal j) hcross (hdiag j)
    exact hji (hl hll).symm
  have hOtherL : ∀ j : Fin r, j ≠ i → ∀ a : Fin r, a ≠ j → Sl (c j) (l a) := by
    intro j hji a haj
    exact (hcover (c j) a).resolve_left ((hc j).2 a (hOtherNonedge j hji a haj))
  have h0L : ∀ a : Fin r, Sl c0 (l a) := fun a => (hcover c0 a).resolve_left (hc0 a)
  have hremain : 1 < ((Finset.univ : Finset (Fin r)).erase i).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, t, ht, hjt⟩ := Finset.one_lt_card.mp hremain
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hti : t ≠ i := (Finset.mem_erase.mp ht).1
  let x : Fin P → Bool := fun a => decide (a = p i)
  let y : Fin L → Bool := fun b => decide (b = l j ∨ b = l t)
  have hhits : ∀ d : Fin k,
      (∃ a : Fin P, Sp d a ∧ x a = true) ∨ (∃ b : Fin L, Sl d b ∧ y b = true) := by
    intro d
    obtain ⟨o, ho⟩ := hsurj d
    cases o with
    | none =>
      change c0 = d at ho
      exact Or.inr ⟨l j, ho ▸ h0L j, by simp [y]⟩
    | some m =>
      change c m = d at ho
      by_cases hmi : m = i
      · subst m
        exact Or.inl ⟨p i, ho ▸ hiP i, by simp [x]⟩
      · by_cases hmj : m = j
        · subst m
          exact Or.inr ⟨l t, ho ▸ hOtherL j hji t (Ne.symm hjt), by simp [y]⟩
        · exact Or.inr ⟨l j, ho ▸ hOtherL m hmi j (Ne.symm hmj), by simp [y]⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
  have haeq : a = p i := by simpa only [x, decide_eq_true_eq] using ha
  have hbeq : b = l j ∨ b = l t := by simpa only [y, decide_eq_true_eq] using hb
  rcases hbeq with hb | hb
  · rw [haeq, hb] at hab
    exact hOtherNonedge j hji i (Ne.symm hji) hab
  · rw [haeq, hb] at hab
    exact hOtherNonedge t hti i (Ne.symm hti) hab

lemma unified_strict_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (S : Fin k → Fin (P + L) → Bool)
    (hcover : ∀ c : Fin k, ∀ i : Fin r,
      S c (Fin.castAdd L (p i)) = true ∨ S c (Fin.natAdd P (l i)) = true)
    (hsafe : ∀ z : Fin (P + L) → Bool,
      (∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true) →
      ∃ a b, I a b ∧ z (Fin.castAdd L a) = true ∧ z (Fin.natAdd P b) = true)
    (hr : 3 ≤ r) : r + 2 ≤ k := by
  apply strict_full_safety_matching_bound I p l hp hl hdiag hfour
    (fun c a => S c (Fin.castAdd L a) = true)
    (fun c b => S c (Fin.natAdd P b) = true) hcover ?_ hr
  intro x y hhits
  let z : Fin (P + L) → Bool := Fin.addCases x y
  have hhits' : ∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true := by
    intro c
    rcases hhits c with ⟨a, ha, hxa⟩ | ⟨b, hb, hyb⟩
    · exact ⟨Fin.castAdd L a, ha, by simpa only [z, Fin.addCases_left] using hxa⟩
    · exact ⟨Fin.natAdd P b, hb, by simpa only [z, Fin.addCases_right] using hyb⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z hhits'
  exact ⟨a, b, hab, by simpa only [z, Fin.addCases_left] using ha,
    by simpa only [z, Fin.addCases_right] using hb⟩

end StrictMatchingCNF

end PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.TightCNF

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

/-- A fully safe positive CNF accepting a matching in a bipartite graph without
  four-cycles needs at least one more clause than matching edges; for three or
  more matching edges it needs at least two more. Cross edges are permitted. -/
lemma matching_clause_bounds {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hfour : NoFourCycle G) (clauses : Finset (Finset (Fin n)))
    (p l : Fin d → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpcolor : ∀ i, color (p i) = false) (hlcolor : ∀ i, color (l i) = true)
    (hedge : ∀ i, G.Adj (p i) (l i))
    (haccept : ∀ i, Holds clauses (setInput {p i, l i}))
    (hsafe : ∀ x, Holds clauses x → graphFun G ∅ x = true) :
    d + 1 ≤ clauses.card ∧ (3 ≤ d → d + 2 ≤ clauses.card) := by
  classical
  let I : Fin n → Fin n → Prop := fun a b =>
    color a = false ∧ color b = true ∧ G.Adj a b
  let clause : Fin clauses.card → Finset (Fin n) := fun c =>
    (clauses.equivFin.symm c).val
  let Sp : Fin clauses.card → Fin n → Prop := fun c a =>
    a ∈ clause c ∧ color a = false
  let Sl : Fin clauses.card → Fin n → Prop := fun c a =>
    a ∈ clause c ∧ color a = true
  have hdiag : ∀ i, I (p i) (l i) := fun i => ⟨hpcolor i, hlcolor i, hedge i⟩
  have hfour' : ∀ a a' : Fin n, a ≠ a' → ∀ b b' : Fin n,
      I a b → I a' b → I a b' → I a' b' → b = b' := by
    intro a a' haa b b' hab ha'b hab' ha'b'
    exact Finset.card_le_one.mp (hfour a a' haa)
      b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.2.2, ha'b.2.2⟩)
      b' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab'.2.2, ha'b'.2.2⟩)
  have hcover : ∀ c i, Sp c (p i) ∨ Sl c (l i) := by
    intro c i
    obtain ⟨v, hv, hx⟩ := haccept i (clause c) (clauses.equivFin.symm c).property
    have hm : v = p i ∨ v = l i := by simpa [setInput] using hx
    rcases hm with rfl | rfl
    · exact Or.inl ⟨hv, hpcolor i⟩
    · exact Or.inr ⟨hv, hlcolor i⟩
  have hsafe' : ∀ (x y : Fin n → Bool),
      (∀ c : Fin clauses.card,
        (∃ a, Sp c a ∧ x a = true) ∨ (∃ b, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true := by
    intro x y hhits
    let z : Fin n → Bool := fun v => if color v then y v else x v
    have hz : Holds clauses z := by
      intro K hK
      let c : Fin clauses.card := clauses.equivFin ⟨K, hK⟩
      have hc : clause c = K := by simp [clause, c]
      rcases hhits c with ⟨a, ha, hxa⟩ | ⟨b, hb, hyb⟩
      · exact ⟨a, hc ▸ ha.1, by simpa [z, ha.2] using hxa⟩
      · exact ⟨b, hc ▸ hb.1, by simpa [z, hb.2] using hyb⟩
    have hex : ∃ a b, G.Adj a b ∧ z a = true ∧ z b = true := by
      simpa [graphFun] using hsafe z hz
    obtain ⟨a, b, hab, hza, hzb⟩ := hex
    have hne := hbip a b hab
    cases ha : color a with
    | false =>
      have hb : color b = true := by cases hb : color b <;> simp_all
      exact ⟨a, b, ⟨ha, hb, hab⟩, by simpa [z, ha] using hza,
        by simpa [z, hb] using hzb⟩
    | true =>
      have hb : color b = false := by cases hb : color b <;> simp_all
      exact ⟨b, a, ⟨hb, ha, hab.symm⟩, by simpa [z, hb] using hzb,
        by simpa [z, ha] using hza⟩
  exact ⟨MatchingCNF.no_four_cycle_full_safety_clause_count
      I p l hp hl hdiag hfour' Sp Sl hcover hsafe',
    StrictMatchingCNF.strict_full_safety_matching_bound
      I p l hp hl hdiag hfour' Sp Sl hcover hsafe'⟩

end PEqualNP.Outside.L_meta_2583.TightCNF

namespace PEqualNP.Outside.L_meta_2583.TightProductive

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma safe_restricted_cnf_matching_bounds {n d j : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (f : (Fin n → Bool) → Bool) (hzero : f (fun _ => false) = false)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, f x = true → x v = true → graphFun G ∅ x = true)
    (clauses : Finset (Finset (Fin n))) (hcard : clauses.card ≤ j + 1)
    (hcnf : ∀ x, f x = true ↔ TightCNF.Holds clauses x)
    (p l : Fin d → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpcolor : ∀ i, color (p i) = false) (hlcolor : ∀ i, color (l i) = true)
    (hW : ∀ i, p i ∈ W ∧ l i ∈ W) (hedge : ∀ i, G.Adj (p i) (l i))
    (haccept : ∀ i, f (setInput {p i, l i}) = true) :
    d ≤ j ∧ (3 ≤ d → d + 1 ≤ j) := by
  have hr := TightCNF.restricted_cnf_safe G f hzero W hsafe clauses hcnf
  have ha : ∀ i, TightCNF.Holds (clauses.image (fun clause => clause ∩ W))
      (setInput {p i, l i}) := by
    intro i
    apply (hr.2.1 _).mp
    rw [TightCNF.restrictTo_setInput W {p i, l i}]
    · exact haccept i
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (hW i).1
      · exact (Finset.mem_singleton.mp hv) ▸ (hW i).2
  have hb := TightCNF.matching_clause_bounds G color hbip hfour
    (clauses.image (fun clause => clause ∩ W)) p l hp hl hpcolor hlcolor hedge ha hr.2.2
  constructor
  · omega
  · intro hd
    have ht := hb.2 hd
    omega

lemma closed_tight_productive_matching_bounds {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C)
    (R : Finset Nat) (hRreal : R ⊆ Finset.range C.gates.length)
    (hRclosed : ∀ k ∈ R, ∀ b : Fin 2, opnd C k b < n ∨ opnd C k b - n ∈ R)
    (T : Finset (Fin n)) (w : Nat) (hwR : w < n ∨ w - n ∈ R)
    (htrue : wv n C (setInput T) w = true)
    (hmin : ∀ S ⊆ T, wv n C (setInput S) w = true → T ⊆ S)
    (htight : T.card = (R.filter (fun k => AndSignature.isAnd C k = true)).card + 1)
    (W : Finset (Fin n))
    (hsafe : ∀ v ∈ W, ∀ x, wv n C x w = true → x v = true → graphFun G ∅ x = true)
    (p l : Fin d → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpcolor : ∀ i, color (p i) = false) (hlcolor : ∀ i, color (l i) = true)
    (hW : ∀ i, p i ∈ W ∧ l i ∈ W) (hedge : ∀ i, G.Adj (p i) (l i))
    (haccept : ∀ i, wv n C (setInput {p i, l i}) w = true) :
    d ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card ∧
      (3 ≤ d → d + 1 ≤ (R.filter (fun k => AndSignature.isAnd C k = true)).card) := by
  obtain ⟨clauses, hcard, hcnf⟩ := TightMinterm.closed_tight_has_short_cnf n C hAO
    R hRreal hRclosed T w hwR htrue hmin htight
  apply safe_restricted_cnf_matching_bounds G color hbip hfour (fun x => wv n C x w)
    (ProductiveCircuit.wv_zero n C hAO w) W hsafe clauses (by omega) hcnf
    p l hp hl hpcolor hlcolor hW hedge haccept

lemma dirty_gateCone_ands_eq_junk {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g) :
    (gateCone n C g).filter (fun k => AndSignature.isAnd C k = true) =
      gateCone n C g ∩ junk G C := by
  apply Finset.Subset.antisymm
  · intro k hk
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hk).1,
      (Finset.mem_inter.mp (gateCone_ands_subset_junk_prefix n G C hTop g hg hk)).1⟩
  · intro k hk
    obtain ⟨hkR, hkj⟩ := Finset.mem_inter.mp hk
    have hd := (Finset.mem_filter.mp hkj).2
    exact Finset.mem_filter.mpr ⟨hkR, by simp [AndSignature.isAnd, hd.1]⟩

lemma dirty_tight_productive_matching_bounds {n d : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g) (T : Finset (Fin n))
    (htrue : gateVal n C g (setInput T) = true)
    (hmin : ∀ S ⊆ T, gateVal n C g (setInput S) = true → T ⊆ S)
    (htight : T.card = (gateCone n C g ∩ junk G C).card + 1)
    (p l : Fin d → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpcolor : ∀ i, color (p i) = false) (hlcolor : ∀ i, color (l i) = true)
    (hW : ∀ i, p i ∈ wmax G C g ∧ l i ∈ wmax G C g)
    (hedge : ∀ i, G.Adj (p i) (l i))
    (haccept : ∀ i, gateVal n C g (setInput {p i, l i}) = true) :
    d ≤ (gateCone n C g ∩ junk G C).card ∧
      (3 ≤ d → d + 1 ≤ (gateCone n C g ∩ junk G C).card) := by
  have hc := closed_tight_productive_matching_bounds G color hbip hfour C hAO
    (gateCone n C g) (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1)
    T (n + g) (Or.inr (by simpa only [Nat.add_sub_cancel_left] using gateCone_self n C g))
    htrue hmin (by rw [dirty_gateCone_ands_eq_junk G C hTop g hg]; exact htight)
    (wmax G C g) (fun v hv => (Finset.mem_filter.mp hv).2)
    p l hp hl hpcolor hlcolor hW hedge haccept
  simpa only [dirty_gateCone_ands_eq_junk G C hTop g hg] using hc

end PEqualNP.Outside.L_meta_2583.TightProductive

namespace PEqualNP.Outside.L_meta_2583.FiniteKonig

-- One side of a least cover is matched into the uncovered part of the other side (Hall).
lemma side {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (P : Finset α) (Q : Finset β)
    (hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card)
    (hcov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) :
    ∃ f : {p // p ∈ P} → β, Function.Injective f ∧ ∀ p, (p.val, f p) ∈ E ∧ f p ∉ Q := by
  let t : {p // p ∈ P} → Finset β :=
    fun p => ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
  have hall : ∀ S : Finset {p // p ∈ P}, S.card ≤ (S.biUnion t).card := by
    intro S
    have hsub : S.image Subtype.val ⊆ P := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact p.property
    have hc := hmin (P \ S.image Subtype.val) (Q ∪ S.biUnion t) (by
      intro e he
      rcases hcov e he with h | h
      · by_cases hS : e.1 ∈ S.image Subtype.val
        · right
          by_cases hq : e.2 ∈ Q
          · exact Finset.mem_union_left _ hq
          · apply Finset.mem_union_right
            obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hS
            rw [Finset.mem_biUnion]
            refine ⟨p, hp, ?_⟩
            show e.2 ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe.symm⟩, rfl⟩, hq⟩
        · left
          exact Finset.mem_sdiff.mpr ⟨h, hS⟩
      · right
        exact Finset.mem_union_left _ h)
    have h1 : (P \ S.image Subtype.val).card + (S.image Subtype.val).card = P.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have h2 : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have h3 := Finset.card_union_le Q (S.biUnion t)
    omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨f, hinj, fun p => ?_⟩
  have := hf p
  have h' : f p ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q := this
  rw [Finset.mem_sdiff] at h'
  obtain ⟨e, he, hef⟩ := Finset.mem_image.mp h'.1
  obtain ⟨heE, hep⟩ := Finset.mem_filter.mp he
  refine ⟨?_, h'.2⟩
  have : e = (p.val, f p) := Prod.ext hep hef
  rw [← this]
  exact heE

lemma konig {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) :
    ∃ (M : Finset (α × β)) (P : Finset α) (Q : Finset β), M ⊆ E ∧
      (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
  classical
  have hex : ∃ k : ℕ, ∃ (P : Finset α) (Q : Finset β),
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card = k :=
    ⟨_, E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), rfl⟩
  obtain ⟨P, Q, hcov, hk⟩ := Nat.find_spec hex
  have hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card := by
    intro P' Q' h
    rw [hk]
    exact Nat.find_min' hex ⟨P', Q', h, rfl⟩
  obtain ⟨f, hfi, hf⟩ := side E P Q hmin hcov
  have hswap : ∀ (a : α) (b : β), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · intro h
      obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
      have : e = (a, b) := by
        rw [← Prod.swap_swap e, hab]; rfl
      rw [← this]; exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(a, b), h, rfl⟩
  obtain ⟨g, hgi, hg⟩ := side (E.image Prod.swap) Q P (by
      intro Q' P' h
      have := hmin P' Q' (fun e he => by
        have := h (e.2, e.1) ((hswap e.1 e.2).mpr he)
        exact this.symm)
      omega) (by
      intro e he
      have h1 : (e.2, e.1) ∈ E := (hswap e.2 e.1).mp he
      exact (hcov _ h1).symm)
  have hg' : ∀ q : {q // q ∈ Q}, (g q, q.val) ∈ E ∧ g q ∉ P :=
    fun q => ⟨(hswap _ _).mp (hg q).1, (hg q).2⟩
  let M1 : Finset (α × β) := P.attach.image (fun p => (p.val, f p))
  let M2 : Finset (α × β) := Q.attach.image (fun q => (g q, q.val))
  have m1 : ∀ e ∈ M1, ∃ p : {p // p ∈ P}, e = (p.val, f p) := by
    intro e he
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    exact ⟨p, hp.symm⟩
  have m2 : ∀ e ∈ M2, ∃ q : {q // q ∈ Q}, e = (g q, q.val) := by
    intro e he
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
    exact ⟨q, hq.symm⟩
  refine ⟨M1 ∪ M2, P, Q, ?_, ?_, ?_, hcov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨p, rfl⟩ := m1 e h
      exact (hf p).1
    · obtain ⟨q, rfl⟩ := m2 e h
      exact (hg' q).1
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := Subtype.ext h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hg' q).2
      have h' : p.val = g q := h
      rw [← h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hg' q).2
      have h' : g q = p.val := h
      rw [h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := hgi h
      rw [this]
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := hfi h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hf p).2
      have h' : f p = q.val := h
      rw [h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hf p).2
      have h' : q.val = f p := h
      rw [← h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := Subtype.ext h
      rw [this]
  · have hd : Disjoint M1 M2 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, hq⟩ := m2 _ h2
      apply (hg' q).2
      have h' : p.val = g q := congrArg Prod.fst hq
      rw [← h']
      exact p.property
    have c1 : M1.card = P.card := by
      rw [Finset.card_image_of_injective _ (fun p p' h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_attach]
    have c2 : M2.card = Q.card := by
      rw [Finset.card_image_of_injective _ (fun q q' h => Subtype.ext (congrArg Prod.snd h)),
        Finset.card_attach]
    rw [Finset.card_union_of_disjoint hd, c1, c2]

end PEqualNP.Outside.L_meta_2583.FiniteKonig

namespace PEqualNP.Outside.L_meta_2583.FiniteKonig

lemma cover_of_injective_pair_bound {α : Type} [DecidableEq α]
    (E : Finset (α × α)) (b : Nat)
    (hbound : ∀ d : Nat, ∀ p l : Fin d → α,
      Function.Injective p → Function.Injective l →
      (∀ i, (p i, l i) ∈ E) → d ≤ b) :
    ∃ K : Finset α, K.card ≤ b ∧ ∀ e ∈ E, e.1 ∈ K ∨ e.2 ∈ K := by
  classical
  obtain ⟨M, P, Q, hME, hfirst, hsecond, hcover, hsize⟩ := konig E
  let edge : Fin M.card → α × α := fun i => (M.equivFin.symm i).val
  have hmem (i : Fin M.card) : edge i ∈ M := (M.equivFin.symm i).property
  have hinj : Function.Injective edge := by
    intro i j hij
    apply M.equivFin.symm.injective
    exact Subtype.ext hij
  have hp : Function.Injective (fun i => (edge i).1) := by
    intro i j hij
    exact hinj (hfirst _ (hmem i) _ (hmem j) hij)
  have hl : Function.Injective (fun i => (edge i).2) := by
    intro i j hij
    exact hinj (hsecond _ (hmem i) _ (hmem j) hij)
  have hb := hbound M.card (fun i => (edge i).1) (fun i => (edge i).2) hp hl
    (fun i => hME (hmem i))
  refine ⟨P ∪ Q, (Finset.card_union_le P Q).trans (hsize.trans hb), ?_⟩
  intro e he
  rcases hcover e he with hp | hq
  · exact Or.inl (Finset.mem_union_left Q hp)
  · exact Or.inr (Finset.mem_union_right P hq)

lemma cover_within_of_injective_pair_bound {α : Type} [DecidableEq α]
    (E : Finset (α × α)) (W : Finset α)
    (hW : ∀ e ∈ E, e.1 ∈ W ∧ e.2 ∈ W) (b : Nat)
    (hbound : ∀ d : Nat, ∀ p l : Fin d → α,
      Function.Injective p → Function.Injective l →
      (∀ i, (p i, l i) ∈ E) → d ≤ b) :
    ∃ K : Finset α, K ⊆ W ∧ K.card ≤ b ∧ ∀ e ∈ E, e.1 ∈ K ∨ e.2 ∈ K := by
  obtain ⟨K, hcard, hcover⟩ := cover_of_injective_pair_bound E b hbound
  refine ⟨K ∩ W, Finset.inter_subset_right, (Finset.card_le_card Finset.inter_subset_left).trans hcard, ?_⟩
  intro e he
  rcases hcover e he with hp | hl
  · exact Or.inl (Finset.mem_inter.mpr ⟨hp, (hW e he).1⟩)
  · exact Or.inr (Finset.mem_inter.mpr ⟨hl, (hW e he).2⟩)

end PEqualNP.Outside.L_meta_2583.FiniteKonig

namespace PEqualNP.Outside.L_meta_2583.FiniteKonig

lemma bipartite_cover_of_matching_bound {n : Nat}
    (H : Fin n → Fin n → Prop) [DecidableRel H]
    (color : Fin n → Bool) (hsym : ∀ u v, H u v → H v u)
    (hbip : ∀ u v, H u v → color u ≠ color v)
    (W : Finset (Fin n)) (hW : ∀ u v, H u v → u ∈ W ∧ v ∈ W)
    (b : Nat)
    (hbound : ∀ d : Nat, ∀ p l : Fin d → Fin n,
      Function.Injective p → Function.Injective l →
      (∀ i, color (p i) = false) → (∀ i, color (l i) = true) →
      (∀ i, H (p i) (l i)) → d ≤ b) :
    ∃ K : Finset (Fin n), K ⊆ W ∧ K.card ≤ b ∧ ∀ u v, H u v → u ∈ K ∨ v ∈ K := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter
    (fun e => H e.1 e.2 ∧ color e.1 = false ∧ color e.2 = true)
  have hEW : ∀ e ∈ E, e.1 ∈ W ∧ e.2 ∈ W := by
    intro e he
    exact hW e.1 e.2 (Finset.mem_filter.mp he).2.1
  have hEb : ∀ d : Nat, ∀ p l : Fin d → Fin n,
      Function.Injective p → Function.Injective l → (∀ i, (p i, l i) ∈ E) → d ≤ b := by
    intro d p l hp hl he
    exact hbound d p l hp hl (fun i => (Finset.mem_filter.mp (he i)).2.2.1)
      (fun i => (Finset.mem_filter.mp (he i)).2.2.2)
      (fun i => (Finset.mem_filter.mp (he i)).2.1)
  obtain ⟨K, hKW, hcard, hcover⟩ := cover_within_of_injective_pair_bound E W hEW b hEb
  refine ⟨K, hKW, hcard, ?_⟩
  intro u v huv
  have hcolor := hbip u v huv
  cases hu : color u <;> cases hv : color v
  · exact False.elim (hcolor (hu.trans hv.symm))
  · exact hcover (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hu, hv⟩)
  · exact (hcover (v, u)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsym u v huv, hv, hu⟩)).symm
  · exact False.elim (hcolor (hu.trans hv.symm))

end PEqualNP.Outside.L_meta_2583.FiniteKonig

namespace PEqualNP.Outside.L_meta_2583.TightProductive

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma dirty_tight_productive_cover {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g) (T : Finset (Fin n))
    (htrue : gateVal n C g (setInput T) = true)
    (hmin : ∀ S ⊆ T, gateVal n C g (setInput S) = true → T ⊆ S)
    (htight : T.card = (gateCone n C g ∩ junk G C).card + 1) :
    ∃ K : Finset (Fin n), K ⊆ wmax G C g ∧
      K.card ≤ (gateCone n C g ∩ junk G C).card ∧
      (3 ≤ K.card → K.card + 1 ≤ (gateCone n C g ∩ junk G C).card) ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g,
        G.Adj u v → gateVal n C g (setInput {u, v}) = true → u ∈ K ∨ v ∈ K := by
  classical
  let H : Fin n → Fin n → Prop := fun u v =>
    G.Adj u v ∧ u ∈ wmax G C g ∧ v ∈ wmax G C g ∧
      gateVal n C g (setInput {u, v}) = true
  let j := (gateCone n C g ∩ junk G C).card
  let b := if 3 ≤ j then j - 1 else j
  have hsym : ∀ u v, H u v → H v u := by
    intro u v h
    refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
    simpa only [Finset.pair_comm] using h.2.2.2
  have hHbip : ∀ u v, H u v → color u ≠ color v := fun u v h => hbip u v h.1
  have hHW : ∀ u v, H u v → u ∈ wmax G C g ∧ v ∈ wmax G C g :=
    fun _ _ h => ⟨h.2.1, h.2.2.1⟩
  have hbound : ∀ d : Nat, ∀ p l : Fin d → Fin n,
      Function.Injective p → Function.Injective l →
      (∀ i, color (p i) = false) → (∀ i, color (l i) = true) →
      (∀ i, H (p i) (l i)) → d ≤ b := by
    intro d p l hp hl hpc hlc hH
    have hd := dirty_tight_productive_matching_bounds G color hbip hfour C hAO hTop g hg T
      htrue hmin htight p l hp hl hpc hlc
      (fun i => ⟨(hH i).2.1, (hH i).2.2.1⟩) (fun i => (hH i).1)
      (fun i => (hH i).2.2.2)
    change d ≤ j ∧ (3 ≤ d → d + 1 ≤ j) at hd
    dsimp [b]
    split_ifs with hj
    · by_cases hd3 : 3 ≤ d
      · have := hd.2 hd3
        omega
      · omega
    · exact hd.1
  obtain ⟨K, hKW, hKcard, hcover⟩ := FiniteKonig.bipartite_cover_of_matching_bound
    H color hsym hHbip (wmax G C g) hHW b hbound
  refine ⟨K, hKW, ?_, ?_, ?_⟩
  · change K.card ≤ j
    dsimp [b] at hKcard
    split_ifs at hKcard <;> omega
  · intro hK3
    change K.card + 1 ≤ j
    dsimp [b] at hKcard
    split_ifs at hKcard <;> omega
  · intro u hu v hv huv hacc
    exact hcover u v ⟨huv, hu, hv, hacc⟩

end PEqualNP.Outside.L_meta_2583.TightProductive

namespace PEqualNP.Outside.L_meta_2583.TightMinterm

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma exists_minimal_true_subset {n : Nat} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (hS : f (setInput S) = true) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ f (setInput T) = true ∧
      (∀ U ⊆ T, f (setInput U) = true → T ⊆ U) ∧ T.card ≤ S.card := by
  classical
  have hex : ∃ k : Nat, ∃ T : Finset (Fin n), T ⊆ S ∧ f (setInput T) = true ∧ T.card = k :=
    ⟨S.card, S, Finset.Subset.refl S, hS, rfl⟩
  obtain ⟨T, hTS, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hTS, hT, ?_, Finset.card_le_card hTS⟩
  intro U hUT hU
  have hle := Nat.find_min' hex (show ∃ V : Finset (Fin n), V ⊆ S ∧
      f (setInput V) = true ∧ V.card = U.card from ⟨U, hUT.trans hTS, hU, rfl⟩)
  have heq : U = T := Finset.eq_of_subset_of_card_le hUT (by omega)
  exact heq ▸ Finset.Subset.refl U

lemma dirty_has_minimal_false_support_in_cone {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (g : Nat) (hg : IsDirty n G C g) :
    ∃ T : Finset (Fin n), graphFun G ∅ (setInput T) = false ∧
      gateVal n C g (setInput T) = true ∧
      (∀ U ⊆ T, gateVal n C g (setInput U) = true → T ⊆ U) ∧
      T.card ≤ (gateCone n C g ∩ junk G C).card + 1 := by
  classical
  obtain ⟨hgreal, x, hgx, hx⟩ := hg
  let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
  have hSx : setInput S = x := by
    funext i
    cases hi : x i <;> simp [setInput, S, hi]
  have hS : graphFun G ∅ (setInput S) = false := by rw [hSx]; exact hx
  have hSg : wv n C (setInput S) (n + g) = true := by rw [hSx]; exact hgx
  obtain ⟨B, hBS, hBg, hBcard⟩ := MintermCircuit.dirty_wire_small_support_closed n C hAO G S hS
    (gateCone n C g) (fun k hk _ b => gateCone_closed n C hAO g hgreal k hk b)
    (n + g) hSg (Or.inr (by simpa only [Nat.add_sub_cancel_left] using gateCone_self n C g))
  obtain ⟨T, hTB, hTg, hmin, hTcard⟩ := exists_minimal_true_subset (fun y => wv n C y (n + g)) B hBg
  refine ⟨T, ?_, hTg, hmin, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro ht
    rw [WmaxJunk.graph_true_iff] at ht
    obtain ⟨a, b, hab, ha, hb⟩ := ht
    have hs : graphFun G ∅ (setInput S) = true := by
      rw [WmaxJunk.graph_true_iff]
      exact ⟨a, b, hab, decide_eq_true (hBS (hTB (of_decide_eq_true ha))),
        decide_eq_true (hBS (hTB (of_decide_eq_true hb)))⟩
    rw [hS] at hs
    contradiction
  · rw [Finset.inter_comm] at hBcard
    omega

end PEqualNP.Outside.L_meta_2583.TightMinterm

namespace PEqualNP.Outside.L_meta_2583.TightProductive

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CleanedNonEdge
  PEqualNP.Outside.L_meta_2583.SingleUse PEqualNP.Outside.L_meta_2583.AncestorJunk

lemma cone_junk_card_le_prefix {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : Nat) :
    (gateCone n C g ∩ junk G C).card ≤ (junk G C ∩ Finset.range (g + 1)).card := by
  apply Finset.card_le_card
  intro k hk
  obtain ⟨hkg, hkj⟩ := Finset.mem_inter.mp hk
  exact Finset.mem_inter.mpr ⟨hkj, gateCone_prefix n C g hkg⟩

lemma exists_productive_cover_in_cone_of_guard_degree {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hdegree : ∀ l ∈ wmax G C g, color l = true → ∀ u ∈ wmax G C g,
      ∀ v ∈ wmax G C g, G.Adj l u → G.Adj l v → u = v) :
    ∃ P : Finset (Fin n), P ⊆ wmax G C g ∧
      P.card ≤ (gateCone n C g ∩ junk G C).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g, G.Adj u v →
        gateVal n C g (setInput {u, v}) = true → u ∈ P ∨ v ∈ P := by
  refine ⟨ProductiveCover.productiveCenters G color (wmax G C g) (gateVal n C g),
    ProductiveCover.productiveCenters_subset G color _ _, ?_,
    ProductiveCover.productiveCenters_cover G color hbip _ _⟩
  apply ProductiveCover.productiveCenters_card_le_cone_junk G color hbip C hAO
    (gateCone n C g) (gateCone_real n C g hg.2.1) (gateCone_closed n C hAO g hg.2.1)
    ?_ (n + g) (Or.inr (by simpa using gateCone_self n C g))
    (ProductiveCircuit.wv_zero n C hAO (n + g)) (wmax G C g)
    (fun v hv => (Finset.mem_filter.mp hv).2) hdegree
  intro k hk hka
  exact (Finset.mem_inter.mp (gateCone_ands_subset_junk_prefix n G C hTop g hg
    (Finset.mem_filter.mpr ⟨hk, hka⟩))).1

lemma dirty_three_cone_junk_productive_cover {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hsmall : (gateCone n C g ∩ junk G C).card ≤ 3) :
    ∃ K : Finset (Fin n), K ⊆ wmax G C g ∧
      K.card ≤ (gateCone n C g ∩ junk G C).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g,
        G.Adj u v → gateVal n C g (setInput {u, v}) = true → u ∈ K ∨ v ∈ K := by
  classical
  obtain ⟨T, hTF, htrue, hmin, hcard⟩ :=
    TightMinterm.dirty_has_minimal_false_support_in_cone G C hAO g hg.2
  by_cases hTsmall : T.card ≤ 3
  · obtain ⟨c, hc⟩ := ThinSupport.small_support_safe_star_orientation G color hbip hfour
      (gateVal n C g)
      (fun x y hxy hx => wv_mono n C hAO.1 hAO.2.1 x y hxy (n + g) hx)
      (wmax G C g) T (fun v hv => (Finset.mem_filter.mp hv).2) hTF htrue hTsmall
    let recolor : Fin n → Bool := fun v => decide (color v = c)
    have hbip' : ∀ a b, G.Adj a b → recolor a ≠ recolor b :=
      ProductiveCover.indicator_color_bipartite G color hbip c
    apply exists_productive_cover_in_cone_of_guard_degree G recolor hbip' C hAO hTop g hg
    intro l hl hcol u hu v hv hlu hlv
    have hcolor : color l = c := of_decide_eq_true hcol
    apply Finset.card_le_one.mp (hc l hl hcolor)
    · exact Finset.mem_filter.mpr ⟨hu, hlu⟩
    · exact Finset.mem_filter.mpr ⟨hv, hlv⟩
  · have htight : T.card = (gateCone n C g ∩ junk G C).card + 1 := by omega
    obtain ⟨K, hKW, hKcard, _hstrict, hcover⟩ := dirty_tight_productive_cover G color hbip hfour
      C hAO hTop g hg T htrue hmin htight
    exact ⟨K, hKW, hKcard, hcover⟩

lemma dirty_three_junk_productive_cover {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v) (hfour : NoFourCycle G)
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g : Nat) (hg : IsDirtyAnd n G C g)
    (hsmall : (junk G C ∩ Finset.range (g + 1)).card ≤ 3) :
    ∃ K : Finset (Fin n), K ⊆ wmax G C g ∧
      K.card ≤ (junk G C ∩ Finset.range (g + 1)).card ∧
      ∀ u ∈ wmax G C g, ∀ v ∈ wmax G C g,
        G.Adj u v → gateVal n C g (setInput {u, v}) = true → u ∈ K ∨ v ∈ K := by
  have hcone := cone_junk_card_le_prefix G C g
  obtain ⟨K, hKW, hKcard, hcover⟩ := dirty_three_cone_junk_productive_cover G color hbip hfour
    C hAO hTop g hg (hcone.trans hsmall)
  exact ⟨K, hKW, hKcard.trans hcone, hcover⟩

end PEqualNP.Outside.L_meta_2583.TightProductive
