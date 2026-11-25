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
