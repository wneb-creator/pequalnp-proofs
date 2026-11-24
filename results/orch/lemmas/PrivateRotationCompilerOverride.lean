import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.PrivateRotation

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]


def WireRep {n : ℕ} (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ r : ℕ, r < n + gs.length ∧ ∀ x, (W gs x).getD r false = f x

def MonoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def CleanList {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) : Prop :=
  ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
    ∀ x, (W gs x).getD (n + i) false = true → F x = true

lemma wireRep_snoc {n : ℕ} (gs : List Gate) (g : Gate)
    (f : (Fin n → Bool) → Bool) (hf : WireRep gs f) : WireRep (gs ++ [g]) f := by
  obtain ⟨r, hr, hv⟩ := hf
  refine ⟨r, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
  intro x
  rw [W_val, if_neg (by omega)]
  exact hv x

lemma append_binary {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hm : MonoList gs) (hc : CleanList F gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (f h : (Fin n → Bool) → Bool) (hf : WireRep gs f) (hh : WireRep gs h)
    (hclean : op = GateOp.and → ∀ x, op.eval [f x, h x] = true → F x = true) :
    ∃ new : List Gate, new.length = gs.length + 1 ∧ MonoList new ∧ CleanList F new ∧
      WireRep new (fun x => op.eval [f x, h x]) ∧
      ∀ q : (Fin n → Bool) → Bool, WireRep gs q → WireRep new q := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨s, hs, hhs⟩ := hh
  let g : Gate := ⟨op, [r, s]⟩
  have hlast (x : Fin n → Bool) :
      (W (gs ++ [g]) x).getD (n + gs.length) false = op.eval [f x, h x] := by
    rw [W_val, if_pos rfl]
    simp only [g, List.map_cons, List.map_nil, hfr x, hhs x]
  refine ⟨gs ++ [g], by simp, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hm t ht
    · have he : t = g := List.mem_singleton.mp ht
      subst t
      exact ⟨hop, by simp [g]⟩
  · intro i hi hiop x hx
    by_cases hlt : i < gs.length
    · have hgate : (gs ++ [g]).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
        simp [List.getD, List.getElem?_append_left hlt]
      rw [hgate] at hiop
      rw [W_val, if_neg (by omega)] at hx
      exact hc i hlt hiop x hx
    · have he : i = gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      have hgate : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD]
      rw [hgate] at hiop
      rw [hlast x] at hx
      exact hclean hiop x hx
  · exact ⟨n + gs.length, by simp, hlast⟩
  · intro q hq
    exact wireRep_snoc gs g q hq

lemma count_marked_succ (M : Finset ℕ) (k : ℕ) :
    (M.filter fun i => i < k + 1).card =
      (M.filter fun i => i < k).card + if k ∈ M then 1 else 0 := by
  by_cases hk : k ∈ M
  · have he : M.filter (fun i => i < k + 1) = insert k (M.filter fun i => i < k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hil⟩
        by_cases he : i = k
        · exact Or.inl he
        · exact Or.inr ⟨hi, by omega⟩
      · rintro (rfl | ⟨hi, hil⟩)
        · exact ⟨hk, by omega⟩
        · exact ⟨hi, by omega⟩
    rw [he, Finset.card_insert_of_notMem (by simp), if_pos hk]
  · have he : M.filter (fun i => i < k + 1) = M.filter fun i => i < k := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hil⟩
        have hne : i ≠ k := fun he => hk (he ▸ hi)
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hil⟩
        exact ⟨hi, by omega⟩
    rw [he, if_neg hk, Nat.add_zero]


lemma wireRep_congr {n : ℕ} (gs : List Gate) (f h : (Fin n → Bool) → Bool)
    (he : ∀ x, f x = h x) (hf : WireRep gs f) : WireRep gs h := by
  obtain ⟨r, hr, hv⟩ := hf
  exact ⟨r, hr, fun x => (hv x).trans (he x)⟩

def BuildInv {n : ℕ} (F : (Fin n → Bool) → Bool)
    (val : ℕ → (Fin n → Bool) → Bool) (M : Finset ℕ) (g k : ℕ) : Prop :=
  ∃ gs : List Gate, MonoList gs ∧ CleanList F gs ∧
    gs.length + (M.filter fun i => i < k).card = k + (if g < k then 1 else 0) ∧
    ∀ r, r < n + k → (r < n ∨ r - n ∉ M) → WireRep gs (val r)

lemma compile_private_rotation {n : ℕ} (N : ℕ)
    (F : (Fin n → Bool) → Bool) (val : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → GateOp) (left right : ℕ → ℕ) (M : Finset ℕ) (g : ℕ)
    (hM : M.Nonempty) (hMbound : ∀ k ∈ M, k < N) (hg : g < N) (hgn : g ∉ M)
    (hop : ∀ k < N, op k = GateOp.and ∨ op k = GateOp.or)
    (hlt : ∀ k < N, left k < n + k ∧ right k < n + k)
    (hvals : ∀ k < N, k ≠ g → ∀ x, val (n + k) x = (op k).eval [val (left k) x, val (right k) x])
    (hinput : ∀ a : Fin n, ∀ x, val a.val x = x a)
    (hkeep : ∀ k < N, k ∉ M → k ≠ g →
      ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∉ M)
    (q : ℕ) (hq : q < n + g) (hqun : q < n ∨ q - n ∉ M) (a z : Fin n)
    (hspecial : ∀ x, val (n + g) x = (x z || (x a && val q x)))
    (holdclean : ∀ k < N, k ≠ g → op k = GateOp.and → ∀ x, val (n + k) x = true → F x = true)
    (hnewclean : ∀ x, x a = true → val q x = true → F x = true)
    (out : ℕ) (hout : out < n + N) (houtun : out < n ∨ out - n ∉ M) :
    ∃ D : Circuit, D.size ≤ N ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      CleanList F D.gates ∧ ∀ x, D.eval (List.ofFn x) = val out x := by
  have hinv : ∀ k, k ≤ N → BuildInv F val M g k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], by simp [MonoList], by simp [CleanList], by simp, ?_⟩
      intro r hr _
      have hrn : r < n := by omega
      refine ⟨r, by simpa using hrn, ?_⟩
      intro x
      have he : (W [] x).getD r false = x ⟨r, hrn⟩ := by
        change (List.ofFn x).getD r false = _
        rw [List.getD_eq_getElem _ _ (by simpa using hrn)]
        simp
      exact he.trans (hinput ⟨r, hrn⟩ x).symm
    | succ k ih =>
      intro hkN
      have hk : k < N := by omega
      obtain ⟨gs, hm, hc, hcount, hrep⟩ := ih (by omega)
      by_cases hkm : k ∈ M
      · have hkg : k ≠ g := fun he => hgn (he ▸ hkm)
        have hdelta : (if g < k + 1 then 1 else 0) = (if g < k then 1 else 0) := by
          split_ifs <;> omega
        refine ⟨gs, hm, hc, ?_, ?_⟩
        · rw [count_marked_succ, if_pos hkm, hdelta]
          omega
        · intro r hr hur
          by_cases he : r = n + k
          · subst r
            rcases hur with hri | hrm
            · omega
            · exact (hrm (by simpa using hkm)).elim
          · exact hrep r (by omega) hur
      · by_cases hkg : k = g
        · subst k
          have har : WireRep gs (fun x => x a) :=
            wireRep_congr gs _ _ (hinput a) (hrep a.val (by have := a.isLt; omega) (Or.inl a.isLt))
          have hzr : WireRep gs (fun x => x z) :=
            wireRep_congr gs _ _ (hinput z) (hrep z.val (by have := z.isLt; omega) (Or.inl z.isLt))
          obtain ⟨gs1, hl1, hm1, hc1, hr1, hp1⟩ :=
            append_binary F gs hm hc GateOp.and (Or.inl rfl) (fun x => x a) (val q)
              har (hrep q hq hqun) (by
                intro _ x hx
                simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true,
                  id_eq, Bool.and_eq_true] at hx
                exact hnewclean x hx.1 hx.2)
          have hinner : WireRep gs1 (fun x => x a && val q x) :=
            wireRep_congr gs1 _ _ (fun x => by simp [GateOp.eval]) hr1
          obtain ⟨gs2, hl2, hm2, hc2, hr2, hp2⟩ :=
            append_binary F gs1 hm1 hc1 GateOp.or (Or.inr rfl) (fun x => x z)
              (fun x => x a && val q x) (hp1 _ hzr) hinner (by intro h; cases h)
          have hnew : WireRep gs2 (val (n + g)) :=
            wireRep_congr gs2 _ _ (fun x => by simp only [GateOp.eval, List.any_cons,
              List.any_nil, Bool.or_false, id_eq]; exact (hspecial x).symm) hr2
          refine ⟨gs2, hm2, hc2, ?_, ?_⟩
          · rw [count_marked_succ, if_neg hgn]
            simp only [Nat.lt_succ_self, if_true, Nat.add_zero]
            simp only [lt_self_iff_false, if_false, Nat.add_zero] at hcount
            omega
          · intro r hr hur
            by_cases he : r = n + g
            · simpa only [he] using hnew
            · exact hp2 _ (hp1 _ (hrep r (by omega) hur))
        · have hl := (hlt k hk).1
          have hr := (hlt k hk).2
          have hlrep := hrep (left k) hl (hkeep k hk hkm hkg _ (Or.inl rfl))
          have hrrep := hrep (right k) hr (hkeep k hk hkm hkg _ (Or.inr rfl))
          obtain ⟨new, hlen, hm', hc', hnew, hpres⟩ :=
            append_binary F gs hm hc (op k) (hop k hk) (val (left k)) (val (right k))
              hlrep hrrep (fun ho x hx => holdclean k hk hkg ho x ((hvals k hk hkg x).trans hx))
          have hnew' : WireRep new (val (n + k)) :=
            wireRep_congr new _ _ (fun x => (hvals k hk hkg x).symm) hnew
          have hdelta : (if g < k + 1 then 1 else 0) = (if g < k then 1 else 0) := by
            split_ifs <;> omega
          refine ⟨new, hm', hc', ?_, ?_⟩
          · rw [count_marked_succ, if_neg hkm, hdelta]
            omega
          · intro r hr hur
            by_cases he : r = n + k
            · simpa only [he] using hnew'
            · exact hpres _ (hrep r (by omega) hur)
  obtain ⟨gs, hm, hc, hcount, hrep⟩ := hinv N le_rfl
  obtain ⟨r, hr, hv⟩ := hrep out hout houtun
  have hfilter : M.filter (fun i => i < N) = M := Finset.filter_eq_self.mpr hMbound
  rw [hfilter, if_pos hg] at hcount
  have hpos := Finset.card_pos.mpr hM
  refine ⟨⟨gs, r⟩, ?_, ?_, hc, hv⟩
  · change gs.length ≤ N
    omega
  · intro t ht
    obtain ⟨htop, htlen⟩ := hm t ht
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using htop, htlen⟩

end PEqualNP.Outside.L_meta_1477.PrivateRotation
