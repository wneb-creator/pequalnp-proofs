import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.PrivateBlock

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
    (val : ℕ → (Fin n → Bool) → Bool) (M : Finset ℕ) (g extra k : ℕ) : Prop :=
  ∃ gs : List Gate, MonoList gs ∧ CleanList F gs ∧
    gs.length + (M.filter fun i => i < k).card ≤ k + (if g < k then extra else 0) ∧
    ∀ r, r < n + k → (r < n ∨ r - n ∉ M) → WireRep gs (val r)

lemma compile_private_block {n : ℕ} (N : ℕ)
    (F : (Fin n → Bool) → Bool) (val : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → GateOp) (left right : ℕ → ℕ) (M : Finset ℕ) (g extra : ℕ)
    (hbudget : extra ≤ M.card) (hMbound : ∀ k ∈ M, k < N) (hg : g < N) (hgn : g ∉ M)
    (hop : ∀ k < N, op k = GateOp.and ∨ op k = GateOp.or)
    (hlt : ∀ k < N, left k < n + k ∧ right k < n + k)
    (hvals : ∀ k < N, k ∉ M → k ≠ g → ∀ x,
      val (n + k) x = (op k).eval [val (left k) x, val (right k) x])
    (hinput : ∀ a : Fin n, ∀ x, val a.val x = x a)
    (hkeep : ∀ k < N, k ∉ M → k ≠ g →
      ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∉ M)
    (hmodule : ∀ gs : List Gate, MonoList gs → CleanList F gs →
      (∀ r, r < n + g → (r < n ∨ r - n ∉ M) → WireRep gs (val r)) →
      ∃ new : List Gate, new.length ≤ gs.length + extra + 1 ∧
        MonoList new ∧ CleanList F new ∧ WireRep new (val (n + g)) ∧
        ∀ f : (Fin n → Bool) → Bool, WireRep gs f → WireRep new f)
    (holdclean : ∀ k < N, k ∉ M → k ≠ g → op k = GateOp.and →
      ∀ x, val (n + k) x = true → F x = true)
    (out : ℕ) (hout : out < n + N) (houtun : out < n ∨ out - n ∉ M) :
    ∃ D : Circuit, D.size ≤ N ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      CleanList F D.gates ∧ ∀ x, D.eval (List.ofFn x) = val out x := by
  have hinv : ∀ k, k ≤ N → BuildInv F val M g extra k := by
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
        have hdelta : (if g < k + 1 then extra else 0) = (if g < k then extra else 0) := by
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
          obtain ⟨new, hlen, hm', hc', hnew, hpres⟩ := hmodule gs hm hc hrep
          refine ⟨new, hm', hc', ?_, ?_⟩
          · rw [count_marked_succ, if_neg hgn]
            simp only [Nat.lt_succ_self, if_true, Nat.add_zero]
            simp only [lt_self_iff_false, if_false, Nat.add_zero] at hcount
            omega
          · intro r hr hur
            by_cases he : r = n + g
            · simpa only [he] using hnew
            · exact hpres _ (hrep r (by omega) hur)
        · have hl := (hlt k hk).1
          have hr := (hlt k hk).2
          have hlrep := hrep (left k) hl (hkeep k hk hkm hkg _ (Or.inl rfl))
          have hrrep := hrep (right k) hr (hkeep k hk hkm hkg _ (Or.inr rfl))
          obtain ⟨new, hlen, hm', hc', hnew, hpres⟩ :=
            append_binary F gs hm hc (op k) (hop k hk) (val (left k)) (val (right k))
              hlrep hrrep (fun ho x hx => holdclean k hk hkm hkg ho x
                ((hvals k hk hkm hkg x).trans hx))
          have hnew' : WireRep new (val (n + k)) :=
            wireRep_congr new _ _ (fun x => (hvals k hk hkm hkg x).symm) hnew
          have hdelta : (if g < k + 1 then extra else 0) = (if g < k then extra else 0) := by
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
  refine ⟨⟨gs, r⟩, ?_, ?_, hc, hv⟩
  · change gs.length ≤ N
    omega
  · intro t ht
    obtain ⟨htop, htlen⟩ := hm t ht
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using htop, htlen⟩

end PEqualNP.Outside.L_meta_1477.PrivateBlock

namespace PEqualNP.Outside.L_meta_1477.PrivateStars

open PEqualNP.CircuitLowerBounds PrivateBlock

def orValue {n : ℕ} (vs : List (Fin n)) (x : Fin n → Bool) : Bool := vs.any x

def starValue {n : ℕ} (s : Fin n × List (Fin n)) (x : Fin n → Bool) : Bool :=
  x s.1 && orValue s.2 x

def starsValue {n : ℕ} (ss : List (Fin n × List (Fin n))) (x : Fin n → Bool) : Bool :=
  ss.any fun s => starValue s x

def starCost {n : ℕ} (ss : List (Fin n × List (Fin n))) : ℕ :=
  (ss.map fun s => s.2.length).sum

lemma append_or_inputs {n : ℕ} (F : (Fin n → Bool) → Bool) (vs : List (Fin n))
    (hne : vs ≠ []) : ∀ gs : List Gate, MonoList gs → CleanList F gs →
      (∀ v ∈ vs, WireRep gs (fun x => x v)) →
      ∃ new : List Gate, new.length + 1 = gs.length + vs.length ∧
        MonoList new ∧ CleanList F new ∧ WireRep new (orValue vs) ∧
        ∀ f : (Fin n → Bool) → Bool, WireRep gs f → WireRep new f := by
  induction vs with
  | nil => exact (hne rfl).elim
  | cons a vs ih =>
    intro gs hm hc hrep
    cases vs with
    | nil =>
      refine ⟨gs, by simp, hm, hc, ?_, fun _ h => h⟩
      apply wireRep_congr gs (fun x => x a) _ (fun x => by simp [orValue])
      exact hrep a (by simp)
    | cons b bs =>
      obtain ⟨gs1, hlen1, hm1, hc1, hr1, hp1⟩ :=
        ih (by simp) gs hm hc (fun v hv => hrep v (List.mem_cons_of_mem a hv))
      obtain ⟨new, hlen, hm2, hc2, hr2, hp2⟩ :=
        append_binary F gs1 hm1 hc1 GateOp.or (Or.inr rfl)
          (fun x => x a) (orValue (b :: bs)) (hp1 _ (hrep a (by simp))) hr1
          (by intro h; cases h)
      refine ⟨new, ?_, hm2, hc2, ?_, fun f hf => hp2 f (hp1 f hf)⟩
      · simp only [List.length_cons] at hlen1 ⊢
        omega
      · apply wireRep_congr new _ _ (fun x => ?_) hr2
        simp [GateOp.eval, orValue]

lemma append_star {n : ℕ} (F : (Fin n → Bool) → Bool)
    (gs : List Gate) (hm : MonoList gs) (hc : CleanList F gs)
    (s : Fin n × List (Fin n)) (hne : s.2 ≠ [])
    (hrep : ∀ v : Fin n, WireRep gs (fun x => x v))
    (hclean : ∀ x, starValue s x = true → F x = true) :
    ∃ new : List Gate, new.length = gs.length + s.2.length ∧
      MonoList new ∧ CleanList F new ∧ WireRep new (starValue s) ∧
      ∀ f : (Fin n → Bool) → Bool, WireRep gs f → WireRep new f := by
  obtain ⟨gs1, hlen1, hm1, hc1, hr1, hp1⟩ :=
    append_or_inputs F s.2 hne gs hm hc (fun v _ => hrep v)
  obtain ⟨new, hlen, hm2, hc2, hr2, hp2⟩ :=
    append_binary F gs1 hm1 hc1 GateOp.and (Or.inl rfl)
      (fun x => x s.1) (orValue s.2) (hp1 _ (hrep s.1)) hr1 (by
        intro _ x hx
        apply hclean x
        simpa only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq, starValue] using hx)
  refine ⟨new, by omega, hm2, hc2, ?_, fun f hf => hp2 f (hp1 f hf)⟩
  apply wireRep_congr new _ _ (fun x => ?_) hr2
  simp [GateOp.eval, starValue]

lemma append_stars {n : ℕ} (F : (Fin n → Bool) → Bool)
    (ss : List (Fin n × List (Fin n))) (hne : ss ≠ [])
    (hstars : ∀ s ∈ ss, s.2 ≠ [])
    (hclean : ∀ s ∈ ss, ∀ x, starValue s x = true → F x = true) :
    ∀ gs : List Gate, MonoList gs → CleanList F gs →
      (∀ v : Fin n, WireRep gs (fun x => x v)) →
      ∃ new : List Gate, new.length + 1 = gs.length + starCost ss + ss.length ∧
        MonoList new ∧ CleanList F new ∧ WireRep new (starsValue ss) ∧
        ∀ f : (Fin n → Bool) → Bool, WireRep gs f → WireRep new f := by
  induction ss with
  | nil => exact (hne rfl).elim
  | cons s ss ih =>
    intro gs hm hc hrep
    obtain ⟨gs1, hlen1, hm1, hc1, hr1, hp1⟩ :=
      append_star F gs hm hc s (hstars s (by simp)) hrep (hclean s (by simp))
    cases ss with
    | nil =>
      refine ⟨gs1, ?_, hm1, hc1, ?_, hp1⟩
      · simp [starCost, hlen1]
      · apply wireRep_congr gs1 _ _ (fun x => by simp [starsValue]) hr1
    | cons t ts =>
      obtain ⟨gs2, hlen2, hm2, hc2, hr2, hp2⟩ := ih (by simp)
        (fun u hu => hstars u (List.mem_cons_of_mem s hu))
        (fun u hu => hclean u (List.mem_cons_of_mem s hu))
        gs1 hm1 hc1 (fun v => hp1 _ (hrep v))
      obtain ⟨new, hlen3, hm3, hc3, hr3, hp3⟩ :=
        append_binary F gs2 hm2 hc2 GateOp.or (Or.inr rfl)
          (starValue s) (starsValue (t :: ts)) (hp2 _ hr1) hr2 (by intro h; cases h)
      refine ⟨new, ?_, hm3, hc3, ?_, fun f hf => hp3 f (hp2 f (hp1 f hf))⟩
      · simp only [starCost, List.map_cons, List.sum_cons, List.length_cons] at hlen2 ⊢
        omega
      · apply wireRep_congr new _ _ (fun x => ?_) hr3
        simp [GateOp.eval, starsValue]

end PEqualNP.Outside.L_meta_1477.PrivateStars

namespace PEqualNP.Outside.L_meta_1477.PrivateStars

open PEqualNP.CircuitLowerBounds PrivateBlock

lemma compile_private_stars {n : ℕ} (N : ℕ)
    (F : (Fin n → Bool) → Bool) (val : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → GateOp) (left right : ℕ → ℕ) (M : Finset ℕ) (g : ℕ)
    (hMbound : ∀ k ∈ M, k < N) (hg : g < N) (hgn : g ∉ M)
    (hop : ∀ k < N, op k = GateOp.and ∨ op k = GateOp.or)
    (hlt : ∀ k < N, left k < n + k ∧ right k < n + k)
    (hvals : ∀ k < N, k ∉ M → k ≠ g → ∀ x,
      val (n + k) x = (op k).eval [val (left k) x, val (right k) x])
    (hinput : ∀ a : Fin n, ∀ x, val a.val x = x a)
    (hkeep : ∀ k < N, k ∉ M → k ≠ g →
      ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∉ M)
    (ss : List (Fin n × List (Fin n))) (hne : ss ≠ [])
    (hstars : ∀ s ∈ ss, s.2 ≠ [])
    (hcost : starCost ss + ss.length ≤ M.card + 2)
    (hspecial : ∀ x, val (n + g) x = starsValue ss x)
    (hstarclean : ∀ s ∈ ss, ∀ x, starValue s x = true → F x = true)
    (holdclean : ∀ k < N, k ∉ M → k ≠ g → op k = GateOp.and →
      ∀ x, val (n + k) x = true → F x = true)
    (out : ℕ) (hout : out < n + N) (houtun : out < n ∨ out - n ∉ M) :
    ∃ D : Circuit, D.size ≤ N ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      CleanList F D.gates ∧ ∀ x, D.eval (List.ofFn x) = val out x := by
  apply compile_private_block N F val op left right M g M.card le_rfl hMbound hg hgn hop hlt
    hvals hinput hkeep ?_ holdclean out hout houtun
  intro gs hm hc hrep
  have hprim (a : Fin n) : WireRep gs (fun x => x a) := by
    apply wireRep_congr gs (val a.val) _ (hinput a)
    exact hrep a.val (by have := a.isLt; omega) (Or.inl a.isLt)
  obtain ⟨new, hlen, hmnew, hcnew, hrnew, hpres⟩ :=
    append_stars F ss hne hstars hstarclean gs hm hc hprim
  refine ⟨new, by omega, hmnew, hcnew, ?_, hpres⟩
  exact wireRep_congr new _ _ (fun x => (hspecial x).symm) hrnew

end PEqualNP.Outside.L_meta_1477.PrivateStars

namespace PEqualNP.Outside.L_meta_1477.StarDecomposition

lemma directed_stars {n : ℕ} (R : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : R.Nonempty) (hT : ∀ e ∈ R, e.1 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum = R.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R) ∧
      (∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2) := by
  classical
  let S := R.image Prod.fst
  let N : Fin n → Finset (Fin n) := fun c => (R.filter (fun e => e.1 = c)).image Prod.snd
  let ss : List (Fin n × List (Fin n)) := S.toList.map (fun c => (c, (N c).toList))
  have hNm (c v : Fin n) : v ∈ N c ↔ (c, v) ∈ R := by
    constructor
    · intro hv
      obtain ⟨⟨a, b⟩, he, hv⟩ := Finset.mem_image.mp hv
      obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
      dsimp at ha hv
      subst a
      subst b
      exact he
    · intro hv
      exact Finset.mem_image.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨hv, rfl⟩, rfl⟩
  have hNcard (c : Fin n) : (N c).card = (R.filter (fun e => e.1 = c)).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  have hlen : ss.length = S.card := by simp [ss]
  have hScard : S.card ≤ T.card := Finset.card_le_card (by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact hT e he)
  have hssne : ss ≠ [] := by
    intro he
    obtain ⟨e, heR⟩ := hne
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e.1, Finset.mem_image.mpr ⟨e, heR, rfl⟩⟩
    simp only [he, List.length_nil] at hlen
    omega
  have hentry : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R := by
    intro s hs v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact (hNm c v).mp (by simpa using hv)
  have hall : ∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2 := by
    intro e he
    refine ⟨(e.1, (N e.1).toList), ?_, rfl, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨e.1, Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
    · exact Finset.mem_toList.mpr ((hNm e.1 e.2).mpr he)
  have hnonempty : ∀ s ∈ ss, s.2 ≠ [] := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hcS : c ∈ S := by simpa using hc
    obtain ⟨e, he, hc⟩ := Finset.mem_image.mp hcS
    have hmem : e.2 ∈ (N c).toList := Finset.mem_toList.mpr ((hNm c e.2).mpr (by rw [← hc]; exact he))
    intro hn
    change (N c).toList = [] at hn
    rw [hn] at hmem
    simp at hmem
  have hcost : (ss.map fun s => s.2.length).sum = R.card := by
    simp only [ss, List.map_map, Function.comp_def, Finset.length_toList]
    rw [Finset.sum_map_toList]
    simp_rw [hNcard]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  exact ⟨ss, hssne, hnonempty, hlen.trans_le hScard, hcost, hentry, hall⟩

lemma oriented_stars {n : ℕ} (E : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : E.Nonempty) (hT : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum ≤ E.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)) := by
  classical
  let orient : (Fin n × Fin n) → (Fin n × Fin n) := fun e =>
    if e.1 ∈ T then e else (e.2, e.1)
  let R := E.image orient
  have hRne : R.Nonempty := Finset.Nonempty.image hne orient
  have hRT : ∀ e ∈ R, e.1 ∈ T := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    by_cases hh : f.1 ∈ T
    · simpa [orient, hh] using hh
    · simpa [orient, hh] using (hT f hf).resolve_left hh
  obtain ⟨ss, hss, hneigh, hlen, hcost, hentry, hall⟩ := directed_stars R T hRne hRT
  have hedges : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E := by
    intro s hs v hv
    obtain ⟨e, he, hor⟩ := Finset.mem_image.mp (hentry s hs v hv)
    by_cases hh : e.1 ∈ T
    · have heq : e = (s.1, v) := by simpa [orient, hh] using hor
      exact Or.inl (heq ▸ he)
    · have heq : (e.2, e.1) = (s.1, v) := by simpa [orient, hh] using hor
      have heq' : e = (v, s.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      exact Or.inr (heq' ▸ he)
  refine ⟨ss, hss, hneigh, hlen, hcost.trans_le (Finset.card_image_le), hedges, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hxs, v, hv, hxv⟩
    rcases hedges s hs v hv with he | he
    · exact ⟨(s.1, v), he, hxs, hxv⟩
    · exact ⟨(v, s.1), he, hxv, hxs⟩
  · rintro ⟨e, he, hx1, hx2⟩
    have heR : orient e ∈ R := Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨s, hs, hs1, hv⟩ := hall (orient e) heR
    refine ⟨s, hs, ?_, (orient e).2, hv, ?_⟩
    · rw [hs1]
      by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx1
      · simpa [orient, hh] using hx2
    · by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx2
      · simpa [orient, hh] using hx1

end PEqualNP.Outside.L_meta_1477.StarDecomposition

namespace PEqualNP.Outside.L_meta_1477.PrivateStars

open PEqualNP.CircuitLowerBounds PrivateBlock

lemma compile_private_edges {n : ℕ} (N : ℕ)
    (F : (Fin n → Bool) → Bool) (val : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → GateOp) (left right : ℕ → ℕ) (M : Finset ℕ) (g : ℕ)
    (hMbound : ∀ k ∈ M, k < N) (hg : g < N) (hgn : g ∉ M)
    (hop : ∀ k < N, op k = GateOp.and ∨ op k = GateOp.or)
    (hlt : ∀ k < N, left k < n + k ∧ right k < n + k)
    (hvals : ∀ k < N, k ∉ M → k ≠ g → ∀ x,
      val (n + k) x = (op k).eval [val (left k) x, val (right k) x])
    (hinput : ∀ a : Fin n, ∀ x, val a.val x = x a)
    (hkeep : ∀ k < N, k ∉ M → k ≠ g →
      ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∉ M)
    (E : Finset (Fin n × Fin n)) (T : Finset (Fin n)) (hE : E.Nonempty)
    (hcover : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T)
    (hcost : E.card + T.card ≤ M.card + 2)
    (hspecial : ∀ x, val (n + g) x = decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true))
    (hedgeclean : ∀ e ∈ E, ∀ x, x e.1 = true → x e.2 = true → F x = true)
    (holdclean : ∀ k < N, k ∉ M → k ≠ g → op k = GateOp.and →
      ∀ x, val (n + k) x = true → F x = true)
    (out : ℕ) (hout : out < n + N) (houtun : out < n ∨ out - n ∉ M) :
    ∃ D : Circuit, D.size ≤ N ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      CleanList F D.gates ∧ ∀ x, D.eval (List.ofFn x) = val out x := by
  obtain ⟨ss, hsne, hstars, hlen, hsum, hedges, hsem⟩ :=
    StarDecomposition.oriented_stars E T hE hcover
  apply compile_private_stars N F val op left right M g hMbound hg hgn hop hlt hvals hinput
    hkeep ss hsne hstars ?_ ?_ ?_ holdclean out hout houtun
  · change (ss.map fun s => s.2.length).sum + ss.length ≤ M.card + 2
    omega
  · intro x
    exact (hspecial x).trans (hsem x).symm
  · intro s hs x hx
    have hp : x s.1 = true ∧ ∃ v ∈ s.2, x v = true := by
      simpa only [starValue, orValue, Bool.and_eq_true, List.any_eq_true] using hx
    obtain ⟨v, hv, hxv⟩ := hp.2
    rcases hedges s hs v hv with he | he
    · exact hedgeclean (s.1, v) he x hp.1 hxv
    · exact hedgeclean (v, s.1) he x hxv hp.1

end PEqualNP.Outside.L_meta_1477.PrivateStars
