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

namespace PEqualNP.Outside.L_meta_1477.GateReplacement

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

lemma bool_le_iff_true (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    op.eval (ins.map f) ≤ op.eval (ins.map g) := by
  rw [bool_le_iff_true]
  intro hf
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true] at hf ⊢
    intro b hb
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact (bool_le_iff_true _ _).mp (h i)
      (hf (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp only [GateOp.eval, List.any_eq_true] at hf ⊢
    rcases hf with ⟨b, hb, hbt⟩
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩,
      (bool_le_iff_true _ _).mp (h i) hbt⟩

lemma step_mono (w v : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : w.length = v.length) (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (step w g).getD i false ≤ (step v g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ (by omega)]
    exact h i
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ (heq.trans hlen)]
      exact op_mono g.op hop _ _ _ h
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (gs.foldl step w).getD i false ≤ (gs.foldl step v).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
    · simp only [step_len, hlen]
    · exact step_mono w v g (hgs g (by simp)) hlen h

lemma fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_len]; omega), step_lt _ _ _ hi]

def zeroGate : Gate := ⟨GateOp.or, []⟩

lemma step_zero_le (w : List Bool) (g : Gate) :
    ∀ i, (step w zeroGate).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      simp [zeroGate, GateOp.eval]
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]


def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma step_replace_le (w : List Bool) (g h : Gate)
    (hle : gateValue w h ≤ gateValue w g) :
    ∀ i, (step w h).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      exact hle
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma set_gate_le (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate)
    (hle : gateValue ((gs.take k).foldl step w) h ≤
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ∀ i, ((gs.set k h).foldl step w).getD i false ≤
      (gs.foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · apply step_replace_le
        simpa using hle
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k
          (by simpa using hle)

lemma set_gate_eq_of_local_eq (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (heq : gateValue ((gs.take k).foldl step w) h =
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    (gs.set k h).foldl step w = gs.foldl step w := by
  induction gs generalizing w k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      have hs : step w h = step w g := by
        have he : gateValue w h = gateValue w g := by simpa using heq
        exact congrArg (fun b => w ++ [b]) he
      simp only [List.set_cons_zero, List.foldl_cons, hs]
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (step w g) k (by simpa using heq)

lemma set_zero_le_set_gate (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate) :
    ∀ i, ((gs.set k zeroGate).foldl step w).getD i false ≤
      ((gs.set k h).foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · exact step_zero_le w h
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k

lemma set_gate_true_of_sensitive_preserved (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k out : ℕ) (h : Gate)
    (hout : (gs.foldl step w).getD out false = true)
    (hsensitive : ((gs.set k zeroGate).foldl step w).getD out false = false →
      gateValue ((gs.take k).foldl step w) h =
        gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ((gs.set k h).foldl step w).getD out false = true := by
  cases hz : ((gs.set k zeroGate).foldl step w).getD out false with
  | false => rw [set_gate_eq_of_local_eq gs w k h (hsensitive hz)]; exact hout
  | true => exact Bool.le_iff_imp.mp (set_zero_le_set_gate gs hgs w k h out) hz

def replaceGate (C : Circuit) (k : ℕ) (g : Gate) : Circuit :=
  { C with gates := C.gates.set k g }

lemma replaceGate_size (C : Circuit) (k : ℕ) (g : Gate) :
    (replaceGate C k g).size = C.size := by
  simp [replaceGate, Circuit.size]


lemma list_set_all {α : Type*} (P : α → Prop) (gs : List α) (k : ℕ) (h : α)
    (hgs : ∀ g ∈ gs, P g) (hh : P h) : ∀ g ∈ gs.set k h, P g := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hh
      · exact hgs a (List.mem_cons_of_mem _ ha)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hgs _ (by simp)
      · exact ih k (fun b hb => hgs b (List.mem_cons_of_mem _ hb)) a ha

lemma replaceGate_monotone2 (C : Circuit) (k : ℕ) (g : Gate)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 (replaceGate C k g) :=
  list_set_all _ C.gates k g hC hg

lemma circuitFun_monotone {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (PEqualNP.MetaComplexity.circuitFun n C) := by
  intro x y hxy
  apply fold_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using hxy ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]

lemma pairInput_le {n : ℕ} {u v : Fin n} {x : Fin n → Bool}
    (hu : x u = true) (hv : x v = true) : PEqualNP.EdgeOwnership.pairInput u v ≤ x := by
  intro i
  rw [bool_le_iff_true]
  intro hi
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma graph_eq_of_le_and_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (hle : ∀ x, f x ≤ PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (hpairs : ∀ u v, G.Adj u v → f (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply le_antisymm (hle x)
  rw [bool_le_iff_true]
  intro hg
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun] at hg
  rcases hg with ⟨u, v, huv, hu, hv⟩
  exact (bool_le_iff_true _ _).mp (hm (pairInput_le hu hv)) (hpairs u v huv)

lemma replaceGate_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) (h : Gate)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hh : h.op = GateOp.and ∨ h.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hle : ∀ x : Fin n → Bool,
      gateValue ((C.gates.take k).foldl step (List.ofFn x)) h ≤
        gateValue ((C.gates.take k).foldl step (List.ofFn x)) (C.gates.getD k zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD C.output false = false →
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) h =
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) (C.gates.getD k zeroGate)) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k h) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · exact circuitFun_monotone (replaceGate C k h) (list_set_all _ C.gates k h hC hh)
  · intro x
    rw [← hgraph]
    exact set_gate_le C.gates hC (List.ofFn x) k h (hle x) C.output
  · intro u v huv
    apply set_gate_true_of_sensitive_preserved C.gates hC
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) k C.output h
    · change PEqualNP.MetaComplexity.circuitFun n C
        (PEqualNP.EdgeOwnership.pairInput u v) = true
      rw [hgraph]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
        false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    · exact hkeep u v huv


lemma prefix_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (a : Fin n) :
    ((gs.take k).foldl step (List.ofFn x)).getD a.val false = x a := by
  rw [fold_preserves _ _ _ (by simpa using a.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp

lemma set_gate_value_at (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (hk : k < gs.length) :
    ((gs.set k h).foldl step w).getD (w.length + k) false =
      gateValue ((gs.take k).foldl step w) h := by
  induction gs generalizing w k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons, Nat.add_zero, List.take_zero,
        List.foldl_nil]
      rw [fold_preserves _ _ _ (by rw [step_len]; omega), step_last _ _ _ rfl]
      rfl
    | succ k =>
      have hi := ih (step w g) k (by simpa using hk)
      simpa only [List.set_cons_succ, List.foldl_cons, List.take_succ_cons,
        step_len, Nat.add_assoc, Nat.add_comm 1 k] using hi

lemma replace_and_with_input_graph_correct {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k u v : ℕ) (a : Fin n)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hgate : C.gates.getD k zeroGate = ⟨GateOp.and, [u, v]⟩)
    (hdom : ∀ x : Fin n → Bool,
      x a ≤ ((C.gates.take k).foldl step (List.ofFn x)).getD u false)
    (hkeep : ∀ p q : Fin n, G.Adj p q →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput p q))).getD C.output false = false →
      PEqualNP.EdgeOwnership.pairInput p q a = true) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply replaceGate_graph_correct G C k _ hC (Or.inl rfl) hgraph
  · intro x
    simp only [gateValue, hgate, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, prefix_input]
    apply Bool.le_iff_imp.mpr
    intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨Bool.le_iff_imp.mp (hdom x) h.1, h.2⟩
  · intro p q hpq hz
    have ha := hkeep p q hpq hz
    have hu := Bool.le_iff_imp.mp (hdom (PEqualNP.EdgeOwnership.pairInput p q)) ha
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, Bool.and_true, prefix_input, ha, hu]

lemma replaced_star_below_graph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k v : ℕ) (a : Fin n)
    (hk : k < C.gates.length)
    (hmask : ∀ x : Fin n → Bool, x a = true →
      ((C.gates.take k).foldl step (List.ofFn x)).getD v false = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    PEqualNP.TopForm.BelowF G (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) k := by
  intro x hx
  change ((C.gates.set k ⟨GateOp.and, [a.val, v]⟩).foldl step (List.ofFn x)).getD
    (n + k) false = true at hx
  have he := set_gate_value_at C.gates (List.ofFn x) k ⟨GateOp.and, [a.val, v]⟩ hk
  simp only [List.length_ofFn] at he
  rw [he] at hx
  simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, Bool.and_true, prefix_input, Bool.and_eq_true] at hx
  exact hmask x hx.1 hx.2

end PEqualNP.Outside.L_meta_1477.GateReplacement


namespace PEqualNP.Outside.L_meta_1477.SensitivePath
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]



end PEqualNP.Outside.L_meta_1477.SensitivePath

namespace PEqualNP.Outside.L_meta_1477.SemanticOverride

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open GateReplacement

def constantGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

lemma gateValue_constant (w : List Bool) (b : Bool) : gateValue w (constantGate b) = b := by
  cases b <;> rfl

def auxiliary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Circuit := replaceGate C j (constantGate (f x))

def value {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (w : ℕ) (x : Fin n → Bool) : Bool := SensitivePath.value (auxiliary C j f x) x w

lemma value_input {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (a : Fin n) (x : Fin n → Bool) : value C j f a.val x = x a :=
  SensitivePath.input_value (auxiliary C j f x) x a

lemma value_at {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (x : Fin n → Bool) : value C j f (n + j) x = f x := by
  have h := set_gate_value_at C.gates (List.ofFn x) j (constantGate (f x)) hj
  simp only [List.length_ofFn, gateValue_constant] at h
  exact h

lemma take_set_same {α : Type*} (gs : List α) (j : ℕ) (a : α) :
    (gs.set j a).take j = gs.take j := by
  induction gs generalizing j with
  | nil => simp
  | cons g gs ih => cases j <;> simp_all

lemma prefix_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j r : ℕ)
    (hj : j < C.gates.length) (hr : r < n + j) :
    ((C.gates.take j).foldl step (List.ofFn x)).getD r false = SensitivePath.value C x r := by
  have hlen : ((C.gates.take j).foldl step (List.ofFn x)).length = n + j := by
    change (W (C.gates.take j) x).length = _
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
  have he := fold_preserves (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x))
    r (by rw [hlen]; exact hr)
  change _ = (C.gates.foldl step (List.ofFn x)).getD r false
  symm
  simpa only [← List.foldl_append, List.take_append_drop] using he

lemma value_before {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (r : ℕ) (hr : r < n + j) (x : Fin n → Bool) :
    value C j f r x = SensitivePath.value C x r := by
  have haux := prefix_wire (auxiliary C j f x) x j r (by simpa [auxiliary, replaceGate] using hj) hr
  have hold := prefix_wire C x j r hj hr
  change _ = SensitivePath.value (auxiliary C j f x) x r at haux
  rw [show (auxiliary C j f x).gates.take j = C.gates.take j by
    exact take_set_same C.gates j (constantGate (f x))] at haux
  exact haux.symm.trans hold

lemma value_binary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkj : k ≠ j)
    (op : GateOp) (l r : ℕ) (hg : C.gates[k] = ⟨op, [l, r]⟩)
    (hl : l < n + k) (hr : r < n + k) (x : Fin n → Bool) :
    value C j f (n + k) x = op.eval [value C j f l x, value C j f r x] := by
  let D := auxiliary C j f x
  have hkD : k < D.gates.length := by simpa [D, auxiliary, replaceGate] using hk
  have hD : D.gates[k] = ⟨op, [l, r]⟩ := by
    have he : (C.gates.set j (constantGate (f x)))[k]'(by simpa using hk) = C.gates[k] :=
      List.getElem_set_of_ne (Ne.symm hkj) _ _
    exact he.trans hg
  have hv := SensitivePath.gate_value D x (n + k) (by omega)
    (by change n + k < n + D.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hD] at hv
  simpa only [List.map_cons, List.map_nil, ite_eq_left hl, ite_eq_left hr, value, D] using hv

lemma value_le {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (w : ℕ) (x : Fin n → Bool) : value C j f w x ≤ SensitivePath.value C x w := by
  apply set_gate_le C.gates hC (List.ofFn x) j (constantGate (f x))
  rw [gateValue_constant]
  exact hle x

lemma output_true {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hkeep : ((C.gates.set j zeroGate).foldl step (List.ofFn x)).getD C.output false = false →
      f x = gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate)) :
    value C j f C.output x = true := by
  apply set_gate_true_of_sensitive_preserved C.gates hC (List.ofFn x) j C.output
    (constantGate (f x)) hx
  intro hz
  rw [gateValue_constant]
  exact hkeep hz

lemma compiled_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD
        C.output false = false → f (PEqualNP.EdgeOwnership.pairInput u v) =
      gateValue ((C.gates.take j).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)))
        (C.gates.getD j zeroGate))
    (hD : PEqualNP.MetaComplexity.Monotone2 D)
    (hval : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = value C j f C.output x) :
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · apply circuitFun_monotone D
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hD g hg).1
  · intro x
    rw [show PEqualNP.MetaComplexity.circuitFun n D x = value C j f C.output x from hval x]
    rw [← hfun]
    exact value_le C j f hC hle C.output x
  · intro u v huv
    rw [show PEqualNP.MetaComplexity.circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) =
      value C j f C.output (PEqualNP.EdgeOwnership.pairInput u v) from hval _]
    apply output_true C j f hC _ ?_ (hkeep u v huv)
    change PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

end PEqualNP.Outside.L_meta_1477.SemanticOverride

namespace PEqualNP.Outside.L_meta_1477.QuadraticProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open GateReplacement

def quadraticPart {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, f (pairInput u v) = true ∧ x u = true ∧ x v = true)

lemma pair_le {n : ℕ} (x : Fin n → Bool) (u v : Fin n) (hu : x u = true) (hv : x v = true) :
    pairInput u v ≤ x := by
  intro w
  apply Bool.le_iff_imp.mpr
  intro hw
  simp only [pairInput, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

lemma quadraticPart_le {n : ℕ} (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (x : Fin n → Bool) : quadraticPart f x ≤ f x := by
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨u, v, hf, hu, hv⟩ := of_decide_eq_true hx
  exact Bool.le_iff_imp.mp (hm (pair_le x u v hu hv)) hf

lemma quadraticPart_pair {n : ℕ} (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (u v : Fin n) : quadraticPart f (pairInput u v) = f (pairInput u v) := by
  apply le_antisymm (quadraticPart_le f hm _)
  apply Bool.le_iff_imp.mpr
  intro hf
  apply decide_eq_true
  exact ⟨u, v, hf, by simp [pairInput], by simp [pairInput]⟩

lemma quadraticPart_mono {n : ℕ} (f : (Fin n → Bool) → Bool) : Monotone (quadraticPart f) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨u, v, hf, hu, hv⟩ := of_decide_eq_true hx
  apply decide_eq_true
  exact ⟨u, v, hf, Bool.le_iff_imp.mp (hxy u) hu, Bool.le_iff_imp.mp (hxy v) hv⟩

lemma local_gate_value {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) =
      SensitivePath.value C x (n + j) := by
  have hv := SensitivePath.gate_value C x (n + j) (by omega)
    (by change n + j < n + C.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hv]
  unfold gateValue
  rw [List.getD_eq_getElem _ _ hj]
  congr 1
  apply List.map_congr_left
  intro r _
  by_cases hr : r < n + j
  · rw [if_pos hr, SemanticOverride.prefix_wire C x j r hj hr]
  · rw [if_neg hr]
    apply List.getD_eq_default
    change (W (C.gates.take j) x).length ≤ r
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
    omega

lemma wire_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => SensitivePath.value C x w) :=
  circuitFun_monotone ⟨C.gates, w⟩ hC

lemma projection_override_le {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x : Fin n → Bool) :
    SemanticOverride.value C j (quadraticPart (fun y => SensitivePath.value C y (n + j))) w x ≤
      SensitivePath.value C x w := by
  apply SemanticOverride.value_le C j _ hC
  intro y
  rw [local_gate_value C j hj y]
  exact quadraticPart_le _ (wire_mono C hC _) y

lemma projection_override_pair_output {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : Fin n) (hx : C.eval (List.ofFn (pairInput u v)) = true) :
    SemanticOverride.value C j (quadraticPart (fun y => SensitivePath.value C y (n + j)))
      C.output (pairInput u v) = true := by
  apply SemanticOverride.output_true C j _ hC _ hx
  intro _
  rw [local_gate_value C j hj, quadraticPart_pair _ (wire_mono C hC _)]

end PEqualNP.Outside.L_meta_1477.QuadraticProjection

namespace PEqualNP.Outside.L_meta_1477.PrivateGraphReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership GateReplacement

lemma binary_data {n : ℕ} (C : Circuit) (hA : IsAO2 n C) (k : ℕ)
    (hk : k < C.gates.length) :
    C.gates[k] = ⟨(gateAt C k).op, [opnd C k 0, opnd C k 1]⟩ ∧
      opnd C k 0 < n + k ∧ opnd C k 1 < n + k := by
  have he : gateAt C k = C.gates[k] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hk]
  have hlen := hA.2.2 _ (List.getElem_mem hk)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : opnd C k 0 = a := by simp [opnd, he, hab]
  have hb : opnd C k 1 = b := by simp [opnd, he, hab]
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hb, he]
    cases hgate : C.gates[k] with
    | mk op ins =>
      simp only [hgate] at hab
      subst ins
      rfl
  · rw [ha]
    exact hA.2.1 k hk a (by simp [he, hab])
  · rw [hb]
    exact hA.2.1 k hk b (by simp [he, hab])

lemma private_graph_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (M : Finset ℕ) (g : ℕ) (hMbound : ∀ k ∈ M, k < C.gates.length)
    (hg : g < C.gates.length) (hgn : g ∉ M)
    (hkeep : ∀ k < C.gates.length, k ∉ M → k ≠ g →
      ∀ r ∈ (gateAt C k).inputs, r < n ∨ r - n ∉ M)
    (holdclean : ∀ k < C.gates.length, k ∉ M → k ≠ g →
      (gateAt C k).op = GateOp.and → BelowF G C k)
    (hout : C.output < n + C.gates.length)
    (houtun : C.output < n ∨ C.output - n ∉ M)
    (E : Finset (Fin n × Fin n)) (T : Finset (Fin n)) (hE : E.Nonempty)
    (hcover : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T)
    (hcost : E.card + T.card ≤ M.card + 2)
    (hEgraph : ∀ e ∈ E, G.Adj e.1 e.2)
    (hpairs : ∀ u v : Fin n, gateVal n C g (pairInput u v) = true ↔
      (u, v) ∈ E ∨ (v, u) ∈ E) :
    ∃ D : Circuit, D.size ≤ C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧
      ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
  let f := QuadraticProjection.quadraticPart (fun x : Fin n → Bool => SensitivePath.value C x (n + g))
  let val := SemanticOverride.value C g f
  have hf (x : Fin n → Bool) : f x = decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true) := by
    apply Bool.eq_iff_iff.mpr
    simp only [f, QuadraticProjection.quadraticPart, decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (hpairs u v).mp huv with he | he
      · exact ⟨(u, v), he, hu, hv⟩
      · exact ⟨(v, u), he, hv, hu⟩
    · rintro ⟨e, he, h1, h2⟩
      exact ⟨e.1, e.2, (hpairs e.1 e.2).mpr (Or.inl he), h1, h2⟩
  have hle (x : Fin n → Bool) : f x ≤
      gateValue ((C.gates.take g).foldl step (List.ofFn x)) (C.gates.getD g zeroGate) := by
    rw [QuadraticProjection.local_gate_value C g hg]
    exact QuadraticProjection.quadraticPart_le _ (QuadraticProjection.wire_mono C hA.1 _) x
  obtain ⟨D, hsize, hm, hc, hev⟩ := PrivateStars.compile_private_edges C.gates.length
    (graphFun G ∅) val (fun k => (gateAt C k).op) (fun k => opnd C k 0) (fun k => opnd C k 1)
    M g hMbound hg hgn (by
      intro k hk
      apply hA.1
      rw [show gateAt C k = C.gates[k] from by unfold gateAt; rw [List.getD_eq_getElem _ _ hk]]
      exact List.getElem_mem hk)
    (fun k hk => (binary_data C hA k hk).2) (by
      intro k hk hkm hkg x
      have hb := binary_data C hA k hk
      exact SemanticOverride.value_binary C g f k hk hkg _ _ _ hb.1 hb.2.1 hb.2.2 x)
    (SemanticOverride.value_input C g f) (by
      intro k hk hkm hkg r hr
      apply hkeep k hk hkm hkg r
      have hb := (binary_data C hA k hk).1
      have he : gateAt C k = C.gates[k] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hk]
      rw [he, hb]
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
    E T hE hcover hcost (fun x => (SemanticOverride.value_at C g f hg x).trans (hf x)) (by
      intro e he x h1 h2
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨e.1, e.2, hEgraph e he, h1, h2⟩)
    (by
      intro k hk hkm hkg hop x hx
      exact holdclean k hk hkm hkg hop x
        (Bool.le_iff_imp.mp (SemanticOverride.value_le C g f hA.1 hle (n + k) x) hx))
    C.output hout houtun
  refine ⟨D, hsize, hm, ?_, ?_⟩
  · apply SemanticOverride.compiled_graph_correct G C D g f hA.1 hfun hle ?_ hm hev
    intro u v _ _
    rw [QuadraticProjection.local_gate_value C g hg]
    exact QuadraticProjection.quadraticPart_pair _ (QuadraticProjection.wire_mono C hA.1 _) u v
  · intro k hk hop x hx
    exact hc k hk hop x hx

end PEqualNP.Outside.L_meta_1477.PrivateGraphReplacement
