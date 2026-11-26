import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_9033_aux

def edgeList : List (Nat × Nat) :=
  [(0, 6), (0, 7), (1, 3), (1, 5), (2, 4), (2, 7),
    (3, 5), (3, 7), (4, 5), (4, 6), (5, 6)]

def graph (s : Fin 256) : Bool :=
  edgeList.any (fun e => s.val.testBit e.1 && s.val.testBit e.2)

def single (v : Fin 8) : Fin 256 :=
  ([1, 2, 4, 8, 16, 32, 64, 128] : List (Fin 256)).getD v.val 0

def addBit (s : Fin 256) (v : Fin 8) : Fin 256 :=
  ⟨(s.val ||| 2 ^ v.val) % 256, Nat.mod_lt _ (by decide)⟩

def maskSubset (s t : Fin 256) : Prop :=
  ∀ i : Fin 8, s.val.testBit i.val = true → t.val.testBit i.val = true

def maskMonotone (u : Fin 256 → Bool) : Prop :=
  ∀ s t, maskSubset s t → u s = true → u t = true

def witness (v y : Fin 8) : Fin 256 :=
  (([
    [0, 66, 68, 72, 144, 160, 64, 128],
    [9, 0, 12, 8, 24, 32, 72, 160],
    [17, 18, 0, 24, 16, 160, 192, 128],
    [3, 2, 6, 0, 18, 32, 66, 128],
    [5, 6, 4, 12, 0, 32, 64, 160],
    [3, 2, 6, 8, 16, 0, 64, 130],
    [1, 3, 5, 9, 16, 32, 0, 144],
    [1, 3, 4, 8, 17, 33, 68, 0]] : List (List (Fin 256))).getD v.val []).getD y.val 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma nonDominationCertificate : ∀ v y : Fin 8, v ≠ y →
    (witness v y).val.testBit y.val = true ∧
    (witness v y).val.testBit v.val = false ∧
    maskSubset (single y) (witness v y) ∧
    graph (witness v y) = false ∧ graph (addBit (witness v y) v) = true := by
  unfold maskSubset
  decide +kernel

lemma nonDomination (v y : Fin 8) (h : v ≠ y) :
    ∃ s : Fin 256, s.val.testBit y.val = true ∧ s.val.testBit v.val = false ∧
      maskSubset (single y) s ∧ graph s = false ∧ graph (addBit s v) = true := by
  exact ⟨witness v y, nonDominationCertificate v y h⟩

lemma singleton_false_of_stable (u : Fin 256 → Bool) (v y : Fin 8)
    (hne : v ≠ y) (hmono : maskMonotone u)
    (hstable : ∀ s, u s = true → graph s = graph (addBit s v)) :
    u (single y) = false := by
  obtain ⟨s, _, _, hsub, hfalse, htrue⟩ := nonDomination v y hne
  cases hu : u (single y) with
  | false => rfl
  | true =>
      have hs : u s = true := hmono (single y) s hsub hu
      have heq : graph s = graph (addBit s v) := hstable s hs
      have bad : (false : Bool) = true := hfalse.symm.trans (heq.trans htrue)
      cases bad

lemma addBit_zero : ∀ v : Fin 8, addBit (0 : Fin 256) v = single v := by
  decide +kernel

lemma own_singleton_false (u : Fin 256 → Bool) (v : Fin 8)
    (hzero : u 0 = false) (hindependent : ∀ s, u (addBit s v) = u s) :
    u (single v) = false := by
  rw [← addBit_zero v, hindependent, hzero]

lemma all_singletons_false (u : Fin 256 → Bool) (v : Fin 8)
    (hmono : maskMonotone u)
    (hstable : ∀ s, u s = true → graph s = graph (addBit s v))
    (hzero : u 0 = false) (hindependent : ∀ s, u (addBit s v) = u s) :
    ∀ y : Fin 8, u (single y) = false := by
  intro y
  by_cases h : v = y
  · subst y
    exact own_singleton_false u v hzero hindependent
  · exact singleton_false_of_stable u v y h hmono hstable

def gateBool (op x y : Bool) : Bool :=
  if op then x && y else x || y

lemma gateBool_mono (op a b c d : Bool)
    (ha : a = true → c = true) (hb : b = true → d = true) :
    gateBool op a b = true → gateBool op c d = true := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [gateBool]

lemma causal_compare_except (n m p : Nat) (op : Nat → Bool)
    (a b : Nat → Nat) (x y : Nat → Bool)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i)
    (hx : ∀ i < m, i ≠ p → x (n + i) = gateBool (op i) (x (a i)) (x (b i)))
    (hy : ∀ i < m, i ≠ p → y (n + i) = gateBool (op i) (y (a i)) (y (b i)))
    (hraw : ∀ j < n, x j = true → y j = true)
    (hcut : p < m → x (n + p) = true → y (n + p) = true) :
    ∀ j < n + m, x j = true → y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hvalue
    by_cases hlow : j < n
    · exact hraw j hlow hvalue
    · have hi : j - n < m := by omega
      have heq : n + (j - n) = j := by omega
      by_cases hp : j - n = p
      · have hjp : j = n + p := by omega
        rw [hjp] at hvalue ⊢
        exact hcut (by omega) hvalue
      · have hleft : a (j - n) < j := by
          have hh := (hcausal (j - n) hi).1
          omega
        have hright : b (j - n) < j := by
          have hh := (hcausal (j - n) hi).2
          omega
        have hxe := hx (j - n) hi hp
        have hye := hy (j - n) hi hp
        rw [heq] at hxe hye
        rw [hxe] at hvalue
        rw [hye]
        exact gateBool_mono _ _ _ _ _
          (ih _ hleft (by omega)) (ih _ hright (by omega)) hvalue

lemma causal_target_preserved {α : Type} (n m p out : Nat)
    (op : Nat → Bool) (a b : Nat → Nat)
    (x y : α → Nat → Bool) (target : α → Bool)
    (hout : out < n + m)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i)
    (hx : ∀ s i, i < m → i ≠ p →
      x s (n + i) = gateBool (op i) (x s (a i)) (x s (b i)))
    (hy : ∀ s i, i < m → i ≠ p →
      y s (n + i) = gateBool (op i) (y s (a i)) (y s (b i)))
    (hraw : ∀ s j, j < n → x s j = y s j)
    (htarget : ∀ s, x s out = target s)
    (hcut : ∀ s, p < m →
      (target s = true → x s (n + p) = true → y s (n + p) = true) ∧
      (target s = false → y s (n + p) = true → x s (n + p) = true)) :
    ∀ s, y s out = target s := by
  intro s
  cases hs : target s with
  | true =>
    exact causal_compare_except n m p op a b (x s) (y s) hcausal
      (hx s) (hy s) (fun j hj hv => (hraw s j hj) ▸ hv)
      (fun hp => (hcut s hp).1 hs) out hout ((htarget s).trans hs)
  | false =>
    have hback := causal_compare_except n m p op a b (y s) (x s) hcausal
      (hy s) (hx s) (fun j hj hv => (hraw s j hj).symm ▸ hv)
      (fun hp => (hcut s hp).2 hs) out hout
    cases hv : y s out with
    | false => rfl
    | true =>
      have hbad : (false : Bool) = true :=
        ((htarget s).trans hs).symm.trans (hback hv)
      cases hbad

lemma causal_equal_before_except (n m p : Nat) (op : Nat → Bool)
    (a b : Nat → Nat) (x y : Nat → Bool) (hp : p ≤ m)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i)
    (hx : ∀ i < m, i ≠ p → x (n + i) = gateBool (op i) (x (a i)) (x (b i)))
    (hy : ∀ i < m, i ≠ p → y (n + i) = gateBool (op i) (y (a i)) (y (b i)))
    (hraw : ∀ j < n, x j = y j) :
    ∀ j < n + p, x j = y j := by
  intro j hj
  have hxy := causal_compare_except n p p op a b x y
    (fun i hi => hcausal i (by omega))
    (fun i hi hne => hx i (by omega) hne)
    (fun i hi hne => hy i (by omega) hne)
    (fun k hk hv => (hraw k hk) ▸ hv)
    (fun h => (Nat.lt_irrefl p h).elim) j hj
  have hyx := causal_compare_except n p p op a b y x
    (fun i hi => hcausal i (by omega))
    (fun i hi hne => hy i (by omega) hne)
    (fun i hi hne => hx i (by omega) hne)
    (fun k hk hv => (hraw k hk).symm ▸ hv)
    (fun h => (Nat.lt_irrefl p h).elim) j hj
  cases hxj : x j <;> cases hyj : y j <;> simp_all

lemma earlier_replacement_preserves_target {α : Type} (n m p q out : Nat)
    (op : Nat → Bool) (a b : Nat → Nat)
    (x y : α → Nat → Bool) (target : α → Bool)
    (hp : p < m) (hq : q < n + p) (hout : out < n + m)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i)
    (hx : ∀ s i, i < m → i ≠ p →
      x s (n + i) = gateBool (op i) (x s (a i)) (x s (b i)))
    (hy : ∀ s i, i < m → i ≠ p →
      y s (n + i) = gateBool (op i) (y s (a i)) (y s (b i)))
    (hraw : ∀ s j, j < n → x s j = y s j)
    (hcopy : ∀ s, y s (n + p) = y s q)
    (htarget : ∀ s, x s out = target s)
    (hdominates : ∀ s,
      (target s = true → x s (n + p) = true → x s q = true) ∧
      (target s = false → x s q = true → x s (n + p) = true)) :
    ∀ s, y s out = target s := by
  apply causal_target_preserved n m p out op a b x y target hout hcausal hx hy hraw htarget
  intro s _
  have hsame := causal_equal_before_except n m p op a b (x s) (y s)
    (Nat.le_of_lt hp) hcausal (hx s) (hy s) (hraw s) q hq
  rw [hcopy s, ← hsame]
  exact hdominates s

def skipIndex (cut i : Nat) : Nat :=
  if i < cut then i else i + 1

def routeIndex (cut source i : Nat) : Nat :=
  if i < cut then i else if i = cut then source else i - 1

lemma skipIndex_ne (cut i : Nat) : skipIndex cut i ≠ cut := by
  unfold skipIndex
  split <;> omega

lemma skipIndex_lt (m cut i : Nat) (hc : cut < m) (hi : i < m - 1) :
    skipIndex cut i < m := by
  unfold skipIndex
  split <;> omega

lemma skipIndex_add (n cut i : Nat) :
    skipIndex (n + cut) (n + i) = n + skipIndex cut i := by
  unfold skipIndex
  split <;> split <;> omega

lemma routeIndex_lt_skip (cut source j bound : Nat) (hs : source < cut)
    (hj : j < skipIndex cut bound) : routeIndex cut source j < bound := by
  unfold skipIndex at hj
  unfold routeIndex
  split <;> split_ifs at hj ⊢ <;> omega

lemma routeIndex_output_lt (n m p q out : Nat) (hp : p < m)
    (hq : q < n + p) (hout : out < n + m) :
    routeIndex (n + p) q out < n + (m - 1) := by
  apply routeIndex_lt_skip (n + p) q out (n + (m - 1)) hq
  unfold skipIndex
  split <;> omega

lemma skip_route_eval {α : Type} (cut source : Nat) (v : Nat → α)
    (hs : source < cut) (hcopy : v cut = v source) (j : Nat) :
    v (skipIndex cut (routeIndex cut source j)) = v j := by
  unfold routeIndex
  split
  · rename_i hlt
    simp only [skipIndex, hlt, ite_true]
  · rename_i hge
    split
    · rename_i heq
      subst j
      simp only [skipIndex, hs, ite_true]
      exact hcopy.symm
    · rename_i hne
      have hnot : ¬j - 1 < cut := by omega
      have hadd : j - 1 + 1 = j := by omega
      simp only [skipIndex, hnot, ite_false, hadd]

lemma deleteGate_causal (n m p q : Nat) (a b : Nat → Nat)
    (hp : p < m) (hq : q < n + p)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i) :
    ∀ i < m - 1,
      routeIndex (n + p) q (a (skipIndex p i)) < n + i ∧
      routeIndex (n + p) q (b (skipIndex p i)) < n + i := by
  intro i hi
  have hbound := hcausal (skipIndex p i) (skipIndex_lt m p i hp hi)
  constructor
  · apply routeIndex_lt_skip (n + p) q _ (n + i) hq
    rw [skipIndex_add]
    exact hbound.1
  · apply routeIndex_lt_skip (n + p) q _ (n + i) hq
    rw [skipIndex_add]
    exact hbound.2

lemma deleteGate_equations {α : Type} (n m p q : Nat)
    (run : Nat → α → α → α) (a b : Nat → Nat) (v : Nat → α)
    (hp : p < m) (hq : q < n + p)
    (heval : ∀ i < m, i ≠ p → v (n + i) = run i (v (a i)) (v (b i)))
    (hcopy : v (n + p) = v q) :
    ∀ i < m - 1,
      v (skipIndex (n + p) (n + i)) =
        run (skipIndex p i)
          (v (skipIndex (n + p) (routeIndex (n + p) q (a (skipIndex p i)))))
          (v (skipIndex (n + p) (routeIndex (n + p) q (b (skipIndex p i))))) := by
  intro i hi
  rw [skipIndex_add]
  rw [skip_route_eval (n + p) q v hq hcopy]
  rw [skip_route_eval (n + p) q v hq hcopy]
  exact heval (skipIndex p i) (skipIndex_lt m p i hp hi) (skipIndex_ne p i)

lemma deleteGate_raw {α : Type} (n p : Nat) (v : Nat → α) :
    ∀ i < n, v (skipIndex (n + p) i) = v i := by
  intro i hi
  have hlt : i < n + p := by omega
  simp only [skipIndex, hlt, ite_true]

lemma deleteGate_output {α : Type} (n p q out : Nat) (v : Nat → α)
    (hq : q < n + p) (hcopy : v (n + p) = v q) :
    v (skipIndex (n + p) (routeIndex (n + p) q out)) = v out := by
  exact skip_route_eval (n + p) q v hq hcopy out

lemma delete_copy_gate {σ α : Type} (n m p q out : Nat)
    (run : Nat → α → α → α) (a b : Nat → Nat) (v : σ → Nat → α)
    (hp : p < m) (hq : q < n + p) (hout : out < n + m)
    (hcausal : ∀ i < m, a i < n + i ∧ b i < n + i)
    (heval : ∀ s i, i < m → i ≠ p →
      v s (n + i) = run i (v s (a i)) (v s (b i)))
    (hcopy : ∀ s, v s (n + p) = v s q) :
    ∃ (run' : Nat → α → α → α) (a' b' : Nat → Nat)
        (out' : Nat) (v' : σ → Nat → α),
      (∀ i, run' i = run (skipIndex p i)) ∧
      out' < n + (m - 1) ∧
      (∀ i < m - 1, a' i < n + i ∧ b' i < n + i) ∧
      (∀ s j, j < n → v' s j = v s j) ∧
      (∀ s i, i < m - 1 →
        v' s (n + i) = run' i (v' s (a' i)) (v' s (b' i))) ∧
      (∀ s, v' s out' = v s out) := by
  refine ⟨fun i => run (skipIndex p i),
    fun i => routeIndex (n + p) q (a (skipIndex p i)),
    fun i => routeIndex (n + p) q (b (skipIndex p i)),
    routeIndex (n + p) q out,
    fun s j => v s (skipIndex (n + p) j), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ => rfl
  · exact routeIndex_output_lt n m p q out hp hq hout
  · exact deleteGate_causal n m p q a b hp hq hcausal
  · exact fun s => deleteGate_raw n p (v s)
  · exact fun s => deleteGate_equations n m p q run a b (v s) hp hq (heval s) (hcopy s)
  · exact fun s => deleteGate_output n p q out (v s) hq (hcopy s)

namespace FirstDirty

def allMasks : List (Fin 32) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def rectangular (l r : Fin 32) : Bool :=
  decide (0 < l.val ∧ l.val < r.val ∧ l.val &&& r.val = 0)

def rectangles : List (Fin 32 × Fin 32) :=
  allMasks.flatMap fun l => (allMasks.filter (rectangular l)).map fun r => (l, r)

def crossCode (l r : Fin 32) : Nat :=
  (if (l.val.testBit 0 && r.val.testBit 1) || (l.val.testBit 1 && r.val.testBit 0) then 1 else 0) +
  (if (l.val.testBit 0 && r.val.testBit 2) || (l.val.testBit 2 && r.val.testBit 0) then 2 else 0) +
  (if (l.val.testBit 0 && r.val.testBit 3) || (l.val.testBit 3 && r.val.testBit 0) then 4 else 0) +
  (if (l.val.testBit 0 && r.val.testBit 4) || (l.val.testBit 4 && r.val.testBit 0) then 8 else 0) +
  (if (l.val.testBit 1 && r.val.testBit 2) || (l.val.testBit 2 && r.val.testBit 1) then 16 else 0) +
  (if (l.val.testBit 1 && r.val.testBit 3) || (l.val.testBit 3 && r.val.testBit 1) then 32 else 0) +
  (if (l.val.testBit 1 && r.val.testBit 4) || (l.val.testBit 4 && r.val.testBit 1) then 64 else 0) +
  (if (l.val.testBit 2 && r.val.testBit 3) || (l.val.testBit 3 && r.val.testBit 2) then 128 else 0) +
  (if (l.val.testBit 2 && r.val.testBit 4) || (l.val.testBit 4 && r.val.testBit 2) then 256 else 0) +
  (if (l.val.testBit 3 && r.val.testBit 4) || (l.val.testBit 4 && r.val.testBit 3) then 512 else 0)

def allowed (permitted extra : Nat) (p : Fin 32 × Fin 32) : Bool :=
  decide (crossCode p.1 p.2 &&& permitted = crossCode p.1 p.2 ∧
    crossCode p.1 p.2 &&& extra ≠ 0)

def maskSize (s : Fin 32) : Nat :=
  ([0, 1, 2, 3, 4] : List Nat).countP fun i => s.val.testBit i

def rectCost (p : Fin 32 × Fin 32) : Nat :=
  maskSize p.1 + maskSize p.2 - 2

def classA : List (Fin 32 × Fin 32) :=
  [(1, 2), (1, 6), (1, 18), (1, 22), (2, 5), (2, 9), (2, 13), (6, 9)]

def classB : List (Fin 32 × Fin 32) :=
  [(2, 16), (2, 20), (2, 24), (2, 28), (3, 16), (3, 20), (8, 16), (8, 18), (8, 20), (8, 22), (9, 16), (9, 20), (10, 16), (10, 20), (11, 16), (11, 20)]

def classC : List (Fin 32 × Fin 32) :=
  [(1, 8), (1, 12), (1, 24), (1, 28), (3, 8), (3, 12), (5, 8), (7, 8)]

def swapEG (s : Fin 32) : Fin 32 :=
  ⟨((if s.val.testBit 0 then 1 else 0) +
    (if s.val.testBit 1 then 8 else 0) +
    (if s.val.testBit 2 then 4 else 0) +
    (if s.val.testBit 3 then 2 else 0) +
    (if s.val.testBit 4 then 16 else 0)) % 32, Nat.mod_lt _ (by decide)⟩

def swapRectangle (p : Fin 32 × Fin 32) : Fin 32 × Fin 32 :=
  let l := swapEG p.1
  let r := swapEG p.2
  if l.val < r.val then (l, r) else (r, l)

lemma allMasks_complete : ∀ i : Fin 32, i ∈ allMasks := by
  decide +kernel

lemma rectangle_census : rectangles.length = 90 := by
  decide +kernel

lemma mem_rectangles_iff (l r : Fin 32) :
    (l, r) ∈ rectangles ↔ rectangular l r = true := by
  simp only [rectangles, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨l', _, r', ⟨_, hrect⟩, heq⟩
    have hl : l' = l := congrArg Prod.fst heq
    have hr : r' = r := congrArg Prod.snd heq
    simpa [hl, hr] using hrect
  · intro hrect
    exact ⟨l, allMasks_complete l, r, ⟨allMasks_complete r, hrect⟩, rfl⟩

lemma classificationA : rectangles.filter (allowed 187 1) = classA := by
  decide +kernel

lemma costsA : classA.map rectCost = [0, 1, 1, 2, 1, 1, 2, 2] := by
  decide +kernel

lemma classificationB : rectangles.filter (allowed 762 576) = classB := by
  decide +kernel

lemma costsB : classB.map rectCost = [0, 1, 1, 2, 1, 2, 0, 1, 1, 2, 1, 2, 1, 2, 2, 3] := by
  decide +kernel

lemma classificationC : rectangles.filter (allowed 190 4) = classC := by
  decide +kernel

lemma costsC : classC.map rectCost = [0, 1, 1, 2, 1, 2, 1, 2] := by
  decide +kernel

lemma classA_classC_symmetry : (classA.map swapRectangle).Perm classC := by
  decide +kernel

lemma classA_swap_cost : (classA.map swapRectangle).map rectCost = classA.map rectCost := by
  decide +kernel

def positiveHit (p : Fin 32 × Fin 32) : Bool :=
  decide (crossCode p.1 p.2 &&& 186 ≠ 0)

def positiveA : List (Fin 32 × Fin 32) :=
  [(1, 6), (1, 18), (1, 22), (2, 5), (2, 9), (2, 13), (6, 9)]

lemma positive_classificationA : classA.filter positiveHit = positiveA := by
  decide +kernel

lemma positive_costsA : positiveA.map rectCost = [1, 1, 2, 1, 1, 2, 2] := by
  decide +kernel

def positiveB : List (Fin 32 × Fin 32) :=
  [(2, 20), (2, 24), (2, 28), (3, 16), (3, 20), (8, 18), (8, 20), (8, 22), (9, 16), (9, 20), (10, 20), (11, 16), (11, 20)]

lemma positive_classificationB : classB.filter positiveHit = positiveB := by
  decide +kernel

lemma positive_costsB : positiveB.map rectCost = [1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3] := by
  decide +kernel

def positiveC : List (Fin 32 × Fin 32) :=
  [(1, 12), (1, 24), (1, 28), (3, 8), (3, 12), (5, 8), (7, 8)]

lemma positive_classificationC : classC.filter positiveHit = positiveC := by
  decide +kernel

lemma positive_costsC : positiveC.map rectCost = [1, 1, 2, 1, 2, 1, 2] := by
  decide +kernel

lemma class_counts : classA.length = 8 ∧ classB.length = 16 ∧ classC.length = 8 := by
  decide +kernel

lemma positive_counts : positiveA.length = 7 ∧ positiveB.length = 13 ∧ positiveC.length = 7 := by
  decide +kernel

lemma positive_symmetry : (positiveA.map swapRectangle).Perm positiveC := by
  decide +kernel

end FirstDirty

namespace R3Family

def singletonMasks : List Nat := [1, 2, 4, 8, 16, 32, 64, 128]

def singleBit (m : Nat) : Bool :=
  m != 0 && (m &&& (m - 1) == 0)

def canUnion (m : Nat) (known : List Nat) : Bool :=
  singleBit (m &&& (m - 1)) ||
  known.any fun a => a != m && (a &&& m == a) &&
    (singleBit (m ^^^ a) || known.any fun b => b != m && (a ||| b == m))

def insertMask (e : Nat) : List Nat → List Nat
  | [] => [e]
  | x :: xs => if e < x then e :: x :: xs else x :: insertMask e xs

def addExtra (e : Nat) (f : List Nat) : List Nat :=
  if e == 0 || singletonMasks.contains e || f.contains e then f else insertMask e f

def closeMasks (f : List Nat) : List Nat :=
  f.foldl (fun known m => if canUnion m known then m :: known else known) []

def generated (f permitted : List Nat) : Bool :=
  f.all fun m => (closeMasks permitted).contains m

def possibleWithFive (f : List Nat) : Bool :=
  if f.length = 5 then generated f f
  else if f.length = 4 then (List.range 256).any fun e => generated f (addExtra e f)
  else true

lemma positive_controls : generated [3, 12, 15] [3, 12, 15] = true ∧
    generated [7] [7] = false ∧
    generated [7] (addExtra 3 [7]) = true ∧
    generated [7] (addExtra 24 [7]) = false := by
  decide +kernel

def block00 : List (List Nat) :=
  [[17, 90, 176, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block00_checked : block00.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block01 : List (List Nat) :=
  [[17, 91, 144, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block01_checked : block01.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block02 : List (List Nat) :=
  [[18, 176, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block02_checked : block02.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block03 : List (List Nat) :=
  [[26, 176, 192, 194]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block03_checked : block03.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block04 : List (List Nat) :=
  [[26, 176, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block04_checked : block04.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block05 : List (List Nat) :=
  [[66, 144, 178, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block05_checked : block05.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block06 : List (List Nat) :=
  [[68, 90, 144, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block06_checked : block06.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block07 : List (List Nat) :=
  [[68, 94, 144, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block07_checked : block07.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block08 : List (List Nat) :=
  [[74, 144, 146, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block08_checked : block08.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block09 : List (List Nat) :=
  [[74, 144, 178, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block09_checked : block09.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block10 : List (List Nat) :=
  [[82, 144, 178, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block10_checked : block10.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block11 : List (List Nat) :=
  [[82, 176, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block11_checked : block11.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block12 : List (List Nat) :=
  [[83, 144, 178, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block12_checked : block12.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block13 : List (List Nat) :=
  [[86, 144, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block13_checked : block13.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block14 : List (List Nat) :=
  [[90, 144, 146, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block14_checked : block14.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block15 : List (List Nat) :=
  [[90, 144, 178, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block15_checked : block15.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block16 : List (List Nat) :=
  [[90, 176, 192, 194]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block16_checked : block16.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block17 : List (List Nat) :=
  [[90, 176, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block17_checked : block17.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block18 : List (List Nat) :=
  [[91, 144, 146, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block18_checked : block18.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block19 : List (List Nat) :=
  [[91, 144, 178, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block19_checked : block19.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block20 : List (List Nat) :=
  [[94, 144, 192, 194]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block20_checked : block20.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block21 : List (List Nat) :=
  [[94, 144, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block21_checked : block21.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block22 : List (List Nat) :=
  [[5, 40, 41, 176, 228],
    [5, 40, 44, 177, 224],
    [5, 40, 57, 164, 176],
    [5, 40, 57, 176, 228],
    [5, 40, 108, 161, 224],
    [5, 40, 108, 177, 224],
    [9, 18, 40, 144, 224],
    [9, 18, 40, 176, 224],
    [9, 18, 66, 144, 224],
    [9, 18, 74, 144, 224],
    [9, 18, 82, 144, 224],
    [9, 18, 90, 144, 192],
    [9, 18, 90, 144, 224],
    [9, 18, 144, 176, 224],
    [9, 40, 68, 144, 224],
    [9, 40, 144, 160, 177],
    [9, 40, 144, 176, 224],
    [9, 40, 144, 177, 224],
    [9, 50, 66, 144, 224],
    [9, 50, 74, 144, 224],
    [9, 50, 82, 144, 192],
    [9, 50, 82, 144, 224],
    [9, 50, 90, 144, 192],
    [9, 50, 90, 144, 224],
    [9, 66, 144, 146, 224]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block22_checked : block22.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block23 : List (List Nat) :=
  [[9, 66, 144, 178, 224],
    [9, 68, 82, 144, 224],
    [9, 68, 90, 144, 192],
    [9, 68, 90, 144, 224],
    [9, 74, 144, 146, 224],
    [9, 74, 144, 178, 224],
    [9, 82, 144, 146, 224],
    [9, 82, 144, 178, 192],
    [9, 82, 144, 178, 224],
    [9, 90, 144, 146, 192],
    [9, 90, 144, 146, 224],
    [9, 90, 144, 178, 192],
    [9, 90, 144, 178, 224],
    [12, 17, 40, 176, 192],
    [12, 17, 82, 176, 192],
    [12, 17, 90, 144, 192],
    [12, 17, 90, 176, 192],
    [12, 18, 66, 176, 192],
    [12, 18, 98, 176, 192],
    [12, 18, 176, 192, 194],
    [12, 18, 176, 192, 226],
    [12, 26, 66, 176, 192],
    [12, 26, 98, 176, 192],
    [12, 26, 176, 192, 194],
    [12, 26, 176, 192, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block23_checked : block23.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block24 : List (List Nat) :=
  [[12, 40, 66, 176, 192],
    [12, 40, 66, 176, 224],
    [12, 40, 160, 192, 228],
    [12, 40, 176, 192, 224],
    [12, 40, 176, 192, 228],
    [12, 66, 82, 176, 192],
    [12, 66, 90, 144, 192],
    [12, 66, 90, 176, 192],
    [12, 66, 176, 192, 224],
    [12, 82, 98, 144, 192],
    [12, 82, 98, 176, 192],
    [12, 82, 144, 192, 226],
    [12, 82, 176, 192, 194],
    [12, 82, 176, 192, 226],
    [12, 90, 98, 144, 192],
    [12, 90, 98, 176, 192],
    [12, 90, 144, 192, 194],
    [12, 90, 144, 192, 226],
    [12, 90, 176, 192, 194],
    [12, 90, 176, 192, 226],
    [13, 40, 41, 48, 228],
    [13, 40, 41, 176, 228],
    [13, 40, 44, 96, 177],
    [13, 40, 44, 177, 224],
    [13, 40, 48, 57, 164]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block24_checked : block24.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block25 : List (List Nat) :=
  [[13, 40, 48, 57, 228],
    [13, 40, 57, 164, 176],
    [13, 40, 57, 176, 228],
    [13, 40, 96, 108, 161],
    [13, 40, 96, 108, 177],
    [13, 40, 108, 161, 224],
    [13, 40, 108, 177, 224],
    [17, 34, 82, 176, 192],
    [17, 34, 83, 144, 192],
    [17, 34, 90, 176, 192],
    [17, 34, 91, 144, 192],
    [17, 40, 88, 176, 192],
    [17, 40, 89, 144, 192],
    [17, 40, 90, 176, 192],
    [17, 40, 91, 144, 192],
    [17, 40, 92, 144, 192],
    [17, 66, 90, 144, 192],
    [17, 82, 98, 144, 192],
    [17, 82, 144, 192, 226],
    [17, 82, 162, 176, 192],
    [17, 82, 176, 192, 224],
    [17, 83, 144, 162, 192],
    [17, 83, 144, 176, 192],
    [17, 90, 98, 144, 192],
    [17, 90, 130, 176, 192]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block25_checked : block25.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block26 : List (List Nat) :=
  [[17, 90, 144, 192, 194],
    [17, 90, 144, 192, 226],
    [17, 90, 162, 176, 192],
    [17, 90, 176, 192, 224],
    [17, 91, 130, 144, 192],
    [17, 91, 144, 162, 192],
    [17, 91, 144, 176, 192],
    [18, 68, 90, 144, 192],
    [18, 144, 176, 178, 224],
    [19, 144, 176, 178, 192],
    [21, 33, 40, 108, 224],
    [21, 36, 40, 57, 176],
    [21, 40, 41, 100, 176],
    [21, 40, 44, 49, 224],
    [21, 40, 49, 108, 224],
    [21, 40, 57, 100, 176],
    [22, 144, 176, 192, 226],
    [26, 144, 146, 176, 224],
    [26, 144, 176, 178, 224],
    [27, 144, 146, 176, 192],
    [27, 144, 176, 178, 192],
    [29, 33, 40, 96, 108],
    [29, 33, 40, 108, 224],
    [29, 36, 40, 48, 57],
    [29, 36, 40, 57, 176]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block26_checked : block26.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block27 : List (List Nat) :=
  [[29, 40, 41, 48, 100],
    [29, 40, 41, 100, 176],
    [29, 40, 44, 49, 96],
    [29, 40, 44, 49, 224],
    [29, 40, 48, 57, 100],
    [29, 40, 49, 96, 108],
    [29, 40, 49, 108, 224],
    [29, 40, 57, 100, 176],
    [30, 144, 176, 192, 194],
    [30, 144, 176, 192, 226],
    [33, 40, 69, 108, 224],
    [33, 40, 77, 96, 108],
    [33, 40, 77, 108, 224],
    [33, 40, 85, 108, 224],
    [33, 40, 93, 96, 108],
    [33, 40, 93, 108, 224],
    [34, 68, 82, 144, 224],
    [34, 68, 86, 144, 192],
    [34, 68, 90, 144, 224],
    [34, 68, 94, 144, 192],
    [36, 40, 48, 57, 77],
    [36, 40, 48, 57, 93],
    [36, 40, 57, 69, 176],
    [36, 40, 57, 77, 176],
    [36, 40, 57, 85, 176]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block27_checked : block27.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block28 : List (List Nat) :=
  [[36, 40, 57, 93, 176],
    [40, 41, 48, 77, 100],
    [40, 41, 48, 93, 100],
    [40, 41, 69, 100, 176],
    [40, 41, 77, 100, 176],
    [40, 41, 85, 100, 176],
    [40, 41, 93, 100, 176],
    [40, 44, 49, 69, 224],
    [40, 44, 49, 77, 96],
    [40, 44, 49, 77, 224],
    [40, 44, 49, 85, 224],
    [40, 44, 49, 93, 96],
    [40, 44, 49, 93, 224],
    [40, 48, 57, 77, 100],
    [40, 48, 57, 93, 100],
    [40, 49, 69, 108, 224],
    [40, 49, 77, 96, 108],
    [40, 49, 77, 108, 224],
    [40, 49, 85, 108, 224],
    [40, 49, 93, 96, 108],
    [40, 49, 93, 108, 224],
    [40, 57, 69, 100, 176],
    [40, 57, 77, 100, 176],
    [40, 57, 85, 100, 176],
    [40, 57, 93, 100, 176]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block28_checked : block28.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block29 : List (List Nat) :=
  [[40, 68, 88, 144, 224],
    [40, 68, 89, 144, 192],
    [40, 68, 90, 144, 224],
    [40, 68, 92, 144, 192],
    [40, 68, 94, 144, 192],
    [50, 68, 82, 144, 192],
    [50, 68, 90, 144, 192],
    [66, 176, 192, 224, 226],
    [67, 144, 178, 192, 224],
    [68, 82, 144, 162, 224],
    [68, 82, 144, 176, 224],
    [68, 82, 144, 178, 192],
    [68, 86, 144, 162, 192],
    [68, 86, 144, 192, 224],
    [68, 90, 130, 144, 224],
    [68, 90, 144, 146, 192],
    [68, 90, 144, 162, 224],
    [68, 90, 144, 176, 224],
    [68, 90, 144, 178, 192],
    [68, 94, 130, 144, 192],
    [68, 94, 144, 162, 192],
    [68, 94, 144, 192, 224],
    [70, 144, 192, 224, 226],
    [74, 176, 192, 194, 224],
    [74, 176, 192, 224, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block29_checked : block29.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block30 : List (List Nat) :=
  [[75, 144, 146, 192, 224],
    [75, 144, 178, 192, 224],
    [78, 144, 192, 194, 224],
    [78, 144, 192, 224, 226],
    [82, 144, 176, 178, 224],
    [82, 144, 176, 192, 226],
    [82, 144, 178, 192, 224],
    [82, 176, 192, 224, 226],
    [83, 144, 176, 178, 192],
    [83, 144, 178, 192, 224],
    [86, 144, 176, 192, 226],
    [86, 144, 192, 224, 226],
    [90, 144, 146, 176, 224],
    [90, 144, 146, 192, 224],
    [90, 144, 176, 178, 224],
    [90, 144, 176, 192, 194],
    [90, 144, 176, 192, 226],
    [90, 144, 178, 192, 224],
    [90, 176, 192, 194, 224],
    [90, 176, 192, 224, 226],
    [91, 144, 146, 176, 192],
    [91, 144, 146, 192, 224],
    [91, 144, 176, 178, 192],
    [91, 144, 178, 192, 224],
    [94, 144, 176, 192, 194]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block30_checked : block30.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def block31 : List (List Nat) :=
  [[94, 144, 176, 192, 226],
    [94, 144, 192, 194, 224],
    [94, 144, 192, 224, 226]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma block31_checked : block31.all (fun f => !possibleWithFive f) = true := by
  decide +kernel

def families : List (List Nat) :=
  block00 ++ block01 ++ block02 ++ block03 ++ block04 ++ block05 ++ block06 ++ block07 ++ block08 ++ block09 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20 ++ block21 ++ block22 ++ block23 ++ block24 ++ block25 ++ block26 ++ block27 ++ block28 ++ block29 ++ block30 ++ block31

set_option maxRecDepth 8192 in
lemma census : families.length = 250 ∧
    (families.filter fun f => f.length == 4).length = 22 ∧
    (families.filter fun f => f.length == 5).length = 228 := by
  decide +kernel

def strictlySorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: xs => (a < b) && strictlySorted (b :: xs)

set_option maxRecDepth 8192 in
lemma families_valid : families.all (fun f => strictlySorted f &&
    f.all (fun m => m < 256 && m != 0 && !singleBit m)) = true := by
  decide +kernel

lemma no_five_or_construction : families.all (fun f => !possibleWithFive f) = true := by
  unfold families
  simp only [List.all_append, block00_checked, block01_checked, block02_checked, block03_checked, block04_checked, block05_checked, block06_checked, block07_checked, block08_checked, block09_checked, block10_checked, block11_checked, block12_checked, block13_checked, block14_checked, block15_checked, block16_checked, block17_checked, block18_checked, block19_checked, block20_checked, block21_checked, block22_checked, block23_checked, block24_checked, block25_checked, block26_checked, block27_checked, block28_checked, block29_checked, block30_checked, block31_checked, Bool.true_and]

set_option maxRecDepth 8192 in
lemma families_nodup : families.Nodup := by
  decide +kernel

end R3Family

end PEqualNP.Outside.L_meta_9033_aux
