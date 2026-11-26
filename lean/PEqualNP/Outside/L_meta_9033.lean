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

lemma canUnion_mono (m : Nat) (xs ys : List Nat)
    (hsub : ∀ x ∈ xs, x ∈ ys) (h : canUnion m xs = true) :
    canUnion m ys = true := by
  simp only [canUnion, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨a, ha, ⟨hne, hsubset⟩, hrest⟩
  · exact Or.inl h
  · apply Or.inr
    refine ⟨a, hsub a ha, ⟨hne, hsubset⟩, ?_⟩
    rcases hrest with hbit | ⟨b, hb, hbn, hbor⟩
    · exact Or.inl hbit
    · exact Or.inr ⟨b, hsub b hb, hbn, hbor⟩

lemma filter_lt_head_empty (a : Nat) (xs : List Nat)
    (h : List.Pairwise (fun x y : Nat => x < y) (a :: xs)) :
    (a :: xs).filter (fun x => x < a) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rcases List.mem_cons.mp hx with hx | hx
  · subst x
    simp
  · have hax := (List.pairwise_cons.mp h).1 x hx
    intro hxlt
    have hxa : x < a := of_decide_eq_true hxlt
    omega

lemma fold_builds_locally_closed (xs known : List Nat)
    (hsorted : List.Pairwise (fun x y : Nat => x < y) xs)
    (hready : ∀ m ∈ xs,
      canUnion m (known ++ xs.filter (fun a => a < m)) = true) :
    xs.foldl (fun acc m => if canUnion m acc then m :: acc else acc) known =
      xs.reverse ++ known := by
  induction xs generalizing known with
  | nil => rfl
  | cons a xs ih =>
    have hhead := hready a (by simp)
    rw [filter_lt_head_empty a xs hsorted, List.append_nil] at hhead
    have hnext : ∀ m ∈ xs,
        canUnion m ((a :: known) ++ xs.filter (fun x => x < m)) = true := by
      intro m hm
      apply canUnion_mono m (known ++ (a :: xs).filter (fun x => x < m))
        ((a :: known) ++ xs.filter (fun x => x < m))
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem a hz))
        · have hz' := List.mem_filter.mp hz
          rcases List.mem_cons.mp hz'.1 with heq | hrest
          · subst z
            exact List.mem_append.mpr (Or.inl (by simp))
          · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨hrest, hz'.2⟩))
      · exact hready m (List.mem_cons_of_mem a hm)
    have htail := ih (a :: known) (List.pairwise_cons.mp hsorted).2 hnext
    simp only [List.foldl_cons, hhead, ite_true]
    rw [htail]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

lemma generated_of_local_closure (f : List Nat)
    (hsorted : List.Pairwise (fun x y : Nat => x < y) f)
    (hlocal : ∀ m ∈ f, canUnion m (f.filter (fun a => a < m)) = true) :
    generated f f = true := by
  have hfold := fold_builds_locally_closed f [] hsorted (by simpa using hlocal)
  simp only [List.append_nil] at hfold
  unfold generated closeMasks
  rw [hfold]
  apply List.all_eq_true.mpr
  intro m hm
  simpa only [List.contains_iff_mem, List.mem_reverse] using hm

def rawMask (i : Fin 8) : Nat := singletonMasks.getD i.val 0

lemma rawMask_complete (a : Nat) (h : a ∈ singletonMasks) :
    ∃ i : Fin 8, rawMask i = a := by
  simp only [singletonMasks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

lemma raw_pair_certificate : ∀ i j : Fin 8,
    rawMask i < rawMask i ||| rawMask j →
    rawMask j < rawMask i ||| rawMask j →
    singleBit ((rawMask i ||| rawMask j) &&& ((rawMask i ||| rawMask j) - 1)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma raw_known_certificate : ∀ i : Fin 8, ∀ a : Fin 256,
    a.val < a.val ||| rawMask i →
    singleBit ((a.val ||| rawMask i) ^^^ a.val) = true := by
  decide +kernel

lemma and_or_absorb (a b : Nat) : a &&& (a ||| b) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> rfl

lemma canUnion_of_known_known (m a b : Nat) (known : List Nat)
    (ha : a < m) (hb : b < m) (hor : a ||| b = m)
    (hmemA : a ∈ known) (hmemB : b ∈ known) : canUnion m known = true := by
  have hsubset : a &&& m = a := by rw [← hor]; exact and_or_absorb a b
  have hinner : (known.any fun x => x != m && (a ||| x == m)) = true := by
    apply List.any_eq_true.mpr
    exact ⟨b, hmemB, by simp [Nat.ne_of_lt hb, hor]⟩
  simp only [canUnion, Bool.or_eq_true]
  right
  apply List.any_eq_true.mpr
  exact ⟨a, hmemA, by simp [Nat.ne_of_lt ha, hsubset, hinner]⟩

lemma canUnion_of_known_raw (m a b : Nat) (known : List Nat)
    (hm : m < 256) (ha : a < m) (hor : a ||| b = m)
    (hmemA : a ∈ known) (hmemB : b ∈ singletonMasks) : canUnion m known = true := by
  obtain ⟨i, hi⟩ := rawMask_complete b hmemB
  have hcert := raw_known_certificate i ⟨a, Nat.lt_trans ha hm⟩
  dsimp only at hcert
  rw [hi, hor] at hcert
  have hbit := hcert ha
  have hsubset : a &&& m = a := by rw [← hor]; exact and_or_absorb a b
  simp only [canUnion, Bool.or_eq_true]
  right
  apply List.any_eq_true.mpr
  exact ⟨a, hmemA, by simp [Nat.ne_of_lt ha, hsubset, hbit]⟩

lemma canUnion_of_proper_union (m a b : Nat) (known : List Nat)
    (hm : m < 256) (ha : a < m) (hb : b < m) (hor : a ||| b = m)
    (hmemA : a ∈ singletonMasks ∨ a ∈ known)
    (hmemB : b ∈ singletonMasks ∨ b ∈ known) : canUnion m known = true := by
  rcases hmemA with hrawA | hknownA <;> rcases hmemB with hrawB | hknownB
  · obtain ⟨i, hi⟩ := rawMask_complete a hrawA
    obtain ⟨j, hj⟩ := rawMask_complete b hrawB
    have hcert := raw_pair_certificate i j
    rw [hi, hj, hor] at hcert
    simp only [canUnion, Bool.or_eq_true]
    exact Or.inl (hcert ha hb)
  · exact canUnion_of_known_raw m b a known hm hb
      ((Nat.or_comm b a).trans hor) hknownB hrawA
  · exact canUnion_of_known_raw m a b known hm ha hor hknownA hrawB
  · exact canUnion_of_known_known m a b known ha hb hor hknownA hknownB

lemma generated_of_proper_union_closed (f : List Nat)
    (hsorted : List.Pairwise (fun x y : Nat => x < y) f)
    (hbound : ∀ m ∈ f, m < 256)
    (hclosed : ∀ m ∈ f, ∃ a b, a < m ∧ b < m ∧ a ||| b = m ∧
      (a ∈ singletonMasks ∨ a ∈ f) ∧ (b ∈ singletonMasks ∨ b ∈ f)) :
    generated f f = true := by
  apply generated_of_local_closure f hsorted
  intro m hm
  obtain ⟨a, b, ha, hb, hor, hmemA, hmemB⟩ := hclosed m hm
  apply canUnion_of_proper_union m a b (f.filter fun x => x < m) (hbound m hm) ha hb hor
  · rcases hmemA with hraw | hin
    · exact Or.inl hraw
    · exact Or.inr (List.mem_filter.mpr ⟨hin, by simpa using ha⟩)
  · rcases hmemB with hraw | hin
    · exact Or.inl hraw
    · exact Or.inr (List.mem_filter.mpr ⟨hin, by simpa using hb⟩)

lemma pairwise_of_strictlySorted (f : List Nat) (h : strictlySorted f = true) :
    List.Pairwise (fun x y : Nat => x < y) f := by
  induction f with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      change (decide (a < b) && strictlySorted (b :: xs)) = true at h
      have hparts : a < b ∧ strictlySorted (b :: xs) = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
      have htail := ih hparts.2
      apply List.pairwise_cons.mpr
      refine ⟨?_, htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with heq | hmem
      · subst x
        exact hparts.1
      · exact Nat.lt_trans hparts.1 ((List.pairwise_cons.mp htail).1 x hmem)

lemma generated_targets_subset (required permitted : List Nat)
    (hsub : ∀ m ∈ required, m ∈ permitted)
    (hgen : generated permitted permitted = true) : generated required permitted = true := by
  unfold generated at hgen ⊢
  apply List.all_eq_true.mpr
  intro m hm
  exact (List.all_eq_true.mp hgen) m (hsub m hm)

lemma generated_subset_of_union_closed (required permitted : List Nat)
    (hsub : ∀ m ∈ required, m ∈ permitted)
    (hsorted : strictlySorted permitted = true)
    (hbound : ∀ m ∈ permitted, m < 256)
    (hclosed : ∀ m ∈ permitted, ∃ a b, a < m ∧ b < m ∧ a ||| b = m ∧
      (a ∈ singletonMasks ∨ a ∈ permitted) ∧
      (b ∈ singletonMasks ∨ b ∈ permitted)) : generated required permitted = true := by
  exact generated_targets_subset required permitted hsub
    (generated_of_proper_union_closed permitted (pairwise_of_strictlySorted permitted hsorted)
      hbound hclosed)

lemma mem_insertMask (e x : Nat) (f : List Nat) :
    x ∈ insertMask e f ↔ x = e ∨ x ∈ f := by
  induction f with
  | nil => simp [insertMask]
  | cons a xs ih =>
    by_cases h : e < a
    · simp [insertMask, h]
    · simp [insertMask, h, ih, or_left_comm]

lemma pairwise_insertMask (e : Nat) (f : List Nat)
    (hsorted : List.Pairwise (fun x y : Nat => x < y) f) (hne : e ∉ f) :
    List.Pairwise (fun x y : Nat => x < y) (insertMask e f) := by
  induction f with
  | nil => simp [insertMask]
  | cons a xs ih =>
    have hs := List.pairwise_cons.mp hsorted
    have hneA : e ≠ a := by
      intro heq
      exact hne (List.mem_cons.mpr (Or.inl heq))
    have hneXs : e ∉ xs := by
      intro he
      exact hne (List.mem_cons_of_mem a he)
    by_cases hea : e < a
    · rw [insertMask, ite_eq_left hea]
      apply List.pairwise_cons.mpr
      refine ⟨?_, hsorted⟩
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact hea
      · exact Nat.lt_trans hea (hs.1 x hx)
    · rw [insertMask, ite_eq_right hea]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hs.2 hneXs⟩
      intro x hx
      rcases (mem_insertMask e x xs).mp hx with hx | hx
      · subst x
        omega
      · exact hs.1 x hx

lemma strictlySorted_of_pairwise (f : List Nat)
    (h : List.Pairwise (fun x y : Nat => x < y) f) : strictlySorted f = true := by
  induction f with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      have hs := List.pairwise_cons.mp h
      have hab := hs.1 b (by simp)
      have htail := ih hs.2
      change (decide (a < b) && strictlySorted (b :: xs)) = true
      simp [hab, htail]

lemma strictlySorted_insertMask (e : Nat) (f : List Nat)
    (hsorted : strictlySorted f = true) (hne : e ∉ f) :
    strictlySorted (insertMask e f) = true := by
  exact strictlySorted_of_pairwise _
    (pairwise_insertMask e f (pairwise_of_strictlySorted f hsorted) hne)

lemma required_mem_addExtra (e : Nat) (f : List Nat) :
    ∀ m ∈ f, m ∈ addExtra e f := by
  intro m hm
  unfold addExtra
  split
  · exact hm
  · exact (mem_insertMask e m f).mpr (Or.inr hm)

lemma strictlySorted_addExtra (e : Nat) (f : List Nat)
    (hsorted : strictlySorted f = true) : strictlySorted (addExtra e f) = true := by
  unfold addExtra
  split
  · exact hsorted
  · rename_i hguard
    apply strictlySorted_insertMask e f hsorted
    intro he
    simp [he] at hguard

lemma bounded_addExtra (e : Fin 256) (f : List Nat)
    (hbound : ∀ m ∈ f, m < 256) : ∀ m ∈ addExtra e.val f, m < 256 := by
  intro m hm
  unfold addExtra at hm
  split at hm
  · exact hbound m hm
  · rcases (mem_insertMask e.val m f).mp hm with hm | hm
    · subst m
      exact e.isLt
    · exact hbound m hm

set_option maxRecDepth 8192 in
lemma family_lengths : families.all (fun f => f.length == 4 || f.length == 5) = true := by
  decide +kernel

lemma family_spec (f : List Nat) (hf : f ∈ families) :
    (f.length = 4 ∨ f.length = 5) ∧ strictlySorted f = true ∧
    (∀ m ∈ f, m < 256) := by
  have hlen := (List.all_eq_true.mp family_lengths) f hf
  have hvalid := (List.all_eq_true.mp families_valid) f hf
  have hl : f.length = 4 ∨ f.length = 5 := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hlen
  have hv : strictlySorted f = true ∧
      f.all (fun m => m < 256 && m != 0 && !singleBit m) = true := by
    simpa only [Bool.and_eq_true] using hvalid
  refine ⟨hl, hv.1, ?_⟩
  intro m hm
  have hmask := (List.all_eq_true.mp hv.2) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmask
  exact hmask.1.1

def permittedForFive (f : List Nat) (e : Fin 256) : List Nat :=
  if f.length = 5 then f else addExtra e.val f

lemma required_mem_permittedForFive (f : List Nat) (e : Fin 256) :
    ∀ m ∈ f, m ∈ permittedForFive f e := by
  unfold permittedForFive
  split
  · exact fun _ hm => hm
  · exact required_mem_addExtra e.val f

lemma permittedForFive_spec (f : List Nat) (hf : f ∈ families) (e : Fin 256) :
    strictlySorted (permittedForFive f e) = true ∧
    (∀ m ∈ permittedForFive f e, m < 256) := by
  have hs := family_spec f hf
  unfold permittedForFive
  split
  · exact ⟨hs.2.1, hs.2.2⟩
  · exact ⟨strictlySorted_addExtra e.val f hs.2.1, bounded_addExtra e f hs.2.2⟩

lemma family_generated_false (f : List Nat) (hf : f ∈ families) (e : Fin 256) :
    generated f (permittedForFive f e) = false := by
  have hn := (List.all_eq_true.mp no_five_or_construction) f hf
  have hfalse : possibleWithFive f = false := by simpa using hn
  rcases (family_spec f hf).1 with h4 | h5
  · have hgen : generated f (addExtra e.val f) = false := by
      cases hval : generated f (addExtra e.val f) with
      | false => rfl
      | true =>
        have hex : (List.range 256).any (fun x => generated f (addExtra x f)) = true :=
          List.any_eq_true.mpr ⟨e.val, List.mem_range.mpr e.isLt, hval⟩
        have hp : possibleWithFive f = true := by
          simpa [possibleWithFive, h4] using hex
        rw [hfalse] at hp
        cases hp
    simpa [permittedForFive, h4] using hgen
  · simpa [possibleWithFive, permittedForFive, h5] using hfalse

def properUnionClosed (f : List Nat) : Prop :=
  ∀ m ∈ f, ∃ a b, a < m ∧ b < m ∧ a ||| b = m ∧
    (a ∈ singletonMasks ∨ a ∈ f) ∧ (b ∈ singletonMasks ∨ b ∈ f)

lemma family_no_proper_union_closure (f : List Nat) (hf : f ∈ families) (e : Fin 256) :
    ¬ properUnionClosed (permittedForFive f e) := by
  intro hclosed
  have hp := permittedForFive_spec f hf e
  have hgen := generated_subset_of_union_closed f (permittedForFive f e)
    (required_mem_permittedForFive f e) hp.1 hp.2 hclosed
  rw [family_generated_false f hf e] at hgen
  cases hgen

lemma family_semantic_obstruction (f : List Nat) (hf : f ∈ families) (e : Fin 256) :
    (∀ m ∈ f, m ∈ permittedForFive f e) ∧
    strictlySorted (permittedForFive f e) = true ∧
    (∀ m ∈ permittedForFive f e, m < 256) ∧
    ¬ properUnionClosed (permittedForFive f e) := by
  have hp := permittedForFive_spec f hf e
  exact ⟨required_mem_permittedForFive f e, hp.1, hp.2,
    family_no_proper_union_closure f hf e⟩

end R3Family

namespace BirthRectangle

def crossed (a₀ b₀ a₁ b₁ : Bool) : Prop :=
  (a₀ = true ∧ b₀ = false ∧ a₁ = false ∧ b₁ = true) ∨
  (a₀ = false ∧ b₀ = true ∧ a₁ = true ∧ b₁ = false)

lemma gateBool_distributes (op merge a₀ b₀ a₁ b₁ : Bool)
    (h : op ≠ merge → ¬ crossed a₀ b₀ a₁ b₁) :
    gateBool op (gateBool merge a₀ a₁) (gateBool merge b₀ b₁) =
      gateBool merge (gateBool op a₀ b₀) (gateBool op a₁ b₁) := by
  cases op <;> cases merge <;> cases a₀ <;> cases b₀ <;> cases a₁ <;> cases b₁ <;>
    simp_all [gateBool, crossed]

-- Unless a gate crosses the two rows, evaluation preserves their union or intersection.
lemma causal_merge_agreement
    {n k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = gateBool merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = gateBool (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = gateBool (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = gateBool (op j) (wm (a j)) (wm (b j)))
    (hcross : ∀ j, op j ≠ merge → ¬ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j))) :
    ∀ i, i < n + k → wm i = gateBool merge (w₀ i) (w₁ i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · exact hraw i hin
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      have hea := ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega)
      have heb := ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega)
      rw [hij, hevalm, heval₀, heval₁, hea, heb]
      exact gateBool_distributes _ _ _ _ _ _ (hcross j)

-- A union accepted above two rejected rows forces an AND crossing; the dual forces OR.
lemma crossing_gate_exists
    {n k out : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = gateBool merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = gateBool (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = gateBool (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = gateBool (op j) (wm (a j)) (wm (b j)))
    (hout : out < n + k) (hflip : wm out ≠ gateBool merge (w₀ out) (w₁ out)) :
    ∃ j, op j ≠ merge ∧ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j)) := by
  by_contra h
  apply hflip
  apply causal_merge_agreement a b op merge w₀ w₁ wm ha hb hraw heval₀ heval₁ hevalm
    (fun j hop hc => h ⟨j, hop, hc⟩) out hout

lemma pair_positive_has_and_crossing
    {n k out : Nat} (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ wp : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wp i = (w₀ i || w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = gateBool (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = gateBool (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalp : ∀ j, wp (n + j.val) = gateBool (op j) (wp (a j)) (wp (b j)))
    (hout : out < n + k)
    (hp : wp out = true) (h₀ : w₀ out = false) (h₁ : w₁ out = false) :
    ∃ j, op j = true ∧
      ((w₀ (a j) = true ∧ w₁ (b j) = true) ∨
       (w₁ (a j) = true ∧ w₀ (b j) = true)) := by
  obtain ⟨j, hj, hc⟩ := crossing_gate_exists a b op false w₀ w₁ wp ha hb
    (fun i hi => by simpa [gateBool] using hraw i hi) heval₀ heval₁ hevalp hout
    (by simp [gateBool, hp, h₀, h₁])
  have hop : op j = true := by
    cases h : op j <;> simp_all
  refine ⟨j, hop, ?_⟩
  rcases hc with ⟨ha₀, _, _, hb₁⟩ | ⟨_, hb₀, ha₁, _⟩
  · exact Or.inl ⟨ha₀, hb₁⟩
  · exact Or.inr ⟨ha₁, hb₀⟩

def inputSingletons {V : Type*} (single : V → Nat → Bool) (wire : Nat) : Set V :=
  {v | single v wire = true}

lemma and_input_singletons_disjoint
    {V : Type*} {n k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool)
    (single : V → Nat → Bool) (j : Fin k)
    (heval : ∀ v i, single v (n + i.val) =
      gateBool (op i) (single v (a i)) (single v (b i)))
    (hop : op j = true) (hzero : ∀ v, single v (n + j.val) = false) :
    ∀ v, v ∈ inputSingletons single (a j) →
      v ∈ inputSingletons single (b j) → False := by
  intro v hl hr
  change single v (a j) = true at hl
  change single v (b j) = true at hr
  have h := heval v j
  rw [hzero v] at h
  simp [gateBool, hop, hl, hr] at h

lemma and_singleton_rectangles_cover
    {V : Type*} {n k out : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool)
    (single : V → Nat → Bool) (pair : V → V → Nat → Bool)
    (edge : V → V → Prop)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ u v i, i < n → pair u v i = (single u i || single v i))
    (hsingle : ∀ v j, single v (n + j.val) =
      gateBool (op j) (single v (a j)) (single v (b j)))
    (hpair : ∀ u v j, pair u v (n + j.val) =
      gateBool (op j) (pair u v (a j)) (pair u v (b j)))
    (handzero : ∀ v j, op j = true → single v (n + j.val) = false)
    (hout : out < n + k) (houtzero : ∀ v, single v out = false)
    (hedge : ∀ u v, edge u v → pair u v out = true) :
    ∃ left right : {j : Fin k // op j = true} → Set V,
      (∀ j v, v ∈ left j → v ∈ right j → False) ∧
      ∀ u v, edge u v → ∃ j,
        (u ∈ left j ∧ v ∈ right j) ∨ (v ∈ left j ∧ u ∈ right j) := by
  refine ⟨(fun j => inputSingletons single (a j.val)),
    (fun j => inputSingletons single (b j.val)), ?_, ?_⟩
  · intro j
    exact and_input_singletons_disjoint a b op single j.val hsingle j.property
      (fun v => handzero v j.val j.property)
  · intro u v huv
    obtain ⟨j, hj, hc⟩ := pair_positive_has_and_crossing a b op
      (single u) (single v) (pair u v) ha hb (hraw u v) (hsingle u) (hsingle v)
      (hpair u v) hout (hedge u v huv) (houtzero u) (houtzero v)
    exact ⟨⟨j, hj⟩, hc⟩

lemma causal_pair_merge_before
    {n k : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ wp : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wp i = (w₀ i || w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = gateBool (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = gateBool (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalp : ∀ j, wp (n + j.val) = gateBool (op j) (wp (a j)) (wp (b j)))
    (hprior : ∀ j, j.val < p.val → op j = true →
      wp (n + j.val) = false ∧ w₀ (n + j.val) = false ∧ w₁ (n + j.val) = false) :
    ∀ wire, wire < n + p.val → wp wire = (w₀ wire || w₁ wire) := by
  intro wire
  induction wire using Nat.strong_induction_on with
  | ind wire ih =>
    intro hwire
    by_cases hlow : wire < n
    · exact hraw wire hlow
    · let j : Fin k := ⟨wire - n, by have := p.isLt; omega⟩
      have heq : wire = n + j.val := by dsimp [j]; omega
      have hjp : j.val < p.val := by dsimp [j]; omega
      cases hop : op j with
      | true =>
        obtain ⟨hp, h₀, h₁⟩ := hprior j hjp hop
        rw [heq, hp, h₀, h₁]
        rfl
      | false =>
        have hl := ih (a j) (by have := ha j; omega) (by have := ha j; omega)
        have hr := ih (b j) (by have := hb j; omega) (by have := hb j; omega)
        rw [heq, hevalp, heval₀, heval₁, hl, hr]
        simpa [gateBool] using gateBool_distributes (op j) false
          (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j)) (by simp [hop])

lemma crossed_of_and_or (a₀ b₀ a₁ b₁ : Bool)
    (hp : ((a₀ || a₁) && (b₀ || b₁)) = true)
    (h₀ : (a₀ && b₀) = false) (h₁ : (a₁ && b₁) = false) :
    crossed a₀ b₀ a₁ b₁ := by
  cases a₀ <;> cases b₀ <;> cases a₁ <;> cases b₁ <;> simp_all [crossed]

lemma and_birth_at_crossed
    {n k : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ wp : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wp i = (w₀ i || w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = gateBool (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = gateBool (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalp : ∀ j, wp (n + j.val) = gateBool (op j) (wp (a j)) (wp (b j)))
    (hprior : ∀ j, j.val < p.val → op j = true →
      wp (n + j.val) = false ∧ w₀ (n + j.val) = false ∧ w₁ (n + j.val) = false)
    (hop : op p = true) (hp : wp (n + p.val) = true)
    (h₀ : w₀ (n + p.val) = false) (h₁ : w₁ (n + p.val) = false) :
    crossed (w₀ (a p)) (w₀ (b p)) (w₁ (a p)) (w₁ (b p)) := by
  have hmerge := causal_pair_merge_before p a b op w₀ w₁ wp ha hb hraw
    heval₀ heval₁ hevalp hprior
  have hl := hmerge (a p) (ha p)
  have hr := hmerge (b p) (hb p)
  exact crossed_of_and_or _ _ _ _
    (by simpa [gateBool, hop, hl, hr] using (hevalp p).symm.trans hp)
    (by simpa [gateBool, hop] using (heval₀ p).symm.trans h₀)
    (by simpa [gateBool, hop] using (heval₁ p).symm.trans h₁)

end BirthRectangle

namespace BirthRectangle

def exclusiveInputSingletons {V : Type*} (single : V → Nat → Bool)
    (wire other : Nat) : Set V :=
  {v | single v wire = true ∧ single v other = false}

lemma and_exclusive_singleton_rectangles_cover
    {V : Type*} {n k out : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool)
    (single : V → Nat → Bool) (pair : V → V → Nat → Bool)
    (edge : V → V → Prop)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ u v i, i < n → pair u v i = (single u i || single v i))
    (hsingle : ∀ v j, single v (n + j.val) =
      gateBool (op j) (single v (a j)) (single v (b j)))
    (hpair : ∀ u v j, pair u v (n + j.val) =
      gateBool (op j) (pair u v (a j)) (pair u v (b j)))
    (hout : out < n + k) (houtzero : ∀ v, single v out = false)
    (hedge : ∀ u v, edge u v → pair u v out = true) :
    ∃ left right : {j : Fin k // op j = true} → Set V,
      (∀ j, left j = exclusiveInputSingletons single (a j.val) (b j.val) ∧
        right j = exclusiveInputSingletons single (b j.val) (a j.val)) ∧
      (∀ j v, v ∈ left j → v ∈ right j → False) ∧
      ∀ u v, edge u v → ∃ j,
        (u ∈ left j ∧ v ∈ right j) ∨ (v ∈ left j ∧ u ∈ right j) := by
  refine ⟨(fun j => exclusiveInputSingletons single (a j.val) (b j.val)),
    (fun j => exclusiveInputSingletons single (b j.val) (a j.val)),
    (fun _ => ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro j v hl hr
    change single v (a j.val) = true ∧ single v (b j.val) = false at hl
    change single v (b j.val) = true ∧ single v (a j.val) = false at hr
    have h : (true : Bool) = false := hl.1.symm.trans hr.2
    cases h
  · intro u v huv
    obtain ⟨j, hj, hc⟩ := crossing_gate_exists a b op false
      (single u) (single v) (pair u v) ha hb
      (fun i hi => by simpa [gateBool] using hraw u v i hi)
      (hsingle u) (hsingle v) (hpair u v) hout
      (by simp [gateBool, hedge u v huv, houtzero u, houtzero v])
    have hop : op j = true := by
      cases h : op j <;> simp_all
    refine ⟨⟨j, hop⟩, ?_⟩
    rcases hc with ⟨ha₀, hb₀, ha₁, hb₁⟩ | ⟨ha₀, hb₀, ha₁, hb₁⟩
    · exact Or.inl ⟨⟨ha₀, hb₀⟩, ⟨hb₁, ha₁⟩⟩
    · exact Or.inr ⟨⟨ha₁, hb₁⟩, ⟨hb₀, ha₀⟩⟩

end BirthRectangle

namespace Diamond

def newOp (a b h : Nat) (op : Nat → Bool) (i : Nat) : Bool :=
  if i = a then true else if i = b then true else if i = h then false else op i

def newLeft (a b h q u : Nat) (left : Nat → Nat) (i : Nat) : Nat :=
  if i = a then q else if i = b then u else if i = h then q else left i

def newRight (n a b h q w : Nat) (right : Nat → Nat) (i : Nat) : Nat :=
  if i = a then q else if i = b then w else if i = h then n + b else right i

lemma bool_identity (q u w : Bool) : ((q || u) && (q || w)) = (q || (u && w)) := by
  cases q <;> cases u <;> cases w <;> rfl

lemma rewrite_causal (n k a b h q u w : Nat) (left right : Nat → Nat)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : left a = q ∧ right a = u)
    (hb : left b = q ∧ right b = w) :
    ∀ i < k,
      newLeft a b h q u left i < n + i ∧
      newRight n a b h q w right i < n + i := by
  have hca := hcausal a (by omega)
  have hcb := hcausal b (by omega)
  rw [ha.1, ha.2] at hca
  rw [hb.1, hb.2] at hcb
  intro i hi
  by_cases hia : i = a
  · subst i
    simp only [newLeft, newRight, ite_true]
    exact ⟨hca.1, hca.1⟩
  · by_cases hib : i = b
    · subst i
      simp only [newLeft, newRight, hia, ite_false, ite_true]
      exact ⟨by omega, hcb.2⟩
    · by_cases hih : i = h
      · subst i
        simp only [newLeft, newRight, hia, hib, ite_false, ite_true]
        exact ⟨by omega, by omega⟩
      · simp only [newLeft, newRight, hia, hib, hih, ite_false]
        exact hcausal i hi

lemma agreement (n k a b h q u w : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x y : Nat → Bool)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ left a = q ∧ right a = u)
    (hb : op b = false ∧ left b = q ∧ right b = w)
    (hd : op h = true ∧ left h = n + a ∧ right h = n + b)
    (hprivate : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b))
    (hx : ∀ i < k, x (n + i) = gateBool (op i) (x (left i)) (x (right i)))
    (hy : ∀ i < k, y (n + i) =
      gateBool (newOp a b h op i)
        (y (newLeft a b h q u left i)) (y (newRight n a b h q w right i)))
    (hraw : ∀ j < n, x j = y j) :
    ∀ j < n + k, j ≠ n + a → j ≠ n + b → x j = y j := by
  have hak : a < k := by omega
  have hbk : b < k := by omega
  have hba : b ≠ a := by omega
  have hha : h ≠ a := by omega
  have hhb : h ≠ b := by omega
  have hca := hcausal a hak
  have hcb := hcausal b hbk
  rw [ha.2.1, ha.2.2] at hca
  rw [hb.2.1, hb.2.2] at hcb
  have hwA : w ≠ n + a := by
    have hpriv := (hprivate b hbk (by omega)).2.1
    rwa [hb.2.2] at hpriv
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjA hjB
    by_cases hjraw : j < n
    · exact hraw j hjraw
    · have hi : j - n < k := by omega
      have heq : n + (j - n) = j := by omega
      have hia : j - n ≠ a := by omega
      have hib : j - n ≠ b := by omega
      by_cases hih : j - n = h
      · have hjh : j = n + h := by omega
        have hq : x q = y q := ih q (by omega) (by omega) (by omega) (by omega)
        have hu : x u = y u := ih u (by omega) (by omega) (by omega) (by omega)
        have hw : x w = y w := ih w (by omega) (by omega) hwA (by omega)
        have hxa : x (n + a) = (x q || x u) := by
          simpa only [ha.1, ha.2.1, ha.2.2, gateBool, Bool.false_eq_true, ite_false] using hx a hak
        have hxb : x (n + b) = (x q || x w) := by
          simpa only [hb.1, hb.2.1, hb.2.2, gateBool, Bool.false_eq_true, ite_false] using hx b hbk
        have hxh : x (n + h) = (x (n + a) && x (n + b)) := by
          simpa only [hd.1, hd.2.1, hd.2.2, gateBool, ite_true] using hx h hh
        have hyb : y (n + b) = (y u && y w) := by
          simpa only [newOp, newLeft, newRight, hba, ite_false, ite_true, gateBool] using hy b hbk
        have hyh : y (n + h) = (y q || y (n + b)) := by
          simpa only [newOp, newLeft, newRight, hha, hhb, ite_false, ite_true,
            gateBool, Bool.false_eq_true] using hy h hh
        rw [hjh, hxh, hxa, hxb, hq, hu, hw, bool_identity, hyh, hyb]
      · have hp := hprivate (j - n) hi hih
        have hc := hcausal (j - n) hi
        have hleft : x (left (j - n)) = y (left (j - n)) :=
          ih _ (by omega) (by omega) hp.1.1 hp.1.2
        have hright : x (right (j - n)) = y (right (j - n)) :=
          ih _ (by omega) (by omega) hp.2.1 hp.2.2
        have hxe := hx (j - n) hi
        have hye := hy (j - n) hi
        simp only [newOp, newLeft, newRight, hia, hib, hih, ite_false] at hye
        rw [heq] at hxe hye
        rw [hxe, hye, hleft, hright]

lemma output_agreement (n k a b h q u w out : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x y : Nat → Bool)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ left a = q ∧ right a = u)
    (hb : op b = false ∧ left b = q ∧ right b = w)
    (hd : op h = true ∧ left h = n + a ∧ right h = n + b)
    (hprivate : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b))
    (hx : ∀ i < k, x (n + i) = gateBool (op i) (x (left i)) (x (right i)))
    (hy : ∀ i < k, y (n + i) =
      gateBool (newOp a b h op i)
        (y (newLeft a b h q u left i)) (y (newRight n a b h q w right i)))
    (hraw : ∀ j < n, x j = y j)
    (hout : out < n + k) (houtA : out ≠ n + a) (houtB : out ≠ n + b) : x out = y out := by
  exact agreement n k a b h q u w op left right x y hab hbh hh hcausal ha hb hd
    hprivate hx hy hraw out hout houtA houtB

def gateNat (op : Bool) (x y : Nat) : Nat :=
  if op then x &&& y else x ||| y

lemma testBit_gateNat (op : Bool) (x y bit : Nat) :
    (gateNat op x y).testBit bit = gateBool op (x.testBit bit) (y.testBit bit) := by
  cases op <;> simp [gateNat, gateBool, Nat.testBit_and, Nat.testBit_or]

lemma nat_identity (q u w : Nat) :
    ((q ||| u) &&& (q ||| w)) = (q ||| (u &&& w)) := by
  exact (Nat.or_and_distrib_left q u w).symm

lemma nat_agreement (n k a b h q u w : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x y : Nat → Nat)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ left a = q ∧ right a = u)
    (hb : op b = false ∧ left b = q ∧ right b = w)
    (hd : op h = true ∧ left h = n + a ∧ right h = n + b)
    (hprivate : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b))
    (hx : ∀ i < k, x (n + i) = gateNat (op i) (x (left i)) (x (right i)))
    (hy : ∀ i < k, y (n + i) =
      gateNat (newOp a b h op i)
        (y (newLeft a b h q u left i)) (y (newRight n a b h q w right i)))
    (hraw : ∀ j < n, x j = y j) :
    ∀ j < n + k, j ≠ n + a → j ≠ n + b → x j = y j := by
  intro j hj hjA hjB
  apply Nat.eq_of_testBit_eq
  intro bit
  apply agreement n k a b h q u w op left right
    (fun i => (x i).testBit bit) (fun i => (y i).testBit bit)
    hab hbh hh hcausal ha hb hd hprivate _ _ _ j hj hjA hjB
  · intro i hi
    rw [hx i hi, testBit_gateNat]
  · intro i hi
    rw [hy i hi, testBit_gateNat]
  · intro i hi
    rw [hraw i hi]

lemma rewrite_sources_preserve (n k a b h q u w : Nat) (left right : Nat → Nat)
    (P : Nat → Prop) (hak : a < k) (hbk : b < k)
    (ha : left a = q ∧ right a = u) (hb : right b = w)
    (hold : ∀ i < k, P (left i) ∧ P (right i)) (hnewB : P (n + b)) :
    ∀ i < k, P (newLeft a b h q u left i) ∧ P (newRight n a b h q w right i) := by
  have hq : P q := by rw [← ha.1]; exact (hold a hak).1
  have hu : P u := by rw [← ha.2]; exact (hold a hak).2
  have hw : P w := by rw [← hb]; exact (hold b hbk).2
  intro i hi
  by_cases hia : i = a
  · subst i
    simp only [newLeft, newRight, ite_true]
    exact ⟨hq, hq⟩
  · by_cases hib : i = b
    · subst i
      simp only [newLeft, newRight, hia, ite_false, ite_true]
      exact ⟨hu, hw⟩
    · by_cases hih : i = h
      · subst i
        simp only [newLeft, newRight, hia, hib, ite_false, ite_true]
        exact ⟨hq, hnewB⟩
      · simp only [newLeft, newRight, hia, hib, hih, ite_false]
        exact hold i hi

lemma rewrite_allowed_raw (n k a b h q u w : Nat) (left right : Nat → Nat)
    (allowed : Nat → Prop) (hak : a < k) (hbk : b < k)
    (ha : left a = q ∧ right a = u) (hb : right b = w)
    (hold : ∀ i < k,
      (left i < n → allowed (left i)) ∧ (right i < n → allowed (right i))) :
    ∀ i < k,
      (newLeft a b h q u left i < n → allowed (newLeft a b h q u left i)) ∧
      (newRight n a b h q w right i < n → allowed (newRight n a b h q w right i)) := by
  apply rewrite_sources_preserve n k a b h q u w left right
    (fun v => v < n → allowed v) hak hbk ha hb hold
  intro hbad
  omega


def andCount (op : Nat → Bool) (k : Nat) : Nat :=
  (List.range k).countP op

def orCount (op : Nat → Bool) (k : Nat) : Nat :=
  (List.range k).countP (fun i => !op i)

lemma countP_range_update (p : Nat → Bool) (x k : Nat) (v : Bool) (hx : x < k) :
    (List.range k).countP (fun i => if i = x then v else p i) +
      (if p x then 1 else 0) =
    (List.range k).countP p + (if v then 1 else 0) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hxeq : x = k
    · subst x
      have heq : (List.range k).countP (fun i => if i = k then v else p i) =
          (List.range k).countP p := by
        apply List.countP_congr
        intro i hi
        have hne : i ≠ k := Nat.ne_of_lt (List.mem_range.mp hi)
        simp [hne]
      simp only [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
      simp [heq]
      omega
    · have hlt : x < k := by omega
      have hbal := ih hlt
      have hneq : k ≠ x := Ne.symm hxeq
      simp only [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
      simp only [hneq, ite_false]
      omega

lemma countP_complement (p : Nat → Bool) (xs : List Nat) :
    xs.countP p + xs.countP (fun i => !p i) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, List.length_cons]
    cases h : p x <;> simp <;> omega

lemma andCount_add_orCount (op : Nat → Bool) (k : Nat) :
    andCount op k + orCount op k = k := by
  simpa [andCount, orCount] using countP_complement op (List.range k)

lemma rewrite_andCount (op : Nat → Bool) (a b h k : Nat)
    (hab : a < b) (hbh : b < h) (hhk : h < k)
    (hoa : op a = false) (hob : op b = false) (hoh : op h = true) :
    andCount (newOp a b h op) k = andCount op k + 1 := by
  let p₁ : Nat → Bool := fun i => if i = h then false else op i
  let p₂ : Nat → Bool := fun i => if i = b then true else p₁ i
  have ha : a < k := by omega
  have hb : b < k := by omega
  have hah : a ≠ h := by omega
  have habn : a ≠ b := by omega
  have hbhn : b ≠ h := by omega
  have h₁ := countP_range_update op h k false hhk
  have h₂ := countP_range_update p₁ b k true hb
  have h₃ := countP_range_update p₂ a k true ha
  have hp₁b : p₁ b = false := by simp [p₁, hbhn, hob]
  have hp₂a : p₂ a = false := by simp [p₂, p₁, habn, hah, hoa]
  simp only [hoh, hp₁b, hp₂a, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at h₁ h₂ h₃
  change andCount (newOp a b h op) k = andCount op k + 1
  have hnew : (fun i => if i = a then true else p₂ i) = newOp a b h op := rfl
  rw [hnew] at h₃
  change andCount p₁ k + 1 = andCount op k at h₁
  change andCount p₂ k = andCount p₁ k + 1 at h₂
  change andCount (newOp a b h op) k = andCount p₂ k + 1 at h₃
  omega

lemma rewrite_orCount (op : Nat → Bool) (a b h k : Nat)
    (hab : a < b) (hbh : b < h) (hhk : h < k)
    (hoa : op a = false) (hob : op b = false) (hoh : op h = true) :
    orCount (newOp a b h op) k + 1 = orCount op k := by
  have h₁ := rewrite_andCount op a b h k hab hbh hhk hoa hob hoh
  have h₂ := andCount_add_orCount op k
  have h₃ := andCount_add_orCount (newOp a b h op) k
  omega

end Diamond

namespace ConsumerFrontier

lemma first_false_on_path (w : Nat → Bool) (path : Nat → Nat) (length : Nat)
    (hstart : w (path 0) = true) (hend : w (path length) = false) :
    ∃ i, i < length ∧ (∀ t, t ≤ i → w (path t) = true) ∧
      w (path (i + 1)) = false := by
  have hscan : ∀ l : Nat,
      (∀ t, t ≤ l → w (path t) = true) ∨
      ∃ i, i < l ∧ (∀ t, t ≤ i → w (path t) = true) ∧
        w (path (i + 1)) = false := by
    intro l
    induction l with
    | zero =>
      left
      intro t ht
      have htzero : t = 0 := by omega
      simpa only [htzero] using hstart
    | succ l ih =>
      rcases ih with hbefore | hfound
      · cases hnext : w (path (l + 1)) with
        | false => exact Or.inr ⟨l, by omega, hbefore, hnext⟩
        | true =>
          left
          intro t ht
          by_cases heq : t = l + 1
          · simpa only [heq] using hnext
          · exact hbefore t (by omega)
      · obtain ⟨i, hi, hbefore, hfalse⟩ := hfound
        exact Or.inr ⟨i, by omega, hbefore, hfalse⟩
  rcases hscan length with hbefore | hfound
  · have hbad : (true : Bool) = false :=
      (hbefore length (Nat.le_refl length)).symm.trans hend
    cases hbad
  · exact hfound

lemma false_gate_with_true_input (op x y : Bool)
    (hgate : gateBool op x y = false) (hinput : x = true ∨ y = true) :
    op = true := by
  cases op <;> cases x <;> cases y <;> simp_all [gateBool]

lemma consumer_path_and_frontier {n k : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (heval : ∀ j, w (n + j.val) = gateBool (op j) (w (a j)) (w (b j)))
    (path : Nat → Nat) (length : Nat)
    (hstep : ∀ i, i < length → ∃ j : Fin k,
      path (i + 1) = n + j.val ∧ (path i = a j ∨ path i = b j))
    (hstart : w (path 0) = true) (hend : w (path length) = false) :
    ∃ i, i < length ∧ (∀ t, t ≤ i → w (path t) = true) ∧
      ∃ j : Fin k, path (i + 1) = n + j.val ∧ op j = true ∧
        w (n + j.val) = false ∧ (w (a j) = true ∨ w (b j) = true) := by
  obtain ⟨i, hi, hbefore, hfalse⟩ := first_false_on_path w path length hstart hend
  obtain ⟨j, hj, hparent⟩ := hstep i hi
  have hzero : w (n + j.val) = false := hj ▸ hfalse
  have hinput : w (a j) = true ∨ w (b j) = true := by
    rcases hparent with ha | hb
    · exact Or.inl (ha ▸ hbefore i (Nat.le_refl i))
    · exact Or.inr (hb ▸ hbefore i (Nat.le_refl i))
  have hop : op j = true := false_gate_with_true_input _ _ _
    ((heval j).symm.trans hzero) hinput
  exact ⟨i, hi, hbefore, j, hj, hop, hzero, hinput⟩

lemma consumer_path_and_frontier_outside {n k : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (heval : ∀ j, w (n + j.val) = gateBool (op j) (w (a j)) (w (b j)))
    (path : Nat → Nat) (length : Nat)
    (hstep : ∀ i, i < length → ∃ j : Fin k,
      path (i + 1) = n + j.val ∧ (path i = a j ∨ path i = b j))
    (hstart : w (path 0) = true) (hend : w (path length) = false)
    (trueGates : Set (Fin k)) (htrue : ∀ j ∈ trueGates, w (n + j.val) = true) :
    ∃ j : Fin k, op j = true ∧ w (n + j.val) = false ∧
      (w (a j) = true ∨ w (b j) = true) ∧ j ∉ trueGates := by
  obtain ⟨_, _, _, j, _, hop, hzero, hinput⟩ :=
    consumer_path_and_frontier a b op w heval path length hstep hstart hend
  refine ⟨j, hop, hzero, hinput, ?_⟩
  intro hjtrue
  have hbad : (true : Bool) = false := (htrue j hjtrue).symm.trans hzero
  cases hbad

end ConsumerFrontier

namespace Diamond

lemma causal_nat_evaluation_exists (n k : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (init : Nat → Nat)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i) :
    ∃ v : Nat → Nat, (∀ j < n, v j = init j) ∧
      ∀ i < k, v (n + i) = gateNat (op i) (v (left i)) (v (right i)) := by
  induction k with
  | zero =>
    exact ⟨init, fun _ _ => rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ k ih =>
    obtain ⟨v, hraw, heval⟩ := ih (fun i hi => hcausal i (by omega))
    let value := gateNat (op k) (v (left k)) (v (right k))
    let next : Nat → Nat := fun j => if j = n + k then value else v j
    refine ⟨next, ?_, ?_⟩
    · intro j hj
      have hne : j ≠ n + k := by omega
      simpa only [next, hne, ite_false] using hraw j hj
    · intro i hi
      by_cases hik : i = k
      · subst i
        have hc := hcausal k (by omega)
        have hl : left k ≠ n + k := by omega
        have hr : right k ≠ n + k := by omega
        simp only [next, hl, hr, ite_false, ite_true, value]
      · have hik' : i < k := by omega
        have hc := hcausal i (by omega)
        have hw : n + i ≠ n + k := by omega
        have hl : left i ≠ n + k := by omega
        have hr : right i ≠ n + k := by omega
        simpa only [next, hw, hl, hr, ite_false] using heval i hik'

lemma exists_nat_rewrite (n k a b h q u w : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) (allowed : Nat → Prop)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ left a = q ∧ right a = u)
    (hb : op b = false ∧ left b = q ∧ right b = w)
    (hd : op h = true ∧ left h = n + a ∧ right h = n + b)
    (hprivate : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b))
    (hx : ∀ i < k, x (n + i) = gateNat (op i) (x (left i)) (x (right i)))
    (hallowed : ∀ i < k,
      (left i < n → allowed (left i)) ∧ (right i < n → allowed (right i))) :
    ∃ y : Nat → Nat,
      (∀ j < n, y j = x j) ∧
      (∀ i < k, y (n + i) = gateNat (newOp a b h op i)
        (y (newLeft a b h q u left i)) (y (newRight n a b h q w right i))) ∧
      (∀ j < n + k, j ≠ n + a → j ≠ n + b → x j = y j) ∧
      (∀ i < k, newLeft a b h q u left i < n + i ∧
        newRight n a b h q w right i < n + i) ∧
      (∀ i < k,
        (newLeft a b h q u left i < n → allowed (newLeft a b h q u left i)) ∧
        (newRight n a b h q w right i < n → allowed (newRight n a b h q w right i))) ∧
      andCount (newOp a b h op) k = andCount op k + 1 ∧
      orCount (newOp a b h op) k + 1 = orCount op k := by
  have hcnew := rewrite_causal n k a b h q u w left right hab hbh hh hcausal ha.2 hb.2
  obtain ⟨y, hyraw, hyeval⟩ := causal_nat_evaluation_exists n k (newOp a b h op)
    (newLeft a b h q u left) (newRight n a b h q w right) x hcnew
  refine ⟨y, hyraw, hyeval, ?_, hcnew, ?_, ?_, ?_⟩
  · exact nat_agreement n k a b h q u w op left right x y hab hbh hh hcausal
      ha hb hd hprivate hx hyeval (fun j hj => (hyraw j hj).symm)
  · exact rewrite_allowed_raw n k a b h q u w left right allowed (by omega) (by omega)
      ha.2 hb.2.2 hallowed
  · exact rewrite_andCount op a b h k hab hbh hh ha.1 hb.1 hd.1
  · exact rewrite_orCount op a b h k hab hbh hh ha.1 hb.1 hd.1

end Diamond

namespace ConsumerFrontier

def consumerReachable {k : Nat} (n : Nat) (a b : Fin k → Nat)
    (source target : Nat) : Prop :=
  ∃ length : Nat, ∃ path : Nat → Nat,
    path 0 = source ∧ path length = target ∧
    ∀ i, i < length → ∃ j : Fin k,
      path (i + 1) = n + j.val ∧ (path i = a j ∨ path i = b j)

lemma consumerReachable_refl {k : Nat} (n : Nat) (a b : Fin k → Nat) (wire : Nat) :
    consumerReachable n a b wire wire := by
  refine ⟨0, fun _ => wire, rfl, rfl, ?_⟩
  intro i hi
  omega

lemma consumerReachable_extend {n k : Nat} (a b : Fin k → Nat)
    (source wire : Nat) (j : Fin k)
    (hpath : consumerReachable n a b source wire)
    (hparent : wire = a j ∨ wire = b j) :
    consumerReachable n a b source (n + j.val) := by
  obtain ⟨length, path, hfirst, hlast, hstep⟩ := hpath
  refine ⟨length + 1, (fun t => if t ≤ length then path t else n + j.val), ?_, ?_, ?_⟩
  · simpa only [show 0 ≤ length by omega, ite_true] using hfirst
  · simp only [show ¬length + 1 ≤ length by omega, ite_false]
  · intro i hi
    by_cases hbefore : i < length
    · obtain ⟨q, hq, hparentq⟩ := hstep i hbefore
      refine ⟨q, ?_, ?_⟩
      · simpa only [show i + 1 ≤ length by omega, ite_true] using hq
      · simpa only [show i ≤ length by omega, ite_true] using hparentq
    · have heq : i = length := by omega
      subst i
      refine ⟨j, ?_, ?_⟩
      · simp only [show ¬length + 1 ≤ length by omega, ite_false]
      · simpa only [Nat.le_refl, ite_true, hlast] using hparent

lemma differing_target_has_consumer_path {α : Type} {n k : Nat}
    (a b : Fin k → Nat) (run : Fin k → α → α → α) (p : Fin k)
    (x y : Nat → α)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → x i = y i)
    (hx : ∀ j, j ≠ p → x (n + j.val) = run j (x (a j)) (x (b j)))
    (hy : ∀ j, j ≠ p → y (n + j.val) = run j (y (a j)) (y (b j))) :
    ∀ out, out < n + k → x out ≠ y out →
      consumerReachable n a b (n + p.val) out := by
  classical
  intro out
  induction out using Nat.strong_induction_on with
  | ind out ih =>
    intro hout hdiff
    by_cases hrawout : out < n
    · exact False.elim (hdiff (hraw out hrawout))
    by_cases hcut : out = n + p.val
    · subst out
      exact consumerReachable_refl n a b (n + p.val)
    let j : Fin k := ⟨out - n, by omega⟩
    have houtj : out = n + j.val := by dsimp [j]; omega
    have hne : j ≠ p := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp [j] at hval
      omega
    have hca := ha j
    have hcb := hb j
    by_cases hleft : x (a j) = y (a j)
    · have hright : x (b j) ≠ y (b j) := by
        intro heq
        apply hdiff
        rw [houtj, hx j hne, hy j hne, hleft, heq]
      have hpath := ih (b j) (by omega) (by omega) hright
      rw [houtj]
      exact consumerReachable_extend a b (n + p.val) (b j) j hpath (Or.inr rfl)
    · have hpath := ih (a j) (by omega) (by omega) hleft
      rw [houtj]
      exact consumerReachable_extend a b (n + p.val) (a j) j hpath (Or.inl rfl)

end ConsumerFrontier

namespace Diamond

lemma no_private_diamond_of_or_lower_bound
    (n k a b h q u w out bound : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) (allowed : Nat → Prop)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ left a = q ∧ right a = u)
    (hb : op b = false ∧ left b = q ∧ right b = w)
    (hd : op h = true ∧ left h = n + a ∧ right h = n + b)
    (hprivate : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b))
    (hx : ∀ i < k, x (n + i) = gateNat (op i) (x (left i)) (x (right i)))
    (hallowed : ∀ i < k,
      (left i < n → allowed (left i)) ∧ (right i < n → allowed (right i)))
    (hout : out < n + k) (houtA : out ≠ n + a) (houtB : out ≠ n + b)
    (hcount : orCount op k ≤ bound)
    (hlower : ∀ (op' : Nat → Bool) (left' right' : Nat → Nat) (y : Nat → Nat),
      (∀ i < k, left' i < n + i ∧ right' i < n + i) →
      (∀ i < k,
        (left' i < n → allowed (left' i)) ∧ (right' i < n → allowed (right' i))) →
      (∀ j < n, y j = x j) →
      (∀ i < k, y (n + i) = gateNat (op' i) (y (left' i)) (y (right' i))) →
      y out = x out → bound ≤ orCount op' k) : False := by
  obtain ⟨y, hyraw, hyeval, hagree, hcnew, hanew, _, hdelta⟩ :=
    exists_nat_rewrite n k a b h q u w op left right x allowed hab hbh hh
      hcausal ha hb hd hprivate hx hallowed
  have hyout : y out = x out := (hagree out hout houtA houtB).symm
  have hbound := hlower (newOp a b h op) (newLeft a b h q u left)
    (newRight n a b h q w right) y hcnew hanew hyraw hyeval hyout
  omega

end Diamond

namespace ConsumerFrontier

def flipAt (op : Nat → Bool) (p i : Nat) : Bool :=
  if i = p then !(op p) else op i

lemma flipAt_breaks_simultaneous_bounds (op : Nat → Bool) (p k : Nat) (hp : p < k) :
    ¬ (Diamond.andCount op k ≤ Diamond.andCount (flipAt op p) k ∧
      Diamond.orCount op k ≤ Diamond.orCount (flipAt op p) k) := by
  intro hbounds
  have hold := Diamond.andCount_add_orCount op k
  have hnew := Diamond.andCount_add_orCount (flipAt op p) k
  have heq : Diamond.andCount (flipAt op p) k = Diamond.andCount op k := by omega
  have hchange := Diamond.countP_range_update op p k (!(op p)) hp
  change Diamond.andCount (flipAt op p) k + (if op p then 1 else 0) =
    Diamond.andCount op k + (if !(op p) then 1 else 0) at hchange
  rw [heq] at hchange
  cases hop : op p <;> simp [hop] at hchange

def fixedParentsOperationMinimal (n k out : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) : Prop :=
  ∀ (op' : Nat → Bool) (y : Nat → Nat),
    (∀ j < n, y j = x j) →
    (∀ i < k, y (n + i) = Diamond.gateNat (op' i) (y (left i)) (y (right i))) →
    y out = x out →
    Diamond.andCount op k ≤ Diamond.andCount op' k ∧
      Diamond.orCount op k ≤ Diamond.orCount op' k

lemma operation_minimal_gate_reachable (n k out : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (hx : ∀ i < k, x (n + i) = Diamond.gateNat (op i) (x (left i)) (x (right i)))
    (hout : out < n + k)
    (hminimal : fixedParentsOperationMinimal n k out op left right x)
    (p : Fin k) :
    consumerReachable n (fun j : Fin k => left j.val) (fun j : Fin k => right j.val)
      (n + p.val) out := by
  obtain ⟨y, hyraw, hyeval⟩ := Diamond.causal_nat_evaluation_exists n k
    (flipAt op p.val) left right x hcausal
  have hdiff : x out ≠ y out := by
    intro heq
    exact flipAt_breaks_simultaneous_bounds op p.val k p.isLt
      (hminimal (flipAt op p.val) y hyraw hyeval heq.symm)
  apply differing_target_has_consumer_path
    (fun j : Fin k => left j.val) (fun j : Fin k => right j.val)
    (fun j : Fin k => Diamond.gateNat (op j.val)) p x y
    (fun j => (hcausal j.val j.isLt).1) (fun j => (hcausal j.val j.isLt).2)
    (fun i hi => (hyraw i hi).symm) _ _ out hout hdiff
  · intro j _
    exact hx j.val j.isLt
  · intro j hne
    have hvals : j.val ≠ p.val := by
      intro heq
      exact hne (Fin.ext heq)
    simpa only [flipAt, hvals, ite_false] using hyeval j.val j.isLt

lemma operation_minimal_true_gate_frontier_outside
    (n k out : Nat) (op : Nat → Bool) (left right : Nat → Nat) (x : Nat → Nat)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (hx : ∀ i < k, x (n + i) = Diamond.gateNat (op i) (x (left i)) (x (right i)))
    (hout : out < n + k)
    (hminimal : fixedParentsOperationMinimal n k out op left right x)
    (w : Nat → Bool)
    (hw : ∀ i < k, w (n + i) = gateBool (op i) (w (left i)) (w (right i)))
    (hwout : w out = false) (p : Fin k) (hp : w (n + p.val) = true)
    (trueGates : Set (Fin k)) (htrue : ∀ j ∈ trueGates, w (n + j.val) = true) :
    ∃ j : Fin k, op j.val = true ∧ w (n + j.val) = false ∧
      (w (left j.val) = true ∨ w (right j.val) = true) ∧ j ∉ trueGates := by
  obtain ⟨length, path, hfirst, hlast, hstep⟩ :=
    operation_minimal_gate_reachable n k out op left right x hcausal hx hout hminimal p
  exact consumer_path_and_frontier_outside
    (fun j : Fin k => left j.val) (fun j : Fin k => right j.val)
    (fun j : Fin k => op j.val) w (fun j => hw j.val j.isLt) path length hstep
    (by rw [hfirst]; exact hp) (by rw [hlast]; exact hwout) trueGates htrue

end ConsumerFrontier

end PEqualNP.Outside.L_meta_9033_aux
