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

namespace CopyElimination

lemma countP_range_succ (op : Nat → Bool) (m : Nat) :
    (List.range (m + 1)).countP op =
      (List.range m).countP op + (if op m then 1 else 0) := by
  simp [List.range_succ]

lemma countP_range_skipIndex (op : Nat → Bool) (m p : Nat) (hp : p < m) :
    (List.range (m - 1)).countP (fun i => op (skipIndex p i)) +
      (if op p then 1 else 0) = (List.range m).countP op := by
  induction m generalizing p with
  | zero => omega
  | succ m ih =>
    by_cases hpm : p < m
    · have hm : m - 1 + 1 = m := by omega
      have hskip : skipIndex p (m - 1) = m := by
        unfold skipIndex
        split <;> omega
      have hstep := countP_range_succ (fun i => op (skipIndex p i)) (m - 1)
      rw [hm, hskip] at hstep
      have hprevious := ih p hpm
      simp only [Nat.succ_sub_one]
      rw [hstep, countP_range_succ]
      omega
    · have hp' : p = m := by omega
      subst p
      have hsame : (List.range m).countP (fun i => op (skipIndex m i)) =
          (List.range m).countP op := by
        apply List.countP_congr
        intro i hi
        have hlt := List.mem_range.mp hi
        simp [skipIndex, hlt]
      simp only [Nat.succ_sub_one]
      rw [hsame, countP_range_succ]

lemma and_count_delete_balance (op : Nat → Bool) (m p : Nat) (hp : p < m) :
    (List.range (m - 1)).countP (fun i => op (skipIndex p i)) +
      (if op p then 1 else 0) = (List.range m).countP op :=
  countP_range_skipIndex op m p hp

lemma or_count_delete_balance (op : Nat → Bool) (m p : Nat) (hp : p < m) :
    (List.range (m - 1)).countP (fun i => !(op (skipIndex p i))) +
      (if !(op p) then 1 else 0) = (List.range m).countP (fun i => !(op i)) :=
  countP_range_skipIndex (fun i => !(op i)) m p hp

lemma and_count_delete_of_true (op : Nat → Bool) (m p : Nat)
    (hp : p < m) (hop : op p = true) :
    (List.range (m - 1)).countP (fun i => op (skipIndex p i)) + 1 =
      (List.range m).countP op := by
  simpa [hop] using and_count_delete_balance op m p hp

lemma and_count_delete_of_false (op : Nat → Bool) (m p : Nat)
    (hp : p < m) (hop : op p = false) :
    (List.range (m - 1)).countP (fun i => op (skipIndex p i)) =
      (List.range m).countP op := by
  simpa [hop] using and_count_delete_balance op m p hp

lemma or_count_delete_of_true (op : Nat → Bool) (m p : Nat)
    (hp : p < m) (hop : op p = true) :
    (List.range (m - 1)).countP (fun i => !(op (skipIndex p i))) =
      (List.range m).countP (fun i => !(op i)) := by
  simpa [hop] using or_count_delete_balance op m p hp

lemma or_count_delete_of_false (op : Nat → Bool) (m p : Nat)
    (hp : p < m) (hop : op p = false) :
    (List.range (m - 1)).countP (fun i => !(op (skipIndex p i))) + 1 =
      (List.range m).countP (fun i => !(op i)) := by
  simpa [hop] using or_count_delete_balance op m p hp

lemma countP_partition {α : Type*} (l : List α) (op marked : α → Bool) :
    l.countP op = l.countP (fun i => op i && !(marked i)) +
      l.countP (fun i => op i && marked i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases op a <;> cases marked a <;> simp <;> omega

lemma countP_range_partition (m : Nat) (op marked : Nat → Bool) :
    (List.range m).countP op =
      (List.range m).countP (fun i => op i && !(marked i)) +
      (List.range m).countP (fun i => op i && marked i) :=
  countP_partition (List.range m) op marked

lemma or_count_range_partition (m : Nat) (op marked : Nat → Bool) :
    (List.range m).countP (fun i => !(op i)) =
      (List.range m).countP (fun i => !(op i) && !(marked i)) +
      (List.range m).countP (fun i => !(op i) && marked i) :=
  countP_partition (List.range m) (fun i => !(op i)) marked

end CopyElimination

namespace PinOne

lemma causal_true_transport {σ : Type*}
    (n k : Nat) (op : Nat → Bool) (a b : Nat → Nat)
    (w : Nat → Bool) (v : σ → Nat → Bool)
    (hcausal : ∀ i < k, a i < n + i ∧ b i < n + i)
    (hw : ∀ i < k, w (n + i) = gateBool (op i) (w (a i)) (w (b i)))
    (hv : ∀ s i, i < k → v s (n + i) =
      gateBool (op i) (v s (a i)) (v s (b i)))
    (hraw : ∀ s i, i < n → w i = true → v s i = true) :
    ∀ s wire, wire < n + k → w wire = true → v s wire = true := by
  intro s wire
  induction wire using Nat.strong_induction_on with
  | ind wire ih =>
    intro hwire hvalue
    by_cases hlow : wire < n
    · exact hraw s wire hlow hvalue
    · have hi : wire - n < k := by omega
      have heq : n + (wire - n) = wire := by omega
      have hleft : a (wire - n) < wire := by
        have h := (hcausal (wire - n) hi).1
        omega
      have hright : b (wire - n) < wire := by
        have h := (hcausal (wire - n) hi).2
        omega
      have hwe := hw (wire - n) hi
      have hve := hv s (wire - n) hi
      rw [heq] at hwe hve
      rw [hwe] at hvalue
      rw [hve]
      exact gateBool_mono _ _ _ _ _
        (ih _ hleft (by omega)) (ih _ hright (by omega)) hvalue

lemma causal_pin_copy_certificates {σ : Type*}
    (n k x : Nat) (op : Nat → Bool) (a b : Nat → Nat)
    (w : Nat → Bool) (v : σ → Nat → Bool)
    (hx : x < n) (hpinned : ∀ s, v s x = true)
    (hcausal : ∀ i < k, a i < n + i ∧ b i < n + i)
    (hw : ∀ i < k, w (n + i) = gateBool (op i) (w (a i)) (w (b i)))
    (hv : ∀ s i, i < k → v s (n + i) =
      gateBool (op i) (v s (a i)) (v s (b i)))
    (hraw : ∀ s i, i < n → w i = true → v s i = true) :
    (∀ p, p < k → w (n + p) = true →
      x < n + p ∧ ∀ s, v s (n + p) = v s x) ∧
    (∀ p, p < k → op p = true → w (a p) = true →
      b p < n + p ∧ ∀ s, v s (n + p) = v s (b p)) ∧
    (∀ p, p < k → op p = true → w (b p) = true →
      a p < n + p ∧ ∀ s, v s (n + p) = v s (a p)) := by
  have htransfer := causal_true_transport n k op a b w v hcausal hw hv hraw
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hvalue
    refine ⟨by omega, ?_⟩
    intro s
    exact (htransfer s (n + p) (by omega) hvalue).trans (hpinned s).symm
  · intro p hp hop hleft
    refine ⟨(hcausal p hp).2, ?_⟩
    intro s
    have hs : v s (a p) = true :=
      htransfer s (a p) (by have h := (hcausal p hp).1; omega) hleft
    rw [hv s p hp]
    simp [gateBool, hop, hs]
  · intro p hp hop hright
    refine ⟨(hcausal p hp).1, ?_⟩
    intro s
    have hs : v s (b p) = true :=
      htransfer s (b p) (by have h := (hcausal p hp).2; omega) hright
    rw [hv s p hp]
    simp [gateBool, hop, hs]

lemma raw_implication_of_pinned_singleton {σ : Type*}
    (n x : Nat) (w : Nat → Bool) (v : σ → Nat → Bool)
    (hraw : ∀ i, i < n → w i = true → i = x)
    (hpinned : ∀ s, v s x = true) :
    ∀ s i, i < n → w i = true → v s i = true := by
  intro s i hi htrue
  rw [hraw i hi htrue]
  exact hpinned s

end PinOne

namespace CopyElimination

lemma eliminate_marked_copies {σ : Type} (reference : σ) (n m out : Nat)
    (op : Nat → Bool) (left right : Nat → Nat) (v : σ → Nat → Bool)
    (marked : Nat → Bool) (source : Nat → Nat)
    (hout : out < n + m)
    (hcausal : ∀ i < m, left i < n + i ∧ right i < n + i)
    (heval : ∀ s i, i < m →
      v s (n + i) = gateBool (op i) (v s (left i)) (v s (right i)))
    (hsource : ∀ i < m, marked i = true → source i < n + i)
    (hcopy : ∀ s i, i < m → marked i = true → v s (n + i) = v s (source i))
    (hclean : ∀ i < m, marked i = false →
      v reference (left i) = false ∧ v reference (right i) = false) :
    ∃ (m' : Nat) (op' : Nat → Bool) (left' right' : Nat → Nat)
        (out' : Nat) (v' : σ → Nat → Bool),
      m' ≤ m ∧ out' < n + m' ∧
      (∀ i < m', left' i < n + i ∧ right' i < n + i) ∧
      (∀ s j, j < n → v' s j = v s j) ∧
      (∀ s i, i < m' →
        v' s (n + i) = gateBool (op' i) (v' s (left' i)) (v' s (right' i))) ∧
      (∀ s, v' s out' = v s out) ∧
      (List.range m').countP op' =
        (List.range m).countP (fun i => op i && !(marked i)) ∧
      (List.range m').countP (fun i => !(op' i)) =
        (List.range m).countP (fun i => !(op i) && !(marked i)) ∧
      (∀ i < m', v' reference (left' i) = false ∧ v' reference (right' i) = false) := by
  classical
  induction m using Nat.strong_induction_on generalizing out op left right v marked source with
  | ind m ih =>
    by_cases hsome : ∃ p, p < m ∧ marked p = true
    · obtain ⟨p, hp, hmarked⟩ := hsome
      let q := source p
      have hq : q < n + p := hsource p hp hmarked
      let op₁ := fun i => op (skipIndex p i)
      let left₁ := fun i => routeIndex (n + p) q (left (skipIndex p i))
      let right₁ := fun i => routeIndex (n + p) q (right (skipIndex p i))
      let out₁ := routeIndex (n + p) q out
      let v₁ := fun s j => v s (skipIndex (n + p) j)
      let marked₁ := fun i => marked (skipIndex p i)
      let source₁ := fun i => routeIndex (n + p) q (source (skipIndex p i))
      have hcopyq : ∀ s, v s (n + p) = v s q := fun s => hcopy s p hp hmarked
      have hout₁ : out₁ < n + (m - 1) := routeIndex_output_lt n m p q out hp hq hout
      have hcausal₁ : ∀ i < m - 1, left₁ i < n + i ∧ right₁ i < n + i :=
        deleteGate_causal n m p q left right hp hq hcausal
      have heval₁ : ∀ s i, i < m - 1 →
          v₁ s (n + i) = gateBool (op₁ i) (v₁ s (left₁ i)) (v₁ s (right₁ i)) := by
        intro s
        exact deleteGate_equations n m p q (fun i => gateBool (op i)) left right
          (v s) hp hq (fun i hi _ => heval s i hi) (hcopyq s)
      have hsource₁ : ∀ i < m - 1, marked₁ i = true → source₁ i < n + i := by
        intro i hi hm
        apply routeIndex_lt_skip (n + p) q _ (n + i) hq
        rw [skipIndex_add]
        exact hsource (skipIndex p i) (skipIndex_lt m p i hp hi) hm
      have hcopy₁ : ∀ s i, i < m - 1 → marked₁ i = true →
          v₁ s (n + i) = v₁ s (source₁ i) := by
        intro s i hi hm
        change v s (skipIndex (n + p) (n + i)) =
          v s (skipIndex (n + p) (routeIndex (n + p) q (source (skipIndex p i))))
        rw [skipIndex_add, skip_route_eval (n + p) q (v s) hq (hcopyq s)]
        exact hcopy s (skipIndex p i) (skipIndex_lt m p i hp hi) hm
      have hclean₁ : ∀ i < m - 1, marked₁ i = false →
          v₁ reference (left₁ i) = false ∧ v₁ reference (right₁ i) = false := by
        intro i hi hm
        change v reference (skipIndex (n + p) (routeIndex (n + p) q (left (skipIndex p i)))) = false ∧
          v reference (skipIndex (n + p) (routeIndex (n + p) q (right (skipIndex p i)))) = false
        rw [skip_route_eval (n + p) q (v reference) hq (hcopyq reference),
          skip_route_eval (n + p) q (v reference) hq (hcopyq reference)]
        exact hclean (skipIndex p i) (skipIndex_lt m p i hp hi) hm
      obtain ⟨m', op', left', right', out', v', hm', hout', hc', hr', he', ho', ha', hor', hcl'⟩ :=
        ih (m - 1) (by omega) out₁ op₁ left₁ right₁ v₁ marked₁ source₁
          hout₁ hcausal₁ heval₁ hsource₁ hcopy₁ hclean₁
      refine ⟨m', op', left', right', out', v', by omega, hout', hc', ?_, he', ?_, ?_, ?_, hcl'⟩
      · intro s j hj
        exact (hr' s j hj).trans (deleteGate_raw n p (v s) j hj)
      · intro s
        exact (ho' s).trans (deleteGate_output n p q out (v s) hq (hcopyq s))
      · rw [ha']
        have hh := countP_range_skipIndex (fun i => op i && !(marked i)) m p hp
        simpa only [hmarked, Bool.not_true, Bool.and_false, Bool.false_eq_true,
          ite_false, Nat.add_zero] using hh
      · rw [hor']
        have hh := countP_range_skipIndex (fun i => !(op i) && !(marked i)) m p hp
        simpa only [hmarked, Bool.not_true, Bool.and_false, Bool.false_eq_true,
          ite_false, Nat.add_zero] using hh
    · have hmfalse : ∀ i < m, marked i = false := by
        intro i hi
        cases heq : marked i with
        | false => rfl
        | true => exact False.elim (hsome ⟨i, hi, heq⟩)
      refine ⟨m, op, left, right, out, v, Nat.le_refl m, hout, hcausal,
        fun _ _ _ => rfl, heval, fun _ => rfl, ?_, ?_, ?_⟩
      · apply List.countP_congr
        intro i hi
        simp only [hmfalse i (List.mem_range.mp hi), Bool.not_false, Bool.and_true]
      · apply List.countP_congr
        intro i hi
        simp only [hmfalse i (List.mem_range.mp hi), Bool.not_false, Bool.and_true]
      · intro i hi
        exact hclean i hi (hmfalse i hi)

end CopyElimination

namespace CopyElimination

def pinMarked (w : Nat → Bool) (left right : Nat → Nat) (i : Nat) : Bool :=
  w (left i) || w (right i)

def pinCopySource (x : Nat) (op : Nat → Bool) (w : Nat → Bool)
    (left right : Nat → Nat) (i : Nat) : Nat :=
  if op i then if w (left i) then right i else left i else x

lemma pin_marked_copy_certificates {σ : Type} (reference : σ) (n m x : Nat)
    (op : Nat → Bool) (left right : Nat → Nat) (v : σ → Nat → Bool)
    (hx : x < n) (hpinned : ∀ s, v s x = true)
    (hcausal : ∀ i < m, left i < n + i ∧ right i < n + i)
    (heval : ∀ s i, i < m →
      v s (n + i) = gateBool (op i) (v s (left i)) (v s (right i)))
    (hraw : ∀ i, i < n → v reference i = true → i = x) :
    (∀ i < m, pinMarked (v reference) left right i = true →
      pinCopySource x op (v reference) left right i < n + i) ∧
    (∀ s i, i < m → pinMarked (v reference) left right i = true →
      v s (n + i) = v s (pinCopySource x op (v reference) left right i)) ∧
    (∀ i < m, pinMarked (v reference) left right i = false →
      v reference (left i) = false ∧ v reference (right i) = false) := by
  have cert := PinOne.causal_pin_copy_certificates n m x op left right
    (v reference) v hx hpinned hcausal (heval reference) heval
    (PinOne.raw_implication_of_pinned_singleton n x (v reference) v hraw hpinned)
  have hboth : ∀ i, i < m → pinMarked (v reference) left right i = true →
      pinCopySource x op (v reference) left right i < n + i ∧
      ∀ s, v s (n + i) = v s (pinCopySource x op (v reference) left right i) := by
    intro i hi hm
    cases hop : op i with
    | false =>
      have ht : v reference (n + i) = true := by
        rw [heval reference i hi]
        simpa only [gateBool, hop, Bool.false_eq_true, ite_false, pinMarked] using hm
      simpa only [pinCopySource, hop, Bool.false_eq_true, ite_false] using cert.1 i hi ht
    | true =>
      cases hl : v reference (left i) with
      | false =>
        have hr : v reference (right i) = true := by simpa [pinMarked, hl] using hm
        simpa only [pinCopySource, hop, hl, ite_true, Bool.false_eq_true, ite_false]
          using cert.2.2 i hi hop hr
      | true =>
        simpa only [pinCopySource, hop, hl, ite_true] using cert.2.1 i hi hop hl
  refine ⟨fun i hi hm => (hboth i hi hm).1,
    fun s i hi hm => (hboth i hi hm).2 s, ?_⟩
  intro i _ hm
  cases hl : v reference (left i) <;> cases hr : v reference (right i) <;>
    simp_all [pinMarked]

lemma pin_one_operation_caps {σ : Type} (reference : σ) (n m x out : Nat)
    (op : Nat → Bool) (left right : Nat → Nat) (v : σ → Nat → Bool)
    (hx : x < n) (hpinned : ∀ s, v s x = true)
    (hout : out < n + m) (hzero : v reference out = false)
    (hcausal : ∀ i < m, left i < n + i ∧ right i < n + i)
    (heval : ∀ s i, i < m →
      v s (n + i) = gateBool (op i) (v s (left i)) (v s (right i)))
    (hraw : ∀ i, i < n → v reference i = true → i = x)
    (hfive : (List.range m).countP op = 5)
    (hnine : (List.range m).countP (fun i => !(op i)) = 9)
    (hlower : ∀ (m' : Nat) (op' : Nat → Bool) (left' right' : Nat → Nat)
        (out' : Nat) (v' : σ → Nat → Bool),
      out' < n + m' →
      (∀ i < m', left' i < n + i ∧ right' i < n + i) →
      (∀ s j, j < n → v' s j = v s j) →
      (∀ s i, i < m' →
        v' s (n + i) = gateBool (op' i) (v' s (left' i)) (v' s (right' i))) →
      (∀ s, v' s out' = v s out) →
      (∀ i < m', left' i ≠ x ∧ right' i ≠ x) → out' ≠ x →
      3 ≤ (List.range m').countP op' ∧
      6 ≤ (List.range m').countP (fun i => !(op' i))) :
    (List.range m).countP (fun i => op i && pinMarked (v reference) left right i) ≤ 2 ∧
    (List.range m).countP (fun i => !(op i) && v reference (n + i)) ≤ 3 := by
  let marked := pinMarked (v reference) left right
  obtain ⟨hs, hcopy, hclean⟩ :=
    pin_marked_copy_certificates reference n m x op left right v hx hpinned hcausal heval hraw
  obtain ⟨m', op', left', right', out', v', _, hout', hc', hr', he', ho', ha', hor', hcl'⟩ :=
    eliminate_marked_copies reference n m out op left right v marked
      (pinCopySource x op (v reference) left right) hout hcausal heval hs hcopy hclean
  have hrawtrue : v' reference x = true := (hr' reference x hx).trans (hpinned reference)
  have havoid : ∀ i < m', left' i ≠ x ∧ right' i ≠ x := by
    intro i hi
    have hc := hcl' i hi
    constructor
    · intro heq
      have hbad : (true : Bool) = false := hrawtrue.symm.trans (heq ▸ hc.1)
      cases hbad
    · intro heq
      have hbad : (true : Bool) = false := hrawtrue.symm.trans (heq ▸ hc.2)
      cases hbad
  have houtavoid : out' ≠ x := by
    intro heq
    have hz : v' reference out' = false := (ho' reference).trans hzero
    have hbad : (true : Bool) = false := hrawtrue.symm.trans (heq ▸ hz)
    cases hbad
  obtain ⟨hla, hlo⟩ := hlower m' op' left' right' out' v' hout' hc' hr' he' ho' havoid houtavoid
  rw [ha'] at hla
  rw [hor'] at hlo
  have hpa := countP_range_partition m op marked
  have hpo := countP_range_partition m (fun i => !(op i)) marked
  have hor_eq : (List.range m).countP (fun i => !(op i) && v reference (n + i)) =
      (List.range m).countP (fun i => !(op i) && marked i) := by
    apply List.countP_congr
    intro i hi
    rw [heval reference i (List.mem_range.mp hi)]
    cases hop : op i <;> simp [gateBool, marked, pinMarked]
  constructor
  · change (List.range m).countP (fun i => op i && marked i) ≤ 2
    omega
  · rw [hor_eq]
    omega

end CopyElimination

namespace ConsumerFrontier

def activeAND {k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool)
    (w : Nat → Bool) (j : Fin k) : Prop :=
  op j = true ∧ (w (a j) = true ∨ w (b j) = true)

lemma activeAND_of_output_true {n k : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (heval : ∀ j, w (n + j.val) = gateBool (op j) (w (a j)) (w (b j)))
    (h : Fin k) (hop : op h = true) (htrue : w (n + h.val) = true) :
    activeAND a b op w h := by
  have hinputs : w (a h) = true ∧ w (b h) = true := by
    simpa [gateBool, hop] using (heval h).symm.trans htrue
  exact ⟨hop, Or.inl hinputs.1⟩

lemma true_gate_has_false_active_frontier {n k out : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (heval : ∀ j, w (n + j.val) = gateBool (op j) (w (a j)) (w (b j)))
    (h : Fin k) (htrue : w (n + h.val) = true)
    (hpath : consumerReachable n a b (n + h.val) out) (hout : w out = false) :
    ∃ f : Fin k, activeAND a b op w f ∧ w (n + f.val) = false ∧ f ≠ h := by
  obtain ⟨length, path, hfirst, hlast, hstep⟩ := hpath
  obtain ⟨i, hi, hbefore, f, hfwire, hfop, hfalse, hfinput⟩ :=
    consumer_path_and_frontier a b op w heval path length hstep
      (by simpa only [hfirst] using htrue) (by simpa only [hlast] using hout)
  refine ⟨f, ⟨hfop, hfinput⟩, hfalse, ?_⟩
  intro heq
  subst f
  have hbad : (true : Bool) = false := htrue.symm.trans hfalse
  cases hbad

lemma unique_true_and_of_active_cap {n k out : Nat}
    (a b : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (heval : ∀ j, w (n + j.val) = gateBool (op j) (w (a j)) (w (b j)))
    (hcap : ∀ i j t : Fin k, activeAND a b op w i → activeAND a b op w j →
      activeAND a b op w t → i = j ∨ i = t ∨ j = t)
    (h : Fin k) (hop : op h = true) (htrue : w (n + h.val) = true)
    (hpath : consumerReachable n a b (n + h.val) out) (hout : w out = false) :
    ∃ f : Fin k, activeAND a b op w f ∧ w (n + f.val) = false ∧ f ≠ h ∧
      (∀ j, activeAND a b op w j → j = h ∨ j = f) ∧
      (∀ j, op j = true → w (n + j.val) = true → j = h) := by
  have hhactive := activeAND_of_output_true a b op w heval h hop htrue
  obtain ⟨f, hfactive, hfalse, hfne⟩ :=
    true_gate_has_false_active_frontier a b op w heval h htrue hpath hout
  have hclassification : ∀ j, activeAND a b op w j → j = h ∨ j = f := by
    intro j hj
    rcases hcap h f j hhactive hfactive hj with heq | heq | heq
    · exact False.elim (hfne heq.symm)
    · exact Or.inl heq.symm
    · exact Or.inr heq.symm
  refine ⟨f, hfactive, hfalse, hfne, hclassification, ?_⟩
  intro j hjop hjtrue
  rcases hclassification j (activeAND_of_output_true a b op w heval j hjop hjtrue) with hjh | hjf
  · exact hjh
  · subst j
    have hbad : (true : Bool) = false := hjtrue.symm.trans hfalse
    cases hbad

end ConsumerFrontier

namespace ConsumerFrontier

def consumes {k : Nat} (left right : Fin k → Nat) (j : Fin k) (wire : Nat) : Prop :=
  left j = wire ∨ right j = wire

lemma live_true_has_direct_frontier {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (h f : Fin k) (out : Nat)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hpath : consumerReachable n left right (n + h.val) out)
    (htrue : w (n + h.val) = true) (hout : w out = false)
    (hnoOR : ∀ j, op j = false → ¬consumes left right j (n + h.val))
    (hactive : ∀ j, op j = true →
      (w (left j) = true ∨ w (right j) = true) → j = h ∨ j = f) :
    consumes left right f (n + h.val) := by
  obtain ⟨length, path, hfirst, hlast, hstep⟩ := hpath
  have hlen : 0 < length := by
    by_contra hz
    have heq : length = 0 := by omega
    subst length
    have hbad : (true : Bool) = false := htrue.symm.trans (hfirst ▸ (hlast ▸ hout))
    cases hbad
  obtain ⟨j, _, hparent⟩ := hstep 0 hlen
  have hj : consumes left right j (n + h.val) := by
    rcases hparent with hl | hr
    · exact Or.inl (hl.symm.trans hfirst)
    · exact Or.inr (hr.symm.trans hfirst)
  have hop : op j = true := by
    cases heq : op j with
    | false => exact False.elim (hnoOR j heq hj)
    | true => rfl
  have hin : w (left j) = true ∨ w (right j) = true := by
    rcases hj with hl | hr
    · exact Or.inl (hl ▸ htrue)
    · exact Or.inr (hr ▸ htrue)
  rcases hactive j hop hin with heq | heq
  · subst j
    have hc := hcausal h
    rcases hj with hl | hr <;> omega
  · simpa only [heq] using hj

lemma false_gate_cannot_consume_two_true {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (f : Fin k) (u v : Nat) (hne : u ≠ v)
    (hu : w u = true) (hv : w v = true)
    (heval : w (n + f.val) = gateBool (op f) (w (left f)) (w (right f)))
    (hfalse : w (n + f.val) = false)
    (hreadu : consumes left right f u) :
    ¬consumes left right f v := by
  intro hreadv
  have hgate : gateBool (op f) (w (left f)) (w (right f)) = false :=
    heval.symm.trans hfalse
  rcases hreadu with hlu | hru <;> rcases hreadv with hlv | hrv
  · exact hne (hlu.symm.trans hlv)
  · rw [hlu, hrv, hu, hv] at hgate
    cases op f <;> simp [gateBool] at hgate
  · rw [hlv, hru, hv, hu] at hgate
    cases op f <;> simp [gateBool] at hgate
  · exact hne (hru.symm.trans hrv)

lemma true_input_private_to_true_gate {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (h f : Fin k) (wire : Nat) (hne : n + h.val ≠ wire)
    (hh : w (n + h.val) = true) (hwire : w wire = true)
    (heval : w (n + f.val) = gateBool (op f) (w (left f)) (w (right f)))
    (hfalse : w (n + f.val) = false)
    (hread : consumes left right f (n + h.val))
    (hnoOR : ∀ j, op j = false → ¬consumes left right j wire)
    (hactive : ∀ j, op j = true →
      (w (left j) = true ∨ w (right j) = true) → j = h ∨ j = f) :
    ∀ j, j ≠ h → ¬consumes left right j wire := by
  intro j hj hconsume
  have hop : op j = true := by
    cases heq : op j with
    | false => exact False.elim (hnoOR j heq hconsume)
    | true => rfl
  have hin : w (left j) = true ∨ w (right j) = true := by
    rcases hconsume with hl | hr
    · exact Or.inl (hl ▸ hwire)
    · exact Or.inr (hr ▸ hwire)
  rcases hactive j hop hin with heq | heq
  · exact hj heq
  · subst j
    exact false_gate_cannot_consume_two_true left right op w f
      (n + h.val) wire hne hh hwire heval hfalse hread hconsume

end ConsumerFrontier

namespace SingletonWire

def profileLe {Bit : Type} (profile : Nat → Bit → Bool) (a b : Nat) : Prop :=
  ∀ bit, profile a bit = true → profile b bit = true

def trueOr {k : Nat} (n : Nat) (op : Fin k → Bool) (w : Nat → Bool) (j : Fin k) : Prop :=
  op j = false ∧ w (n + j.val) = true

def trueAnd {k : Nat} (n : Nat) (op : Fin k → Bool) (w : Nat → Bool) (j : Fin k) : Prop :=
  op j = true ∧ w (n + j.val) = true

lemma reader_precedes_and_dominates {Bit : Type} {n k v : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (profile : Nat → Bit → Bool) (q : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j, j ≠ q → left j ≠ v ∧ right j ≠ v)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hp : ∀ j bit, profile (n + j.val) bit =
      gateBool (op j) (profile (left j) bit) (profile (right j) bit)) :
    ∀ j : Fin k, w (n + j.val) = true →
      q.val ≤ j.val ∧ profileLe profile (n + q.val) (n + j.val) := by
  have hmain : ∀ z, z < n + k → n ≤ z → w z = true →
      n + q.val ≤ z ∧ profileLe profile (n + q.val) z := by
    intro z
    induction z using Nat.strong_induction_on with
    | ind z ih =>
      intro hz hn htrue
      let j : Fin k := ⟨z - n, by omega⟩
      have heq : n + j.val = z := by dsimp [j]; omega
      by_cases hjq : j = q
      · have hzq : z = n + q.val := by rw [← heq, hjq]
        rw [hzq]
        exact ⟨Nat.le_refl _, fun _ h => h⟩
      · have hc := hcausal j
        have hs := hsole j hjq
        have hleft : w (left j) = true →
            n + q.val ≤ left j ∧ profileLe profile (n + q.val) (left j) := by
          intro hval
          have hnleft : n ≤ left j := by
            by_contra hbad
            exact hs.1 (hraw (left j) (by omega) hval)
          exact ih (left j) (by omega) (by omega) hnleft hval
        have hright : w (right j) = true →
            n + q.val ≤ right j ∧ profileLe profile (n + q.val) (right j) := by
          intro hval
          have hnright : n ≤ right j := by
            by_contra hbad
            exact hs.2 (hraw (right j) (by omega) hval)
          exact ih (right j) (by omega) (by omega) hnright hval
        have hgate : gateBool (op j) (w (left j)) (w (right j)) = true := by
          rw [← hw j, heq]
          exact htrue
        cases ho : op j with
        | false =>
          have hv : w (left j) = true ∨ w (right j) = true := by
            simpa [gateBool, ho] using hgate
          rcases hv with hl | hr
          · have hd := hleft hl
            refine ⟨by omega, ?_⟩
            intro bit hbit
            have hval := hd.2 bit hbit
            have hout : profile (n + j.val) bit = true := by
              simpa [gateBool, ho, hval] using hp j bit
            simpa only [heq] using hout
          · have hd := hright hr
            refine ⟨by omega, ?_⟩
            intro bit hbit
            have hval := hd.2 bit hbit
            have hout : profile (n + j.val) bit = true := by
              simpa [gateBool, ho, hval] using hp j bit
            simpa only [heq] using hout
        | true =>
          have hv : w (left j) = true ∧ w (right j) = true := by
            simpa [gateBool, ho] using hgate
          have hl := hleft hv.1
          have hr := hright hv.2
          refine ⟨by omega, ?_⟩
          intro bit hbit
          have hpl := hl.2 bit hbit
          have hpr := hr.2 bit hbit
          have hout : profile (n + j.val) bit = true := by
            simpa [gateBool, ho, hpl, hpr] using hp j bit
          simpa only [heq] using hout
  intro j hj
  have hm := hmain (n + j.val) (by omega) (by omega) hj
  exact ⟨by omega, hm.2⟩

lemma true_source_is_gate {n k v : Nat} (left right : Fin k → Nat)
    (w : Nat → Bool) (q i : Fin k) (source : Nat)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j, j ≠ q → left j ≠ v ∧ right j ≠ v)
    (hiq : i ≠ q) (hsource : source = left i ∨ source = right i)
    (htrue : w source = true) :
    ∃ j : Fin k, source = n + j.val ∧ j.val < i.val ∧ w (n + j.val) = true := by
  have hs : source < n + i.val := by
    rcases hsource with h | h
    · rw [h]; exact (hcausal i).1
    · rw [h]; exact (hcausal i).2
  have hn : n ≤ source := by
    by_contra hbad
    have hv := hraw source (by omega) htrue
    rcases hsource with h | h
    · exact (hsole i hiq).1 (h.symm.trans hv)
    · exact (hsole i hiq).2 (h.symm.trans hv)
  let j : Fin k := ⟨source - n, by omega⟩
  have heq : source = n + j.val := by dsimp [j]; omega
  exact ⟨j, heq, by dsimp [j]; omega, heq ▸ htrue⟩

lemma true_and_has_two_other_ors {Bit : Type} {n k v : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (profile : Nat → Bit → Bool) (q h : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j, j ≠ q → left j ≠ v ∧ right j ≠ v)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hq : op q = false) (hh : trueAnd n op w h)
    (hunique : ∀ j, trueAnd n op w j → j = h)
    (hfront : ∀ j : Fin k, w (n + j.val) = true →
      q.val ≤ j.val ∧ profileLe profile (n + q.val) (n + j.val))
    (hinc : ¬ profileLe profile (left h) (right h) ∧
      ¬ profileLe profile (right h) (left h)) :
    ∃ a b : Fin k, left h = n + a.val ∧ right h = n + b.val ∧
      a.val < h.val ∧ b.val < h.val ∧ trueOr n op w a ∧ trueOr n op w b ∧
      a ≠ b ∧ a ≠ q ∧ b ≠ q ∧ q.val < a.val ∧ q.val < b.val := by
  have hhq : h ≠ q := by
    intro heq
    have hop := hh.1
    rw [heq, hq] at hop
    cases hop
  have hins : w (left h) = true ∧ w (right h) = true := by
    have he := (hw h).symm.trans hh.2
    simpa [gateBool, hh.1] using he
  obtain ⟨a, hla, hah, hwa⟩ := true_source_is_gate left right w q h (left h)
    hcausal hraw hsole hhq (Or.inl rfl) hins.1
  obtain ⟨b, hrb, hbh, hwb⟩ := true_source_is_gate left right w q h (right h)
    hcausal hraw hsole hhq (Or.inr rfl) hins.2
  have hoa : op a = false := by
    cases ho : op a with
    | false => rfl
    | true =>
      have he := hunique a ⟨ho, hwa⟩
      have hv := congrArg Fin.val he
      omega
  have hob : op b = false := by
    cases ho : op b with
    | false => rfl
    | true =>
      have he := hunique b ⟨ho, hwb⟩
      have hv := congrArg Fin.val he
      omega
  have hab : a ≠ b := by
    intro heq
    apply hinc.1
    rw [hla, hrb, heq]
    exact fun _ hbit => hbit
  have haq : a ≠ q := by
    intro heq
    apply hinc.1
    rw [hla, hrb, heq]
    exact (hfront b hwb).2
  have hbq : b ≠ q := by
    intro heq
    apply hinc.2
    rw [hla, hrb, heq]
    exact (hfront a hwa).2
  have hqa : q.val < a.val := by
    have hle := (hfront a hwa).1
    have hne : a.val ≠ q.val := fun h => haq (Fin.ext h)
    omega
  have hqb : q.val < b.val := by
    have hle := (hfront b hwb).1
    have hne : b.val ≠ q.val := fun h => hbq (Fin.ext h)
    omega
  exact ⟨a, b, hla, hrb, hah, hbh, ⟨hoa, hwa⟩, ⟨hob, hwb⟩,
    hab, haq, hbq, hqa, hqb⟩


lemma three_true_ors_exhaust {n k : Nat} (op : Fin k → Bool) (w : Nat → Bool)
    (q a b : Fin k) (hq : trueOr n op w q) (ha : trueOr n op w a)
    (hb : trueOr n op w b) (hqa : q ≠ a) (hqb : q ≠ b) (hab : a ≠ b)
    (hcap : ∀ i j l t : Fin k, trueOr n op w i → trueOr n op w j →
      trueOr n op w l → trueOr n op w t → i ≠ j → i ≠ l → j ≠ l →
      t ≠ i → t ≠ j → t ≠ l → False) :
    ∀ t, trueOr n op w t → t = q ∨ t = a ∨ t = b := by
  intro t ht
  by_cases htq : t = q
  · exact Or.inl htq
  by_cases hta : t = a
  · exact Or.inr (Or.inl hta)
  by_cases htb : t = b
  · exact Or.inr (Or.inr htb)
  exact False.elim (hcap q a b t hq ha hb ht hqa hqb hab htq hta htb)

lemma or_consumer_true_and_profile {Bit : Type} {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (profile : Nat → Bit → Bool) (i : Fin k) (source : Nat)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hp : ∀ j bit, profile (n + j.val) bit =
      gateBool (op j) (profile (left j) bit) (profile (right j) bit))
    (hoi : op i = false) (hsource : source = left i ∨ source = right i)
    (htrue : w source = true) :
    trueOr n op w i ∧ profileLe profile source (n + i.val) := by
  rcases hsource with hs | hs
  · have hv : w (left i) = true := hs ▸ htrue
    refine ⟨⟨hoi, by simpa [gateBool, hoi, hv] using hw i⟩, ?_⟩
    intro bit hbit
    have hb : profile (left i) bit = true := hs ▸ hbit
    simpa [gateBool, hoi, hb] using hp i bit
  · have hv : w (right i) = true := hs ▸ htrue
    refine ⟨⟨hoi, by simpa [gateBool, hoi, hv] using hw i⟩, ?_⟩
    intro bit hbit
    have hb : profile (right i) bit = true := hs ▸ hbit
    simpa [gateBool, hoi, hb] using hp i bit

lemma no_or_consumer_of_incomparable_triple {Bit : Type} {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (profile : Nat → Bit → Bool) (q a b : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hp : ∀ j bit, profile (n + j.val) bit =
      gateBool (op j) (profile (left j) bit) (profile (right j) bit))
    (hwa : w (n + a.val) = true) (hqa : q.val < a.val)
    (hexhaust : ∀ j, trueOr n op w j → j = q ∨ j = a ∨ j = b)
    (hinc : ¬ profileLe profile (n + a.val) (n + b.val)) :
    ∀ i, op i = false → left i ≠ n + a.val ∧ right i ≠ n + a.val := by
  intro i hoi
  have hnot : ¬ (n + a.val = left i ∨ n + a.val = right i) := by
    intro hs
    have hi := or_consumer_true_and_profile left right op w profile i (n + a.val)
      hw hp hoi hs hwa
    have hai : a.val < i.val := by
      rcases hs with hl | hr
      · have hc := (hcausal i).1; omega
      · have hc := (hcausal i).2; omega
    rcases hexhaust i hi.1 with heq | heq | heq
    · have hv := congrArg Fin.val heq; omega
    · have hv := congrArg Fin.val heq; omega
    · apply hinc
      simpa only [heq] using hi.2
  exact ⟨fun he => hnot (Or.inl he.symm), fun he => hnot (Or.inr he.symm)⟩

lemma true_or_reads_common_reader {n k v : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (q a b h i : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j, j ≠ q → left j ≠ v ∧ right j ≠ v)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hunique : ∀ j, trueAnd n op w j → j = h)
    (hexhaust : ∀ j, trueOr n op w j → j = q ∨ j = a ∨ j = b)
    (hnoa : ∀ j, op j = false → left j ≠ n + a.val ∧ right j ≠ n + a.val)
    (hnob : ∀ j, op j = false → left j ≠ n + b.val ∧ right j ≠ n + b.val)
    (hi : trueOr n op w i) (hiq : i ≠ q) (hih : i.val < h.val) :
    left i = n + q.val ∨ right i = n + q.val := by
  have hport : w (left i) = true ∨ w (right i) = true := by
    have he := (hw i).symm.trans hi.2
    simpa [gateBool, hi.1] using he
  have hsource : ∀ source, (source = left i ∨ source = right i) →
      w source = true → source = n + q.val := by
    intro source hs ht
    obtain ⟨j, heq, hji, hjw⟩ := true_source_is_gate left right w q i source
      hcausal hraw hsole hiq hs ht
    have hoj : op j = false := by
      cases ho : op j with
      | false => rfl
      | true =>
        have hje := hunique j ⟨ho, hjw⟩
        have hv := congrArg Fin.val hje
        omega
    rcases hexhaust j ⟨hoj, hjw⟩ with hjq | hja | hjb
    · simpa only [hjq] using heq
    · have he : source = n + a.val := by simpa only [hja] using heq
      rcases hs with hl | hr
      · exact False.elim ((hnoa i hi.1).1 (hl.symm.trans he))
      · exact False.elim ((hnoa i hi.1).2 (hr.symm.trans he))
    · have he : source = n + b.val := by simpa only [hjb] using heq
      rcases hs with hl | hr
      · exact False.elim ((hnob i hi.1).1 (hl.symm.trans he))
      · exact False.elim ((hnob i hi.1).2 (hr.symm.trans he))
  rcases hport with hl | hr
  · exact Or.inl (hsource (left i) (Or.inl rfl) hl)
  · exact Or.inr (hsource (right i) (Or.inr rfl) hr)

lemma no_or_consumer_after_true_ors {n k : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool) (h : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (htrue : w (n + h.val) = true)
    (hbefore : ∀ j, trueOr n op w j → j.val < h.val) :
    ∀ i, op i = false → left i ≠ n + h.val ∧ right i ≠ n + h.val := by
  intro i hoi
  have hnot : ¬ (left i = n + h.val ∨ right i = n + h.val) := by
    intro hs
    have hwi : w (n + i.val) = true := by
      rcases hs with hl | hr
      · simpa [gateBool, hoi, hl, htrue] using hw i
      · simpa [gateBool, hoi, hr, htrue] using hw i
    have hib := hbefore i ⟨hoi, hwi⟩
    rcases hs with hl | hr
    · have hc := (hcausal i).1; omega
    · have hc := (hcausal i).2; omega
  exact ⟨fun he => hnot (Or.inl he), fun he => hnot (Or.inr he)⟩

end SingletonWire


namespace SingletonWire

lemma singleton_true_and_forces_private_diamond {Bit : Type} {n k v out : Nat}
    (left right : Fin k → Nat) (op : Fin k → Bool) (w : Nat → Bool)
    (profile : Nat → Bit → Bool) (q h : Fin k)
    (hcausal : ∀ j, left j < n + j.val ∧ right j < n + j.val)
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j, j ≠ q → left j ≠ v ∧ right j ≠ v)
    (hw : ∀ j : Fin k, w (n + j.val) = gateBool (op j) (w (left j)) (w (right j)))
    (hp : ∀ j bit, profile (n + j.val) bit =
      gateBool (op j) (profile (left j) bit) (profile (right j) bit))
    (hq : trueOr n op w q) (hh : trueAnd n op w h)
    (hinc : ¬ profileLe profile (left h) (right h) ∧
      ¬ profileLe profile (right h) (left h))
    (hORcap : ∀ i j l t : Fin k, trueOr n op w i → trueOr n op w j →
      trueOr n op w l → trueOr n op w t → i ≠ j → i ≠ l → j ≠ l →
      t ≠ i → t ≠ j → t ≠ l → False)
    (hANDcap : ∀ i j t : Fin k, ConsumerFrontier.activeAND left right op w i →
      ConsumerFrontier.activeAND left right op w j →
      ConsumerFrontier.activeAND left right op w t → i = j ∨ i = t ∨ j = t)
    (hpath : ConsumerFrontier.consumerReachable n left right (n + h.val) out)
    (hout : w out = false) :
    ∃ a b : Fin k, left h = n + a.val ∧ right h = n + b.val ∧
      q.val < a.val ∧ q.val < b.val ∧ a.val < h.val ∧ b.val < h.val ∧
      a ≠ b ∧ trueOr n op w a ∧ trueOr n op w b ∧
      (left a = n + q.val ∨ right a = n + q.val) ∧
      (left b = n + q.val ∨ right b = n + q.val) ∧
      (∀ i, i ≠ h → left i ≠ n + a.val ∧ right i ≠ n + a.val ∧
        left i ≠ n + b.val ∧ right i ≠ n + b.val) ∧
      out ≠ n + a.val ∧ out ≠ n + b.val := by
  obtain ⟨f, _, hffalse, _, hactive, huniq⟩ :=
    ConsumerFrontier.unique_true_and_of_active_cap left right op w hw hANDcap
      h hh.1 hh.2 hpath hout
  have hunique : ∀ j, trueAnd n op w j → j = h := by
    intro j hj
    exact huniq j hj.1 hj.2
  have hfront := reader_precedes_and_dominates left right op w profile q
    hcausal hraw hsole hw hp
  obtain ⟨a, b, hla, hrb, hah, hbh, ha, hb, hab, haq, hbq, hqa, hqb⟩ :=
    true_and_has_two_other_ors left right op w profile q h hcausal hraw hsole
      hw hq.1 hh hunique hfront hinc
  have hexhaust := three_true_ors_exhaust op w q a b hq ha hb
    (Ne.symm haq) (Ne.symm hbq) hab hORcap
  have hexhaust' : ∀ j, trueOr n op w j → j = q ∨ j = b ∨ j = a := by
    intro j hj
    rcases hexhaust j hj with hq | ha | hb
    · exact Or.inl hq
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inl hb)
  have hincab : ¬ profileLe profile (n + a.val) (n + b.val) := by
    simpa only [hla, hrb] using hinc.1
  have hincba : ¬ profileLe profile (n + b.val) (n + a.val) := by
    simpa only [hla, hrb] using hinc.2
  have hnoa := no_or_consumer_of_incomparable_triple left right op w profile q a b
    hcausal hw hp ha.2 hqa hexhaust hincab
  have hnob := no_or_consumer_of_incomparable_triple left right op w profile q b a
    hcausal hw hp hb.2 hqb hexhaust' hincba
  have haqread := true_or_reads_common_reader left right op w q a b h a
    hcausal hraw hsole hw hunique hexhaust hnoa hnob ha haq hah
  have hbqread := true_or_reads_common_reader left right op w q a b h b
    hcausal hraw hsole hw hunique hexhaust hnoa hnob hb hbq hbh
  have hbefore : ∀ j, trueOr n op w j → j.val < h.val := by
    intro j hj
    rcases hexhaust j hj with hjq | hja | hjb
    · have hv := congrArg Fin.val hjq; omega
    · simpa only [hja] using hah
    · simpa only [hjb] using hbh
  have hnoh := no_or_consumer_after_true_ors left right op w h hcausal hw hh.2 hbefore
  have hactive' : ∀ j, op j = true →
      (w (left j) = true ∨ w (right j) = true) → j = h ∨ j = f := by
    intro j hop hin
    exact hactive j ⟨hop, hin⟩
  have hread := ConsumerFrontier.live_true_has_direct_frontier left right op w h f out
    hcausal hpath hh.2 hout (by
      intro j hoj hc
      rcases hc with hl | hr
      · exact (hnoh j hoj).1 hl
      · exact (hnoh j hoj).2 hr) hactive'
  have hprivatea := ConsumerFrontier.true_input_private_to_true_gate left right op w h f
    (n + a.val) (by omega) hh.2 ha.2 (hw f) hffalse hread (by
      intro j hoj hc
      rcases hc with hl | hr
      · exact (hnoa j hoj).1 hl
      · exact (hnoa j hoj).2 hr) hactive'
  have hprivateb := ConsumerFrontier.true_input_private_to_true_gate left right op w h f
    (n + b.val) (by omega) hh.2 hb.2 (hw f) hffalse hread (by
      intro j hoj hc
      rcases hc with hl | hr
      · exact (hnob j hoj).1 hl
      · exact (hnob j hoj).2 hr) hactive'
  refine ⟨a, b, hla, hrb, hqa, hqb, hah, hbh, hab, ha, hb, haqread, hbqread, ?_, ?_, ?_⟩
  · intro i hih
    exact ⟨fun he => hprivatea i hih (Or.inl he),
      fun he => hprivatea i hih (Or.inr he),
      fun he => hprivateb i hih (Or.inl he),
      fun he => hprivateb i hih (Or.inr he)⟩
  · intro he
    have hbad : (true : Bool) = false := ha.2.symm.trans (he ▸ hout)
    cases hbad
  · intro he
    have hbad : (true : Bool) = false := hb.2.symm.trans (he ▸ hout)
    cases hbad

end SingletonWire

namespace Diamond

def orientLeft (wanted left right : Nat → Nat) (i : Nat) : Nat :=
  if left i = wanted i then left i else right i

def orientRight (wanted left right : Nat → Nat) (i : Nat) : Nat :=
  if left i = wanted i then right i else left i

lemma orient_causal (n k : Nat) (wanted left right : Nat → Nat)
    (hc : ∀ i < k, left i < n + i ∧ right i < n + i) :
    ∀ i < k, orientLeft wanted left right i < n + i ∧
      orientRight wanted left right i < n + i := by
  intro i hi
  by_cases he : left i = wanted i
  · simpa [orientLeft, orientRight, he] using hc i hi
  · simpa [orientLeft, orientRight, he, and_comm] using hc i hi

lemma orient_preserves_sources (k : Nat) (wanted left right : Nat → Nat)
    (P : Nat → Prop) (hp : ∀ i < k, P (left i) ∧ P (right i)) :
    ∀ i < k, P (orientLeft wanted left right i) ∧ P (orientRight wanted left right i) := by
  intro i hi
  by_cases he : left i = wanted i
  · simpa [orientLeft, orientRight, he] using hp i hi
  · simpa [orientLeft, orientRight, he, and_comm] using hp i hi

lemma orient_eval (n k : Nat) (wanted left right : Nat → Nat)
    (op : Nat → Bool) (x : Nat → Nat)
    (hx : ∀ i < k, x (n + i) = gateNat (op i) (x (left i)) (x (right i))) :
    ∀ i < k, x (n + i) = gateNat (op i)
      (x (orientLeft wanted left right i)) (x (orientRight wanted left right i)) := by
  intro i hi
  by_cases he : left i = wanted i
  · simpa [orientLeft, orientRight, he] using hx i hi
  · have hcomm : gateNat (op i) (x (left i)) (x (right i)) =
        gateNat (op i) (x (right i)) (x (left i)) := by
      cases op i <;> simp [gateNat, Nat.and_comm, Nat.or_comm]
    simpa [orientLeft, orientRight, he] using (hx i hi).trans hcomm

lemma orient_private (n k a b h : Nat) (wanted left right : Nat → Nat)
    (hp : ∀ i < k, i ≠ h →
      (left i ≠ n + a ∧ left i ≠ n + b) ∧
      (right i ≠ n + a ∧ right i ≠ n + b)) :
    ∀ i < k, i ≠ h →
      (orientLeft wanted left right i ≠ n + a ∧ orientLeft wanted left right i ≠ n + b) ∧
      (orientRight wanted left right i ≠ n + a ∧ orientRight wanted left right i ≠ n + b) := by
  intro i hi hih
  by_cases he : left i = wanted i
  · simpa [orientLeft, orientRight, he] using hp i hi hih
  · simpa [orientLeft, orientRight, he, and_comm] using hp i hi hih

lemma no_private_unordered_diamond_of_or_lower_bound
    (n k a b h q out bound : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) (allowed : Nat → Prop)
    (hab : a < b) (hbh : b < h) (hh : h < k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (ha : op a = false ∧ (left a = q ∨ right a = q))
    (hb : op b = false ∧ (left b = q ∨ right b = q))
    (hd : op h = true ∧
      ((left h = n + a ∧ right h = n + b) ∨ (left h = n + b ∧ right h = n + a)))
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
  let wanted : Nat → Nat := fun i => if i = h then n + a else q
  let l := orientLeft wanted left right
  let r := orientRight wanted left right
  have hah : a ≠ h := by omega
  have hbhne : b ≠ h := by omega
  have hla : l a = q := by
    change (if left a = wanted a then left a else right a) = q
    have hw : wanted a = q := by simp [wanted, hah]
    rw [hw]
    rcases ha.2 with hl | hr
    · simp [hl]
    · by_cases hl : left a = q <;> simp [hl, hr]
  have hlb : l b = q := by
    change (if left b = wanted b then left b else right b) = q
    have hw : wanted b = q := by simp [wanted, hbhne]
    rw [hw]
    rcases hb.2 with hl | hr
    · simp [hl]
    · by_cases hl : left b = q <;> simp [hl, hr]
  have hlh : l h = n + a ∧ r h = n + b := by
    change (if left h = wanted h then left h else right h) = n + a ∧
      (if left h = wanted h then right h else left h) = n + b
    have hw : wanted h = n + a := by simp [wanted]
    rw [hw]
    rcases hd.2 with hports | hports
    · simp [hports.1, hports.2]
    · have hne : b ≠ a := by omega
      simp [hports.1, hports.2, hne]
  exact no_private_diamond_of_or_lower_bound n k a b h q (r a) (r b) out bound
    op l r x allowed hab hbh hh (orient_causal n k wanted left right hcausal)
    ⟨ha.1, hla, rfl⟩ ⟨hb.1, hlb, rfl⟩ ⟨hd.1, hlh⟩
    (orient_private n k a b h wanted left right hprivate)
    (orient_eval n k wanted left right op x hx)
    (orient_preserves_sources k wanted left right (fun j => j < n → allowed j) hallowed)
    hout houtA houtB hcount hlower

end Diamond

namespace CountCaps

lemma witnesses_le_count (m : Nat) (p : Nat → Bool) (witnesses : List Nat)
    (hnd : witnesses.Nodup) (hb : ∀ i ∈ witnesses, i < m)
    (hp : ∀ i ∈ witnesses, p i = true) :
    witnesses.length ≤ (List.range m).countP p := by
  rw [List.countP_eq_length_filter]
  apply hnd.length_le_of_subset
  intro i hi
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (hb i hi), hp i hi⟩

lemma three_of_count_le_two {m : Nat} (p : Nat → Bool)
    (hcount : (List.range m).countP p ≤ 2)
    (i j t : Fin m) (hi : p i.val = true) (hj : p j.val = true) (ht : p t.val = true) :
    i = j ∨ i = t ∨ j = t := by
  by_cases hij : i = j
  · exact Or.inl hij
  by_cases hit : i = t
  · exact Or.inr (Or.inl hit)
  by_cases hjt : j = t
  · exact Or.inr (Or.inr hjt)
  have hijv : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hitv : i.val ≠ t.val := fun he => hit (Fin.ext he)
  have hjtv : j.val ≠ t.val := fun he => hjt (Fin.ext he)
  have hw := witnesses_le_count m p [i.val, j.val, t.val]
    (by simp [hijv, hitv, hjtv]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> subst x
      · exact i.isLt
      · exact j.isLt
      · exact t.isLt) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h <;> subst x
      · exact hi
      · exact hj
      · exact ht)
  simp only [List.length_cons, List.length_nil] at hw
  omega

lemma four_impossible_of_count_le_three {m : Nat} (p : Nat → Bool)
    (hcount : (List.range m).countP p ≤ 3)
    (i j l t : Fin m) (hi : p i.val = true) (hj : p j.val = true)
    (hl : p l.val = true) (ht : p t.val = true)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hti : t ≠ i) (htj : t ≠ j) (htl : t ≠ l) : False := by
  have hijv : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hilv : i.val ≠ l.val := fun he => hil (Fin.ext he)
  have hjlv : j.val ≠ l.val := fun he => hjl (Fin.ext he)
  have hitv : i.val ≠ t.val := fun he => hti (Fin.ext he.symm)
  have hjtv : j.val ≠ t.val := fun he => htj (Fin.ext he.symm)
  have hltv : l.val ≠ t.val := fun he => htl (Fin.ext he.symm)
  have hw := witnesses_le_count m p [i.val, j.val, l.val, t.val]
    (by simp [hijv, hilv, hjlv, hitv, hjtv, hltv]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> subst x
      · exact i.isLt
      · exact j.isLt
      · exact l.isLt
      · exact t.isLt) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> subst x
      · exact hi
      · exact hj
      · exact hl
      · exact ht)
  simp only [List.length_cons, List.length_nil] at hw
  omega

end CountCaps

namespace SingletonWire

lemma no_singleton_true_and_of_caps_and_or_lower_bound
    {Bit : Type} (n k v out bound : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) (allowed : Nat → Prop)
    (w : Nat → Bool) (profile : Nat → Bit → Bool) (q h : Fin k)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (hx : ∀ i < k, x (n + i) = Diamond.gateNat (op i) (x (left i)) (x (right i)))
    (hallowed : ∀ i < k,
      (left i < n → allowed (left i)) ∧ (right i < n → allowed (right i)))
    (hraw : ∀ j < n, w j = true → j = v)
    (hsole : ∀ j : Fin k, j ≠ q → left j.val ≠ v ∧ right j.val ≠ v)
    (hw : ∀ j : Fin k, w (n + j.val) =
      gateBool (op j.val) (w (left j.val)) (w (right j.val)))
    (hp : ∀ (j : Fin k) bit, profile (n + j.val) bit =
      gateBool (op j.val) (profile (left j.val) bit) (profile (right j.val) bit))
    (hq : trueOr n (fun j : Fin k => op j.val) w q)
    (hh : trueAnd n (fun j : Fin k => op j.val) w h)
    (hinc : ¬ profileLe profile (left h.val) (right h.val) ∧
      ¬ profileLe profile (right h.val) (left h.val))
    (hORcount : (List.range k).countP (fun i => !(op i) && w (n + i)) ≤ 3)
    (hANDcount : (List.range k).countP
      (fun i => op i && (w (left i) || w (right i))) ≤ 2)
    (hpath : ConsumerFrontier.consumerReachable n (fun j : Fin k => left j.val)
      (fun j : Fin k => right j.val) (n + h.val) out)
    (houtfalse : w out = false) (hout : out < n + k)
    (hcount : Diamond.orCount op k ≤ bound)
    (hlower : ∀ (op' : Nat → Bool) (left' right' : Nat → Nat) (y : Nat → Nat),
      (∀ i < k, left' i < n + i ∧ right' i < n + i) →
      (∀ i < k,
        (left' i < n → allowed (left' i)) ∧ (right' i < n → allowed (right' i))) →
      (∀ j < n, y j = x j) →
      (∀ i < k, y (n + i) = Diamond.gateNat (op' i) (y (left' i)) (y (right' i))) →
      y out = x out → bound ≤ Diamond.orCount op' k) : False := by
  have hORcap : ∀ i j l t : Fin k, trueOr n (fun j : Fin k => op j.val) w i →
      trueOr n (fun j : Fin k => op j.val) w j →
      trueOr n (fun j : Fin k => op j.val) w l →
      trueOr n (fun j : Fin k => op j.val) w t →
      i ≠ j → i ≠ l → j ≠ l → t ≠ i → t ≠ j → t ≠ l → False := by
    intro i j l t hi hj hl ht hij hil hjl hti htj htl
    exact CountCaps.four_impossible_of_count_le_three
      (fun z => !(op z) && w (n + z)) hORcount i j l t
      (by simp [hi.1, hi.2]) (by simp [hj.1, hj.2])
      (by simp [hl.1, hl.2]) (by simp [ht.1, ht.2])
      hij hil hjl hti htj htl
  have hANDcap : ∀ i j t : Fin k,
      ConsumerFrontier.activeAND (fun j : Fin k => left j.val)
        (fun j : Fin k => right j.val) (fun j : Fin k => op j.val) w i →
      ConsumerFrontier.activeAND (fun j : Fin k => left j.val)
        (fun j : Fin k => right j.val) (fun j : Fin k => op j.val) w j →
      ConsumerFrontier.activeAND (fun j : Fin k => left j.val)
        (fun j : Fin k => right j.val) (fun j : Fin k => op j.val) w t →
      i = j ∨ i = t ∨ j = t := by
    intro i j t hi hj ht
    exact CountCaps.three_of_count_le_two
      (fun z => op z && (w (left z) || w (right z))) hANDcount i j t
      (by simpa only [hi.1, Bool.true_and, Bool.or_eq_true] using hi.2)
      (by simpa only [hj.1, Bool.true_and, Bool.or_eq_true] using hj.2)
      (by simpa only [ht.1, Bool.true_and, Bool.or_eq_true] using ht.2)
  obtain ⟨a, b, hla, hrb, _, _, hah, hbh, hab, ha, hb, haq, hbq, hpriv, hoxa, hoxb⟩ :=
    singleton_true_and_forces_private_diamond
      (fun j : Fin k => left j.val) (fun j : Fin k => right j.val)
      (fun j : Fin k => op j.val) w profile q h (fun j => hcausal j.val j.isLt)
      hraw hsole hw hp hq hh hinc hORcap hANDcap hpath houtfalse
  have hprivate : ∀ i < k, i ≠ h.val →
      (left i ≠ n + a.val ∧ left i ≠ n + b.val) ∧
      (right i ≠ n + a.val ∧ right i ≠ n + b.val) := by
    intro i hi hih
    have hp := hpriv ⟨i, hi⟩ (fun he => hih (congrArg Fin.val he))
    exact ⟨⟨hp.1, hp.2.2.1⟩, ⟨hp.2.1, hp.2.2.2⟩⟩
  by_cases hablt : a.val < b.val
  · exact Diamond.no_private_unordered_diamond_of_or_lower_bound
      n k a.val b.val h.val (n + q.val) out bound op left right x allowed
      hablt hbh h.isLt hcausal ⟨ha.1, haq⟩ ⟨hb.1, hbq⟩
      ⟨hh.1, Or.inl ⟨hla, hrb⟩⟩ hprivate hx hallowed hout hoxa hoxb hcount hlower
  · have habne : a.val ≠ b.val := fun he => hab (Fin.ext he)
    have hbalt : b.val < a.val := by omega
    have hprivate' : ∀ i < k, i ≠ h.val →
        (left i ≠ n + b.val ∧ left i ≠ n + a.val) ∧
        (right i ≠ n + b.val ∧ right i ≠ n + a.val) := by
      intro i hi hih
      have hp := hprivate i hi hih
      exact ⟨⟨hp.1.2, hp.1.1⟩, ⟨hp.2.2, hp.2.1⟩⟩
    exact Diamond.no_private_unordered_diamond_of_or_lower_bound
      n k b.val a.val h.val (n + q.val) out bound op left right x allowed
      hbalt hah h.isLt hcausal ⟨hb.1, hbq⟩ ⟨ha.1, haq⟩
      ⟨hh.1, Or.inr ⟨hla, hrb⟩⟩ hprivate' hx hallowed hout hoxb hoxa hcount hlower

end SingletonWire

namespace SingletonWire

lemma no_singleton_true_and_from_five_nine_and_cofactor_bounds
    {σ Bit : Type} (reference : σ) (n k v out : Nat) (op : Nat → Bool)
    (left right : Nat → Nat) (x : Nat → Nat) (allowed : Nat → Prop)
    (V : σ → Nat → Bool) (profile : Nat → Bit → Bool) (q h : Fin k)
    (hv : v < n) (hpinned : ∀ s, V s v = true)
    (hcausal : ∀ i < k, left i < n + i ∧ right i < n + i)
    (hx : ∀ i < k, x (n + i) = Diamond.gateNat (op i) (x (left i)) (x (right i)))
    (hallowed : ∀ i < k,
      (left i < n → allowed (left i)) ∧ (right i < n → allowed (right i)))
    (hV : ∀ s i, i < k → V s (n + i) = gateBool (op i) (V s (left i)) (V s (right i)))
    (hraw : ∀ j < n, V reference j = true → j = v)
    (hsole : ∀ j : Fin k, j ≠ q → left j.val ≠ v ∧ right j.val ≠ v)
    (hp : ∀ (j : Fin k) bit, profile (n + j.val) bit =
      gateBool (op j.val) (profile (left j.val) bit) (profile (right j.val) bit))
    (hq : trueOr n (fun j : Fin k => op j.val) (V reference) q)
    (hh : trueAnd n (fun j : Fin k => op j.val) (V reference) h)
    (hinc : ¬ profileLe profile (left h.val) (right h.val) ∧
      ¬ profileLe profile (right h.val) (left h.val))
    (houtfalse : V reference out = false) (hout : out < n + k)
    (hfive : (List.range k).countP op = 5)
    (hnine : (List.range k).countP (fun i => !(op i)) = 9)
    (hminimal : ConsumerFrontier.fixedParentsOperationMinimal n k out op left right x)
    (hcofactor : ∀ (m' : Nat) (op' : Nat → Bool) (left' right' : Nat → Nat)
        (out' : Nat) (V' : σ → Nat → Bool),
      out' < n + m' →
      (∀ i < m', left' i < n + i ∧ right' i < n + i) →
      (∀ s j, j < n → V' s j = V s j) →
      (∀ s i, i < m' →
        V' s (n + i) = gateBool (op' i) (V' s (left' i)) (V' s (right' i))) →
      (∀ s, V' s out' = V s out) →
      (∀ i < m', left' i ≠ v ∧ right' i ≠ v) → out' ≠ v →
      3 ≤ (List.range m').countP op' ∧
      6 ≤ (List.range m').countP (fun i => !(op' i)))
    (hlower : ∀ (op' : Nat → Bool) (left' right' : Nat → Nat) (y : Nat → Nat),
      (∀ i < k, left' i < n + i ∧ right' i < n + i) →
      (∀ i < k,
        (left' i < n → allowed (left' i)) ∧ (right' i < n → allowed (right' i))) →
      (∀ j < n, y j = x j) →
      (∀ i < k, y (n + i) = Diamond.gateNat (op' i) (y (left' i)) (y (right' i))) →
      y out = x out → 9 ≤ Diamond.orCount op' k) : False := by
  have hcaps := CopyElimination.pin_one_operation_caps reference n k v out op left right V
    hv hpinned hout houtfalse hcausal hV hraw hfive hnine hcofactor
  have hpath := ConsumerFrontier.operation_minimal_gate_reachable n k out op left right x
    hcausal hx hout hminimal h
  exact no_singleton_true_and_of_caps_and_or_lower_bound n k v out 9 op left right x allowed
    (V reference) profile q h hcausal hx hallowed hraw hsole
    (fun j => hV reference j.val j.isLt) hp hq hh hinc hcaps.2
    (by simpa only [CopyElimination.pinMarked] using hcaps.1) hpath houtfalse hout
    (by change (List.range k).countP (fun i => !(op i)) ≤ 9; omega) hlower

end SingletonWire

end PEqualNP.Outside.L_meta_9033_aux
