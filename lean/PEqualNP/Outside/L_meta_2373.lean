import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux.FirstWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateValue {n : ℕ} (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)

def singleInput {n : ℕ} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : ℕ} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

lemma read_eq {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n <;>
    simp [List.getD_eq_getElem?_getD, h]

lemma read_zero {n : ℕ} (i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  rw [read_eq]
  split <;> rfl

lemma read_lt {n : ℕ} {x : Fin n → Bool} {i : ℕ}
    (h : (List.ofFn x).getD i false = true) : i < n := by
  by_cases hlt : i < n
  · exact hlt
  · simp [hlt] at h

lemma read_singleInput {n : ℕ} (i : Fin n) :
    (List.ofFn (singleInput i)).getD i.val false = true := by
  simp [singleInput, i.isLt]

lemma read_pairInput_left {n : ℕ} (i j : Fin n) :
    (List.ofFn (pairInput i j)).getD i.val false = true := by
  simp [pairInput, i.isLt]

lemma read_pairInput_right {n : ℕ} (i j : Fin n) :
    (List.ofFn (pairInput i j)).getD j.val false = true := by
  simp [pairInput, j.isLt]

lemma first_gate_classification {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hzero : f (fun _ => false) = false)
    (hsingle : ∀ i, f (singleInput i) = false)
    (g : Gate)
    (hfan : FanInTwo { gates := [g], output := 0 })
    (htrue : ∃ x : Fin n → Bool, gateValue g x = true)
    (hsound : ∀ x, f x = false → gateValue g x = false) :
    ∃ i j : Fin n, i ≠ j ∧ f (pairInput i j) = true ∧
      g.op = GateOp.and ∧ g.inputs = [i.val, j.val] := by
  have hz := hsound (fun _ => false) hzero
  have hs : ∀ i, gateValue g (singleInput i) = false :=
    fun i => hsound (singleInput i) (hsingle i)
  rcases g with ⟨op, inputs⟩
  have hg := hfan ⟨op, inputs⟩ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  change (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) ∧ inputs.length ≤ 2 at hg
  rcases hg with ⟨hop, hlen⟩
  rcases htrue with ⟨x, hx⟩
  rcases inputs with _ | ⟨a, tail⟩
  · rcases hop with hop | hop | hop <;> subst op <;>
      simp [gateValue, GateOp.eval] at hz hx
  rcases tail with _ | ⟨b, tail⟩
  · rcases hop with hop | hop | hop <;> subst op
    · have ha : a < n := read_lt (by simpa [gateValue, GateOp.eval] using hx)
      have hh := hs ⟨a, ha⟩
      simp [gateValue, GateOp.eval, singleInput, ha] at hh
    · have ha : a < n := read_lt (by simpa [gateValue, GateOp.eval] using hx)
      have hh := hs ⟨a, ha⟩
      simp [gateValue, GateOp.eval, singleInput, ha] at hh
    · change (!(List.ofFn (fun _ : Fin n => false)).getD a false) = false at hz
      rw [read_zero] at hz
      cases hz
  rcases tail with _ | ⟨c, tail⟩
  · rcases hop with hop | hop | hop <;> subst op
    · have hx' : (List.ofFn x).getD a false = true ∧
          (List.ofFn x).getD b false = true := by
        simpa [gateValue, GateOp.eval] using hx
      have ha : a < n := read_lt hx'.1
      have hb : b < n := read_lt hx'.2
      have hab : a ≠ b := by
        intro hab
        subst b
        have hh := hs ⟨a, ha⟩
        simp [gateValue, GateOp.eval, singleInput, ha] at hh
      have hpairInput : gateValue { op := GateOp.and, inputs := [a, b] }
          (pairInput ⟨a, ha⟩ ⟨b, hb⟩) = true := by
        simp [gateValue, GateOp.eval, pairInput, ha, hb]
      have hp : f (pairInput ⟨a, ha⟩ ⟨b, hb⟩) = true := by
        cases hf : f (pairInput ⟨a, ha⟩ ⟨b, hb⟩) with
        | false => exact Bool.noConfusion ((hsound _ hf).symm.trans hpairInput)
        | true => rfl
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Fin.val h), hp, rfl, rfl⟩
    · have hx' : (List.ofFn x).getD a false = true ∨
          (List.ofFn x).getD b false = true := by
        simpa [gateValue, GateOp.eval] using hx
      rcases hx' with hxa | hxb
      · have ha : a < n := read_lt hxa
        have hh := hs ⟨a, ha⟩
        simp [gateValue, GateOp.eval, singleInput, ha] at hh
      · have hb : b < n := read_lt hxb
        have hh := hs ⟨b, hb⟩
        simp [gateValue, GateOp.eval, singleInput, hb] at hh
    · change (!(List.ofFn (fun _ : Fin n => false)).getD a false) = false at hz
      rw [read_zero] at hz
      cases hz
  · simp only [List.length_cons] at hlen
    omega

end PEqualNP.Outside.L_meta_2373_aux.FirstWire

namespace PEqualNP.Outside.L_meta_2373_aux.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil, Circuit.size]
    omega

lemma wires_input (C : Circuit) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (C.wires xs).getD i false = xs.getD i false := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun j => xs.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def prefixValue {n : ℕ} (g : Gate) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD i false

lemma prefix_input {n : ℕ} (g : Gate) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    prefixValue g C x i.val = x i := by
  unfold prefixValue
  rw [wires_input _ _ _ (by rw [wires_length]; simp [Circuit.size])]
  rw [wires_input _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma prefix_first {n : ℕ} (g : Gate) (C : Circuit) (x : Fin n → Bool) :
    prefixValue g C x n =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  unfold prefixValue
  rw [wires_input _ _ _ (by rw [wires_length]; simp [Circuit.size])]
  change (List.ofFn x ++ [_]).getD n false = _
  simp

lemma selected_bounds {n : ℕ} (g : Gate) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hsingle : ∀ i : Fin n, f (fun j => decide (j = i)) = false) (k : ℕ)
    (htrue : ∃ x : Fin n → Bool, prefixValue g C x k = true)
    (hsound : ∀ x, f x = false → prefixValue g C x k = false) :
    n ≤ k ∧ k < n + 1 + C.size := by
  constructor
  · by_contra h
    have hk : k < n := Nat.lt_of_not_ge h
    let i : Fin n := ⟨k, hk⟩
    have hf := hsound (fun j => decide (j = i)) (hsingle i)
    change prefixValue g C (fun j => decide (j = i)) i.val = false at hf
    rw [prefix_input] at hf
    simp at hf
  · obtain ⟨x, hx⟩ := htrue
    by_contra hk
    unfold prefixValue at hx
    rw [List.getD_eq_default _ _ (by
      rw [wires_length, wires_length]
      simp only [List.length_ofFn, Circuit.size, List.length_singleton]
      exact Nat.le_of_not_gt hk)] at hx
    contradiction

lemma selected_distinct {n : ℕ} (g : Gate) (C : Circuit) (i j : ℕ)
    (h : ∃ x : Fin n → Bool, prefixValue g C x i = true ∧
      prefixValue g C x j = false) : i ≠ j := by
  obtain ⟨x, hi, hj⟩ := h
  intro he
  subst j
  rw [hi] at hj
  contradiction

lemma exclusive_first_value {n : ℕ} (g : Gate) (C : Circuit) (j : ℕ)
    (h : ∃ x : Fin n → Bool, prefixValue g C x n = true ∧
      prefixValue g C x j = false) :
    ∃ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = true := by
  obtain ⟨x, hx, _⟩ := h
  exact ⟨x, (prefix_first g C x) ▸ hx⟩

end PEqualNP.Outside.L_meta_2373_aux.Wires

namespace PEqualNP.Outside.L_meta_2373_aux.Petersen

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

lemma zero_false : target (fun _ => false) = false := rfl

lemma singleton_false : ∀ i : Fin 10, target (fun j => decide (j = i)) = false := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma pair_true_iff : ∀ i j : Fin 10,
    target (fun k => decide (k = i ∨ k = j)) = true ↔
      (i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges := by
  decide

end PEqualNP.Outside.L_meta_2373_aux.Petersen

namespace PEqualNP.Outside.L_meta_2373_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma first_selected_is_edge (g : Gate) (C : Circuit)
    (hfan : FanInTwo { gates := [g], output := 0 })
    (htrue : ∃ x : Fin 10 → Bool, Wires.prefixValue g C x 10 = true)
    (hsound : ∀ x, Petersen.target x = false → Wires.prefixValue g C x 10 = false) :
    ∃ i j : Fin 10, i ≠ j ∧
      ((i.val, j.val) ∈ Petersen.edges ∨ (j.val, i.val) ∈ Petersen.edges) ∧
      g.op = GateOp.and ∧ g.inputs = [i.val, j.val] := by
  have ht : ∃ x : Fin 10 → Bool, FirstWire.gateValue g x = true := by
    simpa only [Wires.prefix_first, FirstWire.gateValue] using htrue
  have hs : ∀ x, Petersen.target x = false → FirstWire.gateValue g x = false := by
    simpa only [Wires.prefix_first, FirstWire.gateValue] using hsound
  obtain ⟨i, j, hij, hp, hop, hin⟩ := FirstWire.first_gate_classification
    Petersen.target Petersen.zero_false Petersen.singleton_false g hfan ht hs
  exact ⟨i, j, hij, (Petersen.pair_true_iff i j).mp hp, hop, hin⟩

lemma selected_pair_bounds (g : Gate) (C : Circuit) (i j : ℕ) (hsize : C.size ≤ 17)
    (hleft : ∃ x : Fin 10 → Bool, Wires.prefixValue g C x i = true ∧
      Wires.prefixValue g C x j = false)
    (hright : ∃ x : Fin 10 → Bool, Wires.prefixValue g C x i = false ∧
      Wires.prefixValue g C x j = true)
    (hsound : ∀ x, Petersen.target x = false →
      Wires.prefixValue g C x i = false ∧ Wires.prefixValue g C x j = false) :
    10 ≤ i ∧ i < 28 ∧ 10 ≤ j ∧ j < 28 ∧ i ≠ j := by
  have hi := Wires.selected_bounds g C Petersen.target Petersen.singleton_false i
    (by obtain ⟨x, h, _⟩ := hleft; exact ⟨x, h⟩) (fun x h => (hsound x h).1)
  have hj := Wires.selected_bounds g C Petersen.target Petersen.singleton_false j
    (by obtain ⟨x, _, h⟩ := hright; exact ⟨x, h⟩) (fun x h => (hsound x h).2)
  exact ⟨hi.1, by omega, hj.1, by omega, Wires.selected_distinct g C i j hleft⟩

end PEqualNP.Outside.L_meta_2373_aux


namespace PEqualNP.Outside.L_meta_2373_aux.LivePruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def down (k i : ℕ) : ℕ := if i < k then i else i - 1

def rename (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (down k)⟩

def gateValue (g : Gate) (xs : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

lemma effective_value (g : Gate) (xs : List Bool) :
    gateValue g xs = g.op.eval ((effective g).map fun i => xs.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> try rfl
  cases ins <;> rfl

lemma effective_rename (k : ℕ) (g : Gate) :
    effective (rename k g) = (effective g).map (down k) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [effective, rename, List.map_take]

lemma rename_value (k : ℕ) (g : Gate) (xs ys : List Bool)
    (hun : k ∉ effective g)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    gateValue (rename k g) xs = gateValue g ys := by
  rw [effective_value, effective_value, effective_rename]
  change g.op.eval (((effective g).map (down k)).map fun i => xs.getD i false) = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact heq i (fun h => hun (h ▸ hi))

lemma append_agree (k : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    ∀ i, i ≠ k → (xs ++ [b]).getD (down k i) false = (ys ++ [b]).getD i false := by
  intro i hi
  rcases Nat.lt_trichotomy i ys.length with hlt | he | hgt
  · have hd : down k i < xs.length := by unfold down; split <;> omega
    rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ hlt]
    exact heq i hi
  · subst i
    have hd : down k ys.length = xs.length := by unfold down; split <;> omega
    rw [hd]
    simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by
      simp only [List.length_append, List.length_singleton]
      unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma initial_agree (xs : List Bool) (b : Bool) :
    ∀ i, i ≠ xs.length → xs.getD (down xs.length i) false = (xs ++ [b]).getD i false := by
  intro i hi
  by_cases hlt : i < xs.length
  · simp only [down, ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt]
  · have hgt : xs.length < i := by omega
    rw [List.getD_eq_default _ _ (by unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma wires_rename (k : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length)
    (hun : ∀ g ∈ gs, k ∉ effective g)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    ∀ i, i ≠ k →
      (Circuit.wires ⟨gs.map (rename k), 0⟩ xs).getD (down k i) false =
      (Circuit.wires ⟨gs, 0⟩ ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    have hg : gateValue (rename k g) xs = gateValue g ys :=
      rename_value k g xs ys (hun g (by simp)) heq
    change ∀ i, i ≠ k →
      (Circuit.wires ⟨gs.map (rename k), 0⟩ (xs ++ [gateValue (rename k g) xs])).getD
        (down k i) false =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).getD i false
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro h hh
      exact hun h (by simp [hh])
    · exact append_agree k xs ys _ hlen hk heq

lemma wires_length (gs : List Gate) (xs : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def erase (n : ℕ) (pre post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ post.map (rename (n + pre.length)), down (n + pre.length) o⟩

lemma erase_eval (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hun : ∀ h ∈ post, n + pre.length ∉ effective h)
    (ho : o ≠ n + pre.length) (x : Fin n → Bool) :
    (erase n pre post o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [wires_length, List.length_ofFn]
  simp only [erase, Circuit.eval, Circuit.wires, List.foldl_append,
    List.foldl_cons]
  change (Circuit.wires ⟨post.map (rename (n + pre.length)), 0⟩ xs).getD
      (down (n + pre.length) o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD o false
  apply wires_rename _ _ _ _ (by simp) (by simp [hx]) hun _ o ho
  rw [← hx]
  exact initial_agree xs _

lemma erase_size (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ) :
    (erase n pre post o).size + 1 = (Circuit.mk (pre ++ g :: post) o).size := by
  simp [erase, Circuit.size]
  omega

lemma erase_fanin (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hfan : FanInTwo (Circuit.mk (pre ++ g :: post) o)) :
    FanInTwo (erase n pre post o) := by
  intro h hh
  change h ∈ pre ++ post.map (rename (n + pre.length)) at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hfan h (List.mem_append.mpr (Or.inl hh))
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
    subst h
    have hhf := hfan q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
    simpa [rename] using hhf

lemma minimal_live (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post)
    (ho : C.output ≠ n + pre.length) :
    ∃ h ∈ post, n + pre.length ∈ effective h := by
  by_contra hn
  have hun : ∀ h ∈ post, n + pre.length ∉ effective h := by
    intro h hh hi
    exact hn ⟨h, hh, hi⟩
  have hC : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  have hD := erase_fanin n pre post g C.output (hC ▸ hfan)
  have hsz := hmin (erase n pre post C.output) hD (by
    intro x
    rw [erase_eval n pre post g C.output hun ho x, ← hC])
  have hlen := erase_size n pre post g C.output
  rw [← hC] at hlen
  omega

lemma minimal_output_last (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hpos : 0 < C.size) : C.output + 1 = n + C.size := by
  have split_last (gs : List Gate) (hp : 0 < gs.length) :
      ∃ pre g, gs = pre ++ [g] := by
    induction gs using List.reverseRecOn with
    | nil => simp at hp
    | append_singleton pre g _ => exact ⟨pre, g, rfl⟩
  obtain ⟨pre, g, hs⟩ := split_last C.gates hpos
  have ho : C.output = n + pre.length := by
    by_contra hne
    obtain ⟨h, hh, _⟩ := minimal_live n C hfan hmin pre [] g hs hne
    simp at hh
  rw [ho]
  simp only [Circuit.size, hs, List.length_append, List.length_singleton]
  omega

lemma minimal_live_index (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (p : ℕ) (hp : p + 1 < C.size) :
    ∃ q, p < q ∧ ∃ g, C.gates[q]? = some g ∧ n + p ∈ effective g := by
  have hp' : p < C.gates.length := by change p + 1 < C.gates.length at hp; omega
  have hs : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
    rw [List.getElem_cons_drop hp', List.take_append_drop]
  have hlen : (C.gates.take p).length = p := by simp; omega
  have ho : C.output ≠ n + (C.gates.take p).length := by
    have hlast := minimal_output_last n C hfan hmin (by omega)
    rw [hlen]
    omega
  obtain ⟨g, hg, hread⟩ := minimal_live n C hfan hmin _ _ _ hs ho
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hg
  rw [List.getElem?_drop] at hq
  exact ⟨p + 1 + q, by omega, g, hq, by simpa [hlen] using hread⟩

lemma exists_minimal (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) := by
  classical
  let P (k : ℕ) := ∃ D : Circuit, FanInTwo D ∧ D.size = k ∧
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ k, P k := ⟨C.size, C, hfan, rfl, fun _ => rfl⟩
  obtain ⟨D, hD, hsize, heval⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, heval, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hfan, rfl, fun _ => rfl⟩
  · intro E hE hEC
    rw [hsize]
    apply Nat.find_min' hex
    exact ⟨E, hE, rfl, fun x => (hEC x).trans (heval x)⟩

lemma exists_live (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      (0 < D.size → D.output + 1 = n + D.size) ∧
      (∀ p, p + 1 < D.size →
        ∃ q, p < q ∧ ∃ g, D.gates[q]? = some g ∧ n + p ∈ effective g) := by
  obtain ⟨D, hD, hsz, heval, hmin⟩ := exists_minimal n C hfan
  exact ⟨D, hD, hsz, heval, hmin,
    minimal_output_last n D hD hmin, minimal_live_index n D hD hmin⟩

end PEqualNP.Outside.L_meta_2373_aux.LivePruning

namespace PEqualNP.Outside.L_meta_2373_aux.AliasPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux.LivePruning

def redirect (k p i : ℕ) : ℕ := if i = k then p else down k i

def renamed (k p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redirect k p)⟩

lemma renamed_value (k p : ℕ) (g : Gate) (xs ys : List Bool)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    gateValue (renamed k p g) xs = gateValue g ys := by
  unfold gateValue renamed
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact heq i

lemma append_agree (k p : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (xs ++ [b]).getD (redirect k p i) false = (ys ++ [b]).getD i false := by
  intro i
  by_cases hi : i = k
  · subst i
    simp only [redirect, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk]
    simpa [redirect] using heq k
  · simp only [redirect, ite_eq_right hi]
    apply LivePruning.append_agree k xs ys b hlen hk _ i hi
    intro j hj
    simpa [redirect, hj] using heq j

lemma initial_agree (xs : List Bool) (p : ℕ) (b : Bool)
    (hcopy : b = xs.getD p false) :
    ∀ i, xs.getD (redirect xs.length p i) false = (xs ++ [b]).getD i false := by
  intro i
  by_cases hi : i = xs.length
  · subst i
    simp [redirect, List.getD_eq_getElem?_getD, hcopy]
  · simpa [redirect, hi] using LivePruning.initial_agree xs b i hi

lemma wires_renamed (k p : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (Circuit.wires ⟨gs.map (renamed k p), 0⟩ xs).getD (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    have hg := renamed_value k p g xs ys heq
    change ∀ i,
      (Circuit.wires ⟨gs.map (renamed k p), 0⟩ (xs ++ [gateValue (renamed k p g) xs])).getD
        (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).getD i false
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · exact append_agree k p xs ys _ hlen hk hp heq

lemma wires_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (Circuit.wires ⟨gs, 0⟩ xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def erase (n : ℕ) (pre post : List Gate) (p o : ℕ) : Circuit :=
  ⟨pre ++ post.map (renamed (n + pre.length) p), redirect (n + pre.length) p o⟩

lemma erase_eval (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length)
    (hcopy : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false)
    (x : Fin n → Bool) :
    (erase n pre post p o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [wires_length, List.length_ofFn]
  have hcopy' : gateValue g xs = xs.getD p false := by
    have h := hcopy x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons] at h
    change (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD (n + pre.length) false =
      (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD p false at h
    rw [wires_input _ _ _ (by simp [hx]), wires_input _ _ _ (by simp [hx]; omega)] at h
    rw [List.getD_append xs [gateValue g xs] false p (by omega), ← hx] at h
    simpa [List.getD_eq_getElem?_getD] using h
  simp only [erase, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (Circuit.wires ⟨post.map (renamed (n + pre.length) p), 0⟩ xs).getD
      (redirect (n + pre.length) p o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD o false
  apply wires_renamed _ _ _ _ _ (by simp) (by simp [hx]) hp _ o
  rw [← hx]
  exact initial_agree xs p _ hcopy'

lemma erase_size (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ) :
    (erase n pre post p o).size + 1 = (Circuit.mk (pre ++ g :: post) o).size := by
  simp [erase, Circuit.size]
  omega

lemma erase_fanin (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hfan : FanInTwo (Circuit.mk (pre ++ g :: post) o)) :
    FanInTwo (erase n pre post p o) := by
  intro h hh
  change h ∈ pre ++ post.map (renamed (n + pre.length) p) at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hfan h (List.mem_append.mpr (Or.inl hh))
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
    subst h
    have hhf := hfan q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
    simpa [renamed] using hhf

lemma minimal_no_alias (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post)
    (p : ℕ) (hp : p < n + pre.length) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + pre.length) false =
      (C.wires (List.ofFn x)).getD p false := by
  intro hcopy
  have hC : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  have hD := erase_fanin n pre post g p C.output (hC ▸ hfan)
  have hsz := hmin (erase n pre post p C.output) hD (by
    intro x
    rw [erase_eval n pre post g p C.output hp (by simpa [← hC] using hcopy) x, ← hC])
  have hlen := erase_size n pre post g p C.output
  rw [← hC] at hlen
  omega

lemma minimal_no_alias_index (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (k : ℕ) (hk : k < C.size) (p : ℕ) (hp : p < n + k) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD p false := by
  have hk' : k < C.gates.length := hk
  have hs : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.getElem_cons_drop hk', List.take_append_drop]
  have hlen : (C.gates.take k).length = k := by simp; omega
  simpa [hlen] using minimal_no_alias n C hfan hmin _ _ _ hs p (by simpa [hlen] using hp)

end PEqualNP.Outside.L_meta_2373_aux.AliasPruning


namespace PEqualNP.Outside.L_meta_2373_aux.Seed

open PEqualNP.CircuitLowerBounds

def candidate : Circuit :=
  { gates :=
    [ ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [4, 12]⟩,
      ⟨GateOp.and, [14, 11]⟩,
      ⟨GateOp.and, [7, 12]⟩,
      ⟨GateOp.or, [5, 3]⟩,
      ⟨GateOp.and, [9, 10]⟩,
      ⟨GateOp.or, [8, 15]⟩,
      ⟨GateOp.and, [1, 13]⟩,
      ⟨GateOp.or, [18, 17]⟩,
      ⟨GateOp.and, [19, 21]⟩,
      ⟨GateOp.or, [20, 16]⟩,
      ⟨GateOp.or, [22, 23]⟩ ],
    output := 24 }

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def expression (x : Fin 9 → Bool) : Bool :=
  (((x 8 || ((x 4 || (x 2 || x 5)) && (x 0 || x 3))) && (((x 4 || x 6) && (x 0 || x 6)) || (x 5 || x 3))) || ((x 1 && (x 2 || (x 0 || x 6))) || (x 7 && (x 2 || x 5))))

set_option maxHeartbeats 2000000 in
lemma candidate_expression (x : Fin 9 → Bool) :
    candidate.eval (List.ofFn x) = expression x := by
  simp [candidate, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, expression]

set_option maxHeartbeats 5000000 in
lemma candidate_formula (x : Fin 9 → Bool) :
    candidate.eval (List.ofFn x) =
      (target x || (x 3 && x 5) || (x 0 && x 2 && x 6)) := by
  rw [candidate_expression]
  unfold expression target
  generalize h0 : x 0 = a0
  generalize h1 : x 1 = a1
  generalize h2 : x 2 = a2
  generalize h3 : x 3 = a3
  generalize h4 : x 4 = a4
  generalize h5 : x 5 = a5
  generalize h6 : x 6 = a6
  generalize h7 : x 7 = a7
  generalize h8 : x 8 = a8
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> cases a7 <;> cases a8 <;> rfl

lemma candidate_size : candidate.size = 16 := by
  rfl

lemma candidate_fanin : PEqualNP.MetaComplexity.FanInTwo candidate := by
  simp [PEqualNP.MetaComplexity.FanInTwo, candidate]

end PEqualNP.Outside.L_meta_2373_aux.Seed
