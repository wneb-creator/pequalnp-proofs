import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_5252_aux

-- The monotone propagation argument extends the bypass proof in L_meta_2245.
-- A missing wire denotes false. This permits removal even when the chosen replacement is false.
private def read (w : List Bool) (i : Option ℕ) : Bool :=
  i.elim false (fun j => w.getD j false)

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

private theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private def projectWire (cut a i : ℕ) : Option ℕ :=
  if i < cut then some i else if i = cut then
    (if a < cut then some a else none) else some (i - 1)

private theorem project_bound {cut a i z m : ℕ} (hm : cut ≤ m) (hi : i < m + 1)
    (hz : projectWire cut a i = some z) : z < m := by
  unfold projectWire at hz
  split_ifs at hz <;> simp_all <;> omega

-- An OR gate ignores missing inputs. An AND gate with a missing input becomes an empty OR.
private def mapGate (f : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (fun i => (f i).isNone) then ⟨.or, []⟩
            else ⟨.and, g.inputs.filterMap f⟩
  | op => ⟨op, g.inputs.filterMap f⟩

private theorem mapped_inputs (f : ℕ → Option ℕ) (g : Gate) :
    (mapGate f g).inputs = [] ∨ (mapGate f g).inputs = g.inputs.filterMap f := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases h : ins.any (fun i => (f i).isNone) <;> simp [mapGate, h]

private theorem mapGate_valid (f : ℕ → Option ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (mapGate f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (mapGate f g).inputs.length ≤ 2 := by
  constructor
  · rcases g with ⟨op, ins⟩
    have hop : op = .and ∨ op = .or := by simpa using hg.1
    rcases hop with rfl | rfl
    · cases h : ins.any (fun i => (f i).isNone) <;> simp [mapGate, h]
    · simp [mapGate]
  · rcases mapped_inputs f g with h | h
    · simp [h]
    · rw [h]
      exact (List.length_filterMap_le ..).trans hg.2

private theorem any_project (f : ℕ → Option ℕ) (p : ℕ → Bool) (xs : List ℕ) :
    (xs.filterMap f).any p = xs.any (fun i => (f i).elim false p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : f i <;> simp [h, ih]

private theorem all_project (f : ℕ → Option ℕ) (p : ℕ → Bool) (xs : List ℕ) :
    ((xs.filterMap f).all p && !(xs.any (fun i => (f i).isNone))) =
      xs.all (fun i => (f i).elim false p) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : f i <;> simp [h, ← ih, Bool.and_assoc]

private theorem mapGate_value (f : ℕ → Option ℕ) (g : Gate) (v : List Bool)
    (hop : g.op = .and ∨ g.op = .or) :
    value (mapGate f g) v = g.op.eval (g.inputs.map (fun i => read v (f i))) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hop
  rcases hop with rfl | rfl
  · cases h : ins.any (fun i => (f i).isNone) <;>
      simpa [value, mapGate, h, GateOp.eval, List.all_map, Function.comp_def, read]
        using all_project f (fun i => v.getD i false) ins
  · simpa [value, mapGate, GateOp.eval, List.any_map, Function.comp_def, read]
      using any_project f (fun i => v.getD i false) ins

private theorem opposite {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

private theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

private theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool) (h : ∀ i, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).2

-- For either label, a change toward that label propagates through AND and OR gates.
private theorem run_flow (t : Bool) (f : ℕ → Option ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hp : ∀ i < w.length, ∀ z, f i = some z → z < v.length)
    (hs : ∀ i, w.length ≤ i → f i = some (v.length + (i - w.length)))
    (hf : ∀ i, w.getD i false = t → read v (f i) = t) :
    ∀ i, (run gs w).getD i false = t → read (run (gs.map (mapGate f)) v) (f i) = t := by
  induction gs generalizing w v with
  | nil => exact hf
  | cons g gs ih =>
    have ht (a : Gate) (ha : a ∈ gs) := hops a (List.mem_cons_of_mem _ ha)
    have hstep : value g w = t → value (mapGate f g) v = t := by
      rw [mapGate_value f g v (hops g List.mem_cons_self)]
      exact gate_flow t g.op (hops g List.mem_cons_self) g.inputs _ _ hf
    simp only [List.map_cons, run_cons]
    have hw : (w ++ [value g w]).length = w.length + 1 := by simp
    have hv : (v ++ [value (mapGate f g) v]).length = v.length + 1 := by simp
    apply ih _ _ ht
    · intro i hi z hz
      rw [hw] at hi
      rw [hv]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · exact (hp i hlt z hz).trans (Nat.lt_succ_self _)
      · rw [hs _ le_rfl, Nat.sub_self, Nat.add_zero] at hz
        exact (Option.some.inj hz) ▸ Nat.lt_succ_self _
    · intro i hi
      rw [hw] at hi
      rw [hw, hv, hs i (by omega)]
      congr 1
      omega
    · intro i
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi]
        have keep : read (v ++ [value (mapGate f g) v]) (f i) = read v (f i) := by
          cases h : f i with
          | none => rfl
          | some z => exact List.getD_append _ _ _ _ (hp i hi z h)
        rw [keep]
        exact hf i
      · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hi'
        · rw [hs _ le_rfl, Nat.sub_self, Nat.add_zero]
          simpa [read] using hstep
        · rw [hs i (by omega)]
          change (w ++ [_]).getD i false = t → (v ++ [_]).getD _ false = t
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          exact id

private theorem separate (S : Bool → List Bool → Prop) (C : Circuit)
    (hlen : ∀ t w, S t w → w.length = 26) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (hfit : ∀ t w, S t w → C.eval w = t)
    (hmin : ¬ ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧
      ∀ t w, S t w → D.eval w = t) ∧ D.size < C.size)
    (j : ℕ) (hj : j < C.size) (a : ℕ) (ha : a ≤ 26 + j) :
    ∃ t w, S t w ∧ (C.wires w).getD (26 + j) false = t ∧
      (if a = 26 + j then false else (C.wires w).getD a false) = !t := by
  by_contra miss
  change j < C.gates.length at hj
  let front := C.gates.take j
  let tail := C.gates.drop (j + 1)
  let g := C.gates[j]
  let k := 26 + j
  let f := projectWire k a
  let new := front ++ tail.map (mapGate f)
  let out := (f C.output).getD (26 + new.length)
  have hfront : front.length = j := by simp [front, Nat.min_eq_left hj.le]
  have hsplit : C.gates = front ++ g :: tail := by
    rw [show g :: tail = C.gates.drop j from (List.drop_eq_getElem_cons hj).symm]
    exact (List.take_append_drop j C.gates).symm
  have hnew : new.length = C.gates.length - 1 := by simp [new, hfront, tail]; omega
  apply hmin
  refine ⟨⟨new, out⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro b hmem
    change b ∈ front ++ tail.map (mapGate f) at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hm b (List.mem_of_mem_take hmem)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      exact mapGate_valid f q (hm q (List.mem_of_mem_drop hq))
  · intro i hi u hu
    change i < new.length at hi
    change u ∈ (new.getD i ⟨.or, []⟩).inputs at hu
    rw [List.getD_eq_getElem _ _ hi] at hu
    by_cases hif : i < front.length
    · change u ∈ ((front ++ tail.map (mapGate f))[i]'hi).inputs at hu
      rw [List.getElem_append_left hif] at hu
      have ho : i < C.gates.length := by omega
      apply hb i ho
      unfold gateAt
      rw [List.getD_eq_getElem _ _ ho]
      simpa [front] using hu
    · change u ∈ ((front ++ tail.map (mapGate f))[i]'hi).inputs at hu
      rw [List.getElem_append_right (by omega)] at hu
      simp only [List.getElem_map] at hu
      have hv : i + 1 < C.gates.length := by omega
      have he : i - front.length + (j + 1) = i + 1 := by omega
      have hu' : u ∈ (mapGate f C.gates[i+1]).inputs := by
        simpa only [tail, List.getElem_drop, Nat.add_comm (j+1), he] using hu
      rcases mapped_inputs f C.gates[i+1] with h | h
      · simp [h] at hu'
      · rw [h] at hu'
        obtain ⟨v, hv', hfu⟩ := List.mem_filterMap.mp hu'
        have hvGate : gateAt C (i+1) = C.gates[i+1] := List.getD_eq_getElem _ _ hv
        have hq := hb (i+1) hv v (by rwa [hvGate])
        exact project_bound (cut := k) (by dsimp [k]; omega) (by omega) hfu
  · intro t w hw
    let pre := run front w
    let both := pre ++ [value g pre]
    have hp : pre.length = k := by simp [pre, run_length, hlen t w hw, hfront, k]
    have hp' : both.length = k + 1 := by simp [both, hp]
    have hW : C.wires w = run tail both := by
      change run C.gates w = _
      rw [hsplit, run_append, run_cons]
    have hgate : (C.wires w).getD k false = value g pre := by
      rw [hW, run_preserves _ _ _ (by omega)]
      change (pre ++ [value g pre]).getD k false = _
      rw [← hp]
      simp
    have hlocal : value g pre = t → read pre (f k) = t := by
      intro hval
      by_contra h
      apply miss
      refine ⟨t, w, hw, hgate.trans hval, ?_⟩
      change (if a = k then false else (C.wires w).getD a false) = !t
      have hne := opposite h
      by_cases hself : a = k
      · simpa [f, projectWire, hself, read] using hne
      · have hlt : a < k := lt_of_le_of_ne ha hself
        have hwire : (C.wires w).getD a false = pre.getD a false := by
          rw [hW, run_preserves _ _ _ (by omega)]
          exact List.getD_append _ _ _ _ (by omega)
        rw [ite_eq_right hself, hwire]
        simpa [f, projectWire, hlt, read] using hne
    have hflow : ∀ i, both.getD i false = t → read pre (f i) = t := by
      intro i hi
      by_cases hlt : i < k
      · simp only [f, projectWire, ite_eq_left hlt, read, Option.elim_some]
        exact (List.getD_append _ _ _ _ (by omega : i < pre.length)) ▸ hi
      · by_cases heq : i = k
        · subst i
          apply hlocal
          change (pre ++ [value g pre]).getD k false = t at hi
          simpa [← hp] using hi
        · have hix : f i = some (i - 1) := by simp [f, projectWire, hlt, heq]
          change both.getD i false = t at hi
          rw [hix]
          change pre.getD (i - 1) false = t
          rw [List.getD_eq_default _ _ (by omega)]
          rwa [List.getD_eq_default _ _ (by omega : both.length ≤ i)] at hi
    have hresult := run_flow t f tail both pre
      (fun z hz => by simpa using (hm z (List.mem_of_mem_drop hz)).1)
      (by intro i hi z h; exact project_bound (by omega) (by omega) h)
      (by
        intro i hi
        have h : k < i := by omega
        simp only [f, projectWire, ite_eq_right (by omega : ¬ i < k), ite_eq_right h.ne']
        congr 1
        omega)
      hflow C.output
    have hdef : read (run new w) (f C.output) = (run new w).getD out false := by
      cases h : f C.output with
      | none =>
        simp only [out, h, read, Option.elim_none, Option.getD_none]
        rw [List.getD_eq_default _ _ (by rw [run_length, hlen t w hw])]
      | some z => simp [out, h, read]
    change (run new w).getD out false = t
    rw [← hdef, show new = front ++ tail.map (mapGate f) from rfl, run_append]
    apply hresult
    rw [← hW]
    exact hfit t w hw
  · change new.length < C.gates.length
    omega

end PEqualNP.Outside.L_meta_5252_aux

theorem PEqualNP.Outside.L_meta_5252 : ∀ (S : Bool → List Bool → Prop) (C : Circuit),
    (∀ t w, S t w → w.length = 26) → Monotone2 C → ReadsBack 26 C →
    (∀ t w, S t w → C.eval w = t) →
    (¬ ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧
      ∀ t w, S t w → D.eval w = t) ∧ D.size < C.size) →
    ∀ j < C.size, ∀ a ≤ 26 + j, ∃ t w, S t w ∧
      (C.wires w).getD (26 + j) false = t ∧
      (if a = 26 + j then false else (C.wires w).getD a false) = !t := by
  exact L_meta_5252_aux.separate
