import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_27759

open PEqualNP.CircuitLowerBounds

private abbrev Atom := Fin 6

private def dual (a : Atom) : Atom :=
  if a = 0 then 5 else if a = 5 then 0 else if a = 3 then 4 else if a = 4 then 3 else a

private def infimum (a b : Atom) : Atom :=
  if a = 0 ∨ b = 0 then 0 else if a = 5 then b else if b = 5 then a
  else if a = 3 ∨ b = 3 then 3 else if a = 4 then b else if b = 4 then a
  else if a = b then a else 3

private def op (s : Bool) (a b : Atom) : Atom :=
  if s then dual (infimum (dual a) (dual b)) else infimum a b

private abbrev Col := Atom × Atom
private def dead : Col := (0, 0)
private def goalCol : Col := (3, 4)
private abbrev good (w : Col) : Prop := w ≠ goalCol ∧ w ≠ (4, 3)
private def blend (s : Bool) (u v : Col) : Col := (op s u.1 v.1, op s u.2 v.2)

private def uses (axis : Bool) (a : Atom) : Bool :=
  if a = 0 ∨ a = 5 then false else if a = 1 then !axis else if a = 2 then axis else true

private def cost (axis : Bool) (w : Col) := (uses axis w.1 || uses axis w.2).toNat

private lemma blend_good : ∀ (s : Bool) (u v : Col), good u → good v →
    (∀ t : Bool, cost t u + cost t v ≤ 1) → good (blend s u v) := by decide +kernel

private lemma blend_cost : ∀ (s t : Bool) (u v : Col),
    cost t (blend s u v) ≤ cost t u + cost t v := by decide +kernel

private def observe (p q : Bool) (a : Atom) : Bool :=
  if a = 0 then false else if a = 1 then p else if a = 2 then q
  else if a = 3 then p && q else if a = 4 then p || q else true

private def view (s p q : Bool) (w : Col) : Bool := observe p q (if s then w.2 else w.1)

private lemma blend_view : ∀ (b s p q : Bool) (u v : Col),
    view s p q (blend b u v) =
      if b then view s p q u || view s p q v else view s p q u && view s p q v := by decide +kernel

private lemma distinguish : ∀ w : Col, (∀ s p q, view s p q w = view s p q goalCol) → w = goalCol := by
  decide +kernel

private def bin (op : Bool) (a b : Nat) : Gate := ⟨if op then .or else .and, [a,b]⟩

private def reads (gs : List Gate) (o : Nat) := gs.flatMap Gate.inputs ++ [o]

private def need (t : Bool) (w : List Col) (rs : List Nat) : Nat :=
  (rs.map fun j => cost t (w.getD j dead)).sum

private lemma need_cons (t : Bool) (w : List Col) (a : Nat) (rs : List Nat) :
    need t w (a::rs) = cost t (w.getD a dead) + need t w rs := rfl

private lemma snoc_eq (w : List Col) (v : Col) : (w ++ [v]).getD w.length dead = v := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

private lemma snoc_ne (w : List Col) (v : Col) (j : Nat) (hn : j ≠ w.length) :
    (w ++ [v]).getD j dead = w.getD j dead := by
  by_cases h : j < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma need_snoc (t : Bool) (w : List Col) (v : Col) (rs : List Nat) :
    need t (w ++ [v]) rs ≤ need t w rs + rs.count w.length * cost t v := by
  induction rs with
  | nil => simp [need]
  | cons j rs ih =>
    rw [need_cons, need_cons, List.count_cons]
    by_cases h : j = w.length
    · subst j
      rw [snoc_eq]
      simp only [beq_self_eq_true, ite_true, Nat.add_mul, Nat.one_mul]
      omega
    · rw [snoc_ne _ _ _ h]
      simp [h]
      omega

private def gateCol (g : Gate) (w : List Col) : Col :=
  let s := match g.op with | .or => true | _ => false
  blend s (w.getD (g.inputs.getD 0 0) dead) (w.getD (g.inputs.getD 1 0) dead)

private lemma gate_bin (s : Bool) (a b : Nat) (w : List Col) :
    gateCol (bin s a b) w = blend s (w.getD a dead) (w.getD b dead) := by cases s <;> rfl

private def run : List Gate → List Col → List Col
  | [], w => w
  | g :: gs, w => run gs (w ++ [gateCol g w])

private lemma flow (gs : List Gate) (o : Nat) (w : List Col)
    (binary : ∀ g ∈ gs, ∃ s a b, g = bin s a b)
    (ok : ∀ i, good (w.getD i dead))
    (budget : ∀ t, need t w (reads gs o) ≤ 1)
    (single : ∀ j, w.length ≤ j → (reads gs o).count j ≤ 1) :
    good ((run gs w).getD o dead) := by
  induction gs generalizing w with
  | nil => exact ok o
  | cons g gs ih =>
    obtain ⟨s, a, b, rfl⟩ := binary g List.mem_cons_self
    let z := blend s (w.getD a dead) (w.getD b dead)
    have reads_eq : reads (bin s a b :: gs) o = a :: b :: reads gs o := by
      simp [reads, bin]
    have bounded (t : Bool) : cost t (w.getD a dead) + cost t (w.getD b dead) +
        need t w (reads gs o) ≤ 1 := by simpa only [reads_eq, need_cons, Nat.add_assoc] using budget t
    have gz : good z := blend_good s _ _ (ok a) (ok b) (fun t => by have := bounded t; omega)
    have rest_count (j : Nat) (hj : w.length ≤ j) : (reads gs o).count j ≤ 1 := by
      have h := single j hj
      rw [reads_eq, List.count_cons, List.count_cons] at h
      omega
    rw [run, gate_bin]
    apply ih (w := w ++ [z]) (fun g hg => binary g (List.mem_cons_of_mem _ hg))
    · intro i
      by_cases hi : i = w.length
      · subst i; rwa [snoc_eq]
      · rw [snoc_ne _ _ _ hi]; exact ok i
    · intro t
      have h := need_snoc t w z (reads gs o)
      have hc := Nat.mul_le_mul_right (cost t z) (rest_count w.length le_rfl)
      simp only [Nat.one_mul] at hc
      have hcost : cost t z ≤ cost t (w.getD a dead) + cost t (w.getD b dead) := blend_cost s t _ _
      have hb := bounded t
      omega
    · intro j hj
      exact rest_count j (by simp at hj; omega)

private lemma read_view (w : List Col) (s p q : Bool) (j : Nat) :
    (w.map (view s p q)).getD j false = view s p q (w.getD j dead) := by
  cases h : w[j]? <;> simp [List.getD, h, view, dead, observe]

private def stepBool (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma one_view (w : List Col) (s p q b : Bool) (a d : Nat) :
    (w ++ [gateCol (bin b a d) w]).map (view s p q) =
      stepBool (w.map (view s p q)) (bin b a d) := by
  simp only [List.map_append, List.map_cons, List.map_nil, gate_bin, blend_view]
  rw [← read_view, ← read_view]
  cases b <;> simp [stepBool, bin, GateOp.eval]

private lemma run_view (gs : List Gate) (w : List Col) (s p q : Bool)
    (hb : ∀ g ∈ gs, ∃ t a b, g = bin t a b) :
    (run gs w).map (view s p q) = gs.foldl stepBool (w.map (view s p q)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨t,a,b,rfl⟩ := hb g List.mem_cons_self
    rw [run, List.foldl_cons, ih _ (fun g hg => hb g (List.mem_cons_of_mem _ hg)), one_view]

private def start : List Col :=
  [(5,5), (5,5), (0,5), (5,5), dead, (1,1), (0,5), (2,2), dead]

private def assign (s p q : Bool) (i : Fin 9) := view s p q (start.getD i.val dead)

private def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private lemma start_view : ∀ s p q, start.map (view s p q) = List.ofFn (assign s p q) := by decide

private lemma target : ∀ s p q, matching (assign s p q) = view s p q goalCol := by decide

private lemma start_valid (i : Nat) : good (start.getD i dead) := by
  by_cases h : i < 9
  · exact (by decide : ∀ i : Fin 9, good (start.getD i.val dead)) ⟨i,h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ i; omega)]; decide

private def index (t : Bool) : Nat := if t then 7 else 5

private lemma start_cost (t : Bool) (j : Nat) : cost t (start.getD j dead) = if j = index t then 1 else 0 := by
  by_cases h : j < 9
  · exact (by decide : ∀ t (j : Fin 9), cost t (start.getD j.val dead) =
      if j.val = index t then 1 else 0) t ⟨j,h⟩
  · rw [List.getD_eq_default _ _ (by change 9 ≤ j; omega)]
    cases t <;> simp [index, cost, dead, uses] <;> omega

private lemma start_need (t : Bool) (rs : List Nat) : need t start rs = rs.count (index t) := by
  induction rs with
  | nil => rfl
  | cons j rs ih =>
    rw [need_cons, start_cost, ih, List.count_cons]
    by_cases h : j = index t <;> simp [h, Nat.add_comm]

private lemma impossible (C : Circuit)
    (hc : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x)
    (hb : ∀ g ∈ C.gates, ∃ t a b, g = bin t a b)
    (h5 : (reads C.gates C.output).count 5 ≤ 1) (h6 : (reads C.gates C.output).count 7 ≤ 1)
    (hs : ∀ j, 9 ≤ j → (reads C.gates C.output).count j ≤ 1) : False := by
  have hg := flow C.gates C.output start hb start_valid (fun t => by
    rw [start_need]; cases t <;> first | exact h5 | exact h6) hs
  apply hg.1
  apply distinguish
  intro s p q
  rw [← read_view, run_view _ _ _ _ _ hb, start_view]
  change C.eval (List.ofFn (assign s p q)) = _
  rw [hc, target]


open PEqualNP.CircuitLowerBounds

private def occTarget (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

private def occFirst : Gate := ⟨.or, [0, 1]⟩

private def occSecond : Gate := ⟨.or, [3, 6]⟩

private def occProbe (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

private lemma occWitness (i : Fin 9) : ∃ x y : Fin 9 → Bool,
    occTarget x ≠ occTarget y ∧ (x 0 || x 1) = (y 0 || y 1) ∧
    (x 3 || x 6) = (y 3 || y 6) ∧ (∀ j, j ≠ i → x j = y j) := by
  refine ⟨occProbe (![162, 97, 80, 196, 68, 66, 28, 12, 10] i),
    occProbe (![163, 99, 84, 204, 84, 98, 92, 140, 266] i), ?_⟩
  fin_cases i <;> decide

private def occStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def occAgree (a b : List Bool) (i : ℕ) : Prop :=
  a.length = b.length ∧ ∀ j, j ≠ i → a.getD j false = b.getD j false

private lemma occAppend {a b : List Bool} {i : ℕ} (h : occAgree a b i) (z : Bool) :
    occAgree (a ++ [z]) (b ++ [z]) i := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hjl : j < a.length
  · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (h.1 ▸ hjl)]
    exact h.2 j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

private lemma occFold (gs : List Gate) {i : ℕ} (hn : i ∉ gs.flatMap Gate.inputs)
    {a b : List Bool} (h : occAgree a b i) :
    occAgree (gs.foldl occStep a) (gs.foldl occStep b) i := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hp : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by simpa using hn
    have he : g.inputs.map (fun k => a.getD k false) = g.inputs.map (fun k => b.getD k false) := by
      apply List.map_congr_left
      intro k hk
      exact h.2 k (fun he => hp.1 (he ▸ hk))
    apply ih hp.2
    unfold occStep
    rw [he]
    exact occAppend h _

private lemma occInitial (x : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
    (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

private lemma occPrefix (x : Fin 9 → Bool) :
    occStep (occStep (List.ofFn x) occFirst) occSecond =
      (List.ofFn x ++ [x 0 || x 1]) ++ [x 3 || x 6] := by
  simp [occStep, occFirst, occSecond, GateOp.eval]

private lemma occTailInput (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hout : C.output + 1 = 9 + C.size) (i : Fin 9) :
    i.val ∈ gs.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨x, y, hxy, h01, h38, hsame⟩ := occWitness i
  have hbase : occAgree (List.ofFn x) (List.ofFn y) i.val := by
    refine ⟨by simp, ?_⟩
    intro j hji
    by_cases hj : j < 9
    · rw [occInitial x j hj, occInitial y j hj]
      exact hsame _ (fun h => hji (congrArg Fin.val h))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hpre : occAgree (occStep (occStep (List.ofFn x) occFirst) occSecond)
      (occStep (occStep (List.ofFn y) occFirst) occSecond) i.val := by
    rw [occPrefix, occPrefix, h01, h38]
    exact occAppend (occAppend hbase _) _
  have ho : C.output ≠ i.val := by
    have hz : C.size = gs.length + 2 := by simp [Circuit.size, hg]
    have hi := i.isLt
    omega
  apply hxy
  rw [← hcomp, ← hcomp]
  change (C.gates.foldl occStep (List.ofFn x)).getD C.output false =
    (C.gates.foldl occStep (List.ofFn y)).getD C.output false
  rw [hg]
  exact (occFold gs hn hpre).2 _ ho

private lemma occCap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht := ih (fun a ha => hf a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private lemma occTight (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (he : (gs.flatMap Gate.inputs).length = 2 * gs.length) :
    ∀ g ∈ gs, g.inputs.length = 2 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := hf g (by simp)
    have ht : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hf a (by simp [ha])
    have hc := occCap gs ht
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at he
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact ih ht (by omega) a ha

private lemma occSplit (C : Circuit) (h0 : C.gates.head? = some occFirst)
    (h1 : C.gates.tail.head? = some occSecond) :
    ∃ gs, C.gates = occFirst :: occSecond :: gs := by
  cases hg : C.gates with
  | nil => simp [hg] at h0
  | cons a t =>
    cases ht : t with
    | nil => simp [hg, ht] at h1
    | cons b gs =>
      have ha : a = occFirst := by simpa [hg] using h0
      have hb : b = occSecond := by simpa [hg, ht] using h1
      exact ⟨gs, by simp [ha, hb]⟩

private lemma occRigidTail (C : Circuit) (gs : List Gate) (hg : C.gates = occFirst :: occSecond :: gs)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 12)
    (hout : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hinputs : ∀ i : Fin 9, i.val ∈ gs.flatMap Gate.inputs) :
    C.size = 12 ∧ (∀ g ∈ C.gates, g.inputs.length = 2) ∧
      (gs.flatMap Gate.inputs ++ [C.output]).Nodup := by
  let r := gs.flatMap Gate.inputs ++ [C.output]
  have hlen : C.size = gs.length + 2 := by simp [Circuit.size, hg]
  have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g hm => (hf g (by simp [hg, hm])).2
  have hsub : Finset.range (9 + C.size) ⊆ r.toFinset := by
    intro j hj
    have hb := Finset.mem_range.mp hj
    apply List.mem_toFinset.mpr
    by_cases hsmall : j < 9
    · exact List.mem_append_left _ (hinputs ⟨j, hsmall⟩)
    by_cases hlast : j = C.output
    · simp [r, hlast]
    have hidx : j - 9 < C.gates.length := by change j - 9 < C.size; omega
    let k : Fin C.gates.length := ⟨j - 9, hidx⟩
    have hjk : 9 + k.val = j := by dsimp [k]; omega
    have hnlast : k.val + 1 < C.gates.length := by change j - 9 + 1 < C.size; omega
    obtain ⟨n, _, hn⟩ := hlive k hnlast
    have hall : j ∈ C.gates.flatMap Gate.inputs :=
      List.mem_flatMap.mpr ⟨C.gates.get n, List.get_mem _ _, hjk ▸ hn⟩
    simp only [hg, List.flatMap_cons, occFirst, occSecond, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hall
    apply List.mem_append_left
    rcases hall with (h | h) | (h | h) | ha <;> omega
  have hcard : 9 + C.size ≤ r.toFinset.card := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hcl := List.toFinset_card_le r
  have hrl : r.length = (gs.flatMap Gate.inputs).length + 1 := by simp [r]
  have hc := occCap gs hgs
  refine ⟨by omega, ?_, ?_⟩
  · intro g hm
    rw [hg] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    exact occTight gs hgs (by omega) g hm
  · exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (r : Multiset ℕ))).mp
      (show r.toFinset.card = r.length by omega)

private lemma occRigid (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 12)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = occTarget x)
    (hout : C.output + 1 = 9 + C.size)
    (hnorm : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some occFirst) (h1 : C.gates.tail.head? = some occSecond) :
    C.size = 12 ∧ (∀ g ∈ C.gates, ∃ a b : ℕ,
        g = ⟨GateOp.and, [a,b]⟩ ∨ g = ⟨GateOp.or, [a,b]⟩) ∧
      (C.gates.flatMap Gate.inputs ++ [C.output]).count 5 ≤ 1 ∧
      (C.gates.flatMap Gate.inputs ++ [C.output]).count 7 ≤ 1 ∧
      ∀ j : ℕ, 9 ≤ j → (C.gates.flatMap Gate.inputs ++ [C.output]).count j ≤ 1 := by
  obtain ⟨gs, hg⟩ := occSplit C h0 h1
  obtain ⟨hsize, hlen, hnd⟩ := occRigidTail C gs hg hf hs hout hlive
    (occTailInput C gs hg hcomp hout)
  have he : C.gates.flatMap Gate.inputs ++ [C.output] =
      0 :: 1 :: 3 :: 6 :: (gs.flatMap Gate.inputs ++ [C.output]) := by
    simp [hg, occFirst, occSecond]
  have hu (j : ℕ) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj6 : j ≠ 6) :
      (C.gates.flatMap Gate.inputs ++ [C.output]).count j ≤ 1 := by
    rw [he]
    simpa [List.count_cons, Ne.symm hj0, Ne.symm hj1, Ne.symm hj3, Ne.symm hj6] using
      List.nodup_iff_count_le_one.mp hnd j
  refine ⟨hsize, ?_, hu 5 (by decide) (by decide) (by decide) (by decide),
    hu 7 (by decide) (by decide) (by decide) (by decide),
    fun j hj => hu j (by omega) (by omega) (by omega) (by omega)⟩
  intro g hm
  obtain ⟨n, hn⟩ := List.get_of_mem hm
  have hnrm := hnorm n
  rw [hn] at hnrm
  rcases hnrm with ⟨_, a, _, ha⟩ | ⟨hop, a, b, _, _, hp⟩
  · have hl := hlen g hm
    simp [ha] at hl
  · refine ⟨a, b, ?_⟩
    have heq : g = ⟨g.op, g.inputs⟩ := rfl
    rcases hop with hop | hop
    · left
      exact heq.trans (by rw [hop, hp])
    · right
      exact heq.trans (by rw [hop, hp])



end PEqualNP.Outside.L_meta_27759

open PEqualNP.Outside.L_meta_27759 in
theorem PEqualNP.Outside.L_meta_27759 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩)) := by
  rintro ⟨C, hf, hs, hc, hout, hnorm, _, hlive, h0, h1⟩
  obtain ⟨_, hg, h5, h6, hi⟩ := occRigid C hf hs hc hout hnorm hlive h0 h1
  apply impossible C hc ?_ h5 h6 hi
  intro g hm
  obtain ⟨a, b, h | h⟩ := hg g hm
  · exact ⟨false, a, b, h⟩
  · exact ⟨true, a, b, h⟩
