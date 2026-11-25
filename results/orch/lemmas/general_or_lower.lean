import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_1031_aux.CompactOr

open PEqualNP.CircuitLowerBounds

def meet (values : List Bool) (atoms : List ℕ) : Bool :=
  atoms.all (fun i => values.getD i false)

def step (values : List Bool) (g : List ℕ × List ℕ) : List Bool :=
  values ++ [meet values g.1 || meet values g.2]

def wires (program : List (List ℕ × List ℕ)) (x : List Bool) : List Bool :=
  program.foldl step x

def eval (program : List (List ℕ × List ℕ)) (output : List ℕ) (x : List Bool) : Bool :=
  meet (wires program x) output

def bounded (bound : ℕ) (atoms : List ℕ) : Prop := ∀ i ∈ atoms, i < bound

def wellFormed (n : ℕ) (program : List (List ℕ × List ℕ)) : Prop :=
  ∀ j < program.length,
    bounded (n + j) (program.getD j ([], [])).1 ∧
    bounded (n + j) (program.getD j ([], [])).2

def isOr (g : Gate) : Bool := match g.op with
  | GateOp.or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP isOr

lemma meet_append (values : List Bool) (a b : List ℕ) :
    meet values (a ++ b) = (meet values a && meet values b) := by
  simp [meet]

lemma meet_singleton (values : List Bool) (i : ℕ) :
    meet values [i] = values.getD i false := by
  simp [meet]

lemma meet_congr {a b : List Bool} {atoms : List ℕ}
    (h : ∀ i ∈ atoms, a.getD i false = b.getD i false) : meet a atoms = meet b atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    change (a.getD i false && meet a atoms) = (b.getD i false && meet b atoms)
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma meet_extend (values suffix : List Bool) (atoms : List ℕ)
    (h : bounded values.length atoms) : meet (values ++ suffix) atoms = meet values atoms := by
  apply meet_congr
  intro i hi
  exact List.getD_append values suffix false i (h i hi)

lemma wires_length (program : List (List ℕ × List ℕ)) (x : List Bool) :
    (wires program x).length = x.length + program.length := by
  induction program generalizing x with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wires_append (program : List (List ℕ × List ℕ)) (g : List ℕ × List ℕ)
    (x : List Bool) : wires (program ++ [g]) x = step (wires program x) g := by
  simp [wires, List.foldl_append]

lemma original_wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma original_wires_append (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]


def Represents (n : ℕ) (gs : List Gate) (program : List (List ℕ × List ℕ))
    (reps : List (List ℕ)) : Prop :=
  wellFormed n program ∧ reps.length = n + gs.length ∧
  (∀ r ∈ reps, bounded (n + program.length) r) ∧
  ∀ x : List Bool, x.length = n →
    reps.map (meet (wires program x)) = Circuit.wires ⟨gs, 0⟩ x

lemma getD_mem {α : Type} (xs : List α) (d : α) {i : ℕ} (hi : i < xs.length) :
    xs.getD i d ∈ xs := by
  simp [hi]

lemma rep_value {values old : List Bool} {reps : List (List ℕ)} {i : ℕ}
    (hrep : reps.map (meet values) = old) (hi : i < reps.length) :
    meet values (reps.getD i []) = old.getD i false := by
  rw [← hrep]
  simp [hi]

lemma getD_snoc {α : Type} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma represents_nil (n : ℕ) :
    Represents n [] [] ((List.range n).map (fun i => [i])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp at hj
  · simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    intro j hj
    have : j = i := by simpa using hj
    subst j
    simpa using List.mem_range.mp hi
  · intro x hx
    simp only [wires, List.foldl_nil, List.map_map, Circuit.wires]
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hx'
      simp only [List.length_map, List.length_range] at hi
      simp [hx, hi, meet]

lemma represents_and {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.and, [a, b]⟩]) program
      (reps ++ [reps.getD a [] ++ reps.getD b []]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨hwf, ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hbound r hr
    · have heq : r = reps.getD a [] ++ reps.getD b [] := by simpa using hr
      subst r
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hbound _ (getD_mem reps [] ha) i hi
      · exact hbound _ (getD_mem reps [] hb) i hi
  · intro x hx
    rw [List.map_append]
    simp only [List.map_singleton, meet_append, original_wires_append]
    rw [hvalues x hx, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [GateOp.eval]


lemma wellFormed_append {n : ℕ} {program : List (List ℕ × List ℕ)}
    (hwf : wellFormed n program) (a b : List ℕ)
    (ha : bounded (n + program.length) a) (hb : bounded (n + program.length) b) :
    wellFormed n (program ++ [(a, b)]) := by
  intro j hj
  by_cases hlt : j < program.length
  · rw [List.getD_append program [(a, b)] ([], []) j hlt]
    exact hwf j hlt
  · have heq : j = program.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [getD_snoc]
    exact ⟨ha, hb⟩

lemma represents_or {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.or, [a, b]⟩])
      (program ++ [(reps.getD a [], reps.getD b [])])
      (reps ++ [[n + program.length]]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨wellFormed_append hwf _ _ (hbound _ (getD_mem reps [] ha))
    (hbound _ (getD_mem reps [] hb)), ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr i hi
    rcases List.mem_append.mp hr with hr | hr
    · have hbnd := hbound r hr i hi
      simp only [List.length_append, List.length_singleton]
      omega
    · have heq : r = [n + program.length] := by simpa using hr
      subst r
      have hieq : i = n + program.length := by simpa using hi
      simp [hieq]
  · intro x hx
    have hmaps : reps.map (meet (wires (program ++ [(reps.getD a [], reps.getD b [])]) x)) =
        reps.map (meet (wires program x)) := by
      apply List.map_congr_left
      intro r hr
      rw [wires_append]
      apply meet_extend
      simpa [wires_length, hx] using hbound r hr
    rw [List.map_append]
    simp only [List.map_singleton, meet_singleton]
    rw [hmaps, hvalues x hx, wires_append]
    change Circuit.wires ⟨gs, 0⟩ x ++
      [(wires program x ++ [meet (wires program x) (reps.getD a []) ||
        meet (wires program x) (reps.getD b [])]).getD (n + program.length) false] = _
    have hwlen : n + program.length = (wires program x).length := by simp [wires_length, hx]
    rw [hwlen, getD_snoc, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [original_wires_append, GateOp.eval]


def normalized (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b : ℕ,
    gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or)

theorem compile (n : ℕ) (gs : List Gate) (hnorm : normalized n gs) :
    ∃ program reps, Represents n gs program reps ∧ program.length = orCount gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    exact ⟨[], (List.range n).map (fun i => [i]), represents_nil n, rfl⟩
  | append_singleton gs g ih =>
    have hprefix : normalized n gs := by
      intro j hj
      obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm j (by simp; omega)
      exact ⟨a, b, by simpa [List.getElem_append_left hj] using hp, ha, hb,
        by simpa [List.getElem_append_left hj] using hop⟩
    obtain ⟨program, reps, hrep, hcount⟩ := ih hprefix
    obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm gs.length (by simp)
    have hlast : (gs ++ [g])[gs.length] = g := by simp
    rw [hlast] at hp hop
    have harep : a < reps.length := by rw [hrep.2.1]; exact ha
    have hbrep : b < reps.length := by rw [hrep.2.1]; exact hb
    rcases hop with hand | hor
    · have hg : g = ⟨GateOp.and, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program, reps ++ [reps.getD a [] ++ reps.getD b []],
        represents_and hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount
    · have hg : g = ⟨GateOp.or, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program ++ [(reps.getD a [], reps.getD b [])],
        reps ++ [[n + program.length]], represents_or hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount

theorem circuit_translation (n : ℕ) (C : Circuit) (hnorm : normalized n C.gates)
    (hout : C.output < n + C.gates.length) :
    ∃ program output, program.length = orCount C.gates ∧ wellFormed n program ∧
      bounded (n + program.length) output ∧
      ∀ x : List Bool, x.length = n → eval program output x = C.eval x := by
  obtain ⟨program, reps, hrep, hcount⟩ := compile n C.gates hnorm
  have ho : C.output < reps.length := by rw [hrep.2.1]; exact hout
  refine ⟨program, reps.getD C.output [], hcount, hrep.1,
    hrep.2.2.1 _ (getD_mem reps [] ho), ?_⟩
  intro x hx
  exact rep_value (hrep.2.2.2 x hx) ho


lemma meet_wires (program : List (List ℕ × List ℕ)) (x : List Bool) (atoms : List ℕ)
    (hbound : bounded x.length atoms) : meet (wires program x) atoms = meet x atoms := by
  induction program generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change meet (wires gs (step x g)) atoms = meet x atoms
    rw [ih]
    · exact meet_extend x _ atoms hbound
    · intro i hi
      have hb := hbound i hi
      simp only [step, List.length_append, List.length_singleton]
      omega

lemma eval_append (n : ℕ) (program suffix : List (List ℕ × List ℕ)) (output : List ℕ)
    (hbound : bounded (n + program.length) output) (x : List Bool) (hx : x.length = n) :
    eval (program ++ suffix) output x = eval program output x := by
  unfold eval
  have heq : wires (program ++ suffix) x = wires suffix (wires program x) := by
    simp [wires, List.foldl_append]
  rw [heq]
  apply meet_wires
  simpa [wires_length, hx] using hbound

theorem pad_by (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (extra : ℕ) :
    ∃ padded, padded.length = program.length + extra ∧ wellFormed n padded ∧
      bounded (n + padded.length) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  induction extra generalizing program with
  | zero => exact ⟨program, by simp, hwf, hbound, fun _ _ => rfl⟩
  | succ extra ih =>
    let next := program ++ [([0], [0])]
    have hzero : bounded (n + program.length) [0] := by
      intro i hi
      have : i = 0 := by simpa using hi
      omega
    have hnext : wellFormed n next := wellFormed_append hwf [0] [0] hzero hzero
    have hbnext : bounded (n + next.length) output := by
      intro i hi
      have hb := hbound i hi
      simp only [next, List.length_append, List.length_singleton]
      omega
    obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := ih next hnext hbnext
    refine ⟨padded, ?_, hpwf, hpbound, ?_⟩
    · simp only [next, List.length_append, List.length_singleton] at hlen
      omega
    · intro x hx
      exact (hpeval x hx).trans (eval_append n program [([0], [0])] output hbound x hx)

theorem pad_to (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (k : ℕ) (hk : program.length ≤ k) :
    ∃ padded, padded.length = k ∧ wellFormed n padded ∧ bounded (n + k) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := pad_by n program output hn hwf hbound (k - program.length)
  have heq : padded.length = k := by omega
  exact ⟨padded, heq, hpwf, heq ▸ hpbound, hpeval⟩



end PEqualNP.Outside.L_meta_1031_aux.CompactOr

namespace PEqualNP.Outside.L_meta_1031_aux.TwoChoiceRectangle

lemma factor_singleton {α : Type} [DecidableEq α] (A B C D : Finset α)
    (hAC : (A ∪ C).card = 2) (hAD : (A ∪ D).card = 2)
    (hBC : (B ∪ C).card = 2)
    (hrow : A ∪ C ≠ A ∪ D) (hcol : A ∪ C ≠ B ∪ C) :
    ∃ a, A = {a} := by
  have hle : A.card ≤ 2 := (Finset.card_le_card Finset.subset_union_left).trans_eq hAC
  have hzero : A.card ≠ 0 := by
    intro hz
    have he : A = ∅ := Finset.card_eq_zero.mp hz
    have hc : C.card = 2 := by simpa [he] using hAC
    have heq : C = B ∪ C := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    apply hcol
    simpa [he] using heq
  have htwo : A.card ≠ 2 := by
    intro ht
    have h1 : A = A ∪ C := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have h2 : A = A ∪ D := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    exact hrow (h1.symm.trans h2)
  exact Finset.card_eq_one.mp (by omega)

def HasEdge {α : Type} (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, G.Adj u v

lemma hasEdge_pair {α : Type} [DecidableEq α] (G : SimpleGraph α) (a b : α) :
    HasEdge G {a, b} ↔ G.Adj a b := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.ne_of_adj huv rfl).elim
    · exact huv
    · exact huv.symm
    · exact (G.ne_of_adj huv rfl).elim
  · intro hab
    exact ⟨a, by simp, b, by simp, hab⟩

lemma corners_repeat {α : Type} [DecidableEq α] (G : SimpleGraph α)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D : Finset α)
    (hAC : (A ∪ C).card = 2) (hAD : (A ∪ D).card = 2)
    (hBC : (B ∪ C).card = 2) (hBD : (B ∪ D).card = 2)
    (eAC : HasEdge G (A ∪ C)) (eAD : HasEdge G (A ∪ D))
    (eBC : HasEdge G (B ∪ C)) (eBD : HasEdge G (B ∪ D)) :
    A ∪ C = A ∪ D ∨ A ∪ C = B ∪ C ∨ B ∪ C = B ∪ D ∨ A ∪ D = B ∪ D := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨a, rfl⟩ := factor_singleton A B C D hAC hAD hBC hn.1 hn.2.1
  obtain ⟨b, rfl⟩ := factor_singleton B {a} C D hBC hBD hAC hn.2.2.1 (Ne.symm hn.2.1)
  obtain ⟨c, rfl⟩ := factor_singleton C D {a} {b}
    (by simpa [Finset.union_comm] using hAC)
    (by simpa [Finset.union_comm] using hBC)
    (by simpa [Finset.union_comm] using hAD)
    (by simpa [Finset.union_comm] using hn.2.1)
    (by simpa [Finset.union_comm] using hn.1)
  obtain ⟨d, rfl⟩ := factor_singleton D {c} {a} {b}
    (by simpa [Finset.union_comm] using hAD)
    (by simpa [Finset.union_comm] using hBD)
    (by simpa [Finset.union_comm] using hAC)
    (by simpa [Finset.union_comm] using hn.2.2.2)
    (by simpa [Finset.union_comm] using (Ne.symm hn.1))
  have hac : G.Adj a c := (hasEdge_pair G a c).mp (by simpa using eAC)
  have had : G.Adj a d := (hasEdge_pair G a d).mp (by simpa using eAD)
  have hbc : G.Adj b c := (hasEdge_pair G b c).mp (by simpa using eBC)
  have hbd : G.Adj b d := (hasEdge_pair G b d).mp (by simpa using eBD)
  rcases hfour a c b d hac hbc.symm hbd had.symm with hab | hcd
  · subst b
    exact hn.2.1 rfl
  · subst d
    exact hn.1 rfl


noncomputable def edgeCorners {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (A B C D : Finset α) : Finset (Finset α) := by
  classical
  exact ({A ∪ C, A ∪ D, B ∪ C, B ∪ D} : Finset (Finset α)).filter (fun S => S.card = 2 ∧ HasEdge G S)

lemma edgeCorners_card_le_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) (A B C D : Finset α) :
    (edgeCorners G A B C D).card ≤ 3 := by
  classical
  let corners : Finset (Finset α) := {A ∪ C, A ∪ D, B ∪ C, B ∪ D}
  have hsub : edgeCorners G A B C D ⊆ corners := Finset.filter_subset _ _
  have hcard : corners.card ≤ 4 := Finset.card_le_four
  by_contra hn
  have heq : edgeCorners G A B C D = corners :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hp (S : Finset α) (hS : S ∈ corners) : S.card = 2 ∧ HasEdge G S := by
    rw [← heq] at hS
    exact (Finset.mem_filter.mp hS).2
  have hAC := hp (A ∪ C) (by simp [corners])
  have hAD := hp (A ∪ D) (by simp [corners])
  have hBC := hp (B ∪ C) (by simp [corners])
  have hBD := hp (B ∪ D) (by simp [corners])
  have hsmall : corners.card ≤ 3 := by
    rcases corners_repeat G hfour A B C D hAC.1 hAD.1 hBC.1 hBD.1
      hAC.2 hAD.2 hBC.2 hBD.2 with h | h | h | h
    · simpa [corners, h] using (Finset.card_le_three (a := A ∪ D) (b := B ∪ C) (c := B ∪ D))
    · have hs : corners ⊆ {A ∪ D, B ∪ C, B ∪ D} := by
        intro S hS
        simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hS ⊢
        rcases hS with rfl | rfl | rfl | rfl <;> simp_all
      exact (Finset.card_le_card hs).trans Finset.card_le_three
    · simpa [corners, h] using (Finset.card_le_three (a := A ∪ C) (b := A ∪ D) (c := B ∪ D))
    · have hs : corners ⊆ {A ∪ C, B ∪ C, B ∪ D} := by
        intro S hS
        simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hS ⊢
        rcases hS with rfl | rfl | rfl | rfl <;> simp_all
      exact (Finset.card_le_card hs).trans Finset.card_le_three
  rw [← heq] at hsmall
  exact hn hsmall


lemma HasEdge.card_ge_two {α : Type} [DecidableEq α] {G : SimpleGraph α}
    {S : Finset α} (h : HasEdge G S) : 2 ≤ S.card := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  have hpair : ({u, v} : Finset α).card = 2 := by simp [G.ne_of_adj huv]
  have hsub : ({u, v} : Finset α) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  rw [← hpair]
  exact Finset.card_le_card hsub

lemma two_choices_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D : Finset α) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, (A ⊆ S ∨ B ⊆ S) ∧ (C ⊆ S ∨ D ⊆ S))
    (hsound : ∀ S : Finset α, (A ⊆ S ∨ B ⊆ S) → (C ⊆ S ∨ D ⊆ S) →
      HasEdge G S) : E.card ≤ 3 := by
  classical
  have hsub : E ⊆ edgeCorners G A B C D := by
    intro S hS
    obtain ⟨hl, hr⟩ := haccept S hS
    have hcorner : ∃ T ∈ ({A ∪ C, A ∪ D, B ∪ C, B ∪ D} : Finset (Finset α)),
        T ⊆ S ∧ HasEdge G T := by
      rcases hl with hA | hB <;> rcases hr with hC | hD
      · exact ⟨A ∪ C, by simp, Finset.union_subset hA hC,
          hsound _ (Or.inl Finset.subset_union_left) (Or.inl Finset.subset_union_right)⟩
      · exact ⟨A ∪ D, by simp, Finset.union_subset hA hD,
          hsound _ (Or.inl Finset.subset_union_left) (Or.inr Finset.subset_union_right)⟩
      · exact ⟨B ∪ C, by simp, Finset.union_subset hB hC,
          hsound _ (Or.inr Finset.subset_union_left) (Or.inl Finset.subset_union_right)⟩
      · exact ⟨B ∪ D, by simp, Finset.union_subset hB hD,
          hsound _ (Or.inr Finset.subset_union_left) (Or.inr Finset.subset_union_right)⟩
    obtain ⟨T, hT, hTS, hEdge⟩ := hcorner
    have hEq : T = S := Finset.eq_of_subset_of_card_le hTS (by
      have := hEdge.card_ge_two
      have := hcard S hS
      omega)
    subst T
    exact Finset.mem_filter.mpr ⟨hT, hcard S hS, hEdge⟩
  exact (Finset.card_le_card hsub).trans (edgeCorners_card_le_three G hfour A B C D)


lemma three_monomials_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    (A B C : Finset α) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, A ⊆ S ∨ B ⊆ S ∨ C ⊆ S)
    (hsound : ∀ S : Finset α, (A ⊆ S ∨ B ⊆ S ∨ C ⊆ S) → HasEdge G S) :
    E.card ≤ 3 := by
  have hsub : E ⊆ {A, B, C} := by
    intro S hS
    have hEq (T : Finset α) (hTS : T ⊆ S) (hEdge : HasEdge G T) : T = S :=
      Finset.eq_of_subset_of_card_le hTS (by
        have := hEdge.card_ge_two
        have := hcard S hS
        omega)
    rcases haccept S hS with hA | hB | hC
    · have he := hEq A hA (hsound A (Or.inl Finset.Subset.rfl))
      simp [← he]
    · have he := hEq B hB (hsound B (Or.inr (Or.inl Finset.Subset.rfl)))
      simp [← he]
    · have he := hEq C hC (hsound C (Or.inr (Or.inr Finset.Subset.rfl)))
      simp [← he]
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

def pattern {α : Type} [DecidableEq α] (A B C D K : Finset α)
    (p q r u : Prop) (S : Finset α) : Prop :=
  K ⊆ S ∧ (r → A ⊆ S ∨ B ⊆ S) ∧
    (u → ((C ⊆ S ∧ (p → A ⊆ S ∨ B ⊆ S)) ∨
      (D ⊆ S ∧ (q → A ⊆ S ∨ B ⊆ S))))

lemma two_or_pattern_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D K : Finset α) (p q r u : Prop) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, pattern A B C D K p q r u S)
    (hsound : ∀ S : Finset α, pattern A B C D K p q r u S → HasEdge G S) :
    E.card ≤ 3 := by
  classical
  by_cases hu : u
  · by_cases hr : r
    · apply two_choices_at_most_three G hfour (K ∪ A) (K ∪ B) C D E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, true_implies, Finset.union_subset_iff] at h ⊢
        aesop
      · intro S hl hrS
        apply hsound S
        simp only [pattern, hr, hu, true_implies, Finset.union_subset_iff] at hl ⊢
        aesop
    · by_cases hp : p
      · by_cases hq : q
        · apply two_choices_at_most_three G hfour (K ∪ A) (K ∪ B) C D E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S hl hrS
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies,
              Finset.union_subset_iff] at hl ⊢
            aesop
        · apply three_monomials_at_most_three G ((K ∪ A) ∪ C) ((K ∪ B) ∪ C) (K ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
      · by_cases hq : q
        · apply three_monomials_at_most_three G (K ∪ C) ((K ∪ A) ∪ D) ((K ∪ B) ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
        · apply three_monomials_at_most_three G (K ∪ C) (K ∪ D) (K ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
  · by_cases hr : r
    · apply three_monomials_at_most_three G (K ∪ A) (K ∪ B) (K ∪ B) E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, true_implies, false_implies, and_true,
          Finset.union_subset_iff] at h ⊢
        aesop
      · intro S h
        apply hsound S
        simp only [pattern, hr, hu, true_implies, false_implies, and_true,
          Finset.union_subset_iff] at h ⊢
        aesop
    · apply three_monomials_at_most_three G K K K E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, false_implies, and_true] at h
        exact Or.inl h
      · intro S h
        apply hsound S
        simpa only [pattern, hr, hu, false_implies, and_true, or_self] using h

end PEqualNP.Outside.L_meta_1031_aux.TwoChoiceRectangle


namespace PEqualNP.Outside.L_meta_1031_aux.TwoOrBridge

open TwoChoiceRectangle

def support (n : ℕ) (atoms : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ atoms)

def input (n : ℕ) (S : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ S))

def meet (values : List Bool) (atoms : List ℕ) : Bool :=
  atoms.all (fun i => values.getD i false)

def bounded (n : ℕ) (atoms : List ℕ) : Prop := ∀ i ∈ atoms, i < n

lemma input_length (n : ℕ) (S : Finset (Fin n)) : (input n S).length = n := by
  simp [input]

lemma input_get (n : ℕ) (S : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (input n S).getD i false = decide ((⟨i, hi⟩ : Fin n) ∈ S) := by
  simp [input, hi]

lemma support_subset (n : ℕ) (atoms : List ℕ) (S : Finset (Fin n)) :
    support n atoms ⊆ S ↔ ∀ i : Fin n, i.val ∈ atoms → i ∈ S := by
  simp only [support, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]

lemma meet_input (n : ℕ) (atoms : List ℕ) (hb : bounded n atoms) (S : Finset (Fin n)) :
    meet (input n S) atoms = true ↔ support n atoms ⊆ S := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    have hv := h i.val hi
    rw [input_get n S i.val i.isLt] at hv
    exact of_decide_eq_true hv
  · intro h i hi
    rw [input_get n S i (hb i hi)]
    exact decide_eq_true (h ⟨i, hb i hi⟩ hi)

lemma meet_append_one (n : ℕ) (atoms : List ℕ) (hb : bounded (n + 1) atoms)
    (S : Finset (Fin n)) (v : Bool) :
    meet (input n S ++ [v]) atoms = true ↔
      support n atoms ⊆ S ∧ (n ∈ atoms → v = true) := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h
    constructor
    · intro i hi
      have hv := h i.val hi
      rw [List.getD_append _ _ _ _ (by simp [input_length]),
        input_get n S i.val i.isLt] at hv
      exact of_decide_eq_true hv
    · intro hn
      have hv := h n hn
      simpa [List.getD_eq_getElem?_getD, input_length] using hv
  · rintro ⟨hS, hv⟩ i hi
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by simpa [input_length] using hin), input_get n S i hin]
      exact decide_eq_true (hS ⟨i, hin⟩ hi)
    · have heq : i = n := by have := hb i hi; omega
      subst i
      simpa [List.getD_eq_getElem?_getD, input_length] using hv hi

lemma meet_append_two (n : ℕ) (atoms : List ℕ) (hb : bounded (n + 2) atoms)
    (S : Finset (Fin n)) (v w : Bool) :
    meet (input n S ++ [v] ++ [w]) atoms = true ↔
      support n atoms ⊆ S ∧ (n ∈ atoms → v = true) ∧ (n + 1 ∈ atoms → w = true) := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h
    constructor
    · intro i hi
      have hv := h i.val hi
      rw [List.getD_append _ _ _ _ (by
          simpa only [List.length_append, List.length_singleton, input_length]
            using Nat.lt_succ_of_lt i.isLt),
        List.getD_append _ _ _ _ (by simp [input_length]),
        input_get n S i.val i.isLt] at hv
      exact of_decide_eq_true hv
    · constructor
      · intro hn
        have hv := h n hn
        simpa [List.getD_eq_getElem?_getD, input_length] using hv
      · intro hn
        have hv := h (n + 1) hn
        simpa [List.getD_eq_getElem?_getD, input_length] using hv
  · rintro ⟨hS, hv, hw⟩ i hi
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by
          simpa only [List.length_append, List.length_singleton, input_length]
            using Nat.lt_succ_of_lt hin),
        List.getD_append _ _ _ _ (by simpa [input_length] using hin), input_get n S i hin]
      exact decide_eq_true (hS ⟨i, hin⟩ hi)
    · have heq : i = n ∨ i = n + 1 := by have := hb i hi; omega
      rcases heq with rfl | rfl
      · simpa [List.getD_eq_getElem?_getD, input_length] using hv hi
      · simpa [List.getD_eq_getElem?_getD, input_length] using hw hi


def evalTwo (a b c d out : List ℕ) (x : List Bool) : Bool :=
  let v := meet x a || meet x b
  let w := meet (x ++ [v]) c || meet (x ++ [v]) d
  meet (x ++ [v] ++ [w]) out

lemma evalTwo_pattern (n : ℕ) (a b c d out : List ℕ)
    (ha : bounded n a) (hb : bounded n b)
    (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (hout : bounded (n + 2) out) (S : Finset (Fin n)) :
    evalTwo a b c d out (input n S) = true ↔
      pattern (support n a) (support n b) (support n c) (support n d) (support n out)
        (n ∈ c) (n ∈ d) (n ∈ out) (n + 1 ∈ out) S := by
  let v := meet (input n S) a || meet (input n S) b
  let w := meet (input n S ++ [v]) c || meet (input n S ++ [v]) d
  have hv : v = true ↔ support n a ⊆ S ∨ support n b ⊆ S := by
    simp only [v, Bool.or_eq_true, meet_input n a ha S, meet_input n b hb S]
  have hw : w = true ↔
      (support n c ⊆ S ∧ (n ∈ c → support n a ⊆ S ∨ support n b ⊆ S)) ∨
      (support n d ⊆ S ∧ (n ∈ d → support n a ⊆ S ∨ support n b ⊆ S)) := by
    simp only [w, Bool.or_eq_true, meet_append_one n c hc S v, meet_append_one n d hd S v, hv]
  change meet (input n S ++ [v] ++ [w]) out = true ↔ _
  rw [meet_append_two n out hout S v w]
  simp only [pattern, hv, hw]

theorem two_or_program_at_most_three (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d out : List ℕ)
    (ha : bounded n a) (hb : bounded n b)
    (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (hout : bounded (n + 2) out) (E : Finset (Finset (Fin n)))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, evalTwo a b c d out (input n S) = true)
    (hsound : ∀ S : Finset (Fin n), evalTwo a b c d out (input n S) = true → HasEdge G S) :
    E.card ≤ 3 := by
  apply two_or_pattern_at_most_three G hfour
    (support n a) (support n b) (support n c) (support n d) (support n out)
    (n ∈ c) (n ∈ d) (n ∈ out) (n + 1 ∈ out) E hcard
  · intro S hS
    exact (evalTwo_pattern n a b c d out ha hb hc hd hout S).mp (haccept S hS)
  · intro S hp
    exact hsound S ((evalTwo_pattern n a b c d out ha hb hc hd hout S).mpr hp)

end PEqualNP.Outside.L_meta_1031_aux.TwoOrBridge

namespace PEqualNP.Outside.L_meta_1031_aux.GeneralOrLower

open PEqualNP.CircuitLowerBounds
open TwoChoiceRectangle TwoOrBridge

lemma list_two {α : Type} (xs : List α) (h : xs.length = 2) :
    ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      have he : xs = [] := by
        cases xs with
        | nil => rfl
        | cons c xs => simp at h
      exact ⟨a, b, by simp [he]⟩

theorem circuit_or_ge_three (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (C : Circuit) (hnorm : CompactOr.normalized n C.gates)
    (hout : C.output < n + C.gates.length) (E : Finset (Finset (Fin n)))
    (hE : 4 ≤ E.card) (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, C.eval (input n S) = true)
    (hsound : ∀ S : Finset (Fin n), C.eval (input n S) = true → HasEdge G S) :
    3 ≤ CompactOr.orCount C.gates := by
  by_contra hlt
  have hcount : CompactOr.orCount C.gates ≤ 2 := by omega
  obtain ⟨program, out, hlen, hwf, hbound, heval⟩ :=
    CompactOr.circuit_translation n C hnorm hout
  obtain ⟨padded, hpadlen, hpadwf, hpadbound, hpadeval⟩ :=
    CompactOr.pad_to n program out hn hwf hbound 2 (by omega)
  obtain ⟨⟨a,b⟩, ⟨c,d⟩, hpad⟩ := list_two padded hpadlen
  subst padded
  have ha : bounded n a ∧ bounded n b := by simpa [bounded, CompactOr.bounded] using hpadwf 0 (by simp)
  have hc : bounded (n + 1) c ∧ bounded (n + 1) d := by
    simpa [bounded, CompactOr.bounded] using hpadwf 1 (by simp)
  have hev (S : Finset (Fin n)) : evalTwo a b c d out (input n S) = C.eval (input n S) := by
    change CompactOr.eval [(a,b),(c,d)] out (input n S) = _
    exact (hpadeval _ (input_length n S)).trans (heval _ (input_length n S))
  have hsmall := two_or_program_at_most_three n G hfour a b c d out
    ha.1 ha.2 hc.1 hc.2 hpadbound E hcard
    (fun S hS => by rw [hev]; exact haccept S hS)
    (fun S hS => hsound S (by rwa [hev] at hS))
  omega

end PEqualNP.Outside.L_meta_1031_aux.GeneralOrLower
