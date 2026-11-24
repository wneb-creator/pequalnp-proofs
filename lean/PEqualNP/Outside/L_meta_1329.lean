import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1329_aux

def readers (G : Finset ℕ) (parents : ℕ → Finset ℕ) (x : ℕ) : Finset ℕ :=
  G.filter fun g => x ∈ parents g

private lemma count_edges (A B : Finset ℕ) (parents : ℕ → Finset ℕ) :
    (∑ x ∈ A, (readers B parents x).card) = ∑ g ∈ B, (A ∩ parents g).card := by
  classical
  simp only [readers, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  exact Finset.sum_comm

theorem count_bound (X G O : Finset ℕ) (parents : ℕ → Finset ℕ)
    (disj : Disjoint X G) (arity : ∀ g ∈ G, (parents g).card ≤ 2)
    (rawLive : ∀ x ∈ X, (readers G parents x).Nonempty)
    (sink : ∀ g ∈ G, readers G parents g = ∅ → g ∈ O)
    (single : ∀ x ∈ X, ∀ g, readers G parents x = {g} →
      (∀ y ∈ X, y ∈ parents g → y = x) ∧ (readers G parents g).Nonempty ∧
      (∀ h, readers G parents g = {h} → Disjoint (parents h) X)) :
    4 * X.card ≤ 3 * G.card + O.card := by
  classical
  let S := X.filter fun x => (readers G parents x).card = 1
  let B := G.filter fun g => X ∩ parents g = ∅
  have subS : S ⊆ X := Finset.filter_subset _ _
  have inB (g : ℕ) (hg : g ∈ G) : g ∈ B ↔ X ∩ parents g = ∅ := by simp [B, hg]
  have Ssum : (∑ g ∈ G, (S ∩ parents g).card) = S.card := by
    rw [← count_edges]
    calc
      _ = ∑ _x ∈ S, 1 := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
      _ = _ := by simp
  have Bsum : (∑ g ∈ G, if X ∩ parents g = ∅ then 1 else 0) = B.card :=
    (Finset.card_filter _ _).symm
  have Osum : (∑ g ∈ G, if g ∈ O then 1 else 0) ≤ O.card := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card fun g hg => (Finset.mem_filter.mp hg).2
  have lowRaw : 2 * X.card ≤ (∑ g ∈ G, (X ∩ parents g).card) + S.card := by
    have hp (x : ℕ) (hx : x ∈ X) : 2 ≤ (readers G parents x).card +
        (if (readers G parents x).card = 1 then 1 else 0) := by
      have pos := Finset.card_pos.mpr (rawLive x hx)
      split <;> omega
    have ht := Finset.sum_le_sum hp
    simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, count_edges] at ht
    rw [← Finset.card_filter] at ht
    simpa [S, Nat.mul_comm] using ht
  have info (g : ℕ) (hg : g ∈ G) (hxg : (S ∩ parents g).Nonempty) :
      (X ∩ parents g).card = 1 ∧ (S ∩ parents g).card = 1 ∧
      (readers G parents g).Nonempty ∧
      (∀ h, readers G parents g = {h} → Disjoint (parents h) X) := by
    obtain ⟨x, hx⟩ := hxg
    obtain ⟨hs, hp⟩ := Finset.mem_inter.mp hx
    obtain ⟨hX, hd⟩ := Finset.mem_filter.mp hs
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hd
    have hgr : g ∈ readers G parents x := Finset.mem_filter.mpr ⟨hg, hp⟩
    rw [hk, Finset.mem_singleton] at hgr
    subst k
    obtain ⟨hy, hn, hh⟩ := single x hX g hk
    have eqX : X ∩ parents g = {x} := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_singleton]
      exact ⟨fun ⟨h1,h2⟩ => hy y h1 h2, fun he => he ▸ ⟨hX,hp⟩⟩
    have eqS : S ∩ parents g = {x} := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_singleton]
      exact ⟨fun ⟨h1,h2⟩ => hy y (subS h1) h2, fun he => he ▸ ⟨hs,hp⟩⟩
    exact ⟨by simp [eqX], by simp [eqS], hn, hh⟩
  have smallB : (∑ g ∈ G, (X ∩ parents g).card) + S.card + 2 * B.card ≤ 2 * G.card := by
    have hp (g : ℕ) (hg : g ∈ G) :
        (X ∩ parents g).card + (S ∩ parents g).card +
        2 * (if X ∩ parents g = ∅ then 1 else 0) ≤ 2 := by
      by_cases h : (S ∩ parents g).Nonempty
      · obtain ⟨x,s,_,_⟩ := info g hg h
        have hn : X ∩ parents g ≠ ∅ := by intro he; simp [he] at x
        simp [hn, x, s]
      · have he := Finset.not_nonempty_iff_eq_empty.mp h
        by_cases hx : X ∩ parents g = ∅
        · simp [he, hx]
        · simpa [he, hx] using (Finset.card_le_card Finset.inter_subset_right).trans (arity g hg)
    have ht := Finset.sum_le_sum hp
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Bsum, Ssum,
      Finset.sum_const, smul_eq_mul, Nat.mul_comm G.card 2] using ht
  have slots : (∑ g ∈ G, (X ∩ parents g).card) + (∑ g ∈ G, (G ∩ parents g).card)
      ≤ 2 * G.card := by
    have hp (g : ℕ) (hg : g ∈ G) : (X ∩ parents g).card + (G ∩ parents g).card ≤ 2 := by
      have hdis : Disjoint (X ∩ parents g) (G ∩ parents g) :=
        disj.mono Finset.inter_subset_left Finset.inter_subset_left
      rw [← Finset.card_union_of_disjoint hdis]
      exact (Finset.card_le_card (Finset.union_subset Finset.inter_subset_right
        Finset.inter_subset_right)).trans (arity g hg)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm G.card 2] using Finset.sum_le_sum hp
  have Bslots : (∑ g ∈ G, (readers B parents g).card) ≤ 2 * B.card := by
    rw [count_edges]
    have hp (g : ℕ) (hg : g ∈ B) : (G ∩ parents g).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans (arity g (Finset.mem_filter.mp hg).1)
    simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm B.card 2] using Finset.sum_le_sum hp
  have flows : S.card + G.card ≤ (∑ g ∈ G, (G ∩ parents g).card) + O.card + 2 * B.card := by
    have hp (g : ℕ) (hg : g ∈ G) : (S ∩ parents g).card + 1 ≤
        (readers G parents g).card + (if g ∈ O then 1 else 0) + (readers B parents g).card := by
      by_cases h : (S ∩ parents g).Nonempty
      · obtain ⟨_, hs, hn, hnext⟩ := info g hg h
        have pos := Finset.card_pos.mpr hn
        by_cases hd : (readers G parents g).card = 1
        · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hd
          have hjm : j ∈ readers G parents g := by simp [hj]
          obtain ⟨hjG,hgp⟩ := Finset.mem_filter.mp hjm
          have hdj := (hnext j hj).symm
          have hb : j ∈ B := (inB j hjG).mpr (Finset.disjoint_iff_inter_eq_empty.mp hdj)
          have posB := Finset.card_pos.mpr (show (readers B parents g).Nonempty from
            ⟨j,Finset.mem_filter.mpr ⟨hb,hgp⟩⟩)
          omega
        · omega
      · have hs := Finset.not_nonempty_iff_eq_empty.mp h
        simp only [hs, Finset.card_empty, Nat.zero_add]
        by_cases hn : (readers G parents g).Nonempty
        · have pos := Finset.card_pos.mpr hn
          omega
        · have hgO := sink g hg (Finset.not_nonempty_iff_eq_empty.mp hn)
          simp only [hgO, ↓reduceIte]
          omega
    have ht := Finset.sum_le_sum hp
    simp only [Finset.sum_add_distrib, Ssum, Finset.sum_const, smul_eq_mul,
      Nat.mul_one] at ht
    rw [count_edges G G parents] at ht
    omega
  omega

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireVal (C : Circuit) (n : ℕ) (U : Finset ℕ) (w : ℕ) : Bool :=
  (C.wires (List.ofFn fun i : Fin n => decide (i.val ∈ U))).getD w false

def wireGate (C : Circuit) (n g : ℕ) : Gate :=
  if h : n ≤ g ∧ g < n + C.gates.length then C.gates[g-n]'(by omega)
  else ⟨.or, []⟩

def wireParents (C : Circuit) (n g : ℕ) : Finset ℕ :=
  (wireGate C n g).inputs.toFinset.filter (· < g)

theorem wireParents_mem (C : Circuit) (n g p : ℕ) :
    p ∈ wireParents C n g ↔ p ∈ (wireGate C n g).inputs ∧ p < g := by
  simp [wireParents]

theorem wireParents_lt (C : Circuit) (n g p : ℕ) (hp : p ∈ wireParents C n g) :
    p < g := ((wireParents_mem C n g p).mp hp).2

private theorem wvGate_mem (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size) :
    wireGate C n g ∈ C.gates := by
  unfold Circuit.size at hg
  rw [wireGate, dite_eq_left ⟨hn,hg⟩]
  exact List.getElem_mem _

theorem wireGate_op (C : Circuit) (hMono : Monotone2 C) (n g : ℕ)
    (hn : n ≤ g) (hg : g < n + C.size) :
    (wireGate C n g).op = .and ∨ (wireGate C n g).op = .or := by
  exact (hMono _ (wvGate_mem C n g hn hg)).1

theorem wireParents_card (C : Circuit) (hMono : Monotone2 C) (n g : ℕ)
    (hn : n ≤ g) (hg : g < n + C.size) : (wireParents C n g).card ≤ 2 :=
  (Finset.card_filter_le _ _).trans
    (List.toFinset_card_le _ |>.trans (hMono _ (wvGate_mem C n g hn hg)).2)

private def wvRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wvRun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wvRun (g :: gs) x = wvRun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma wvRun_length (gs : List Gate) (x : List Bool) :
    (wvRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wvRun]
  | cons g gs ih => rw [wvRun_cons, ih]; simp; omega

private lemma wvRun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wvRun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wvRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma wvRun_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    wvRun gs x = wvRun (gs.drop j) (wvRun (gs.take j) x) := by
  simpa only [wvRun, List.foldl_append] using
    congrArg (fun l : List Gate => wvRun l x) (List.take_append_drop j gs).symm

theorem wireVal_raw (C : Circuit) (n : ℕ) (U : Finset ℕ) (w : ℕ) (hw : w < n) :
    wireVal C n U w = decide (w ∈ U) := by
  let x := List.ofFn fun i : Fin n => decide (i.val ∈ U)
  change (wvRun C.gates x).getD w false = _
  have hp : w < x.length := by simpa [x] using hw
  rw [wvRun_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp [x]

theorem wireVal_missing (C : Circuit) (n : ℕ) (U : Finset ℕ) (w : ℕ)
    (hw : n + C.size ≤ w) : wireVal C n U w = false := by
  let x := List.ofFn fun i : Fin n => decide (i.val ∈ U)
  change (wvRun C.gates x).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [wvRun_length, x, Circuit.size] using hw)

theorem wireVal_gate (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size)
    (U : Finset ℕ) : wireVal C n U g = (wireGate C n g).op.eval
      ((wireGate C n g).inputs.map fun p => if p < g then wireVal C n U p else false) := by
  let j := g - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let gate := C.gates[j]
  have he : wireGate C n g = gate := by
    unfold Circuit.size at hg
    rw [wireGate, dite_eq_left ⟨hn,hg⟩]
  let x := List.ofFn fun i : Fin n => decide (i.val ∈ U)
  let earlier := wvRun (C.gates.take j) x
  have plen : earlier.length = g := by
    simp [earlier, wvRun_length, x, Nat.min_eq_left hj.le, j]; omega
  have split : wvRun C.gates x = wvRun (gate :: C.gates.drop (j+1)) earlier := by
    rw [wvRun_split C.gates x j, List.drop_eq_getElem_cons hj]
  have read (p : ℕ) : earlier.getD p false = if p < g then wireVal C n U p else false := by
    by_cases hp : p < g
    · rw [ite_eq_left hp]
      change earlier.getD p false = (wvRun C.gates x).getD p false
      rw [split]
      exact (wvRun_getD _ earlier p (by simpa only [plen] using hp)).symm
    · rw [ite_eq_right hp]
      exact List.getD_eq_default _ _ (by omega)
  rw [he]
  change (wvRun C.gates x).getD g false = _
  rw (occs := [1]) [split]
  rw (occs := [1]) [wvRun_cons]
  rw [wvRun_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma wv_and (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size)
    (U : Finset ℕ) (hop : (wireGate C n g).op = .and) :
    wireVal C n U g = true ↔ ∀ p ∈ (wireGate C n g).inputs, p < g ∧ wireVal C n U p = true := by
  rw [wireVal_gate C n g hn hg U, hop]
  simp [GateOp.eval, List.all_map]

private lemma wv_or (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size)
    (U : Finset ℕ) (hop : (wireGate C n g).op = .or) :
    wireVal C n U g = true ↔ ∃ p ∈ wireParents C n g, wireVal C n U p = true := by
  rw [wireVal_gate C n g hn hg U, hop]
  simp [GateOp.eval, List.any_map, wireParents, and_assoc]

theorem wireVal_and_parent_false (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size)
    (U : Finset ℕ) (p : ℕ) (hp : p ∈ wireParents C n g)
    (hop : (wireGate C n g).op = .and) (hy : wireVal C n U p = false) :
    wireVal C n U g = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have hp' := ((wv_and C n g hn hg U hop).mp ht p ((wireParents_mem C n g p).mp hp).1).2
  simp [hy] at hp'

theorem wireVal_or_parent_true (C : Circuit) (n g : ℕ) (hn : n ≤ g) (hg : g < n + C.size)
    (U : Finset ℕ) (p : ℕ) (hp : p ∈ wireParents C n g)
    (hop : (wireGate C n g).op = .or) (hy : wireVal C n U p = true) :
    wireVal C n U g = true := (wv_or C n g hn hg U hop).mpr ⟨p,hp,hy⟩

theorem wireVal_parent_flip (C : Circuit) (hMono : Monotone2 C) (n g : ℕ)
    (hn : n ≤ g) (hg : g < n + C.size) (A B : Finset ℕ)
    (hA : wireVal C n A g = true) (hB : wireVal C n B g = false) :
    ∃ p ∈ wireParents C n g, wireVal C n A p = true ∧ wireVal C n B p = false := by
  rcases wireGate_op C hMono n g hn hg with hop | hop
  · have ha := (wv_and C n g hn hg A hop).mp hA
    have hb : ¬ ∀ p ∈ (wireGate C n g).inputs, p < g ∧ wireVal C n B p = true := by
      intro hall
      have := (wv_and C n g hn hg B hop).mpr hall
      simp [hB] at this
    push Not at hb
    obtain ⟨p,hp,hbad⟩ := hb
    obtain ⟨hlt,hat⟩ := ha p hp
    refine ⟨p, (wireParents_mem C n g p).mpr ⟨hp,hlt⟩, hat, ?_⟩
    by_cases hbt : wireVal C n B p = true <;> simp_all
  · obtain ⟨p,hp,ha⟩ := (wv_or C n g hn hg A hop).mp hA
    refine ⟨p,hp,ha,?_⟩
    apply Bool.eq_false_iff.mpr
    intro ht
    have := wireVal_or_parent_true C n g hn hg B p hp hop ht
    simp [hB] at this

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

private def liveLink (allG : Finset ℕ) (parents : ℕ → Finset ℕ) (p g : ℕ) : Prop :=
  g ∈ allG ∧ p ∈ parents g

noncomputable def liveSet (allG O : Finset ℕ) (parents : ℕ → Finset ℕ) : Finset ℕ := by
  classical
  exact allG.filter fun g => ∃ o ∈ O, Relation.ReflTransGen (liveLink allG parents) g o

private lemma liveSet_spec {allG O : Finset ℕ} {parents : ℕ → Finset ℕ} {g : ℕ} :
    g ∈ liveSet allG O parents ↔
      g ∈ allG ∧ ∃ o ∈ O, Relation.ReflTransGen (liveLink allG parents) g o := by
  classical
  exact Finset.mem_filter

lemma liveSet_subset (allG O : Finset ℕ) (parents : ℕ → Finset ℕ) :
    liveSet allG O parents ⊆ allG := fun _ hg => (liveSet_spec.mp hg).1

lemma liveSet_output {allG O : Finset ℕ} {parents : ℕ → Finset ℕ} {g : ℕ}
    (hg : g ∈ allG) (ho : g ∈ O) : g ∈ liveSet allG O parents :=
  liveSet_spec.mpr ⟨hg, g, ho, .refl⟩

lemma liveSet_parent {allG O : Finset ℕ} {parents : ℕ → Finset ℕ} {g p : ℕ}
    (hg : g ∈ liveSet allG O parents) (hp : p ∈ parents g) (ha : p ∈ allG) :
    p ∈ liveSet allG O parents := by
  obtain ⟨hga, o, ho, hgo⟩ := liveSet_spec.mp hg
  exact liveSet_spec.mpr ⟨ha, o, ho, hgo.head ⟨hga, hp⟩⟩

lemma liveSet_successor {allG O : Finset ℕ} {parents : ℕ → Finset ℕ} {g : ℕ}
    (hg : g ∈ liveSet allG O parents) (hn : g ∉ O) :
    ∃ h ∈ liveSet allG O parents, g ∈ parents h := by
  obtain ⟨_, o, ho, hgo⟩ := liveSet_spec.mp hg
  rcases hgo.cases_head with rfl | ⟨h, link, tail⟩
  · exact (hn ho).elim
  · exact ⟨h, liveSet_spec.mpr ⟨link.1, o, ho, tail⟩, link.2⟩

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

abbrev GeoVertex := Fin 162
abbrev GeoTile := Fin 27

def geoIncN (p l : ℕ) : Bool :=
  (p / 9 % 3 + (l / 3 % 3) * (p / 3 % 3)) % 3 == (l % 3 * (p % 3) + l / 9 % 3) % 3 &&
  p / 27 % 3 == (l % 3 * (p / 3 % 3) + l / 3 % 3 * (p % 3) + l / 27) % 3

def geoPivotN (t : GeoTile) (p : ℕ) : Bool :=
  (p / 9 % 3 + t.val/3 % 3 * (p/3 % 3)) % 3 == (t.val/3 % 3 * (t.val % 3)) % 3 &&
  p / 27 % 3 == (t.val/3 % 3 * (p % 3) + t.val/9) % 3

def geoTileN (p l : ℕ) :=
  p/3 % 3 + 3*(l/3 % 3) + 9*((l/27 + (p/3 % 3)*(l % 3)) % 3)

def geoRequiredPL (t : GeoTile) (p l : ℕ) : Bool :=
  geoIncN p l && !geoPivotN t p && (geoTileN p l == t.val)

def geoRequired (t : GeoTile) (u v : GeoVertex) : Bool :=
  if u.val < 81 ∧ 81 ≤ v.val then geoRequiredPL t u.val (v.val-81)
  else if v.val < 81 ∧ 81 ≤ u.val then geoRequiredPL t v.val (u.val-81) else false

def geoOff (t : GeoTile) (v : GeoVertex) : Bool :=
  if v.val < 81 then !geoPivotN t v.val else true

def geoPairEdge (u v : GeoVertex) : Bool :=
  if u.val < 81 ∧ 81 ≤ v.val then geoIncN u.val (v.val-81)
  else if v.val < 81 ∧ 81 ≤ u.val then geoIncN v.val (u.val-81) else false

def geoNegative (t : GeoTile) (u v : GeoVertex) : Bool :=
  geoOff t u && geoOff t v && !geoPairEdge u v

def geoActiveB (v : GeoVertex) : Bool :=
  if v.val < 81 then v.val / 9 % 3 != 0 else (v.val-81) % 27 != 0

def geoActive : Finset GeoVertex := Finset.univ.filter (fun x => geoActiveB x = true)

theorem geoActive_card : geoActive.card = 132 := by decide +kernel

abbrev GeoWitness := GeoTile × GeoVertex × GeoVertex × GeoVertex

private def geoRows : Array (List GeoWitness) := #[
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(0,91,19,83), (0,90,10,82)],
  [(0,82,20,92), (0,90,9,91)],
  [(0,83,19,91), (0,90,9,92)],
  [(1,119,23,99), (1,90,13,128)],
  [(1,128,21,99), (1,90,12,119)],
  [(1,110,22,99), (1,90,12,119)],
  [(2,118,25,99), (2,90,16,109)],
  [(2,109,26,99), (2,90,15,118)],
  [(2,127,24,99), (2,90,15,118)],
  [(0,100,11,83), (0,99,9,90)],
  [(0,83,11,90), (0,91,9,92)],
  [(0,82,10,90), (0,92,9,91)],
  [(1,128,13,90), (1,99,12,119)],
  [(1,110,14,90), (1,99,12,119)],
  [(1,119,12,90), (1,99,13,128)],
  [(2,127,17,90), (2,99,15,118)],
  [(2,118,15,90), (2,99,16,109)],
  [(2,109,16,90), (2,99,15,118)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(9,118,46,110), (9,117,37,109)],
  [(9,109,47,119), (9,117,36,118)],
  [(9,110,46,118), (9,117,36,119)],
  [(10,91,49,126), (10,117,40,82)],
  [(10,82,50,126), (10,117,39,91)],
  [(10,100,48,126), (10,117,39,91)],
  [(11,92,53,126), (11,117,43,101)],
  [(11,101,51,126), (11,117,42,92)],
  [(11,83,52,126), (11,117,42,92)],
  [(9,127,38,110), (9,126,36,117)],
  [(9,110,38,117), (9,118,36,119)],
  [(9,109,37,117), (9,119,36,118)],
  [(10,100,41,117), (10,126,39,91)],
  [(10,91,39,117), (10,126,40,82)],
  [(10,82,40,117), (10,126,39,91)],
  [(11,101,43,117), (11,126,42,92)],
  [(11,83,44,117), (11,126,42,92)],
  [(11,92,42,117), (11,126,43,101)],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [(18,145,73,137), (18,144,64,136)],
  [(18,136,74,146), (18,144,63,145)],
  [(18,137,73,145), (18,144,63,146)],
  [(19,92,77,109), (19,118,67,101)],
  [(19,101,75,127), (19,109,66,92)],
  [(19,83,76,118), (19,127,66,92)],
  [(20,91,79,110), (20,119,70,82)],
  [(20,82,80,119), (20,128,69,91)],
  [(20,100,78,128), (20,110,69,91)],
  [(18,154,65,137), (18,153,63,144)],
  [(18,137,65,144), (18,145,63,146)],
  [(18,136,64,144), (18,146,63,145)],
  [(19,101,67,109), (19,127,66,92)],
  [(19,83,68,127), (19,118,66,92)],
  [(19,92,66,118), (19,109,67,101)],
  [(20,100,71,110), (20,128,69,91)],
  [(20,91,69,119), (20,110,70,82)],
  [(20,82,70,128), (20,119,69,91)],
  [],
  [(0,10,9,90), (0,20,11,83)],
  [(0,11,9,90), (0,19,10,82)],
  [(4,21,40,113), (5,15,43,130), (4,21,12,102)],
  [(3,37,9,93), (13,14,23,94)],
  [(3,46,9,94), (14,26,17,104)],
  [(7,12,50,116), (8,24,53,124), (7,12,21,96)],
  [(6,47,9,98), (16,22,13,106)],
  [(6,38,9,96), (17,16,25,98)],
  [(0,9,19,91), (0,10,11,83)],
  [(0,9,10,90), (0,19,11,83)],
  [(0,9,10,90), (0,20,11,83)],
  [(3,9,46,94), (5,24,52,112), (3,9,18,102)],
  [(3,9,37,93), (13,23,14,85)],
  [(3,9,37,93), (14,51,17,104)],
  [(6,9,47,98), (7,21,50,116), (6,9,18,105)],
  [(6,9,38,96), (16,48,13,106)],
  [(6,9,38,96), (17,25,16,89)],
  [(0,18,10,101), (0,19,9,90)],
  [(0,11,9,90), (0,18,10,82)],
  [(0,10,9,90), (0,18,11,83)],
  [(3,18,37,104), (4,12,40,113), (3,18,9,93)],
  [(3,18,37,104), (13,39,14,85)],
  [(3,18,46,102), (14,17,26,86)],
  [(6,18,38,106), (8,15,44,115), (6,18,9,96)],
  [(6,18,47,105), (16,13,22,88)],
  [(6,18,38,106), (17,42,16,89)],
  [],
  [(2,16,15,90), (2,26,17,127)],
  [(1,14,12,90), (1,22,13,128)],
  [(13,23,39,158), (14,17,42,86), (13,23,14,85)],
  [(5,15,43,84), (12,20,11,113)],
  [(4,21,49,84), (12,11,20,112)],
  [(16,13,48,152), (17,25,51,89), (16,13,22,88)],
  [(8,24,53,87), (15,10,19,116)],
  [(7,12,41,87), (15,19,10,115)],
  [(9,36,46,118), (9,37,38,110)],
  [(2,15,16,90), (2,25,17,127)],
  [(1,12,13,90), (1,23,14,110)],
  [(12,11,45,130), (14,26,51,95), (12,11,20,112)],
  [(5,24,43,149), (12,36,11,113)],
  [(4,49,12,157), (12,20,11,113)],
  [(15,10,45,134), (16,22,48,97), (15,10,19,116)],
  [(8,53,15,161), (15,19,10,115)],
  [(7,21,41,151), (15,36,10,115)],
  [(9,45,37,128), (9,46,36,117)],
  [(2,17,15,90), (2,24,16,109)],
  [(1,13,12,90), (1,21,14,110)],
  [(12,20,36,122), (13,14,39,103), (12,20,11,113)],
  [(5,43,15,84), (12,11,20,112)],
  [(4,12,40,102), (12,45,11,113)],
  [(15,19,36,124), (17,16,42,107), (15,19,10,115)],
  [(8,15,44,105), (15,45,10,115)],
  [(7,41,12,87), (15,10,19,116)],
  [],
  [(1,13,12,90), (1,23,14,110)],
  [(2,17,15,90), (2,25,16,109)],
  [(22,22,41,95), (23,16,44,94), (22,22,13,86)],
  [(4,21,40,113), (14,42,17,104)],
  [(5,15,43,84), (13,48,14,85)],
  [(25,14,49,107), (26,26,52,106), (25,14,23,89)],
  [(7,12,41,87), (17,51,16,89)],
  [(8,24,44,115), (16,39,13,106)],
  [(18,63,73,145), (18,64,65,137)],
  [(1,12,13,90), (1,22,14,110)],
  [(2,15,16,90), (2,26,17,127)],
  [(21,10,47,139), (23,25,53,103), (21,10,19,140)],
  [(4,40,12,102), (14,17,26,86)],
  [(5,24,52,93), (13,14,23,94)],
  [(24,11,46,143), (25,23,49,107), (24,11,20,142)],
  [(7,21,50,96), (17,16,25,98)],
  [(8,44,15,105), (16,13,22,88)],
  [(18,72,64,155), (18,73,63,144)],
  [(1,14,12,90), (1,21,13,128)],
  [(2,16,15,90), (2,24,17,127)],
  [(21,19,38,140), (22,13,41,95), (21,19,10,139)],
  [(4,12,40,102), (14,26,17,104)],
  [(5,52,15,112), (13,23,14,85)],
  [(24,20,37,142), (26,17,43,97), (24,20,11,143)],
  [(7,50,12,116), (17,25,16,89)],
  [(8,15,44,105), (16,22,13,106)]]
private def geoChoices (x : GeoVertex) := geoRows[x.val]?.getD []

private def geoValid (x y : GeoVertex) (w : GeoWitness) : Bool :=
  let (t,z,u,v) := w
  geoRequired t x z && geoRequired t u v && geoNegative t y z &&
    geoNegative t z z && geoNegative t x x && (z != y) &&
    (u != x) && (v != x) && (u != y) && (v != y) && (u != z) && (v != z)

private theorem geo_checked : ∀ x y : GeoVertex,
    geoActiveB x = true → geoActiveB y = true → x ≠ y →
    (geoChoices x).any (geoValid x y) = true := by
  decide +kernel

theorem geo_separate (x y : GeoVertex) (hx : x ∈ geoActive) (hy : y ∈ geoActive) (hxy : x ≠ y) :
    ∃ (t : GeoTile) (z u v : GeoVertex), geoRequired t x z = true ∧ geoRequired t u v = true ∧
      geoNegative t y z = true ∧ geoNegative t z z = true ∧ geoNegative t x x = true ∧ z ≠ y ∧
      u ≠ x ∧ v ≠ x ∧ u ≠ y ∧ v ≠ y ∧ u ≠ z ∧ v ≠ z := by
  obtain ⟨⟨t,z,u,v⟩,_,good⟩ := List.any_eq_true.mp
    (geo_checked x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy)
  exact ⟨t,z,u,v, by simpa only [geoValid, Bool.and_eq_true, bne_iff_ne, and_assoc] using good⟩

def geoInc (p l : Fin 81) : Prop := geoIncN p.val l.val = true

theorem geo_required_ne (t : GeoTile) (x z : GeoVertex) (req : geoRequired t x z = true) : x ≠ z := by
  rintro rfl
  simp [geoRequired, show ¬ (x.val < 81 ∧ 81 ≤ x.val) by omega] at req

theorem geo_pair_api (x y : GeoVertex) (hx : x ∈ geoActive) (hy : y ∈ geoActive) (hne : x ≠ y) :
    ∃ (t : GeoTile) (z u v : GeoVertex), x ≠ z ∧ z ≠ y ∧ geoRequired t x z = true ∧
      geoNegative t z z = true ∧ geoNegative t y z = true ∧ geoNegative t x x = true ∧
      geoRequired t u v = true ∧ x ∉ ({u,v} : Finset GeoVertex) := by
  obtain ⟨t,z,u,v,hxpos,huv,hneg,hz,hxneg,hzy,hux,hvx,_⟩ := geo_separate x y hx hy hne
  exact ⟨t,z,u,v,geo_required_ne t x z hxpos,hzy,hxpos,hz,hneg,hxneg,huv,
    by simp [Ne.symm hux, Ne.symm hvx]⟩

theorem geo_single_api (x : GeoVertex) (hx : x ∈ geoActive) :
    ∃ (t : GeoTile) (z u v : GeoVertex), x ≠ z ∧ geoRequired t x z = true ∧
      geoNegative t z z = true ∧ geoNegative t x x = true ∧ geoRequired t u v = true ∧
      x ∉ ({u,v} : Finset GeoVertex) := by
  have other : ∃ y ∈ geoActive, x ≠ y := by
    by_cases h : x = 9
    · exact ⟨10, by decide, h ▸ (by decide : (9 : GeoVertex) ≠ 10)⟩
    · exact ⟨9, by decide, h⟩
  obtain ⟨y,hy,hne⟩ := other
  obtain ⟨t,z,u,v,hxz,_,hp,hz,_,hx0,hw,hm⟩ := geo_pair_api x y hx hy hne
  exact ⟨t,z,u,v,hxz,hp,hz,hx0,hw,hm⟩

def geoPiv (a m g : ZMod 3) (p : Fin 81) : Prop :=
  (((p.val / 9 % 3 : ℕ) : ZMod 3) + m * ((p.val / 3 % 3 : ℕ) : ZMod 3) = m * a ∧
   ((p.val / 27 : ℕ) : ZMod 3) = m * ((p.val % 3 : ℕ) : ZMod 3) + g)

theorem geoInc_desk (p l : Fin 81) : geoInc p l ↔
    (((p.val / 9 % 3 : ℕ) : ZMod 3) + ((l.val / 3 % 3 : ℕ) : ZMod 3) * ((p.val / 3 % 3 : ℕ) : ZMod 3) =
      ((l.val % 3 : ℕ) : ZMod 3) * ((p.val % 3 : ℕ) : ZMod 3) + ((l.val / 9 % 3 : ℕ) : ZMod 3) ∧
    ((p.val / 27 : ℕ) : ZMod 3) = ((l.val % 3 : ℕ) : ZMod 3) * ((p.val / 3 % 3 : ℕ) : ZMod 3) +
      ((l.val / 3 % 3 : ℕ) : ZMod 3) * ((p.val % 3 : ℕ) : ZMod 3) + ((l.val / 27 : ℕ) : ZMod 3)) := by
  revert p l
  unfold geoInc
  decide +kernel

def geoA (t : GeoTile) : ZMod 3 := (t.val % 3 : ℕ)
def geoM (t : GeoTile) : ZMod 3 := (t.val/3 % 3 : ℕ)
def geoG (t : GeoTile) : ZMod 3 := (t.val/9 : ℕ)

theorem geoPiv_desk (t : GeoTile) (p : Fin 81) :
    geoPiv (geoA t) (geoM t) (geoG t) p ↔ geoPivotN t p.val = true := by
  revert t p
  unfold geoPiv
  decide +kernel

theorem geoTag_desk (t : GeoTile) (p l : Fin 81) (ht : geoTileN p.val l.val = t.val) :
    geoA t = ((p.val/3 % 3 : ℕ) : ZMod 3) ∧ geoM t = ((l.val/3 % 3 : ℕ) : ZMod 3) ∧
    geoG t = ((l.val/27 : ℕ) : ZMod 3) + ((p.val/3 % 3 : ℕ) : ZMod 3) * ((l.val % 3 : ℕ) : ZMod 3) := by
  revert t
  revert p l
  decide +kernel

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

open PEqualNP.CircuitLowerBounds

private abbrev bridgeA (p : Fin 81) : ZMod 3 := ((p.val / 3 % 3 : ℕ) : ZMod 3)
private abbrev bridgeM (l : Fin 81) : ZMod 3 := ((l.val / 3 % 3 : ℕ) : ZMod 3)
private abbrev bridgeG (p l : Fin 81) : ZMod 3 :=
  ((l.val / 27 : ℕ) : ZMod 3) + bridgeA p * ((l.val % 3 : ℕ) : ZMod 3)

def BridgePositive (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) : Prop :=
  ∀ p l : Fin 81, inc p l → ¬ onPiv (bridgeA p) (bridgeM l) (bridgeG p l) p →
    (C.wires (List.ofFn (fun v : Fin (81 + 81) =>
      if v = Fin.castAdd 81 p then true else if v = Fin.natAdd 81 l then true else false))).getD
      (fg (bridgeA p) (bridgeM l) (bridgeG p l)) false = true

def BridgeSound (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) : Prop :=
  ∀ (a m g : ZMod 3) (zz : Fin (81 + 81) → Bool),
    (∀ p : Fin 81, onPiv a m g p → zz (Fin.castAdd 81 p) = false) →
    (C.wires (List.ofFn zz)).getD (fg a m g) false = true →
    ∃ p l : Fin 81, inc p l ∧ zz (Fin.castAdd 81 p) = true ∧ zz (Fin.natAdd 81 l) = true

def GeoChecks (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) : Prop :=
  (∀ (t : GeoTile) (x z : GeoVertex), geoRequired t x z = true →
    wireVal C 162 ({x.val,z.val} : Finset ℕ) (fg (geoA t) (geoM t) (geoG t)) = true) ∧
  (∀ (t : GeoTile) (x z : GeoVertex), geoNegative t x z = true →
    wireVal C 162 ({x.val,z.val} : Finset ℕ) (fg (geoA t) (geoM t) (geoG t)) = false)

private def bridgeRow (x z i : GeoVertex) : Bool :=
  decide (i.val ∈ ({x.val,z.val} : Finset ℕ))

private theorem bridgeRow_true (x z i : GeoVertex) :
    bridgeRow x z i = true ↔ i = x ∨ i = z := by
  simp [bridgeRow, Fin.ext_iff]

private theorem bridgeRow_ifs (x z : GeoVertex) :
    (fun i : GeoVertex => if i = x then true else if i = z then true else false) =
      bridgeRow x z := by
  funext i
  by_cases hx : i = x
  · have ht := (bridgeRow_true x z i).mpr (Or.inl hx)
    rw [ht, ite_eq_left hx]
  · by_cases hz : i = z
    · have ht := (bridgeRow_true x z i).mpr (Or.inr hz)
      rw [ht, ite_eq_right hx, ite_eq_left hz]
    · have ht : bridgeRow x z i = false := by
        cases h : bridgeRow x z i with
        | false => rfl
        | true => exact False.elim (((bridgeRow_true x z i).mp h).elim hx hz)
      rw [ht, ite_eq_right hx, ite_eq_right hz]

private theorem bridge_requiredForward
    (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (hinc : ∀ p l, inc p l ↔ geoInc p l)
    (hpiv : ∀ a m g p, onPiv a m g p ↔ geoPiv a m g p)
    (positive : BridgePositive inc onPiv C fg) (t : GeoTile) (x z : GeoVertex)
    (hx : x.val < 81) (hz : 81 ≤ z.val) (req : geoRequiredPL t x.val (z.val - 81) = true) :
    wireVal C 162 ({x.val,z.val} : Finset ℕ) (fg (geoA t) (geoM t) (geoG t)) = true := by
  let p : Fin 81 := ⟨x.val,hx⟩
  let l : Fin 81 := ⟨z.val-81, by have := z.isLt; omega⟩
  have hxp : Fin.castAdd 81 p = x := Fin.ext rfl
  have hzl : Fin.natAdd 81 l = z := Fin.ext (by simp [l]; omega)
  have req' : geoRequiredPL t p.val l.val = true := req
  simp only [geoRequiredPL, Bool.and_eq_true, beq_iff_eq] at req'
  obtain ⟨⟨hInc,hOff⟩,hTag⟩ := req'
  obtain ⟨ha,hm,hg⟩ := geoTag_desk t p l hTag
  have off : ¬ onPiv (geoA t) (geoM t) (geoG t) p := by
    intro ht
    have hon := (geoPiv_desk t p).mp ((hpiv _ _ _ p).mp ht)
    simp [hon] at hOff
  have hOff' : ¬ onPiv (bridgeA p) (bridgeM l) (bridgeG p l) p := by
    rw [ha,hm,hg] at off
    exact off
  have eval := positive p l ((hinc p l).mpr hInc) hOff'
  change (C.wires (List.ofFn (bridgeRow x z))).getD
    (fg (geoA t) (geoM t) (geoG t)) false = true
  rw [← bridgeRow_ifs x z, ha,hm,hg]
  simpa only [hxp,hzl] using eval

private theorem bridge_required
    (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (hinc : ∀ p l, inc p l ↔ geoInc p l)
    (hpiv : ∀ a m g p, onPiv a m g p ↔ geoPiv a m g p)
    (positive : BridgePositive inc onPiv C fg) (t : GeoTile) (x z : GeoVertex)
    (req : geoRequired t x z = true) :
    wireVal C 162 ({x.val,z.val} : Finset ℕ) (fg (geoA t) (geoM t) (geoG t)) = true := by
  by_cases left : x.val < 81 ∧ 81 ≤ z.val
  · apply bridge_requiredForward C fg inc onPiv hinc hpiv positive t x z left.1 left.2
    simpa only [geoRequired, ite_eq_left left] using req
  by_cases right : z.val < 81 ∧ 81 ≤ x.val
  · have rev := bridge_requiredForward C fg inc onPiv hinc hpiv positive t z x right.1 right.2
      (by simpa only [geoRequired, ite_eq_right left, ite_eq_left right] using req)
    have comm : ({x.val,z.val} : Finset ℕ) = {z.val,x.val} := by
      ext v
      simp [or_comm]
    rw [comm]
    exact rev
  · simp only [geoRequired, ite_eq_right left, ite_eq_right right, Bool.false_eq_true] at req

private theorem bridge_pivOff (t : GeoTile) (p : Fin 81)
    (hon : geoPiv (geoA t) (geoM t) (geoG t) p) :
    geoOff t (Fin.castAdd 81 p) ≠ true := by
  have h := (geoPiv_desk t p).mp hon
  simp [geoOff,h]

private theorem bridge_matchEdge (p l : Fin 81) (x z : GeoVertex)
    (hInc : geoInc p l) (pOn : bridgeRow x z (Fin.castAdd 81 p) = true)
    (lOn : bridgeRow x z (Fin.natAdd 81 l) = true) : geoPairEdge x z = true := by
  have hp : (Fin.castAdd 81 p).val < 81 := p.isLt
  have hl : 81 ≤ (Fin.natAdd 81 l).val := by simp
  have hf : ¬ ((Fin.natAdd 81 l).val < 81 ∧ 81 ≤ (Fin.castAdd 81 p).val) := by omega
  have hpl : Fin.castAdd 81 p ≠ Fin.natAdd 81 l := by
    intro h
    have e := congrArg Fin.val h
    omega
  rcases (bridgeRow_true x z _).mp pOn with hpx | hpz <;>
    rcases (bridgeRow_true x z _).mp lOn with hlx | hlz
  · exact False.elim (hpl (hpx.trans hlx.symm))
  · subst x
    subst z
    simpa [geoPairEdge,hp,hl,geoInc] using hInc
  · subst x
    subst z
    simpa [geoPairEdge,hf,hp,hl,geoInc] using hInc
  · exact False.elim (hpl (hpz.trans hlz.symm))

private theorem bridge_negative
    (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ) (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (hinc : ∀ p l, inc p l ↔ geoInc p l)
    (hpiv : ∀ a m g p, onPiv a m g p ↔ geoPiv a m g p)
    (sound : BridgeSound inc onPiv C fg) (t : GeoTile) (x z : GeoVertex)
    (neg : geoNegative t x z = true) :
    wireVal C 162 ({x.val,z.val} : Finset ℕ) (fg (geoA t) (geoM t) (geoG t)) = false := by
  simp only [geoNegative, Bool.and_eq_true] at neg
  obtain ⟨⟨hx,hz⟩,hnoEdge⟩ := neg
  have allOff (p : Fin 81) (hon : onPiv (geoA t) (geoM t) (geoG t) p) :
      bridgeRow x z (Fin.castAdd 81 p) = false := by
    cases e : bridgeRow x z (Fin.castAdd 81 p) with
    | false => rfl
    | true =>
      have hf := bridge_pivOff t p ((hpiv _ _ _ p).mp hon)
      rcases (bridgeRow_true x z _).mp e with q | q
      · exact False.elim (hf (q.symm ▸ hx))
      · exact False.elim (hf (q.symm ▸ hz))
  change (C.wires (List.ofFn (bridgeRow x z))).getD
    (fg (geoA t) (geoM t) (geoG t)) false = false
  cases e : (C.wires (List.ofFn (bridgeRow x z))).getD (fg (geoA t) (geoM t) (geoG t)) false with
  | false => rfl
  | true =>
    obtain ⟨p,l,hi,hp,hl⟩ := sound (geoA t) (geoM t) (geoG t) (bridgeRow x z) allOff e
    have edge := bridge_matchEdge p l x z ((hinc p l).mp hi) hp hl
    simp [edge] at hnoEdge

theorem bridge_geoChecks (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ)
    (inc : Fin 81 → Fin 81 → Prop)
    (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop)
    (hinc : ∀ p l, inc p l ↔ geoInc p l)
    (hpiv : ∀ a m g p, onPiv a m g p ↔ geoPiv a m g p)
    (positive : BridgePositive inc onPiv C fg) (sound : BridgeSound inc onPiv C fg) :
    GeoChecks C fg := by
  exact ⟨bridge_required C fg inc onPiv hinc hpiv positive,
    bridge_negative C fg inc onPiv hinc hpiv sound⟩

private def bridgeTileRows : Array (GeoVertex × GeoVertex × GeoVertex × GeoVertex) := #[
  (9, 90, 10, 82),
  (12, 90, 13, 128),
  (15, 90, 16, 109),
  (9, 93, 18, 102),
  (12, 102, 21, 84),
  (15, 84, 24, 93),
  (9, 96, 18, 105),
  (12, 87, 21, 96),
  (15, 105, 24, 87),
  (36, 117, 37, 109),
  (39, 91, 40, 82),
  (42, 92, 43, 101),
  (11, 113, 20, 112),
  (14, 85, 23, 94),
  (17, 104, 26, 86),
  (10, 115, 19, 116),
  (13, 106, 22, 88),
  (16, 89, 25, 98),
  (63, 144, 64, 136),
  (66, 92, 67, 101),
  (69, 91, 70, 82),
  (10, 139, 19, 140),
  (13, 86, 22, 95),
  (16, 103, 25, 85),
  (11, 143, 20, 142),
  (14, 107, 23, 89),
  (17, 88, 26, 97)]

private def bridgeTileRow (t : GeoTile) : GeoVertex × GeoVertex × GeoVertex × GeoVertex :=
  bridgeTileRows[t.val]?.getD (0,0,0,0)

private theorem bridgeTileRow_valid : ∀ t : GeoTile,
    let (x,z,u,v) := bridgeTileRow t
    geoRequired t x z = true ∧ geoRequired t u v = true ∧
    Disjoint ({x.val,z.val} : Finset ℕ) {u.val,v.val} := by
  decide +kernel

theorem bridge_output_bounds (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ)
    (checks : GeoChecks C fg) (t : GeoTile) :
    162 ≤ fg (geoA t) (geoM t) (geoG t) ∧ fg (geoA t) (geoM t) (geoG t) < 162 + C.size := by
  let w := fg (geoA t) (geoM t) (geoG t)
  rcases ht : bridgeTileRow t with ⟨x,z,u,v⟩
  have rows := bridgeTileRow_valid t
  rw [ht] at rows
  obtain ⟨hx,hu,hd⟩ := rows
  have ex := checks.1 t x z hx
  have eu := checks.1 t u v hu
  change 162 ≤ w ∧ w < 162+C.size
  constructor
  · by_contra! hw
    have xw := of_decide_eq_true ((wireVal_raw C 162 {x.val,z.val} w hw).symm.trans ex)
    have uw := of_decide_eq_true ((wireVal_raw C 162 {u.val,v.val} w hw).symm.trans eu)
    exact Finset.disjoint_left.mp hd xw uw
  · by_contra! hw
    have no := wireVal_missing C 162 {x.val,z.val} w hw
    exact Bool.false_ne_true (no.symm.trans ex)

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

private theorem drop_location (n x : ℕ) (G D : Finset ℕ) (P : ℕ → Finset ℕ)
    (E : Finset ℕ → ℕ → Bool) (A B : Finset ℕ)
    (earlier : ∀ g ∈ G, ∀ p ∈ P g, p < g)
    (closed : ∀ g ∈ G, ∀ p ∈ P g, n ≤ p → p ∈ G)
    (raw : ∀ T p, p < n → E T p = decide (p ∈ T))
    (flip : ∀ g ∈ G, ∀ T U, E T g = true → E U g = false →
      ∃ p ∈ P g, E T p = true ∧ E U p = false)
    (delta : ∀ p ∈ A, p ∉ B → p = x)
    (stop : ∀ k ∈ G, k ∉ D → ∀ p ∈ P k, (p = x ∨ p ∈ D) →
      ¬(E A k = true ∧ E B k = false)) :
    ∀ w ∈ G, E A w = true → E B w = false → w ∈ D := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ha hb
    by_contra hout
    obtain ⟨p, hp, hpa, hpb⟩ := flip w hw A B ha hb
    apply stop w hw hout p hp _ ⟨ha, hb⟩
    by_cases hpn : p < n
    · rw [raw A p hpn] at hpa
      rw [raw B p hpn] at hpb
      exact Or.inl (delta p (of_decide_eq_true hpa) (of_decide_eq_false hpb))
    · exact Or.inr (ih p (earlier w hw p hp) (closed w hw p hp (by omega)) hpa hpb)

private lemma diff_keep (x z p : ℕ) (ha : p ∈ ({x,z} : Finset ℕ))
    (hb : p ∉ ({z} : Finset ℕ)) : p = x := by
  exact (Finset.mem_insert.mp ha).resolve_right hb

private lemma diff_swap (x y z p : ℕ) (ha : p ∈ ({x,z} : Finset ℕ))
    (hb : p ∉ ({y,z} : Finset ℕ)) : p = x := by
  apply diff_keep x z p ha
  exact fun hp => hb (Finset.mem_insert_of_mem hp)

set_option maxHeartbeats 800000 in
theorem separation_conditions (n : ℕ) (X G O : Finset ℕ) (P : ℕ → Finset ℕ)
    (E : Finset ℕ → ℕ → Bool) (oG : O ⊆ G)
    (earlier : ∀ g ∈ G, ∀ p ∈ P g, p < g)
    (closed : ∀ g ∈ G, ∀ p ∈ P g, n ≤ p → p ∈ G)
    (raw : ∀ A p, p < n → E A p = decide (p ∈ A))
    (flip : ∀ g ∈ G, ∀ A B, E A g = true → E B g = false →
      ∃ p ∈ P g, E A p = true ∧ E B p = false)
    (blocks : ∀ g ∈ G, ∀ y ∈ X, y ∈ P g →
      (∀ A : Finset ℕ, y ∉ A → E A g = false) ∨
      (∀ B : Finset ℕ, y ∈ B → E B g = true))
    (other : ∀ x ∈ X, ∃ y ∈ X, y ≠ x)
    (tests : ∀ x ∈ X, ∀ y ∈ X, y ≠ x → ∃ o ∈ O, ∃ z u v : ℕ,
      x ≠ z ∧ z ≠ y ∧ E {x,z} o = true ∧ E {z} o = false ∧ E {y,z} o = false ∧
      E {x} o = false ∧ E {u,v} o = true ∧ x ∉ ({u,v} : Finset ℕ)) :
    (∀ x ∈ X, (readers G P x).Nonempty) ∧
    (∀ x ∈ X, ∀ g, readers G P x = {g} →
      (∀ y ∈ X, y ∈ P g → y = x) ∧ (readers G P g).Nonempty ∧
      (∀ h, readers G P g = {h} → Disjoint (P h) X)) := by
  classical
  have uniqueReader (x g k : ℕ) (h : readers G P x = {g}) (hk : k ∈ G)
      (hp : x ∈ P k) : k = g := by
    have hd : k ∈ readers G P x := Finset.mem_filter.mpr ⟨hk, hp⟩
    simpa [h] using hd
  have readerInfo (x g : ℕ) (h : readers G P x = {g}) : g ∈ G ∧ x ∈ P g := by
    have hd : g ∈ readers G P x := by simp [h]
    exact Finset.mem_filter.mp hd
  constructor
  · intro x hx
    obtain ⟨y, hy, hne⟩ := other x hx
    obtain ⟨o, ho, z, u, v, _, _, ha, hb, _⟩ := tests x hx y hy hne
    by_contra hnone
    have impossible := drop_location n x G ∅ P E {x,z} {z} earlier closed raw flip
    have atO : o ∈ (∅ : Finset ℕ) := by
      apply impossible _ _ o (oG ho) ha hb
      · exact diff_keep x z
      · intro k hk _ p hp hsrc
        rcases hsrc with rfl | hbad
        · exact fun _ => hnone ⟨k, Finset.mem_filter.mpr ⟨hk, hp⟩⟩
        · simp at hbad
    exact Finset.notMem_empty o atO
  · intro x hx g hxg
    obtain ⟨hg, hxp⟩ := readerInfo x g hxg
    have outputDiff (o u v : ℕ) (neg : E {x} o = false) (pos : E {u,v} o = true)
        (off : x ∉ ({u,v} : Finset ℕ)) : o ≠ g := by
      rintro rfl
      rcases blocks o hg x hx hxp with hand | hor
      · have h := hand {u,v} off
        rw [h] at pos
        contradiction
      · have h := hor {x} (by simp)
        rw [h] at neg
        contradiction
    have force (y k : ℕ) (hy : y ∈ X) (hyx : y ≠ x) (hk : k ∈ G) (hyp : y ∈ P k)
        (D : Finset ℕ)
        (guard : ∀ j ∈ G, j ∉ D → ∀ p ∈ P j, (p = x ∨ p ∈ D) → j = k)
        (exclude : ∀ o u v : ℕ, E {x} o = false → E {u,v} o = true →
          x ∉ ({u,v} : Finset ℕ) → o ∉ D) : False := by
      obtain ⟨o, ho, z, u, v, _, hzy, hpos, hneg, hswap, hnx, huv, hoff⟩ := tests x hx y hy hyx
      apply exclude o u v hnx huv hoff
      rcases blocks k hk y hy hyp with hand | hor
      · apply drop_location n x G D P E {x,z} {z} earlier closed raw flip _ _ o (oG ho) hpos hneg
        · exact diff_keep x z
        · intro j hj hjd p hp hsrc
          have hjk := guard j hj hjd p hp hsrc
          subst j
          have blocked := hand {x,z} (by simp [hyx, Ne.symm hzy])
          simp [blocked]
      · apply drop_location n x G D P E {x,z} {y,z} earlier closed raw flip _ _ o (oG ho) hpos hswap
        · exact diff_swap x y z
        · intro j hj hjd p hp hsrc
          have hjk := guard j hj hjd p hp hsrc
          subst j
          have blocked := hor {y,z} (by simp)
          simp [blocked]
    refine ⟨?_, ?_, ?_⟩
    · intro y hy hyp
      by_contra hyx
      apply force y g hy hyx hg hyp ∅ _ (by simp)
      intro k hk _ p hp hsrc
      rcases hsrc with rfl | hbad
      · exact uniqueReader p g k hxg hk hp
      · simp at hbad
    · obtain ⟨y, hy, hne⟩ := other x hx
      obtain ⟨o, ho, z, u, v, _, _, ha, hb, _, neg, pos, off⟩ := tests x hx y hy hne
      by_contra hnone
      apply outputDiff o u v neg pos off
      apply Finset.mem_singleton.mp
      apply drop_location n x G {g} P E {x,z} {z} earlier closed raw flip _ _ o (oG ho) ha hb
      · exact diff_keep x z
      · intro k hk hkg p hp hsrc
        rcases hsrc with rfl | hmem
        · have eq := uniqueReader p g k hxg hk hp
          exact (hkg (Finset.mem_singleton.mpr eq)).elim
        · have eq := Finset.mem_singleton.mp hmem
          subst p
          exact fun _ => hnone ⟨k, Finset.mem_filter.mpr ⟨hk, hp⟩⟩
    · intro h hgh
      apply Finset.disjoint_left.mpr
      intro y hyp hy
      obtain ⟨hh, hgp⟩ := readerInfo g h hgh
      have hyx : y ≠ x := by
        rintro rfl
        have eq := uniqueReader y g h hxg hh hyp
        have lt := earlier h hh g hgp
        omega
      apply force y h hy hyx hh hyp {g} _ _
      · intro k hk hkg p hp hsrc
        rcases hsrc with rfl | hmem
        · have eq := uniqueReader p g k hxg hk hp
          exact (hkg (Finset.mem_singleton.mpr eq)).elim
        · have eq := Finset.mem_singleton.mp hmem
          subst p
          exact uniqueReader g h k hgh hk hp
      · intro o u v neg pos off
        simpa using outputDiff o u v neg pos off

end PEqualNP.Outside.L_meta_1329_aux

namespace PEqualNP.Outside.L_meta_1329_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem assembly_size (C : Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ)
    (hm : Monotone2 C) (checks : GeoChecks C fg) : 167 ≤ C.size := by
  classical
  let X := geoActive.image Fin.val
  let allG := Finset.Ico 162 (162 + C.size)
  let out := fun t : GeoTile => fg (geoA t) (geoM t) (geoG t)
  let O := Finset.univ.image out
  let P := wireParents C 162
  let G := liveSet allG O P
  let E := wireVal C 162
  have xcard : X.card = 132 := by
    simpa [X, Finset.card_image_of_injective _ Fin.val_injective] using geoActive_card
  have ocard : O.card ≤ 27 := by
    calc
      O.card ≤ (Finset.univ : Finset GeoTile).card := Finset.card_image_le
      _ = 27 := by simp [GeoTile]
  have gcard : G.card ≤ C.size := by
    have := Finset.card_le_card (liveSet_subset allG O P)
    simpa [G, allG] using this
  have xbound {x : ℕ} (hx : x ∈ X) : x < 162 := by
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact v.isLt
  have gbounds {g : ℕ} (hg : g ∈ G) : 162 ≤ g ∧ g < 162 + C.size :=
    Finset.mem_Ico.mp (liveSet_subset allG O P hg)
  have oG : O ⊆ G := by
    intro o ho
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ho
    exact liveSet_output (Finset.mem_Ico.mpr (bridge_output_bounds C fg checks t)) ho
  have earlier : ∀ g ∈ G, ∀ p ∈ P g, p < g :=
    fun g _ p hp => wireParents_lt C 162 g p hp
  have closed : ∀ g ∈ G, ∀ p ∈ P g, 162 ≤ p → p ∈ G := by
    intro g hg p hp hl
    exact liveSet_parent hg hp (Finset.mem_Ico.mpr ⟨hl, (earlier g hg p hp).trans (gbounds hg).2⟩)
  have blocks : ∀ g ∈ G, ∀ y ∈ X, y ∈ P g →
      (∀ A : Finset ℕ, y ∉ A → E A g = false) ∨
      (∀ B : Finset ℕ, y ∈ B → E B g = true) := by
    intro g hg y hy hp
    obtain ⟨hl,hu⟩ := gbounds hg
    rcases wireGate_op C hm 162 g hl hu with ha | ho
    · left
      intro A h
      exact wireVal_and_parent_false C 162 g hl hu A y hp ha
        (by simp [wireVal_raw C 162 A y (xbound hy), h])
    · right
      intro B h
      exact wireVal_or_parent_true C 162 g hl hu B y hp ho
        (by simp [wireVal_raw C 162 B y (xbound hy), h])
  have other : ∀ x ∈ X, ∃ y ∈ X, y ≠ x := by
    intro x hx
    by_contra! e
    have sub : X ⊆ {x} := fun y hy => Finset.mem_singleton.mpr (e y hy)
    have := Finset.card_le_card sub
    simp [xcard] at this
  have tests : ∀ x ∈ X, ∀ y ∈ X, y ≠ x → ∃ o ∈ O, ∃ z u v : ℕ,
      x ≠ z ∧ z ≠ y ∧ E {x,z} o = true ∧ E {z} o = false ∧ E {y,z} o = false ∧
      E {x} o = false ∧ E {u,v} o = true ∧ x ∉ ({u,v} : Finset ℕ) := by
    intro x hx y hy hne
    obtain ⟨xi,hxi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨yi,hyi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t,z,u,v,hn,hz,ha,hb,hc,hd,he,hf⟩ :=
      geo_pair_api xi yi hxi hyi (fun h => hne (congrArg Fin.val h.symm))
    refine ⟨out t, Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩,z.val,u.val,v.val,
      (fun h => hn (Fin.ext h)), (fun h => hz (Fin.ext h)), checks.1 t xi z ha, ?_,
      checks.2 t yi z hc, ?_, checks.1 t u v he, ?_⟩
    · simpa [E,out] using checks.2 t z z hb
    · simpa [E,out] using checks.2 t xi xi hd
    · simpa [Fin.ext_iff] using hf
  obtain ⟨hit,singleUse⟩ := separation_conditions 162 X G O P E oG earlier closed
    (fun A p hp => wireVal_raw C 162 A p hp)
    (fun g hg => wireVal_parent_flip C hm 162 g (gbounds hg).1 (gbounds hg).2)
    blocks other tests
  have disj : Disjoint X G := Finset.disjoint_left.mpr fun x hx hg =>
    (Nat.not_le_of_gt (xbound hx)) (gbounds hg).1
  have sink : ∀ g ∈ G, readers G P g = ∅ → g ∈ O := by
    intro g hg h
    by_contra hn
    obtain ⟨j,hj,hp⟩ := liveSet_successor hg hn
    have hmem : j ∈ readers G P g := Finset.mem_filter.mpr ⟨hj,hp⟩
    simp [h] at hmem
  have count := count_bound X G O P disj
    (fun g hg => wireParents_card C hm 162 g (gbounds hg).1 (gbounds hg).2)
    hit sink singleUse
  omega

end PEqualNP.Outside.L_meta_1329_aux

open PEqualNP.Outside.L_meta_1329_aux

theorem PEqualNP.Outside.L_meta_1329 : ∀ (inc : Fin 81 → Fin 81 → Prop) (onPiv : ZMod 3 → ZMod 3 → ZMod 3 → Fin 81 → Prop), (∀ Pi Li : Fin 81, inc Pi Li ↔ (((Pi.val / 9 % 3 : ℕ) : ZMod 3) + ((Li.val / 3 % 3 : ℕ) : ZMod 3) * ((Pi.val / 3 % 3 : ℕ) : ZMod 3) = ((Li.val % 3 : ℕ) : ZMod 3) * ((Pi.val % 3 : ℕ) : ZMod 3) + ((Li.val / 9 % 3 : ℕ) : ZMod 3) ∧ ((Pi.val / 27 : ℕ) : ZMod 3) = ((Li.val % 3 : ℕ) : ZMod 3) * ((Pi.val / 3 % 3 : ℕ) : ZMod 3) + ((Li.val / 3 % 3 : ℕ) : ZMod 3) * ((Pi.val % 3 : ℕ) : ZMod 3) + ((Li.val / 27 : ℕ) : ZMod 3))) → (∀ (ai mi gi : ZMod 3) (Pv : Fin 81), onPiv ai mi gi Pv ↔ (((Pv.val / 9 % 3 : ℕ) : ZMod 3) + mi * ((Pv.val / 3 % 3 : ℕ) : ZMod 3) = mi * ai ∧ ((Pv.val / 27 : ℕ) : ZMod 3) = mi * ((Pv.val % 3 : ℕ) : ZMod 3) + gi)) → ¬ (∃ (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fg : ZMod 3 → ZMod 3 → ZMod 3 → ℕ), PEqualNP.MetaComplexity.Monotone2 Ckt ∧ Ckt.size ≤ 160 ∧ (∀ ad md gd : ZMod 3, (Ckt.lineDegrees (81 + 81) (Finset.Ico 81 (81 + 81))).getD (fg ad md gd) 0 ≤ 2) ∧ (∀ Pa La : Fin 81, inc Pa La → ¬ onPiv ((Pa.val / 3 % 3 : ℕ) : ZMod 3) ((La.val / 3 % 3 : ℕ) : ZMod 3) (((La.val / 27 : ℕ) : ZMod 3) + ((Pa.val / 3 % 3 : ℕ) : ZMod 3) * ((La.val % 3 : ℕ) : ZMod 3)) Pa → (Ckt.wires (List.ofFn (fun vq : Fin (81 + 81) => if vq = Fin.castAdd 81 Pa then true else if vq = Fin.natAdd 81 La then true else false))).getD (fg ((Pa.val / 3 % 3 : ℕ) : ZMod 3) ((La.val / 3 % 3 : ℕ) : ZMod 3) (((La.val / 27 : ℕ) : ZMod 3) + ((Pa.val / 3 % 3 : ℕ) : ZMod 3) * ((La.val % 3 : ℕ) : ZMod 3))) false = true) ∧ (∀ (aw mw gw : ZMod 3) (zz : Fin (81 + 81) → Bool), (∀ Ps : Fin 81, onPiv aw mw gw Ps → zz (Fin.castAdd 81 Ps) = false) → (Ckt.wires (List.ofFn zz)).getD (fg aw mw gw) false = true → ∃ (Pe Le : Fin 81), inc Pe Le ∧ zz (Fin.castAdd 81 Pe) = true ∧ zz (Fin.natAdd 81 Le) = true)) := by
  intro inc onPiv hinc hpiv h
  obtain ⟨C,fg,hm,hsize,_,positive,sound⟩ := h
  have checks := bridge_geoChecks C fg inc onPiv
    (fun p l => (hinc p l).trans (geoInc_desk p l).symm) hpiv positive sound
  have bound := assembly_size C fg hm checks
  omega
