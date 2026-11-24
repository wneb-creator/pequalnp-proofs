import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.DNFCertificate
open PEqualNP.CircuitLowerBounds

abbrev Term := Finset ℕ
abbrev DNF := List Term

def TermHolds (x : List Bool) (t : Term) : Prop :=
  ∀ i ∈ t, x.getD i false = true

def Holds (x : List Bool) (d : DNF) : Prop :=
  ∃ t ∈ d, TermHolds x t

def insertTerm (t : Term) (d : DNF) : DNF :=
  if ∃ s ∈ d, s ⊆ t then d else t :: d.filter (fun s => ¬ t ⊆ s)

lemma term_subset {x : List Bool} {s t : Term} (h : s ⊆ t)
    (ht : TermHolds x t) : TermHolds x s := fun i hi => ht i (h hi)

lemma holds_insert (x : List Bool) (t : Term) (d : DNF) :
    Holds x (insertTerm t d) ↔ TermHolds x t ∨ Holds x d := by
  unfold insertTerm
  split
  · rename_i h
    constructor
    · exact Or.inr
    · rintro (ht | hd)
      · obtain ⟨s, hs, hst⟩ := h
        exact ⟨s, hs, term_subset hst ht⟩
      · exact hd
  · constructor
    · rintro ⟨s, hs, ht⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl ht
      · exact Or.inr ⟨s, (List.mem_filter.mp hs).1, ht⟩
    · rintro (ht | ⟨s, hs, ht⟩)
      · exact ⟨t, List.mem_cons_self, ht⟩
      · by_cases hts : t ⊆ s
        · exact ⟨t, List.mem_cons_self, term_subset hts ht⟩
        · exact ⟨s, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hs, by simpa⟩), ht⟩

def merge (a b : DNF) : DNF := b.foldl (fun d t => insertTerm t d) a

lemma holds_merge (x : List Bool) (a b : DNF) :
    Holds x (merge a b) ↔ Holds x a ∨ Holds x b := by
  induction b generalizing a with
  | nil => simp [merge, Holds]
  | cons t ts ih =>
    change Holds x (merge (insertTerm t a) ts) ↔ _
    rw [ih, holds_insert]
    simp only [Holds, List.mem_cons, exists_eq_or_imp]
    aesop

def multiply (a b : DNF) : DNF :=
  merge [] (a.flatMap fun s => b.map fun t => s ∪ t)

lemma holds_multiply (x : List Bool) (a b : DNF) :
    Holds x (multiply a b) ↔ Holds x a ∧ Holds x b := by
  rw [multiply, holds_merge]
  simp only [Holds, List.not_mem_nil, false_and, exists_false, false_or,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, ⟨s, hs, t, ht, rfl⟩, hu⟩
    exact ⟨⟨s, hs, fun i hi => hu i (Finset.mem_union_left t hi)⟩,
      ⟨t, ht, fun i hi => hu i (Finset.mem_union_right s hi)⟩⟩
  · rintro ⟨⟨s, hs, hst⟩, ⟨t, ht, htt⟩⟩
    refine ⟨s ∪ t, ⟨s, hs, t, ht, rfl⟩, ?_⟩
    intro i hi
    exact (Finset.mem_union.mp hi).elim (hst i) (htt i)

def gateDNF (op : GateOp) (ds : List DNF) : DNF :=
  match op with
  | .and => ds.foldl multiply [∅]
  | .or => ds.foldl merge []
  | _ => []

lemma holds_and_fold (x : List Bool) (ds : List DNF) (a : DNF) :
    Holds x (ds.foldl multiply a) ↔ Holds x a ∧ ∀ d ∈ ds, Holds x d := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, holds_multiply, List.mem_cons,
      forall_eq_or_imp]
    tauto

lemma holds_or_fold (x : List Bool) (ds : List DNF) (a : DNF) :
    Holds x (ds.foldl merge a) ↔ Holds x a ∨ ∃ d ∈ ds, Holds x d := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, holds_merge, List.mem_cons,
      exists_eq_or_imp]
    tauto

def wiresDNF (C : Circuit) (n : ℕ) : List DNF :=
  C.gates.foldl (fun w g => w ++ [gateDNF g.op (g.inputs.map fun i => w.getD i [])])
    ((List.range n).map fun i => [{i}])

def circuitDNF (C : Circuit) (n : ℕ) : DNF := (wiresDNF C n).getD C.output []

lemma gate_correct (x : List Bool) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (dw : List DNF)
    (hw : ∀ i, w.getD i false = true ↔ Holds x (dw.getD i [])) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true ↔
      Holds x (gateDNF g.op (g.inputs.map fun i => dw.getD i [])) := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [gateDNF]
    rw [holds_and_fold]
    have hbase : Holds x [∅] := by simp [Holds, TermHolds]
    simp [GateOp.eval, List.all_eq_true, hbase]
    exact forall_congr' fun i => forall_congr' fun _ => hw i
  · rw [hg]
    simp only [gateDNF]
    rw [holds_or_fold]
    have hbase : ¬ Holds x [] := by simp [Holds]
    simp [GateOp.eval, List.any_eq_true, hbase]
    exact exists_congr fun i => and_congr_right fun _ => hw i

def Related (x : List Bool) (w : List Bool) (dw : List DNF) : Prop :=
  w.length = dw.length ∧ ∀ i, w.getD i false = true ↔ Holds x (dw.getD i [])

lemma related_append {x w : List Bool} {dw : List DNF} (h : Related x w dw)
    (b : Bool) (d : DNF) (hb : b = true ↔ Holds x d) :
    Related x (w ++ [b]) (dw ++ [d]) := by
  have hlen := h.1
  refine ⟨by simp [hlen], ?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by omega)]
    exact h.2 i
  · by_cases heq : i = w.length
    · subst i
      have hwget : (w ++ [b]).getD w.length false = b := by simp
      have hdget : (dw ++ [d]).getD dw.length [] = d := by simp
      rw [hwget, hlen, hdget]
      exact hb
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      simp [Holds]

lemma related_initial (x : List Bool) :
    Related x x ((List.range x.length).map fun i => [{i}]) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < x.length
  · have hd : ((List.range x.length).map fun j => ([{j}] : DNF)).getD i [] = [{i}] := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    rw [hd]
    simp [Holds, TermHolds]
  · rw [List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]
    simp [Holds]

lemma fold_correct (x : List Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (dw : List DNF) (hw : Related x w dw) :
    Related x
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun w g => w ++ [gateDNF g.op (g.inputs.map fun i => w.getD i [])]) dw) := by
  induction gs generalizing w dw with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem g hk))
    exact related_append hw _ _ (gate_correct x g (hg g List.mem_cons_self) w dw hw.2)

theorem circuit_correct (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (x : List Bool) :
    C.eval x = true ↔ Holds x (circuitDNF C x.length) := by
  exact (fold_correct x C.gates (fun g hg => by simpa using (hm g hg).1)
    x _ (related_initial x)).2 C.output

lemma holds_ext (x : List Bool) (a b : DNF) (h : a.toFinset = b.toFinset) :
    Holds x a ↔ Holds x b := by
  have hm : ∀ t, t ∈ a ↔ t ∈ b := by
    intro t
    have ht := congrArg (fun s : Finset Term => t ∈ s) h
    simpa using ht
  simp only [Holds, hm]

theorem certificate (C : Circuit) (n : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (expected : DNF)
    (hc : (circuitDNF C n).toFinset = expected.toFinset)
    (x : List Bool) (hx : x.length = n) :
    C.eval x = true ↔ Holds x expected := by
  rw [circuit_correct C hm, hx]
  exact holds_ext x _ _ hc

end PEqualNP.Outside.L_meta_1477.DNFCertificate
