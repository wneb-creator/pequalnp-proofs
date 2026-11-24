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

lemma circuit_correct (C : Circuit)
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

lemma certificate (C : Circuit) (n : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (expected : DNF)
    (hc : (circuitDNF C n).toFinset = expected.toFinset)
    (x : List Bool) (hx : x.length = n) :
    C.eval x = true ↔ Holds x expected := by
  rw [circuit_correct C hm, hx]
  exact holds_ext x _ _ hc

end PEqualNP.Outside.L_meta_1477.DNFCertificate

namespace PEqualNP.Outside.L_meta_1477.DNFCertificate
open PEqualNP.CircuitLowerBounds

lemma take_step {α : Type} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take (k+1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simp

def TableValid (C : Circuit) (n : ℕ) (table : List DNF) : Prop :=
  table.length = n + C.gates.length ∧
  table.take n = (List.range n).map (fun i => [{i}]) ∧
  ∀ j : Fin C.gates.length,
    (gateDNF C.gates[j.val].op (C.gates[j.val].inputs.map fun i =>
      (table.take (n+j.val)).getD i [])).toFinset =
    (table.getD (n+j.val) []).toFinset

lemma table_correct (C : Circuit) (n : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (table : List DNF)
    (ht : TableValid C n table) (x : List Bool) (hx : x.length = n) :
    C.eval x = true ↔ Holds x (table.getD C.output []) := by
  subst n
  obtain ⟨htlen, htinit, htstep⟩ := ht
  have hp : ∀ k, k ≤ C.gates.length → Related x
      ((C.gates.take k).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x)
      (table.take (x.length+k)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa only [List.take_zero, List.foldl_nil, Nat.add_zero, htinit] using related_initial x
    | succ k ih =>
      intro hk
      have hkg : k < C.gates.length := by omega
      have hkt : x.length+k < table.length := by omega
      have hs := ih (by omega)
      let w := (C.gates.take k).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      have hgate := gate_correct x C.gates[k]
        (by simpa using (hm C.gates[k] (List.getElem_mem hkg)).1)
        w (table.take (x.length+k)) hs.2
      have hc : (gateDNF C.gates[k].op (C.gates[k].inputs.map fun i =>
          (table.take (x.length+k)).getD i [])).toFinset = (table[x.length+k]).toFinset := by
        simpa only [List.getD_eq_getElem _ _ hkt] using htstep ⟨k,hkg⟩
      have hnew := related_append hs _ (table[x.length+k])
        (hgate.trans (holds_ext x _ _ hc))
      rw [take_step C.gates k hkg, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [show x.length + (k+1) = (x.length+k)+1 by omega,
        take_step table (x.length+k) hkt]
      exact hnew
  have hfinal := (hp C.gates.length (by omega)).2 C.output
  simpa only [Circuit.eval, Circuit.wires, List.take_length, ← htlen] using hfinal

lemma table_certificate (C : Circuit) (n : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (table : List DNF)
    (ht : TableValid C n table) (expected : DNF)
    (hc : (table.getD C.output []).toFinset = expected.toFinset)
    (x : List Bool) (hx : x.length = n) :
    C.eval x = true ↔ Holds x expected :=
  (table_correct C n hm table ht x hx).trans (holds_ext x _ _ hc)

end PEqualNP.Outside.L_meta_1477.DNFCertificate

namespace PEqualNP.Outside.L_meta_1477.Complement12DNF

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1477.DNFCertificate

def localPairs : List (Fin 33 × Fin 33) :=
  [(0, 14), (0, 17), (0, 18), (0, 23), (0, 25), (1, 15), (1, 18), (1, 19), (1, 24), (1, 26), (2, 16), (2, 19), (2, 20), (2, 25), (2, 27), (3, 17), (3, 20), (3, 21), (3, 26), (3, 28), (4, 19), (4, 22), (4, 23), (4, 28), (4, 30), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 12), (6, 22), (6, 25), (6, 26), (6, 31), (7, 13), (7, 23), (7, 26), (7, 27), (7, 32), (8, 12), (8, 14), (8, 24), (8, 27), (8, 28), (9, 13), (9, 15), (9, 25), (9, 28), (9, 29), (10, 14), (10, 16), (10, 26), (10, 29), (10, 30), (11, 16), (11, 18), (11, 28), (11, 31), (11, 32)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def baseline71 : Circuit :=
  ⟨[⟨.or, [14, 17]⟩,
    ⟨.or, [18, 33]⟩,
    ⟨.or, [23, 34]⟩,
    ⟨.or, [25, 35]⟩,
    ⟨.and, [0, 36]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [19, 38]⟩,
    ⟨.or, [24, 39]⟩,
    ⟨.or, [26, 40]⟩,
    ⟨.and, [1, 41]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.or, [20, 43]⟩,
    ⟨.or, [25, 44]⟩,
    ⟨.or, [27, 45]⟩,
    ⟨.and, [2, 46]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.or, [21, 48]⟩,
    ⟨.or, [26, 49]⟩,
    ⟨.or, [28, 50]⟩,
    ⟨.and, [3, 51]⟩,
    ⟨.or, [19, 22]⟩,
    ⟨.or, [23, 53]⟩,
    ⟨.or, [28, 54]⟩,
    ⟨.or, [30, 55]⟩,
    ⟨.and, [4, 56]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.or, [25, 58]⟩,
    ⟨.or, [30, 59]⟩,
    ⟨.or, [32, 60]⟩,
    ⟨.and, [5, 61]⟩,
    ⟨.or, [12, 22]⟩,
    ⟨.or, [25, 63]⟩,
    ⟨.or, [26, 64]⟩,
    ⟨.or, [31, 65]⟩,
    ⟨.and, [6, 66]⟩,
    ⟨.or, [13, 23]⟩,
    ⟨.or, [26, 68]⟩,
    ⟨.or, [27, 69]⟩,
    ⟨.or, [32, 70]⟩,
    ⟨.and, [7, 71]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [24, 73]⟩,
    ⟨.or, [27, 74]⟩,
    ⟨.or, [28, 75]⟩,
    ⟨.and, [8, 76]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [25, 78]⟩,
    ⟨.or, [28, 79]⟩,
    ⟨.or, [29, 80]⟩,
    ⟨.and, [9, 81]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [26, 83]⟩,
    ⟨.or, [29, 84]⟩,
    ⟨.or, [30, 85]⟩,
    ⟨.and, [10, 86]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [28, 88]⟩,
    ⟨.or, [31, 89]⟩,
    ⟨.or, [32, 90]⟩,
    ⟨.and, [11, 91]⟩,
    ⟨.or, [37, 42]⟩,
    ⟨.or, [47, 93]⟩,
    ⟨.or, [52, 94]⟩,
    ⟨.or, [57, 95]⟩,
    ⟨.or, [62, 96]⟩,
    ⟨.or, [67, 97]⟩,
    ⟨.or, [72, 98]⟩,
    ⟨.or, [77, 99]⟩,
    ⟨.or, [82, 100]⟩,
    ⟨.or, [87, 101]⟩,
    ⟨.or, [92, 102]⟩], 103⟩

def expected : DNF := localPairs.map (fun e => {e.1.val, e.2.val})

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def table : List DNF :=
  [[{0}],
   [{1}],
   [{2}],
   [{3}],
   [{4}],
   [{5}],
   [{6}],
   [{7}],
   [{8}],
   [{9}],
   [{10}],
   [{11}],
   [{12}],
   [{13}],
   [{14}],
   [{15}],
   [{16}],
   [{17}],
   [{18}],
   [{19}],
   [{20}],
   [{21}],
   [{22}],
   [{23}],
   [{24}],
   [{25}],
   [{26}],
   [{27}],
   [{28}],
   [{29}],
   [{30}],
   [{31}],
   [{32}],
   [{14}, {17}],
   [{14}, {17}, {18}],
   [{14}, {17}, {18}, {23}],
   [{14}, {17}, {18}, {23}, {25}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}],
   [{15}, {18}],
   [{15}, {18}, {19}],
   [{15}, {18}, {19}, {24}],
   [{15}, {18}, {19}, {24}, {26}],
   [{1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}],
   [{16}, {19}],
   [{16}, {19}, {20}],
   [{16}, {19}, {20}, {25}],
   [{16}, {19}, {20}, {25}, {27}],
   [{2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}],
   [{17}, {20}],
   [{17}, {20}, {21}],
   [{17}, {20}, {21}, {26}],
   [{17}, {20}, {21}, {26}, {28}],
   [{3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}],
   [{19}, {22}],
   [{19}, {22}, {23}],
   [{19}, {22}, {23}, {28}],
   [{19}, {22}, {23}, {28}, {30}],
   [{4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}],
   [{21}, {24}],
   [{21}, {24}, {25}],
   [{21}, {24}, {25}, {30}],
   [{21}, {24}, {25}, {30}, {32}],
   [{5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}],
   [{12}, {22}],
   [{12}, {22}, {25}],
   [{12}, {22}, {25}, {26}],
   [{12}, {22}, {25}, {26}, {31}],
   [{6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}],
   [{13}, {23}],
   [{13}, {23}, {26}],
   [{13}, {23}, {26}, {27}],
   [{13}, {23}, {26}, {27}, {32}],
   [{7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}],
   [{12}, {14}],
   [{12}, {14}, {24}],
   [{12}, {14}, {24}, {27}],
   [{12}, {14}, {24}, {27}, {28}],
   [{8, 12}, {8, 14}, {8, 24}, {8, 27}, {8, 28}],
   [{13}, {15}],
   [{13}, {15}, {25}],
   [{13}, {15}, {25}, {28}],
   [{13}, {15}, {25}, {28}, {29}],
   [{9, 13}, {9, 15}, {9, 25}, {9, 28}, {9, 29}],
   [{14}, {16}],
   [{14}, {16}, {26}],
   [{14}, {16}, {26}, {29}],
   [{14}, {16}, {26}, {29}, {30}],
   [{10, 14}, {10, 16}, {10, 26}, {10, 29}, {10, 30}],
   [{16}, {18}],
   [{16}, {18}, {28}],
   [{16}, {18}, {28}, {31}],
   [{16}, {18}, {28}, {31}, {32}],
   [{11, 16}, {11, 18}, {11, 28}, {11, 31}, {11, 32}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}, {7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}, {7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}, {8, 12}, {8, 14}, {8, 24}, {8, 27}, {8, 28}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}, {7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}, {8, 12}, {8, 14}, {8, 24}, {8, 27}, {8, 28}, {9, 13}, {9, 15}, {9, 25}, {9, 28}, {9, 29}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}, {7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}, {8, 12}, {8, 14}, {8, 24}, {8, 27}, {8, 28}, {9, 13}, {9, 15}, {9, 25}, {9, 28}, {9, 29}, {10, 14}, {10, 16}, {10, 26}, {10, 29}, {10, 30}],
   [{0, 14}, {0, 17}, {0, 18}, {0, 23}, {0, 25}, {1, 15}, {1, 18}, {1, 19}, {1, 24}, {1, 26}, {2, 16}, {2, 19}, {2, 20}, {2, 25}, {2, 27}, {3, 17}, {3, 20}, {3, 21}, {3, 26}, {3, 28}, {4, 19}, {4, 22}, {4, 23}, {4, 28}, {4, 30}, {5, 21}, {5, 24}, {5, 25}, {5, 30}, {5, 32}, {6, 12}, {6, 22}, {6, 25}, {6, 26}, {6, 31}, {7, 13}, {7, 23}, {7, 26}, {7, 27}, {7, 32}, {8, 12}, {8, 14}, {8, 24}, {8, 27}, {8, 28}, {9, 13}, {9, 15}, {9, 25}, {9, 28}, {9, 29}, {10, 14}, {10, 16}, {10, 26}, {10, 29}, {10, 30}, {11, 16}, {11, 18}, {11, 28}, {11, 31}, {11, 32}]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma baseline71_monotone : PEqualNP.MetaComplexity.Monotone2 baseline71 := by
  simp [PEqualNP.MetaComplexity.Monotone2, baseline71]

lemma baseline71_size : baseline71.size = 71 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma table_valid : TableValid baseline71 33 table := by
  unfold TableValid
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma table_output : (table.getD baseline71.output []).toFinset = expected.toFinset := by
  decide

lemma holds_pairs (x : Fin 33 → Bool) : Holds (List.ofFn x) expected ↔
    ∃ u v : Fin 33, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true := by
  have get (i : Fin 33) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn (f := x) (i := i.val) (by simp)
  unfold Holds expected
  constructor
  · rintro ⟨t, ht, hh⟩
    obtain ⟨⟨u, v⟩, he, rfl⟩ := List.mem_map.mp ht
    refine ⟨u, v, he, ?_, ?_⟩
    · rw [← get u]
      exact hh u.val (by simp)
    · rw [← get v]
      exact hh v.val (by simp)
  · rintro ⟨u, v, he, hu, hv⟩
    refine ⟨{u.val, v.val}, List.mem_map.mpr ⟨(u, v), he, rfl⟩, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      simpa only [get] using hu
    · have hi := Finset.mem_singleton.mp hi
      subst i
      simpa only [get] using hv

lemma baseline71_computes (x : Fin 33 → Bool) :
    baseline71.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 33, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true :=
  (table_certificate baseline71 33 baseline71_monotone table table_valid expected
    table_output (List.ofFn x) (by simp)).trans (holds_pairs x)

end PEqualNP.Outside.L_meta_1477.Complement12DNF
