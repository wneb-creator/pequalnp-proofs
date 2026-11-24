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

theorem table_correct (C : Circuit) (n : ℕ)
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

theorem table_certificate (C : Circuit) (n : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (table : List DNF)
    (ht : TableValid C n table) (expected : DNF)
    (hc : (table.getD C.output []).toFinset = expected.toFinset)
    (x : List Bool) (hx : x.length = n) :
    C.eval x = true ↔ Holds x expected :=
  (table_correct C n hm table ht x hx).trans (holds_ext x _ _ hc)

end PEqualNP.Outside.L_meta_1477.DNFCertificate

namespace PEqualNP.Outside.L_meta_1477.DNFTableBaseline
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1477.DNFCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def planeStar : Circuit :=
  ⟨[⟨.or, [21, 26]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 38]⟩,
    ⟨.or, [44, 41]⟩,
    ⟨.and, [0, 45]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [47, 27]⟩,
    ⟨.or, [48, 29]⟩,
    ⟨.or, [49, 39]⟩,
    ⟨.and, [1, 50]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [52, 28]⟩,
    ⟨.or, [53, 30]⟩,
    ⟨.or, [54, 40]⟩,
    ⟨.and, [2, 55]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.or, [57, 29]⟩,
    ⟨.or, [58, 31]⟩,
    ⟨.or, [59, 41]⟩,
    ⟨.and, [3, 60]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.or, [62, 25]⟩,
    ⟨.or, [63, 30]⟩,
    ⟨.or, [64, 32]⟩,
    ⟨.and, [4, 65]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.or, [67, 26]⟩,
    ⟨.or, [68, 31]⟩,
    ⟨.or, [69, 33]⟩,
    ⟨.and, [5, 70]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [72, 27]⟩,
    ⟨.or, [73, 32]⟩,
    ⟨.or, [74, 34]⟩,
    ⟨.and, [6, 75]⟩,
    ⟨.or, [24, 27]⟩,
    ⟨.or, [77, 28]⟩,
    ⟨.or, [78, 33]⟩,
    ⟨.or, [79, 35]⟩,
    ⟨.and, [7, 80]⟩,
    ⟨.or, [25, 28]⟩,
    ⟨.or, [82, 29]⟩,
    ⟨.or, [83, 34]⟩,
    ⟨.or, [84, 36]⟩,
    ⟨.and, [8, 85]⟩,
    ⟨.or, [26, 29]⟩,
    ⟨.or, [87, 30]⟩,
    ⟨.or, [88, 35]⟩,
    ⟨.or, [89, 37]⟩,
    ⟨.and, [9, 90]⟩,
    ⟨.or, [27, 30]⟩,
    ⟨.or, [92, 31]⟩,
    ⟨.or, [93, 36]⟩,
    ⟨.or, [94, 38]⟩,
    ⟨.and, [10, 95]⟩,
    ⟨.or, [28, 31]⟩,
    ⟨.or, [97, 32]⟩,
    ⟨.or, [98, 37]⟩,
    ⟨.or, [99, 39]⟩,
    ⟨.and, [11, 100]⟩,
    ⟨.or, [29, 32]⟩,
    ⟨.or, [102, 33]⟩,
    ⟨.or, [103, 38]⟩,
    ⟨.or, [104, 40]⟩,
    ⟨.and, [12, 105]⟩,
    ⟨.or, [30, 33]⟩,
    ⟨.or, [107, 34]⟩,
    ⟨.or, [108, 39]⟩,
    ⟨.or, [109, 41]⟩,
    ⟨.and, [13, 110]⟩,
    ⟨.or, [21, 31]⟩,
    ⟨.or, [112, 34]⟩,
    ⟨.or, [113, 35]⟩,
    ⟨.or, [114, 40]⟩,
    ⟨.and, [14, 115]⟩,
    ⟨.or, [22, 32]⟩,
    ⟨.or, [117, 35]⟩,
    ⟨.or, [118, 36]⟩,
    ⟨.or, [119, 41]⟩,
    ⟨.and, [15, 120]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [122, 33]⟩,
    ⟨.or, [123, 36]⟩,
    ⟨.or, [124, 37]⟩,
    ⟨.and, [16, 125]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [127, 34]⟩,
    ⟨.or, [128, 37]⟩,
    ⟨.or, [129, 38]⟩,
    ⟨.and, [17, 130]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [132, 35]⟩,
    ⟨.or, [133, 38]⟩,
    ⟨.or, [134, 39]⟩,
    ⟨.and, [18, 135]⟩,
    ⟨.or, [24, 26]⟩,
    ⟨.or, [137, 36]⟩,
    ⟨.or, [138, 39]⟩,
    ⟨.or, [139, 40]⟩,
    ⟨.and, [19, 140]⟩,
    ⟨.or, [25, 27]⟩,
    ⟨.or, [142, 37]⟩,
    ⟨.or, [143, 40]⟩,
    ⟨.or, [144, 41]⟩,
    ⟨.and, [20, 145]⟩,
    ⟨.or, [46, 51]⟩,
    ⟨.or, [147, 56]⟩,
    ⟨.or, [148, 61]⟩,
    ⟨.or, [149, 66]⟩,
    ⟨.or, [150, 71]⟩,
    ⟨.or, [151, 76]⟩,
    ⟨.or, [152, 81]⟩,
    ⟨.or, [153, 86]⟩,
    ⟨.or, [154, 91]⟩,
    ⟨.or, [155, 96]⟩,
    ⟨.or, [156, 101]⟩,
    ⟨.or, [157, 106]⟩,
    ⟨.or, [158, 111]⟩,
    ⟨.or, [159, 116]⟩,
    ⟨.or, [160, 121]⟩,
    ⟨.or, [161, 126]⟩,
    ⟨.or, [162, 131]⟩,
    ⟨.or, [163, 136]⟩,
    ⟨.or, [164, 141]⟩,
    ⟨.or, [165, 146]⟩], 166⟩

def expected : DNF :=
  [{0, 21}, {0, 26}, {0, 28}, {0, 38}, {0, 41}, {1, 21}, {1, 22}, {1, 27}, {1, 29}, {1, 39}, {2, 22}, {2, 23}, {2, 28}, {2, 30}, {2, 40}, {3, 23}, {3, 24}, {3, 29}, {3, 31}, {3, 41}, {4, 21}, {4, 24}, {4, 25}, {4, 30}, {4, 32}, {5, 22}, {5, 25}, {5, 26}, {5, 31}, {5, 33}, {6, 23}, {6, 26}, {6, 27}, {6, 32}, {6, 34}, {7, 24}, {7, 27}, {7, 28}, {7, 33}, {7, 35}, {8, 25}, {8, 28}, {8, 29}, {8, 34}, {8, 36}, {9, 26}, {9, 29}, {9, 30}, {9, 35}, {9, 37}, {10, 27}, {10, 30}, {10, 31}, {10, 36}, {10, 38}, {11, 28}, {11, 31}, {11, 32}, {11, 37}, {11, 39}, {12, 29}, {12, 32}, {12, 33}, {12, 38}, {12, 40}, {13, 30}, {13, 33}, {13, 34}, {13, 39}, {13, 41}, {14, 21}, {14, 31}, {14, 34}, {14, 35}, {14, 40}, {15, 22}, {15, 32}, {15, 35}, {15, 36}, {15, 41}, {16, 21}, {16, 23}, {16, 33}, {16, 36}, {16, 37}, {17, 22}, {17, 24}, {17, 34}, {17, 37}, {17, 38}, {18, 23}, {18, 25}, {18, 35}, {18, 38}, {18, 39}, {19, 24}, {19, 26}, {19, 36}, {19, 39}, {19, 40}, {20, 25}, {20, 27}, {20, 37}, {20, 40}, {20, 41}]

theorem planeStar_mono : PEqualNP.MetaComplexity.Monotone2 planeStar := by
  simp [PEqualNP.MetaComplexity.Monotone2, planeStar]
theorem planeStar_size : planeStar.size = 125 := by decide

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
    [{33}],
    [{34}],
    [{35}],
    [{36}],
    [{37}],
    [{38}],
    [{39}],
    [{40}],
    [{41}],
    [{26}, {21}],
    [{28}, {21}, {26}],
    [{38}, {26}, {21}, {28}],
    [{41}, {28}, {21}, {26}, {38}],
    [{0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}],
    [{22}, {21}],
    [{27}, {21}, {22}],
    [{29}, {22}, {21}, {27}],
    [{39}, {27}, {21}, {22}, {29}],
    [{1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}],
    [{23}, {22}],
    [{28}, {22}, {23}],
    [{30}, {23}, {22}, {28}],
    [{40}, {28}, {22}, {23}, {30}],
    [{2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}],
    [{24}, {23}],
    [{29}, {23}, {24}],
    [{31}, {24}, {23}, {29}],
    [{41}, {29}, {23}, {24}, {31}],
    [{3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}],
    [{24}, {21}],
    [{25}, {21}, {24}],
    [{30}, {24}, {21}, {25}],
    [{32}, {25}, {21}, {24}, {30}],
    [{4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}],
    [{25}, {22}],
    [{26}, {22}, {25}],
    [{31}, {25}, {22}, {26}],
    [{33}, {26}, {22}, {25}, {31}],
    [{5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}],
    [{26}, {23}],
    [{27}, {23}, {26}],
    [{32}, {26}, {23}, {27}],
    [{34}, {27}, {23}, {26}, {32}],
    [{6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}],
    [{27}, {24}],
    [{28}, {24}, {27}],
    [{33}, {27}, {24}, {28}],
    [{35}, {28}, {24}, {27}, {33}],
    [{7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}],
    [{28}, {25}],
    [{29}, {25}, {28}],
    [{34}, {28}, {25}, {29}],
    [{36}, {29}, {25}, {28}, {34}],
    [{8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}],
    [{29}, {26}],
    [{30}, {26}, {29}],
    [{35}, {29}, {26}, {30}],
    [{37}, {30}, {26}, {29}, {35}],
    [{9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}],
    [{30}, {27}],
    [{31}, {27}, {30}],
    [{36}, {30}, {27}, {31}],
    [{38}, {31}, {27}, {30}, {36}],
    [{10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}],
    [{31}, {28}],
    [{32}, {28}, {31}],
    [{37}, {31}, {28}, {32}],
    [{39}, {32}, {28}, {31}, {37}],
    [{11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}],
    [{32}, {29}],
    [{33}, {29}, {32}],
    [{38}, {32}, {29}, {33}],
    [{40}, {33}, {29}, {32}, {38}],
    [{12, 38}, {12, 32}, {12, 29}, {12, 33}, {12, 40}],
    [{33}, {30}],
    [{34}, {30}, {33}],
    [{39}, {33}, {30}, {34}],
    [{41}, {34}, {30}, {33}, {39}],
    [{13, 39}, {13, 33}, {13, 30}, {13, 34}, {13, 41}],
    [{31}, {21}],
    [{34}, {21}, {31}],
    [{35}, {31}, {21}, {34}],
    [{40}, {34}, {21}, {31}, {35}],
    [{14, 35}, {14, 31}, {14, 21}, {14, 34}, {14, 40}],
    [{32}, {22}],
    [{35}, {22}, {32}],
    [{36}, {32}, {22}, {35}],
    [{41}, {35}, {22}, {32}, {36}],
    [{15, 36}, {15, 32}, {15, 22}, {15, 35}, {15, 41}],
    [{23}, {21}],
    [{33}, {21}, {23}],
    [{36}, {23}, {21}, {33}],
    [{37}, {33}, {21}, {23}, {36}],
    [{16, 36}, {16, 23}, {16, 21}, {16, 33}, {16, 37}],
    [{24}, {22}],
    [{34}, {22}, {24}],
    [{37}, {24}, {22}, {34}],
    [{38}, {34}, {22}, {24}, {37}],
    [{17, 37}, {17, 24}, {17, 22}, {17, 34}, {17, 38}],
    [{25}, {23}],
    [{35}, {23}, {25}],
    [{38}, {25}, {23}, {35}],
    [{39}, {35}, {23}, {25}, {38}],
    [{18, 38}, {18, 25}, {18, 23}, {18, 35}, {18, 39}],
    [{26}, {24}],
    [{36}, {24}, {26}],
    [{39}, {26}, {24}, {36}],
    [{40}, {36}, {24}, {26}, {39}],
    [{19, 39}, {19, 26}, {19, 24}, {19, 36}, {19, 40}],
    [{27}, {25}],
    [{37}, {25}, {27}],
    [{40}, {27}, {25}, {37}],
    [{41}, {37}, {25}, {27}, {40}],
    [{20, 40}, {20, 27}, {20, 25}, {20, 37}, {20, 41}],
    [{1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}],
    [{2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}],
    [{3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}],
    [{4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}],
    [{5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}],
    [{6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}],
    [{7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}],
    [{8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}],
    [{9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}],
    [{10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}],
    [{11, 39}, {11, 32}, {11, 28}, {11, 31}, {11, 37}, {9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}, {10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}],
    [{12, 40}, {12, 33}, {12, 29}, {12, 32}, {12, 38}, {10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}, {11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}],
    [{13, 41}, {13, 34}, {13, 30}, {13, 33}, {13, 39}, {11, 39}, {11, 32}, {11, 28}, {11, 31}, {11, 37}, {9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}, {10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}, {12, 38}, {12, 32}, {12, 29}, {12, 33}, {12, 40}],
    [{14, 40}, {14, 34}, {14, 21}, {14, 31}, {14, 35}, {12, 40}, {12, 33}, {12, 29}, {12, 32}, {12, 38}, {10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}, {11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}, {13, 39}, {13, 33}, {13, 30}, {13, 34}, {13, 41}],
    [{15, 41}, {15, 35}, {15, 22}, {15, 32}, {15, 36}, {13, 41}, {13, 34}, {13, 30}, {13, 33}, {13, 39}, {11, 39}, {11, 32}, {11, 28}, {11, 31}, {11, 37}, {9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}, {10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}, {12, 38}, {12, 32}, {12, 29}, {12, 33}, {12, 40}, {14, 35}, {14, 31}, {14, 21}, {14, 34}, {14, 40}],
    [{16, 37}, {16, 33}, {16, 21}, {16, 23}, {16, 36}, {14, 40}, {14, 34}, {14, 21}, {14, 31}, {14, 35}, {12, 40}, {12, 33}, {12, 29}, {12, 32}, {12, 38}, {10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}, {11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}, {13, 39}, {13, 33}, {13, 30}, {13, 34}, {13, 41}, {15, 36}, {15, 32}, {15, 22}, {15, 35}, {15, 41}],
    [{17, 38}, {17, 34}, {17, 22}, {17, 24}, {17, 37}, {15, 41}, {15, 35}, {15, 22}, {15, 32}, {15, 36}, {13, 41}, {13, 34}, {13, 30}, {13, 33}, {13, 39}, {11, 39}, {11, 32}, {11, 28}, {11, 31}, {11, 37}, {9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}, {10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}, {12, 38}, {12, 32}, {12, 29}, {12, 33}, {12, 40}, {14, 35}, {14, 31}, {14, 21}, {14, 34}, {14, 40}, {16, 36}, {16, 23}, {16, 21}, {16, 33}, {16, 37}],
    [{18, 39}, {18, 35}, {18, 23}, {18, 25}, {18, 38}, {16, 37}, {16, 33}, {16, 21}, {16, 23}, {16, 36}, {14, 40}, {14, 34}, {14, 21}, {14, 31}, {14, 35}, {12, 40}, {12, 33}, {12, 29}, {12, 32}, {12, 38}, {10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}, {11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}, {13, 39}, {13, 33}, {13, 30}, {13, 34}, {13, 41}, {15, 36}, {15, 32}, {15, 22}, {15, 35}, {15, 41}, {17, 37}, {17, 24}, {17, 22}, {17, 34}, {17, 38}],
    [{19, 40}, {19, 36}, {19, 24}, {19, 26}, {19, 39}, {17, 38}, {17, 34}, {17, 22}, {17, 24}, {17, 37}, {15, 41}, {15, 35}, {15, 22}, {15, 32}, {15, 36}, {13, 41}, {13, 34}, {13, 30}, {13, 33}, {13, 39}, {11, 39}, {11, 32}, {11, 28}, {11, 31}, {11, 37}, {9, 37}, {9, 30}, {9, 26}, {9, 29}, {9, 35}, {7, 35}, {7, 28}, {7, 24}, {7, 27}, {7, 33}, {5, 33}, {5, 26}, {5, 22}, {5, 25}, {5, 31}, {3, 41}, {3, 29}, {3, 23}, {3, 24}, {3, 31}, {1, 39}, {1, 27}, {1, 21}, {1, 22}, {1, 29}, {0, 41}, {0, 28}, {0, 21}, {0, 26}, {0, 38}, {2, 30}, {2, 23}, {2, 22}, {2, 28}, {2, 40}, {4, 30}, {4, 24}, {4, 21}, {4, 25}, {4, 32}, {6, 32}, {6, 26}, {6, 23}, {6, 27}, {6, 34}, {8, 34}, {8, 28}, {8, 25}, {8, 29}, {8, 36}, {10, 36}, {10, 30}, {10, 27}, {10, 31}, {10, 38}, {12, 38}, {12, 32}, {12, 29}, {12, 33}, {12, 40}, {14, 35}, {14, 31}, {14, 21}, {14, 34}, {14, 40}, {16, 36}, {16, 23}, {16, 21}, {16, 33}, {16, 37}, {18, 38}, {18, 25}, {18, 23}, {18, 35}, {18, 39}],
    [{20, 41}, {20, 37}, {20, 25}, {20, 27}, {20, 40}, {18, 39}, {18, 35}, {18, 23}, {18, 25}, {18, 38}, {16, 37}, {16, 33}, {16, 21}, {16, 23}, {16, 36}, {14, 40}, {14, 34}, {14, 21}, {14, 31}, {14, 35}, {12, 40}, {12, 33}, {12, 29}, {12, 32}, {12, 38}, {10, 38}, {10, 31}, {10, 27}, {10, 30}, {10, 36}, {8, 36}, {8, 29}, {8, 25}, {8, 28}, {8, 34}, {6, 34}, {6, 27}, {6, 23}, {6, 26}, {6, 32}, {4, 32}, {4, 25}, {4, 21}, {4, 24}, {4, 30}, {2, 40}, {2, 28}, {2, 22}, {2, 23}, {2, 30}, {0, 38}, {0, 26}, {0, 21}, {0, 28}, {0, 41}, {1, 29}, {1, 22}, {1, 21}, {1, 27}, {1, 39}, {3, 31}, {3, 24}, {3, 23}, {3, 29}, {3, 41}, {5, 31}, {5, 25}, {5, 22}, {5, 26}, {5, 33}, {7, 33}, {7, 27}, {7, 24}, {7, 28}, {7, 35}, {9, 35}, {9, 29}, {9, 26}, {9, 30}, {9, 37}, {11, 37}, {11, 31}, {11, 28}, {11, 32}, {11, 39}, {13, 39}, {13, 33}, {13, 30}, {13, 34}, {13, 41}, {15, 36}, {15, 32}, {15, 22}, {15, 35}, {15, 41}, {17, 37}, {17, 24}, {17, 22}, {17, 34}, {17, 38}, {19, 39}, {19, 26}, {19, 24}, {19, 36}, {19, 40}]]

lemma planeStar_table : TableValid planeStar 42 table := by
  unfold TableValid
  decide
lemma planeStar_output : (table.getD planeStar.output []).toFinset = expected.toFinset := by decide
lemma planeStar_correct (x : List Bool) (hx : x.length = 42) :
    planeStar.eval x = true ↔ Holds x expected :=
  table_certificate planeStar 42 planeStar_mono table planeStar_table expected planeStar_output x hx

end PEqualNP.Outside.L_meta_1477.DNFTableBaseline
