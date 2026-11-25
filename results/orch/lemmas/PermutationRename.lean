import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Automorphisms

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def renameWire {n : ℕ} (σ : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then σ ⟨i,h⟩ else i

def renameGate {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (renameWire σ)⟩

def renameCircuit {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate σ),renameWire σ C.output⟩

lemma renameWire_high {n i : ℕ} (σ : Fin n → Fin n) (hi : n ≤ i) : renameWire σ i = i := by
  simp [renameWire, Nat.not_lt.mpr hi]

lemma renameWire_lt {n m i : ℕ} (σ : Fin n → Fin n) (hm : n ≤ m) (hi : i < m) :
    renameWire σ i < m := by
  unfold renameWire
  split_ifs with h
  · exact lt_of_lt_of_le (σ ⟨i,h⟩).isLt hm
  · exact hi

lemma read_relation_snoc {n : ℕ} (σ : Fin n → Fin n) (x y : List Bool) (v : Bool)
    (hn : n ≤ x.length) (hlen : x.length = y.length)
    (rel : ∀ i, x.getD (renameWire σ i) false = y.getD i false) :
    ∀ i, (x ++ [v]).getD (renameWire σ i) false = (y ++ [v]).getD i false := by
  intro i
  rcases lt_trichotomy i x.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ (renameWire_lt σ hn hi),
      List.getD_append _ _ _ _ (by omega)]
    exact rel i
  · rw [renameWire_high σ hn]
    calc (x ++ [v]).getD x.length false = v := by simp [List.getD_eq_getElem?_getD]
         _ = (y ++ [v]).getD x.length false := by rw [hlen]; simp [List.getD_eq_getElem?_getD]
  · rw [renameWire_high σ (by omega), List.getD_eq_default _ _ (by simp;omega),
      List.getD_eq_default _ _ (by simp;omega)]

lemma fold_rename_relation {n : ℕ} (σ : Fin n → Fin n) (gs : List Gate)
    (x y : List Bool) (hn : n ≤ x.length) (hlen : x.length = y.length)
    (rel : ∀ i, x.getD (renameWire σ i) false = y.getD i false) :
    ∀ i,
      ((gs.map (renameGate σ)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD
        (renameWire σ i) false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) y).getD i false := by
  induction gs generalizing x y with
  | nil => exact rel
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have hv : (renameGate σ g).op.eval ((renameGate σ g).inputs.map fun j => x.getD j false) =
        g.op.eval (g.inputs.map fun j => y.getD j false) := by
      simp only [renameGate,List.map_map]
      congr 1
      exact List.map_congr_left (fun j hj => rel j)
    rw [hv]
    apply ih
    · simp
      omega
    · simp [hlen]
    · exact read_relation_snoc σ x y _ hn hlen rel

lemma initial_read_relation {n : ℕ} (σ : Fin n → Fin n) (x : Fin n → Bool) (tail : List Bool) :
    ∀ i, (List.ofFn x ++ tail).getD (renameWire σ i) false =
      (List.ofFn (fun j => x (σ j)) ++ tail).getD i false := by
  intro i
  by_cases hi : i < n
  · have hr : renameWire σ i < n := renameWire_lt σ le_rfl hi
    rw [List.getD_append _ _ _ _ (by simpa using hr),
      List.getD_append _ _ _ _ (by simpa using hi)]
    simp [renameWire,hi,List.getD_eq_getElem?_getD]
  · rw [renameWire_high σ (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hi),
      List.getElem?_append_right (by simpa using Nat.le_of_not_lt hi)]
    simp

lemma renameCircuit_eval {n : ℕ} (σ : Fin n → Fin n) (C : Circuit)
    (x : Fin n → Bool) (tail : List Bool) :
    (renameCircuit σ C).eval (List.ofFn x ++ tail) =
      C.eval (List.ofFn (fun i => x (σ i)) ++ tail) := by
  exact fold_rename_relation σ C.gates _ _ (by simp) (by simp)
    (initial_read_relation σ x tail) C.output

lemma renameCircuit_size {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) :
    (renameCircuit σ C).size = C.size := by
  simp [renameCircuit,Circuit.size]

lemma renameCircuit_fanInTwo {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (fan : FanInTwo C) :
    FanInTwo (renameCircuit σ C) := by
  intro g hg
  change g ∈ C.gates.map (renameGate σ) at hg
  obtain ⟨a,ha,heq⟩ := List.mem_map.mp hg
  rw [← heq]
  obtain ⟨hop,hlen⟩ := fan a ha
  exact ⟨hop,by simpa [renameGate] using hlen⟩

lemma renameCircuit_notCount {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) :
    PEqualNP.NotBracket.notCount (renameCircuit σ C) = PEqualNP.NotBracket.notCount C := by
  simp only [PEqualNP.NotBracket.notCount,renameCircuit,List.filter_map,List.length_map]
  rfl

end PEqualNP.Outside.L_meta_2592.Automorphisms
