import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push
import Mathlib.Logic.Relation

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds

lemma empty_incidence_replacement (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D y =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  let D : Circuit := ⟨[], P + L⟩
  have eval_false (y : Fin (P + L) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (P + L) D y = false := by
    simp [D, PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires,
      List.getD_eq_default]
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.TopForm.IsAO2,
      PEqualNP.EdgeOwnership.AndOrOnly,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · intro y
    rw [eval_false]
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨p, l, hi, _, _⟩
    exact hI p l hi
  · simp [D, Circuit.size]
  · intro S hS
    have htrue := hS.1
    rw [eval_false] at htrue
    exact Bool.false_ne_true htrue |>.elim

end PEqualNP.Outside.L_meta_2585


-- The scan and vector lemmas follow L_meta_7344.

namespace PEqualNP.Outside.L_meta_2585.Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi


lemma scan_two {α : Type} (step : List α → Gate → α) (gs : List Gate) (g1 g2 : Gate)
    (w : List α) :
    scan step (gs ++ [g1, g2]) w =
      (scan step gs w ++ [step (scan step gs w) g1]) ++
        [step (scan step gs w ++ [step (scan step gs w) g1]) g2] := by
  rw [scan_append]
  rfl

lemma getD_init {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_last' {α : Type} (z : α) (l : List α) (b : α) (m : ℕ) (hm : l.length = m) :
    (l ++ [b]).getD m z = b := by
  subst hm
  exact getD_last z l b

-- One step of readVectors.
def rstep (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = scan (rstep k S) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq, scan_length]
  simp

lemma readVectors_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (a : ℕ) (ha : a < n) :
    (readVectors C n S k).getD a [] = leafVectors S k a := by
  rw [readVectors_eq, scan_prefix _ _ _ _ _ (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha]

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep (k : ℕ) (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

lemma mem_orFold (v : List ℕ) (ins : List (List (List ℕ))) (acc : List (List ℕ)) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins generalizing acc with
  | nil => simp
  | cons A ins ih =>
    simp only [List.foldl_cons, ih, mem_fold_insertNew, List.mem_cons, exists_eq_or_imp]
    tauto

lemma mem_rstep_or (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (v : List ℕ)
    (h : v ∈ R.getD i [] ∨ v ∈ R.getD j []) :
    v ∈ rstep k S R ⟨GateOp.or, [i, j]⟩ := by
  show v ∈ ([i, j].map fun t => R.getD t []).foldl (fun acc A => A.foldl insertNew acc) []
  rw [mem_orFold]
  right
  rcases h with h | h
  · exact ⟨R.getD i [], by simp, h⟩
  · exact ⟨R.getD j [], by simp, h⟩

lemma mem_rstep_and (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (u w : List ℕ)
    (hu : u ∈ R.getD i []) (hw : w ∈ R.getD j []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) w ∈ rstep k S R ⟨GateOp.and, [i, j]⟩ := by
  show _ ∈ andStep k (andStep k [S.map fun _ => 0] (R.getD i [])) (R.getD j [])
  rw [mem_andStep]
  exact ⟨_, (mem_andStep _ _ _ _).mpr ⟨_, by simp, u, hu, rfl⟩, w, hw, rfl⟩

lemma capAdd_map (k : ℕ) (S : List ℕ) (f g : ℕ → ℕ) :
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    simp only [capAdd, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]


def addGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩

lemma addGate_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate n C op a b).size = C.size + 1 := by
  simp [addGate, Circuit.size]

lemma addGate_run {α : Type} (step : List α → Gate → α) (n : ℕ) (C : Circuit)
    (op : GateOp) (a b : ℕ) (w : List α) (d : α) (hw : w.length = n) :
    (scan step (addGate n C op a b).gates w).getD (addGate n C op a b).output d =
      step (scan step C.gates w) ⟨op, [a, b]⟩ := by
  simp only [addGate, scan_append]
  change (scan step C.gates w ++ [step (scan step C.gates w) ⟨op, [a, b]⟩]).getD
    (n + C.gates.length) d = _
  exact getD_last' d _ _ _ (by rw [scan_length, hw])

lemma addGate_eval (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (addGate n C op a b).eval x =
      op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  exact addGate_run (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    n C op a b x false hx

lemma addGate_vectors (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (S : List ℕ) (k : ℕ) :
    (readVectors (addGate n C op a b) n S k).getD (addGate n C op a b).output [] =
      rstep k S (readVectors C n S k) ⟨op, [a, b]⟩ := by
  exact addGate_run (rstep k S) n C op a b _ [] (by simp)

lemma addGate_valid (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : a < n + C.size) (hb : b < n + C.size) :
    PEqualNP.TopForm.IsAO2 n (addGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [addGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.1 g hg
    · exact hop
  · intro j hj i hi
    by_cases hj' : j < C.gates.length
    · have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt (addGate n C op a b) j =
          PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        exact List.getD_append _ _ _ _ hj'
      rw [hgate] at hi
      exact hC.2.1 j hj' i hi
    · have heq : j = C.gates.length := by
        simp only [addGate, List.length_append, List.length_singleton] at hj
        omega
      subst j
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt
          (addGate n C op a b) C.gates.length = ⟨op, [a, b]⟩ := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, addGate,
          List.getD_eq_getElem?_getD]
      rw [hgate] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [addGate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.2.2 g hg
    · rfl

def orCircuit (n a : ℕ) : List ℕ → Circuit
  | [] => ⟨[], a⟩
  | b :: bs => let C := orCircuit n a bs; addGate n C GateOp.or C.output b

lemma orCircuit_size (n a : ℕ) (bs : List ℕ) : (orCircuit n a bs).size = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [orCircuit, addGate_size] using ih

lemma orCircuit_output (n a : ℕ) (bs : List ℕ) (ha : a < n) :
    (orCircuit n a bs).output < n + (orCircuit n a bs).size := by
  cases bs with
  | nil => exact ha
  | cons b bs => simp [orCircuit, addGate, Circuit.size]

lemma orCircuit_valid (n a : ℕ) (bs : List ℕ) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) : PEqualNP.TopForm.IsAO2 n (orCircuit n a bs) := by
  induction bs with
  | nil => simp [orCircuit, PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  | cons b bs ih =>
    apply addGate_valid
    · exact ih (fun c hc => hbs c (by simp [hc]))
    · exact Or.inr rfl
    · exact orCircuit_output n a bs ha
    · have := hbs b (by simp)
      omega

lemma wires_input (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (a : ℕ) (ha : a < n) : (C.wires x).getD a false = x.getD a false :=
  scan_prefix _ _ _ _ _ (by omega)

lemma orCircuit_eval (n a : ℕ) (bs : List ℕ) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) (x : List Bool) (hx : x.length = n) :
    (orCircuit n a bs).eval x = (x.getD a false || bs.any (fun b => x.getD b false)) := by
  induction bs with
  | nil => simp [orCircuit, Circuit.eval, Circuit.wires]
  | cons b bs ih =>
    rw [orCircuit, addGate_eval n _ _ _ _ x hx,
      wires_input n _ x hx b (hbs b (by simp))]
    change ((orCircuit n a bs).eval x || (x.getD b false || false)) = _
    rw [ih (fun c hc => hbs c (by simp [hc]))]
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

lemma orCircuit_vectors (n a : ℕ) (bs : List ℕ) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) (S : List ℕ) (k : ℕ) (b : ℕ) (hb : b ∈ a :: bs)
    (v : List ℕ) (hv : v ∈ leafVectors S k b) :
    v ∈ (readVectors (orCircuit n a bs) n S k).getD (orCircuit n a bs).output [] := by
  induction bs with
  | nil =>
    have heq : b = a := by simpa using hb
    subst b
    change v ∈ (readVectors (orCircuit n a []) n S k).getD a []
    rw [readVectors_leaf _ _ _ _ _ ha]
    exact hv
  | cons c bs ih =>
    rw [orCircuit, addGate_vectors]
    apply mem_rstep_or
    by_cases heq : b = c
    · right
      subst b
      rw [readVectors_leaf _ _ _ _ _ (hbs c (by simp))]
      exact hv
    · left
      apply ih (fun d hd => hbs d (by simp [hd]))
      simpa [heq, List.mem_cons, or_assoc] using hb

def starCircuit (n p a : ℕ) (bs : List ℕ) : Circuit :=
  let C := orCircuit n a bs
  addGate n C GateOp.and p C.output

lemma starCircuit_size (n p a : ℕ) (bs : List ℕ) :
    (starCircuit n p a bs).size = bs.length + 1 := by
  rw [starCircuit, addGate_size, orCircuit_size]

lemma starCircuit_valid (n p a : ℕ) (bs : List ℕ) (hp : p < n) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) : PEqualNP.TopForm.IsAO2 n (starCircuit n p a bs) := by
  apply addGate_valid
  · exact orCircuit_valid n a bs ha hbs
  · exact Or.inl rfl
  · omega
  · exact orCircuit_output n a bs ha

lemma starCircuit_eval (n p a : ℕ) (bs : List ℕ) (hp : p < n) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) (x : List Bool) (hx : x.length = n) :
    (starCircuit n p a bs).eval x =
      (x.getD p false && (x.getD a false || bs.any (fun b => x.getD b false))) := by
  rw [starCircuit, addGate_eval n _ _ _ _ x hx, wires_input n _ x hx p hp]
  change (x.getD p false && ((orCircuit n a bs).eval x && true)) = _
  rw [orCircuit_eval n a bs ha hbs x hx]
  simp

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (a : ℕ) :
    a ∈ setList S ↔ ∃ i ∈ S, i.val = a := by
  simp [setList]

lemma getD_setInput {n : ℕ} (S : Finset (Fin n)) (a : ℕ) (ha : a < n) :
    (List.ofFn (setInput S)).getD a false = decide ((⟨a, ha⟩ : Fin n) ∈ S) := by
  simp [List.getD_eq_getElem?_getD, ha, setInput]

lemma starCircuit_read_one (n p a : ℕ) (bs : List ℕ) (hp : p < n) (ha : a < n)
    (hbs : ∀ b ∈ bs, b < n) (hne : ∀ b ∈ a :: bs, p ≠ b) :
    IsReadK n (starCircuit n p a bs) 1 := by
  intro S hS
  have heval := hS.1
  change (starCircuit n p a bs).eval (List.ofFn (setInput S)) = true at heval
  rw [starCircuit_eval n p a bs hp ha hbs _ (by simp), Bool.and_eq_true] at heval
  have hpS : p ∈ setList S := by
    exact (mem_setList S p).2 ⟨⟨p, hp⟩,
      of_decide_eq_true (by simpa only [getD_setInput S p hp] using heval.1), rfl⟩
  obtain ⟨b, hb, hbtrue⟩ : ∃ b ∈ a :: bs,
      (List.ofFn (setInput S)).getD b false = true := by
    have ht := heval.2
    rw [Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · exact ⟨a, by simp, ht⟩
    · obtain ⟨b, hb, ht⟩ := List.any_eq_true.mp ht
      exact ⟨b, by simp [hb], ht⟩
  have hbn : b < n := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hbs b hb
  have hbS : b ∈ setList S := by
    exact (mem_setList S b).2 ⟨⟨b, hbn⟩,
      of_decide_eq_true (by simpa only [getD_setInput S b hbn] using hbtrue), rfl⟩
  have hpvec : ((setList S).map fun j => if j = p then min 1 (1 + 1) else 0) ∈
      (readVectors (orCircuit n a bs) n (setList S) 1).getD p [] := by
    rw [readVectors_leaf _ _ _ _ _ hp]
    simp [leafVectors, hpS]
  have hbvec : ((setList S).map fun j => if j = b then min 1 (1 + 1) else 0) ∈
      (readVectors (orCircuit n a bs) n (setList S) 1).getD (orCircuit n a bs).output [] := by
    apply orCircuit_vectors n a bs ha hbs (setList S) 1 b hb
    simp [leafVectors, hbS]
  unfold readsAtMost
  rw [List.any_eq_true]
  have hmem := mem_rstep_and 1 (setList S) (readVectors (orCircuit n a bs) n (setList S) 1)
    p (orCircuit n a bs).output _ _ hpvec hbvec
  refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0)
    ((setList S).map fun j => if j = p then min 1 (1 + 1) else 0))
    ((setList S).map fun j => if j = b then min 1 (1 + 1) else 0), ?_, ?_⟩
  · simpa only [starCircuit, addGate_vectors] using hmem
  · rw [capAdd_map, capAdd_map, List.all_eq_true]
    intro t ht
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    have hpb := hne b hb
    by_cases hjp : j = p
    · have hjb : j ≠ b := fun h => hpb (hjp.symm.trans h)
      simp [hjp, hjb, hpb]
    · by_cases hjb : j = b
      · subst j
        simp [hjp]
      · simp [hjp, hjb]

end PEqualNP.Outside.L_meta_2585.Star


-- The support invariant follows MetaComplexity.Helpers.Support.

namespace PEqualNP.Outside.L_meta_2585.Support

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma essential_card_le (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (A : Finset (Fin n))
    (hdep : ∀ i ∈ A, ∃ x : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n C (Function.update x i (!x i)) ≠
        PEqualNP.MetaComplexity.circuitFun n C x) :
    A.card ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hsub : A ⊆ S := by
    intro i hiA
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiA
    apply hx
    exact (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma cast_ne_nat {P L : ℕ} (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = P + l.val at hv
  omega

lemma incident_point_essential (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (p : Fin P) (l : Fin L) (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C
        (Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p))) ≠
      PEqualNP.MetaComplexity.circuitFun (P + L) C x := by
  let x : Fin (P + L) → Bool :=
    fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
  have hp : x (Fin.castAdd L p) = true := by simp [x]
  have hl : x (Fin.natAdd P l) = true := by simp [x]
  have htrue : PEqualNP.MetaComplexity.circuitFun (P + L) C x = true := by
    rw [hf, decide_eq_true_eq]
    exact ⟨p, l, hi, hp, hl⟩
  have hall (q : Fin P) :
      Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p)) (Fin.castAdd L q) = false := by
    rw [hp]
    by_cases heq : Fin.castAdd L q = Fin.castAdd L p
    · simp [heq]
    · rw [Function.update_of_ne heq]
      simp [x, heq, cast_ne_nat q l]
  have hfalse : PEqualNP.MetaComplexity.circuitFun (P + L) C
      (Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p))) = false := by
    rw [hf, decide_eq_false_iff_not]
    rintro ⟨q, m, _, hq, _⟩
    rw [hall q] at hq
    exact Bool.false_ne_true hq
  exact ⟨x, by rw [hfalse, htrue]; decide⟩

lemma incident_line_essential (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (p : Fin P) (l : Fin L) (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C
        (Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l))) ≠
      PEqualNP.MetaComplexity.circuitFun (P + L) C x := by
  let x : Fin (P + L) → Bool :=
    fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
  have hp : x (Fin.castAdd L p) = true := by simp [x]
  have hl : x (Fin.natAdd P l) = true := by simp [x]
  have htrue : PEqualNP.MetaComplexity.circuitFun (P + L) C x = true := by
    rw [hf, decide_eq_true_eq]
    exact ⟨p, l, hi, hp, hl⟩
  have hall (m : Fin L) :
      Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l)) (Fin.natAdd P m) = false := by
    rw [hl]
    by_cases heq : Fin.natAdd P m = Fin.natAdd P l
    · simp [heq]
    · rw [Function.update_of_ne heq]
      simp [x, heq, (cast_ne_nat p m).symm]
  have hfalse : PEqualNP.MetaComplexity.circuitFun (P + L) C
      (Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l))) = false := by
    rw [hf, decide_eq_false_iff_not]
    rintro ⟨q, m, _, _, hm⟩
    rw [hall m] at hm
    exact Bool.false_ne_true hm
  exact ⟨x, by rw [hfalse, htrue]; decide⟩

lemma incident_vertices_card_le (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hf : ∀ x : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    (Finset.univ.filter (fun v : Fin (P + L) => ∃ p : Fin P, ∃ l : Fin L,
      I p l ∧ (v = Fin.castAdd L p ∨ v = Fin.natAdd P l))).card ≤ C.size + 1 := by
  apply essential_card_le
  · intro g hg
    exact (hC.2.2 g hg).le
  · intro v hv
    obtain ⟨p, l, hi, hv⟩ := (Finset.mem_filter.mp hv).2
    rcases hv with rfl | rfl
    · exact incident_point_essential P L I C hf p l hi
    · exact incident_line_essential P L I C hf p l hi

end PEqualNP.Outside.L_meta_2585.Support


namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds

lemma single_point_replacement (L : ℕ) (I : Fin 1 → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (1 + L) C)
    (hf : ∀ y : Fin (1 + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (1 + L) C y =
        decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (1 + L) D ∧
      (∀ y : Fin (1 + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (1 + L) D y =
          decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (1 + L) D 1 := by
  let N : Finset (Fin L) := Finset.univ.filter (fun l => I 0 l)
  let ls : List (Fin L) := N.toList
  have memls (l : Fin L) : l ∈ ls ↔ I 0 l := by simp [ls, N]
  cases hls : ls with
  | nil =>
    apply empty_incidence_replacement 1 L I C
    intro p l hi
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    have hl := (memls l).2 hi
    simp [hls] at hl
  | cons a bs =>
    have hIa : I 0 a := (memls a).1 (by simp [hls])
    let ns := bs.map (fun l : Fin L => 1 + l.val)
    have hna : 1 + a.val < 1 + L := by omega
    have hns : ∀ b ∈ ns, b < 1 + L := by
      intro b hb
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
      omega
    let D := Star.starCircuit (1 + L) 0 (1 + a.val) ns
    have hDvalid : PEqualNP.TopForm.IsAO2 (1 + L) D :=
      Star.starCircuit_valid (1 + L) 0 (1 + a.val) ns (by omega) hna hns
    have hDread : PEqualNP.ReadK.IsReadK (1 + L) D 1 := by
      apply Star.starCircuit_read_one (1 + L) 0 (1 + a.val) ns (by omega) hna hns
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
        omega
    have hDfun (y : Fin (1 + L) → Bool) :
        PEqualNP.MetaComplexity.circuitFun (1 + L) D y =
          decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true) := by
      have getp : (List.ofFn y).getD 0 false = y (Fin.castAdd L (0 : Fin 1)) := by
        simp [List.getD_eq_getElem?_getD]
        rfl
      have getl (l : Fin L) : (List.ofFn y).getD (1 + l.val) false = y (Fin.natAdd 1 l) := by
        rw [List.getD_eq_getElem _ _ (by simpa using l.isLt), List.getElem_ofFn]
        rfl
      change (Star.starCircuit (1 + L) 0 (1 + a.val) ns).eval (List.ofFn y) = _
      rw [Star.starCircuit_eval (1 + L) 0 (1 + a.val) ns (by omega) hna hns _ (by simp), getp, getl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, ha | ⟨b, hb, hby⟩⟩
        · exact ⟨0, a, hIa, hp, ha⟩
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
          rw [getl] at hby
          exact ⟨0, l, (memls l).1 (by simp [hls, hl]), hp, hby⟩
      · rintro ⟨p, l, hi, hp, hl⟩
        have hpeq : p = 0 := Subsingleton.elim _ _
        subst p
        refine ⟨hp, ?_⟩
        have hmem : l ∈ a :: bs := by simpa only [hls] using (memls l).2 hi
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Or.inl hl
        · exact Or.inr ⟨1 + l.val, List.mem_map.mpr ⟨l, hmem, rfl⟩, by rw [getl]; exact hl⟩
    let A : Finset (Fin (1 + L)) :=
      insert (Fin.castAdd L (0 : Fin 1)) (N.image (Fin.natAdd 1))
    have hinj : Function.Injective (Fin.natAdd 1 : Fin L → Fin (1 + L)) := by
      intro l m h
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 1 + l.val = 1 + m.val at hv
      omega
    have hnot : Fin.castAdd L (0 : Fin 1) ∉ N.image (Fin.natAdd 1) := by
      intro h
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp h
      exact Support.cast_ne_nat (0 : Fin 1) l hl.symm
    have hAcard : A.card = N.card + 1 := by
      rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]
    have hbound : A.card ≤ C.size + 1 := by
      apply Support.essential_card_le
      · intro g hg
        exact (hC.2.2 g hg).le
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Support.incident_point_essential 1 L I C hf 0 a hIa
        · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
          exact Support.incident_line_essential 1 L I C hf 0 l ((Finset.mem_filter.mp hl).2)
    have hNbound : N.card ≤ C.size := by rw [hAcard] at hbound; omega
    have hlen : bs.length + 1 = N.card := by
      have h := congrArg List.length hls
      simpa [ls] using h.symm
    refine ⟨D, hDvalid, hDfun, ?_, hDread⟩
    calc
      D.size = bs.length + 1 := by simp [D, Star.starCircuit_size, ns]
      _ = N.card := hlen
      _ ≤ C.size := hNbound

end PEqualNP.Outside.L_meta_2585

namespace PEqualNP.Outside.L_meta_2585_aux

lemma rectangle_has_thin_side {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hI : ∀ p ∈ A, ∀ l ∈ B, I p l) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  classical
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    by_contra hll'
    have hA' : ¬ ∀ p ∈ A, ∀ p' ∈ A, p = p' :=
      fun h => hA (Finset.card_le_one.mpr h)
    push Not at hA'
    obtain ⟨p, hp, p', hp', hpp'⟩ := hA'
    exact hfour p p' l l' hpp' hll'
      ⟨hI p hp l hl, hI p hp l' hl', hI p' hp' l hl, hI p' hp' l' hl'⟩

lemma rectangle_is_star {P L : ℕ} (I : Fin P → Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hI : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    (∃ p, A = {p}) ∨ (∃ l, B = {l}) := by
  obtain h | h := rectangle_has_thin_side I hfour A B hI
  · left
    apply Finset.card_eq_one.mp
    have := Finset.card_pos.mpr hA
    omega
  · right
    apply Finset.card_eq_one.mp
    have := Finset.card_pos.mpr hB
    omega

lemma neighborhood_inter_card_le_one {P L : ℕ} (I : Fin P → Fin L → Prop)
    [DecidableRel I]
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin P) (hpp' : p ≠ p') :
    ((Finset.univ.filter (I p)) ∩ (Finset.univ.filter (I p'))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  by_contra hll'
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hl hl'
  exact hfour p p' l l' hpp' hll' ⟨hl.1, hl'.1, hl.2, hl'.2⟩

end PEqualNP.Outside.L_meta_2585_aux

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma prime_incidence_iff (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧
        S = {Fin.castAdd L p, Fin.natAdd P l} := by
  constructor
  · intro hS
    have hs := hS.1
    rw [hC] at hs
    obtain ⟨p, l, hi, hp, hl⟩ := of_decide_eq_true hs
    have hp' : Fin.castAdd L p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd P l ∈ S := of_decide_eq_true hl
    refine ⟨p, l, hi, ?_⟩
    have hsub : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊆ S := by
      simpa using (Finset.insert_subset_iff.mpr ⟨hp', Finset.singleton_subset_iff.mpr hl'⟩)
    by_contra hne
    have hproper : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hz := hS.2 _ (Finset.mem_ssubsets.mpr hproper)
    rw [hC] at hz
    have ht : (∃ p' : Fin P, ∃ l' : Fin L, I p' l' ∧
        setInput ({Fin.castAdd L p, Fin.natAdd P l} : Finset _)
          (Fin.castAdd L p') = true ∧
        setInput ({Fin.castAdd L p, Fin.natAdd P l} : Finset _)
          (Fin.natAdd P l') = true) := by
      exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
    simpa [ht] using hz
  · rintro ⟨p, l, hi, rfl⟩
    constructor
    · rw [hC]
      apply decide_eq_true
      exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
    · intro T hT
      rw [hC, decide_eq_false_iff_not]
      rintro ⟨p', l', hi', hp', hl'⟩
      have hsub := (Finset.mem_ssubsets.mp hT).1
      have hpT : Fin.castAdd L p' ∈ T := of_decide_eq_true hp'
      have hlT : Fin.natAdd P l' ∈ T := of_decide_eq_true hl'
      have hpPair := hsub hpT
      have hlPair := hsub hlT
      have hple : (Fin.castAdd L p' : Fin (P + L)) ≠ Fin.natAdd P l := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have hlpe : (Fin.natAdd P l' : Fin (P + L)) ≠ Fin.castAdd L p := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have heqp : Fin.castAdd L p' = Fin.castAdd L p := by
        simpa [Finset.mem_insert, Finset.mem_singleton, hple] using hpPair
      have heql : Fin.natAdd P l' = Fin.natAdd P l := by
        simpa [Finset.mem_insert, Finset.mem_singleton, hlpe] using hlPair
      have hback : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊆ T := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨heqp ▸ hpT, heql ▸ hlT⟩
      exact (Finset.mem_ssubsets.mp hT).2 hback

lemma read_one_of_incidence_edges (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (hread : ∀ p : Fin P, ∀ l : Fin L, I p l →
      readsAtMost C (P + L) (setList {Fin.castAdd L p, Fin.natAdd P l}) 1 = true) :
    IsReadK (P + L) C 1 := by
  intro S hS
  obtain ⟨p, l, hi, rfl⟩ := (prime_incidence_iff P L I C hC S).mp hS
  exact hread p l hi

end PEqualNP.Outside.L_meta_2585

-- The lifting argument is adapted from the checked L-meta-4295.
-- The final lemmas combine its normalization with size and function preservation.

namespace PEqualNP.Outside.L_meta_2585.normalization

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

lemma eraseRedirect_lt (n m p j u : ℕ) (hp : p < n + m) (hmj : m ≤ j) (hu : u < n + (j + 1)) :
    eraseRedirect n m p u < n + j := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_gates_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  simp [eraseGate, hm]
  omega

lemma liftAt_gates_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  simp [liftAt, eraseGate_gates_length n C m p hm]
  omega

lemma eraseGate_output_lt (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hout : C.output < n + C.gates.length) :
    (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length := by
  rw [eraseGate_gates_length n C m p hm]
  simp only [eraseGate, hm, ↓reduceIte]
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_getElem_lt (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hjm : j < m) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] = C.gates[j]'(by omega) := by
  have htake : j < (C.gates.take m).length := by simp; omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_left htake, List.getElem_take]

lemma eraseGate_getElem_ge (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hmj : m ≤ j) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] =
      ⟨(C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).op,
        (C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).inputs.map
          (eraseRedirect n m p)⟩ := by
  have hlen := eraseGate_gates_length n C m p hm
  have htake : (C.gates.take m).length = m := by simp; omega
  have hidx : m + 1 + (j - m) = j + 1 := by omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_right (by omega)]
  simp only [htake, List.getElem_map, List.getElem_drop, hidx]

lemma eraseGate_isAO2 (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  rcases hAO with ⟨hAO_op, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hAO_op g (List.mem_of_mem_take h1)
    · exact hAO_op g0 (List.mem_of_mem_drop hg0)
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    by_cases hjm : j < m
    · rw [eraseGate_getElem_lt n C m p j hm hjm hj] at hi
      have := hRB j (by omega) i
      rw [gateAt_eq_getElem C j (by omega)] at this
      exact this hi
    · have hmj : m ≤ j := by omega
      have hlen := eraseGate_gates_length n C m p hm
      rw [eraseGate_getElem_ge n C m p j hm hmj hj] at hi
      simp only [List.mem_map] at hi
      rcases hi with ⟨u, hu, rfl⟩
      have hu_lt : u < n + (j + 1) := by
        have := hRB (j + 1) (by omega) u
        rw [gateAt_eq_getElem C (j + 1) (by omega)] at this
        exact this hu
      exact eraseRedirect_lt n m p j u hp hmj hu_lt
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hLen2 g (List.mem_of_mem_take h1)
    · simp [hLen2 g0 (List.mem_of_mem_drop hg0)]

lemma liftAt_isAO2 (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m) :
    IsAO2 n (liftAt n C m p h) := by
  have hE := eraseGate_isAO2 n C m p hAO hm hp
  have hEout := eraseGate_output_lt n C m p hm hp hout
  have hElen := eraseGate_gates_length n C m p hm
  rcases hE with ⟨hE_op, hE_RB, hE_len2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_op g hg
    · exact Or.inr rfl
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [liftAt, List.length_append, List.length_singleton] at hj
    by_cases hjE : j < (eraseGate n C m p).gates.length
    · have hg : (liftAt n C m p h).gates[j] = (eraseGate n C m p).gates[j] := by
        simp only [liftAt]
        rw [List.getElem_append_left hjE]
      rw [hg] at hi
      have := hE_RB j hjE i
      rw [gateAt_eq_getElem _ j hjE] at this
      exact this hi
    · have hj_eq : j = (eraseGate n C m p).gates.length := by omega
      have hg : (liftAt n C m p h).gates[j] = ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
        simp only [liftAt]
        rw [List.getElem_append_right (by omega)]
        have : j - (eraseGate n C m p).gates.length = 0 := by omega
        simp [this]
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · omega
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_len2 g hg
    · rfl

lemma eraseGate_wires_prefix (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + m) :
    ((eraseGate n C m p).wires x).getD k false = (C.wires x).getD k false := by
  change (evalGates (eraseGate n C m p).gates x).getD k false = (evalGates C.gates x).getD k false
  have hC : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
  have hE : (eraseGate n C m p).gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
    simp [eraseGate, hm]
  have hlen : (evalGates (C.gates.take m) x).length = n + m := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hl : (evalGates (eraseGate n C m p).gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    rw [hE, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  have hr : (evalGates C.gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    conv_lhs => rw [hC, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  rw [hl, hr]

lemma liftAt_wires_lt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + (eraseGate n C m p).gates.length) :
    ((liftAt n C m p h).wires x).getD k false = ((eraseGate n C m p).wires x).getD k false := by
  change (evalGates ((eraseGate n C m p).gates ++ _) x).getD k false =
    (evalGates (eraseGate n C m p).gates x).getD k false
  rw [evalGates_append]
  have hlen : (evalGates (eraseGate n C m p).gates x).length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  exact evalGates_getD_lt _ _ k (by omega)

lemma liftAt_eval_formula (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (liftAt n C m p h).eval x =
      ((eraseGate n C m p).eval x || ((eraseGate n C m p).wires x).getD h false) := by
  unfold Circuit.eval liftAt
  change (evalGates ((eraseGate n C m p).gates ++ [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]) x).getD
      (n + (eraseGate n C m p).gates.length) false =
    ((evalGates (eraseGate n C m p).gates x).getD (eraseGate n C m p).output false ||
      (evalGates (eraseGate n C m p).gates x).getD h false)
  rw [evalGates_append]
  set wE := evalGates (eraseGate n C m p).gates x
  have hwE : wE.length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hwE]
  simp [List.getD_eq_getElem?_getD, GateOp.eval]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma gate_m_val (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hRB : ReadsBack n C) (hm : m < C.gates.length)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    (C.wires x).getD (n + m) false = ((C.wires x).getD p false || (C.wires x).getD h false) := by
  rw [wires_getD_gate n C hRB x hx m hm]
  have hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hgate with h1 | h1
    · left; simpa [hm] using h1
    · right; simpa [hm] using h1
  rcases hg with h1 | h1
  · rw [h1]; simp [GateOp.eval]
  · rw [h1]; simp [GateOp.eval, Bool.or_comm]

lemma eraseGate_wires_le (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false = true →
      (C.wires x).getD (if k < n + m then k else k + 1) false = true := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      rwa [eraseGate_wires_prefix n C m p hm x hx k hkm] at htrue
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj] at htrue ⊢
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE] at htrue
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE] at htrue
      rw [List.map_map] at htrue
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      have hop : (C.gates[j + 1]).op = GateOp.and ∨ (C.gates[j + 1]).op = GateOp.or :=
        hAO.1 _ (List.getElem_mem hjC)
      refine gateOp_eval_mono _ hop _ _ _ ?_ htrue
      intro u hu huE
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply] at huE
      unfold eraseRedirect at huE
      split_ifs at huE with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx]
        rw [eraseGate_wires_prefix n C m p hm x hx p hp] at huE
        rw [huE]
        rfl
      · have hstep := ih (u - 1) (by omega) (by omega) huE
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        rwa [eraseGate_wires_prefix n C m p hm x hx u hult] at huE

lemma eraseGate_wires_eq_of_h_false (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) (hfalse : (C.wires x).getD h false = false) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false =
      (C.wires x).getD (if k < n + m then k else k + 1) false := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      exact eraseGate_wires_prefix n C m p hm x hx k hkm
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj]
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE]
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE]
      rw [List.map_map]
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx, hfalse, Bool.or_false]
        exact eraseGate_wires_prefix n C m p hm x hx p hp
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult

lemma liftAt_eval_eq (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (v : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  rw [liftAt_eval_formula n C m p h (List.ofFn v) hx]
  rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx h hh]
  cases hb : (C.wires (List.ofFn v)).getD h false
  · rw [Bool.or_false]
    unfold Circuit.eval
    have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
      simp [eraseGate, hm]
    rw [hEout]
    have hElen := eraseGate_gates_length n C m p hm
    unfold eraseRedirect
    split_ifs with heq hgt
    · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx, hb, Bool.or_false]
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp
    · have hstep := eraseGate_wires_eq_of_h_false n C m p h hAO hm hp hgate
        (List.ofFn v) hx hb (C.output - 1) (by omega)
      have hnotlt : ¬ (C.output - 1 < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hstep
      have ho1 : C.output - 1 + 1 = C.output := by omega
      rwa [ho1] at hstep
    · have holt : C.output < n + m := by omega
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt
  · rw [Bool.or_true]
    exact (hBelowH v hb).symm

noncomputable def belowCount (n : ℕ) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))).card

lemma belowCount_le (n : ℕ) (C : Circuit) : belowCount n C ≤ C.gates.length := by
  unfold belowCount
  calc ((Finset.range C.gates.length).filter _).card
      ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
    _ = C.gates.length := Finset.card_range _

lemma belowCount_lt_liftAt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (hNotBelowP : ¬ WireBelowOutput n C p) :
    belowCount n C < belowCount n (liftAt n C m p h) := by
  classical
  have hElen : (eraseGate n C m p).gates.length = C.gates.length - 1 :=
    eraseGate_gates_length n C m p hm
  have hC'len : (liftAt n C m p h).gates.length = C.gates.length :=
    liftAt_gates_length n C m p h hm
  have heval : ∀ v : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) :=
    liftAt_eval_eq n C m p h hAO hout hm hp hh hgate hBelowH
  set S := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))
  set S' := (Finset.range (liftAt n C m p h).gates.length).filter
    (fun j => WireBelowOutput n (liftAt n C m p h) (n + j))
  have hm_not : m ∉ S := by
    intro hmS
    have hBm : WireBelowOutput n C (n + m) := (Finset.mem_filter.mp hmS).2
    apply hNotBelowP
    intro v hpv
    apply hBm v
    rw [gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) List.length_ofFn, hpv]
    rfl
  have hlast_mem : (eraseGate n C m p).gates.length ∈ S' := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro v hv
    exact hv
  let f : ℕ → ℕ := fun j => if j < m then j else j - 1
  have hsub : S.image f ⊆ S'.erase (eraseGate n C m p).gates.length := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hjS, rfl⟩
    have hj_ne : j ≠ m := fun heq => hm_not (heq ▸ hjS)
    rcases Finset.mem_filter.mp hjS with ⟨hj_rng, hBj⟩
    have hj_lt : j < C.gates.length := Finset.mem_range.mp hj_rng
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    by_cases hjm : j < m
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
      rwa [eraseGate_wires_prefix n C m p hm (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega)] at hv
      have hle := eraseGate_wires_le n C m p h hAO hm hp hgate
        (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega) hv
      have hnotlt : ¬ (n + (j - 1) < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hle
      have hj1 : n + (j - 1) + 1 = n + j := by omega
      rwa [hj1] at hle
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro j1 hj1 j2 hj2 hfeq
    have h1ne : j1 ≠ m := fun heq => hm_not (heq ▸ hj1)
    have h2ne : j2 ≠ m := fun heq => hm_not (heq ▸ hj2)
    simp only [f] at hfeq
    split_ifs at hfeq <;> omega
  have hcard1 : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  have hcard2 : (S.image f).card ≤ (S'.erase (eraseGate n C m p).gates.length).card :=
    Finset.card_le_card hsub
  have hcard3 : (S'.erase (eraseGate n C m p).gates.length).card + 1 = S'.card :=
    Finset.card_erase_add_one hlast_mem
  show S.card < S'.card
  omega


lemma fixedpoint_exists : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hAO hout
  have main : ∀ k : ℕ, ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C0 →
      C0.output < n + C0.gates.length →
      C0.gates.length - PEqualNP.Outside.L_meta_2585.normalization.belowCount n C0 = k →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift n) C0 C' ∧
        ∀ m < C'.gates.length, ∀ a b : ℕ,
          C'.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C' b → PEqualNP.CircuitMoves.WireBelowOutput n C' a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C' a → PEqualNP.CircuitMoves.WireBelowOutput n C' b) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C0 hAO0 hout0 hk0
      by_cases hNF : ∀ m < C0.gates.length, ∀ a b : ℕ,
          C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b → PEqualNP.CircuitMoves.WireBelowOutput n C0 a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C0 a → PEqualNP.CircuitMoves.WireBelowOutput n C0 b)
      · exact ⟨C0, Relation.ReflTransGen.refl, hNF⟩
      · push Not at hNF
        rcases hNF with ⟨m, hm, a, b, hgate, hbad⟩
        have ha_lt : a < n + m := by
          have := hAO0.2.1 m hm a
          rw [PEqualNP.Outside.L_meta_2585.normalization.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hb_lt : b < n + m := by
          have := hAO0.2.1 m hm b
          rw [PEqualNP.Outside.L_meta_2585.normalization.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hstep : ∃ p h : ℕ, p < n + m ∧ h < n + m ∧ n ≤ h ∧
            (C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p, h] } ∨
              C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [h, p] }) ∧
            PEqualNP.CircuitMoves.WireBelowOutput n C0 h ∧
            ¬ PEqualNP.CircuitMoves.WireBelowOutput n C0 p := by
          by_cases h1 : n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b →
              PEqualNP.CircuitMoves.WireBelowOutput n C0 a
          · rcases hbad h1 with ⟨hna, hBa, hNb⟩
            exact ⟨b, a, hb_lt, ha_lt, hna, Or.inr hgate, hBa, hNb⟩
          · push Not at h1
            rcases h1 with ⟨hnb, hBb, hNa⟩
            exact ⟨a, b, ha_lt, hb_lt, hnb, Or.inl hgate, hBb, hNa⟩
        rcases hstep with ⟨p, h, hp, hh, hnh, hgm, hBh, hNp⟩
        have hLift : PEqualNP.CircuitMoves.Lift n C0 (PEqualNP.CircuitMoves.liftAt n C0 m p h) :=
          ⟨m, hm, p, hp, h, hh, hnh, hgm, hBh, rfl⟩
        have hAO1 := PEqualNP.Outside.L_meta_2585.normalization.liftAt_isAO2 n C0 m p h hAO0 hout0 hm hp hh
        have hlen1 := PEqualNP.Outside.L_meta_2585.normalization.liftAt_gates_length n C0 m p h hm
        have hElen := PEqualNP.Outside.L_meta_2585.normalization.eraseGate_gates_length n C0 m p hm
        have hout1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).output <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length := by
          change n + (PEqualNP.CircuitMoves.eraseGate n C0 m p).gates.length <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length
          omega
        have hlt := PEqualNP.Outside.L_meta_2585.normalization.belowCount_lt_liftAt n C0 m p h hAO0 hout0 hm hp hh hgm hBh hNp
        have hle1 := PEqualNP.Outside.L_meta_2585.normalization.belowCount_le n (PEqualNP.CircuitMoves.liftAt n C0 m p h)
        have hk1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length -
            PEqualNP.Outside.L_meta_2585.normalization.belowCount n (PEqualNP.CircuitMoves.liftAt n C0 m p h) < k := by
          omega
        obtain ⟨C', hR, hNF'⟩ := ih _ hk1 (PEqualNP.CircuitMoves.liftAt n C0 m p h) hAO1 hout1 rfl
        exact ⟨C', Relation.ReflTransGen.head hLift hR, hNF'⟩
  exact main _ C hAO hout rfl

lemma lift_step (n : ℕ) (C D : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hL : PEqualNP.CircuitMoves.Lift n C D) :
    PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.gates.length ∧
    D.size = C.size ∧ PEqualNP.MetaComplexity.circuitFun n D =
      PEqualNP.MetaComplexity.circuitFun n C := by
  obtain ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩ := hL
  refine ⟨liftAt_isAO2 n C m p h hAO hout hm hp hh, ?_, ?_, ?_⟩
  · simp [PEqualNP.CircuitMoves.liftAt]
  · exact liftAt_gates_length n C m p h hm
  · funext x
    exact liftAt_eval_eq n C m p h hAO hout hm hp hh hgate hbelow x

lemma lift_chain (n : ℕ) (C D : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hCD : Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift n) C D) :
    PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.gates.length ∧
    D.size = C.size ∧ PEqualNP.MetaComplexity.circuitFun n D =
      PEqualNP.MetaComplexity.circuitFun n C := by
  induction hCD with
  | refl => exact ⟨hAO, hout, rfl, rfl⟩
  | @tail D E hCD hDE ih =>
    obtain ⟨hE, houtE, hsizeE, hfunE⟩ := lift_step n D E ih.1 ih.2.1 hDE
    exact ⟨hE, houtE, hsizeE.trans ih.2.2.1, hfunE.trans ih.2.2.2⟩

lemma normalized_exists (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.gates.length ∧ D.size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      ∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ →
        (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n D b →
          PEqualNP.CircuitMoves.WireBelowOutput n D a) ∧
        (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n D a →
          PEqualNP.CircuitMoves.WireBelowOutput n D b) := by
  obtain ⟨D, hCD, hfix⟩ := fixedpoint_exists n C hAO hout
  obtain ⟨hD, houtD, hsize, hfun⟩ := lift_chain n C D hAO hout hCD
  exact ⟨D, hD, houtD, hsize, hfun, hfix⟩

lemma input_not_below (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (i : Fin n)
    (hzero : PEqualNP.MetaComplexity.circuitFun n C (fun j => decide (j = i)) = false) :
    ¬ PEqualNP.CircuitMoves.WireBelowOutput n C i := by
  intro hbelow
  have hw : (C.wires (List.ofFn (fun j : Fin n => decide (j = i)))).getD i false = true := by
    change (evalGates C.gates (List.ofFn (fun j : Fin n => decide (j = i)))).getD i false = true
    have hi : i.val < (List.ofFn (fun j : Fin n => decide (j = i))).length := by simp
    rw [evalGates_getD_lt _ _ _ hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    simp
  have hf := hbelow (fun j => decide (j = i)) hw
  change PEqualNP.MetaComplexity.circuitFun n C (fun j => decide (j = i)) = true at hf
  rw [hzero] at hf
  cases hf

lemma normalized_or_uniform (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hzero : ∀ i : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun j => decide (j = i)) = false) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n D ∧ D.output < n + D.gates.length ∧ D.size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      ∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ →
        (PEqualNP.CircuitMoves.WireBelowOutput n D a ↔
          PEqualNP.CircuitMoves.WireBelowOutput n D b) := by
  obtain ⟨D, hD, houtD, hsize, hfun, hfix⟩ := normalized_exists n C hAO hout
  refine ⟨D, hD, houtD, hsize, hfun, ?_⟩
  intro m hm a b hgate
  have hge : ∀ w, PEqualNP.CircuitMoves.WireBelowOutput n D w → n ≤ w := by
    intro w hw
    by_contra hn
    have hwlt : w < n := by omega
    apply input_not_below n D ⟨w, hwlt⟩ (by rw [hfun]; exact hzero ⟨w, hwlt⟩)
    exact hw
  constructor
  · intro ha
    exact (hfix m hm a b hgate).2 (hge a ha) ha
  · intro hb
    exact (hfix m hm a b hgate).1 (hge b hb) hb

lemma incidence_singleton (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (i : Fin (P + L)) :
    decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
      decide (Fin.castAdd L p = i) = true ∧ decide (Fin.natAdd P l = i) = true) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨p, l, _, hp, hl⟩
  have hp' : Fin.castAdd L p = i := of_decide_eq_true hp
  have hl' : Fin.natAdd P l = i := of_decide_eq_true hl
  have heq := congrArg Fin.val (hp'.trans hl'.symm)
  change p.val = P + l.val at heq
  have hbound := p.isLt
  omega

lemma normalized_incidence (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hout : C.output < P + L + C.gates.length)
    (hfun : ∀ z : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (P + L) D ∧ D.size = C.size ∧
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧
      ∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩ →
        (PEqualNP.CircuitMoves.WireBelowOutput (P + L) D a ↔
          PEqualNP.CircuitMoves.WireBelowOutput (P + L) D b) := by
  obtain ⟨D, hD, _, hsize, heq, hfix⟩ := normalized_or_uniform (P + L) C hAO hout
    (fun i => by rw [hfun]; exact incidence_singleton P L I i)
  refine ⟨D, hD, hsize, ?_, hfix⟩
  intro z
  rw [heq]
  exact hfun z

lemma output_lt_of_true (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (x : Fin n → Bool) (htrue : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    change (evalGates C.gates (List.ofFn x)).length = n + C.gates.length
    rw [evalGates_length, List.length_ofFn]
  by_contra hnot
  have hfalse : PEqualNP.MetaComplexity.circuitFun n C x = false := by
    change (C.wires (List.ofFn x)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [hlen]; omega)
  rw [htrue] at hfalse
  cases hfalse

lemma incidence_output_lt (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hne : ∃ p l, I p l)
    (hfun : ∀ z : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    C.output < P + L + C.gates.length := by
  apply output_lt_of_true (P + L) C (fun _ => true)
  rw [hfun]
  apply decide_eq_true_eq.mpr
  obtain ⟨p, l, hp⟩ := hne
  exact ⟨p, l, hp, rfl, rfl⟩

end PEqualNP.Outside.L_meta_2585.normalization

namespace PEqualNP.Outside.L_meta_2585_aux.Multilinear

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi


lemma scan_two {α : Type} (step : List α → Gate → α) (gs : List Gate) (g1 g2 : Gate)
    (w : List α) :
    scan step (gs ++ [g1, g2]) w =
      (scan step gs w ++ [step (scan step gs w) g1]) ++
        [step (scan step gs w ++ [step (scan step gs w) g1]) g2] := by
  rw [scan_append]
  rfl

lemma getD_init {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_last' {α : Type} (z : α) (l : List α) (b : α) (m : ℕ) (hm : l.length = m) :
    (l ++ [b]).getD m z = b := by
  subst hm
  exact getD_last z l b

def rstep (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = scan (rstep k S) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq, scan_length]
  simp

lemma readVectors_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (a : ℕ) (ha : a < n) :
    (readVectors C n S k).getD a [] = leafVectors S k a := by
  rw [readVectors_eq, scan_prefix _ _ _ _ _ (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha]

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep (k : ℕ) (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

lemma mem_orFold (v : List ℕ) (ins : List (List (List ℕ))) (acc : List (List ℕ)) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins generalizing acc with
  | nil => simp
  | cons A ins ih =>
    simp only [List.foldl_cons, ih, mem_fold_insertNew, List.mem_cons, exists_eq_or_imp]
    tauto

lemma mem_rstep_or (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (v : List ℕ)
    (h : v ∈ R.getD i [] ∨ v ∈ R.getD j []) :
    v ∈ rstep k S R ⟨GateOp.or, [i, j]⟩ := by
  show v ∈ ([i, j].map fun t => R.getD t []).foldl (fun acc A => A.foldl insertNew acc) []
  rw [mem_orFold]
  right
  rcases h with h | h
  · exact ⟨R.getD i [], by simp, h⟩
  · exact ⟨R.getD j [], by simp, h⟩

lemma mem_rstep_and (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (u w : List ℕ)
    (hu : u ∈ R.getD i []) (hw : w ∈ R.getD j []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) w ∈ rstep k S R ⟨GateOp.and, [i, j]⟩ := by
  show _ ∈ andStep k (andStep k [S.map fun _ => 0] (R.getD i [])) (R.getD j [])
  rw [mem_andStep]
  exact ⟨_, (mem_andStep _ _ _ _).mpr ⟨_, by simp, u, hu, rfl⟩, w, hw, rfl⟩

lemma capAdd_map (k : ℕ) (S : List ℕ) (f g : ℕ → ℕ) :
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    simp only [capAdd, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

open PEqualNP.SyntacticMultilinear PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def vvec {n : ℕ} (S T : Finset (Fin n)) : List ℕ :=
  (setList S).map fun j => if j ∈ T.image Fin.val then 1 else 0

def sstep {n : ℕ} (U : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  g.inputs.foldr (fun w acc => U.getD w ∅ ∪ acc) ∅

def bstep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma vvec_union {n : ℕ} (S A B : Finset (Fin n)) (hab : Disjoint A B) :
    capAdd 1 (vvec S A) (vvec S B) = vvec S (A ∪ B) := by
  have hd : Disjoint (A.image Fin.val) (B.image Fin.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hj
    have e : b = a := Fin.ext hba
    subst b
    exact Finset.disjoint_left.mp hab ha hb
  rw [vvec, vvec, capAdd_map]
  unfold vvec
  apply List.map_congr_left
  intro j hj
  by_cases ha : j ∈ A.image Fin.val <;> by_cases hb : j ∈ B.image Fin.val
  · exact (Finset.disjoint_left.mp hd ha hb).elim
  · simp [Finset.image_union, ha, hb]
  · simp [Finset.image_union, ha, hb]
  · simp [Finset.image_union, ha, hb]

lemma cap_zero_vvec {n : ℕ} (S A : Finset (Fin n)) :
    capAdd 1 ((setList S).map fun _ => 0) (vvec S A) = vvec S A := by
  unfold vvec
  rw [capAdd_map]
  apply List.map_congr_left
  intro j hj
  by_cases h : j ∈ A.image Fin.val <;> simp [h]

def Inv {n : ℕ} (S : Finset (Fin n)) (U : List (Finset (Fin n)))
    (w : List Bool) (R : List (List (List ℕ))) : Prop :=
  U.length = w.length ∧ R.length = w.length ∧
  ∀ i, w.getD i false = true →
    ∃ T : Finset (Fin n), T ⊆ U.getD i ∅ ∧ vvec S T ∈ R.getD i []

lemma snoc_other {α : Type} (l : List α) (a d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  by_cases h : i < l.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma inv_step {n : ℕ} (S : Finset (Fin n)) (U : List (Finset (Fin n)))
    (w : List Bool) (R : List (List (List ℕ))) (a b : ℕ) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hdis : op = GateOp.and → Disjoint (U.getD a ∅) (U.getD b ∅))
    (hi : Inv S U w R) :
    Inv S (U ++ [sstep U ⟨op, [a,b]⟩])
      (w ++ [bstep w ⟨op, [a,b]⟩])
      (R ++ [rstep 1 (setList S) R ⟨op, [a,b]⟩]) := by
  obtain ⟨hu, hr, hi⟩ := hi
  refine ⟨by simp [hu], by simp [hr], ?_⟩
  intro i hval
  by_cases heq : i = w.length
  · subst i
    rw [getD_last] at hval
    rw [← hu, getD_last, hu, ← hr, getD_last]
    rcases hop with rfl | rfl
    · have hbits : w.getD a false = true ∧ w.getD b false = true := by
        simpa [bstep, GateOp.eval] using hval
      obtain ⟨A, hA, hvA⟩ := hi a hbits.1
      obtain ⟨B, hB, hvB⟩ := hi b hbits.2
      refine ⟨A ∪ B, ?_, ?_⟩
      · simpa [sstep] using Finset.union_subset_union hA hB
      · have hd : Disjoint A B := (hdis rfl).mono hA hB
        have hm := mem_rstep_and 1 (setList S) R a b (vvec S A) (vvec S B) hvA hvB
        rw [cap_zero_vvec, vvec_union S A B hd] at hm
        exact hm
    · have hbits : w.getD a false = true ∨ w.getD b false = true := by
        simpa [bstep, GateOp.eval] using hval
      rcases hbits with ha | hb
      · obtain ⟨A, hA, hvA⟩ := hi a ha
        refine ⟨A, ?_, mem_rstep_or 1 (setList S) R a b _ (Or.inl hvA)⟩
        simpa [sstep] using hA.trans (Finset.subset_union_left)
      · obtain ⟨B, hB, hvB⟩ := hi b hb
        refine ⟨B, ?_, mem_rstep_or 1 (setList S) R a b _ (Or.inr hvB)⟩
        simpa [sstep] using hB.trans (Finset.subset_union_right)
  · rw [snoc_other _ _ _ _ heq] at hval
    rw [snoc_other _ _ _ _ (by omega), snoc_other _ _ _ _ (by omega)]
    exact hi i hval

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (a : ℕ) :
    a ∈ setList S ↔ ∃ i ∈ S, i.val = a := by
  simp [setList]

lemma inv_inputs {n : ℕ} (S : Finset (Fin n)) :
    Inv S (List.ofFn fun i : Fin n => ({i} : Finset (Fin n)))
      (List.ofFn (setInput S)) ((List.range n).map (leafVectors (setList S) 1)) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  have hin : i < n := by
    by_contra h
    rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi
  have his : (⟨i,hin⟩ : Fin n) ∈ S := by
    simpa [List.getD_eq_getElem?_getD, hin, setInput] using hi
  have hm : i ∈ setList S := mem_setList S i |>.mpr ⟨⟨i,hin⟩,his,rfl⟩
  refine ⟨{⟨i,hin⟩}, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD, hin]
  · simp [List.getD_eq_getElem?_getD, hin, leafVectors, hm, vvec]

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate)
    (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma scan_take_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate)
    (w : List α) (d : α) (j i : ℕ) (hi : i < w.length + (gs.take j).length) :
    (scan step gs w).getD i d = (scan step (gs.take j) w).getD i d := by
  calc
    _ = (scan step (gs.drop j) (scan step (gs.take j) w)).getD i d := by
      rw [← scan_append, List.take_append_drop]
    _ = _ := scan_prefix step _ _ d i (by simpa [scan_length] using hi)

lemma support_prefix (n : ℕ) (C : Circuit) (j i : ℕ)
    (hi : i < n + (C.gates.take j).length) :
    support n C i =
      (scan sstep (C.gates.take j) (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD i ∅ := by
  exact scan_take_prefix sstep C.gates _ ∅ j i (by simpa using hi)

lemma inv_full (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (hAO : IsAO2 n C) (hml : IsSyntMultilinear n C) :
    Inv S (supports n C) (C.wires (List.ofFn (setInput S))) (readVectors C n (setList S) 1) := by
  have h : ∀ j, j ≤ C.gates.length →
      Inv S
        (scan sstep (C.gates.take j) (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))))
        (scan bstep (C.gates.take j) (List.ofFn (setInput S)))
        (scan (rstep 1 (setList S)) (C.gates.take j)
          ((List.range n).map (leafVectors (setList S) 1))) := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [scan] using inv_inputs S
    | succ j ih =>
      intro hj
      have hj' : j < C.gates.length := by omega
      have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj'
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
      have hgat : gateAt C j = C.gates[j] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj']
      have hshape : C.gates[j] = ⟨(C.gates[j]).op, [a,b]⟩ := by rw [← hab]
      have hop := hAO.1 _ hm
      have ha : a < n + j := hAO.2.1 j hj' a (by simp [hgat, hab])
      have hb : b < n + j := hAO.2.1 j hj' b (by simp [hgat, hab])
      have hdis : (C.gates[j]).op = GateOp.and →
          Disjoint
            ((scan sstep (C.gates.take j)
              (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD a ∅)
            ((scan sstep (C.gates.take j)
              (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD b ∅) := by
        intro hand
        have hd : Disjoint (operandSupport n C j a) (operandSupport n C j b) := by
          simpa [AndOperandsDisjoint, hgat, hab] using hml j hj' (by simpa [hgat] using hand)
        rw [operandSupport, operandSupport, ite_eq_left ha, ite_eq_left hb] at hd
        rw [support_prefix n C j a (by simp; omega),
          support_prefix n C j b (by simp; omega)] at hd
        exact hd
      rw [List.take_succ_eq_append_getElem hj', scan_snoc, scan_snoc, scan_snoc, hshape]
      exact inv_step S _ _ _ a b _ hop hdis (ih (by omega))
  have hs : supports n C = scan sstep C.gates
      (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))) := rfl
  have hw : C.wires (List.ofFn (setInput S)) =
      scan bstep C.gates (List.ofFn (setInput S)) := rfl
  rw [hs, hw, readVectors_eq]
  simpa only [List.take_length] using h C.gates.length le_rfl

lemma syntactic_multilinear_read_one (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hml : IsSyntMultilinear n C) : IsReadK n C 1 := by
  intro S hS
  have hi := inv_full n C S hAO hml
  have hv : (C.wires (List.ofFn (setInput S))).getD C.output false = true := hS.1
  obtain ⟨T, _, hT⟩ := hi.2.2 C.output hv
  apply List.any_eq_true.mpr
  refine ⟨vvec S T, hT, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  by_cases h : j ∈ T.image Fin.val <;> simp [h]

end PEqualNP.Outside.L_meta_2585_aux.Multilinear

namespace PEqualNP.Outside.L_meta_2585_aux.OrBound

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C (fun a : Fin n => decide (a = i)) w = true

lemma mem_T {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ (T C w : Finset (Fin n)) ↔ val C (fun a : Fin n => decide (a = i)) w = true := by
  simp [T]

lemma T_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext i
  rw [mem_T]
  have h := val_input C (fun a : Fin n => decide (a = i)) ⟨w, hw⟩
  change val C (fun a : Fin n => decide (a = i)) w = _ at h
  rw [h]
  simp only [decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma T_gate {n : ℕ} (C : Circuit) (hC : IsOrCircuit n C) (p : ℕ) (hp : p < C.gates.length) :
    ∃ a b, a < n + p ∧ b < n + p ∧ (T C (n + p) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hop, hlen, hin⟩ := hC p hp
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  have hor : (C.gates[p]).op = GateOp.or := by
    generalize (C.gates[p]).op = o at hop
    cases o <;> first | rfl | (simp [isOrOp] at hop)
  obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p]).inputs = [a, b] := by
    match h : (C.gates[p]).inputs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have ha : a < n + p := hin a (by simp [hab])
  have hb : b < n + p := hin b (by simp [hab])
  refine ⟨a, b, ha, hb, ?_⟩
  ext i
  rw [Finset.mem_union, mem_T, mem_T, mem_T, val_gate C _ hg, hor, hab]
  simp [GateOp.eval, operand, ha, hb]

lemma T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp


def Good {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ t ∈ (T C (n + j) : Finset (Fin n)), R c t) ∧
    u ∈ (T C (n + j) : Finset (Fin n)) ∧ ∃ u0 ∈ (T C (n + j) : Finset (Fin n)), u0 < u

lemma no_below {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j)
    (hadj : ∀ t ∈ (T C a : Finset (Fin n)), R c t) (hu : u ∈ (T C a : Finset (Fin n)))
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') : ∀ t ∈ (T C a : Finset (Fin n)), ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j', rfl⟩ : ∃ j', a = n + j' := ⟨a - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hadj, hu, t, ht, hlt⟩

lemma no_lt_aux {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j) (hb : b < n + j)
    (hT : (T C (n + j) : Finset (Fin n)) = T C a ∪ T C b)
    (hg : Good R C c u j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') (hu'a : u' ∈ (T C a : Finset (Fin n))) : False := by
  obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
  have hadja : ∀ t ∈ (T C a : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hadjb : ∀ t ∈ (T C b : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := no_below R C c u' j a hj ha hadja hu'a hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below R C c u j b hj hb hadjb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma no_lt {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (hC : IsOrCircuit n C)
    (c : Fin m) (u u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') : False := by
  have hj := hg.1
  obtain ⟨a, b, ha, hb, hT⟩ := T_gate C hC j hj
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux R C c u u' j a b hj ha hb hT hg hmin hmin' hlt h
  · exact no_lt_aux R C c u u' j b a hj hb ha (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

lemma inj_core {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (c : Fin m) (u : Fin n) (c' : Fin m) (u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c' u' j') :
    c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
    exact hN u0 u (ne_of_lt hu0lt) c c' (hadj u0 hu0) (hadj u hu) (hg'.2.1 u0 hu0) (hg'.2.1 u hu)
  subst hcc
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt R C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt R C hC c u' u j hg' hg hmin' hmin h).elim

lemma leaf_min {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (L : Finset (Fin n))
    (hS : ∃ w < n + C.gates.length, ComputesOr n C w L) (c : Fin m) (u : Fin n)
    (hadj : ∀ t ∈ L, R c t) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good R C c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hcomp⟩ := hS
  have hT := T_computes C w L hcomp
  by_cases hwn : w < n
  · rw [← hT, T_input C w hwn, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT]; exact hadj, by rw [hT]; exact hu, t,
      by rw [hT]; exact ht, hlt⟩

lemma card_le_of_unique_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, Set.Subsingleton {a | a ∈ s ∧ r a b}) : s.card ≤ t.card := by
  classical
  let f : s → β := fun a => Classical.choose (hs a.1 a.2)
  have hf (a : s) : f a ∈ t ∧ r a.1 (f a) := Classical.choose_spec (hs a.1 a.2)
  let g : s → t := fun a => ⟨f a, (hf a).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' heq
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply Subtype.ext
  exact ht (f a) (hf a).1 ⟨a.2, (hf a).2⟩ ⟨a'.2, heq'.symm ▸ (hf a').2⟩

lemma count_gen {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (K : Finset (Fin m × Finset (Fin n)))
    (hK : ∀ k ∈ K, (∃ w < n + C.gates.length, ComputesOr n C w k.2) ∧ ∀ t ∈ k.2, R k.1 t)
    (P : Finset (Σ _ : Fin m, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ C.gates.length + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good R C q.1 q.2 j).card ≤ C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    refine card_le_of_unique_fibers
      (fun q j => Good R C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good R C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_range.2 (Nat.find_spec hex).1
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core R hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good R C q.1 q.2 j).card ≤ K.card := by
    refine card_le_of_unique_fibers
      (fun q k => k.1 = q.1 ∧ q.2 ∈ k.2) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro k hk q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      have hcc : c = c' := hqc.symm.trans hqc'
      subst hcc
      obtain ⟨hcomp, hadj⟩ := hK k hk
      rw [hqc] at hadj
      have h1 := leaf_min R C k.2 hcomp c u hadj hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min R C k.2 hcomp c u' hadj hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good R C q.1 q.2 j)
  omega

lemma linear_family_or_bound_active {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c) :
    (∑ p : Fin m, (S p).card) ≤ c + (Finset.univ.filter fun p => (S p).Nonempty).card := by
  classical
  obtain ⟨C, hC, hsize⟩ := hcost
  let R : Fin m → Fin n → Prop := fun p u => u ∈ S p
  have hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ p q : Fin m,
      R p u0 → R p u → R q u0 → R q u → p = q := by
    intro u0 u hne p q hp0 hpu hq0 hqu
    by_contra hpq
    have hs : ({u0, u} : Finset (Fin n)) ⊆ S p ∩ S q := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hp0, hq0⟩
      · exact Finset.mem_inter.mpr ⟨hpu, hqu⟩
    have hc : ({u0, u} : Finset (Fin n)).card = 2 := by simp [hne]
    have hle := Finset.card_le_card hs
    have hsmall := hlin p q hpq
    omega
  let A : Finset (Fin m) := Finset.univ.filter fun p => (S p).Nonempty
  let K : Finset (Fin m × Finset (Fin n)) := A.image fun p => (p, S p)
  let I : Finset (Σ _ : Fin m, Fin n) := Finset.univ.sigma S
  have hK : ∀ k ∈ K,
      (∃ w < n + C.gates.length, ComputesOr n C w k.2) ∧ ∀ t ∈ k.2, R k.1 t := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨hC.2 (S p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩),
      fun _ ht => ht⟩
  have hP : ∀ q ∈ I, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2 := by
    intro q hq
    refine ⟨(q.1, S q.1), ?_, rfl, (Finset.mem_sigma.mp hq).2⟩
    exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨q.2, (Finset.mem_sigma.mp hq).2⟩⟩, rfl⟩
  have hbound := count_gen R hN C hC.1 K hK I hP
  have hKcard : K.card ≤ A.card := Finset.card_image_le
  dsimp [A] at hKcard
  have hIcard : I.card = ∑ p : Fin m, (S p).card := Finset.card_sigma _ _
  omega

lemma linear_family_or_cost {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c) :
    (∑ p : Fin m, ((S p).card - 1)) ≤ c := by
  classical
  have hcard (p : Fin m) :
      (S p).card = ((S p).card - 1) + if (S p).Nonempty then 1 else 0 := by
    by_cases hp : (S p).Nonempty
    · have hpos := Finset.card_pos.mpr hp
      simp only [ite_eq_left hp]
      omega
    · have hempty : S p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      simp [hempty]
  have hsum : (∑ p : Fin m, (S p).card) =
      (∑ p : Fin m, ((S p).card - 1)) +
        (Finset.univ.filter fun p => (S p).Nonempty).card := by
    calc
      (∑ p : Fin m, (S p).card) =
          ∑ p : Fin m, (((S p).card - 1) + if (S p).Nonempty then 1 else 0) :=
        Finset.sum_congr rfl (fun p _ => hcard p)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  have hb := linear_family_or_bound_active S hlin hcost
  omega

lemma linear_family_or_bound {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n (Finset.univ.image S) c) :
    (∑ p : Fin m, (S p).card) ≤ c + m := by
  classical
  have hcost' : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c := by
    obtain ⟨C, ⟨hC, hCs⟩, hsize⟩ := hcost
    refine ⟨C, ⟨hC, ?_⟩, hsize⟩
    intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact hCs (S p) (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have hb := linear_family_or_bound_active S hlin hcost'
  have ha : (Finset.univ.filter fun p => (S p).Nonempty).card ≤ m := by
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  omega

end PEqualNP.Outside.L_meta_2585_aux.OrBound
