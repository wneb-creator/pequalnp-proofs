import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Powerset

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

namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def shIdx (n s i : ℕ) : ℕ := if i < n then i else i + s

def shGate (n s : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shIdx n s)⟩

def concat (n : ℕ) (C D : Circuit) : Circuit :=
  ⟨C.gates ++ D.gates.map (shGate n C.size), shIdx n C.size D.output⟩

lemma shIdx_lt (n s j i : ℕ) (hi : i < n + j) :
    shIdx n s i < n + s + j := by
  unfold shIdx
  split_ifs <;> omega

lemma concat_size (n : ℕ) (C D : Circuit) :
    (concat n C D).size = C.size + D.size := by
  simp [concat, Circuit.size]

lemma gateAt_concat_left (n : ℕ) (C D : Circuit) (j : ℕ)
    (hj : j < C.gates.length) : gateAt (concat n C D) j = gateAt C j := by
  exact List.getD_append _ _ _ _ hj

lemma gateAt_concat_right (n : ℕ) (C D : Circuit) (j : ℕ)
    (hj : j < D.gates.length) :
    gateAt (concat n C D) (C.gates.length + j) = shGate n C.size (gateAt D j) := by
  unfold gateAt concat
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma concat_valid (n : ℕ) (C D : Circuit)
    (hC : IsAO2 n C) (hD : IsAO2 n D) : IsAO2 n (concat n C D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [concat, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g, hg, rfl⟩
    · exact hC.1 g hg
    · exact hD.1 g hg
  · intro j hj i hi
    have hj' : j < C.gates.length + D.gates.length := by simpa [concat] using hj
    by_cases hjC : j < C.gates.length
    · rw [gateAt_concat_left n C D j hjC] at hi
      exact hC.2.1 j hjC i hi
    · let k := j - C.gates.length
      have hk : k < D.gates.length := by dsimp [k]; omega
      have hjk : j = C.gates.length + k := by dsimp [k]; omega
      rw [hjk, gateAt_concat_right n C D k hk] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have hb := shIdx_lt n C.size k a (hD.2.1 k hk a ha)
      simpa [Circuit.size, hjk, Nat.add_assoc] using hb
  · intro g hg
    simp only [concat, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g, hg, rfl⟩
    · exact hC.2.2 g hg
    · simpa [shGate] using hD.2.2 g hg

lemma concat_output (n : ℕ) (C D : Circuit) (hD : D.output < n + D.size) :
    (concat n C D).output < n + (concat n C D).size := by
  change shIdx n C.size D.output < n + (concat n C D).size
  rw [concat_size]
  have h := shIdx_lt n C.size D.size D.output hD
  omega

end PEqualNP.Outside.L_meta_2585.Merge


namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def fold {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [op g.op (g.inputs.map fun i => w.getD i d)]) w

lemma fold_append {α : Type} (d : α) (op : GateOp → List α → α)
    (gs hs : List Gate) (w : List α) :
    fold d op (gs ++ hs) w = fold d op hs (fold d op gs w) := by
  simp [fold, List.foldl_append]

lemma fold_snoc {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (g : Gate) (w : List α) :
    fold d op (gs ++ [g]) w = fold d op gs w ++
      [op g.op (g.inputs.map fun i => (fold d op gs w).getD i d)] := by
  rw [fold_append]
  rfl

lemma fold_length {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : (fold d op gs w).length = w.length + gs.length :=
  Star.scan_length _ _ _

lemma fold_input {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) (i : ℕ) (hi : i < w.length) :
    (fold d op gs w).getD i d = w.getD i d := Star.scan_prefix _ _ _ _ _ hi

lemma fold_shift {α : Type} (d : α) (op : GateOp → List α → α) (F init : List α) (n s : ℕ)
    (hinit : init.length = n) (hF : F.length = n + s) (hFi : ∀ i < n, F.getD i d = init.getD i d)
    (H : List Gate) : ∀ u, (fold d op (H.map (shGate n s)) F).getD (shIdx n s u) d =
      (fold d op H init).getD u d := by
  induction H using List.reverseRecOn with
  | nil =>
    intro u
    simp only [List.map_nil, fold, List.foldl_nil]
    unfold shIdx
    split_ifs with h
    · exact hFi u h
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton H g ih =>
    intro u
    rw [List.map_append, List.map_singleton, fold_snoc, fold_snoc]
    have hA := fold_length d op (H.map (shGate n s)) F
    have hB := fold_length d op H init
    simp only [List.length_map] at hA
    have ihu := ih u
    unfold shIdx at ihu ⊢
    split_ifs with hu
    · rw [if_pos hu] at ihu
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ihu
    · rw [if_neg hu] at ihu
      rcases lt_trichotomy u (n + H.length) with h | h | h
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ihu
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [hA, hB, show u + s - (F.length + H.length) = 0 by omega,
          show u - (init.length + H.length) = 0 by omega]
        simp only [List.getD_cons_zero, shGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma concat_fold_right {α : Type} (d : α) (op : GateOp → List α → α)
    (n : ℕ) (C D : Circuit) (init : List α) (hn : init.length = n) (i : ℕ) :
    (fold d op (concat n C D).gates init).getD (shIdx n C.size i) d =
      (fold d op D.gates init).getD i d := by
  rw [concat, fold_append]
  apply fold_shift d op _ init n C.size hn
  · rw [fold_length, hn]
    rfl
  · intro j hj
    exact fold_input d op C.gates init j (by omega)

lemma concat_fold_left {α : Type} (d : α) (op : GateOp → List α → α)
    (n : ℕ) (C D : Circuit) (init : List α) (hn : init.length = n) (i : ℕ)
    (hi : i < n + C.size) :
    (fold d op (concat n C D).gates init).getD i d =
      (fold d op C.gates init).getD i d := by
  rw [concat, fold_append]
  apply fold_input
  simpa only [fold_length, hn, Circuit.size] using hi

lemma concat_eval (n : ℕ) (C D : Circuit) (x : List Bool) (hx : x.length = n) :
    (concat n C D).eval x = D.eval x :=
  concat_fold_right false GateOp.eval n C D x hx D.output

def readOp (S : List ℕ) (k : ℕ) : GateOp → List (List (List ℕ)) → List (List ℕ)
  | .or, ins => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and, ins => ins.foldl (andStep k) [S.map fun _ => 0]
  | _, _ => []

lemma readVectors_fold (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = fold [] (readOp S k) C.gates ((List.range n).map (leafVectors S k)) := by
  unfold readVectors fold
  congr 1
  funext R g
  cases g.op <;> rfl

lemma concat_vectors_right (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ) :
    (readVectors (concat n C D) n S k).getD (concat n C D).output [] =
      (readVectors D n S k).getD D.output [] := by
  rw [readVectors_fold, readVectors_fold]
  exact concat_fold_right [] (readOp S k) n C D ((List.range n).map (leafVectors S k)) (by simp) D.output

lemma concat_vectors_left (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ)
    (hC : C.output < n + C.size) :
    (readVectors (concat n C D) n S k).getD C.output [] =
      (readVectors C n S k).getD C.output [] := by
  rw [readVectors_fold, readVectors_fold]
  exact concat_fold_left [] (readOp S k) n C D ((List.range n).map (leafVectors S k)) (by simp) C.output hC

def unionCircuit (n : ℕ) (C D : Circuit) : Circuit :=
  Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output

lemma union_size (n : ℕ) (C D : Circuit) :
    (unionCircuit n C D).size = C.size + D.size + 1 := by
  rw [unionCircuit, Star.addGate_size, concat_size]

lemma union_output (n : ℕ) (C D : Circuit) :
    (unionCircuit n C D).output < n + (unionCircuit n C D).size := by
  simp [unionCircuit, Star.addGate, Circuit.size]

lemma union_valid (n : ℕ) (C D : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hD : PEqualNP.TopForm.IsAO2 n D)
    (hoC : C.output < n + C.size) (hoD : D.output < n + D.size) :
    PEqualNP.TopForm.IsAO2 n (unionCircuit n C D) := by
  apply Star.addGate_valid
  · exact concat_valid n C D hC hD
  · exact Or.inr rfl
  · rw [concat_size]
    omega
  · exact concat_output n C D hoD

lemma union_eval (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (x : List Bool) (hx : x.length = n) :
    (unionCircuit n C D).eval x = (C.eval x || D.eval x) := by
  rw [unionCircuit, Star.addGate_eval n _ _ _ _ x hx]
  have hleft : ((concat n C D).wires x).getD C.output false = C.eval x :=
    concat_fold_left false GateOp.eval n C D x hx C.output hC
  have hright : ((concat n C D).wires x).getD (concat n C D).output false = D.eval x :=
    concat_eval n C D x hx
  simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hleft, hright]

lemma union_read_left (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (S : List ℕ) (k : ℕ) (hr : readsAtMost C n S k = true) :
    readsAtMost (unionCircuit n C D) n S k = true := by
  obtain ⟨v, hv, hread⟩ := List.any_eq_true.mp hr
  apply List.any_eq_true.mpr
  refine ⟨v, ?_, hread⟩
  change v ∈ (readVectors (Star.addGate n (concat n C D) GateOp.or C.output
    (concat n C D).output) n S k).getD
    (Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output).output []
  rw [Star.addGate_vectors]
  apply Star.mem_rstep_or
  left
  rw [concat_vectors_left n C D S k hC]
  exact hv

lemma union_read_right (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ)
    (hr : readsAtMost D n S k = true) :
    readsAtMost (unionCircuit n C D) n S k = true := by
  obtain ⟨v, hv, hread⟩ := List.any_eq_true.mp hr
  apply List.any_eq_true.mpr
  refine ⟨v, ?_, hread⟩
  change v ∈ (readVectors (Star.addGate n (concat n C D) GateOp.or C.output
    (concat n C D).output) n S k).getD
    (Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output).output []
  rw [Star.addGate_vectors]
  apply Star.mem_rstep_or
  right
  rw [concat_vectors_right]
  exact hv

lemma union_read_one (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (rC : IsReadK n C 1) (rD : IsReadK n D 1) :
    IsReadK n (unionCircuit n C D) 1 := by
  intro S hS
  have heval := hS.1
  change (unionCircuit n C D).eval (List.ofFn (setInput S)) = true at heval
  rw [union_eval n C D hC _ (by simp), Bool.or_eq_true] at heval
  have hprime (T : Finset (Fin n)) (hT : T ∈ S.ssubsets) :
      C.eval (List.ofFn (setInput T)) = false ∧ D.eval (List.ofFn (setInput T)) = false := by
    have hf := hS.2 T hT
    change (unionCircuit n C D).eval (List.ofFn (setInput T)) = false at hf
    rw [union_eval n C D hC _ (by simp)] at hf
    cases hc : C.eval (List.ofFn (setInput T)) <;>
      cases hd : D.eval (List.ofFn (setInput T)) <;> simp_all
  rcases heval with heval | heval
  · apply union_read_left n C D hC
    exact rC S ⟨heval, fun T hT => (hprime T hT).1⟩
  · apply union_read_right n C D
    exact rD S ⟨heval, fun T hT => (hprime T hT).2⟩

end PEqualNP.Outside.L_meta_2585.Merge


namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def familyFun (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun s => x.getD s.1 false && s.2.any (fun b => x.getD b false))

lemma family_exists (n : ℕ) : ∀ own : List (ℕ × List ℕ),
    (∀ s ∈ own, s.2 ≠ [] ∧ s.1 < n ∧ ∀ b ∈ s.2, b < n ∧ s.1 ≠ b) →
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      (∀ x : List Bool, x.length = n → D.eval x = familyFun x own) ∧
      D.size = (own.map (fun s => s.2.length)).sum + own.length - 1 ∧
      IsReadK n D 1 ∧ (own ≠ [] → D.output < n + D.size) := by
  intro own
  induction own with
  | nil =>
    intro _
    let D : Circuit := ⟨[], n⟩
    have hfalse (x : List Bool) (hx : x.length = n) : D.eval x = false := by
      simp [D, Circuit.eval, Circuit.wires, ← hx]
    refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
    · simp [D, PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
        PEqualNP.MetaComplexity.NestedCover.ReadsBack]
    · intro x hx
      simpa [familyFun] using hfalse x hx
    · simp [D, Circuit.size]
    · intro S hS
      have ht := hS.1
      change D.eval (List.ofFn (setInput S)) = true at ht
      rw [hfalse _ (by simp)] at ht
      exact (Bool.false_ne_true ht).elim
    · simp
  | cons s own ih =>
    intro hgood
    have hs := hgood s (by simp)
    rcases s with ⟨p, leaves⟩
    cases leaves with
    | nil => exact (hs.1 rfl).elim
    | cons a bs =>
      have hp : p < n := hs.2.1
      have ha : a < n := (hs.2.2 a (by simp)).1
      have hbs : ∀ b ∈ bs, b < n := fun b hb => (hs.2.2 b (by simp [hb])).1
      let S := Star.starCircuit n p a bs
      have hSv : PEqualNP.TopForm.IsAO2 n S := Star.starCircuit_valid n p a bs hp ha hbs
      have hSr : IsReadK n S 1 := Star.starCircuit_read_one n p a bs hp ha hbs
        (fun b hb => (hs.2.2 b hb).2)
      have hSo : S.output < n + S.size := by
        simp [S, Star.starCircuit, Star.addGate, Circuit.size]
      have hSf (x : List Bool) (hx : x.length = n) :
          S.eval x = (x.getD p false && (a :: bs).any (fun b => x.getD b false)) := by
        simpa using Star.starCircuit_eval n p a bs hp ha hbs x hx
      by_cases hown : own = []
      · subst own
        refine ⟨S, hSv, ?_, ?_, hSr, fun _ => hSo⟩
        · intro x hx
          simpa [familyFun] using hSf x hx
        · simp [S, Star.starCircuit_size]
      · obtain ⟨D, hDv, hDf, hDs, hDr, hDo⟩ := ih (fun s hs => hgood s (by simp [hs]))
        refine ⟨unionCircuit n S D, union_valid n S D hSv hDv hSo (hDo hown), ?_, ?_,
          union_read_one n S D hSo hSr hDr, fun _ => union_output n S D⟩
        · intro x hx
          rw [union_eval n S D hSo x hx, hSf x hx, hDf x hx]
          rfl
        · rw [union_size, show S.size = bs.length + 1 from Star.starCircuit_size n p a bs, hDs]
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have hpos : 0 < own.length := List.length_pos_iff.mpr hown
          omega

end PEqualNP.Outside.L_meta_2585.Merge


namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma replacement_of_star_cover (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (hshape : ∀ s ∈ own, s.2 ≠ [] ∧
      ((s.1 < P ∧ ∀ b ∈ s.2, P ≤ b ∧ b < P + L) ∨
        P ≤ s.1 ∧ s.1 < P + L ∧ ∀ b ∈ s.2, b < P))
    (hcover : ∀ p : Fin P, ∀ l : Fin L, I p l ↔ ∃ s ∈ own,
      s.1 = p.val ∧ P + l.val ∈ s.2 ∨ s.1 = P + l.val ∧ p.val ∈ s.2)
    (hcost : (own.map (fun s => s.2.length)).sum + own.length - 1 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + L) D 1 := by
  have hgood : ∀ s ∈ own, s.2 ≠ [] ∧ s.1 < P + L ∧
      ∀ b ∈ s.2, b < P + L ∧ s.1 ≠ b := by
    intro s hs
    have h := hshape s hs
    refine ⟨h.1, ?_, ?_⟩
    · rcases h.2 with ⟨hc, _⟩ | ⟨_, hc, _⟩ <;> omega
    · intro b hb
      rcases h.2 with ⟨hc, hbs⟩ | ⟨hc, _, hbs⟩
      · have := hbs b hb
        constructor <;> omega
      · have := hbs b hb
        constructor <;> omega
  obtain ⟨D, hDv, hDf, hDs, hDr, _⟩ := family_exists (P + L) own hgood
  refine ⟨D, hDv, ?_, by rw [hDs]; exact hcost, hDr⟩
  intro y
  have readp (p : Fin P) :
      (List.ofFn y).getD p.val false = y (Fin.castAdd L p) := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
    rfl
  have readl (l : Fin L) :
      (List.ofFn y).getD (P + l.val) false = y (Fin.natAdd P l) := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
    rfl
  change D.eval (List.ofFn y) = _
  rw [hDf _ (by simp)]
  apply Bool.eq_iff_iff.mpr
  simp only [familyFun, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hc, b, hb, hbt⟩
    rcases (hshape s hs).2 with ⟨hsp, hbl⟩ | ⟨hsl, hsn, hbp⟩
    · have hbn := hbl b hb
      let p : Fin P := ⟨s.1, hsp⟩
      let l : Fin L := ⟨b - P, by omega⟩
      have hbeq : P + l.val = b := by dsimp [l]; omega
      have hi : I p l := (hcover p l).2 ⟨s, hs, Or.inl ⟨rfl, by rw [hbeq]; exact hb⟩⟩
      refine ⟨p, l, hi, ?_, ?_⟩
      · rw [← readp p]
        exact hc
      · rw [← readl l, hbeq]
        exact hbt
    · have hbn := hbp b hb
      let p : Fin P := ⟨b, hbn⟩
      let l : Fin L := ⟨s.1 - P, by omega⟩
      have hseq : P + l.val = s.1 := by dsimp [l]; omega
      have hi : I p l := (hcover p l).2 ⟨s, hs, Or.inr ⟨hseq.symm, hb⟩⟩
      refine ⟨p, l, hi, ?_, ?_⟩
      · rw [← readp p]
        exact hbt
      · rw [← readl l, hseq]
        exact hc
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨s, hs, h⟩ := (hcover p l).1 hi
    rcases h with ⟨hc, hb⟩ | ⟨hc, hb⟩
    · refine ⟨s, hs, ?_, P + l.val, hb, ?_⟩
      · rw [hc, readp]
        exact hp
      · rw [readl]
        exact hl
    · refine ⟨s, hs, ?_, p.val, hb, ?_⟩
      · rw [hc, readl]
        exact hl
      · rw [readp]
        exact hp

end PEqualNP.Outside.L_meta_2585.Merge

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


open PEqualNP.EdgeOwnership

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma scan_gate_value {α : Type} (step : List α → Gate → α) (gs : List Gate)
    (w : List α) (d : α) (k : ℕ) (hk : k < gs.length) :
    (scan step gs w).getD (w.length + k) d =
      step (scan step (gs.take k) w) gs[k] := by
  rw [scan_take_prefix step gs w d (k+1) (w.length+k) (by simp; omega),
    List.take_succ_eq_append_getElem hk, scan_snoc]
  apply getD_last'
  simp [scan_length]
  omega

lemma support_gate_two (n : ℕ) (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : (gateAt C j).inputs = [a,b]) (ha : a < n+j) (hb : b < n+j) :
    support n C (n+j) = support n C a ∪ support n C b := by
  have h := scan_gate_value sstep C.gates
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) ∅ j hj
  simp only [List.length_ofFn] at h
  have hgat := gateAt_eq C j hj
  rw [hgat] at hab
  simp only [sstep, hab, List.foldr_cons, List.foldr_nil, Finset.union_empty] at h
  rw [← support_prefix n C j a (by simp; omega),
    ← support_prefix n C j b (by simp; omega)] at h
  exact h

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wire_gate_two (n : ℕ) (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : (gateAt C j).inputs = [a,b]) (ha : a < n+j) (hb : b < n+j)
    (x : Fin n → Bool) :
    wv n C x (n+j) = (gateAt C j).op.eval [wv n C x a, wv n C x b] := by
  have h := scan_gate_value bstep C.gates (List.ofFn x) false j hj
  simp only [List.length_ofFn] at h
  have hgat := gateAt_eq C j hj
  rw [hgat] at hab
  simp only [bstep, hab, List.map_cons, List.map_nil] at h
  rw [← scan_take_prefix bstep C.gates (List.ofFn x) false j a (by simp; omega),
    ← scan_take_prefix bstep C.gates (List.ofFn x) false j b (by simp; omega)] at h
  simpa only [hgat, wv, Circuit.wires, scan, bstep] using h

lemma support_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    support n C w = {⟨w,hw⟩} := by
  rw [support_prefix n C 0 w (by simpa using hw)]
  simp [scan, List.getD_eq_getElem?_getD, hw]

lemma wire_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wv n C x w = x ⟨w,hw⟩ := by
  change (scan bstep C.gates (List.ofFn x)).getD w false = _
  rw [scan_prefix bstep C.gates (List.ofFn x) false w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma no_and_support_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length →
      (∀ k < C.gates.length, (w = n+k ∨ n ≤ w ∧ InCone n C k (w-n)) →
        (gateAt C k).op ≠ GateOp.and) →
      ∀ v : Fin n, v ∈ support n C w →
        wv n C (fun r => decide (r=v)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hno v hv
    by_cases hwn : w < n
    · rw [support_input n C w hwn, Finset.mem_singleton] at hv
      rw [wire_input n C w hwn]
      simp [hv]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hgat := gateAt_eq C j hj
      have hm : gateAt C j ∈ C.gates := by rw [hgat]; exact List.getElem_mem hj
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
      have ha : a < n+j := hAO.2.1 j hj a (by simp [hab])
      have hb : b < n+j := hAO.2.1 j hj b (by simp [hab])
      have hop : (gateAt C j).op = GateOp.or := by
        rcases hAO.1 _ hm with h | h
        · exact (hno j hj (Or.inl rfl) h).elim
        · exact h
      have hchild (r : ℕ) (hr : r ∈ (gateAt C j).inputs) (hlt : r < n+j) :
          ∀ k < C.gates.length, (r = n+k ∨ n ≤ r ∧ InCone n C k (r-n)) →
            (gateAt C k).op ≠ GateOp.and := by
        intro k hk hc
        apply hno k hk
        right
        refine ⟨by omega, ?_⟩
        have hc' : InCone n C k j := by
          apply (inCone_iff n C k j hj).mpr
          rcases hc with heq | ⟨hn, hcone⟩
          · exact ⟨r, hr, by omega, hlt, Or.inl (by omega)⟩
          · exact ⟨r, hr, hn, hlt, Or.inr hcone⟩
        simpa using hc'
      rw [support_gate_two n C j a b hj hab ha hb, Finset.mem_union] at hv
      rw [wire_gate_two n C j a b hj hab ha hb, hop]
      rcases hv with hva | hvb
      · have ht := ih a ha (by omega) (hchild a (by simp [hab]) ha) v hva
        simp [GateOp.eval, ht]
      · have ht := ih b hb (by omega) (hchild b (by simp [hab]) hb) v hvb
        simp [GateOp.eval, ht]

lemma no_nested_and_multilinear (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hnested : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j)
    (hzero : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, gateVal n C j (fun r => decide (r=v)) = false) :
    IsSyntMultilinear n C := by
  intro j hj hand
  have hgat := gateAt_eq C j hj
  have hm : gateAt C j ∈ C.gates := by rw [hgat]; exact List.getElem_mem hj
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : a < n+j := hAO.2.1 j hj a (by simp [hab])
  have hb : b < n+j := hAO.2.1 j hj b (by simp [hab])
  have hchild (r : ℕ) (hr : r ∈ (gateAt C j).inputs) (hlt : r < n+j) :
      ∀ k < C.gates.length, (r = n+k ∨ n ≤ r ∧ InCone n C k (r-n)) →
        (gateAt C k).op ≠ GateOp.and := by
    intro k hk hc hkand
    apply hnested k hk j hj hkand hand
    apply (inCone_iff n C k j hj).mpr
    rcases hc with heq | ⟨hn, hcone⟩
    · exact ⟨r,hr,by omega,hlt,Or.inl (by omega)⟩
    · exact ⟨r,hr,hn,hlt,Or.inr hcone⟩
  have hd : Disjoint (support n C a) (support n C b) := by
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    have va := no_and_support_true n C hAO a (by omega)
      (hchild a (by simp [hab]) ha) v hva
    have vb := no_and_support_true n C hAO b (by omega)
      (hchild b (by simp [hab]) hb) v hvb
    have htrue : gateVal n C j (fun r => decide (r=v)) = true := by
      change wv n C (fun r => decide (r=v)) (n+j) = true
      rw [wire_gate_two n C j a b hj hab ha hb, hand]
      simp [GateOp.eval, va, vb]
    rw [hzero j hj hand v] at htrue
    cases htrue
  simpa [AndOperandsDisjoint,hab,operandSupport,ha,hb] using hd

lemma and_pairs_zero_read_one (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hpairs : andPairs n C = 0)
    (hzero : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, gateVal n C j (fun r => decide (r=v)) = false) :
    IsReadK n C 1 := by
  apply syntactic_multilinear_read_one n C hAO
  apply no_nested_and_multilinear n C hAO ?_ hzero
  intro i hi j hj hiand hjand hcone
  have hpos : 0 < andPairs n C := by
    apply Finset.card_pos.mpr
    refine ⟨(i,j), ?_⟩
    simp [hi, hj, hiand, hjand, hcone]
  omega

end PEqualNP.Outside.L_meta_2585_aux.Multilinear

namespace PEqualNP.Outside.L_meta_2585.CleanTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (PEqualNP.SplitCount.unitInput v) = false := by
  simp [graphFun, PEqualNP.SplitCount.unitInput]

lemma no_nested_and (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (htop : TopForm G C)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  intro i hi j hj hopi hopj
  exact htop i hi j hj hopi (hclean i hi hopi) hopj

lemma and_singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ∀ v : Fin n,
      gateVal n C i (PEqualNP.SplitCount.unitInput v) = false := by
  intro i hi hop v
  cases hv : gateVal n C i (PEqualNP.SplitCount.unitInput v) with
  | false => rfl
  | true =>
    have h := hclean i hi hop (PEqualNP.SplitCount.unitInput v) hv
    rw [singleton_false n G v] at h
    cases h

end PEqualNP.Outside.L_meta_2585.CleanTopForm

namespace PEqualNP.Outside.L_meta_2585.CleanJunk

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma all_and_below_of_junk_empty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hJ : junk G C = ∅) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i := by
  intro i hi hop x hx
  cases hF : graphFun G ∅ x with
  | true => rfl
  | false =>
    have hmem : i ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, hop, hi, x, hx, hF⟩
    have hnot : i ∉ junk G C := by simp [hJ]
    exact False.elim (hnot hmem)

end PEqualNP.Outside.L_meta_2585.CleanJunk

namespace PEqualNP.Outside.L_meta_2585.CleanReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma clean_topform_read_one (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (htop : TopForm G C) (hJ : junk G C = ∅) :
    PEqualNP.ReadK.IsReadK n C 1 := by
  have hbelow := PEqualNP.Outside.L_meta_2585.CleanJunk.all_and_below_of_junk_empty n G C hJ
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.syntactic_multilinear_read_one n C hAO
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.no_nested_and_multilinear n C hAO
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.no_nested_and n G C htop hbelow
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.and_singleton_false n G C hbelow

lemma incidence_replacement_of_clean_topform (P L : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (G : SimpleGraph (Fin (P + L))) [DecidableRel G.Adj]
    (hAO : IsAO2 (P + L) C) (htop : TopForm G C) (hJ : junk G C = ∅)
    (hfun : ∀ z : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  exact ⟨C, hAO, hfun, le_rfl, clean_topform_read_one (P + L) G C hAO htop hJ⟩

end PEqualNP.Outside.L_meta_2585.CleanReadOne

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

namespace PEqualNP.Outside.L_meta_2585.CircuitMonotone

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
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

lemma append_mono (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = w.length
    · subst i
      have ha : a = true := by simpa using hi
      simpa [hlen] using hab ha
    · have hle : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hle] at hi
      cases hi

lemma run_mono (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (run gs w).getD i false = true → (run gs v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i,
      (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true →
      (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    · simpa using hlen
    · apply append_mono w v _ _ hlen h
      apply eval_mono g.op (hao g (by simp))
      intro i _
      exact h i

lemma circuitFun_mono (n : ℕ) (C : Circuit)
    (hao : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true := by
  apply run_mono C.gates hao (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases hin : i < n
  · have hx : i < (List.ofFn x).length := by simpa
    have hy : i < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact hxy ⟨i, hin⟩ hi
  · have hle : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hle] at hi
    cases hi

lemma ao2_mono (n : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true :=
  circuitFun_mono n C hao.1 x y hxy

end PEqualNP.Outside.L_meta_2585.CircuitMonotone

namespace PEqualNP.Outside.L_meta_2585.EdgeInvisible

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.CircuitMonotone

def atGate (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ g :: post, out⟩

def offGate (pre post : List Gate) (out : ℕ) : Circuit :=
  atGate pre post ⟨GateOp.or, []⟩ out

def gateValue (pre : List Gate) (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (run pre x).getD i false)

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma offGate_size (pre post : List Gate) (g : Gate) (out : ℕ) :
    (offGate pre post out).size = (atGate pre post g out).size := by
  simp [offGate, atGate, Circuit.size]

lemma offGate_eval_eq (pre post : List Gate) (g : Gate) (out : ℕ) (x : List Bool)
    (hfalse : gateValue pre g x = false) :
    (offGate pre post out).eval x = (atGate pre post g out).eval x := by
  change (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD out false =
    (run (pre ++ g :: post) x).getD out false
  rw [run_append, run_append, run_cons, run_cons]
  change (run post (run pre x ++ [false])).getD out false =
    (run post (run pre x ++ [gateValue pre g x])).getD out false
  rw [hfalse]

lemma offGate_eval_le (pre post : List Gate) (g : Gate) (out : ℕ) (x : List Bool)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or) :
    (offGate pre post out).eval x = true → (atGate pre post g out).eval x = true := by
  change (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD out false = true →
    (run (pre ++ g :: post) x).getD out false = true
  rw [run_append, run_append, run_cons, run_cons]
  change (run post (run pre x ++ [false])).getD out false = true →
    (run post (run pre x ++ [gateValue pre g x])).getD out false = true
  apply run_mono post hpost _ _ (by simp) _ out
  apply append_mono _ _ false _ rfl (fun _ h => h)
  intro h
  cases h

lemma offGate_ao (pre post : List Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or) :
    PEqualNP.EdgeOwnership.AndOrOnly (offGate pre post out) := by
  intro h hh
  change h ∈ pre ++ ⟨GateOp.or, []⟩ :: post at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hpre h hh
  · rcases List.mem_cons.mp hh with rfl | hh
    · exact Or.inr rfl
    · exact hpost h hh

lemma offGate_incidence (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hinvisible : ∀ p : Fin P, ∀ l : Fin L, I p l →
      gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false) :
    ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    have hc := offGate_eval_le pre post g out (List.ofFn x) hpost hx
    change circuitFun (P + L) (atGate pre post g out) x = true at hc
    rw [hfun] at hc
    exact of_decide_eq_true hc
  · rintro ⟨p, l, hi, hp, hl⟩
    let e : Fin (P + L) → Bool := fun i =>
      decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
    have he : circuitFun (P + L) (offGate pre post out) e = true := by
      change (offGate pre post out).eval (List.ofFn e) = true
      rw [offGate_eval_eq pre post g out (List.ofFn e) (hinvisible p l hi)]
      change circuitFun (P + L) (atGate pre post g out) e = true
      rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hi, by simp [e], by simp [e]⟩
    apply circuitFun_mono (P + L) (offGate pre post out) (offGate_ao pre post out hpre hpost) e x ?_ he
    intro i hei
    rcases of_decide_eq_true hei with rfl | rfl
    · exact hp
    · exact hl

end PEqualNP.Outside.L_meta_2585.EdgeInvisible

namespace PEqualNP.Outside.L_meta_2585.ConstantCleanup

open PEqualNP.CircuitLowerBounds

-- The status pass and invariant follow the checked Elim and Parity3 helper files.
-- The status type here is the library sum of Bool and Nat.

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not

lemma wiresFrom_append (a b : List Gate) (w : List Bool) :
    wiresFrom (a ++ b) w = wiresFrom b (wiresFrom a w) := by
  simp [wiresFrom, List.foldl_append]

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · change wiresFrom gs (w ++ [_]) = _
      rw [ht]
      simp [List.append_assoc]
    · simp [hlen]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)


def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]


def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega


lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj


def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])


def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

lemma CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

lemma CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

lemma clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

lemma simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

lemma toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h


lemma clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i)

lemma inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


lemma simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg


lemma elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    NotFree gs → NotFree acc.2 → NotFree (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self


lemma ao_of_clean (n : ℕ) (gs : List Gate) (out : ℕ)
    (hclean : CleanL n gs) (hnf : NotFree gs) :
    PEqualNP.TopForm.IsAO2 n ⟨gs, out⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    rcases hclean j g hj with ⟨hn, _⟩ | ⟨hao, _⟩
    · exact False.elim (hnf g hg hn)
    · exact hao
  · intro j hj i hi
    have hget : gs[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    exact (hclean j _ hget).lt i hi
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    rcases hclean j g hj with ⟨hn, _⟩ | ⟨_, a, b, _, _, hinputs⟩
    · exact False.elim (hnf g hg hn)
    · simp [hinputs]

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_zero_len (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    (elim n (pre ++ ⟨GateOp.or, []⟩ :: post) acc).2.length ≤
      acc.2.length + pre.length + post.length := by
  rw [elim_append]
  change (elim n post (elimStep n (elim n pre acc) ⟨GateOp.or, []⟩)).2.length ≤ _
  have hpost := elim_len n post (elimStep n (elim n pre acc) ⟨GateOp.or, []⟩)
  have hpre := elim_len n pre acc
  have hstep : (elimStep n (elim n pre acc) ⟨GateOp.or, []⟩).2.length =
      (elim n pre acc).2.length := by simp [elimStep, simplify, simpOr]
  rw [hstep] at hpost
  omega

def withZero (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩

lemma cleanup_withZero (n : ℕ) (pre post : List Gate) (out : ℕ)
    (hao : PEqualNP.EdgeOwnership.AndOrOnly (withZero pre post out))
    (hfan : ∀ g ∈ (withZero pre post out).gates, g.inputs.length ≤ 2)
    (hnc : ∃ x y : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n (withZero pre post out) x ≠
        PEqualNP.MetaComplexity.circuitFun n (withZero pre post out) y) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      D.size + 1 ≤ (withZero pre post out).size ∧
      PEqualNP.MetaComplexity.circuitFun n D =
        PEqualNP.MetaComplexity.circuitFun n (withZero pre post out) := by
  let C := withZero pre post out
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    refine ⟨?_, hfan g hg⟩
    rcases hao g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hnf : NotFree C.gates := by
    intro g hg hn
    rcases hao g hg with h | h <;> rw [h] at hn <;> cases hn
  let acc := elim n C.gates (idStats n, [])
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD out (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        PEqualNP.MetaComplexity.circuitFun n C y := by
    intro y
    exact (hinv y).2 out |>.2
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hne⟩ := hnc
    apply hne
    change PEqualNP.MetaComplexity.circuitFun n C x = PEqualNP.MetaComplexity.circuitFun n C y
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
    · apply ao_of_clean n acc.2 j
      · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
          (inv_id n _) (by intro p g hp; simp at hp)
      · exact elim_mono n C.gates _ hnf (by intro g hg; simp at hg)
    · have hlen := elim_zero_len n pre post (idStats n, [])
      change (elim n (pre ++ ⟨GateOp.or, []⟩ :: post) (idStats n, [])).2.length + 1 ≤
        (withZero pre post out).size
      simp only [List.length_nil, zero_add] at hlen
      simp only [withZero, Circuit.size, List.length_append, List.length_cons]
      omega
    · funext y
      have h := hval y
      rw [hst] at h
      exact h

end PEqualNP.Outside.L_meta_2585.ConstantCleanup

namespace PEqualNP.Outside.L_meta_2585.EdgeElimination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.EdgeInvisible

lemma drop_invisible_gate (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hinvisible : ∀ p : Fin P, ∀ l : Fin L, I p l →
      gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      D.size < (atGate pre post g out).size ∧
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) := by
  have hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  have hf := offGate_incidence P L I pre post g out hpre hpost hfun hinvisible
  have hfan : ∀ h ∈ (offGate pre post out).gates, h.inputs.length ≤ 2 := by
    intro h hh
    change h ∈ pre ++ ⟨GateOp.or, []⟩ :: post at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact (hAO.2.2 h (List.mem_append_left _ hh)).le
    · rcases List.mem_cons.mp hh with rfl | hh
      · simp
      · exact (hAO.2.2 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))).le
  have hfalse : circuitFun (P + L) (offGate pre post out) (fun _ => false) = false := by
    rw [hf]
    simp
  have htrue : circuitFun (P + L) (offGate pre post out) (fun _ => true) = true := by
    rw [hf, decide_eq_true_eq]
    obtain ⟨p, l, hi⟩ := hne
    exact ⟨p, l, hi, rfl, rfl⟩
  have hnc : ∃ x y : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x ≠
        circuitFun (P + L) (offGate pre post out) y :=
    ⟨(fun _ => false), (fun _ => true), by rw [hfalse, htrue]; decide⟩
  obtain ⟨D, hD, hsize, hDfun⟩ :=
    PEqualNP.Outside.L_meta_2585.ConstantCleanup.cleanup_withZero (P + L) pre post out
      (offGate_ao pre post out hpre hpost) hfan hnc
  refine ⟨D, hD, ?_, ?_⟩
  · have hs : (PEqualNP.Outside.L_meta_2585.ConstantCleanup.withZero pre post out).size =
        (atGate pre post g out).size := offGate_size pre post g out
    rw [hs] at hsize
    omega
  · intro x
    rw [hDfun]
    exact hf x

lemma least_gate_accepts_edge (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D →
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      (atGate pre post g out).size ≤ D.size) :
    ∃ p : Fin P, ∃ l : Fin L, I p l ∧
      gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = true := by
  by_contra h
  have hinvisible : ∀ p : Fin P, ∀ l : Fin L, I p l →
      gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false := by
    intro p l hi
    cases hv : gateValue pre g (List.ofFn fun i : Fin (P + L) =>
        decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) with
    | false => rfl
    | true => exact False.elim (h ⟨p, l, hi, hv⟩)
  obtain ⟨D, hD, hsmall, hDf⟩ := drop_invisible_gate P L I pre post g out hAO hne hfun hinvisible
  have hle := hmin D hD hDf
  omega

end PEqualNP.Outside.L_meta_2585.EdgeElimination


namespace PEqualNP.Outside.L_meta_2585.EdgeEssential

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.EdgeInvisible
open PEqualNP.Outside.L_meta_2585.CircuitMonotone

lemma offGate_incidence_of_edges (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hkeep : ∀ p : Fin P, ∀ l : Fin L, I p l →
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = true) :
    ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    have hc := offGate_eval_le pre post g out (List.ofFn x) hpost hx
    change circuitFun (P + L) (atGate pre post g out) x = true at hc
    rw [hfun] at hc
    exact of_decide_eq_true hc
  · rintro ⟨p, l, hi, hp, hl⟩
    let e : Fin (P + L) → Bool := fun i =>
      decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)
    have he : circuitFun (P + L) (offGate pre post out) e = true := hkeep p l hi
    apply circuitFun_mono (P + L) (offGate pre post out) (offGate_ao pre post out hpre hpost) e x ?_ he
    intro i hei
    rcases of_decide_eq_true hei with rfl | rfl
    · exact hp
    · exact hl


lemma drop_gate_of_function (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hoff : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      D.size < (atGate pre post g out).size ∧
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) := by
  have hpre : ∀ h ∈ pre, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    exact hAO.1 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  have hf := hoff
  have hfan : ∀ h ∈ (offGate pre post out).gates, h.inputs.length ≤ 2 := by
    intro h hh
    change h ∈ pre ++ ⟨GateOp.or, []⟩ :: post at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact (hAO.2.2 h (List.mem_append_left _ hh)).le
    · rcases List.mem_cons.mp hh with rfl | hh
      · simp
      · exact (hAO.2.2 h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))).le
  have hfalse : circuitFun (P + L) (offGate pre post out) (fun _ => false) = false := by
    rw [hf]
    simp
  have htrue : circuitFun (P + L) (offGate pre post out) (fun _ => true) = true := by
    rw [hf, decide_eq_true_eq]
    obtain ⟨p, l, hi⟩ := hne
    exact ⟨p, l, hi, rfl, rfl⟩
  have hnc : ∃ x y : Fin (P + L) → Bool,
      circuitFun (P + L) (offGate pre post out) x ≠
        circuitFun (P + L) (offGate pre post out) y :=
    ⟨(fun _ => false), (fun _ => true), by rw [hfalse, htrue]; decide⟩
  obtain ⟨D, hD, hsize, hDfun⟩ :=
    PEqualNP.Outside.L_meta_2585.ConstantCleanup.cleanup_withZero (P + L) pre post out
      (offGate_ao pre post out hpre hpost) hfan hnc
  refine ⟨D, hD, ?_, ?_⟩
  · have hs : (PEqualNP.Outside.L_meta_2585.ConstantCleanup.withZero pre post out).size =
        (atGate pre post g out).size := offGate_size pre post g out
    rw [hs] at hsize
    omega
  · intro x
    rw [hDfun]
    exact hf x


lemma least_gate_output_essential (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) (atGate pre post g out))
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) (atGate pre post g out) x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D →
      (∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) D x =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      (atGate pre post g out).size ≤ D.size) :
    ∃ p : Fin P, ∃ l : Fin L, I p l ∧
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false := by
  by_contra h
  have hkeep : ∀ p : Fin P, ∀ l : Fin L, I p l →
      circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = true := by
    intro p l hi
    cases hv : circuitFun (P + L) (offGate pre post out)
        (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) with
    | true => rfl
    | false => exact False.elim (h ⟨p, l, hi, hv⟩)
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hAO.1 q (List.mem_append_left _ hq)
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hAO.1 q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
  have hf := offGate_incidence_of_edges P L I pre post g out hpre hpost hfun hkeep
  obtain ⟨D, hD, hsmall, hDf⟩ := drop_gate_of_function P L I pre post g out hAO hne hfun hf
  have hle := hmin D hD hDf
  omega

end PEqualNP.Outside.L_meta_2585.EdgeEssential

namespace PEqualNP.Outside.L_meta_2585

lemma graph_test_criterion {α : Type*} [Fintype α] [DecidableEq α]
    (E : α → α → Prop) [DecidableRel E] (f : (α → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (accepts : ∀ u v, E u v → f (fun i => decide (i = u ∨ i = v)) = true)
    (rejects : ∀ S : Finset α, (∀ u ∈ S, ∀ v ∈ S, ¬ E u v) →
      f (fun i => decide (i ∈ S)) = false) :
    ∀ x, f x = decide (∃ u v, E u v ∧ x u = true ∧ x v = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    by_contra h
    let S : Finset α := Finset.univ.filter fun i => x i = true
    have independent : ∀ u ∈ S, ∀ v ∈ S, ¬ E u v := by
      intro u hu v hv huv
      exact h ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
    have input : (fun i => decide (i ∈ S)) = x := by
      funext i
      simp [S]
    have hf := rejects S independent
    rw [input, hx] at hf
    cases hf
  · rintro ⟨u, v, huv, hu, hv⟩
    apply mono (fun i => decide (i = u ∨ i = v)) x ?_ (accepts u v huv)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

end PEqualNP.Outside.L_meta_2585

namespace PEqualNP.Outside.L_meta_2585

lemma incidence_test_criterion {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (I : α → β → Prop) [DecidableRel I]
    (f : (α → Bool) → (β → Bool) → Bool)
    (mono : ∀ x y x' y', (∀ a, x a = true → x' a = true) →
      (∀ b, y b = true → y' b = true) → f x y = true → f x' y' = true)
    (accepts : ∀ a b, I a b → f (fun a' => decide (a' = a))
      (fun b' => decide (b' = b)) = true)
    (rejects : ∀ S : Finset α, f (fun a => decide (a ∈ S))
      (fun b => decide (∀ a ∈ S, ¬ I a b)) = false) :
    ∀ x y, f x y = decide (∃ a b, I a b ∧ x a = true ∧ y b = true) := by
  intro x y
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hxy
    by_contra h
    let S : Finset α := Finset.univ.filter fun a => x a = true
    have points : ∀ a, x a = true → decide (a ∈ S) = true := by
      intro a ha
      simp [S, ha]
    have lines : ∀ b, y b = true → decide (∀ a ∈ S, ¬ I a b) = true := by
      intro b hb
      apply decide_eq_true
      intro a ha hab
      exact h ⟨a, b, hab, (Finset.mem_filter.mp ha).2, hb⟩
    have accepted := mono x y _ _ points lines hxy
    rw [rejects S] at accepted
    cases accepted
  · rintro ⟨a, b, hab, ha, hb⟩
    apply mono (fun a' => decide (a' = a)) (fun b' => decide (b' = b))
      x y ?_ ?_ (accepts a b hab)
    · intro a' ha'
      simp only [decide_eq_true_eq] at ha'
      subst a'
      exact ha
    · intro b' hb'
      simp only [decide_eq_true_eq] at hb'
      subst b'
      exact hb

end PEqualNP.Outside.L_meta_2585

namespace PEqualNP.Outside.L_meta_2585

lemma closed_incidence_test_criterion {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (I : α → β → Prop) [DecidableRel I]
    (f : (α → Bool) → (β → Bool) → Bool)
    (mono : ∀ x y x' y', (∀ a, x a = true → x' a = true) →
      (∀ b, y b = true → y' b = true) → f x y = true → f x' y' = true)
    (accepts : ∀ a b, I a b → f (fun a' => decide (a' = a))
      (fun b' => decide (b' = b)) = true)
    (rejects : ∀ S : Finset α,
      (∀ a, (∀ b, (∀ a' ∈ S, ¬ I a' b) → ¬ I a b) → a ∈ S) →
      f (fun a => decide (a ∈ S)) (fun b => decide (∀ a ∈ S, ¬ I a b)) = false) :
    ∀ x y, f x y = decide (∃ a b, I a b ∧ x a = true ∧ y b = true) := by
  intro x y
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hxy
    by_contra h
    let S : Finset α := Finset.univ.filter fun a => x a = true
    let T : Finset α := Finset.univ.filter fun a =>
      ∀ b, (∀ a' ∈ S, ¬ I a' b) → ¬ I a b
    have sub : ∀ a, a ∈ S → a ∈ T := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      exact hb a ha
    have same_lines (b : β) : (∀ a ∈ T, ¬ I a b) ↔ ∀ a ∈ S, ¬ I a b := by
      constructor
      · intro hb a ha
        exact hb a (sub a ha)
      · intro hb a ha
        exact (Finset.mem_filter.mp ha).2 b hb
    have closed : ∀ a, (∀ b, (∀ a' ∈ T, ¬ I a' b) → ¬ I a b) → a ∈ T := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      exact ha b ((same_lines b).mpr hb)
    have points : ∀ a, x a = true → decide (a ∈ T) = true := by
      intro a ha
      apply decide_eq_true
      apply sub
      simp [S, ha]
    have lines : ∀ b, y b = true → decide (∀ a ∈ T, ¬ I a b) = true := by
      intro b hb
      apply decide_eq_true
      apply (same_lines b).mpr
      intro a ha hab
      exact h ⟨a, b, hab, (Finset.mem_filter.mp ha).2, hb⟩
    have accepted := mono x y _ _ points lines hxy
    rw [rejects T closed] at accepted
    cases accepted
  · rintro ⟨a, b, hab, ha, hb⟩
    apply mono (fun a' => decide (a' = a)) (fun b' => decide (b' = b))
      x y ?_ ?_ (accepts a b hab)
    · intro a' ha'
      simp only [decide_eq_true_eq] at ha'
      subst a'
      exact ha
    · intro b' hb'
      simp only [decide_eq_true_eq] at hb'
      subst b'
      exact hb

end PEqualNP.Outside.L_meta_2585

namespace PEqualNP.Outside.L_meta_2585_aux.MixedLinear

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost PEqualNP.TopForm

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

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
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

lemma append_mono (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = w.length
    · subst i
      have ha : a = true := by simpa using hi
      simpa [hlen] using hab ha
    · have hle : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hle] at hi
      cases hi

lemma wiresFrom_mono (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i,
      (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true →
      (wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    · simpa using hlen
    · apply append_mono w v _ _ hlen h
      apply eval_mono g.op (hao g (by simp))
      intro i _
      exact h i


lemma val_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    val C x w = true → val C y w = true := by
  apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) _ w
  intro i hi
  by_cases hin : i < n
  · have hx : i < (List.ofFn x).length := by simpa
    have hy : i < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact hxy ⟨i, hin⟩ hi
  · have hle : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hle] at hi
    cases hi

def Pure {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  val C (fun i => decide (i ∉ S)) w = false

lemma pure_support {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hp : Pure C S w) : T C w ⊆ S := by
  intro i hi
  by_contra hni
  have hmono := val_mono C hC (fun a : Fin n => decide (a = i))
    (fun a => decide (a ∉ S)) (by
      intro a ha
      have hai : a = i := of_decide_eq_true ha
      subst a
      exact decide_eq_true hni) w ((mem_T C w i).mp hi)
  unfold Pure at hp
  rw [hp] at hmono
  cases hmono

lemma gate_data {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ g a b, C.gates[j]? = some g ∧ g.inputs = [a,b] ∧ a < n+j ∧ b < n+j ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  let g := C.gates[j]
  have hg : g ∈ C.gates := List.getElem_mem hj
  have hl := hC.2.2 g hg
  obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := by
    match h : g.inputs, hl with
    | [a,b], _ => exact ⟨a,b,rfl⟩
  have hread := hC.2.1 j hj
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getElem?_eq_getElem hj,g]
  rw [hgate] at hread
  exact ⟨g,a,b,List.getElem?_eq_getElem hj,hab,hread a (by simp [hab]),
    hread b (by simp [hab]),hC.1 g hg⟩

lemma or_support {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b := by
  ext i
  rw [Finset.mem_union,mem_T,mem_T,mem_T,val_gate C _ hg,hop,hab]
  simp [GateOp.eval,operand,ha,hb]

lemma and_support {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (T C (n+j) : Finset (Fin n)) = T C a ∩ T C b := by
  ext i
  rw [Finset.mem_inter,mem_T,mem_T,mem_T,val_gate C _ hg,hop,hab]
  simp [GateOp.eval,operand,ha,hb]

lemma pure_or {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) (S : Finset (Fin n)) :
    Pure C S (n+j) ↔ Pure C S a ∧ Pure C S b := by
  simp [Pure,val_gate C _ hg,hop,hab,GateOp.eval,operand,ha,hb]

lemma pure_and {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) (S : Finset (Fin n)) :
    Pure C S (n+j) ↔ Pure C S a ∨ Pure C S b := by
  simp only [Pure,val_gate C _ hg,hop,hab,GateOp.eval,List.map_cons,List.map_nil,
    List.all_cons,List.all_nil, Bool.and_true,operand,ite_eq_left ha,ite_eq_left hb]
  cases val C (fun i => decide (i ∉ S)) a <;>
    cases val C (fun i => decide (i ∉ S)) b <;> decide

lemma T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp



def Good {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ Pure C (S c) (n+j) ∧
    u ∈ T C (n+j) ∧ ∃ u0 ∈ T C (n+j), u0 < u

lemma no_below {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n+j) (hp : Pure C (S c) a)
    (hu : u ∈ T C a) (hmin : ∀ j', j' < j → ¬ Good S C c u j') :
    ∀ t ∈ T C a, ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han,Finset.mem_singleton] at hu ht
    rw [hu,ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j',rfl⟩ : ∃ j', a = n+j' := ⟨a-n,by omega⟩
    exact hmin j' (by omega) ⟨by omega,hp,hu,t,ht,hlt⟩

lemma first_good_or {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hC : IsAO2 n C) (c : Fin m) (u : Fin n) (j : ℕ)
    (hg : Good S C c u j) (hmin : ∀ j', j' < j → ¬ Good S C c u j') :
    ∃ g a b, C.gates[j]? = some g ∧ g.op = GateOp.or ∧ g.inputs = [a,b] ∧
      a < n+j ∧ b < n+j ∧ Pure C (S c) a ∧ Pure C (S c) b ∧
      (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hj,hp,hu,u0,hu0,hlt⟩ := hg
  obtain ⟨g,a,b,hg,hab,ha,hb,hop⟩ := gate_data C hC j hj
  rcases hop with hand | hor
  · have hT := and_support C hg hand hab ha hb
    rw [hT,Finset.mem_inter] at hu hu0
    rcases (pure_and C hg hand hab ha hb (S c)).mp hp with hpa | hpb
    · exact (no_below S C c u j a hj ha hpa hu.1 hmin u0 hu0.1 hlt).elim
    · exact (no_below S C c u j b hj hb hpb hu.2 hmin u0 hu0.2 hlt).elim
  · obtain ⟨hpa,hpb⟩ := (pure_or C hg hor hab ha hb (S c)).mp hp
    exact ⟨g,a,b,hg,hor,hab,ha,hb,hpa,hpb,or_support C hg hor hab ha hb⟩

lemma no_lt_aux {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n+j) (hb : b < n+j)
    (hT : (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b)
    (hpa : Pure C (S c) a) (hpb : Pure C (S c) b)
    (hg : Good S C c u j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j')
    (hmin' : ∀ j', j' < j → ¬ Good S C c u' j')
    (hlt : u < u') (hu'a : u' ∈ T C a) : False := by
  obtain ⟨_,_,hu,u0,hu0,hu0lt⟩ := hg
  have h1 := no_below S C c u' j a hj ha hpa hu'a hmin'
  rw [hT,Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below S C c u j b hj hb hpb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma no_lt {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (hC : IsAO2 n C)
    (c : Fin m) (u u' : Fin n) (j : ℕ) (hg : Good S C c u j) (hg' : Good S C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j') (hmin' : ∀ j', j' < j → ¬ Good S C c u' j')
    (hlt : u < u') : False := by
  obtain ⟨g,a,b,_,_,_,ha,hb,hpa,hpb,hT⟩ := first_good_or S C hC c u j hg hmin
  have hu' := hg'.2.2.1
  rw [hT,Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux S C c u u' j a b hg.1 ha hb hT hpa hpb hg hmin hmin' hlt h
  · exact no_lt_aux S C c u u' j b a hg.1 hb ha
      (by rw [hT,Finset.union_comm]) hpb hpa hg hmin hmin' hlt h

lemma inj_core {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', u0 ∈ S c → u ∈ S c →
      u0 ∈ S c' → u ∈ S c' → c = c') (C : Circuit) (hC : IsAO2 n C)
    (c : Fin m) (u : Fin n) (c' : Fin m) (u' : Fin n) (j : ℕ)
    (hg : Good S C c u j) (hg' : Good S C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j')
    (hmin' : ∀ j', j' < j → ¬ Good S C c' u' j') : c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_,hp,hu,u0,hu0,hlt⟩ := hg
    have hsub := pure_support C hC (S c) (n+j) hp
    have hsub' := pure_support C hC (S c') (n+j) hg'.2.1
    exact hN u0 u (ne_of_lt hlt) c c' (hsub hu0) (hsub hu) (hsub' hu0) (hsub' hu)
  subst hcc
  refine ⟨rfl,?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt S C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt S C hC c u' u j hg' hg hmin' hmin h).elim

lemma pure_computes {n : ℕ} (C : Circuit) (w : ℕ) (L S : Finset (Fin n))
    (hc : ComputesOr n C w L) (hs : L ⊆ S) : Pure C S w := by
  have h := hc.2 (fun a : Fin n => decide (a ∉ S))
  change (val C (fun a : Fin n => decide (a ∉ S)) w = true ↔ _) at h
  unfold Pure
  apply Bool.eq_false_iff.mpr
  intro hv
  obtain ⟨i,hi,hi'⟩ := h.mp hv
  exact (of_decide_eq_true hi') (hs hi)

lemma leaf_min {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (L : Finset (Fin n))
    (c : Fin m) (hS : ∃ w < n+C.gates.length, Pure C (S c) w ∧ L ⊆ T C w)
    (u : Fin n) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good S C c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w,hw,hpure,hT⟩ := hS
  have hu' := hT hu
  have ht' := hT ht
  by_cases hwn : w < n
  · rw [T_input C w hwn,Finset.mem_singleton] at hu' ht'
    rw [hu',ht'] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    exact hng ⟨j,by omega,hpure,hu',t,ht',hlt⟩

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



def orGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    (C.gates[j]?.map fun g => isOrOp g.op).getD false = true

lemma count_gen {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', u0 ∈ S c → u ∈ S c → u0 ∈ S c' → u ∈ S c' → c = c')
    (C : Circuit) (hC : IsAO2 n C)
    (K : Finset (Fin m × Finset (Fin n)))
    (hK : ∀ k ∈ K, ∃ w < n+C.gates.length, Pure C (S k.1) w ∧ k.2 ⊆ T C w)
    (P : Finset (Σ _ : Fin m, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ (orGates C).card + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good S C q.1 q.2 j).card ≤ (orGates C).card := by
    refine card_le_of_unique_fibers
      (fun q j => Good S C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good S C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      obtain ⟨g,a,b,hg,hop,_⟩ := first_good_or S C hC q.1 q.2 (Nat.find hex)
          (Nat.find_spec hex) (fun j' hj' => Nat.find_min hex hj')
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.find_spec hex).1,?_⟩
      simp [hg,hop,isOrOp]
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core S hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good S C q.1 q.2 j).card ≤ K.card := by
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
      have hcomp := hK k hk
      rw [hqc] at hcomp
      have h1 := leaf_min S C k.2 c hcomp u hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min S C k.2 c hcomp u' hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good S C q.1 q.2 j)
  omega

lemma pure_family_ao_bound_active {m n : ℕ} (S U : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (U p).Nonempty → ∃ w < n+C.gates.length, Pure C (S p) w ∧ U p ⊆ T C w) :
    (∑ p : Fin m, (U p).card) ≤ (orGates C).card + (Finset.univ.filter fun p => (U p).Nonempty).card := by
  classical
  have hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ p q : Fin m,
      u0 ∈ S p → u ∈ S p → u0 ∈ S q → u ∈ S q → p = q := by
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
  let A : Finset (Fin m) := Finset.univ.filter fun p => (U p).Nonempty
  let K : Finset (Fin m × Finset (Fin n)) := A.image fun p => (p,U p)
  let I : Finset (Σ _ : Fin m, Fin n) := Finset.univ.sigma U
  have hK : ∀ k ∈ K,
      ∃ w < n+C.gates.length, Pure C (S k.1) w ∧ k.2 ⊆ T C w := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact hcomp p (Finset.mem_filter.mp hp).2
  have hP : ∀ q ∈ I, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2 := by
    intro q hq
    refine ⟨(q.1,U q.1), ?_, rfl, (Finset.mem_sigma.mp hq).2⟩
    exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨q.2, (Finset.mem_sigma.mp hq).2⟩⟩, rfl⟩
  have hbound := count_gen S hN C hC K hK I hP
  have hKcard : K.card ≤ A.card := Finset.card_image_le
  dsimp [A] at hKcard
  have hIcard : I.card = ∑ p : Fin m, (U p).card := Finset.card_sigma _ _
  omega

lemma linear_family_ao_bound_active {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (S p).Nonempty → ∃ w < n+C.gates.length, ComputesOr n C w (S p)) :
    (∑ p : Fin m, (S p).card) ≤ (orGates C).card +
      (Finset.univ.filter fun p => (S p).Nonempty).card := by
  apply pure_family_ao_bound_active S S hlin C hC
  intro p hp
  obtain ⟨w,hw,hcomp⟩ := hcomp p hp
  exact ⟨w,hw,pure_computes C w (S p) (S p) hcomp (by intro i hi; exact hi),
    by rw [T_computes C w (S p) hcomp]⟩

lemma linear_family_ao_cost {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (S p).Nonempty → ∃ w < n+C.gates.length, ComputesOr n C w (S p)) :
    (∑ p : Fin m, ((S p).card - 1)) ≤ (orGates C).card := by
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
  have hb := linear_family_ao_bound_active S hlin C hC hcomp
  omega


end PEqualNP.Outside.L_meta_2585_aux.MixedLinear

namespace PEqualNP.Outside.L_meta_2585.LeastNormalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.EdgeInvisible
open PEqualNP.Outside.L_meta_2585.normalization

lemma exists_least_normalized_essential (P L : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      D.size ≤ C.size ∧ circuitFun (P + L) D = circuitFun (P + L) C ∧
      (∀ E : Circuit, PEqualNP.TopForm.IsAO2 (P + L) E →
        circuitFun (P + L) E = circuitFun (P + L) C → D.size ≤ E.size) ∧
      (∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨GateOp.or, [a, b]⟩ →
        (PEqualNP.CircuitMoves.WireBelowOutput (P + L) D a ↔
          PEqualNP.CircuitMoves.WireBelowOutput (P + L) D b)) ∧
      (∀ (pre post : List Gate) (g : Gate), D.gates = pre ++ g :: post →
        ∃ p : Fin P, ∃ l : Fin L, I p l ∧
          circuitFun (P + L) (offGate pre post D.output)
            (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false) := by
  classical
  let good : Circuit → Prop := fun E =>
    PEqualNP.TopForm.IsAO2 (P + L) E ∧ circuitFun (P + L) E = circuitFun (P + L) C
  have hex : ∃ k : ℕ, ∃ E : Circuit, good E ∧ E.size = k :=
    ⟨C.size, C, ⟨hAO, rfl⟩, rfl⟩
  obtain ⟨E, hE, hsizeE⟩ := Nat.find_spec hex
  have hminE : ∀ A : Circuit, good A → E.size ≤ A.size := by
    intro A hA
    rw [hsizeE]
    exact Nat.find_min' hex ⟨A, hA, rfl⟩
  have hEf : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) E x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
    intro x
    rw [hE.2]
    exact hfun x
  obtain ⟨D, hD, hs, hDf, hnorm⟩ := normalized_incidence P L I E hE.1
    (incidence_output_lt P L I E hne hEf) hEf
  have hsame : circuitFun (P + L) D = circuitFun (P + L) C := by
    funext x
    rw [hDf, hfun]
  have hminD : ∀ A : Circuit, PEqualNP.TopForm.IsAO2 (P + L) A →
      circuitFun (P + L) A = circuitFun (P + L) C → D.size ≤ A.size := by
    intro A hA hAf
    rw [hs]
    exact hminE A ⟨hA, hAf⟩
  refine ⟨D, hD, hminD C hAO rfl, hsame, hminD, hnorm, ?_⟩
  intro pre post g hgs
  have hsplit : atGate pre post g D.output = D := by
    unfold atGate
    rw [← hgs]
  apply PEqualNP.Outside.L_meta_2585.EdgeEssential.least_gate_output_essential
    P L I pre post g D.output
  · rw [hsplit]
    exact hD
  · exact hne
  · rw [hsplit]
    exact hDf
  · intro A hA hAf
    rw [hsplit]
    apply hminD A hA
    funext x
    rw [hAf, hfun]

end PEqualNP.Outside.L_meta_2585.LeastNormalized

namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

open PEqualNP.CircuitLowerBounds

-- Two disjoint three-leaf stars amplify the repeated edges without amplifying
-- the gap between this dirty circuit and the ordinary read-one construction.

def C : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.and, [16, 17]⟩], 18⟩

def D : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩], 14⟩

def E : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]

def isLine (i : ℕ) : Bool := decide (2 ≤ i)

abbrev I (p : Fin 2) (l : Fin 6) : Prop :=
  (p = 0 ∧ l.val < 3) ∨ (p = 1 ∧ 3 ≤ l.val)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma valid_C : PEqualNP.TopForm.IsAO2 8 C := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma valid_D : PEqualNP.TopForm.IsAO2 8 D := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma no_four_cycle : ∀ p p' : Fin 2, ∀ l l' : Fin 6,
    p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma computes_C : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 C z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma computes_D : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 D z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma all_interior_not_below : ∀ w : Fin 18,
    ¬ PEqualNP.CircuitMoves.WireBelowOutput 8 C w.val := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma all_edges_double_reread : PEqualNP.ReadK.doubleReread C 8 isLine E = E := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_one_D : PEqualNP.ReadK.IsReadK 8 D 1 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma sizes : C.size = 11 ∧ D.size = 7 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma repeats_exceed_size_gap :
    C.size - D.size < (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample

namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

lemma replacement_optimal (T : PEqualNP.CircuitLowerBounds.Circuit)
    (hT : PEqualNP.TopForm.IsAO2 8 T)
    (hf : PEqualNP.MetaComplexity.circuitFun 8 T =
      PEqualNP.MetaComplexity.circuitFun 8 C) : D.size ≤ T.size := by
  have hTf : ∀ z : Fin 8 → Bool,
      PEqualNP.MetaComplexity.circuitFun 8 T z =
        decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
          z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by
    intro z
    rw [hf]
    exact computes_C z
  have hbound := PEqualNP.Outside.L_meta_2585.Support.incident_vertices_card_le
    2 6 I T hT hTf
  have hcard : (Finset.univ.filter (fun v : Fin (2 + 6) =>
      ∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        (v = Fin.castAdd 6 p ∨ v = Fin.natAdd 2 l))).card = 8 := by decide
  rw [hcard] at hbound
  change 7 ≤ T.size
  omega

lemma optimum_plus_repeats_too_large :
    C.size < D.size + (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample
