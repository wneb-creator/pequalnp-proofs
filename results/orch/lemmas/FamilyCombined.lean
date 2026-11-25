import PEqualNP.Defs

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
