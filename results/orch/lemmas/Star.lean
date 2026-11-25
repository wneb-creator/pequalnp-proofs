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
