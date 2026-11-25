import PEqualNP.Defs

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
