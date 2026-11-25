import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

lemma local_aux_elimination
    (c : Bool → Bool → Bool → Bool) (f : Bool → Bool → Bool)
    (hcorrect : ∀ a b, c a b (a && b) = f a b)
    (hjoin : f true true = (f true false || f false true))
    (hleft : c true false false = true → c true true false = true)
    (hright : c false true false = true → c true true false = true)
    (hseed : c true true false = true → c true true true = true) :
    ∀ a b, c a b false = f a b := by
  intro a b
  cases a with
  | false => exact hcorrect false b
  | true =>
    cases b with
    | false => exact hcorrect true false
    | true =>
      have hc11 := hcorrect true true
      have hc10 := hcorrect true false
      have hc01 := hcorrect false true
      change c true true true = f true true at hc11
      change c true false false = f true false at hc10
      change c false true false = f false true at hc01
      cases hz : c true true false with
      | false =>
        have h10 : f true false = false := by
          cases hh : f true false with
          | false => rfl
          | true =>
            have := hleft (hc10.trans hh)
            rw [hz] at this
            cases this
        have h01 : f false true = false := by
          cases hh : f false true with
          | false => rfl
          | true =>
            have := hright (hc01.trans hh)
            rw [hz] at this
            cases this
        rw [hjoin, h10, h01]
        rfl
      | true => exact (hseed hz).symm.trans hc11

lemma local_aux_obstruction
    (c : Bool → Bool → Bool → Bool) (f : Bool → Bool → Bool)
    (hcorrect : ∀ a b, c a b (a && b) = f a b)
    (hjoin : f true true = (f true false || f false true))
    (hessential : ∃ a b, c a b false ≠ f a b) :
    (c true false false = true ∧ c true true false = false) ∨
    (c false true false = true ∧ c true true false = false) ∨
    (c true true false = true ∧ c true true true = false) := by
  cases h10 : c true false false <;>
    cases h01 : c false true false <;>
      cases h00 : c true true false <;>
        cases h11 : c true true true <;>
          simp_all [Bool.or_eq_true]
  obtain ⟨⟨_, hft⟩, htf, htt⟩ := hcorrect
  simp_all

lemma local_aux_obstruction_iff
    (c : Bool → Bool → Bool → Bool) (f : Bool → Bool → Bool)
    (hcorrect : ∀ a b, c a b (a && b) = f a b)
    (hjoin : f true true = (f true false || f false true)) :
    (∃ a b, c a b false ≠ f a b) ↔
    (c true false false = true ∧ c true true false = false) ∨
    (c false true false = true ∧ c true true false = false) ∨
    (c true true false = true ∧ c true true true = false) := by
  constructor
  · exact local_aux_obstruction c f hcorrect hjoin
  · intro h
    refine ⟨true, true, ?_⟩
    rcases h with h | h | h
    · have hf : f true false = true := (hcorrect true false).symm.trans h.1
      rw [h.2, hjoin, hf, Bool.true_or]
      decide
    · have hf : f false true = true := (hcorrect false true).symm.trans h.1
      rw [h.2, hjoin, hf, Bool.or_true]
      decide
    · have hf : f true true = false := (hcorrect true true).symm.trans h.2
      rw [h.1, hf]
      decide

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
  x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def endpoint (x : Fin 10 → Bool) (a b : Bool) (i : Fin 10) : Bool :=
  if i = 0 then a else if i = 2 then b else x i

lemma petersen_endpoint_join (x : Fin 10 → Bool) :
    petersen (endpoint x true true) =
      (petersen (endpoint x true false) || petersen (endpoint x false true)) := by
  have h : ∀ v1 v3 v4 v5 v6 v7 v8 v9 : Bool,
      ((true && v1) || (v1 && true) || (true && v3) || (v3 && v4) || (v4 && true) || (true && v5) || (v1 && v6) || (true && v7) || (v3 && v8) || (v4 && v9) || (v5 && v7) || (v7 && v9) || (v9 && v6) || (v6 && v8) || (v8 && v5)) =
        (((true && v1) || (v1 && false) || (false && v3) || (v3 && v4) || (v4 && true) || (true && v5) || (v1 && v6) || (false && v7) || (v3 && v8) || (v4 && v9) || (v5 && v7) || (v7 && v9) || (v9 && v6) || (v6 && v8) || (v8 && v5)) ||
          ((false && v1) || (v1 && true) || (true && v3) || (v3 && v4) || (v4 && false) || (false && v5) || (v1 && v6) || (true && v7) || (v3 && v8) || (v4 && v9) || (v5 && v7) || (v7 && v9) || (v9 && v6) || (v6 && v8) || (v8 && v5))) := by decide
  exact h (x 1) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

lemma petersen_aux_elimination
    (c : (Fin 10 → Bool) → Bool → Bool)
    (hcorrect : ∀ x, c x (x 0 && x 2) = petersen x)
    (hleft : ∀ x, c (endpoint x true false) false = true →
      c (endpoint x true true) false = true)
    (hright : ∀ x, c (endpoint x false true) false = true →
      c (endpoint x true true) false = true)
    (hseed : ∀ x, c (endpoint x true true) false = true →
      c (endpoint x true true) true = true) :
    ∀ x, c x false = petersen x := by
  intro x
  have h := local_aux_elimination
    (fun a b t => c (endpoint x a b) t)
    (fun a b => petersen (endpoint x a b))
    (fun a b => by simpa [endpoint] using hcorrect (endpoint x a b))
    (petersen_endpoint_join x) (hleft x) (hright x) (hseed x)
    (x 0) (x 2)
  have heq : endpoint x (x 0) (x 2) = x := by
    funext i
    simp only [endpoint]
    split
    · rename_i hi
      subst i
      rfl
    · split
      · rename_i hi
        subst i
        rfl
      · rfl
  simpa only [heq] using h

lemma endpoint_self (x : Fin 10 → Bool) : endpoint x (x 0) (x 2) = x := by
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [endpoint]
  · by_cases h2 : i = 2
    · subst i
      simp [endpoint]
    · simp [endpoint, h0, h2]

def probe (C : PEqualNP.CircuitLowerBounds.Circuit) (r : Fin 10 → Fin 10)
    (x : Fin 10 → Bool) (a b t : Bool) : Bool :=
  C.eval (List.ofFn (endpoint x a b ∘ r) ++ [t])

lemma circuit_seed_obstruction
    (C : PEqualNP.CircuitLowerBounds.Circuit) (r : Fin 10 → Fin 10)
    (hcorrect : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [x 0 && x 2]) = petersen x)
    (hessential : ∃ x, C.eval (List.ofFn (x ∘ r) ++ [false]) ≠ petersen x) :
    ∃ x,
      (probe C r x true false false = true ∧ probe C r x true true false = false) ∨
      (probe C r x false true false = true ∧ probe C r x true true false = false) ∨
      (probe C r x true true false = true ∧ probe C r x true true true = false) := by
  obtain ⟨x, hx⟩ := hessential
  refine ⟨x, local_aux_obstruction (probe C r x)
    (fun a b => petersen (endpoint x a b)) ?_ (petersen_endpoint_join x) ?_⟩
  · intro a b
    simpa [probe, endpoint] using hcorrect (endpoint x a b)
  · refine ⟨x 0, x 2, ?_⟩
    simpa only [probe, endpoint_self] using hx

end PEqualNP.Outside.L_meta_1890_aux




namespace PEqualNP.Outside.L_meta_1890_aux.Monotone
open PEqualNP.CircuitLowerBounds

def bimp (a b : Bool) : Prop := a = true → b = true

def listLE (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, bimp (w.getD i false) (v.getD i false)

lemma getD_mono {w v : List Bool} (h : listLE w v) (i : Nat) :
    bimp (w.getD i false) (v.getD i false) := h.2 i

lemma snoc_mono {w v : List Bool} {a b : Bool}
    (h : listLE w v) (hab : bimp a b) :
    listLE (w ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [← h.1]
  by_cases hi : i < w.length
  · simpa [hi] using h.2 i
  · simp only [hi, ↓reduceIte]
    cases he : i - w.length with
    | zero => simpa [he] using hab
    | succ n => simp [bimp]

lemma and_mono (is : List Nat) {w v : List Bool} (h : listLE w v) :
    bimp (GateOp.and.eval (is.map fun i => w.getD i false))
      (GateOp.and.eval (is.map fun i => v.getD i false)) := by
  intro hall
  rw [GateOp.eval, List.all_eq_true] at hall ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact getD_mono h i (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))

lemma or_mono (is : List Nat) {w v : List Bool} (h : listLE w v) :
    bimp (GateOp.or.eval (is.map fun i => w.getD i false))
      (GateOp.or.eval (is.map fun i => v.getD i false)) := by
  intro hany
  rw [GateOp.eval, List.any_eq_true] at hany ⊢
  obtain ⟨b, hb, hbt⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact ⟨v.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, getD_mono h i hbt⟩

lemma gate_mono (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {w v : List Bool} (h : listLE w v) :
    bimp (g.op.eval (g.inputs.map fun i => w.getD i false))
      (g.op.eval (g.inputs.map fun i => v.getD i false)) := by
  rcases hop with hop | hop
  · rw [hop]
    exact and_mono g.inputs h
  · rw [hop]
    exact or_mono g.inputs h

lemma fold_mono (gs : List Gate) (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {w v : List Bool} (h : listLE w v) :
    listLE
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w)
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'
      exact hop g' (List.mem_cons_of_mem g hg')
    · exact snoc_mono h (gate_mono g (hop g (List.mem_cons_self)) h)

lemma circuit_eval_mono (C : Circuit)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    {w v : List Bool} (h : listLE w v) :
    bimp (C.eval w) (C.eval v) :=
  getD_mono (fold_mono C.gates hop h) C.output


lemma discard_auxiliary {α : Type}
    (F h : (α → Bool) → Bool) (C : (α → Bool) → Bool → Bool)
    (hmono : ∀ x y a b,
      (∀ i, x i = true → y i = true) → (a = true → b = true) →
      C x a = true → C y b = true)
    (hmin : ∀ x, F x = true → ∃ y,
      (∀ i, y i = true → x i = true) ∧ F y = true ∧ h y = false)
    (hcompute : ∀ x, C x (h x) = F x) :
    ∀ x, C x false = F x := by
  intro x
  cases hc : C x false with
  | false =>
    cases hf : F x with
    | false => rfl
    | true =>
      obtain ⟨y, hyx, hyF, hyh⟩ := hmin x hf
      have hcy : C y false = true := by rw [← hyh, hcompute y, hyF]
      have hc' := hmono y x false false hyx (fun ha => ha) hcy
      rw [hc] at hc'
      contradiction
  | true =>
    have hx : C x (h x) = true :=
      hmono x x false (h x) (fun _ ha => ha) (by intro hf; cases hf) hc
    rw [hcompute x] at hx
    exact hx.symm

lemma ofFn_mono {n : Nat} {x y : Fin n → Bool} (h : ∀ i, bimp (x i) (y i)) :
    listLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, hi, bimp]

lemma circuit_discard_aux {n m : Nat} (F h : (Fin n → Bool) → Bool)
    (C : Circuit) (r : Fin m → Fin n)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hmin : ∀ x, F x = true → ∃ y,
      (∀ i, y i = true → x i = true) ∧ F y = true ∧ h y = false)
    (hcompute : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [h x]) = F x) :
    ∀ x, C.eval (List.ofFn (x ∘ r) ++ [false]) = F x := by
  apply discard_auxiliary F h (fun x b => C.eval (List.ofFn (x ∘ r) ++ [b]))
  · intro x y a b hxy hab
    exact circuit_eval_mono C hop (snoc_mono (ofFn_mono (fun i => hxy (r i))) hab)
  · exact hmin
  · exact hcompute

def pairInput {α : Type} [DecidableEq α] (e : α × α) (i : α) : Bool :=
  decide (i = e.1 ∨ i = e.2)

def edgeFun {α : Type} (edges : List (α × α)) (x : α → Bool) : Bool :=
  edges.any (fun e => x e.1 && x e.2)

lemma edge_minimum {α : Type} [DecidableEq α] (edges : List (α × α))
    (aux : (α → Bool) → Bool)
    (haux : ∀ e ∈ edges, aux (pairInput e) = false) :
    ∀ x, edgeFun edges x = true → ∃ y,
      (∀ i, y i = true → x i = true) ∧ edgeFun edges y = true ∧ aux y = false := by
  intro x hx
  obtain ⟨e, he, hxt⟩ := List.any_eq_true.mp hx
  refine ⟨pairInput e, ?_, ?_, haux e he⟩
  · intro i hi
    have hi' : i = e.1 ∨ i = e.2 := by simpa [pairInput] using hi
    rcases hi' with rfl | rfl
    · exact (Bool.and_eq_true_iff.mp hxt).1
    · exact (Bool.and_eq_true_iff.mp hxt).2
  · exact List.any_eq_true.mpr ⟨e, he, by simp [pairInput]⟩

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

lemma petersen_pair_aux_false :
    ∀ e ∈ petersenEdges, (pairInput e 0 && pairInput e 2) = false := by
  decide

lemma petersen_discard_aux (C : Circuit) (r : Fin 10 → Fin 10)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hcompute : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [x 0 && x 2]) = edgeFun petersenEdges x) :
    ∀ x, C.eval (List.ofFn (x ∘ r) ++ [false]) = edgeFun petersenEdges x :=
  circuit_discard_aux (edgeFun petersenEdges) (fun x => x 0 && x 2) C r hop
    (edge_minimum petersenEdges (fun x => x 0 && x 2) petersen_pair_aux_false) hcompute


def petersenFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma edgeFun_petersen (x : Fin 10 → Bool) :
    edgeFun petersenEdges x = petersenFunction x := by
  simp [edgeFun, petersenEdges, petersenFunction, Bool.or_assoc]

lemma petersen_discard_aux_exact (C : Circuit) (r : Fin 10 → Fin 10)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hcompute : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [x 0 && x 2]) = petersenFunction x) :
    ∀ x, C.eval (List.ofFn (x ∘ r) ++ [false]) = petersenFunction x := by
  have h := petersen_discard_aux C r hop (fun x => (hcompute x).trans (edgeFun_petersen x).symm)
  intro x
  exact (h x).trans (edgeFun_petersen x)

def rewire (rho : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map rho⟩

def rewireCircuit (C : Circuit) (rho : Nat → Nat) : Circuit :=
  ⟨C.gates.map (rewire rho), rho C.output⟩

lemma getD_append_left (w v : List Bool) (i : Nat) (b : Bool) (hi : i < w.length) :
    (w ++ v).getD i b = w.getD i b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (w v : List Bool) (i : Nat) (b : Bool) (hi : w.length ≤ i) :
    (w ++ v).getD i b = v.getD (i - w.length) b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_eq_default (w : List Bool) (b : Bool) {i : Nat} (hi : w.length ≤ i) :
    w.getD i b = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma getD_ofFn {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp

lemma rewire_run {n m B : Nat} (rho : Nat → Nat)
    (early : ∀ i, i < n → rho i < m ∨ B ≤ rho i)
    (late : ∀ i, n ≤ i → rho i = m + (i - n))
    (gs : List Gate) (u w : List Bool) (base : n ≤ u.length)
    (lens : u.length + m = w.length + n) (past : w.length + gs.length ≤ B)
    (agree : ∀ i, w.getD (rho i) false = u.getD i false) :
    ∀ i, ((⟨gs.map (rewire rho), 0⟩ : Circuit).wires w).getD (rho i) false =
      ((⟨gs, 0⟩ : Circuit).wires u).getD i false := by
  induction gs generalizing u w with
  | nil => exact agree
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun i => u.getD i false)
    have step : (rewire rho g).op.eval ((rewire rho g).inputs.map fun i => w.getD i false) = val := by
      simp only [rewire, List.map_map, Function.comp_def, agree, val]
    change ∀ i, ((⟨gs.map (rewire rho), 0⟩ : Circuit).wires (w ++ [_])).getD (rho i) false =
      ((⟨gs, 0⟩ : Circuit).wires (u ++ [val])).getD i false
    rw [step]
    simp only [List.length_cons] at past
    apply ih _ _ (by simp; omega) (by simp; omega) (by simp; omega)
    intro i
    by_cases hi : i < u.length
    · rw [getD_append_left _ _ _ _ hi, ← agree i]
      by_cases hh : rho i < w.length
      · exact getD_append_left _ _ _ _ hh
      · have hr : B ≤ rho i := by
          by_cases hn : i < n
          · rcases early i hn with h | h <;> omega
          · rw [late i (by omega)] at hh
            omega
        rw [getD_eq_default (w ++ [val]) false (by simp; omega),
          getD_eq_default w false (by omega)]
    · have eq := late i (by omega)
      rw [getD_append_right _ _ _ _ (by omega), getD_append_right _ _ _ _ (by omega)]
      congr 1; omega

def eraseSeedIndex {n : Nat} (s : Nat) (r : Fin n → Fin n) (i : Nat) : Nat :=
  if h : i < n then (r ⟨i, h⟩).val else if i = n then n + s else i - 1

lemma eraseSeed_early {n s : Nat} (r : Fin n → Fin n) (i : Nat) (hi : i < n + 1) :
    eraseSeedIndex s r i < n ∨ n + s ≤ eraseSeedIndex s r i := by
  by_cases h : i < n
  · left
    simp only [eraseSeedIndex, h, ↓reduceDIte]
    exact (r ⟨i, h⟩).isLt
  · have e : i = n := by omega
    right
    simp [eraseSeedIndex, e]

lemma eraseSeed_late {n s : Nat} (r : Fin n → Fin n) (i : Nat) (hi : n + 1 ≤ i) :
    eraseSeedIndex s r i = n + (i - (n + 1)) := by
  have h : ¬ i < n := by omega
  have e : i ≠ n := by omega
  simp only [eraseSeedIndex, h, ↓reduceDIte, e, ↓reduceIte]
  omega

lemma eraseSeed_initial {n s : Nat} (r : Fin n → Fin n) (x : Fin n → Bool) (i : Nat) :
    (List.ofFn x).getD (eraseSeedIndex s r i) false =
      (List.ofFn (x ∘ r) ++ [false]).getD i false := by
  by_cases h : i < n
  · rw [getD_append_left _ _ _ _ (by simpa using h)]
    simp only [eraseSeedIndex, h, ↓reduceDIte]
    exact (getD_ofFn x (r ⟨i, h⟩)).trans (getD_ofFn (x ∘ r) ⟨i, h⟩).symm
  · by_cases e : i = n
    · subst i
      simp only [eraseSeedIndex, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte]
      rw [getD_eq_default _ false (by simp),
        getD_append_right _ _ _ _ (by simp)]
      simp
    · have hhi : n + 1 ≤ i := by omega
      simp only [eraseSeedIndex, h, ↓reduceDIte, e, ↓reduceIte]
      rw [getD_eq_default _ false (by simp; omega),
        getD_eq_default _ false (by simp; omega)]

lemma eraseSeed_eval {n : Nat} (C : Circuit) (r : Fin n → Fin n) (x : Fin n → Bool) :
    (rewireCircuit C (eraseSeedIndex C.gates.length r)).eval (List.ofFn x) =
      C.eval (List.ofFn (x ∘ r) ++ [false]) := by
  exact rewire_run (eraseSeedIndex C.gates.length r) (eraseSeed_early r)
    (eraseSeed_late r) C.gates (List.ofFn (x ∘ r) ++ [false]) (List.ofFn x)
    (by simp) (by simp; omega) (by simp) (eraseSeed_initial r x) C.output

lemma rewire_length (C : Circuit) (rho : Nat → Nat) :
    (rewireCircuit C rho).gates.length = C.gates.length := by
  simp [rewireCircuit]

lemma rewire_gate_property (C : Circuit) (rho : Nat → Nat) (P : GateOp → Nat → Prop)
    (hP : ∀ g ∈ C.gates, P g.op g.inputs.length) :
    ∀ g ∈ (rewireCircuit C rho).gates, P g.op g.inputs.length := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [rewire] using hP g' hg'

lemma petersen_ordinary (C : Circuit) (r : Fin 10 → Fin 10)
    (hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [x 0 && x 2]) = petersenFunction x) :
    ∃ D : Circuit, D.gates.length = C.gates.length ∧
      (∀ g ∈ D.gates, g.op = .and ∨ g.op = .or) ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      ∀ x, D.eval (List.ofFn x) = petersenFunction x := by
  refine ⟨rewireCircuit C (eraseSeedIndex C.gates.length r), rewire_length _ _, ?_, ?_, ?_⟩
  · exact rewire_gate_property C _ (fun op _ => op = .and ∨ op = .or) hop
  · exact rewire_gate_property C _ (fun _ len => len ≤ 2) hin
  · intro x
    rw [eraseSeed_eval]
    exact petersen_discard_aux_exact C r hop hcompute x

lemma petersen_not_free_normalize (C : Circuit) (r : Fin 10 → Fin 10)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hnot : ∀ g ∈ C.gates, g.op ≠ .not)
    (hcompute : ∀ x, C.eval (List.ofFn (x ∘ r) ++ [x 0 && x 2]) = petersenFunction x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      (∀ g ∈ D.gates, g.op ≠ .not) ∧ D.size = C.size ∧
      ∀ x, D.eval (List.ofFn x) = petersenFunction x := by
  have hop : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    have ho : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
    rcases ho with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hnot g hg hn).elim
  obtain ⟨D, hs, hDop, hDin, hDf⟩ :=
    petersen_ordinary C r hop (fun g hg => (hC g hg).2) hcompute
  refine ⟨D, ?_, ?_, hs, hDf⟩
  · intro g hg
    refine ⟨?_, hDin g hg⟩
    rcases hDop g hg with h | h <;> simp [h]
  · intro g hg
    rcases hDop g hg with h | h <;> simp [h]

end PEqualNP.Outside.L_meta_1890_aux.Monotone


namespace PEqualNP.Outside.L_meta_1890_aux.NegativeInfluence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bimp (a b : Bool) : Prop := a = true → b = true

def listLE (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, bimp (w.getD i false) (v.getD i false)

lemma getD_mono {w v : List Bool} (h : listLE w v) (i : Nat) :
    bimp (w.getD i false) (v.getD i false) := h.2 i

lemma snoc_mono {w v : List Bool} {a b : Bool}
    (h : listLE w v) (hab : bimp a b) :
    listLE (w ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [← h.1]
  by_cases hi : i < w.length
  · simpa [hi] using h.2 i
  · simp only [hi, ↓reduceIte]
    cases he : i - w.length with
    | zero => simpa [he] using hab
    | succ n => simp [bimp]

lemma and_mono (is : List Nat) {w v : List Bool} (h : listLE w v) :
    bimp (GateOp.and.eval (is.map fun i => w.getD i false))
      (GateOp.and.eval (is.map fun i => v.getD i false)) := by
  intro hall
  rw [GateOp.eval, List.all_eq_true] at hall ⊢
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact getD_mono h i (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))

lemma or_mono (is : List Nat) {w v : List Bool} (h : listLE w v) :
    bimp (GateOp.or.eval (is.map fun i => w.getD i false))
      (GateOp.or.eval (is.map fun i => v.getD i false)) := by
  intro hany
  rw [GateOp.eval, List.any_eq_true] at hany ⊢
  obtain ⟨b, hb, hbt⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact ⟨v.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, getD_mono h i hbt⟩

lemma gate_mono (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {w v : List Bool} (h : listLE w v) :
    bimp (g.op.eval (g.inputs.map fun i => w.getD i false))
      (g.op.eval (g.inputs.map fun i => v.getD i false)) := by
  rcases hop with hop | hop
  · rw [hop]
    exact and_mono g.inputs h
  · rw [hop]
    exact or_mono g.inputs h


def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

lemma negative_gate (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {w v : List Bool} (h : listLE w v)
    (hdrop : ¬ bimp (g.op.eval (g.inputs.map fun i => w.getD i false))
      (g.op.eval (g.inputs.map fun i => v.getD i false))) :
    g.op = .not ∧
      (g.inputs.map fun i => w.getD i false).headD false = false ∧
      (g.inputs.map fun i => v.getD i false).headD false = true := by
  rcases hop with hop | hop | hop
  · exact False.elim (hdrop (gate_mono g (Or.inl hop) h))
  · exact False.elim (hdrop (gate_mono g (Or.inr hop) h))
  · refine ⟨hop, ?_⟩
    rw [hop] at hdrop
    simp only [GateOp.eval, bimp] at hdrop
    cases ha : (g.inputs.map fun i => w.getD i false).headD false <;>
      cases hb : (g.inputs.map fun i => v.getD i false).headD false <;>
        simp_all

lemma negative_fold (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {w v : List Bool} (h : listLE w v) (out : Nat)
    (htrue : (run gs w).getD out false = true)
    (hfalse : (run gs v).getD out false = false) :
    ∃ (pre post : List Gate) (g : Gate), gs = pre ++ g :: post ∧
      g.op = .not ∧ listLE (run pre w) (run pre v) ∧
      (g.inputs.map fun i => (run pre w).getD i false).headD false = false ∧
      (g.inputs.map fun i => (run pre v).getD i false).headD false = true := by
  induction gs generalizing w v with
  | nil =>
    have hx := h.2 out htrue
    change v.getD out false = false at hfalse
    rw [hfalse] at hx
    cases hx
  | cons g gs ih =>
    by_cases hc : bimp (g.op.eval (g.inputs.map fun i => w.getD i false))
        (g.op.eval (g.inputs.map fun i => v.getD i false))
    · obtain ⟨pre, post, q, heq, hq, hprefix, hlo, hhi⟩ :=
        ih (fun q hq => hop q (List.mem_cons_of_mem _ hq)) (snoc_mono h hc) htrue hfalse
      refine ⟨g :: pre, post, q, ?_, hq, hprefix, hlo, hhi⟩
      simp [heq]
    · obtain ⟨hg, hlo, hhi⟩ := negative_gate g (hop g List.mem_cons_self) h hc
      exact ⟨[], gs, g, rfl, hg, h, hlo, hhi⟩

lemma circuit_negative_influence (C : Circuit) (hfan : FanInTwo C)
    {w v : List Bool} (h : listLE w v)
    (htrue : C.eval w = true) (hfalse : C.eval v = false) :
    ∃ (pre post : List Gate) (g : Gate), C.gates = pre ++ g :: post ∧
      g.op = .not ∧ listLE (run pre w) (run pre v) ∧
      (g.inputs.map fun i => (run pre w).getD i false).headD false = false ∧
      (g.inputs.map fun i => (run pre v).getD i false).headD false = true := by
  apply negative_fold C.gates _ h C.output htrue hfalse
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hg).1

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma circuit_negative_reader (C : Circuit) (hfan : FanInTwo C)
    {w v : List Bool} (h : listLE w v)
    (htrue : C.eval w = true) (hfalse : C.eval v = false) :
    ∃ (pre post : List Gate) (g : Gate) (pin : Nat) (rest : List Nat),
      C.gates = pre ++ g :: post ∧ g.op = .not ∧ g.inputs = pin :: rest ∧
      pin < w.length + pre.length ∧
      listLE (run pre w) (run pre v) ∧
      (run pre w).getD pin false = false ∧ (run pre v).getD pin false = true := by
  obtain ⟨pre, post, g, hsplit, hg, hpre, hlo, hhi⟩ :=
    circuit_negative_influence C hfan h htrue hfalse
  cases hins : g.inputs with
  | nil => simp [hins] at hhi
  | cons pin rest =>
    simp only [hins, List.map_cons, List.headD_cons] at hlo hhi
    refine ⟨pre, post, g, pin, rest, hsplit, hg, hins, ?_, hpre, hlo, hhi⟩
    by_contra hh
    have hn : (run pre v).length ≤ pin := by rw [run_length, ← h.1]; omega
    have hf : (run pre v).getD pin false = false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn, Option.getD_none]
    rw [hf] at hhi
    cases hhi

end PEqualNP.Outside.L_meta_1890_aux.NegativeInfluence


namespace PEqualNP.Outside.L_meta_1890_aux.EffectiveReaders

open PEqualNP.CircuitLowerBounds

def effectiveInputs (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def AgreeExcept (i : Nat) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ j, j ≠ i → w.getD j false = w'.getD j false

lemma eval_ignore (g : Gate) (i : Nat) (w w' : List Bool)
    (h : AgreeExcept i w w') (hi : i ∉ effectiveInputs g) :
    g.op.eval (g.inputs.map fun j => w.getD j false) =
      g.op.eval (g.inputs.map fun j => w'.getD j false) := by
  obtain ⟨op, ins⟩ := g
  have hm (hm : i ∉ ins) : ins.map (fun j => w.getD j false) =
      ins.map (fun j => w'.getD j false) := by
    apply List.map_congr_left
    intro j hj
    exact h.2 j (fun e => hm (e ▸ hj))
  cases op with
  | and => rw [hm hi]
  | or => rw [hm hi]
  | mod m => rw [hm hi]
  | maj => rw [hm hi]
  | not =>
    cases ins with
    | nil => rfl
    | cons j js =>
      have hj : j ≠ i := by simpa [effectiveInputs, eq_comm] using hi
      simpa [GateOp.eval] using congrArg Bool.not (h.2 j hj)

lemma agree_append (i : Nat) (w w' : List Bool) (b : Bool)
    (h : AgreeExcept i w w') : AgreeExcept i (w ++ [b]) (w' ++ [b]) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro j hj
  have hlen := h.1
  by_cases hjw : j < w.length
  · rw [List.getD_append _ _ _ _ hjw,
      List.getD_append _ _ _ _ (by simpa [← h.1] using hjw)]
    exact h.2 j hj
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), h.1]

lemma wires_ignore (gs : List Gate) (i : Nat)
    (hi : ∀ g ∈ gs, i ∉ effectiveInputs g) :
    ∀ w w' : List Bool, AgreeExcept i w w' →
      AgreeExcept i ((⟨gs, 0⟩ : Circuit).wires w) ((⟨gs, 0⟩ : Circuit).wires w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    change AgreeExcept i
      ((⟨gs, 0⟩ : Circuit).wires (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]))
      ((⟨gs, 0⟩ : Circuit).wires (w' ++ [g.op.eval (g.inputs.map fun j => w'.getD j false)]))
    rw [← eval_ignore g i w w' h (hi g List.mem_cons_self)]
    apply ih (fun g hg => hi g (List.mem_cons_of_mem _ hg))
    exact agree_append i w w' _ h

lemma eval_ignore_wire (C : Circuit) (i : Nat)
    (hi : ∀ g ∈ C.gates, i ∉ effectiveInputs g) (hout : C.output ≠ i)
    (w w' : List Bool) (h : AgreeExcept i w w') : C.eval w = C.eval w' := by
  exact (wires_ignore C.gates i hi w w' h).2 C.output hout

lemma effective_reader_of_difference (C : Circuit) (i : Nat) (hout : C.output ≠ i)
    (w w' : List Bool) (h : AgreeExcept i w w') (he : C.eval w ≠ C.eval w') :
    ∃ g ∈ C.gates, i ∈ effectiveInputs g := by
  apply Classical.byContradiction
  intro hr
  apply he
  apply eval_ignore_wire C i _ hout w w' h
  intro g hg hread
  exact hr ⟨g, hg, hread⟩


lemma agree_ofFn_append {n : Nat} (i : Fin n) (x y : Fin n → Bool) (b : Bool)
    (h : ∀ j, j ≠ i → x j = y j) :
    AgreeExcept i.val (List.ofFn x ++ [b]) (List.ofFn y ++ [b]) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hne : (⟨j, hjn⟩ : Fin n) ≠ i := by
      intro he
      exact hj (congrArg Fin.val he)
    have he := h ⟨j, hjn⟩ hne
    rw [List.getD_append _ _ _ _ (by simpa using hjn),
      List.getD_append _ _ _ _ (by simpa using hjn)]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hjn] using he
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hjn),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hjn)]
    simp

lemma wires_preserve_input (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    ((⟨gs, 0⟩ : Circuit).wires w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((⟨gs, 0⟩ : Circuit).wires (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def point (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i)
def pairpoint (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i ∨ j = 1)
def seed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 && x 2]

lemma point_false : ∀ i : Fin 10, petersen (point i) = false := by decide

lemma read_ofFn {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]

lemma read_seed (x : Fin 10 → Bool) (i : Fin 10) : (seed x).getD i.val false = x i := by
  unfold seed
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact read_ofFn x i

lemma output_not_input (C : Circuit) (hC : ∀ x, C.eval (seed x) = petersen x) (i : Fin 10) :
    C.output ≠ i.val := by
  intro hi
  have he := hC (point i)
  change ((⟨C.gates, 0⟩ : Circuit).wires (seed (point i))).getD C.output false = _ at he
  rw [hi, wires_preserve_input C.gates _ _ (by simp [seed]; omega), read_seed, point_false] at he
  simp [point] at he

lemma endpoint_samples : ∀ i : Fin 10, (i = 0 ∨ i = 2) →
    (∀ j, j ≠ i → point 1 j = pairpoint i j) ∧
    ((point 1 0 && point 1 2) = (pairpoint i 0 && pairpoint i 2)) ∧
    petersen (point 1) ≠ petersen (pairpoint i) := by decide

lemma endpoint_has_effective_reader (C : Circuit)
    (hC : ∀ x, C.eval (seed x) = petersen x) (i : Fin 10) (hi : i = 0 ∨ i = 2) :
    ∃ g ∈ C.gates, i.val ∈ effectiveInputs g := by
  have hs := endpoint_samples i hi
  apply effective_reader_of_difference C i.val (output_not_input C hC i)
    (seed (point 1)) (seed (pairpoint i))
  · unfold seed
    rw [hs.2.1]
    exact agree_ofFn_append i (point 1) (pairpoint i) _ hs.1
  · rw [hC, hC]
    exact hs.2.2


lemma effectiveInputs_length (g : Gate) : (effectiveInputs g).length ≤ g.inputs.length := by
  cases g with
  | mk op ins => cases op <;> simp [effectiveInputs, Nat.min_le_right]

lemma list_no_three (l : List Nat) (h : l.length ≤ 2)
    (a b c : Nat) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) : False := by
  cases l with
  | nil => simp at ha
  | cons u l =>
    cases l with
    | nil => simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc; omega
    | cons v l =>
      cases l with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega
      | cons w l => simp only [List.length_cons] at h; omega

lemma different_endpoint_reader (C : Circuit)
    (hC : ∀ x, C.eval (seed x) = petersen x)
    (H : Gate) (hH : H.inputs.length ≤ 2) (k : Nat) (hk0 : k ≠ 0) (hk2 : k ≠ 2)
    (hk : k ∈ effectiveInputs H) :
    ∃ i : Fin 10, (i = 0 ∨ i = 2) ∧
      ∃ G ∈ C.gates, i.val ∈ effectiveInputs G ∧ G ≠ H := by
  obtain ⟨G0, hG0, hr0⟩ := endpoint_has_effective_reader C hC 0 (Or.inl rfl)
  obtain ⟨G2, hG2, hr2⟩ := endpoint_has_effective_reader C hC 2 (Or.inr rfl)
  by_cases he0 : G0 = H
  · by_cases he2 : G2 = H
    · have hlen := effectiveInputs_length H
      exact False.elim (list_no_three (effectiveInputs H) (by omega)
        0 2 k (by decide) (Ne.symm hk0) (Ne.symm hk2)
        (he0 ▸ hr0) (he2 ▸ hr2) hk)
    · exact ⟨2, Or.inr rfl, G2, hG2, hr2, he2⟩
  · exact ⟨0, Or.inl rfl, G0, hG0, hr0, he0⟩

end PEqualNP.Outside.L_meta_1890_aux.EffectiveReaders


namespace PEqualNP.Outside.L_meta_1890_aux.EffectiveReaderIndexed

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1890_aux.EffectiveReaders

lemma indexed_endpoint_reader (C : Circuit)
    (hC : ∀ x, C.eval (seed x) = petersen x)
    (pN pH : Nat) (H : Gate) (hHlen : H.inputs.length ≤ 2)
    (hN : C.gates[pN]? = some ⟨GateOp.not, [10]⟩)
    (hH : C.gates[pH]? = some H) (hread : 11+pN ∈ effectiveInputs H) :
    ∃ i : Fin 10, (i = 0 ∨ i = 2) ∧ ∃ p G,
      C.gates[p]? = some G ∧ i.val ∈ effectiveInputs G ∧ p ≠ pN ∧ p ≠ pH := by
  obtain ⟨i, hi, G, hGmem, hreadG, hne⟩ := different_endpoint_reader C hC H hHlen
    (11+pN) (by omega) (by omega) hread
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hGmem
  refine ⟨i, hi, p, G, hp, hreadG, ?_, ?_⟩
  · intro he
    have hgate : G = ⟨GateOp.not, [10]⟩ := by
      apply Option.some.inj
      calc
        some G = C.gates[p]? := hp.symm
        _ = C.gates[pN]? := by rw [he]
        _ = some ⟨GateOp.not, [10]⟩ := hN
    rw [hgate] at hreadG
    have hival := i.isLt
    simp [effectiveInputs] at hreadG
    omega
  · intro he
    apply hne
    apply Option.some.inj
    calc
      some G = C.gates[p]? := hp.symm
      _ = C.gates[pH]? := by rw [he]
      _ = some H := hH

end PEqualNP.Outside.L_meta_1890_aux.EffectiveReaderIndexed


namespace PEqualNP.Outside.L_meta_1890_aux.Propagation
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]


def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


abbrev Stat := Sum Bool ℕ

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

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]


lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp


def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

lemma elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)



lemma const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'



lemma elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega


lemma compile_of_inv {α : Type} (n : ℕ) (C : Circuit) (st : List Stat)
    (old new : α → List Bool) (hnew : ∀ x, (new x).length = n)
    (hok : ∀ g ∈ C.gates, NOk g)
    (hi : ∀ x, Inv n (new x) (old x) (st, []))
    (hnc : ∃ x y, C.eval (old x) ≠ C.eval (old y))
    (S : Finset ℕ)
    (hS : ∀ p ∈ S, ∃ g, C.gates[p]? = some g ∧ ∃ a ∈ g.inputs,
      a < st.length + p ∧ ∃ c,
      (elim n C.gates (st, [])).1.getD a (Sum.inl false) = Sum.inl c) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + S.card ≤ C.size ∧ ∀ x, D.eval (new x) = C.eval (old x) := by
  let acc := elim n C.gates (st, [])
  have hval (x : α) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (new x)) =
        C.eval (old x) := by
    exact (inv_elim n (new x) (hnew x) C.gates (old x) (st, [])
      (fun g hg => (hok g hg).1) (hi x)).2 C.output |>.2
  cases hout : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    exact False.elim (hxy (by rw [← hval x, ← hval y, hout]; rfl))
  | inr o =>
    refine ⟨⟨acc.2, o⟩, elim_ok n C.gates (st, []) (by simp), ?_, ?_⟩
    · simpa [acc, Circuit.size] using elim_count n (st, []) C.gates hok S hS
    · intro x
      have hx := hval x
      rw [hout] at hx
      exact hx

lemma const_of_not_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : ℕ) (a : ℕ) (hp : gs[p]? = some ⟨GateOp.not, [a]⟩)
    (hlt : a < acc.1.length + p) (c : Bool)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) :
    (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl (!c) := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p _ hp
  rw [elim_split_getD_lt n pre _ post acc a _ hlt] at hc
  rw [elim_split_getD n pre _ post acc _ _ (le_refl _)]
  change ((elim n pre acc).1 ++ [_]).getD (acc.1.length + pre.length) (Sum.inl false) = _
  rw [← elim_fst_len n pre acc, getD_snoc_eq]
  simp only [List.map_cons, List.map_nil, hc, simplify, simpNot]

lemma const_of_and_false (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p a b : ℕ) (hp : gs[p]? = some ⟨GateOp.and, [a,b]⟩)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl false := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p _ hp
  rw [elim_split_getD_lt n pre _ post acc a _ hlt] at hc
  rw [elim_split_getD n pre _ post acc _ _ (le_refl _)]
  change ((elim n pre acc).1 ++ [_]).getD (acc.1.length + pre.length) (Sum.inl false) = _
  rw [← elim_fst_len n pre acc, getD_snoc_eq]
  simp only [List.map_cons, List.map_nil, hc, simplify]
  cases (elim n pre acc).1.getD b (Sum.inl false) <;> simp [simpAnd]

lemma const_of_and_false_right (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p a b : ℕ) (hp : gs[p]? = some ⟨GateOp.and, [a,b]⟩)
    (hlt : b < acc.1.length + p)
    (hc : (elim n gs acc).1.getD b (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).1.getD (acc.1.length + p) (Sum.inl false) = Sum.inl false := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p _ hp
  rw [elim_split_getD_lt n pre _ post acc b _ hlt] at hc
  rw [elim_split_getD n pre _ post acc _ _ (le_refl _)]
  change ((elim n pre acc).1 ++ [_]).getD (acc.1.length + pre.length) (Sum.inl false) = _
  rw [← elim_fst_len n pre acc, getD_snoc_eq]
  simp only [List.map_cons, List.map_nil, hc, simplify]
  cases (elim n pre acc).1.getD a (Sum.inl false) <;> simp [simpAnd]


lemma compile_four_after_and_not {α : Type} (n : ℕ) (C : Circuit) (st : List Stat)
    (old new : α → List Bool) (hnew : ∀ x, (new x).length = n)
    (hok : ∀ g ∈ C.gates, NOk g)
    (hi : ∀ x, Inv n (new x) (old x) (st, []))
    (hnc : ∃ x y, C.eval (old x) ≠ C.eval (old y))
    (k l p0 p1 p2 p3 : ℕ) (g2 g3 : Gate)
    (hk : k < st.length) (hfixed : st.getD k (Sum.inl false) = Sum.inl false)
    (hseed : C.gates[p0]? = some ⟨GateOp.and, [k,l]⟩ ∨
      C.gates[p0]? = some ⟨GateOp.and, [l,k]⟩)
    (hnot : C.gates[p1]? = some ⟨GateOp.not, [st.length+p0]⟩)
    (hr2 : C.gates[p2]? = some g2) (hin2 : st.length+p1 ∈ g2.inputs)
    (hr3 : C.gates[p3]? = some g3) (hin3 : k ∈ g3.inputs)
    (h01 : p0 < p1) (h12 : p1 < p2)
    (h03 : p0 ≠ p3) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + 4 ≤ C.size ∧ ∀ x, D.eval (new x) = C.eval (old x) := by
  let acc := (st, ([] : List Gate))
  have hc0 : (elim n C.gates acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ C.gates acc hk]
    exact hfixed
  have hc1 : (elim n C.gates acc).1.getD (st.length+p0) (Sum.inl false) =
      Sum.inl false := by
    rcases hseed with hseed | hseed
    · exact const_of_and_false n C.gates acc p0 k l hseed (by simpa [acc] using hk.trans_le (Nat.le_add_right _ _)) hc0
    · exact const_of_and_false_right n C.gates acc p0 l k hseed (by simpa [acc] using hk.trans_le (Nat.le_add_right _ _)) hc0
  have hc2 : (elim n C.gates acc).1.getD (st.length+p1) (Sum.inl false) =
      Sum.inl true := by
    exact const_of_not_read n C.gates acc p1 (st.length+p0) hnot (by dsimp [acc]; omega) false hc1
  let S : Finset ℕ := {p0,p1,p2,p3}
  have hcard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem (by simp [h03,show p0 ≠ p1 by omega,show p0 ≠ p2 by omega]),
      Finset.card_eq_three.2 ⟨p1,p2,p3,by omega,h13,h23,rfl⟩]
  obtain ⟨D,hD,hs,hDval⟩ := compile_of_inv n C st old new hnew hok hi hnc S (by
    intro p hp
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rcases hseed with hseed | hseed
      · exact ⟨_,hseed,k,by simp,by omega,false,hc0⟩
      · exact ⟨_,hseed,k,by simp,by omega,false,hc0⟩
    · exact ⟨_,hnot,st.length+p0,by simp,by omega,false,hc1⟩
    · exact ⟨_,hr2,st.length+p1,hin2,by omega,true,hc2⟩
    · exact ⟨_,hr3,k,hin3,by omega,false,hc0⟩)
  exact ⟨D,hD,by simpa only [hcard] using hs,hDval⟩

lemma getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp



def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Sum.inl b) (fun k : Fin n => Sum.inr k.val) : Fin (n + 1) → Stat)

lemma statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

lemma statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Sum.inl false) = Sum.inl b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

lemma statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Sum.inl false) = Sum.inr k.val := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

lemma inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Sum.inl false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Sum.inl false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


lemma four_after_and_not_restrict (n : ℕ) (C : Circuit)
    (hok : ∀ g ∈ C.gates, NOk g) (i : Fin (n+1))
    (hnc : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn (Fin.insertNth i false x)) ≠
        C.eval (List.ofFn (Fin.insertNth i false y)))
    (l p0 p1 p2 p3 : ℕ) (g2 g3 : Gate)
    (hseed : C.gates[p0]? = some ⟨GateOp.and, [i.val,l]⟩ ∨
      C.gates[p0]? = some ⟨GateOp.and, [l,i.val]⟩)
    (hnot : C.gates[p1]? = some ⟨GateOp.not, [n+1+p0]⟩)
    (hr2 : C.gates[p2]? = some g2) (hin2 : n+1+p1 ∈ g2.inputs)
    (hr3 : C.gates[p3]? = some g3) (hin3 : i.val ∈ g3.inputs)
    (h01 : p0 < p1) (h12 : p1 < p2)
    (h03 : p0 ≠ p3) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + 4 ≤ C.size ∧ ∀ x : Fin n → Bool,
      D.eval (List.ofFn x) = C.eval (List.ofFn (Fin.insertNth i false x)) := by
  exact compile_four_after_and_not n C (statAt n i false)
    (fun x : Fin n → Bool => List.ofFn (Fin.insertNth i false x)) List.ofFn
    (fun _ => by simp) hok (inv_at n i false) hnc i l p0 p1 p2 p3 g2 g3
    (by simpa only [statAt_length] using i.isLt) (statAt_at n i false)
    hseed (by simpa only [statAt_length] using hnot) hr2
    (by simpa only [statAt_length] using hin2) hr3 hin3 h01 h12 h03 h13 h23

end PEqualNP.Outside.L_meta_1890_aux.Propagation

namespace PEqualNP.Outside.L_meta_1890_aux.DirectSeedNot

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1890_aux.Propagation
open PEqualNP.Outside.L_meta_1890_aux.EffectiveReaders
open PEqualNP.Outside.L_meta_1890_aux.EffectiveReaderIndexed

def prependSeed (C : Circuit) : Circuit :=
  ⟨⟨GateOp.and,[0,2]⟩ :: C.gates,C.output⟩

lemma prependSeed_eval (C : Circuit) (x : Fin 10 → Bool) :
    (prependSeed C).eval (List.ofFn x) = C.eval (seed x) := by
  change C.eval (List.ofFn x ++ [GateOp.and.eval ([0,2].map
    (fun k => (List.ofFn x).getD k false))]) = _
  have h0 : (List.ofFn x).getD 0 false = x 0 := read_ofFn x 0
  have h2 : (List.ofFn x).getD 2 false = x 2 := read_ofFn x 2
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id,
    h0,h2,Bool.and_true]
  rfl

lemma effectiveInputs_subset (g : Gate) (a : ℕ) (h : a ∈ effectiveInputs g) :
    a ∈ g.inputs := by
  cases hop : g.op <;> simp only [effectiveInputs,hop] at h
  all_goals try exact h
  exact List.mem_of_mem_take h

lemma direct_not_seed_saves_three (C : Circuit)
    (hok : ∀ g ∈ C.gates, NOk g)
    (hC : ∀ x, C.eval (seed x) = petersen x)
    (pN pH : ℕ) (H : Gate)
    (hN : C.gates[pN]? = some ⟨GateOp.not,[10]⟩)
    (hH : C.gates[pH]? = some H) (hNH : pN < pH)
    (hread : 11+pN ∈ effectiveInputs H) :
    ∃ i : Fin 10, (i=0 ∨ i=2) ∧ ∃ D : Circuit,
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size+3 ≤ C.size ∧
      ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x) = petersen (Fin.insertNth i false x) := by
  have hHmem : H ∈ C.gates := List.mem_iff_getElem?.mpr ⟨pH,hH⟩
  obtain ⟨i,hi,p,G,hG,hreadG,hpN,hpH⟩ :=
    indexed_endpoint_reader C hC pN pH H (hok H hHmem).1.2 hN hH hread
  let A := prependSeed C
  have hA : ∀ g ∈ A.gates, NOk g := by
    intro g hg
    change g ∈ ⟨GateOp.and,[0,2]⟩ :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [NOk,Ok]
    · exact hok g hg
  have correct (x : Fin 10 → Bool) : A.eval (List.ofFn x) = petersen x :=
    (prependSeed_eval C x).trans (hC x)
  have hnc : ∃ x y : Fin 9 → Bool,
      A.eval (List.ofFn (Fin.insertNth i false x)) ≠
        A.eval (List.ofFn (Fin.insertNth i false y)) := by
    refine ⟨fun _ => false, fun j => decide (j=2 ∨ j=3), ?_⟩
    rw [correct,correct]
    rcases hi with rfl | rfl <;> decide
  have hseed : A.gates[0]? = some ⟨GateOp.and,[i.val,if i=0 then 2 else 0]⟩ ∨
      A.gates[0]? = some ⟨GateOp.and,[if i=0 then 2 else 0,i.val]⟩ := by
    rcases hi with rfl | rfl <;> simp [A,prependSeed]
  obtain ⟨D,hD,hs,hval⟩ := four_after_and_not_restrict 9 A hA i hnc
    (if i=0 then 2 else 0) 0 (pN+1) (pH+1) (p+1) H G hseed
    (by simpa [A,prependSeed] using hN)
    (by simpa [A,prependSeed] using hH)
    (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using effectiveInputs_subset H _ hread)
    (by simpa [A,prependSeed] using hG)
    (effectiveInputs_subset G _ hreadG)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨i,hi,D,hD,?_,?_⟩
  · have ha : A.size = C.size+1 := by simp [A,prependSeed,Circuit.size]
    omega
  · intro x
    exact (hval x).trans (correct (Fin.insertNth i false x))


lemma direct_not_seed_saves_three_fanin (C : Circuit)
    (hok : PEqualNP.MetaComplexity.FanInTwo C)
    (hC : ∀ x, C.eval (seed x) = petersen x)
    (pN pH : ℕ) (H : Gate)
    (hN : C.gates[pN]? = some ⟨GateOp.not,[10]⟩)
    (hH : C.gates[pH]? = some H) (hNH : pN < pH)
    (hread : 11+pN ∈ effectiveInputs H) :
    ∃ i : Fin 10, (i=0 ∨ i=2) ∧ ∃ D : Circuit,
      PEqualNP.MetaComplexity.FanInTwo D ∧ D.size+3 ≤ C.size ∧
      ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x) = petersen (Fin.insertNth i false x) := by
  let E : Circuit := ⟨C.gates.map normGate,C.output⟩
  have hE : ∀ g ∈ E.gates, NOk g := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hok g0 hg0)
  have ecorrect (x : Fin 10 → Bool) : E.eval (seed x) = petersen x := by
    change (wiresFrom (C.gates.map normGate) (seed x)).getD C.output false = _
    rw [wiresFrom_norm]
    exact hC x
  have hn : E.gates[pN]? = some ⟨GateOp.not,[10]⟩ := by
    simp [E,List.getElem?_map,hN,normGate]
  have hh : E.gates[pH]? = some (normGate H) := by
    simp [E,List.getElem?_map,hH]
  have heff : effectiveInputs (normGate H) = effectiveInputs H := by
    cases hop : H.op <;> simp [effectiveInputs,normGate,hop,List.take_take]
  obtain ⟨i,hi,D,hD,hs,hval⟩ := direct_not_seed_saves_three E hE ecorrect
    pN pH (normGate H) hn hh hNH (by simpa only [heff] using hread)
  refine ⟨i,hi,D,hD,?_,hval⟩
  simpa [E,Circuit.size] using hs

end PEqualNP.Outside.L_meta_1890_aux.DirectSeedNot
