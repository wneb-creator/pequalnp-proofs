import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def adjacent (i j : Fin 10) : Bool :=
  (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
lemma pivotalWitness : ∀ (i j k : Fin 10) (a b : Bool),
    i ≠ j → i ≠ k → j ≠ k → ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ l : Fin 10, ∀ z : Bool,
      edgeFunction (fun t => if t = i then z else if t = j then a else
        if t = k then b else decide (t = l)) = z := by
  decide +kernel

lemma pivotal (i j k : Fin 10) (a b : Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (pins : ¬ (a = true ∧ b = true ∧ adjacent j k = true)) :
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧
      ∀ z : Bool, edgeFunction (Function.update x i z) = z := by
  obtain ⟨l, hl⟩ := pivotalWitness i j k a b hij hik hjk pins
  let x : Fin 10 → Bool := fun t => if t = i then false else if t = j then a else
    if t = k then b else decide (t = l)
  refine ⟨x, by simp [x, Ne.symm hij], by simp [x, Ne.symm hik, Ne.symm hjk], ?_⟩
  intro z
  have update_eq : Function.update x i z =
      (fun t => if t = i then z else if t = j then a else
        if t = k then b else decide (t = l)) := by
    funext t
    by_cases h : t = i
    · subst t
      simp
    · simp [Function.update_of_ne h, x, h]
  rw [update_eq]
  exact hl z

namespace Relabel

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (m N : ℕ) (σ : Fin m → Fin N) (k : ℕ) : ℕ :=
  if h : k < m then (σ ⟨k, h⟩).val else N + (k - m)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma getD_rho {m N : ℕ} (W y T : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (k : ℕ) : (W ++ T).getD (rho m N σ k) false = (y ++ T).getD k false := by
  unfold rho
  split_ifs with h
  · have := (σ ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hyv k h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_rel {m N : ℕ} (W y : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (reGate (rho m N σ))).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map (rho m N σ)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_rho W y T σ hW hy hyv i)
    have e1 : stepW (W ++ T) (reGate (rho m N σ) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (rho m N σ)).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end Relabel

namespace Relabel

open PEqualNP.CircuitLowerBounds

def sig (n : ℕ) (σ : Fin n → Fin n) (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : k.val < n then ⟨(σ ⟨k.val, h⟩).val, by omega⟩ else k

lemma hyv_lem (n : ℕ) (σ : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    ∀ k (h : k < n + 1), (List.ofFn (x ∘ σ) ++ [b]).getD k false
      = (List.ofFn x ++ [b]).getD (sig n σ ⟨k, h⟩) false := by
  intro k h
  unfold sig
  by_cases hk : k < n
  · have := (σ ⟨k, hk⟩).isLt
    simp only [hk, dite_true]
    rw [List.getD_append _ _ _ _ (by simp [hk]), List.getD_append _ _ _ _ (by simpa using this)]
    simp [List.getD_eq_getElem?_getD, hk, this]
  · simp only [hk, dite_false]
    have hk' : k = n := by omega
    subst hk'
    rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp

end Relabel


open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1884.Relabel in
lemma relabel : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro n σ C hC
  refine ⟨⟨C.gates.map (reGate (rho (n + 1) (n + 1) (sig n σ))), rho (n + 1) (n + 1) (sig n σ) C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro x b
    have hW : (List.ofFn x ++ [b]).length = n + 1 := by simp
    have hy : (List.ofFn (x ∘ σ) ++ [b]).length = n + 1 := by simp
    obtain ⟨R, h1, h2⟩ := fold_rel _ _ (sig n σ) hW hy (hyv_lem n σ x b) C.gates []
    simp only [List.append_nil] at h1 h2
    show (List.foldl stepW _ _).getD _ false = (List.foldl stepW _ _).getD _ false
    rw [h1, h2, getD_rho _ _ R (sig n σ) hW hy (hyv_lem n σ x b)]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Unary

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)


private def touches (k : ℕ) (g : Gate) : Bool :=
  g.inputs.any (fun i => decide (i = k))

private def effectiveTouches (k : ℕ) (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
    (fun i => decide (i = k))

private lemma touches_norm (k : ℕ) (g : Gate) (hg : OkGate g) :
    touches k (normGate g) = effectiveTouches k g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp_all [touches, effectiveTouches, normGate, GateOp.eval, OkGate]

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma count_norm (k : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, OkGate g) :
    (gs.map normGate).countP (touches k) = gs.countP (effectiveTouches k) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.countP_cons, touches_norm k g (h g List.mem_cons_self),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

private lemma elimPass_count (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ gs, NOkGate g)
    (hk : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (ha : k < acc.1.length) :
    (elimPass m gs acc).2.length + gs.countP (touches k) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    have hk' : (elimStep m acc g).1.getD k (Sum.inl false) = Sum.inl false := by
      unfold elimStep
      rw [getD_snoc_lt _ _ _ _ ha, hk]
    have ha' : k < (elimStep m acc g).1.length := by simp [elimStep]; omega
    have ht := ih (elimStep m acc g) (fun a hm => h a (List.mem_cons_of_mem _ hm)) hk' ha'
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    let part := simplifyGate g.op (m + acc.2.length) ins
    have hb : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ part.1.toList).length ≤ _
      rw [List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    rw [elimPass_cons, List.countP_cons, List.length_cons]
    cases he : touches k g with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      have hn : part.1 = none := by
        have hg := h g List.mem_cons_self
        apply simplifyGate_none_of_const _ _ _ hg.1.1
        · simpa [ins] using hg.1.2
        · intro hn
          simpa [ins] using hg.2 hn
        · obtain ⟨i, hi, hb⟩ := List.any_eq_true.mp he
          have hi' : i = k := by simpa using hb
          rw [hi'] at hi
          exact ⟨false, List.mem_map.mpr ⟨k, hi, hk⟩⟩
      have hd : (elimStep m acc g).2.length = acc.2.length := by
        change (acc.2 ++ part.1.toList).length = _
        simp [hn]
      simp only [↓reduceIte]
      omega

private def hmap (h : Bool → Bool) (i n : ℕ) : Bool ⊕ ℕ :=
  match h false, h true with
  | false, true => Sum.inr i
  | true, false => Sum.inr n
  | b, _ => Sum.inl b

private lemma hmap_spec (h : Bool → Bool) (n : ℕ) (i : Fin n) (x : Fin n → Bool) :
    statValid (n + 1) (hmap h i.val n) ∧
      statVal (List.ofFn x ++ [!x i]) (hmap h i.val n) = h (x i) := by
  have hi : i.val < (List.ofFn x).length := by simp
  have hxi : (List.ofFn x ++ [!x i]).getD i.val false = x i := by
    rw [getD_snoc_lt _ _ _ _ hi]
    simp [List.getD]
  have hxn : (List.ofFn x ++ [!x i]).getD n false = !x i := getD_snoc_eq _ _ _ _ (by simp)
  unfold hmap
  cases h0 : h false <;> cases h1 : h true <;>
    simp only [statValid, statVal, hxi, hxn] <;> cases hx : x i <;> simp_all

private def initMap2 (h : Bool → Bool) (n : ℕ) (i : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun k : Fin n => (Sum.inr k.val : Bool ⊕ ℕ)) ++ [hmap h i.val n]

private lemma initMap2_lt (h : Bool → Bool) (n : ℕ) (i : Fin n) (j : ℕ) (hj : j < n) :
    (initMap2 h n i).getD j (Sum.inl false) = Sum.inr j := by
  unfold initMap2
  rw [getD_snoc_lt _ _ _ _ (by simpa using hj)]
  simp [List.getD, hj]

private lemma first_inv2 (h : Bool → Bool) (n : ℕ) (i : Fin n) (x : Fin n → Bool) :
    ElimInv (n + 1) (List.ofFn x ++ [!x i]) (List.ofFn x ++ [h (x i)]) (initMap2 h n i, []) := by
  refine ⟨by simp, by simp [initMap2], ?_⟩
  intro j
  rcases lt_trichotomy j n with hj | hj | hj
  · show statValid (n + 1 + 0) ((initMap2 h n i).getD j (Sum.inl false)) ∧
      statVal (List.ofFn x ++ [!x i]) ((initMap2 h n i).getD j (Sum.inl false)) =
        (List.ofFn x ++ [h (x i)]).getD j false
    rw [initMap2_lt h n i j hj, getD_snoc_lt _ _ _ _ (by simpa using hj)]
    refine ⟨by simp [statValid]; omega, ?_⟩
    show (List.ofFn x ++ [!x i]).getD j false = (List.ofFn x).getD j false
    exact getD_snoc_lt _ _ _ _ (by simpa using hj)
  · subst hj
    have h1 : (initMap2 h j i).getD j (Sum.inl false) = hmap h i.val j := by
      unfold initMap2
      exact getD_snoc_eq _ _ _ _ (by simp)
    show statValid (j + 1 + 0) ((initMap2 h j i).getD j (Sum.inl false)) ∧
      statVal (List.ofFn x ++ [!x i]) ((initMap2 h j i).getD j (Sum.inl false)) =
        (List.ofFn x ++ [h (x i)]).getD j false
    rw [h1, getD_snoc_eq _ _ _ _ (by simp)]
    exact hmap_spec h j i x
  · rw [List.getD_eq_default _ _ (by simp [initMap2]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      unfold elimStep
      simp only [List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    simp only [List.length_cons]
    omega

private lemma initMap2_ne_true (h : Bool → Bool) (n : ℕ) (i : Fin n) (o : ℕ) (ho : o ≠ n) :
    (initMap2 h n i).getD o (Sum.inl false) ≠ Sum.inl true := by
  rcases lt_or_gt_of_ne ho with hlt | hgt
  · rw [initMap2_lt h n i o hlt]
    simp
  · rw [List.getD_eq_default _ _ (by simp [initMap2]; omega)]
    simp

private lemma main (n : ℕ) (i : Fin n) (h : Bool → Bool) (C : Circuit) (hfan : FanInTwo C)
    (hout : C.output ≠ n) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [!x i]) = C.eval (List.ofFn x ++ [h (x i)]) := by
  let gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok a (hfan a ha)
  let acc := elimPass (n + 1) gs (initMap2 h n i, [])
  have hs : acc.2.length ≤ C.size := by
    have ht := elimPass_len (n + 1) gs (initMap2 h n i, [])
    have hl : gs.length = C.size := List.length_map _
    simp only [List.length_nil] at ht
    show (elimPass (n + 1) gs (initMap2 h n i, [])).2.length ≤ C.size
    omega
  have hv (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x ++ [!x i])) (acc.1.getD C.output (Sum.inl false)) =
        C.eval (List.ofFn x ++ [h (x i)]) := by
    have hr := ((elimInv_pass (n + 1) (List.ofFn x ++ [!x i]) gs (List.ofFn x ++ [h (x i)])
      (initMap2 h n i, []) (fun g hg => (hnok g hg).1) (first_inv2 h n i x)).2.2 C.output).2
    show _ = (wiresFrom C.gates (List.ofFn x ++ [h (x i)])).getD C.output false
    exact hr.trans (congrArg (fun w => w.getD C.output false)
      (wiresFrom_norm C.gates (List.ofFn x ++ [h (x i)])))
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      refine ⟨⟨[], n + 1⟩, by simp [FanInTwo], by change 0 ≤ C.size; omega, ?_⟩
      intro x
      have hx := hv x
      rw [ho] at hx
      rw [← hx]
      change (List.ofFn x ++ [!x i]).getD (n + 1) false = false
      exact List.getD_eq_default _ _ (by simp)
    | true =>
      by_cases hc : C.size = 0
      · exfalso
        have hg : C.gates = [] := List.eq_nil_of_length_eq_zero hc
        have hacc : acc = (initMap2 h n i, []) := by
          show elimPass (n + 1) (C.gates.map normGate) (initMap2 h n i, []) = _
          rw [hg]
          rfl
        rw [hacc] at ho
        exact initMap2_ne_true h n i C.output hout ho
      · refine ⟨⟨[⟨GateOp.not, []⟩], n + 1⟩, ?_, by change 1 ≤ C.size; omega, ?_⟩
        · intro g hg
          simp only [List.mem_singleton] at hg
          subst hg
          simp
        · intro x
          have hx := hv x
          rw [ho] at hx
          rw [← hx]
          change (List.ofFn x ++ [!x i] ++ [GateOp.not.eval []]).getD (n + 1) false = true
          rw [getD_snoc_eq _ _ _ _ (by simp)]
          rfl
  | inr j =>
    refine ⟨⟨acc.2, j⟩, elimPass_ok (n + 1) gs _ (by simp), by simpa [Circuit.size] using hs, ?_⟩
    intro x
    have hx := hv x
    rw [ho] at hx
    exact hx

end Unary


lemma normalize : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : Bool → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.output ≠ x1 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ x4.size ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8 ++ [!x8 x2]) = x4.eval (List.ofFn x8 ++ [x3 (x8 x2)]) := by
  intro n i h C hfan hout
  exact PEqualNP.Outside.L_meta_1884.Unary.main n i h C hfan hout



lemma canonical_reduction
    (lower : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 → ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ f model budget
  let target := (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)))
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) ≠ target x
  by_contra noWitness
  obtain ⟨D, modelD, sizeD, evalD⟩ := relabel 10 σ C model
  have computes (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = target x := by
    rw [evalD]
    by_contra different
    exact noWitness ⟨x, different⟩
  by_cases direct : D.output = 10
  · have reads (gs : List Gate) (w : List Bool) (h : 10 < w.length) :
        (Circuit.mk gs 10).eval w = w.getD 10 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        let next := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        change (Circuit.mk gs 10).eval next = w.getD 10 false
        rw [ih next (by simp [next]; omega)]
        exact List.getD_append _ _ _ _ h
    have wire (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = f (x 0) := by
      change (Circuit.mk D.gates D.output).eval _ = _
      rw [direct, reads D.gates _ (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    let zero : Fin 10 → Bool := fun _ => false
    let edge : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have noEdge : target zero = false := by decide
    have hasEdge : target edge = true := by decide
    have b₀ := (wire zero).symm.trans (computes zero)
    have b₁ := (wire edge).symm.trans (computes edge)
    rw [noEdge] at b₀
    rw [hasEdge] at b₁
    change f false = false at b₀
    change f false = true at b₁
    exact Bool.false_ne_true (b₀.symm.trans b₁)
  · obtain ⟨E, modelE, sizeE, evalE⟩ := normalize 10 0 f D modelD direct
    obtain ⟨x, different⟩ := lower E modelE (sizeE.trans (sizeD ▸ budget))
    exact different ((evalE x).trans (computes x))

lemma move_or_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = true → continuation (a || b) = true) :
    continuation (a || b) = (continuation a || b) := by
  cases hb : b with
  | false => simp
  | true => simpa [hb] using certified hb

lemma move_and_to_output (a b : Bool) (continuation : Bool → Bool)
    (certified : b = false → continuation (a && b) = false) :
    continuation (a && b) = (continuation a && b) := by
  cases hb : b with
  | false => simpa [hb] using certified hb
  | true => simp

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ![1, 2, 3, 4, 0, 7, 8, 9, 5, 6] i

def singletonInput (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = neighbor i)

def edgeInput (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = i ∨ j = neighbor i)

lemma singleton_target (i : Fin 10) : target (singletonInput i) = false := by
  fin_cases i <;> decide

lemma edge_target (i : Fin 10) : target (edgeInput i) = true := by
  fin_cases i <;> decide

lemma inputs_agree (i j : Fin 10) (h : j ≠ i) :
    singletonInput i j = edgeInput i j := by
  simp [singletonInput, edgeInput, h]

lemma omitted_vertex
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (omitted : ∀ j, σ j ≠ i)
    (sameFree : u (singletonInput i 0) = u (edgeInput i 0)) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  have same :
      List.ofFn (singletonInput i ∘ σ) ++ [u (singletonInput i 0)] =
      List.ofFn (edgeInput i ∘ σ) ++ [u (edgeInput i 0)] := by
    have hfirst : singletonInput i ∘ σ = edgeInput i ∘ σ := by
      funext j
      exact inputs_agree i (σ j) (omitted j)
    rw [hfirst, sameFree]
  by_cases h : C.eval (List.ofFn (singletonInput i ∘ σ) ++
      [u (singletonInput i 0)]) = false
  · refine ⟨edgeInput i, ?_⟩
    rw [edge_target, ← same, h]
    decide
  · refine ⟨singletonInput i, ?_⟩
    rwa [singleton_target]

lemma omitted_nonzero_vertex
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (hi : i ≠ 0)
    (omitted : ∀ j, σ j ≠ i) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  apply omitted_vertex C σ u i omitted
  rw [inputs_agree i 0 (Ne.symm hi)]

lemma omitted_vertex_constant_free
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (constant : u false = u true)
    (omitted : ∀ j, σ j ≠ i) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  apply omitted_vertex C σ u i omitted
  have same (a b : Bool) : u a = u b := by
    cases a <;> cases b <;> simp [constant]
  exact same _ _

lemma necessary_vertex_coverage
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    ∀ i : Fin 10, i ≠ 0 → ∃ j, σ j = i := by
  intro i hi
  by_contra omitted
  push Not at omitted
  obtain ⟨x, different⟩ := omitted_nonzero_vertex C σ u i hi omitted
  exact different (computes x)

lemma necessary_coverage_or_nonconstant
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    Function.Surjective σ ∨ u false ≠ u true := by
  by_cases constant : u false = u true
  · left
    intro i
    by_contra omitted
    push Not at omitted
    obtain ⟨x, different⟩ := omitted_vertex_constant_free C σ u i constant omitted
    exact different (computes x)
  · exact Or.inr constant

lemma free_nonconstant_of_omitted_zero
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (omitted : ∀ j, σ j ≠ 0)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    u false ≠ u true := by
  intro constant
  obtain ⟨x, different⟩ := omitted_vertex_constant_free C σ u 0 constant omitted
  exact different (computes x)

lemma unary_nonconstant_cases (u : Bool → Bool) (h : u false ≠ u true) :
    u = id ∨ u = Bool.not := by
  cases hf : u false <;> cases ht : u true
  · exact False.elim (h (hf.trans ht.symm))
  · left
    funext b
    cases b <;> simp [hf, ht]
  · right
    funext b
    cases b <;> simp [hf, ht]
  · exact False.elim (h (hf.trans ht.symm))

lemma target_separation (q : Fin 10) :
    ∃ x y : Fin 10 → Bool, x q = y q ∧ x 0 = y 0 ∧ target x ≠ target y := by
  have choice : ∃ i : Fin 10, i ≠ q ∧ i ≠ 0 := by
    by_cases hq : q = 1
    · exact ⟨2, by omega, by decide⟩
    · exact ⟨1, Ne.symm hq, by decide⟩
  obtain ⟨i, hiq, hi0⟩ := choice
  refine ⟨singletonInput i, edgeInput i,
    inputs_agree i q (Ne.symm hiq), inputs_agree i 0 (Ne.symm hi0), ?_⟩
  rw [singleton_target, edge_target]
  decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def capGate (bound : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i bound)⟩

def capCircuit (bound : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate bound), min C.output bound⟩

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

lemma getD_cap (w : List Bool) (bound i : Nat) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega : bound ≤ i)]
    rw [List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega : w.length ≤ i)]

lemma gateStep_cap (w : List Bool) (bound : Nat) (g : Gate)
    (h : w.length ≤ bound) : gateStep w (capGate bound g) = gateStep w g := by
  change w ++ [g.op.eval ((g.inputs.map (fun i => min i bound)).map
    (fun i => w.getD i false))] = w ++ [g.op.eval (g.inputs.map
    (fun i => w.getD i false))]
  rw [List.map_map]
  have hm : g.inputs.map ((fun i => w.getD i false) ∘ (fun i => min i bound)) =
      g.inputs.map (fun i => w.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact getD_cap w bound i h
  rw [hm]

lemma fold_cap (gs : List Gate) (w : List Bool) (bound : Nat)
    (h : w.length + gs.length ≤ bound) :
    (gs.map (capGate bound)).foldl gateStep w = gs.foldl gateStep w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      gateStep_cap w bound g (by simp only [List.length_cons] at h; omega)]
    apply ih
    simp only [gateStep, List.length_append, List.length_singleton]
    simp only [List.length_cons] at h
    omega

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [gateStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma capCircuit_eval (C : Circuit) (w : List Bool) (bound : Nat)
    (h : w.length + C.size ≤ bound) : (capCircuit bound C).eval w = C.eval w := by
  change ((C.gates.map (capGate bound)).foldl gateStep w).getD
    (min C.output bound) false = (C.gates.foldl gateStep w).getD C.output false
  rw [fold_cap C.gates w bound h]
  exact getD_cap _ bound C.output (by rw [fold_length]; exact h)

lemma capCircuit_size (C : Circuit) (bound : Nat) :
    (capCircuit bound C).size = C.size := by
  simp only [capCircuit, Circuit.size, List.length_map]

lemma capCircuit_fan (C : Circuit) (bound : Nat) (h : FanInTwo C) :
    FanInTwo (capCircuit bound C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  have hx := h a ha
  exact ⟨hx.1, by simpa only [capGate, List.length_map] using hx.2⟩

lemma capCircuit_inputs (C : Circuit) (bound : Nat) :
    ∀ g ∈ (capCircuit bound C).gates, ∀ i ∈ g.inputs, i ≤ bound := by
  intro g hg i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right j bound

lemma bounded_sources (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 18) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 29 ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 29) ∧
      ∀ w : List Bool, w.length = 11 → D.eval w = C.eval w := by
  refine ⟨capCircuit 29 C, capCircuit_fan C 29 hfan, capCircuit_size C 29,
    Nat.min_le_right _ _, capCircuit_inputs C 29, ?_⟩
  intro w hw
  exact capCircuit_eval C w 29 (by rw [hw]; omega)

lemma fold_getD_input (gs : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length) : (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (gateStep w g) (by simp only [gateStep,
      List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma eval_input (C : Circuit) (w : List Bool) (hi : C.output < w.length) :
    C.eval w = w.getD C.output false := by
  exact fold_getD_input C.gates w C.output hi

lemma output_internal (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (f : (Fin 10 → Bool) → Bool)
    (separates : ∀ q : Fin 10, ∃ x y : Fin 10 → Bool,
      x q = y q ∧ x 0 = y 0 ∧ f x ≠ f y)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = f x) :
    11 ≤ C.output ∧ C.output < 11 + C.size := by
  constructor
  · by_contra low
    have lower : C.output < 11 := by omega
    by_cases ten : C.output < 10
    · obtain ⟨x, y, same, _, different⟩ := separates (σ ⟨C.output, ten⟩)
      apply different
      rw [← computes x, ← computes y,
        eval_input C _ (by simpa using lower),
        eval_input C _ (by simpa using lower)]
      rw [List.getD_append _ _ _ _ (by simpa using ten),
        List.getD_append _ _ _ _ (by simpa using ten),
        List.getD_eq_getElem _ _ (by simpa using ten),
        List.getD_eq_getElem _ _ (by simpa using ten)]
      simpa only [List.getElem_ofFn, Function.comp_apply] using same
    · have eqten : C.output = 10 := by omega
      obtain ⟨x, y, _, same, different⟩ := separates 0
      apply different
      rw [← computes x, ← computes y,
        eval_input C _ (by simpa using lower),
        eval_input C _ (by simpa using lower), eqten]
      exact congrArg u same
  · by_contra high
    have high' : 11 + C.size ≤ C.output := by omega
    have always_false (x : Fin 10 → Bool) : f x = false := by
      rw [← computes x]
      change (C.gates.foldl gateStep _).getD C.output false = false
      apply List.getD_eq_default
      rw [fold_length]
      simpa only [List.length_append, List.length_ofFn, List.length_singleton,
        Circuit.size] using high'
    obtain ⟨x, y, _, _, different⟩ := separates 0
    exact different ((always_false x).trans (always_false y).symm)

end PEqualNP.Outside.L_meta_1884
