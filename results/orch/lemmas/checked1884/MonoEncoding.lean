import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.NormalizedEncoding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

noncomputable section Encoding

open Classical

-- Wires

-- Run gates on a wire list: the fold inside `Circuit.wires`.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

-- The abstract model

-- Operation, first source, second source of each gate, output source, gate values.
def Model : Type := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)

def Model.mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) : Model := (op, s1, s2, so, w)

def Model.op (M : Model) : ℕ → ℕ := Prod.fst M
def Model.s1 (M : Model) : ℕ → ℕ := Prod.fst (Prod.snd M)
def Model.s2 (M : Model) : ℕ → ℕ := Prod.fst (Prod.snd (Prod.snd M))
def Model.so (M : Model) : ℕ := Prod.fst (Prod.snd (Prod.snd (Prod.snd M)))
def Model.w (M : Model) : ℕ → ℕ → Bool := Prod.snd (Prod.snd (Prod.snd (Prod.snd M)))

theorem Model.op_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) : (Model.mk a b c d e).op = a := rfl
theorem Model.s1_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) : (Model.mk a b c d e).s1 = b := rfl
theorem Model.s2_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) : (Model.mk a b c d e).s2 = c := rfl
theorem Model.so_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) : (Model.mk a b c d e).so = d := rfl
theorem Model.w_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) : (Model.mk a b c d e).w = e := rfl

-- The value of source `k` for gate `j` on row `r`.
def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

-- The gate operations.
def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

-- A model with `s` gates computing `g` on the rows satisfying `R`.
def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 3) ∧ (∀ j < s, M.s1 j ≤ n + j) ∧ (∀ j < s, M.s2 j ≤ n + j) ∧
  M.so ≤ n + s ∧
  (∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)) ∧
  (∀ r, R r → M.sv n s M.so r = g r)

section validf
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
theorem Valid.op_lt (h : Valid n s g R M) : ∀ j < s, M.op j < 3 := h.1
theorem Valid.s1_le (h : Valid n s g R M) : ∀ j < s, M.s1 j ≤ n + j := h.2.1
theorem Valid.s2_le (h : Valid n s g R M) : ∀ j < s, M.s2 j ≤ n + j := h.2.2.1
theorem Valid.so_le (h : Valid n s g R M) : M.so ≤ n + s := h.2.2.2.1
theorem Valid.w_eq (h : Valid n s g R M) :
    ∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r) :=
  h.2.2.2.2.1
theorem Valid.out_eq (h : Valid n s g R M) : ∀ r, R r → M.sv n s M.so r = g r := h.2.2.2.2.2
theorem Valid.intro (a : ∀ j < s, M.op j < 3) (b : ∀ j < s, M.s1 j ≤ n + j)
    (c : ∀ j < s, M.s2 j ≤ n + j) (d : M.so ≤ n + s)
    (e : ∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r))
    (f : ∀ r, R r → M.sv n s M.so r = g r) : Valid n s g R M := ⟨a, b, c, d, e, f⟩
end validf

-- Gate `j` is padding: `TRUE` reading `F` twice.
def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

-- Gate `j` is below gate `j + 1` in the order of the triples (first source, second source,
-- operation).
def LexLt (M : Model) (j : ℕ) : Prop :=
  M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ M.s2 j < M.s2 (j + 1)) ∨
    (M.s1 j = M.s1 (j + 1) ∧ M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)

-- The normal form.
def NF (n s : ℕ) (M : Model) : Prop :=
  (∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j) ∧
  (∀ j < s, M.op j = 2 → M.pad n j) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j) ∧
  (∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j) ∧
  (∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)) ∧
  (0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)) ∧
  (∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j → LexLt M j)

section nff
variable {n s : ℕ} {M : Model}
theorem NF.pre (h : NF n s M) : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := h.1
theorem NF.padOp (h : NF n s M) : ∀ j < s, M.op j = 2 → M.pad n j := h.2.1
theorem NF.noF (h : NF n s M) : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := h.2.2.1
theorem NF.noPadRd (h : NF n s M) :
    ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := h.2.2.2.1
theorem NF.ord (h : NF n s M) : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := h.2.2.2.2.1
theorem NF.used (h : NF n s M) :
    ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j) :=
  h.2.2.2.2.2.1
theorem NF.out (h : NF n s M) : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1) := h.2.2.2.2.2.2.1
theorem NF.lex (h : NF n s M) :
    ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j → LexLt M j :=
  h.2.2.2.2.2.2.2
end nff

-- The valuation of a model

-- What variable `(kd, j, a)` says of a model.
def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

-- The valuation of a model (checker variable `v + 1` is variable `v`).
def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

-- Source `e` (1 or 2) of gate `j`.
def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha


-- Clauses of `enc` hold in a valid model in normal form

theorem cs_append (a : ℕ → Bool) (c d : List ℕ) :
    ClauseSat a (c ++ d) ↔ ClauseSat a c ∨ ClauseSat a d := by
  constructor
  · rintro ⟨l, hl, hv⟩
    rcases List.mem_append.1 hl with h | h
    · exact Or.inl ⟨l, h, hv⟩
    · exact Or.inr ⟨l, h, hv⟩
  · rintro (⟨l, hl, hv⟩ | ⟨l, hl, hv⟩)
    · exact ⟨l, List.mem_append_left _ hl, hv⟩
    · exact ⟨l, List.mem_append_right _ hl, hv⟩

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in
-- A valid model in normal form satisfies every clause of `enc`.
theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

theorem s_fLex : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j → 
      ClauseSat (val n s M) (lexBase n s j) := by
    intro h
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2,
      or_false, beq_iff_eq, decide_eq_true_eq]
    exact h
  by_cases hE : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · have hb := hesc hE
    rcases hc with ⟨b, hb', rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact (cs_append _ _ _).2 (Or.inr hb)
  · have hj1 : j + 1 < s := by clear * - hj; omega
    have hL := hn.lex j hj1 (fun h => hE (Or.inl h)) (fun h => hE (Or.inr (Or.inl h)))
      (fun h => hE (Or.inr (Or.inr h)))
    unfold LexLt at hL
    rcases hc with ⟨b, hb', rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      refine (cs_append _ _ _).2 (Or.inl ?_) <;>
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_op, or_false,
        Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] <;>
      by_contra hh <;> push_neg at hh <;> omega

include hrows in
theorem enc2_sat : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn c h

end sound

-- From a circuit to a model

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The input of row `r`.
def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

-- A wire index read by gate `j`: an index that does not exist yet becomes `F`.
def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

-- Operation and sources of gate `g` at position `j`: `AND []` becomes padding `(TRUE, F, F)`,
-- `OR []` becomes `OR F F`, a single input is read twice.
def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

-- Gate `j` of `C`, or `AND []` past the end.
def gAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

-- The model of a circuit: gates past the end are padding.
def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  Model.mk (fun j => (code n (gAt C j) j).1) (fun j => (code n (gAt C j) j).2.1)
    (fun j => (code n (gAt C j) j).2.2)
    (if C.output < n + C.gates.length then C.output else n + s)
    (fun j r => if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true)

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

-- The wire of gate `j` is its operation on the wires before it.
theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gAt C j).op.eval ((gAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gAt C j :: C.gates.drop (j + 1)) := by
    rw [gAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gAt C j).op.eval ((gAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · intro j _; exact (code_le n _ j).1
  · intro j _; exact (code_le n _ j).2.1
  · intro j _; exact (code_le n _ j).2.2
  · exact by simp only [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs <;> omega
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gAt C j ∈ C.gates := by
        rw [gAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gAt C j = ⟨.and, []⟩ := by
        rw [gAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, hjl, hga, code, gfun]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

-- Moving a gate to the front

-- New index of an old wire other than `n + d` when gate `d` moves to the front.
def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

-- A redirected source of a reader at old position `j > d` (`j = s`: the output). Target
-- `t = 0`: `F`; `t = 1`: the new padding wire `n`; `t = c + 2`: old source `c`.
def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

-- The value of target `t`.
def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

-- Gate `d` moved to the front as padding, its readers redirected to target `t`.
def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model :=
  Model.mk (fun j => if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j)
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j))
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j))
    (rd n d t s M.so)
    (fun j r => if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r)

-- Some later gate or the output reads gate `d`.
def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

-- A target is admissible for gate `d`.
def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · skip
    have := hv.so_le
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj r hr
    by_cases h0 : j = 0
    · subst h0; simp [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  · intro r hr
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

-- The measure

-- `1` for a gate that is not padding.
def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

-- Weighted count of the gates that are not padding: gate `j` weighs `s - j`.
def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j
theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl


-- The base of the source digits.
def bb (n s : ℕ) : ℕ := n + s + 1

-- The key of gate `j`: its triple (first source, second source, operation) as a number.
def key (n s : ℕ) (M : Model) (j : ℕ) : ℕ := (M.s1 j * bb n s + M.s2 j) * 3 + M.op j

-- The bound of the keys.
def KK (n s : ℕ) : ℕ := 3 * (bb n s * bb n s)

-- The digits `a 0, ..., a (m - 1)` in base `K`, most significant first.
def hor (K : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => hor K a m * K + a m

theorem hor_lt (K : ℕ) (a : ℕ → ℕ) : ∀ m, (∀ i < m, a i < K) → hor K a m < K ^ m := by
  intro m
  induction m with
  | zero => intro _; simp [hor]
  | succ m ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h m (by omega)
    show hor K a m * K + a m < K ^ (m + 1)
    calc hor K a m * K + a m < hor K a m * K + K := by omega
      _ = (hor K a m + 1) * K := by ring
      _ ≤ K ^ m * K := Nat.mul_le_mul_right K h1
      _ = K ^ (m + 1) := (pow_succ K m).symm

theorem hor_congr (K : ℕ) (a b : ℕ → ℕ) : ∀ m, (∀ i < m, a i = b i) → hor K a m = hor K b m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    show hor K a m * K + a m = hor K b m * K + b m
    rw [ih (fun i hi => h i (by omega)), h m (by omega)]

theorem hor_lex (K : ℕ) (a b : ℕ → ℕ) (j : ℕ) (heq : ∀ i < j, b i = a i) (hlt : b j < a j)
    (hK : ∀ i, b i < K) : ∀ m, j < m → hor K b m < hor K a m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro hm
    show hor K b m * K + b m < hor K a m * K + a m
    by_cases hjm : j = m
    · subst hjm
      rw [hor_congr K b a j heq]
      omega
    · have h1 := ih (by omega)
      have h2 := hK m
      calc hor K b m * K + b m < hor K b m * K + K := by omega
        _ = (hor K b m + 1) * K := by ring
        _ ≤ hor K a m * K := Nat.mul_le_mul_right K h1
        _ ≤ hor K a m * K + a m := by omega

-- The measure: first the weighted count of the gates that are not padding, then the keys of
-- the gates in order.
def meas (n s : ℕ) (M : Model) : ℕ := KK n s ^ s * muf s (ind n M) + hor (KK n s) (key n s M) s

theorem key_lt {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) : key n s M j < KK n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  unfold key KK
  have hb : M.s1 j + 1 ≤ bb n s := by unfold bb; omega
  have hb2 : M.s2 j < bb n s := by unfold bb; omega
  have := Nat.mul_le_mul_right (bb n s) hb
  rw [Nat.add_mul, Nat.one_mul] at this
  generalize M.s1 j * bb n s = p at *
  generalize bb n s * bb n s = q at *
  omega

-- The keys of a valid model, with `0` past the last gate.
def keyV (n s : ℕ) (M : Model) (j : ℕ) : ℕ := if j < s then key n s M j else 0

theorem hor_keyV (n s : ℕ) (M : Model) :
    hor (KK n s) (key n s M) s = hor (KK n s) (keyV n s M) s :=
  hor_congr _ _ _ s fun i hi => by simp [keyV, hi]

theorem keyV_lt {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (i : ℕ) : keyV n s M i < KK n s := by
  unfold keyV
  split_ifs with h
  · exact key_lt hv h
  · unfold KK bb; positivity

theorem hor_key_lt {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    hor (KK n s) (key n s M) s < KK n s ^ s := by
  rw [hor_keyV]
  exact hor_lt _ _ s fun i _ => keyV_lt hv i

-- The measure drops when the weighted count drops.
theorem meas_lt_of_muf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M M' : Model}
    (hv' : Valid n s g R M') (h : muf s (ind n M') < muf s (ind n M)) : meas n s M' < meas n s M := by
  have b := hor_key_lt hv'
  unfold meas
  have : KK n s ^ s * muf s (ind n M') + KK n s ^ s ≤ KK n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
  omega

-- The measure drops when the padding is the same and the keys drop in the order.
theorem meas_lt_of_key {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M M' : Model}
    (hv' : Valid n s g R M') (hind : ind n M' = ind n M) {j : ℕ} (hj : j < s)
    (heq : ∀ i < j, key n s M' i = key n s M i) (hlt : key n s M' j < key n s M j) :
    meas n s M' < meas n s M := by
  unfold meas
  rw [hind, hor_keyV n s M', hor_keyV n s M]
  have : hor (KK n s) (keyV n s M') s < hor (KK n s) (keyV n s M) s := by
    apply hor_lex _ _ _ j _ _ (keyV_lt hv') s hj
    · intro i hi; simp [keyV, show i < s by omega, heq i hi]
    · simp [keyV, hj, hlt]
  omega

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  apply meas_lt_of_muf hv'
  apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
  · simp [ind, pad_mv0]
  · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
  · intro j hj _
    unfold ind
    by_cases h1 : (mv n s M d t).pad n j
    · simp [h1]
    · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
      simp [h1, h2]
  · rcases hpos with h | ⟨i, hi, h⟩
    · left; simp [ind, h]
    · right; exact ⟨i, hi, by simp [ind, h]⟩

-- Swapping the sources of a gate

-- Gate `j` with its two sources swapped.
def sw (M : Model) (j : ℕ) : Model :=
  Model.mk M.op (fun i => if i = j then M.s2 j else M.s1 i) (fun i => if i = j then M.s1 j else M.s2 i)
    M.so M.w

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · exact hv.op_lt
  · intro i hi
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  · intro i hi
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  · exact hv.so_le
  · intro i hi r hr
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  · intro r hr; exact hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) : meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  apply meas_lt_of_key (valid_sw hv j) hind hj
  · intro i hi
    simp [key, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show i ≠ j by omega]
  · have h1 := hv.s1_le j hj
    simp only [key, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, ↓reduceIte]
    have hb : M.s2 j + 1 ≤ M.s1 j := hlt
    have := Nat.mul_le_mul_right (bb n s) hb
    have hB : M.s1 j < bb n s := by unfold bb; omega
    rw [Nat.add_mul, Nat.one_mul] at this
    generalize M.s2 j * bb n s = p at *
    generalize M.s1 j * bb n s = q at *
    omega

-- Swapping two adjacent gates

-- Wires `n + d` and `n + d + 1` exchanged.
def tau (n d k : ℕ) : ℕ := if k = n + d then n + d + 1 else if k = n + d + 1 then n + d else k

-- Gates `d` and `d + 1` exchanged, the later readers renumbered.
def xg (n : ℕ) (M : Model) (d : ℕ) : Model :=
  Model.mk (fun j => if j = d then M.op (d + 1) else if j = d + 1 then M.op d else M.op j)
    (fun j => if j = d then M.s1 (d + 1) else if j = d + 1 then M.s1 d
      else if d + 1 < j then tau n d (M.s1 j) else M.s1 j)
    (fun j => if j = d then M.s2 (d + 1) else if j = d + 1 then M.s2 d
      else if d + 1 < j then tau n d (M.s2 j) else M.s2 j)
    (tau n d M.so)
    (fun j r => if j = d then M.w (d + 1) r else if j = d + 1 then M.w d r else M.w j r)

section xgl
variable (n : ℕ) (M : Model) (d : ℕ)

theorem xg_op_d : (xg n M d).op d = M.op (d + 1) := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_op_d1 : (xg n M d).op (d + 1) = M.op d := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_s1_d : (xg n M d).s1 d = M.s1 (d + 1) := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_s1_d1 : (xg n M d).s1 (d + 1) = M.s1 d := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_s2_d : (xg n M d).s2 d = M.s2 (d + 1) := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_s2_d1 : (xg n M d).s2 (d + 1) = M.s2 d := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_w_d (r : ℕ) : (xg n M d).w d r = M.w (d + 1) r := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_w_d1 (r : ℕ) : (xg n M d).w (d + 1) r = M.w d r := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
theorem xg_so : (xg n M d).so = tau n d M.so := by simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
variable {n M d}
theorem xg_op_lt {j : ℕ} (h : j < d) : (xg n M d).op j = M.op j := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega]
theorem xg_s1_lt {j : ℕ} (h : j < d) : (xg n M d).s1 j = M.s1 j := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega, show ¬ d + 1 < j by omega]
theorem xg_s2_lt {j : ℕ} (h : j < d) : (xg n M d).s2 j = M.s2 j := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega, show ¬ d + 1 < j by omega]
theorem xg_op_gt {j : ℕ} (h : d + 1 < j) : (xg n M d).op j = M.op j := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega]
theorem xg_s1_gt {j : ℕ} (h : d + 1 < j) : (xg n M d).s1 j = tau n d (M.s1 j) := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega, h]
theorem xg_s2_gt {j : ℕ} (h : d + 1 < j) : (xg n M d).s2 j = tau n d (M.s2 j) := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show j ≠ d by omega, show j ≠ d + 1 by omega, h]
theorem xg_w_ne {j : ℕ} (h1 : j ≠ d) (h2 : j ≠ d + 1) (r : ℕ) : (xg n M d).w j r = M.w j r := by
  simp [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, h1, h2]
end xgl

theorem sv_mono (n : ℕ) (M : Model) {j j' k r : ℕ} (hk : k < n + j) (hjj : j ≤ j') :
    M.sv n j k r = M.sv n j' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · rw [if_neg h6, if_neg h6, if_pos hk, if_pos (show k < n + j' by omega)]

theorem xg_sv_low (n : ℕ) (M : Model) {d j k r : ℕ} (hj : j ≤ d) :
    (xg n M d).sv n j k r = M.sv n j k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + j
    · rw [if_neg h6, if_neg h6, if_pos h7, if_pos h7,
        xg_w_ne (show k - n ≠ d by omega) (show k - n ≠ d + 1 by omega)]
    · rw [if_neg h6, if_neg h6, if_neg h7, if_neg h7]

theorem xg_sv_d1 (n : ℕ) (M : Model) {d k r : ℕ} (hk : k < n + d) :
    (xg n M d).sv n (d + 1) k r = M.sv n d k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · rw [if_neg h6, if_neg h6, if_pos (show k < n + (d + 1) by omega), if_pos hk,
      xg_w_ne (show k - n ≠ d by omega) (show k - n ≠ d + 1 by omega)]

theorem xg_sv_high (n : ℕ) (M : Model) {d j k r : ℕ} (hj : d + 1 < j) :
    (xg n M d).sv n j (tau n d k) r = M.sv n j k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · have : tau n d k = k := by unfold tau; split_ifs <;> omega
    rw [this]; simp [h6]
  · by_cases h7 : k < n + j
    · have t1 : ¬ tau n d k < n := by unfold tau; split_ifs <;> omega
      have t2 : tau n d k < n + j := by unfold tau; split_ifs <;> omega
      rw [if_neg h6, if_pos h7, if_neg t1, if_pos t2]
      by_cases e1 : k = n + d
      · have : tau n d k = n + d + 1 := by unfold tau; rw [if_pos e1]
        rw [this, show n + d + 1 - n = d + 1 by omega, xg_w_d1, show k - n = d by omega]
      · by_cases e2 : k = n + d + 1
        · have : tau n d k = n + d := by unfold tau; rw [if_neg e1, if_pos e2]
          rw [this, show n + d - n = d by omega, xg_w_d, show k - n = d + 1 by omega]
        · have : tau n d k = k := by unfold tau; rw [if_neg e1, if_neg e2]
          rw [this, xg_w_ne (show k - n ≠ d by omega) (show k - n ≠ d + 1 by omega)]
    · have : tau n d k = k := by unfold tau; split_ifs <;> omega
      rw [this]; simp [h6, h7]

section xgv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d : ℕ}
  (hv : Valid n s g R M) (hd : d + 1 < s) (ha1 : M.s1 (d + 1) < n + d)
  (ha2 : M.s2 (d + 1) < n + d) (hb1 : M.s1 d < n + d) (hb2 : M.s2 d < n + d)
include hv hd ha1 ha2 hb1 hb2

theorem valid_xg : Valid n s g R (xg n M d) := by
  refine Valid.intro ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs
    · exact hv.op_lt _ hd
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  · intro j hj
    have := hv.s1_le j hj
    simp only [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; unfold tau; split_ifs <;> omega
  · intro j hj
    have := hv.s2_le j hj
    simp only [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; unfold tau; split_ifs <;> omega
  · have := hv.so_le
    simp only [xg, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; unfold tau; split_ifs <;> omega
  · intro j hj r hr
    by_cases h1 : j = d
    · rw [h1, xg_w_d, xg_op_d, xg_s1_d, xg_s2_d, xg_sv_low n M (le_refl d),
        xg_sv_low n M (le_refl d), hv.w_eq (d + 1) hd r hr, sv_mono n M ha1 (Nat.le_succ d),
        sv_mono n M ha2 (Nat.le_succ d)]
    · by_cases h2 : j = d + 1
      · rw [h2, xg_w_d1, xg_op_d1, xg_s1_d1, xg_s2_d1, xg_sv_d1 n M hb1, xg_sv_d1 n M hb2]
        exact hv.w_eq d (by omega) r hr
      · rw [xg_w_ne h1 h2]
        by_cases h3 : j < d
        · rw [xg_op_lt h3, xg_s1_lt h3, xg_s2_lt h3, xg_sv_low n M (le_of_lt h3),
            xg_sv_low n M (le_of_lt h3)]
          exact hv.w_eq j hj r hr
        · have h4 : d + 1 < j := by omega
          rw [xg_op_gt h4, xg_s1_gt h4, xg_s2_gt h4, xg_sv_high n M h4, xg_sv_high n M h4]
          exact hv.w_eq j hj r hr
  · intro r hr
    rw [xg_so, xg_sv_high n M hd]
    exact hv.out_eq r hr

omit hv in
theorem pad_xg (j : ℕ) : (xg n M d).pad n j ↔ M.pad n j := by
  unfold Model.pad
  by_cases h1 : j = d
  · subst h1
    rw [xg_op_d, xg_s1_d, xg_s2_d]
    constructor <;> rintro ⟨_, h, _⟩ <;> omega
  · by_cases h2 : j = d + 1
    · subst h2
      rw [xg_op_d1, xg_s1_d1, xg_s2_d1]
      constructor <;> rintro ⟨_, h, _⟩ <;> omega
    · by_cases h3 : j < d
      · rw [xg_op_lt h3, xg_s1_lt h3, xg_s2_lt h3]
      · have h4 : d + 1 < j := by omega
        have ht : ∀ k, tau n d k = n + j ↔ k = n + j := by
          intro k; unfold tau; split_ifs <;> omega
        rw [xg_op_gt h4, xg_s1_gt h4, xg_s2_gt h4, ht, ht]

theorem meas_xg (hlt : key n s M (d + 1) < key n s M d) : meas n s (xg n M d) < meas n s M := by
  have hind : ind n (xg n M d) = ind n M := by
    funext i; simp only [ind, pad_xg hd ha1 ha2 hb1 hb2]
  apply meas_lt_of_key (valid_xg hv hd ha1 ha2 hb1 hb2) hind (show d < s by omega)
  · intro i hi
    unfold key
    rw [xg_op_lt hi, xg_s1_lt hi, xg_s2_lt hi]
  · unfold key at hlt ⊢
    rw [xg_op_d, xg_s1_d, xg_s2_d]
    exact hlt

end xgv

theorem key_lt_of {n s : ℕ} {M : Model} {j : ℕ} (h1 : M.s2 j < bb n s)
    (h2 : M.s2 (j + 1) < bb n s) (ho1 : M.op j < 2) (ho2 : M.op (j + 1) < 2) (hn : ¬ LexLt M j)
    (hne : ¬ (M.s1 j = M.s1 (j + 1) ∧ M.s2 j = M.s2 (j + 1) ∧ M.op j = M.op (j + 1))) :
    key n s M (j + 1) < key n s M j := by
  unfold LexLt at hn
  unfold key
  rcases Nat.lt_or_ge (M.s1 (j + 1)) (M.s1 j) with h | h
  · have := Nat.mul_le_mul_right (bb n s) (show M.s1 (j + 1) + 1 ≤ M.s1 j from h)
    rw [Nat.add_mul, Nat.one_mul] at this
    generalize M.s1 (j + 1) * bb n s = p at *
    generalize M.s1 j * bb n s = q at *
    omega
  · have he : M.s1 (j + 1) = M.s1 j := by omega
    rw [he]
    generalize M.s1 j * bb n s = q
    omega

-- Trivial gates

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

-- A `TRUE` gate is trivial.
theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

-- A gate one of whose sources is `false` on every row is trivial.
theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

-- A gate one of whose sources is `true` on every row is trivial.
theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

-- A gate reading one source twice is trivial.
theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

-- A least model is in normal form

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  have used : ∀ j, j + 1 < s → ¬ M.pad n j →
      ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j) := by
    intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  have out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1) := by
    intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega
  have lex : ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
      LexLt M j := by
    intro j hj hnp h1 h2
    by_contra hc
    have hp1 : ¬ M.pad n (j + 1) := fun h => hnp (pre j hj h)
    have f0 := noF j (by omega) hnp
    have f1 := noF (j + 1) hj hp1
    have a1 := hv.s1_le j (by omega)
    have a2 := hv.s2_le j (by omega)
    have a3 := hv.s1_le (j + 1) hj
    have a4 := hv.s2_le (j + 1) hj
    have o0 := hv.op_lt j (by omega)
    have o1 := hv.op_lt (j + 1) hj
    have o0' : M.op j ≠ 2 := fun h => hnp (padOp j (by omega) h)
    have o1' : M.op (j + 1) ≠ 2 := fun h => hp1 (padOp (j + 1) hj h)
    by_cases heq : M.s1 j = M.s1 (j + 1) ∧ M.s2 j = M.s2 (j + 1) ∧ M.op j = M.op (j + 1)
    · obtain ⟨e1, e2, e3⟩ := heq
      refine htriv (j + 1) hj hp1 (copy_tgt hv hj (k := n + j) (by omega) fun r hr => ?_)
      have hw1 := hv.w_eq (j + 1) hj r hr
      have hw0 := hv.w_eq j (by omega) r hr
      have hs : M.sv n (j + 1) (n + j) r = M.w j r := by
        unfold Model.sv
        rw [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
          show n + j - n = j by omega]
      rw [hs, hw1, hw0, ← e1, ← e2, ← e3, sv_mono n M (show M.s1 j < n + j by omega) (Nat.le_succ j),
        sv_mono n M (show M.s2 j < n + j by omega) (Nat.le_succ j)]
    · have hk := key_lt_of (n := n) (s := s) (M := M) (j := j) (by unfold bb; omega)
        (by unfold bb; omega) (by omega) (by omega) hc heq
      exact hmin _ (valid_xg hv hj (by omega) (by omega) (by omega) (by omega))
        (meas_xg hv hj (by omega) (by omega) (by omega) (by omega) hk)
  exact ⟨M, hv, pre, padOp, noF, padRd, ord, used, out, lex⟩

-- The split into cubes

theorem main (n s : ℕ) (hs : 0 < s) (g : ℕ → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ r ∈ rows, C.eval (xr n r) = g r) :
    ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k) := by
  have hv := valid_ofCirc n s g (· ∈ rows) C hC hsz hev
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  have h1 := hM.s1_le (s - 1) (by omega)
  have h0 := hM.op_lt (s - 1) (by omega)
  refine ⟨M.op (s - 1) * (n + s) + M.s1 (s - 1), ?_, val n s M, ?_⟩
  · unfold enc2CubeCount
    have := Nat.mul_le_mul_right (n + s) (show M.op (s - 1) + 1 ≤ 3 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact enc2_sat hrows hM hnf c h
    · have hmod : (M.op (s - 1) * (n + s) + M.s1 (s - 1)) % (n + s) = M.s1 (s - 1) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hdiv : (M.op (s - 1) * (n + s) + M.s1 (s - 1)) / (n + s) = M.op (s - 1) := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
          Nat.zero_add]
      simp only [enc2Cube, hmod, hdiv, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_s1, or_false, beq_self_eq_true]
      · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, or_false, beq_self_eq_true]

end Encoding

end PEqualNP.Outside.L_meta_1884.NormalizedEncoding

namespace PEqualNP.Outside.L_meta_1884.NormalizedEncoding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

def freeRows : List ℕ := [3, 1030, 1036, 13, 17, 1048, 33, 1074, 1090, 69, 1128, 1140, 1156, 133, 1162, 1184, 1224, 201, 1232, 1288, 265, 1300, 1312, 1344, 321, 385, 1426, 521, 1552, 1572, 1578, 1600, 577, 1664, 641, 1794, 1796, 773]

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def rowValue (r : ℕ) : Bool := target (fun i => r.testBit i)

lemma freeRows_lt : ∀ r ∈ freeRows, r < 2 ^ 11 := by decide +kernel

lemma freeRows_correlated : ∀ r ∈ freeRows,
    xr 11 r = List.ofFn (fun i : Fin 10 => r.testBit i) ++ [!(r.testBit 0)] := by
  decide +kernel

lemma monotone_of_zero_not (C : Circuit) (hC : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 0) : Monotone2 C := by
  classical
  have he : (C.gates.filter fun (g : Gate) => decide (g.op = GateOp.not)) = [] :=
    List.length_eq_zero_iff.mp (by simpa [PEqualNP.NotBracket.notCount] using hn)
  intro g hg
  obtain ⟨hop, hlen⟩ := hC g hg
  have hnot : g.op ≠ GateOp.not := by
    intro h
    have hm : g ∈ C.gates.filter (fun (g : Gate) => decide (g.op = GateOp.not)) := by
      exact List.mem_filter.mpr ⟨hg, by simp [h]⟩
    rw [he] at hm
    simp at hm
  exact ⟨by simpa [hnot] using hop, hlen⟩

theorem circuit_sat_normalized (n s : ℕ) (hs : 0 < s) (g : ℕ → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C)
    (hsize : C.size ≤ s) (he : ∀ r ∈ rows, C.eval (xr n r) = g r) :
    FormulaSat (enc2 n s g rows) := by
  obtain ⟨k, hk, a, hsat⟩ := main n s hs g rows hrows C hC hsize he
  exact ⟨a, fun cl hcl => hsat cl (List.mem_append_left _ hcl)⟩

theorem canonical_zero_not_sat (C : Circuit) (hC : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 0) (hsize : C.size ≤ 18)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) = target x) :
    FormulaSat (enc2 11 18 rowValue freeRows) := by
  apply circuit_sat_normalized 11 18 (by decide) rowValue freeRows freeRows_lt C
    (monotone_of_zero_not C hC hn) hsize
  intro r hr
  rw [freeRows_correlated r hr]
  exact correct (fun i => r.testBit i)

theorem canonical_zero_not_from_unsat
    (unsat : ¬ FormulaSat (enc2 11 18 rowValue freeRows))
    (C : Circuit) (hC : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 0) (hsize : C.size ≤ 18) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) ≠ target x := by
  by_contra h
  push Not at h
  exact unsat (canonical_zero_not_sat C hC hn hsize h)

end PEqualNP.Outside.L_meta_1884.NormalizedEncoding
