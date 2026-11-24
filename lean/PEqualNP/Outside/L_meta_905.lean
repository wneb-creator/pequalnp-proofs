import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_905
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 10
def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}
def related (v w : V) : Bool := decide (s(v, w) ∈ edges)
def Good (I : Finset V) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, related v w = false) ∧
  (∀ u : V, u ∉ I → ∃ v ∈ I, related u v = true)
def rows : Fin 15 → Finset V := ![{1, 4, 5}, {0, 2, 6}, {3, 5, 6}, {2, 4, 5, 6}, {1, 3, 7}, {0, 3, 6, 7}, {4, 6, 7}, {2, 4, 8}, {0, 7, 8}, {1, 4, 7, 8}, {0, 3, 9}, {2, 5, 9}, {1, 3, 5, 9}, {1, 8, 9}, {0, 2, 8, 9}]
def through : V → Fin 5 → Fin 15 := ![![1, 5, 8, 10, 14],
    ![0, 4, 9, 12, 13],
    ![1, 3, 7, 11, 14],
    ![2, 4, 5, 10, 12],
    ![0, 3, 6, 7, 9],
    ![0, 2, 3, 11, 12],
    ![1, 2, 3, 5, 6],
    ![4, 5, 6, 8, 9],
    ![7, 8, 9, 13, 14],
    ![10, 11, 12, 13, 14]]
theorem rowsGood : ∀ i, Good (rows i) := by
  unfold Good
  decide +kernel
theorem rowContains : ∀ v i, v ∈ rows (through v i) := by decide +kernel
private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩
private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]
private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]
def Separates (C : AndCountCircuit 10) : Prop :=
  ∀ I, Good I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true
theorem bare_out_empty (C : AndCountCircuit 10) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  have he := (h _ (rowsGood (through v 0))).1
  have ht : C.eval (rows (through v 0)) = true :=
    decide_eq_true (Or.inl ⟨v, hv, rowContains v 0⟩)
  simp [he] at ht
theorem jointlyPresent : ∀ a b : V, related a b = false → ∃ i, a ∈ rows i ∧ b ∈ rows i := by
  decide +kernel
def preScan (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => match f n with | true => preScan f n | false => false
lemma preScan_at {f : ℕ → Bool} {n : ℕ} (h : preScan f n = true) {x : ℕ} (hx : x < n) : f x = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases e : f n
    · simp [preScan,e] at h
    · by_cases eq : x = n
      · simpa only [eq] using e
      · exact ih (by simpa only [preScan,e] using h) (by omega)
def preAdj (a b : ℕ) : Bool :=
  Nat.testBit 0x3406889302606094508a11432 (Nat.add (Nat.mul 10 a) b)
lemma preAdj_eq : ∀ a b : V, related a b = preAdj a.val b.val := by decide +kernel
def preNeighbor (a b : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight 0x4600704764635003036505990920250098898101700800870003990003004028808024730173010166200020004551004101 (4*(10*a+b))) 15
def preCommon (a b c : ℕ) : Bool :=
  Nat.beq a b || (!(preAdj a c && preAdj b c) || Nat.beq c (preNeighbor a b))
lemma preCommon_all : preScan (fun a => preScan (fun b => preScan (preCommon a b) 10) 10) 10 = true := by decide +kernel
theorem noSquare : ∀ a b c d : V, related a c = true → related a d = true →
    related b c = true → related b d = true → a = b ∨ c = d := by
  intro a b c d h1 h2 h3 h4
  by_cases e : a = b
  · exact Or.inl e
  · right
    have diff : Nat.beq a.val b.val = false :=
      Bool.eq_false_iff.mpr (fun h => e (Fin.ext (Nat.eq_of_beq_eq_true h)))
    have common : ∀ z : V, related a z = true → related b z = true → z.val = preNeighbor a.val b.val := by
      intro z left right
      rw [preAdj_eq] at left right
      have good := preScan_at (preScan_at (preScan_at preCommon_all a.isLt) b.isLt) z.isLt
      simpa [preCommon,diff,left,right] using good
    exact Fin.ext ((common c h1 h3).trans (common d h2 h4).symm)
theorem isolatedEdge : ∀ a b : V, related a b = true → ∃ i, a ∉ rows i ∧
    ∀ x ∈ insert a (rows i), ∀ y ∈ insert a (rows i), related x y = true →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by decide +kernel
theorem starCenter (L R : Finset V) (h : ∀ a ∈ L, ∀ b ∈ R, related a b = true) :
    ∃ t : V, ∀ a ∈ L, ∀ b ∈ R, a = t ∨ b = t := by
  rcases L.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · exact ⟨0, by simp [he]⟩
  rcases R.eq_empty_or_nonempty with he | ⟨b, hb⟩
  · exact ⟨0, by simp [he]⟩
  by_cases hl : ∀ x ∈ L, x = a
  · exact ⟨a, fun x hx _ _ => Or.inl (hl x hx)⟩
  push Not at hl
  obtain ⟨x, hx, hn⟩ := hl
  exact ⟨b, fun _ _ y hy => Or.inr ((noSquare x a y b
    (h x hx y hy) (h x hx b hb) (h a ha y hy) (h a ha b hb)).resolve_left hn)⟩
theorem firstTrue (C : AndCountCircuit 10) (h : Separates C) (U : Finset V) (hu : C.eval U = true) :
    ∃ i, (∃ a ∈ C.leftVars i, a ∈ U) ∧ (∃ b ∈ C.rightVars i, b ∈ U) := by
  by_contra hn
  have hz (d : ℕ) (i : Fin C.size) : C.gateValFuel U d i = false := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      apply Bool.eq_false_iff.mpr
      simp only [gateValFuel, sideTrue, ih, Bool.false_eq_true,
        and_false, exists_false, or_false]
      exact fun ht => hn ⟨i, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht⟩
  rw [eval, decide_eq_true_eq] at hu
  rcases hu with ⟨v, hv, _⟩ | ⟨i, _, ht⟩
  · exact bare_out_empty C h v hv
  · simp [gateVal, hz] at ht
def bare (C : AndCountCircuit 10) (v : V) :=
  Finset.univ.filter fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i
lemma degreeThree : ∀ v : V, (Finset.univ.filter (fun w : V => related v w)).card = 3 := by
  decide +kernel
lemma safeImpossible (C : AndCountCircuit 10) (h : Separates C)
    (small : C.size ≤ 6) (readTwo : ∀ v, (bare C v).card ≤ 2)
    (safe : ∀ i j, C.gateVal (rows j) i = false) : False := by
  classical
  have rect (i : Fin C.size) (a : V) (ha : a ∈ C.leftVars i) (b : V) (hb : b ∈ C.rightVars i) :
      related a b = true := by
    by_contra! hn
    obtain ⟨j, hja, hjb⟩ := jointlyPresent a b (Bool.eq_false_iff.mpr hn)
    have ht : C.gateVal (rows j) i = true := by
      rw [gateVal_unfold, Bool.and_eq_true]
      exact ⟨decide_eq_true (Or.inl ⟨a, ha, hja⟩), decide_eq_true (Or.inl ⟨b, hb, hjb⟩)⟩
    simp [safe] at ht
  choose center hc using fun i => starCenter _ _ (rect i)
  let T := Finset.univ.image center
  obtain ⟨v,hv⟩ : ∃ v : V, v ∉ T := by
    by_contra! hh
    have eq : T = Finset.univ := Finset.eq_univ_of_forall hh
    have card : T.card ≤ C.size := Finset.card_image_le.trans_eq (by simp)
    rw [eq] at card
    simp [V] at card
    omega
  have sub : Finset.univ.filter (fun w : V => related v w) ⊆ (bare C v).image center := by
    intro w hw
    have edge : related v w = true := (Finset.mem_filter.mp hw).2
    obtain ⟨j,missing,isolated⟩ := isolatedEdge v w edge
    have hp := (h _ (rowsGood j)).2 v missing
    obtain ⟨i, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := firstTrue C h _ hp
    have neq : v ≠ center i := fun e => hv (e ▸ Finset.mem_image_of_mem center (Finset.mem_univ i))
    have cen := hc i x hx y hy
    rcases isolated x hx' y hy' (rect i x hx y hy) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hx⟩,
        (cen.resolve_left neq).symm⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hy⟩,
        (cen.resolve_right neq).symm⟩
  have bound := (Finset.card_le_card sub).trans (Finset.card_image_le.trans (readTwo v))
  rw [degreeThree] at bound
  omega
def portVars (C : AndCountCircuit 10) (i : Fin C.size) : Bool → Finset V
  | false => C.leftVars i
  | true => C.rightVars i
def references (C : AndCountCircuit 10) (i : Fin C.size) : Bool → Finset (Fin C.size)
  | false => C.leftGates i
  | true => C.rightGates i
def meets (B U : Finset V) : Prop := ∃ v ∈ B, v ∈ U
def seed (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) : Prop :=
  ∀ b, meets (portVars C p b) U
def firesAt (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) (b : Bool) : Prop :=
  meets (portVars C i b) U ∨ ∃ j ∈ references C i b, j < i ∧ C.gateVal U j = true
lemma gate_iff (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) :
    C.gateVal U i = true ↔ ∀ b, firesAt C i U b := by
  rw [gateVal_unfold, Bool.and_eq_true]
  simp only [sideTrue, decide_eq_true_eq]
  exact ⟨fun h b => by cases b with | false => exact h.1 | true => exact h.2,
    fun h => ⟨h false, h true⟩⟩
def residualRaw (C : AndCountCircuit 10) (p i : Fin C.size) (U : Finset V) (b : Bool) : Prop :=
  meets (portVars C i b) U ∨ p ∈ references C i b ∧ seed C p U
def residualOut (C : AndCountCircuit 10) (p i : Fin C.size) : Prop := i < p ∨ i ∈ C.outGates
lemma positiveClosure (C : AndCountCircuit 10) (correct : Separates C) (p : Fin C.size)
    (outside : p ∉ C.outGates) (U : Finset V) (hu : C.eval U = true)
    (active : Fin C.size → Prop)
    (closed : ∀ i, i ≠ p → (∀ b, residualRaw C p i U b ∨
      ∃ j ∈ references C i b, j ≠ p ∧ active j) → active i) :
    ∃ i, i ≠ p ∧ residualOut C p i ∧ active i := by
  by_contra h
  have off (i : Fin C.size) (hi : i < p) : ¬ active i :=
    fun a => h ⟨i, ne_of_lt hi, Or.inl hi, a⟩
  have sim (i : Fin C.size) :
      C.gateVal U i = true → (i = p → seed C p U) ∧ (i ≠ p → active i) := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro val
      have sides := (gate_iff C i U).mp val
      constructor
      · rintro rfl b
        rcases sides b with hv | ⟨j, _, hj, valj⟩
        · exact hv
        · exact (off j hj ((ih j hj valj).2 (ne_of_lt hj))).elim
      · intro ne
        apply closed i ne
        intro b
        rcases sides b with hv | ⟨j, hj, ltj, valj⟩
        · exact Or.inl (Or.inl hv)
        · by_cases e : j = p
          · exact Or.inl (Or.inr ⟨e ▸ hj, (ih j ltj valj).1 e⟩)
          · exact Or.inr ⟨j, hj, e, (ih j ltj valj).2 e⟩
  rcases (decide_eq_true_eq.mp hu : (∃ v ∈ C.outVars, v ∈ U) ∨
      ∃ i ∈ C.outGates, C.gateVal U i = true) with ⟨v, hv, _⟩ | ⟨i, hi, val⟩
  · exact bare_out_empty C correct v hv
  · have ne : i ≠ p := fun e => outside (e ▸ hi)
    exact h ⟨i, ne, Or.inr hi, (sim i val).2 ne⟩
def early (C : AndCountCircuit 10) (p : Fin C.size) : Prop :=
  ∀ j, j < p → ∀ r, C.gateVal (rows r) j = false
lemma seed_eq (C : AndCountCircuit 10) (p : Fin C.size) (r : Fin 15) (ep : early C p) :
    seed C p (rows r) ↔ C.gateVal (rows r) p = true := by
  rw [gate_iff]
  constructor
  · intro h b
    exact Or.inl (h b)
  · intro h b
    rcases h b with v | ⟨j, _, e, ht⟩
    · exact v
    · simp [ep j e r] at ht
lemma refs_earlier (C : AndCountCircuit 10) (wf : C.WellFormed) (i j : Fin C.size) (b : Bool)
    (mem : j ∈ references C i b) : j < i := by
  cases b with
  | false => exact (wf i).1 j mem
  | true => exact (wf i).2 j mem
def chosenSide (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) : Bool :=
  decide ((C.leftVars i ∩ U).Nonempty ∨
    ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true)
lemma choice_false (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V)
    (z : C.gateVal U i = false) : ¬ firesAt C i U (chosenSide C i U) := by
  have bv : chosenSide C i U = true ↔ firesAt C i U false := by
    simp [chosenSide, firesAt, meets, portVars, references, Finset.Nonempty]
  cases v : chosenSide C i U with
  | false => exact fun f => by have := bv.mpr f; simp [v] at this
  | true =>
    intro f
    have g := (gate_iff C i U).mpr (fun b => by
      cases b with | false => exact bv.mp v | true => exact f)
    simp [z] at g
def selected (C : AndCountCircuit 10) (p i : Fin C.size) (r : Fin 15) (b : Bool) : Prop :=
  i ≠ p ∧ C.gateVal (rows r) i = false ∧ b = chosenSide C i (rows r)
lemma selected_raw (C : AndCountCircuit 10) (wf : C.WellFormed) (p : Fin C.size)
    (ep : early C p) (r : Fin 15) (i : Fin C.size) (b : Bool) (sel : selected C p i r b) :
    ¬ residualRaw C p i (rows r) b := by
  obtain ⟨_, hz, rfl⟩ := sel
  intro h
  apply choice_false C i _ hz
  rcases h with hv | ⟨mem, hot⟩
  · exact Or.inl hv
  · exact Or.inr ⟨p, mem, refs_earlier C wf i p _ mem, (seed_eq C p r ep).mp hot⟩
lemma selected_ref (C : AndCountCircuit 10) (wf : C.WellFormed) (p : Fin C.size)
    (r : Fin 15) (i j : Fin C.size) (b : Bool) (sel : selected C p i r b)
    (mem : j ∈ references C i b) (ne : j ≠ p) : ∃ b', selected C p j r b' := by
  obtain ⟨_, hz, rfl⟩ := sel
  refine ⟨_, ne, Bool.eq_false_iff.mpr ?_, rfl⟩
  intro ht
  exact choice_false C i _ hz (Or.inr ⟨j, mem, refs_earlier C wf i j _ mem, ht⟩)
lemma selected_out (C : AndCountCircuit 10) (correct : Separates C) (p : Fin C.size)
    (ep : early C p) (r : Fin 15) (i : Fin C.size) (ne : i ≠ p) (out : residualOut C p i) :
    ∃ b, selected C p i r b := by
  refine ⟨_, ne, ?_, rfl⟩
  rcases out with hi | hi
  · exact ep i hi r
  · apply Bool.eq_false_iff.mpr
    intro ht
    have con : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨i,hi,ht⟩)
    simp [(correct _ (rowsGood r)).1] at con
abbrev Slot := Fin 5 × Bool
abbrev Feature := Option V
def present (A B U : Finset V) : Feature → Prop
  | some v => v ∈ U
  | none => meets A U ∧ meets B U
def point (U : Finset V) : Prop := ∃ r : Fin 15, ∃ v : V, v ∉ rows r ∧ U = insert v (rows r)
def layout (A B : Finset V) (pos : Feature → Slot → Prop) : Prop :=
  ∃ (out : Fin 5 → Prop) (ref : Slot → Fin 5 → Prop) (cut : Fin 15 → Slot → Prop),
    (∀ r k b d, cut r (k,b) → cut r (k,d) → b = d) ∧
    (∀ r s z, cut r s → pos z s → ¬ present A B (rows r) z) ∧
    (∀ r s j, cut r s → ref s j → ∃ b, cut r (j,b)) ∧
    (∀ r k, out k → ∃ b, cut r (k,b)) ∧
    ∀ U, point U → ∀ a : Fin 5 → Prop,
      (∀ k, (∀ b, (∃ z, pos z (k,b) ∧ present A B U z) ∨
        ∃ j, ref (k,b) j ∧ a j) → a k) → ∃ k, out k ∧ a k
def capacity (A B : Finset V) (pos : Feature → Slot → Prop) : Prop :=
  ∀ v : V, ∃ S : Finset (Fin 5), (∀ k, k ∈ S ↔ ∃ b, pos (some v) (k,b)) ∧
    S.card ≤ 2 ∧ (v ∈ A ∨ v ∈ B → S.card ≤ 1)
abbrev otherGate (C : AndCountCircuit 10) (p : Fin C.size) := {i : Fin C.size // i ≠ p}
def number (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (i : otherGate C p) : Fin 5 :=
  ⟨if i.val < p then i.val.val else i.val.val - 1, by
    have hn : i.val.val ≠ p.val := fun h => i.property (Fin.ext h)
    have hi := i.val.isLt
    have hp := p.isLt
    split <;> simp_all only [Fin.lt_def] <;> omega⟩
lemma number_inj (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6) :
    Function.Injective (number C p small) := by
  intro i j h
  have hi : i.val.val ≠ p.val := fun h => i.property (Fin.ext h)
  have hj : j.val.val ≠ p.val := fun h => j.property (Fin.ext h)
  apply Subtype.ext
  apply Fin.ext
  have eq := congrArg Fin.val h
  simp only [number, Fin.lt_def] at eq
  split at eq <;> split at eq <;> omega
def marking (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (z : Feature) (s : Slot) : Prop :=
  ∃ i : otherGate C p, number C p small i = s.1 ∧ match z with
    | some v => v ∈ portVars C i.val s.2
    | none => p ∈ references C i.val s.2
lemma seed_present (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) :
    seed C p U ↔ present (C.leftVars p) (C.rightVars p) U none :=
  ⟨fun h => ⟨h false,h true⟩, fun h b => by cases b with | false => exact h.1 | true => exact h.2⟩
lemma marking_raw (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (i : otherGate C p) (b : Bool) (U : Finset V) :
    residualRaw C p i.val U b ↔ ∃ z, marking C p small z (number C p small i,b) ∧
      present (C.leftVars p) (C.rightVars p) U z := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨hp, hs⟩)
    · exact ⟨some v, ⟨i, rfl, hv⟩, hu⟩
    · exact ⟨none, ⟨i, rfl, hp⟩, (seed_present C p U).mp hs⟩
  · rintro ⟨z, ⟨j, eq, mem⟩, hz⟩
    obtain rfl := number_inj C p small eq
    cases z with
    | none => exact Or.inr ⟨mem,(seed_present C p U).mpr hz⟩
    | some v => exact Or.inl ⟨v,mem,hz⟩
lemma get_layout (C : AndCountCircuit 10) (wf : C.WellFormed) (correct : Separates C)
    (p : Fin C.size) (small : C.size ≤ 6) (ep : early C p) (outside : p ∉ C.outGates) :
    layout (C.leftVars p) (C.rightVars p) (marking C p small) := by
  let f := number C p small
  let O (k : Fin 5) := ∃ i : otherGate C p, f i = k ∧ residualOut C p i.val
  let R (s : Slot) (k : Fin 5) := ∃ i j : otherGate C p,
    f i = s.1 ∧ f j = k ∧ j.val ∈ references C i.val s.2
  let M (r : Fin 15) (s : Slot) := ∃ i : otherGate C p, f i = s.1 ∧ selected C p i.val r s.2
  have inj : Function.Injective f := number_inj C p small
  refine ⟨O,R,M,?_,?_,?_,?_,?_⟩
  · rintro r k b d ⟨i, ei, hb⟩ ⟨j, ej, hd⟩
    obtain rfl := inj (ei.trans ej.symm)
    exact hb.2.2.trans hd.2.2.symm
  · rintro r ⟨k,b⟩ z ⟨i,ei,sel⟩ pos hz
    change f i = k at ei
    subst k
    exact selected_raw C wf p ep r i.val b sel ((marking_raw C p small i b _).mpr ⟨z,pos,hz⟩)
  · rintro r ⟨k,b⟩ j ⟨i,ei,sel⟩ ⟨x,y,ex,ey,ref⟩
    obtain rfl := inj (ei.trans ex.symm)
    obtain ⟨d,hd⟩ := selected_ref C wf p r i.val y.val b sel ref y.property
    exact ⟨d,y,ey,hd⟩
  · rintro r k ⟨i,ei,out⟩
    obtain ⟨b,hb⟩ := selected_out C correct p ep r i.val i.property out
    exact ⟨b,i,ei,hb⟩
  · rintro U ⟨r,v,miss,rfl⟩ a closed
    let active (i : Fin C.size) := ∃ e : i ≠ p, a (f ⟨i,e⟩)
    have cl (i : Fin C.size) (ne : i ≠ p) (hs : ∀ b, residualRaw C p i (insert v (rows r)) b ∨
        ∃ j ∈ references C i b, j ≠ p ∧ active j) : active i := by
      let x : otherGate C p := ⟨i,ne⟩
      refine ⟨ne,closed (f x) ?_⟩
      intro b
      rcases hs b with raw | ⟨j,ref,ne',_,act⟩
      · exact Or.inl ((marking_raw C p small x b _).mp raw)
      · let y : otherGate C p := ⟨j,ne'⟩
        exact Or.inr ⟨f y,⟨x,y,rfl,rfl,ref⟩,act⟩
    obtain ⟨i,ne,out,_,act⟩ := positiveClosure C correct p outside _ ((correct _ (rowsGood r)).2 v miss) active cl
    exact ⟨f ⟨i,ne⟩,⟨⟨i,ne⟩,rfl,out⟩,act⟩
lemma get_capacity (C : AndCountCircuit 10) (p : Fin C.size) (small : C.size ≤ 6)
    (bound : ∀ v, (bare C v).card ≤ 2) :
    capacity (C.leftVars p) (C.rightVars p) (marking C p small) := by
  classical
  intro v
  let T := Finset.univ.filter (fun i : otherGate C p => i.val ∈ bare C v)
  let f := number C p small
  have eq : T.image Subtype.val = (bare C v).erase p := by
    ext i
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨j,h,rfl⟩
      exact ⟨j.property,h⟩
    · rintro ⟨ne,mem⟩
      exact ⟨⟨i,ne⟩,mem,rfl⟩
  have count : T.card = ((bare C v).erase p).card := by
    rw [← eq, Finset.card_image_of_injective _ Subtype.val_injective]
  refine ⟨T.image f,?_,(Finset.card_image_le.trans count.le).trans
    ((Finset.card_le_card (Finset.erase_subset _ _)).trans (bound v)),?_⟩
  · intro k
    constructor
    · rintro h
      obtain ⟨i,mem,e⟩ := Finset.mem_image.mp h
      rcases (Finset.mem_filter.mp (Finset.mem_filter.mp mem).2).2 with hl | hr
      · exact ⟨false,i,e,hl⟩
      · exact ⟨true,i,e,hr⟩
    · rintro ⟨b,i,e,mem⟩
      refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,e⟩
      cases b with
      | false => exact Or.inl mem
      | true => exact Or.inr mem
  · intro hp
    have own : p ∈ bare C v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
    have total := Finset.card_erase_add_one own
    have le := (Finset.card_image_le : (T.image f).card ≤ T.card).trans count.le
    have bound' := bound v
    omega
def edgePairs : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def graph : SimpleGraph V := SimpleGraph.fromRel fun a b : V => (a.val,b.val) ∈ edgePairs
lemma graph_iff (v w : V) : graph.Adj v w ↔ related v w = true := by
  change (v ≠ w ∧ ((v.val,w.val) ∈ edgePairs ∨ (w.val,v.val) ∈ edgePairs)) ↔ _
  revert v w
  decide +kernel
lemma related_symm : ∀ v w : V, related v w = related w v := by decide +kernel
lemma reduce_problem (noLayout : ∀ A B pos, (∃ r, present A B (rows r) none) →
    capacity A B pos → layout A B pos → False)
    (C : AndCountCircuit 10) (wf : C.WellFormed) (small : C.size ≤ 6)
    (bound : ∀ v, (bare C v).card ≤ 2)
    (spec : ∀ I : Finset V, (∀ a ∈ I, ∀ c ∈ I, ¬ graph.Adj a c) →
      (∀ w : V, w ∉ I → ∃ a ∈ I, graph.Adj a w) →
      C.eval I = false ∧ ∀ w : V, w ∉ I → C.eval (insert w I) = true) : False := by
  classical
  have correct : Separates C := by
    intro I hI
    refine spec I (fun a ha c hc h => ?_) (fun w hw => ?_)
    · have eq := (graph_iff a c).mp h
      simp [hI.1 a ha c hc] at eq
    · obtain ⟨a,ha,adj⟩ := hI.2 w hw
      exact ⟨a,ha,(graph_iff a w).mpr ((related_symm a w).trans adj)⟩
  let S := Finset.univ.filter fun i : Fin C.size => ∃ r : Fin 15, C.gateVal (rows r) i = true
  have ne : S.Nonempty := by
    by_contra hn
    exact safeImpossible C correct small bound fun i r => Bool.eq_false_iff.mpr
      (fun h => hn ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,h⟩⟩)
  let p := S.min' ne
  obtain ⟨r,hr⟩ := (Finset.mem_filter.mp (S.min'_mem ne)).2
  have ep : early C p := by
    intro i hi t
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (not_le_of_gt hi) (S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,t,ht⟩))
  have out : p ∉ C.outGates := by
    intro hp
    have ht : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨p,hp,hr⟩)
    simp [(correct _ (rowsGood r)).1] at ht
  exact noLayout _ _ _ ⟨r,(seed_present C p _).mp ((seed_eq C p r ep).mpr hr)⟩
    (get_capacity C p small bound) (get_layout C wf correct p small ep out)
def stable (A B : Finset V) (r : Fin 15) (v : V) : Prop :=
  v ∉ rows r ∧ (present A B (insert v (rows r)) none → present A B (rows r) none)
def conflict (A B : Finset V) (v w : V) : Prop :=
  (∃ r, stable A B r v ∧ stable A B r w) ∧
  (∃ r, stable A B r v ∧ w ∈ rows r) ∧ (∃ r, stable A B r w ∧ v ∈ rows r)
def coverCuts (A B : Finset V) (pos : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) : Prop :=
  (∀ r k b d, M r (k,b) → M r (k,d) → b = d) ∧
  (∀ r s z, M r s → pos z s → ¬ present A B (rows r) z) ∧
  ∀ r U, point U → ∃ s z, M r s ∧ pos z s ∧ present A B U z
lemma cuts_of_layout {A B : Finset V} {pos : Feature → Slot → Prop} (h : layout A B pos) :
    ∃ M, coverCuts A B pos M := by
  classical
  obtain ⟨O,R,M,unique,avoid,closed,root,positive⟩ := h
  refine ⟨M,unique,avoid,?_⟩
  intro r U hu
  by_contra nf
  let a (k : Fin 5) := ¬ ∃ b, M r (k,b)
  have hh (k) (inputs : ∀ b, (∃ z, pos z (k,b) ∧ present A B U z) ∨ ∃ j, R (k,b) j ∧ a j) :
      a k := by
    rintro ⟨b,mem⟩
    rcases inputs b with ⟨z,pz,hz⟩ | ⟨j,ref,absent⟩
    · exact nf ⟨_,z,mem,pz,hz⟩
    · exact absent (closed r _ j mem ref)
  obtain ⟨k,out,off⟩ := positive U hu a hh
  exact off (root r k out)
lemma stable_cut {A B : Finset V} {pos : Feature → Slot → Prop} {M : Fin 15 → Slot → Prop}
    (h : coverCuts A B pos M) {r : Fin 15} {v : V} (st : stable A B r v) :
    ∃ s, M r s ∧ pos (some v) s := by
  obtain ⟨s,z,mem,pz,hz⟩ := h.2.2 r _ ⟨r,v,st.1,rfl⟩
  cases z with
  | none => exact (h.2.1 r s none mem pz (st.2 hz)).elim
  | some w =>
    rcases Finset.mem_insert.mp hz with e | hin
    · exact ⟨s,mem,e ▸ pz⟩
    · exact (h.2.1 r s (some w) mem pz hin).elim
lemma conflict_distinct {A B : Finset V} {pos : Feature → Slot → Prop} {M : Fin 15 → Slot → Prop}
    (h : coverCuts A B pos M) {v w : V} (hc : conflict A B v w) (k : Fin 5)
    (onlyV : ∀ s, pos (some v) s → s.1 = k)
    (onlyW : ∀ s, pos (some w) s → s.1 = k) : False := by
  obtain ⟨⟨r,sv,sw⟩,⟨j,sj,wj⟩,⟨l,sl,vl⟩⟩ := hc
  obtain ⟨⟨k₁,b⟩,mb,pb⟩ := stable_cut h sv
  obtain ⟨⟨k₂,d⟩,md,pd⟩ := stable_cut h sw
  have eqk₁ : k₁ = k := onlyV _ pb
  subst k₁
  have eqk₂ : k₂ = k := onlyW _ pd
  subst k₂
  have eqd := h.1 r k b d mb md
  subst d
  obtain ⟨⟨k₃,c⟩,mc,pc⟩ := stable_cut h sj
  have eqk₃ : k₃ = k := onlyV _ pc
  subst k₃
  obtain ⟨⟨k₄,e⟩,me,pe⟩ := stable_cut h sl
  have eqk₄ : k₄ = k := onlyW _ pe
  subst k₄
  have nc : ¬pos (some w) (k,c) := fun hh => h.2.1 j _ (some w) mc hh wj
  have ne : ¬pos (some v) (k,e) := fun hh => h.2.1 l _ (some v) me hh vl
  have bd : b ≠ c := fun eq => nc (eq ▸ pd)
  have be : b ≠ e := fun eq => ne (eq ▸ pb)
  have ce : c ≠ e := fun eq => nc (eq ▸ pe)
  exact (show ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False by decide) b c e bd be ce
lemma six_conflict {A B : Finset V} {pos : Feature → Slot → Prop}
    (cap : capacity A B pos) (h : layout A B pos) (xs : Fin 6 → V)
    (use : ∀ i, xs i ∈ A ∨ xs i ∈ B) (cl : ∀ i j, i ≠ j → conflict A B (xs i) (xs j)) : False := by
  classical
  obtain ⟨M,hM⟩ := cuts_of_layout h
  choose S hs using cap
  have single (i : Fin 6) : ∃ k : Fin 5, ∀ s, pos (some (xs i)) s → s.1 = k := by
    let j : Fin 6 := if i = 0 then 1 else 0
    have different : i ≠ j := by by_cases hi : i = 0 <;> simp [j,hi]
    obtain ⟨r,sv,_⟩ := (cl i j different).1
    obtain ⟨s,_,ps⟩ := stable_cut hM sv
    have mem : s.1 ∈ S (xs i) := ((hs (xs i)).1 s.1).mpr ⟨s.2,ps⟩
    have one := (hs (xs i)).2.2 (use i)
    obtain ⟨k,eq⟩ := Finset.card_eq_one.mp (le_antisymm one (Finset.card_pos.mpr ⟨_,mem⟩))
    refine ⟨k,fun t ht => ?_⟩
    have ht' := ((hs (xs i)).1 t.1).mpr ⟨t.2,ht⟩
    simpa [eq] using ht'
  choose f hf using single
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    exact conflict_distinct hM (cl i j ne) (f i) (hf i) (fun s ht => (hf j s ht).trans eq.symm)
  have bad := Fintype.card_le_of_injective f inj
  simp at bad
def flipSide (e b : Bool) : Bool := if e then !b else b
lemma flip_twice (e b : Bool) : flipSide e (flipSide e b) = b := by cases e <;> cases b <;> rfl
def relabel (pos : Feature → Slot → Prop) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool)
    (z : Feature) (s : Slot) : Prop := pos z (π s.1,flipSide (sw s.1) s.2)
lemma cap_relabel {A B : Finset V} {pos : Feature → Slot → Prop}
    (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : capacity A B pos) :
    capacity A B (relabel pos π sw) := by
  intro v
  obtain ⟨S,he,le,one⟩ := h v
  refine ⟨S.map π.symm.toEmbedding,?_,by simpa using le,fun hv => by simpa using one hv⟩
  intro k
  simp only [Finset.mem_map_equiv,Equiv.symm_symm]
  rw [he]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨flipSide (sw k) b,by simpa only [relabel,flip_twice] using hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨flipSide (sw k) b,hb⟩
def apartRows (A B : Finset V) (r s : Fin 15) : Prop :=
  ∃ U, point U ∧ ∀ z, present A B U z → present A B (rows r) z ∨ present A B (rows s) z
def rooted (A B : Finset V) (P : Feature → Slot → Prop) (O : Fin 5 → Prop)
    (R : Slot → Fin 5 → Prop) (M : Fin 15 → Slot → Prop) : Prop :=
    (∀ r k b d, M r (k,b) → M r (k,d) → b = d) ∧
    (∀ r s z, M r s → P z s → ¬ present A B (rows r) z) ∧
    (∀ r s j, M r s → R s j → ∃ b, M r (j,b)) ∧
    (∀ r k, O k → ∃ b, M r (k,b)) ∧
    ∀ U, point U → ∀ a : Fin 5 → Prop,
      (∀ k, (∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
        ∃ j, R (k,b) j ∧ a j) → a k) → ∃ k, O k ∧ a k
lemma apart_cut {A B P O R M} (h : rooted A B P O R M) {r s : Fin 15}
    (apt : apartRows A B r s) : ∃ k b, M r (k,b) ∧ M s (k,!b) := by
  classical
  obtain ⟨_,avoid,refs,out,pos⟩ := h
  obtain ⟨U,hU,sub⟩ := apt
  by_contra noCross
  let a (k : Fin 5) := ¬((∃ b, M r (k,b)) ∧ (∃ b, M s (k,b)))
  have step (k : Fin 5) (both : ∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
      ∃ j, R (k,b) j ∧ a j) : a k := by
    rintro ⟨⟨b,hr⟩,⟨d,hs⟩⟩
    have e : d = b := by
      by_contra ne
      have ee : d = !b := (show ∀ x y : Bool, x ≠ y → x = !y by decide) _ _ ne
      exact noCross ⟨k,b,hr,ee ▸ hs⟩
    subst d
    rcases both b with ⟨z,pz,pr⟩ | ⟨j,rd,act⟩
    · rcases sub z pr with hit | hit
      · exact avoid r _ z hr pz hit
      · exact avoid s _ z hs pz hit
    · exact act ⟨refs r _ j hr rd,refs s _ j hs rd⟩
  obtain ⟨k,hk,act⟩ := pos U hU a step
  exact act ⟨out r k hk,out s k hk⟩
lemma row_gap : ∀ r s : Fin 15, r ≠ s → ∃ v ∈ rows s, v ∉ rows r := by decide +kernel
lemma hot_apart {A B : Finset V} {r s : Fin 15} (ne : r ≠ s) (hr : present A B (rows r) none) :
    apartRows A B r s := by
  obtain ⟨v,hs,hn⟩ := row_gap r s ne
  refine ⟨insert v (rows r),⟨r,v,hn,rfl⟩,?_⟩
  rintro ( _ | w ) hz
  · exact Or.inl hr
  · rcases Finset.mem_insert.mp hz with eq | mem
    · exact Or.inr (eq ▸ hs)
    · exact Or.inl mem
lemma idle_capacity {A B P O R M} (h : rooted A B P O R M) (T : Finset (Fin 15))
    (hot : ∀ r ∈ T, present A B (rows r) none) (S : Finset (Fin 5))
    (idle : ∀ k, k ∈ S ↔ ∀ b, ¬P none (k,b)) : T.card ≤ 2 ^ S.card := by
  classical
  let code (r : ↥T) (k : ↥S) := decide (M r.val (k.val,true))
  have inj : Function.Injective code := by
    intro r s eq
    by_contra ne
    have diff : r.val ≠ s.val := fun e => ne (Subtype.ext e)
    obtain ⟨k,b,mr,ms⟩ := apart_cut h (hot_apart diff (hot _ r.property))
    have hn (c : Bool) : ¬ P none (k,c) := by
      intro mem
      by_cases same : c = b
      · exact h.2.1 r.val _ none mr (same ▸ mem) (hot _ r.property)
      · have other : c = !b := (show ∀ x y : Bool, x ≠ y → x = !y by decide) _ _ same
        exact h.2.1 s.val _ none ms (other ▸ mem) (hot _ s.property)
    let i : ↥S := ⟨k,(idle k).mpr hn⟩
    have he := congrFun eq i
    change decide (M r.val (k,true)) = decide (M s.val (k,true)) at he
    have link := decide_eq_decide.mp he
    cases b with
    | false =>
      have both := h.1 r.val k false true mr (link.mpr ms)
      contradiction
    | true =>
      have both := h.1 s.val k true false (link.mp mr) ms
      contradiction
  have hc := Fintype.card_le_of_injective code inj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool] using hc
def vectorBits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => vectorBits f n ||| (if f n then 2^n else 0)
lemma vectorBits_bit (f : ℕ → Bool) (n i : ℕ) :
    (vectorBits f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [vectorBits]
  | succ n ih =>
    rw [vectorBits,Nat.testBit_or,ih]
    by_cases e : i = n
    · subst i
      cases hf : f n <;> simp [hf,Nat.testBit_two_pow]
    · by_cases lt : i < n
      · have le : i < n+1 := by omega
        cases hf : f n <;> simp [hf,lt,le,Nat.testBit_two_pow,e,Ne.symm e]
      · have ge : ¬i < n+1 := by omega
        cases hf : f n <;> simp [hf,lt,ge,Nat.testBit_two_pow,e,Ne.symm e]
lemma vectorBits_lt (f : ℕ → Bool) (n : ℕ) : vectorBits f n < 2^n := by
  by_contra! he
  obtain ⟨i,hi,ht⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow he
  simp [vectorBits_bit, Nat.not_lt_of_ge hi] at ht
def slotNum (s : Slot) : ℕ := 2*s.1.val+s.2.toNat
def readSlot (i : ℕ) : Slot := (⟨(i/2) % 5,by omega⟩,decide (i % 2=1))
lemma flipSlotNum : ∀ s : Slot, readSlot (slotNum s) = s := by decide +kernel
lemma slotNum_lt : ∀ s : Slot, slotNum s < 10 := by decide +kernel
lemma readSlotNum : ∀ i : Fin 10, slotNum (readSlot i.val) = i.val := by decide +kernel
noncomputable def word (P : Slot → Prop) : Fin 1024 :=
  ⟨vectorBits (fun i => @decide (P (readSlot i)) (Classical.propDecidable _)) 10,
    vectorBits_lt _ 10⟩
lemma word_spec (P : Slot → Prop) (s : Slot) : (word P).val.testBit (slotNum s) = true ↔ P s := by
  simp [word,vectorBits_bit,slotNum_lt,flipSlotNum]
def fsCode (m : ℕ) : Finset V := Finset.univ.filter fun v => m.testBit v.val
def fsWord (S : Finset V) : Fin 1024 :=
  ⟨vectorBits (fun i => decide (⟨i % 10,by omega⟩ ∈ S)) 10, vectorBits_lt _ 10⟩
lemma fsRound (S : Finset V) : fsCode (fsWord S).val = S := by
  ext v
  simp [fsCode,fsWord,vectorBits_bit,V,v.isLt,Nat.mod_eq_of_lt v.isLt]
def overlaps (x y : ℕ) : Bool := (x &&& y) != 0
lemma overlaps_bit {x y i : ℕ} (a : x.testBit i = true) (b : y.testBit i = true) : overlaps x y = true := by
  apply bne_iff_ne.mpr
  intro eq
  have h := congrArg (fun n : ℕ => n.testBit i) eq
  simp [Nat.testBit_and,a,b] at h
def featureNum : Feature → ℕ
  | none => 10
  | some v => v.val
def atFeature (i : ℕ) : Feature := if i < 10 then some ⟨i % 10,by omega⟩ else none
lemma feature_inv : ∀ z : Feature, atFeature (featureNum z) = z := by decide +kernel
def allWords : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def col0 : ℕ := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def ncol0 : ℕ := 0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
def col1 : ℕ := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def ncol1 : ℕ := 0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333
def col2 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def ncol2 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def col3 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def ncol3 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def col4 : ℕ := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def ncol4 : ℕ := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def col5 : ℕ := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def ncol5 : ℕ := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def col6 : ℕ := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def ncol6 : ℕ := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff
def col7 : ℕ := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def ncol7 : ℕ := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff
def col8 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def ncol8 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def col9 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def ncol9 : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def column (k : ℕ) : ℕ :=
  if k < 5 then if k < 2 then if k < 1 then col0 else col1 else if k < 3 then col2 else if k < 4 then col3 else col4 else if k < 7 then if k < 6 then col5 else col6 else if k < 8 then col7 else if k < 9 then col8 else col9
def included (x y : ℕ) : Prop := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 10000 in
lemma column_ok : ∀ m : Fin 1024, ∀ i : Fin 10,
    (column i.val).testBit m.val = m.val.testBit i.val := by
  intro m i
  have all : preScan (fun j => preScan (fun n => (Nat.testBit (column j) n == Nat.testBit n j)) 1024) 10 = true := by decide +kernel
  exact beq_iff_eq.mp (preScan_at (preScan_at all i.isLt) m.isLt)
set_option maxRecDepth 10000 in
lemma allWords_bit : ∀ m : Fin 1024, allWords.testBit m.val = true := by
  intro m
  change (2^1024-1 : ℕ).testBit m.val = true
  simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq] using m.isLt
lemma singleton_sub {D u : ℕ} (h : D.testBit u = true) : included (2^u) D := by
  intro i hi
  simp only [Nat.testBit_two_pow,decide_eq_true_eq] at hi
  simpa [hi] using h
def signedColumn (up : Bool) (i : ℕ) := if up then column i else allWords ^^^ column i
def upperSet (m : ℕ) (up : Bool) : ℕ :=
  (List.range 10).foldl (fun d i => if m.testBit i == up then d &&& signedColumn up i else d) allWords
def orderWords (up : Bool) (x y : Fin 1024) : Prop :=
  ∀ i : Fin 10, x.val.testBit i.val = up → y.val.testBit i.val = up
lemma upperSet_bit {m y : Fin 1024} (up : Bool) (h : orderWords up m y) :
    (upperSet m.val up).testBit y.val = true := by
  have loop (xs : List ℕ) (bd : ∀ i ∈ xs, i < 10) (d : ℕ) (hd : d.testBit y.val = true) :
      (xs.foldl (fun a i => if m.val.testBit i == up then a &&& signedColumn up i else a) d).testBit y.val = true := by
    induction xs generalizing d with
    | nil => exact hd
    | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih (fun j hj => bd j (by simp [hj]))
      split
      · rename_i eq
        rw [Nat.testBit_and,hd,Bool.true_and]
        have k : i < 10 := bd i (by simp)
        have he := h ⟨i,k⟩ (beq_iff_eq.mp eq)
        have hc : (column i).testBit y.val = y.val.testBit i := column_ok y ⟨i,k⟩
        cases up <;> simp [signedColumn,Nat.testBit_xor,allWords_bit,hc,he]
      · exact hd
  exact loop _ (by simpa using fun (i : ℕ) (h : i < 10) => h) allWords (allWords_bit y)
def growStep (up : Bool) (i d : ℕ) : ℕ :=
  if up then d ||| ((d &&& signedColumn false i) <<< (2^i))
  else d ||| ((d &&& column i) >>> (2^i))
def grow (up : Bool) (d : ℕ) := (List.range 10).foldl (fun a i => growStep up i a) d
lemma grow_mono {x y : ℕ} (up : Bool) (h : included x y) : included (grow up x) (grow up y) := by
  have step (i x y : ℕ) (le : included x y) : included (growStep up i x) (growStep up i y) := by
    intro j hj
    cases up <;> simp only [growStep,Bool.false_eq_true,↓reduceIte,Nat.testBit_or,
      Nat.testBit_shiftRight,Nat.testBit_shiftLeft,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at hj ⊢
    · exact hj.imp (le _) (fun v => ⟨le _ v.1,v.2⟩)
    · exact hj.imp (le _) (fun v => ⟨v.1,le _ v.2.1,v.2.2⟩)
  change included ((List.range 10).foldl _ x) ((List.range 10).foldl _ y)
  generalize List.range 10 = xs
  induction xs generalizing x y with
  | nil => exact h
  | cons i xs ih => exact ih (step _ _ _ h)
set_option maxRecDepth 10000 in
def prePickUp (v i d m : ℕ) : ℕ :=
  match v.testBit i with | true => Nat.land d m | false => d
def prePickDown (v i d m : ℕ) : ℕ :=
  match v.testBit i with | false => Nat.land d m | true => d
def preUpperStep (up : Bool) (v d i : ℕ) :=
  match up with
  | true => prePickUp v i d (column i)
  | false => prePickDown v i d (Nat.xor allWords (column i))
lemma preUpper_eq (up : Bool) (v : ℕ) : upperSet v up =
    (List.range 10).foldl (preUpperStep up v) allWords := by
  unfold upperSet
  congr 1
  funext d i
  cases up <;> cases h : v.testBit i <;> simp [preUpperStep,prePickUp,prePickDown,h,signedColumn]
def preGrowUp (v : ℕ) : ℕ :=
  let d := Nat.shiftLeft 1 v
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol0) 1)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol1) 2)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol2) 4)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol3) 8)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol4) 16)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol5) 32)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol6) 64)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol7) 128)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol8) 256)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol9) 512)
  d
def preUpperUp (v : ℕ) : ℕ :=
  let d := allWords
  let d := prePickUp v 0 d col0
  let d := prePickUp v 1 d col1
  let d := prePickUp v 2 d col2
  let d := prePickUp v 3 d col3
  let d := prePickUp v 4 d col4
  let d := prePickUp v 5 d col5
  let d := prePickUp v 6 d col6
  let d := prePickUp v 7 d col7
  let d := prePickUp v 8 d col8
  let d := prePickUp v 9 d col9
  d
lemma preGrowUp_eq (v : ℕ) : preGrowUp v = grow true (1 <<< v) := by rfl
lemma preUpperUp_eq (v : ℕ) : preUpperUp v = upperSet v true := by rw [preUpper_eq]; rfl
def preGrowDown (v : ℕ) : ℕ :=
  let d := Nat.shiftLeft 1 v
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col0) 1)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col1) 2)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col2) 4)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col3) 8)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col4) 16)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col5) 32)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col6) 64)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col7) 128)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col8) 256)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col9) 512)
  d
def preUpperDown (v : ℕ) : ℕ :=
  let d := allWords
  let d := prePickDown v 0 d ncol0
  let d := prePickDown v 1 d ncol1
  let d := prePickDown v 2 d ncol2
  let d := prePickDown v 3 d ncol3
  let d := prePickDown v 4 d ncol4
  let d := prePickDown v 5 d ncol5
  let d := prePickDown v 6 d ncol6
  let d := prePickDown v 7 d ncol7
  let d := prePickDown v 8 d ncol8
  let d := prePickDown v 9 d ncol9
  d
lemma preGrowDown_eq (v : ℕ) : preGrowDown v = grow false (1 <<< v) := by rfl
lemma preUpperDown_eq (v : ℕ) : preUpperDown v = upperSet v false := by rw [preUpper_eq]; rfl
lemma grow_one : ∀ up : Bool, ∀ m : Fin 1024, grow up (2^m.val) = upperSet m.val up := by
  intro up m
  cases up
  · have all : preScan (fun v => Nat.beq (preGrowDown v) (preUpperDown v)) 1024 = true := by decide +kernel
    simpa only [preGrowDown_eq,preUpperDown_eq,Nat.one_shiftLeft] using Nat.eq_of_beq_eq_true (preScan_at all m.isLt)
  · have all : preScan (fun v => Nat.beq (preGrowUp v) (preUpperUp v)) 1024 = true := by decide +kernel
    simpa only [preGrowUp_eq,preUpperUp_eq,Nat.one_shiftLeft] using Nat.eq_of_beq_eq_true (preScan_at all m.isLt)
lemma grow_contains {up : Bool} {D : ℕ} {x y : Fin 1024}
    (hx : D.testBit x.val = true) (rel : orderWords up x y) : (grow up D).testBit y.val = true := by
  apply grow_mono up (singleton_sub hx) y.val
  rw [grow_one]
  exact upperSet_bit up rel
def holdsWord (d : ℕ) (x : Fin 1024) : Prop := d.testBit x.val = true
def spanBits (d : ℕ) (b : Bool) := vectorBits (fun i => overlaps d (signedColumn b i)) 10
def someBits (m : ℕ) (b : Bool) : ℕ :=
  (List.range 10).foldl (fun d i => if m.testBit i then d ||| signedColumn b i else d) 0
lemma signedColumn_bit (x : Fin 1024) (i : Fin 10) (b : Bool) :
    (signedColumn b i.val).testBit x.val = true ↔ x.val.testBit i.val = b := by
  cases b <;> simp [signedColumn,Nat.testBit_xor,column_ok,allWords_bit]
lemma spanBits_bit {x : Fin 1024} {d : ℕ} {i : Fin 10} {b : Bool}
    (hx : holdsWord d x) (bit : x.val.testBit i.val = b) : (spanBits d b).testBit i.val = true := by
  simp only [spanBits,vectorBits_bit,decide_eq_true i.isLt,Bool.true_and]
  exact overlaps_bit hx ((signedColumn_bit x i b).mpr bit)
lemma someBits_keep {m d : ℕ} {b : Bool} (xs : List ℕ) (x : Fin 1024) (hx : holdsWord d x) :
    holdsWord (xs.foldl (fun q i => if m.testBit i then q ||| signedColumn b i else q) d) x := by
  induction xs generalizing d with
  | nil => exact hx
  | cons i xs ih =>
    apply ih
    change holdsWord (if m.testBit i then d ||| signedColumn b i else d) x
    split
    · change (d ||| signedColumn b i).testBit x.val = true
      simp only [Nat.testBit_or,Bool.or_eq_true]
      exact Or.inl hx
    · exact hx
lemma someBits_bit {m : ℕ} {b : Bool} {x : Fin 1024} {i : Fin 10}
    (mask : m.testBit i.val = true) (bit : x.val.testBit i.val = b) : holdsWord (someBits m b) x := by
  have aux (xs : List ℕ) (d : ℕ) (mem : i.val ∈ xs) :
      holdsWord (xs.foldl (fun q j => if m.testBit j then q ||| signedColumn b j else q) d) x := by
    induction xs generalizing d with
    | nil => simp at mem
    | cons j xs ih =>
      rcases List.mem_cons.mp mem with eq | mem
      · subst j
        simp only [List.foldl_cons,mask,↓reduceIte]
        apply someBits_keep
        change (d ||| signedColumn b i.val).testBit x.val = true
        rw [Nat.testBit_or]
        simp only [Bool.or_eq_true]
        exact Or.inr ((signedColumn_bit x i b).mpr bit)
      · exact ih _ mem
  exact aux _ _ (List.mem_range.mpr i.isLt)
def swapWord (x : ℕ) := ((x &&& 341) <<< 1) ||| ((x >>> 1) &&& 341)
set_option maxRecDepth 10000 in
lemma swapWord_bit : ∀ x : Fin 1024, ∀ s : Slot,
    (swapWord x.val).testBit (slotNum s) = x.val.testBit (slotNum (s.1,!s.2)) := by
  rintro x ⟨k,b⟩
  have m0 : Nat.testBit 341 0 = true := by decide
  have m1 : Nat.testBit 341 1 = false := by decide
  have m2 : Nat.testBit 341 2 = true := by decide
  have m3 : Nat.testBit 341 3 = false := by decide
  have m4 : Nat.testBit 341 4 = true := by decide
  have m5 : Nat.testBit 341 5 = false := by decide
  have m6 : Nat.testBit 341 6 = true := by decide
  have m7 : Nat.testBit 341 7 = false := by decide
  have m8 : Nat.testBit 341 8 = true := by decide
  have m9 : Nat.testBit 341 9 = false := by decide
  fin_cases k <;> cases b <;> simp [swapWord,slotNum,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight,m0,m1,m2,m3,m4,m5,m6,m7,m8,m9]
abbrev Id := Fin 26
abbrev Valuation := Id → Fin 1024
def crossOrKeep (fl : Bool) (s : Slot) : Slot := (s.1,flipSide fl s.2)
lemma flipIndex_twice (fl : Bool) (s : Slot) : crossOrKeep fl (crossOrKeep fl s) = s := by
  cases s
  simp [crossOrKeep,flip_twice]
def twist (fl : Bool) (x : Fin 1024) : ℕ := if fl then swapWord x.val else x.val
lemma twist_bit (fl : Bool) (x : Fin 1024) (s : Slot) :
    (twist fl x).testBit (slotNum s) = x.val.testBit (slotNum (crossOrKeep fl s)) := by
  cases fl <;> simp [twist,crossOrKeep,flipSide,swapWord_bit]
def witnesses (w : Valuation) (vs : List Id) (j : Id) : Prop :=
  ∃ v ∈ vs, ∃ s : Slot, (w v).val.testBit (slotNum s) = true ∧ (w j).val.testBit (slotNum s) = false
def negNumber (i : ℕ) : ℕ :=
  if i < 7 then if i < 3 then if i < 1 then 50 else if i < 2 then 69 else 104 else if i < 5 then if i < 4 then 116 else 138 else if i < 6 then 201 else 208 else if i < 11 then if i < 9 then if i < 8 then 276 else 385 else if i < 10 then 402 else 521 else if i < 13 then if i < 12 then 548 else 554 else if i < 14 then 770 else 773
def posNumber (i : ℕ) : ℕ :=
  if i < 50 then if i < 25 then if i < 12 then if i < 6 then if i < 3 then if i < 1 then 51 else if i < 2 then 54 else 58 else if i < 4 then 71 else if i < 5 then 77 else 85 else if i < 9 then if i < 7 then 101 else if i < 8 then 105 else 106 else if i < 10 then 108 else if i < 11 then 114 else 117 else if i < 18 then if i < 15 then if i < 13 then 118 else if i < 14 then 120 else 124 else if i < 16 then 139 else if i < 17 then 142 else 154 else if i < 21 then if i < 19 then 170 else if i < 20 then 178 else 197 else if i < 23 then if i < 22 then 202 else 203 else if i < 24 then 205 else 209 else if i < 37 then if i < 31 then if i < 28 then if i < 26 then 210 else if i < 27 then 212 else 216 else if i < 29 then 217 else if i < 30 then 232 else 233 else if i < 34 then if i < 32 then 240 else if i < 33 then 244 else 277 else if i < 35 then 278 else if i < 36 then 284 else 306 else if i < 43 then if i < 40 then if i < 38 then 308 else if i < 39 then 325 else 340 else if i < 41 then 360 else if i < 42 then 372 else 387 else if i < 46 then if i < 44 then 389 else if i < 45 then 393 else 394 else if i < 48 then if i < 47 then 401 else 403 else if i < 49 then 404 else 406 else if i < 75 then if i < 62 then if i < 56 then if i < 53 then if i < 51 then 410 else if i < 52 then 417 else 434 else if i < 54 then 449 else if i < 55 then 457 else 464 else if i < 59 then if i < 57 then 466 else if i < 58 then 523 else 525 else if i < 60 then 537 else if i < 61 then 549 else 550 else if i < 68 then if i < 65 then if i < 63 then 553 else if i < 64 then 555 else 556 else if i < 66 then 558 else if i < 67 then 562 else 564 else if i < 71 then if i < 69 then 570 else if i < 70 then 581 else 585 else if i < 73 then if i < 72 then 612 else 616 else if i < 74 then 618 else 628 else if i < 87 then if i < 81 then if i < 78 then if i < 76 then 649 else if i < 77 then 650 else 676 else if i < 79 then 682 else if i < 80 then 713 else 720 else if i < 84 then if i < 82 then 771 else if i < 83 then 774 else 775 else if i < 85 then 777 else if i < 86 then 778 else 781 else if i < 93 then if i < 90 then if i < 88 then 786 else if i < 89 then 788 else 789 else if i < 91 then 802 else if i < 92 then 804 else 805 else if i < 96 then if i < 94 then 810 else if i < 95 then 834 else 837 else if i < 98 then if i < 97 then 897 else 898 else if i < 99 then 901 else 914
abbrev FeatureId := Fin 11
abbrev PositiveId := Fin 100
def featureOf (z : FeatureId) : Feature := atFeature z.val
def fid (z : Feature) : FeatureId := ⟨featureNum z,by cases z <;> simp [featureNum]; omega⟩
def primal (v : FeatureId) : Id := Fin.castLE (by decide) v
def dual (r : Fin 15) : Id := ⟨11+r.val,by omega⟩
def liftRow (r : Fin 15) : Fin 1024 := ⟨negNumber r.val,by revert r; decide +kernel⟩
def liftPoint (u : PositiveId) : Fin 1024 := ⟨posNumber u.val,by revert u; decide +kernel⟩
lemma featureOf_inv (z : Feature) : featureOf (fid z) = z := feature_inv z
set_option maxRecDepth 10000 in
lemma negNumber_spec : ∀ r : Fin 15, fsCode (liftRow r).val = rows r := by decide +kernel
def origin (u : PositiveId) : Fin 15 × V :=
  let n := liftPoint u
  ((List.finRange 15).flatMap (fun r => (List.finRange 10).map fun v => (r,v))).find?
    (fun p => !(liftRow p.1).val.testBit p.2.val && ((liftRow p.1).val ||| 2^p.2.val == n.val))
    |>.getD (0,0)
set_option maxRecDepth 10000 in
lemma origin_spec : ∀ u : PositiveId, (origin u).2 ∉ rows (origin u).1 ∧
    fsCode (liftPoint u).val = insert (origin u).2 (rows (origin u).1) := by decide +kernel
lemma posNumber_spec (u : PositiveId) : point (fsCode (liftPoint u).val) :=
  ⟨(origin u).1,(origin u).2,(origin_spec u).1,(origin_spec u).2⟩
noncomputable def wordAt (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (i : Id) : Fin 1024 :=
  if h : i.val < 11 then word (P (featureOf ⟨i.val,h⟩)) else
    word (fun s => ¬ M ⟨i.val-11,by omega⟩ s)
lemma primal_word (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (z : FeatureId) (s : Slot) :
    (wordAt P M (primal z)).val.testBit (slotNum s) = true ↔ P (featureOf z) s := by
  change (wordAt P M ⟨z.val,_⟩).val.testBit (slotNum s) = true ↔ _
  simpa only [wordAt,dif_pos z.isLt] using word_spec (P (featureOf z)) s
lemma dual_word (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (r : Fin 15) (s : Slot) :
    (wordAt P M (dual r)).val.testBit (slotNum s) = false ↔ M r s := by
  classical
  have addr : wordAt P M (dual r) = word (fun q => ¬M r q) := by
    unfold wordAt
    split
    · rename_i eq
      simp [dual] at eq
    · congr 1
      funext q
      congr 2
      apply Fin.ext
      dsimp [dual]
      omega
  rw [addr,Bool.eq_false_iff]
  exact (not_congr (word_spec (fun q => ¬M r q) s)).trans not_not
def encLayout (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (w : Valuation)
    (O : Fin 5 → Prop) (R : Slot → Fin 5 → Prop) : Prop :=
  (∀ r k b d, (w (dual r)).val.testBit (slotNum (k,b)) = false →
    (w (dual r)).val.testBit (slotNum (k,d)) = false → b = d) ∧
  (∀ r k z, (neg r).testBit z.val = true → (w (primal z)).val.testBit (slotNum k) = true →
    (w (dual r)).val.testBit (slotNum k) = true) ∧
  (∀ r s k, (w (dual r)).val.testBit (slotNum s) = false → R s k →
    ∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
  (∀ r k, O k → ∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
  ∀ u : PositiveId, ∀ a : Fin 5 → Prop,
    (∀ k, (∀ b, (∃ z : FeatureId, (pos u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ a j) → a k) →
    ∃ k, O k ∧ a k
lemma frame_of_rooted {A B P O R M} (h : rooted A B P O R M) (neg : Fin 15 → ℕ)
    (pos : PositiveId → ℕ) (hn : ∀ r z, (neg r).testBit z.val = true → present A B (rows r) (featureOf z))
    (hp : ∀ u z, present A B (fsCode (liftPoint u).val) z → (pos u).testBit (fid z).val = true) :
    encLayout neg pos (wordAt P M) O R := by
  obtain ⟨uniq,avoid,closed,out,positive⟩ := h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r k b d l rr
    exact uniq r k b d ((dual_word ..).mp l) ((dual_word ..).mp rr)
  · intro r k z hv hw
    cases e : (wordAt P M (dual r)).val.testBit (slotNum k) with
    | true => rfl
    | false => exact (avoid r k (featureOf z) ((dual_word ..).mp e) ((primal_word ..).mp hw) (hn r z hv)).elim
  · intro r s k mem ref
    obtain ⟨b,sel⟩ := closed r s k ((dual_word ..).mp mem) ref
    exact ⟨b,(dual_word ..).mpr sel⟩
  · intro r k hk
    obtain ⟨b,mem⟩ := out r k hk
    exact ⟨b,(dual_word ..).mpr mem⟩
  · intro u a cl
    apply positive _ (posNumber_spec u) a
    intro k both
    apply cl k
    intro b
    rcases both b with ⟨z,hz,pr⟩ | ref
    · exact Or.inl ⟨fid z,hp u z pr,(primal_word P M (fid z) _).mpr (by simpa only [featureOf_inv] using hz)⟩
    · exact Or.inr ref
lemma frame_hit {n p w O R} (h : encLayout n p w O R) (r : Fin 15) (u : PositiveId)
    (xs : List Id) (includedVars : ∀ z : FeatureId, (p u).testBit z.val = true →
      (n r).testBit z.val = false → primal z ∈ xs) : witnesses w xs (dual r) := by
  classical
  let a (k : Fin 5) := ∀ b, (w (dual r)).val.testBit (slotNum (k,b)) = true
  by_contra nf
  have step (k) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ a j) : a k := by
    intro b
    cases e : (w (dual r)).val.testBit (slotNum (k,b)) with
    | true => rfl
    | false =>
      rcases both b with ⟨z,hz,pz⟩ | ⟨j,ref,on⟩
      · cases present : (n r).testBit z.val with
        | true => have contra := h.2.1 r _ z present pz; simp [e] at contra
        | false => exact (nf ⟨_,includedVars z hz present,_,pz,e⟩).elim
      · obtain ⟨s,hs⟩ := h.2.2.1 r _ _ e ref
        have contra := on s
        simp [hs] at contra
  obtain ⟨k,out,on⟩ := h.2.2.2.2 u a step
  obtain ⟨b,absent⟩ := h.2.2.2.1 r k out
  have x := on b
  simp [absent] at x
lemma enc_sub {n p w O R} (h : encLayout n p w O R) {r : Fin 15} {z : FeatureId}
    (hz : (n r).testBit z.val = true) : orderWords true (w (primal z)) (w (dual r)) := by
  intro i
  simpa only [readSlotNum i] using h.2.1 r (readSlot i.val) z hz
lemma enc_cross {n p w O R} (h : encLayout n p w O R) {r s : Fin 15} {u : PositiveId}
    (sub : ∀ z : FeatureId, (p u).testBit z.val = true →
      (n r).testBit z.val = true ∨ (n s).testBit z.val = true) :
    ∃ q : Slot, (w (dual r)).val.testBit (slotNum q) = false ∧
      (w (dual s)).val.testBit (slotNum (crossOrKeep true q)) = false := by
  classical
  by_contra missing
  let active (k : Fin 5) := ¬((∃ b, (w (dual r)).val.testBit (slotNum (k,b)) = false) ∧
                             (∃ b, (w (dual s)).val.testBit (slotNum (k,b)) = false))
  have step (k) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ active j) : active k := by
    rintro ⟨⟨b,hb⟩,⟨d,hd⟩⟩
    have e : d = b := by
      by_contra ne
      have other : d = !b := (show ∀ x y : Bool, x ≠ y → x = !y by decide) _ _ ne
      exact missing ⟨(k,b),hb,by simpa only [crossOrKeep,flipSide,↓reduceIte,other] using hd⟩
    subst d
    rcases both b with ⟨z,hz,pz⟩ | ⟨j,ref,act⟩
    · rcases sub z hz with rr | ss
      · have hit := h.2.1 r _ _ rr pz
        simp [hb] at hit
      · have hit := h.2.1 s _ _ ss pz
        simp [hd] at hit
    · exact act ⟨h.2.2.1 r _ j hb ref,h.2.2.1 s _ j hd ref⟩
  obtain ⟨k,out,act⟩ := h.2.2.2.2 u active step
  exact act ⟨h.2.2.2.1 r k out,h.2.2.2.1 s k out⟩
def gateWord (f : Fin 5 → Bool) := vectorBits (fun k => f ⟨k % 5,by omega⟩) 5
lemma gateWord_bit (f : Fin 5 → Bool) (k : Fin 5) : (gateWord f).testBit k.val = f k := by
  simp [gateWord,vectorBits_bit,k.isLt,Nat.mod_eq_of_lt k.isLt]
abbrev Marks := Fin 26 → Fin 5 → Bool → Bool
def turn (s b : Bool) := if s then !b else b
def moved (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) : Marks :=
  fun z k b => m z (π k) (turn (s k) b)
def digit (m : Marks) (z : Fin 26) (k : Fin 5) (s : Bool) : ℕ :=
  (m z k (turn s false)).toNat + 2 * (m z k (turn s true)).toNat
def history (m : Marks) (k : Fin 5) (s : Bool) : List (Fin 26) → ℕ
  | [] => 0
  | z::xs => digit m z k s + 4 * history m k s xs
lemma digit_bound (m : Marks) (z : Fin 26) (k : Fin 5) (s : Bool) : digit m z k s < 4 := by
  unfold digit
  cases m z k (turn s false) <;> cases m z k (turn s true) <;> decide
lemma history_div (m : Marks) (k : Fin 5) (s : Bool) (z : Fin 26) (xs : List (Fin 26)) :
    history m k s (z::xs) / 4 = history m k s xs := by
  simp only [history]
  have := digit_bound m z k s
  omega
def ordered (m : Marks) (xs : List (Fin 26)) : Prop :=
  (∀ k, history m k false xs ≤ history m k true xs) ∧ Monotone (fun k => history m k false xs)
lemma tail_ordered {m : Marks} {z xs} (h : ordered m (z::xs)) : ordered m xs := by
  exact ⟨fun k => by simpa only [history_div] using Nat.div_le_div_right (c := 4) (h.1 k),
    fun _ _ hle => by simpa only [history_div] using Nat.div_le_div_right (c := 4) (h.2 hle)⟩
lemma history_moved (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool)
    (k : Fin 5) (b : Bool) (xs : List (Fin 26)) :
    history (moved m π s) k b xs = history m (π k) (turn (s k) b) xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [history, ih]
    congr 1
    unfold digit moved
    cases e : s k <;> cases b <;> simp [turn]
lemma make_ordered (m : Marks) (xs : List (Fin 26)) :
    ∃ (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool), ordered (moved m π s) xs := by
  let s k := decide (history m k true xs < history m k false xs)
  let key k := history m k (s k) xs
  let π := Tuple.sort key
  refine ⟨π,fun k => s (π k),?_,?_⟩
  · intro k
    rw [history_moved,history_moved]
    by_cases lt : history m (π k) true xs < history m (π k) false xs
    · simpa [s,turn,lt] using lt.le
    · simpa [s,turn,lt] using Nat.le_of_not_gt lt
  · intro i j hij
    change history _ i false xs ≤ history _ j false xs
    rw [history_moved,history_moved]
    have hf (b : Bool) : turn b false = b := by cases b <;> rfl
    simp only [hf]
    exact Tuple.monotone_sort key hij
lemma history_min (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool) (k : Fin 5)
    (xs : List (Fin 26)) (h : ordered m xs) (g : ordered (moved m π s) xs) :
    history (moved m π s) k false xs = history m (π k) false xs := by
  have le := h.1 (π k)
  have rev := g.1 k
  rw [history_moved,history_moved] at rev
  rw [history_moved]
  cases e : s k <;> simp [turn,e] at rev ⊢
  exact le_antisymm rev le
lemma history_unique (m : Marks) (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool)
    (xs : List (Fin 26)) (h : ordered m xs) (g : ordered (moved m π s) xs) (k : Fin 5) :
    history (moved m π s) k false xs = history m k false xs := by
  let f k := history m k false xs
  have changed (j) := history_min m π s j xs h g
  have mp : Monotone (f ∘ π) := by
    intro i j hij
    change history m (π i) false xs ≤ history m (π j) false xs
    rw [←changed i,←changed j]
    exact g.2 hij
  have idm : Monotone (f ∘ Equiv.refl _) := h.2
  exact (changed k).trans (congrFun (Tuple.unique_monotone mp idm) k)
lemma history_reads {m m' : Marks} {k : Fin 5} {xs : List (Fin 26)}
    (eq : history m k false xs = history m' k false xs) :
    ∀ z ∈ xs, ∀ b, m z k b = m' z k b := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    have tail := congrArg (fun n : ℕ => n / 4) eq
    simp only [history_div] at tail
    have eqd : digit m v k false = digit m' v k false := by
      simp only [history,tail] at eq
      omega
    intro z mem b
    rcases List.mem_cons.mp mem with rfl | rest
    · unfold digit at eqd
      simp only [turn,Bool.false_eq_true,↓reduceIte] at eqd
      have both := (show ∀ a c d e : Bool, a.toNat+2*c.toNat = d.toNat+2*e.toNat →
          a=d ∧ c=e by decide) _ _ _ _ eqd
      cases b
      · exact both.1
      · exact both.2
    · exact ih tail z rest b
lemma extend_ordered {m : Marks} {xs} (h : ordered m xs) (z : Fin 26) :
    ∃ (π : Equiv.Perm (Fin 5)) (s : Fin 5 → Bool),
      ordered (moved m π s) (z::xs) ∧ ∀ v ∈ xs, ∀ k b, moved m π s v k b = m v k b := by
  obtain ⟨π,s,hnew⟩ := make_ordered m (z::xs)
  refine ⟨π,s,hnew,fun v hv k b => ?_⟩
  exact history_reads (history_unique m π s xs h (tail_ordered hnew) k) v hv b
def rawNumber (m : Marks) (i : Id) : Fin 1024 :=
  ⟨vectorBits (fun j => m i (readSlot j).1 (readSlot j).2) 10, vectorBits_lt _ 10⟩
def represented (m : Marks) (i : Id) : Fin 1024 :=
  if i.val < 11 then rawNumber m i else ⟨1023-(rawNumber m i).val,by omega⟩
lemma rawNumber_bit (m : Marks) (i : Id) (k : Fin 5) (b : Bool) :
    (rawNumber m i).val.testBit (slotNum (k,b)) = m i k b := by
  simp [rawNumber,vectorBits_bit,slotNum_lt,flipSlotNum]
def rawFrom (i : Id) (v : Fin 1024) : ℕ := if i.val < 11 then v.val else 1023-v.val
lemma rawFrom_rep (m : Marks) (i : Id) : rawFrom i (represented m i) = (rawNumber m i).val := by
  have := (rawNumber m i).isLt
  by_cases h : i.val < 11 <;> simp [rawFrom,represented,h] <;> omega
def pairDigit (x : ℕ) (k : Fin 5) := (x >>> (2*k.val)) % 4
set_option maxRecDepth 10000 in
lemma pairDigit_bits : ∀ x : Fin 1024, ∀ k : Fin 5, pairDigit x.val k =
    (x.val.testBit (slotNum (k,false))).toNat + 2*(x.val.testBit (slotNum (k,true))).toNat := by
  intro x k
  let y := x.val >>> (2*k.val)
  have l : y.testBit 0 = x.val.testBit (slotNum (k,false)) := by simp [y,slotNum]
  have r : y.testBit 1 = x.val.testBit (slotNum (k,true)) := by simp [y,slotNum]
  rw [← l,← r,Nat.toNat_testBit,Nat.toNat_testBit]
  change y % 4 = y / 1 % 2 + 2*(y/2 % 2)
  omega
lemma digit_raw (m : Marks) (i : Id) (k : Fin 5) :
    pairDigit (rawNumber m i).val k = digit m i k false := by
  rw [pairDigit_bits,rawNumber_bit,rawNumber_bit]
  rfl
lemma digit_swap (m : Marks) (i : Id) (k : Fin 5) :
    (digit m i k false ≤ digit m i k true ↔ digit m i k false ≠ 2) ∧
    (digit m i k false = digit m i k true ↔ digit m i k false = 0 ∨ digit m i k false = 3) := by
  simp only [digit,turn,Bool.false_eq_true,Bool.not_false,Bool.not_true,↓reduceIte]
  cases m i k false <;> cases m i k true <;> decide
def prevGate (k : Fin 5) : Fin 5 := ⟨k.val-1,by omega⟩
def flagsMatch (m : Marks) (xs : List Id) (eq fl : ℕ) : Prop :=
  (∀ k : Fin 5, eq.testBit k.val = true → history m (prevGate k) false xs = history m k false xs) ∧
  (∀ k : Fin 5, fl.testBit k.val = true → history m k false xs = history m k true xs)
lemma flags_nil (m : Marks) : flagsMatch m [] 30 31 := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
def acceptMark (eq fl x : ℕ) : Prop := ∀ k : Fin 5,
  (fl.testBit k.val = true → pairDigit x k ≠ 2) ∧
  (eq.testBit k.val = true → pairDigit x (prevGate k) ≤ pairDigit x k)
lemma accepted_order {m : Marks} {xs eq fl i} (s : flagsMatch m xs eq fl) (h : ordered m (i::xs)) :
    acceptMark eq fl (rawNumber m i).val := by
  intro k
  constructor
  · intro free
    rw [digit_raw]
    apply (digit_swap m i k).1.mp
    have le := h.1 k
    simp only [history,s.2 k free] at le
    omega
  · intro tie
    rw [digit_raw,digit_raw]
    have hle : prevGate k ≤ k := by change k.val-1 ≤ k.val; omega
    have le := h.2 hle
    change digit m i (prevGate k) false + 4*history m (prevGate k) false xs ≤
      digit m i k false + 4*history m k false xs at le
    rw [s.1 k tie] at le
    omega
def sameMark (x : ℕ) := gateWord fun k => pairDigit x k == pairDigit x (prevGate k)
def freeMark (x : ℕ) := gateWord fun k => pairDigit x k == 0 || pairDigit x k == 3
lemma advance_flags {m : Marks} {xs eq fl i} (s : flagsMatch m xs eq fl) :
    flagsMatch m (i::xs) (eq &&& sameMark (rawNumber m i).val) (fl &&& freeMark (rawNumber m i).val) := by
  constructor
  · intro k h
    simp only [Nat.testBit_and,sameMark,gateWord_bit,digit_raw,Bool.and_eq_true,beq_iff_eq] at h
    simp only [history,s.1 k h.1,h.2]
  · intro k h
    simp only [Nat.testBit_and,freeMark,gateWord_bit,digit_raw,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
    have e := (digit_swap m i k).2.mpr h.2
    simp only [history,s.2 k h.1,e]
def fixedHistory (hist : List (Id × Fin 1024)) (m : Marks) : Prop :=
  ∀ iv ∈ hist, represented m iv.1 = iv.2
lemma rawNumber_congr {x y : Marks} {i : Id} (eq : ∀ k b, x i k b = y i k b) :
    rawNumber x i = rawNumber y i := by
  apply Fin.ext
  change vectorBits _ 10 = vectorBits _ 10
  congr 1
  funext j
  exact eq _ _
lemma fixed_move {x y : Marks} {hist : List (Id × Fin 1024)} (fixed : fixedHistory hist x)
    (eq : ∀ i ∈ hist.map Prod.fst, ∀ k b, y i k b = x i k b) : fixedHistory hist y := by
  intro iv mem
  have en := rawNumber_congr (eq iv.1 (List.mem_map.mpr ⟨iv,mem,rfl⟩))
  simpa only [represented,en] using fixed iv mem
lemma flags_move {x y : Marks} {hist : List (Id × Fin 1024)} {eq fl}
    (h : flagsMatch x (hist.map Prod.fst) eq fl)
    (same : ∀ i ∈ hist.map Prod.fst, ∀ k b, y i k b = x i k b) : flagsMatch y (hist.map Prod.fst) eq fl := by
  have congH (xs : List Id) (use : ∀ v ∈ xs, v ∈ hist.map Prod.fst) (k : Fin 5) (b : Bool) :
      history y k b xs = history x k b xs := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [history,digit,same i (use i (by simp)),ih (fun v hv => use v (by simp [hv]))]
  exact ⟨fun k hk => by simpa only [congH _ (fun _ hz => hz)] using h.1 k hk,
    fun k hk => by simpa only [congH _ (fun _ hz => hz)] using h.2 k hk⟩
def fieldMask := 2^1024-1
def strideFlags : List Bool → ℕ
  | [] => 0
  | f::fs => 2^1025 * strideFlags fs + f.toNat
lemma scatter_read (xs : List Bool) (d : ℕ) (small : d < 2^1025) (i j : ℕ) (hj : j < 1025) :
    (d * strideFlags xs).testBit (1025*i+j) = ((xs[i]?).getD false && d.testBit j) := by
  induction xs generalizing i with
  | nil => simp [strideFlags]
  | cons f fs ih =>
    have eq : d * strideFlags (f::fs) = 2^1025 * (d * strideFlags fs) + d * f.toNat := by
      simp only [strideFlags,Nat.mul_add]
      ring
    have bd : d * f.toNat < 2^1025 := by cases f <;> simp_all
    rw [eq,Nat.testBit_two_pow_mul_add _ bd]
    cases i with
    | zero => cases f <;> simp [hj]
    | succ i =>
      have ge : ¬ 1025*(i+1)+j < 1025 := by omega
      have diff : 1025*(i+1)+j-1025=1025*i+j := by omega
      simpa only [ge,↓reduceIte,diff,List.getElem?_cons_succ] using ih i
def laneRead (d i : ℕ) := (d >>> (1025*i)) &&& fieldMask
lemma laneRead_bit (d i : ℕ) (v : Fin 1024) :
    (laneRead d i).testBit v.val = d.testBit (1025*i+v.val) := by
  simp only [laneRead,fieldMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,
    decide_eq_true v.isLt,Bool.and_true,Nat.testBit_shiftRight,Nat.add_comm]
def insidePacked (d : ℕ) (w : Fin 26 → Fin 1024) : Prop :=
  ∀ i, d.testBit (1025*i.val+(w i).val) = true
def restrictPacked (d mask : ℕ) := d ^^^ (d &&& mask)
lemma restrictPacked_sound (d mask : ℕ) (w : Fin 26 → Fin 1024)
    (ok : insidePacked d w) (keep : ∀ i, mask.testBit (1025*i.val+(w i).val) = false) :
    insidePacked (restrictPacked d mask) w := by
  intro i
  simp [restrictPacked,Nat.testBit_xor,Nat.testBit_and,ok i,keep i]
lemma scatter_safe (xs : List Bool) (w : Fin 26 → Fin 1024) (filter : ℕ)
    (bound : filter < 2^1025)
    (safe : ∀ i : Fin 26, (xs[i.val]?).getD false = true → filter.testBit (w i).val = false) :
    ∀ i : Fin 26, (filter*strideFlags xs).testBit (1025*i.val+(w i).val) = false := by
  intro i
  rw [scatter_read xs filter bound _ _ (by have := (w i).isLt; omega)]
  cases h : (xs[i.val]?).getD false with
  | false => rfl
  | true => simpa only [Bool.true_and] using safe i h
def replacePacked (d i x : ℕ) := d ^^^ ((laneRead d i ^^^ x) <<< (1025*i))
lemma low_lane (d i : ℕ) : laneRead d i < 2^1024 := by
  exact (Nat.and_le_right (n := d >>> (1025*i)) (m := fieldMask)).trans_lt
    (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
lemma replacePacked_sound {d : ℕ} {w : Fin 26 → Fin 1024} (ok : insidePacked d w) (i : Fin 26) :
    insidePacked (replacePacked d i.val (1 <<< (w i).val)) w := by
  intro j
  let v := (w j).val
  have vlt : v < 1024 := (w j).isLt
  have wi : (w i).val < 1024 := (w i).isLt
  rw [Nat.one_shiftLeft]
  simp only [replacePacked,Nat.testBit_xor,Nat.testBit_shiftLeft,ok j,Bool.true_xor]
  by_cases e : j=i
  · subst j
    have eq : 1025*i.val + (w i).val - 1025*i.val = (w i).val := by omega
    simp [eq,laneRead_bit,ok i,Nat.testBit_two_pow]
  · have ne : j.val ≠ i.val := fun h => e (Fin.ext h)
    by_cases lt : j.val < i.val
    · have no : ¬1025*i.val ≤ 1025*j.val+(w j).val := by omega
      simp [no]
    · have ge : 1024 ≤ 1025*j.val+(w j).val-1025*i.val := by omega
      have pow : 2^1024 ≤ 2^(1025*j.val+(w j).val-1025*i.val) := Nat.pow_le_pow_right (by decide) ge
      have f := Nat.testBit_lt_two_pow ((low_lane d i.val).trans_le pow)
      have nw : (w i).val ≠ 1025*j.val+(w j).val-1025*i.val := by omega
      simp [Nat.testBit_two_pow,f,nw]
lemma heldLane {w : Valuation} {d : ℕ} (ok : insidePacked d w) (i : Id) :
    holdsWord (laneRead d i.val) (w i) := by
  change (laneRead d i.val).testBit (w i).val = true
  rw [laneRead_bit]
  exact ok i
def pairBits (k : Fin 5) : ℕ := 3 <<< (2*k.val)
lemma pairBits_hit : ∀ k : Fin 5, ∀ b : Bool,
    (pairBits k).testBit (slotNum (k,b)) = true := by decide +kernel
def barredRoot (d : ℕ) (r : Fin 15) (k : Fin 5) : Bool :=
  !overlaps (laneRead d (dual r).val) (someBits (pairBits k) false)
def barredArc (d : ℕ) (r : Fin 15) (s : Slot) (k : Fin 5) : Bool :=
  !overlaps (laneRead d (dual r).val) (column (slotNum s) ||| someBits (pairBits k) false)
def barredRaw (d u : ℕ) (s : Slot) : Bool :=
  (List.finRange 11).all fun z =>
    !u.testBit z.val || !overlaps (laneRead d (primal z).val) (column (slotNum s))
lemma barredRoot_sound {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (r : Fin 15) (k : Fin 5) (bad : barredRoot d r k = true) : ¬O k := by
  intro out
  obtain ⟨b,hb⟩ := h.2.2.2.1 r k out
  have somebit := someBits_bit (i := ⟨_,slotNum_lt (k,b)⟩) (pairBits_hit k b) hb
  have no := overlaps_bit (heldLane ok (dual r)) somebit
  simp [barredRoot,no] at bad
lemma barredArc_sound {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (r : Fin 15) (s : Slot) (k : Fin 5) (bad : barredArc d r s k = true) : ¬ R s k := by
  intro ref
  have mem : ((column (slotNum s)) ||| someBits (pairBits k) false).testBit (w (dual r)).val = true := by
    rw [Nat.testBit_or,Bool.or_eq_true]
    cases bit : (w (dual r)).val.testBit (slotNum s) with
    | true => exact Or.inl ((column_ok _ ⟨_,slotNum_lt s⟩).trans bit)
    | false =>
      obtain ⟨b,hb⟩ := h.2.2.1 r s k bit ref
      exact Or.inr (someBits_bit (i := ⟨_,slotNum_lt (k,b)⟩) (pairBits_hit k b) hb)
  have no := overlaps_bit (heldLane ok (dual r)) mem
  simp [barredArc,no] at bad
lemma barredRaw_sound {w : Valuation} {d u : ℕ} (ok : insidePacked d w) {s : Slot}
    (bad : barredRaw d u s = true) (z : FeatureId) (hz : u.testBit z.val = true) :
    (w (primal z)).val.testBit (slotNum s) ≠ true := by
  intro bit
  have no := overlaps_bit (heldLane ok (primal z)) ((column_ok _ ⟨_,slotNum_lt s⟩).trans bit)
  have row := List.all_eq_true.mp bad z (List.mem_finRange z)
  simp [hz,no] at row
def graphLeaf (d u on sw : ℕ) (r : Fin 5 → Fin 5 → Fin 15) : Bool :=
  (List.finRange 5).all fun k =>
    if on.testBit k.val then barredRoot d (r k 0) k else
      let s := (k,sw.testBit k.val)
      barredRaw d u s && (List.finRange 5).all fun j =>
        !on.testBit j.val || barredArc d (r k j) s j
lemma graphLeaf_impossible {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (u : PositiveId) (on sw : ℕ) (r : Fin 5 → Fin 5 → Fin 15) (bad : graphLeaf d (p u) on sw r = true) : False := by
  let active (k : Fin 5) := on.testBit k.val = true
  have checked := List.all_eq_true.mp bad
  have cl (k : Fin 5) (both : ∀ b, (∃ z : FeatureId, (p u).testBit z.val = true ∧
      (w (primal z)).val.testBit (slotNum (k,b)) = true) ∨ ∃ j, R (k,b) j ∧ active j) :
      active k := by
    cases e : on.testBit k.val with
    | true => exact e
    | false =>
      have no := checked k (List.mem_finRange k)
      simp only [e,Bool.false_eq_true,↓reduceIte,Bool.and_eq_true] at no
      rcases both (sw.testBit k.val) with ⟨z,hz,bit⟩ | ⟨j,ref,act⟩
      · exact (barredRaw_sound ok no.1 z hz bit).elim
      · have ar := List.all_eq_true.mp no.2 j (List.mem_finRange j)
        simp only [active] at act
        simp only [act,Bool.not_true,Bool.false_or] at ar
        exact (barredArc_sound h ok _ _ _ ar ref).elim
  obtain ⟨k,out,act⟩ := h.2.2.2.2 u active cl
  have no := checked k (List.mem_finRange k)
  simp only [active] at act
  simp only [act,↓reduceIte] at no
  exact barredRoot_sound h ok _ _ no out
def orientation (i : Id) : Bool := decide (i.val < 11)
def relatedJoin (w : Valuation) (i j : Id) (a b flip : Bool) : Prop :=
  ∃ s : Slot, (w i).val.testBit (slotNum s) = a ∧
    (w j).val.testBit (slotNum (crossOrKeep flip s)) = b
abbrev Link := Fin 3 → Id → Id → Bool
def linkValid (net : Link) (w : Valuation) : Prop :=
  (∀ i j, net 0 i j = true → orderWords (orientation i) (w i) (w j)) ∧
  (∀ i j, net 1 i j = true → relatedJoin w i j (orientation i) (!(orientation i)) false) ∧
  (∀ i j, net 2 i j = true → relatedJoin w i j false false true)
def spread (net : Link) (mode : Fin 3) (i : Id) (mask : ℕ) :=
  (fieldMask &&& (fieldMask ^^^ mask)) * strideFlags (List.ofFn (net mode i))
lemma spread_safe {net : Link} {w : Valuation} {i : Id} {mode : Fin 3} {mask : ℕ}
    (safe : ∀ j : Id, net mode i j = true → mask.testBit (w j).val = true) (j : Id) :
    (spread net mode i mask).testBit (1025*j.val+(w j).val) = false := by
  apply scatter_safe
  · have bd : fieldMask &&& (fieldMask ^^^ mask) ≤ fieldMask := Nat.and_le_left
    have lo : fieldMask < 2^1024 := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    exact (bd.trans_lt lo).trans_le (Nat.pow_le_pow_right (by decide) (by decide : 1024 ≤ 1025))
  · intro q hq
    have edge : net mode i q = true := by simpa only [List.getElem?_ofFn, q.isLt,↓reduceDIte,Option.getD_some] using hq
    have bit := safe _ edge
    simp [fieldMask,Nat.testBit_and,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,(w q).isLt,bit]
def filterOrder (d : ℕ) (i : Id) := grow (orientation i) (laneRead d i.val)
def filterJoin (d : ℕ) (i : Id) (a b fl : Bool) :=
  someBits (if fl then swapWord (spanBits (laneRead d i.val) a) else spanBits (laneRead d i.val) a) b
lemma filterJoin_safe {w : Valuation} {d : ℕ} (ok : insidePacked d w)
    {i j : Id} {a b fl : Bool} (hit : relatedJoin w i j a b fl) :
    (filterJoin d i a b fl).testBit (w j).val = true := by
  obtain ⟨s,hs,ht⟩ := hit
  let t := crossOrKeep fl s
  have same := flipIndex_twice fl s
  let n := spanBits (laneRead d i.val) a
  have hspan : n.testBit (slotNum s) = true := spanBits_bit (i := ⟨_,slotNum_lt s⟩) (heldLane ok i) hs
  have bd : n < 1024 := vectorBits_lt _ 10
  let ns : Fin 1024 := ⟨n,bd⟩
  have tr := twist_bit fl ns t
  change (if fl then swapWord n else n).testBit (slotNum t) = n.testBit (slotNum (crossOrKeep fl t)) at tr
  have val : (if fl then swapWord n else n).testBit (slotNum t) = true := tr.trans (by simpa only [t,same] using hspan)
  exact someBits_bit (i := ⟨_,slotNum_lt t⟩) val ht
def sourceCut (net : Link) (d : ℕ) (i : Id) : ℕ :=
  spread net 0 i (filterOrder d i) ||| spread net 1 i (filterJoin d i (orientation i) (!(orientation i)) false) |||
    spread net 2 i (filterJoin d i false false true)
lemma sourceCut_keep {net : Link} {w : Valuation} {d : ℕ} (ok : insidePacked d w) (v : linkValid net w) (i : Id) :
    insidePacked (restrictPacked d (sourceCut net d i)) w := by
  apply restrictPacked_sound _ _ _ ok
  intro j
  have a (j : Id) (edge : net 0 i j = true) :
      (filterOrder d i).testBit (w j).val = true := grow_contains (heldLane ok i) (v.1 i j edge)
  have b (j : Id) (edge : net 1 i j = true) :
      (filterJoin d i (orientation i) (!(orientation i)) false).testBit (w j).val = true :=
    filterJoin_safe ok (v.2.1 i j edge)
  have c (j : Id) (edge : net 2 i j = true) :
      (filterJoin d i false false true).testBit (w j).val = true := filterJoin_safe ok (v.2.2 i j edge)
  simp only [sourceCut,Nat.testBit_or,spread_safe a j,spread_safe b j,spread_safe c j,Bool.false_or]
def optionsBy (high : ℕ → ℕ) : ℕ → ℕ → Option (List ℕ)
  | 0,x => if x == 0 then some [] else none
  | n+1,x =>
    if x == 0 then some [] else
    let i := high x
    (optionsBy high n (x ^^^ (1 <<< i))).map (i :: ·)
lemma optionsBy_covers {high : ℕ → ℕ} {fuel x : ℕ} {xs : List ℕ}
    (ok : optionsBy high fuel x = some xs) {v : ℕ} (present : x.testBit v = true) : v ∈ xs := by
  induction fuel generalizing x xs with
  | zero => 
    by_cases empty : x = 0
    · simp [empty] at present
    · simp [optionsBy,empty] at ok
  | succ fuel ih =>
    by_cases empty : x = 0
    · simp [empty] at present
    · simp only [optionsBy,beq_iff_eq,empty,↓reduceIte] at ok
      cases h : optionsBy high fuel (x ^^^ (1 <<< high x)) with
      | none => simp [h] at ok
      | some ys =>
        simp only [h,Option.map_some,Option.some.injEq] at ok
        subst xs
        by_cases eq : high x = v
        · simp [eq]
        · apply List.mem_cons_of_mem
          apply ih h
          simp [Nat.one_shiftLeft,Nat.testBit_xor,present,eq]
lemma checkedList {α : Type} (f : ℕ → α → ℕ) (xs : List α) (start : ℕ)
    (pass : xs.foldl (fun t a => if t == 0 then 0 else f t a) start ≠ 0) :
    ∀ a ∈ xs, ∃ t ≠ 0, f t a ≠ 0 := by
  have zero (l : List α) : l.foldl (fun t a => if t == 0 then 0 else f t a) 0 = 0 := by
    induction l with
    | nil => rfl
    | cons a l ih => simpa only [List.foldl_cons,beq_self_eq_true,↓reduceIte] using ih
  induction xs generalizing start with
  | nil => simp
  | cons a l ih =>
    have hs : start ≠ 0 := fun eq => pass (eq ▸ zero _)
    have e : (start == 0) = false := beq_eq_false_iff_ne.mpr hs
    simp only [List.foldl_cons,e,Bool.false_eq_true,↓reduceIte] at pass
    have ha : f start a ≠ 0 := by
      intro eq
      rw [eq,zero] at pass
      exact pass rfl
    intro b hb
    rcases List.mem_cons.mp hb with rfl | m
    · exact ⟨_,hs,ha⟩
    · exact ih _ pass b m
abbrev Trail := List (Id × Fin 1024)
def pathBounds (P : Marks → Prop) (hist : Trail) (d : ℕ) : Prop :=
  ∀ m, P m → fixedHistory hist m → insidePacked d (represented m)
noncomputable def marksFor (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) : Marks := by
  classical
  exact fun i k b => if h : i.val < 11 then decide (P (featureOf ⟨i.val,h⟩) (k,b)) else
    decide (M ⟨i.val-11,by omega⟩ (k,b))
def world (A B : Finset V) (m : Marks) : Prop :=
  ∃ P O R M, capacity A B P ∧ rooted A B P O R M ∧ marksFor P M = m
def rotSlot (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (s : Slot) :=
  (π s.1,flipSide (sw s.1) s.2)
lemma root_changed {A B P O R M} (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : rooted A B P O R M) :
    rooted A B (relabel P π sw) (fun k => O (π k)) (fun s k => R (rotSlot π sw s) (π k))
      (fun r s => M r (rotSlot π sw s)) := by
  obtain ⟨uniq,avoid,closed,out,positive⟩ := h
  let f := rotSlot π sw
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r k b d hb hd
    have eq := uniq r (π k) (flipSide (sw k) b) (flipSide (sw k) d) hb hd
    simpa only [flip_twice] using congrArg (flipSide (sw k)) eq
  · intro r s z hm hp
    exact avoid r (f s) z hm hp
  · intro r s j hm ref
    obtain ⟨b,hb⟩ := closed r _ _ hm ref
    exact ⟨flipSide (sw j) b,by simpa only [f,rotSlot,flip_twice] using hb⟩
  · intro r k hk
    obtain ⟨b,hb⟩ := out r _ hk
    exact ⟨flipSide (sw k) b,by simpa only [f,rotSlot,flip_twice] using hb⟩
  · intro U hu a cl
    let active (k : Fin 5) := a (π.symm k)
    have step (k : Fin 5) (hh : ∀ b, (∃ z, P z (k,b) ∧ present A B U z) ∨
        ∃ j, R (k,b) j ∧ active j) : active k := by
      apply cl (π.symm k)
      intro b
      rcases hh (flipSide (sw (π.symm k)) b) with ⟨z,hz,pr⟩ | ⟨j,ref,act⟩
      · exact Or.inl ⟨z,by simpa only [relabel,Equiv.apply_symm_apply] using hz,pr⟩
      · exact Or.inr ⟨π.symm j,by simpa only [f,rotSlot,Equiv.apply_symm_apply] using ref,act⟩
    obtain ⟨k,hk,ak⟩ := positive U hu active step
    exact ⟨π.symm k,by simpa only [Equiv.apply_symm_apply] using hk,ak⟩
lemma move_world {A B m} (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) (h : world A B m) :
    world A B (moved m π sw) := by
  classical
  obtain ⟨P,O,R,M,cap,root,rfl⟩ := h
  refine ⟨relabel P π sw,fun k => O (π k),fun s k => R (rotSlot π sw s) (π k),
    fun r s => M r (rotSlot π sw s),cap_relabel π sw cap,?_,?_⟩
  · exact root_changed π sw root
  · funext i k b
    by_cases hi : i.val < 11 <;> apply Bool.eq_iff_iff.mpr <;> simp [moved,marksFor,relabel,rotSlot,turn,flipSide,hi] <;> exact ⟨fun hh => decide_eq_true hh,fun hh => of_decide_eq_true hh⟩
lemma word_ext {a b : Fin 1024} (h : ∀ k : Fin 5, ∀ s : Bool,
    a.val.testBit (slotNum (k,s)) = b.val.testBit (slotNum (k,s))) : a=b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · let t := readSlot i
    have r := readSlotNum (⟨i,hi⟩ : Fin 10)
    simpa only [t,r] using h t.1 t.2
  · have le : 2^10 ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le le),Nat.testBit_lt_two_pow (b.isLt.trans_le le)]
set_option maxRecDepth 10000 in
lemma mirror_bits : ∀ x : Fin 1024, ∀ k : Fin 5, ∀ b : Bool,
    (1023-x.val).testBit (slotNum (k,b)) = !(x.val.testBit (slotNum (k,b))) := by
  intro x k b
  have eq : 1023-x.val = 2^10-(x.val+1) := by omega
  rw [eq,Nat.testBit_two_pow_sub_succ (by exact x.isLt),decide_eq_true (slotNum_lt _),Bool.true_and]
lemma rep_primal (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (z : FeatureId) (k : Fin 5) (b : Bool) :
    (represented (marksFor P M) (primal z)).val.testBit (slotNum (k,b)) = true ↔ P (featureOf z) (k,b) := by
  change ((if z.val < 11 then rawNumber (marksFor P M) (primal z) else _).val).testBit _ = true ↔ _
  simp [z.isLt,rawNumber_bit,marksFor,primal]
lemma rep_dual (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) (r : Fin 15) (k : Fin 5) (b : Bool) :
    (represented (marksFor P M) (dual r)).val.testBit (slotNum (k,b)) = false ↔ M r (k,b) := by
  have ge : ¬(dual r).val < 11 := by change ¬11+r.val < 11; omega
  simp only [represented,ge,↓reduceIte,mirror_bits,rawNumber_bit,marksFor,↓reduceDIte]
  have er : (⟨(dual r).val-11,by change 11+r.val-11 < 15; omega⟩ : Fin 15) = r := by
    apply Fin.ext
    change 11+r.val-11=r.val
    omega
  simp [er]
lemma represented_actual (P : Feature → Slot → Prop) (M : Fin 15 → Slot → Prop) :
    represented (marksFor P M) = wordAt P M := by
  funext i
  apply word_ext
  intro k b
  by_cases hi : i.val < 11
  · let z : FeatureId := ⟨i.val,hi⟩
    have e : i = primal z := Fin.ext rfl
    rw [e]
    apply Bool.eq_iff_iff.mpr
    exact (rep_primal P M z k b).trans (primal_word P M z (k,b)).symm
  · let r : Fin 15 := ⟨i.val-11,by omega⟩
    have e : i = dual r := by apply Fin.ext; change i.val=11+(i.val-11); omega
    rw [e]
    have h := (rep_dual P M r k b).trans (dual_word P M r (k,b)).symm
    cases x : (represented (marksFor P M) (dual r)).val.testBit (slotNum (k,b)) <;>
      cases y : (wordAt P M (dual r)).val.testBit (slotNum (k,b)) <;> simp_all
lemma numeric_world {A B m} (n : Fin 15 → ℕ) (p : PositiveId → ℕ)
    (neg : ∀ r z, (n r).testBit z.val = true → present A B (rows r) (featureOf z))
    (pos : ∀ u z, present A B (fsCode (liftPoint u).val) z → (p u).testBit (fid z).val = true)
    (h : world A B m) : ∃ O R, encLayout n p (represented m) O R := by
  obtain ⟨P,O,R,M,_,root,rfl⟩ := h
  rw [represented_actual]
  exact ⟨O,R,frame_of_rooted root n p neg pos⟩
def decodeId (i : Id) : FeatureId ⊕ Fin 15 :=
  if h : i.val < 11 then .inl ⟨i.val,h⟩ else .inr ⟨i.val-11,by omega⟩
lemma at_primal (z : FeatureId) : decodeId (primal z) = .inl z := by
  simp [decodeId,primal,z.isLt]
lemma at_dual (r : Fin 15) : decodeId (dual r) = .inr r := by
  have neg : ¬(dual r).val < 11 := by change ¬11+r.val < 11; omega
  simp only [decodeId,neg,↓reduceDIte,Sum.inr.injEq]
  apply Fin.ext
  change 11+r.val-11=r.val
  omega
lemma id_cases (i : Id) : (∃ z, i=primal z) ∨ ∃ r, i=dual r := by
  by_cases lt : i.val<11
  · exact Or.inl ⟨⟨i.val,lt⟩,Fin.ext rfl⟩
  · refine Or.inr ⟨⟨i.val-11,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=11+(i.val-11)
    omega
def delta (x y : ℕ) := x &&& (2047 ^^^ y)
def unitLink (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (r : Fin 15) (z : FeatureId) : Bool :=
  (List.finRange 100).any fun u => delta (pos u) (neg r) == 1 <<< z.val
def crossLink (neg : Fin 15 → ℕ) (pos : PositiveId → ℕ) (r s : Fin 15) : Bool :=
  r != s && (List.finRange 100).any fun u => pos u &&& (neg r ||| neg s) == pos u
def generatedNet (n : Fin 15 → ℕ) (p : PositiveId → ℕ) (mode : Fin 3) (i j : Id) : Bool :=
  match decodeId i,decodeId j with
  | .inl _, .inl _ => false
  | .inl z, .inr r | .inr r, .inl z =>
    if mode.val=0 then (n r).testBit z.val else if mode.val=1 then unitLink n p r z else false
  | .inr r, .inr s => mode.val=2 && crossLink n p r s
lemma unit_link_valid {n p w O R} (h : encLayout n p w O R) {r : Fin 15} {z : FeatureId}
    (ok : unitLink n p r z = true) : ∃ s : Slot,
    (w (primal z)).val.testBit (slotNum s) = true ∧ (w (dual r)).val.testBit (slotNum s) = false := by
  obtain ⟨u,_,eq⟩ := List.any_eq_true.mp ok
  have mask := beq_iff_eq.mp eq
  have cnt : ∀ v : FeatureId, (2047 : ℕ).testBit v.val = true := by decide +kernel
  have hit := frame_hit h r u [primal z] (by
    intro v present absent
    have read := congrArg (fun t : ℕ => t.testBit v.val) mask
    simp only [delta,Nat.testBit_and,Nat.testBit_xor,present,absent,cnt,Bool.true_xor,Bool.not_false,
      Bool.true_and,Nat.one_shiftLeft,Nat.testBit_two_pow,Bool.true_eq] at read
    have ev : z.val = v.val := of_decide_eq_true read
    exact Fin.ext ev ▸ List.mem_singleton_self _)
  obtain ⟨i,hi,s,l,r'⟩ := hit
  exact ⟨s,List.mem_singleton.mp hi ▸ l,r'⟩
lemma cross_link_valid {n p w O R} (h : encLayout n p w O R) {r s}
    (ok : crossLink n p r s = true) : relatedJoin w (dual r) (dual s) false false true := by
  obtain ⟨_,ex⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨u,_,eq⟩ := List.any_eq_true.mp ex
  apply enc_cross (u := u) h
  intro z hit
  have ev := congrArg (fun t : ℕ => t.testBit z.val) (beq_iff_eq.mp eq)
  simpa only [Nat.testBit_and,Nat.testBit_or,hit,Bool.true_and,Bool.or_eq_true] using ev
lemma generated_valid {n p w O R} (h : encLayout n p w O R) : linkValid (generatedNet n p) w := by
  have orientP (z : FeatureId) : orientation (primal z) = true := decide_eq_true z.isLt
  have orientN (r : Fin 15) : orientation (dual r) = false := by
    simp [orientation,dual]
  constructor
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    · rw [orientP]
      exact enc_sub h edge
    · rw [orientN]
      intro k off
      cases e : (w (primal v)).val.testBit k.val with
      | false => rfl
      | true => have bad := enc_sub h edge k e; simp [off] at bad
  constructor
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    · obtain ⟨q,l,right⟩ := unit_link_valid h edge
      rw [orientP]
      exact ⟨q,l,right⟩
    · obtain ⟨q,l,right⟩ := unit_link_valid h edge
      rw [orientN]
      exact ⟨q,right,l⟩
  · intro i j edge
    rcases id_cases i with ⟨z,rfl⟩ | ⟨r,rfl⟩ <;> rcases id_cases j with ⟨v,rfl⟩ | ⟨s,rfl⟩ <;>
      simp [generatedNet,at_primal,at_dual] at edge
    exact cross_link_valid h edge
def occupied (x : Fin 1024) : Finset (Fin 5) := Finset.univ.filter fun k =>
  x.val.testBit (slotNum (k,false)) || x.val.testBit (slotNum (k,true))
lemma occupied_mem {x : Fin 1024} (k : Fin 5) :
    k ∈ occupied x ↔ ∃ b : Bool, x.val.testBit (slotNum (k,b)) = true := by
  simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and,Bool.or_eq_true]
  exact ⟨fun h => h.elim (fun q => ⟨false,q⟩) (fun q => ⟨true,q⟩),
    fun ⟨b,q⟩ => by cases b <;> simp [q]⟩
def consistent (x : Fin 1024) : Prop :=
  ∀ k : Fin 5, ∀ b d : Bool, x.val.testBit (slotNum (k,b)) = false →
    x.val.testBit (slotNum (k,d)) = false → b=d
def seedRows (hot : ℕ) := Finset.univ.filter fun r : Fin 15 => hot.testBit r.val
def packDomains : List ℕ → ℕ
  | [] => 0
  | x::xs => (packDomains xs <<< 1025) ||| x
lemma packed_reads {xs : List ℕ} {i v : ℕ} (slot : ((xs[i]?).getD 0).testBit v = true) :
    (packDomains xs).testBit (1025*i+v) = true := by
  induction xs generalizing i with
  | nil => simp at slot
  | cons x xs ih =>
    rw [packDomains,Nat.testBit_or,Bool.or_eq_true]
    cases i with
    | zero => right; simpa using slot
    | succ i =>
      left
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      have ge : 1025 ≤ 1025*(i+1)+v := by omega
      have ee : 1025*(i+1)+v-1025=1025*i+v := by omega
      exact ⟨decide_eq_true ge,ee ▸ ih (by simpa using slot)⟩
def budgetOne : ℕ := 0x100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000010000000000000001000100010001111f
def budgetTwo : ℕ := 0x100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000000000000000100000000000000010000000000000001000100010001111f000100010001111f000100010001111f000100010001111f111f111f111fffff
def cutDomain : ℕ := 0xeee0eee0eee00000eee0eee0eee00000eee0eee0eee000000000000000000000eee0eee0eee00000eee0eee0eee00000eee0eee0eee000000000000000000000eee0eee0eee00000eee0eee0eee00000eee0eee0eee0000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def virtualDomain (n : ℕ) : ℕ :=
  if n ≤ 1 then allWords else if n ≤ 2 then 0x111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else if n ≤ 4 then 0x100010001111f000100010001111f000100010001111f111f111f111fffff000100010001111f000100010001111f000100010001111f111f111f111fffff000100010001111f000100010001111f000100010001111f111f111f111fffff111f111f111fffff111f111f111fffff111f111f111fffffffffffffffffffff else if n ≤ 8 then budgetTwo else if n ≤ 16 then budgetOne else if n ≤ 32 then 0x1 else 0
set_option maxRecDepth 10000 in
def prePair (v i : ℕ) : Bool :=
  Nat.testBit v (Nat.mul 2 i) || Nat.testBit v (Nat.add (Nat.mul 2 i) 1)
def preOcc (v : ℕ) : ℕ :=
  (prePair v 0).toNat + ((prePair v 1).toNat + ((prePair v 2).toNat +
    ((prePair v 3).toNat + (prePair v 4).toNat)))
lemma preOcc_eq (x : Fin 1024) : (occupied x).card = preOcc x.val := by
  unfold occupied
  rw [Fin.card_filter_univ_succ',Fin.card_filter_univ_succ',Fin.card_filter_univ_succ',
    Fin.card_filter_univ_succ',Fin.card_filter_univ_succ']
  simp only [Finset.univ_eq_empty,Finset.filter_empty,Finset.card_empty,Nat.add_zero]
  have bit (b : Bool) : (if b = true then 1 else 0 : ℕ) = b.toNat := by cases b <;> rfl
  simp only [bit]
  rfl
def prePairMask (k : ℕ) : ℕ := Nat.lor (column (2*k)) (column (2*k+1))
lemma prePairMask_bit (x : Fin 1024) (k : ℕ) (hk : k < 5) :
    (prePairMask k).testBit x.val = prePair x.val k := by
  have a := column_ok x (⟨2*k,by omega⟩ : Fin 10)
  have b := column_ok x (⟨2*k+1,by omega⟩ : Fin 10)
  exact (Nat.testBit_or ..).trans (congrArg₂ (· || ·) a b)
def preRanks : ℕ → ℕ → ℕ
  | 0,_ => allWords
  | k+1,0 => Nat.land (preRanks k 0) (Nat.xor allWords (prePairMask k))
  | k+1,l+1 => Nat.land (preRanks k (l+1)) (Nat.lor (Nat.xor allWords (prePairMask k)) (preRanks k l))
def preCount (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => preCount x k + (prePair x k).toNat
lemma preCount_eq (x : ℕ) : preCount x 5 = preOcc x := by
  simp [preCount,preOcc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
lemma preRanks_at (x : Fin 1024) (k : ℕ) (hk : k ≤ 5) (l : ℕ) :
    (preRanks k l).testBit x.val = decide (preCount x.val k ≤ l) := by
  induction k generalizing l with
  | zero => simpa [preRanks,preCount] using allWords_bit x
  | succ k ih =>
    have le : k ≤ 5 := by omega
    have mask : (allWords ^^^ prePairMask k).testBit x.val = !(prePair x.val k) := by
      rw [Nat.testBit_xor,allWords_bit,prePairMask_bit x k (by omega)]; cases prePair x.val k <;> rfl
    cases l with
    | zero =>
      change (((preRanks k 0) &&& (allWords ^^^ prePairMask k)).testBit x.val) = _
      rw [Nat.testBit_and,mask,ih le]
      cases e : prePair x.val k <;> simp [preCount,e]
    | succ l =>
      change (((preRanks k (l+1)) &&& ((allWords ^^^ prePairMask k) ||| preRanks k l)).testBit x.val) = _
      rw [Nat.testBit_and,Nat.testBit_or,mask,ih le,ih le]
      cases e : prePair x.val k <;> simp [preCount,e] <;> omega
lemma budgetOne_ok : ∀ x : Fin 1024, (occupied x).card ≤ 1 → budgetOne.testBit x.val = true := by
  intro x h
  have eq : budgetOne = preRanks 5 1 := by decide +kernel
  rw [eq,preRanks_at x 5 (by decide),decide_eq_true_eq,preCount_eq,← preOcc_eq]
  exact h
set_option maxRecDepth 10000 in
lemma budgetTwo_ok : ∀ x : Fin 1024, (occupied x).card ≤ 2 → budgetTwo.testBit x.val = true := by
  intro x h
  have eq : budgetTwo = preRanks 5 2 := by decide +kernel
  rw [eq,preRanks_at x 5 (by decide),decide_eq_true_eq,preCount_eq,← preOcc_eq]
  exact h
set_option maxRecDepth 10000 in
lemma cutDomain_ok : ∀ x : Fin 1024, consistent x → cutDomain.testBit x.val = true := by
  intro x h
  have on (k : Fin 5) : prePair x.val k.val = true := by
    by_contra h0
    have z : prePair x.val k.val = false := by simpa using h0
    have parts := Bool.or_eq_false_iff.mp z
    exact Bool.noConfusion (h k false true (by simpa [slotNum] using parts.1) (by simpa [slotNum] using parts.2))
  have full : preOcc x.val = 5 := by
    unfold preOcc
    have h0 := on 0
    have h1 := on 1
    have h2 := on 2
    have h3 := on 3
    have h4 := on 4
    change prePair x.val 0 = true at h0
    change prePair x.val 1 = true at h1
    change prePair x.val 2 = true at h2
    change prePair x.val 3 = true at h3
    change prePair x.val 4 = true at h4
    simp [h0,h1,h2,h3,h4]
  have eq : cutDomain = allWords ^^^ preRanks 5 4 := by decide +kernel
  rw [eq,Nat.testBit_xor,allWords_bit,preRanks_at x 5 (by decide),preCount_eq,full]
  decide
set_option maxRecDepth 10000 in
def preLimit (n : ℕ) :=
  if n ≤ 1 then 5 else if n ≤ 2 then 4 else if n ≤ 4 then 3 else if n ≤ 8 then 2 else 1
lemma virtualDomain_aux : ∀ k : Fin 16, ∀ x : Fin 1024, k.val ≤ 2^(5-(occupied x).card) →
    (virtualDomain k.val).testBit x.val = true := by
  intro k x h
  have equalMasks : preScan (fun n => Nat.beq (virtualDomain n) (preRanks 5 (preLimit n))) 16 = true := by decide +kernel
  have rule : preScan (fun n => preScan (fun c =>
      Nat.blt (2^(5-c)) n || Nat.ble c (preLimit n)) 6) 16 = true := by decide +kernel
  have hc : (occupied x).card < 6 := by
    have hb := Finset.card_le_univ (occupied x)
    simpa using Nat.lt_succ_of_le hb
  have lim := preScan_at (preScan_at rule k.isLt) hc
  have good := (Bool.or_eq_true_iff.mp lim).resolve_left (by simpa using Nat.not_lt_of_ge h)
  rw [Nat.eq_of_beq_eq_true (preScan_at equalMasks k.isLt),preRanks_at x 5 (by decide),decide_eq_true_eq,preCount_eq,← preOcc_eq]
  exact Nat.le_of_ble_eq_true good
lemma virtualDomain_ok (k : ℕ) (x : Fin 1024) (bd : k ≤ 15) (h : k ≤ 2^(5-(occupied x).card)) :
    (virtualDomain k).testBit x.val = true := virtualDomain_aux ⟨k,by omega⟩ x h
def startingField (support hot : ℕ) (i : Id) : ℕ :=
  if i.val < 10 then if support.testBit i.val then budgetOne else budgetTwo
  else if i.val=10 then virtualDomain (seedRows hot).card else cutDomain
def initialPacked (support hot : ℕ) := packDomains (List.ofFn (startingField support hot))
lemma start_preserved {A B : Finset V} {m : Marks} (support hot : ℕ)
    (support_ok : ∀ v : V, support.testBit v.val = true → v ∈ A ∨ v ∈ B)
    (hot_ok : ∀ r ∈ seedRows hot, present A B (rows r) none)
    (h : world A B m) : insidePacked (initialPacked support hot) (represented m) := by
  classical
  obtain ⟨P,O,R,M,cap,root,rfl⟩ := h
  let w := represented (marksFor P M)
  have used (z : FeatureId) (k : Fin 5) :
      k ∈ occupied (w (primal z)) ↔ ∃ b, P (featureOf z) (k,b) := by
    rw [occupied_mem]
    exact exists_congr fun b => rep_primal P M z k b
  intro i
  apply packed_reads
  simp only [List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
  change (startingField support hot i).testBit (w i).val = true
  by_cases vert : i.val<10
  · let v : V := ⟨i.val,vert⟩
    let z := fid (some v)
    have addr : i=primal z := Fin.ext rfl
    obtain ⟨S,hs,two,one⟩ := cap v
    have eql : occupied (w i)=S := by
      ext k
      rw [addr,used,hs]
      simp [z,featureOf_inv]
    simp only [startingField,vert,↓reduceIte]
    split
    · rename_i bit
      apply budgetOne_ok
      rw [eql]
      exact one (support_ok v bit)
    · apply budgetTwo_ok
      rwa [eql]
  · by_cases mid : i.val=10
    · let z := fid none
      have addr : i=primal z := Fin.ext mid
      let idle := (occupied (w i))ᶜ
      have spec (k) : k ∈ idle ↔ ∀ b, ¬ P none (k,b) := by
        change k ∈ (occupied (w i))ᶜ ↔ _
        rw [Finset.mem_compl,addr,used]
        simp [z,featureOf_inv]
      have count := idle_capacity root (seedRows hot) hot_ok idle spec
      have eq : idle.card = 5-(occupied (w i)).card := by simp [idle,Finset.card_compl]
      rw [eq] at count
      simp only [startingField,vert,mid,↓reduceIte]
      apply virtualDomain_ok
      · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 15)
      · exact count
    · let r : Fin 15 := ⟨i.val-11,by omega⟩
      have addr : i=dual r := by apply Fin.ext; change i.val=11+(i.val-11); omega
      simp only [startingField,vert,mid,↓reduceIte]
      apply cutDomain_ok
      intro k b e hb he
      rw [addr] at hb he
      exact root.1 r k b e ((rep_dual P M r k b).mp hb) ((rep_dual P M r k e).mp he)
def admissibleTable (negative : Bool) (v : Fin 1024) : ℕ := if negative then 1023-v.val else v.val
def sideMask (neg : Bool) (k : Fin 5) : ℕ :=
  if neg then
    if k.val=0 then 0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd else if k.val=1 then 0xff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f else if k.val=2 then 0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffff else if k.val=3 then 0xffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  else
    if k.val=0 then 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb else if k.val=1 then 0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ff else if k.val=2 then 0xffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff else if k.val=3 then 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def orderMask (neg : Bool) (k : Fin 5) : ℕ :=
  if neg then
    if k.val=0 then allWords else if k.val=1 then 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef else if k.val=2 then 0xf000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0fffff000ff00fff0ffff else if k.val=3 then 0xffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffffffff000000000000ffffffff00000000ffffffffffff0000ffffffffffffffff else 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  else
    if k.val=0 then allWords else if k.val=1 then 0xf731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731f731 else if k.val=2 then 0xffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000fffff0fff00ff000f else if k.val=3 then 0xffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffffffffffffffffffff0000ffffffffffff00000000ffffffff000000000000ffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff
set_option maxRecDepth 10000 in
def preWireMask (b : Bool) (k : Fin 5) (s : Bool) : ℕ :=
  if b then allWords ^^^ column (slotNum (k,s)) else column (slotNum (k,s))
lemma preWire_bit (b : Bool) (k : Fin 5) (s : Bool) (v : Fin 1024) :
    (preWireMask b k s).testBit v.val = (admissibleTable b v).testBit (slotNum (k,s)) := by
  have col := column_ok v (⟨slotNum (k,s),slotNum_lt _⟩ : Fin 10)
  cases b with
  | false => exact col
  | true =>
    change (allWords ^^^ column (slotNum (k,s))).testBit v.val = (1023-v.val).testBit _
    rw [Nat.testBit_xor,allWords_bit,col,mirror_bits]
    cases v.val.testBit (slotNum (k,s)) <;> rfl
def preSideWord (b : Bool) (k : Fin 5) :=
  preWireMask b k false ||| (allWords ^^^ preWireMask b k true)
def preOrderWord (b : Bool) (k : Fin 5) :=
  let prev := prevGate k
  let low := preWireMask b k false
  let high := preWireMask b k true
  let zeroLow := allWords ^^^ preWireMask b prev false
  let zeroHigh := allWords ^^^ preWireMask b prev true
  (zeroHigh ||| high) &&& ((zeroHigh &&& high) ||| (zeroLow ||| low))
lemma preWordValue (b : Bool) (v : Fin 1024) : admissibleTable b v < 1024 := by
  cases b <;> simp [admissibleTable] <;> omega
lemma sideMask_ok : ∀ b k (v : Fin 1024), pairDigit (admissibleTable b v) k ≠ 2 →
    (sideMask b k).testBit v.val = true := by
  have masks : ∀ b k, sideMask b k = preSideWord b k := by decide +kernel
  have rule : ∀ a b : Bool, a.toNat + 2*b.toNat ≠ 2 → (a || !b) = true := by decide
  intro b k v h
  let w : Fin 1024 := ⟨admissibleTable b v,preWordValue b v⟩
  change pairDigit w.val k ≠ 2 at h
  rw [pairDigit_bits] at h
  rw [masks]
  simpa only [preSideWord,Nat.testBit_or,Nat.testBit_xor,allWords_bit,Bool.true_xor,preWire_bit]
    using rule _ _ h
set_option maxRecDepth 10000 in
lemma orderMask_ok : ∀ b k (v : Fin 1024),
    pairDigit (admissibleTable b v) (prevGate k) ≤ pairDigit (admissibleTable b v) k →
    (orderMask b k).testBit v.val = true := by
  have masks : ∀ b k, orderMask b k = preOrderWord b k := by decide +kernel
  have rule : ∀ p q u v : Bool, p.toNat + 2*q.toNat ≤ u.toNat + 2*v.toNat →
      ((!q || v) && ((!q && v) || (!p || u))) = true := by decide
  intro b k v h
  let w : Fin 1024 := ⟨admissibleTable b v,preWordValue b v⟩
  change pairDigit w.val (prevGate k) ≤ pairDigit w.val k at h
  rw [pairDigit_bits,pairDigit_bits] at h
  rw [masks]
  simpa only [preOrderWord,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,allWords_bit,Bool.true_xor,preWire_bit]
    using rule _ _ _ _ h
def negativeSig (m : ℕ) : ℕ := Nat.lor (if m.testBit 9 then 0x7c00 else 0) (Nat.lor (if m.testBit 8 then 0x6380 else 0) (Nat.lor (if m.testBit 7 then 0x370 else 0) (Nat.lor (if m.testBit 6 then 0x6e else 0) (Nat.lor (if m.testBit 5 then 0x180d else 0) (Nat.lor (if m.testBit 4 then 0x2c9 else 0) (Nat.lor (if m.testBit 3 then 0x1434 else 0) (Nat.lor (if m.testBit 2 then 0x488a else 0) (Nat.lor (if m.testBit 1 then 0x3211 else 0) (Nat.lor (if m.testBit 0 then 0x4522 else 0) (0))))))))))
def positiveSig (m : ℕ) : ℕ := Nat.lor (if m.testBit 9 then 0xffffffffffe00000000000000 else 0) (Nat.lor (if m.testBit 8 then 0xffffe000001fffffe00000000 else 0) (Nat.lor (if m.testBit 7 then 0xf0001f80001fffc01ffff8000 else 0) (Nat.lor (if m.testBit 6 then 0xc00187e001e003c1fff07ff8 else 0) (Nat.lor (if m.testBit 5 then 0x3c00679ff0180331e00c7fc7 else 0) (Nat.lor (if m.testBit 4 then 0x80381041c0997c2bf9f0a7c27 else 0) (Nat.lor (if m.testBit 3 then 0x2070db53ce44310878e7e394 else 0) (Nat.lor (if m.testBit 2 then 0x49b4c24ab34030aef04915a7a else 0) (Nat.lor (if m.testBit 1 then 0xa64ae5216a316a414026f950f else 0) (Nat.lor (if m.testBit 0 then 0x5925a8860de68dc4251d088f9 else 0) (0))))))))))
def incidence (i : ℕ) : ℕ := (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x4522 | false => 0x3211) | false => (match Nat.blt i 3 with | true => 0x488a | false => (match Nat.blt i 4 with | true => 0x1434 | false => 0x2c9))) | false => (match Nat.blt i 7 with | true => (match Nat.blt i 6 with | true => 0x180d | false => 0x6e) | false => (match Nat.blt i 8 with | true => 0x370 | false => (match Nat.blt i 9 with | true => 0x6380 | false => 0x7c00))))
def permNumBlock (i : ℕ) : ℕ := 0x130246857900000031826405790000000815643279000000803546127900000020314758690000000251743869000000530847216900000035287401690000001520768349000000518067234900000028136750490000008253761049000000024135796800000020715349680000004709532168000000742935016800000014203697580000004190632758000000291763405800000092473610580000001702569438000000719265043800000009146572380000009074561238000000031425869700000030845216970000001806523497000000813625049700000041302968570000001460923857000000631829405700000036489210570000000641958327000000608159432700000048035961270000008463950127000000302418579600000003548127960000005207183496000000253781049600000042031975860000002473910586000000702519438600000007459123860000004530897216000000547098321600000037429850160000007352894016000000241307968500000042937016850000001926704385000000914607238500000031420869750000001362804975000000641908327500000046398012750000002631879405000000629178340500000039247861050000009364872105000000182630579400000081560327940000002517038694000000528730169400000071520968340000001762905834000000651809723400000056789012340000002671938504000000628139750400000078253961040000008765932104000000071524968300000070954216830000001906427583000000917624058300000015608279430000005170286943000000671928504300000076598210430000000651849723000000609148572300000059074861230000009567840123000000084531697200000080651349720000004609138572000000648931057200000009547168320000009064175832000000560817943200000065987104320000005480379612000000459073861200000098463750120000008956734012000000354802796100000053782049610000004739205861000000745902386100000084530697210000004893605721000000954706832100000059876043210000009374268501000000398462750100000087352694010000007895623401000000293741685000000092671438500000003628149750000000639841275000000082631579400000002873516940000000762915834000000067895123400000003782549610000000739245861000000089364572100000009876543210
def permNum (i : ℕ) := Nat.land (Nat.shiftRight (permNumBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def repNumBlock (i : ℕ) : ℕ := 0x3ff01ff017f00ff00fd00fb00fa00bf00bd007f007d007700750074006f006d003f003e0037003600330032002f002d002b002a001f000f000b00070005000300010000
def repNum (i : ℕ) := Nat.land (Nat.shiftRight (repNumBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def envRecordBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1b37bf59ffffffbdffbfb7fdfe11ac7d00b61e4f17f7178f5ffec3ffd623307701361d49d7f4d78ddeaba3b5f622a87711b71f4ffff7ff8ffffff7fffe29247709249500c1bcd19884a3a111f30088771b35bf59fffffdbdefbfb7fdff292c7709369d49d7fcd79ddeaba3b5f722a87719b79f4fffffff9ffffff7ffff2b2c771bedbd94edfefdb8aca7ff3bff488c771dffddedfffeffddfeafffbffe6a2c771bffbfdfffffffbffffffffffe6324770924b510c1bcd13884a3a111f310886f1fedfdb4edfefdf8aca7ff3bfe40446f0becbd96effef5babcf7fbfffe40946f0964f5b6e7bcd97a94f3efd7fb40d86f1fedfdb6effefdfabcf7fffffe40d46f0be4f7bfe7bfd9ff97ffeffffa00b86f1fedffbfeffffdffbffffffffe40bc6f09fc99cfffeaf416fff7faffff20b86f01b0bf5fd7ffd52fdbffe3fff630a06f0bfebfdffffff7bffffffbffff34a86f01f8fffffffffd6ffbfffffffe60f06f0bf4fffff7ffddffdfffefffff70f86f0bf6fffff7ffdfffdfffefffff62f86f0924b510c1bc91b884a3a111f310883f1fedfdb4edfefdf8aca7ff3bfe48443f1ffdfdfdfffefdfcffb7fffffe60643f1079fdffbffebd6e7bf5dfffbe48143f1ffdfdfffffefdfefff7ffffff401c3f0036bd5997fc97ad5eab83b5f632a03f004e5cac3d542fcd7f3adffa5e42643f107fe3fdbfffbfe57fbfdfffee7ae43f14fffffdbfffbfed7fbfdffffeca643f14ff5cef3ff63fcf7ffedfffde62703f14fffdffbffebfef7fffdffffe72b43f0936bd59d7fc97bddeaba3b5f732a83f097edced7f7c2fddff3bfffeff626c3f1dffdeed7f7f2fddff3ffffeff6a6c3f1dfffdfffffebfffffffffffff62383f19769acf77fb3f97dfff3effff4938fd0b76b1fff7fcdfffdefbeff7fe0488fd1ee4f7ffa7bfffff17fffffffa11f0fb0be4f7bfe7bfd9ff97ffeffffa44d8fb14cdffbebfdfafef7fffdfff7e4844fb1fedfdb4edfefdf8aca7ff3bfe5cccfb0a36bd5997fcd7bd5eaba3b5f636a0bf0078e1fdbffcb86473f1dfffae70e4bf14f9fdfdbffebd6c7bf5dfffbe38e4bf0a76fdffb7fcdfff5efbeff7fe66f0bf147fffffbfffbfef7fffdffffe58d4bf0b76ddff77fcdfffdefbeff7ff44d8bf1feffffeffffffffffffffffff480cbf1b37bf59ffffffbdffbfb7fdfe20287f19ff9bcffffbff97fffffeffff001c7f10ffbfdfbfffbfaf7fffdffffe30b47f1bedbd96effefdbabcf7ffffff5c9c7f09f6deef77ff1fdfdfffeffffe63707f0976ddeff7fcdfdfdefbeff7fe40d87f0976fdfff7fcdfffdefbeff7fe50d87f1bfffdfdfffefffdfeafffbfff484c7f10f9fdffbffebd6e7bf5dfffbe68747f1bedfdb6effefdfabcf7ffffff58dc7f14f9fddfbffebd6e7bf5dfffbeb8b57f196f9acf7ffb3f97ffff3effff493cff | false => 0x97491cff7e8d017d7fbeafffe00986d0934b159d7fcd035d6aba3b5f610886d0974f1fff7fcd877d6fbeff7fe70b86d0976f9fff7fcde77dffbefffff62b86d09f6fbfff7ffde77dfffeffffe01b86d0bb6bf5fd7ffd7bfdfffe3fff714a86d0bf6bfdff7ffd7bfdfffebffff54986d0bfeffffffffffffffffffffff54f86d00369849166806055e0902b4f422203e097ed8ed7f7c2e55ff39fffefe40643e104958a42d462d402804df2a1e48443e107fc2ed3f7f2fc57f3fdffeee6a643e197fdaed7f7f2fd5ff3ffffeff6a6c3e1dffdeed7f7f2fddff3ffffefec8643e1049f9b6afdead6238f5dfef3e48143e1079f9ffbffebd667bf5dfffbe68343e107fd8ef3ffe3f477ffddffffe62303e197ff9fffffebf77fffdffffff62783e14f9dcef3ffe3d4e7bf5dfffbec8543e14ffffffbfffbfef7fffdffffeea743e1dffffffffffbfffffffffffffea7c3e10491c842d462d0828049f2a1e48043714cf5eac3d572fcd7f3edffa5e0224370924940041bc119884a3a111f30008371deddca46dfe3dd8aca7ff3bff480c371defdcac7dee3f5dff8dfffbff022c371defdeac7dff3fddffbffffbff0b2c371b6dbd94edfefdb8aca7bf3bff5c8c371fefffbcfdfffffdffbffffbff16ac3709369c4957fc179ddeaba3b5f62220371b37bd59fffeffbdffafb7fdff2a2c371b7fbdddfffeffbdfeafbfbffe6a24371ffffdfdfffefffdffaffffffeea643714ff5eef3ff73fcf7ffedfffde2b24371fffffffffffffffffffffffff2b2c370924b510c1bc913884a1a111f310882f00485ca42d442d482800df2a1e40442f1fedfdb4edfefdf8aca7ff3bff50cc2f0964f5b6e7bc997a94f1efd7fb40582f0048fdb6afdcad6a38f1dfef3e50942f1fedfdb6effefdfabcf7ffffff401c2f0030bd5997fc952c5aa183b5b630a02f14f9fdfdbffebd6c7aa5dfbfbe70e42f1ffffdfdfffefffdfeafffbfff34a82f1ffffdfffffefffffffffffffe70f02f1b25bd10effefdb8bcb7b7fdff10881f1fedfdb6effefdfabcf7ffffff58cc1f0006bd1897dc87ad5eab83b57612a01f0b26bd18d7fcd7bddeaba3b5f716a81f1b77fdfdfffefffdfeafffbfff5eec1f1ffffffffffffffffffffffffedae41f14c95fffbfd7bfef7bffdffffe4844fa14cfe3ffbfdfffef7ffffffffe59f4fa0a76e1ffb7fcdfff5efbeff7ee26a0bd196492c667bb3f9297ff3ed7fb4918bd0b6491b667b8d9fa94f3efd7fb44d8bd1b769bff77fbffffdffffff7ff6238bd0b64b596e7bcd9ba94f3efd7fb00887d0be4b79fe7bfd9bf97ffeffffb01387d09f69bcff7fbdf97dfffeefffe62387d0b76fdfff7fcdfffdefbeff7fe32a87d1967928f7fbb3f97ffff3efffe02247d0186030ff813ef87fffff4fffe02bc7d09fe9bcffffbff97fffffeffff202c7d) | false => (match Nat.blt i 3 with | true => 0x14c95ca62fc62d4a28c4dfef1ec8542a14f9fdffbffebd6e7bf5dfffbef8f42a0000b510819c812800a181013210800b0040e1b4a59c886000a1cf032850c00b0040f5b6a79c896a10f1cfc73a50d00b0b64f5b4e5bcd9f884a3ef13fb54c80b1fedfdb6effefdfabcf7ffffffdcdc0b09249400412c01188401a110f30008070b24bd10c5fcd5b88ca3a331f71488071deddca46d6e2d58ac05ff3affc84c071ffffdfdfffefffdfeafffbffffeec070136004956600605de0920b4f422287409369a497e6b2615ff3f32fcfe212c7419ff9bcffffbff97fffffeffff2b3c74104918842d422d0028041e2a1e480436104f188c3d422f057f0c1efa5e02243614cf5cac3d462f4d7f0cdffa5eca643600361849166006055e0802b4d422203614ff5ced3f662f4d7e0cdfbede6a24361dffdced7f6e2f5dff0dfffeff2a2c36107f1acd3f732f857f3e1efede0b243614ff5eed3f772fcd7f3edffedeeb6436107f1acf3ff33f877ffe1effde6b34361dffdeef7fff3fdfffffffffff6b2c36106d14842df63d882ca69d3bde48043314ed5ca42df63dc82ca6df3bdec844331b6db594edfefdb8aca7bd3bff5c8c3314cd5cac3d562dcc6f26dffa5ec8643314ef5eac3df73fcd7fbedffbdecb64331fffffffffffffffffffffffffdcec330030a15997fc902452a183b5a630a02d0924b110c1bc903084a1a111f310882d0b34b559d7fcd1bcd6a3a3b5f734a82d0974b1dff7fc8036c6e1a9f7fd70b82d0b7efdfffffcfffffffbffffff72b82d0020b51081bc912800a18111b210802b004854a42d4429482000df2a1e40442b14e9fdb4adfebd6828a5df3bbe50c42b0b6cf5b4edfcf9f8a4a3ff3bff54cc2b0060f5b6a7bc996a10f1cfd7ba40502b0b6cf5b6effcf9fab4f3fffffe50d42b14e95ca62fe63d4a28c4dfff9ec8542b14e9fdb6affebd6a38f5dfffbed8d42b1ffdfdfffffefdfefff7fffffffcfc2b0000bd1087dc852818a183a53610800f0924b510c1bc813884a1a111f310880f0936bd59d7fc873ddea9a3b5f732a80f00405ca425440d480800cf221e40400f0964d4a4672c09589401ef96fb40480f0964f9b4e5fc8c708ca1ef33fd50c80f1deddca46f6e2d58bc05ffbeffc84c0f1dedfdb4edfead78aca5ff3bffd8cc0f1dfffdfdfffeaf7dfeadffbffffaec0f0b24bd10c7fcd5b89ca3a3b5f714880f0b64fdb4e7fcddf89ca3efb7ff54c80f0b76fdfdf7fcdffddeabefb7ff76e80f0b64fdb6e7fcddfa9cf3eff7ff54d80f1ffffdfffffefffffeffffffffdccc0f09249100c1b8d19084a3a011f30088751b27b718f9bfffbdffbfb5f9fe03247509369949d7f8d795deaba2b5f622a8751b37bf59ffffffbdffbfb7fdfe212c7519379a4f7ffb3f97ffff36fffe2330751bffbfdfffffffbfffffffffff23b875 | false => 0x14e456ef27b73fcf17fedfffda4970fb0b24b510c1bcd1b884a3a111f3148801092490004028001084012010f10008050b36bd59d7fcd7bddeaba3b5f736a8051fedfdb4edfefdf8aca7ff3bffdccc03104900842d422d0028041c2a0e48043214c95cac3d462d4c6b04dffa1ec8643214ff5eef3ff73fcf7ffedfffdeeb7432004840a42d4428402000df2a0e40442a))
def envRecord (i : ℕ) := Nat.land (Nat.shiftRight (envRecordBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def suppNum (i : ℕ) := Nat.land (envRecord i) 1023
def hotNum (i : ℕ) := Nat.land (Nat.shiftRight (envRecord i) 10) 32767
def pointNum (i : ℕ) := Nat.shiftRight (envRecord i) 25
def firstKeyBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0xf000e700e3c0b9c0e170d3e0b6209220e1d0da50d310b3c0b470adb08ef07df0ea10c900b8408450b5e091f0a6e07550c3d0bc509350575080b055f073f031f0e340b940d4409540d9f0b1c0aea07d20d2d0b340cb508dc0acf0a03087706fb0b7c08400b1005940ae607c809f604ab0930057008b804f80793048306c702b30e8d0ba40c5c08540b4a0adc080c05620b450ad908ed07dc0a5509e9071c04710c5908510839038908f207d9074203210809055d073d031d0719046d0629022d0b640a74091007700ad209fc079404880acd0a00087506f809dd096506a403f9090c076c07c10341087a06f406ca02b40791048006c502b106a103f505b101b50e880ba00b6c0a7c0c37094a081a07360b420ad70aca0a0607fa0782052f045a0c56084e091407680816072e072606360807055a078f0485034a030202d7020a0c54084c0916076a0bbf058a0556031608ea07d4087206f2052a045204b202be0834038407bc033c054e030e045e0242073a031806c202ae02d20206027e01160c34094808180734080007880350030808f7087f07a006bc070f069702e6027a0bbc0588055403140532045602da020c053704bf0449029c02df027601e7010e0814072c072406340530045402d8020e079c06b406ac05bc043a03c202600196054c030c045c024004b802b80284011c0447029403cf01c8025a018e016f00960e100d380d980b240d200ca80b0208aa0b410ad50ac90a0508f5087d07a306bf0b5909190ae107cd0af908a10a0f06dd08050559078d0487053504bd044b029f0b5809180ae007cc0af808a00a0e06dc08e907d7087106f1079f06b706af05bf0a68075009f004a40a0806d80978042c0739031b06c102ad0445029703cd01cb0c3009500bb8059008fc0884053c04c407f90781052d0459070d069502e502790811073105510311079906b9044c02990349030102d5020902dd027501e5010d0810073005500310079806b8044d02980529045004b102bd043903c102630195072006300460024806a805b803d401d002d10205027d01150259018d016d00950b400ad40ac80a0408f4087c07a206be0a5009e409d80960070a0692043e03c608e807d6087006f0079e06b606ae05be07150469069d03f102e30273025f019208040558078c0486053404bc044a029e07140468069c03f002e20272025e01930738031a06c002ac0444029603cc01ca0624022805ac01b001e2010a016a009207f80780052c0458070c069402e4027807080690043c03c4061805a001f4017c0528045104b002bc043803c00262019402e10271025d019101ed017500f500890348030002d4020802dc027401e4010c02e00270025c019001ec017400f4008802d00204027c01140258018c016c009401e001080168009000f0008400780000 | false => 0xf780f6c0f380ee40f060e7a0eaa0c9a0f030e730e3f0b9f0e8f0ba70c5f08570f310edd0e5d0c7d0e3a0b9b0b83084b0ea30c930b8708470c5a0853083b038b0f300edc0e5c0c7c0e3b0b9a0b82084a0e370b970d4709570b670a77091307730e580c780de00c000d4a095a0b1a059a0b7f08430b130597090f076f07c303430f040e780ea80c980e240dac0c440bcc0e150d3d0b6109210b490adf080f05610e390b990b8108490d340b39093905790b5d091d0a6d075708f107db074103230e380b980b8008480d350b38093805780d9d0b1f0ae907d00ad109ff0797048a0d4809580b1805980cbc08e008c005000ae507cb09f504a9087906f706c902b70f020e720e3e0b9e0e8e0ba60c5e08560e120d3a0d9a0b260c3209520bba05920e360b960d4609560b660a76091207720b5b091a0ae307cf08130732055203130ea20c920b8608460c5b0852083a038a0b5a091b0ae207ce08120733055303120b7e08420b120596090e076e07c203420a6a075209f204a6072206320462024a0e140d3c0b6009200b480ade080e05600d220caa0b0008a808fe0886053e04c60d9c0b1e0ae807d10ad009fe0796048b0afa08a20a0d06df079b06ba044f029b0b5c091c0a6c075608f007da074003220afb08a30a0c06de079a06bb044e029a0ae407ca09f404a8087806f606c802b60a0a06da097a042e06aa05ba03d601d20f010e710e3d0b9d0e160d3f0b6309230e890ba10b6d0a7d0c36094b081b07370e350b950d4509550d9e0b1d0aeb07d30c55084d0917076b0bbe058b055703170ea00c910b8508440b5f091e0a6f07540c57084f091507690817072f072706370b7d08410b1105950ae707c909f704aa0835038507bd033d054f030f045f02430e8c0ba50c5d08550b4b0add080d05630c3509490819073508010789035103090b650a75091107710ad309fd079504890815072d072506350531045502d9020f0c5808500838038808f307d8074303200bbd0589055503150533045702db020d090d076d07c00340087b06f506cb02b5054d030d045d024104b902b90285011d0e1c0da40d300b3d0b460ada08ee07de0b430ad60acb0a0707fb0783052e045b0d2c0b350cb408dd0ace0a02087606fa08eb07d5087306f3052b045304b302bf0c3c0bc409340574080a055e073e031e0806055b078e0484034b030302d6020b0931057108b904f90792048206c602b2073b031906c302af02d30207027f01170b440ad808ec07dd0a5409e8071d047008f6087e07a106bd070e069602e7027b0acc0a01087406f909dc096406a503f8079d06b506ad05bd043b03c3026101970808055c073c031c0718046c0628022c053604be0448029d02de027701e6010f0790048106c402b006a003f405b001b40446029503ce01c9025b018f016e0097)
def firstKey (i : ℕ) := Nat.land (Nat.shiftRight (firstKeyBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def permuteBits (pw x : ℕ) : ℕ := (List.range 10).foldl (fun acc i =>
  if x.testBit i then acc ||| (1 <<< ((pw >>> (4*i)) &&& 15)) else acc) 0
def bitSub (a b : ℕ) : Bool := a &&& b == a
def coldMask (a b : ℕ) := negativeSig a &&& negativeSig b
def stableSig (a b na nb v : ℕ) : ℕ :=
  (32767 ^^^ incidence v) &&& ((32767 ^^^ ((if a.testBit v then 32767 else na) &&&
    (if b.testBit v then 32767 else nb))) ||| (na &&& nb))
def validClique (a b c : ℕ) : Bool :=
  let xs := (List.range 10).filter (fun v => c.testBit v)
  bitSub c (a ||| b) && xs.length == 6 &&
    let na := negativeSig a
    let nb := negativeSig b
    let ss := xs.map fun v => (v,stableSig a b na nb v,incidence v)
    ss.all fun v => ss.all fun w => v.1 == w.1 || (v.2.1 &&& w.2.1 != 0 && v.2.1 &&& w.2.2 != 0)
def validEnv (e a b : ℕ) : Bool :=
  bitSub (suppNum e) (a ||| b) && bitSub (hotNum e) (coldMask a b) &&
    bitSub (positiveSig a &&& positiveSig b) (pointNum e)
def vertexMark (π : Equiv.Perm V) (P : Feature → Slot → Prop) (z : Feature) := P (z.map π.symm)
lemma meet_map (π : Equiv.Perm V) (L U : Finset V) :
    meets (L.map π.toEmbedding) (U.map π.toEmbedding) ↔ meets L U := by
  constructor
  · rintro ⟨x,hx,ux⟩
    exact ⟨π.symm x,Finset.mem_map_equiv.mp hx,Finset.mem_map_equiv.mp ux⟩
  · rintro ⟨x,hx,ux⟩
    exact ⟨π x,Finset.mem_map.mpr ⟨x,hx,rfl⟩,Finset.mem_map.mpr ⟨x,ux,rfl⟩⟩
lemma present_push (π : Equiv.Perm V) (A B U : Finset V) (z : Feature) :
    present (A.map π.toEmbedding) (B.map π.toEmbedding) (U.map π.toEmbedding) z ↔
      present A B U (z.map π.symm) := by
  cases z with
  | none => exact (meet_map π A U).and (meet_map π B U)
  | some v => exact Finset.mem_map_equiv
lemma Vcap {A B P} (π : Equiv.Perm V) (h : capacity A B P) :
    capacity (A.map π.toEmbedding) (B.map π.toEmbedding) (vertexMark π P) := by
  intro v
  obtain ⟨S,mem,le,one⟩ := h (π.symm v)
  exact ⟨S,mem,le,fun hv => one (hv.imp Finset.mem_map_equiv.mp Finset.mem_map_equiv.mp)⟩
lemma Vlayout {A B P} (π : Equiv.Perm V) (ρ : Equiv.Perm (Fin 15))
    (row : ∀ r, (rows r).map π.toEmbedding = rows (ρ r)) (h : layout A B P) :
    layout (A.map π.toEmbedding) (B.map π.toEmbedding) (vertexMark π P) := by
  obtain ⟨O,R,M,uniq,avoid,refs,out,pos⟩ := h
  refine ⟨O,R,fun r s => M (ρ.symm r) s,fun r => uniq (ρ.symm r),?_,fun r => refs (ρ.symm r),
    fun r => out (ρ.symm r),?_⟩
  · intro r s z mr pm pr
    apply avoid (ρ.symm r) s (z.map π.symm) mr pm
    apply (present_push π A B (rows (ρ.symm r)) z).mp
    simpa only [row,Equiv.apply_symm_apply] using pr
  · rintro _ ⟨r,v,miss,rfl⟩ a cl
    let T := insert (π.symm v) (rows (ρ.symm r))
    have er : (rows (ρ.symm r)).map π.toEmbedding = rows r := by rw [row,Equiv.apply_symm_apply]
    have pushed : T.map π.toEmbedding = insert v (rows r) := by
      simp only [T,Finset.map_insert,Equiv.coe_toEmbedding,Equiv.apply_symm_apply,er]
    have hv : π.symm v ∉ rows (ρ.symm r) := by
      intro inside
      exact miss (er ▸ Finset.mem_map_equiv.mpr inside)
    apply pos T ⟨ρ.symm r,π.symm v,hv,rfl⟩ a
    intro k both
    apply cl k
    intro b
    rcases both b with ⟨z,hz,pr⟩ | ref
    · let t := z.map π
      have inv : t.map π.symm = z := by cases z <;> simp [t]
      refine Or.inl ⟨t,by simpa only [vertexMark,inv] using hz,?_⟩
      rw [←pushed]
      exact (present_push π A B T t).mpr (inv.symm ▸ pr)
    · exact Or.inr ref
def positiveColumn (i : ℕ) : ℕ := (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x5925a8860de68dc4251d088f9 | false => 0xa64ae5216a316a414026f950f) | false => (match Nat.blt i 3 with | true => 0x49b4c24ab34030aef04915a7a | false => (match Nat.blt i 4 with | true => 0x2070db53ce44310878e7e394 | false => 0x80381041c0997c2bf9f0a7c27))) | false => (match Nat.blt i 7 with | true => (match Nat.blt i 6 with | true => 0x3c00679ff0180331e00c7fc7 | false => 0xc00187e001e003c1fff07ff8) | false => (match Nat.blt i 8 with | true => 0xf0001f80001fffc01ffff8000 | false => (match Nat.blt i 9 with | true => 0xffffe000001fffffe00000000 | false => 0xffffffffffe00000000000000))))
def accumulateSig (col : ℕ → ℕ) (x : ℕ) := (List.range 10).foldl
  (fun a v => (if x.testBit v then col v else 0) ||| a) 0
lemma accumulates (col : ℕ → ℕ) (x j : ℕ) :
    (accumulateSig col x).testBit j = true ↔
      ∃ v : V, x.testBit v.val = true ∧ (col v.val).testBit j = true := by
  have go (xs : List ℕ) (a : ℕ) :
      (xs.foldl (fun d v => (if x.testBit v then col v else 0) ||| d) a).testBit j = true ↔
        a.testBit j = true ∨ ∃ i ∈ xs, x.testBit i = true ∧ (col i).testBit j = true := by
    induction xs generalizing a with
    | nil => simp
    | cons i xs ih =>
      simp only [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true,List.mem_cons]
      cases e : x.testBit i <;> simp [e] <;> aesop
  rw [accumulateSig,go]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  exact ⟨fun ⟨v,hv,hit⟩ => ⟨⟨v,hv⟩,hit⟩,fun ⟨v,hit⟩ => ⟨v.val,v.isLt,hit⟩⟩
lemma negative_join (x : ℕ) : negativeSig x = accumulateSig incidence x := by rfl
lemma positive_join (x : ℕ) : positiveSig x = accumulateSig positiveColumn x := by rfl
lemma incidence_ok : ∀ v : V, ∀ r : Fin 15, (incidence v.val).testBit r.val = true ↔ v ∈ rows r := by
  decide +kernel
set_option maxRecDepth 10000 in
lemma col_point_ok : ∀ v : V, ∀ u : PositiveId, (positiveColumn v.val).testBit u.val = true ↔
    v ∈ fsCode (liftPoint u).val := by decide +kernel
lemma negative_has (x : ℕ) (r : Fin 15) :
    (negativeSig x).testBit r.val = true ↔ meets (fsCode x) (rows r) := by
  rw [negative_join,accumulates]
  unfold meets
  apply exists_congr
  intro v
  simp [fsCode,incidence_ok]
lemma positive_has (x : ℕ) (u : PositiveId) :
    (positiveSig x).testBit u.val = true ↔ meets (fsCode x) (fsCode (liftPoint u).val) := by
  rw [positive_join,accumulates]
  unfold meets
  apply exists_congr
  intro v
  exact and_congr (by simp [fsCode]) (col_point_ok v u)
lemma bitSub_use {a b : ℕ} (h : bitSub a b = true) (i : ℕ) (e : a.testBit i = true) : b.testBit i = true := by
  have t := congrArg (fun z : ℕ => z.testBit i) (beq_iff_eq.mp h)
  simpa only [Nat.testBit_and,e,Bool.true_and] using t
def modelNeg (e : ℕ) (r : Fin 15) := (liftRow r).val ||| (if (hotNum e).testBit r.val then 1024 else 0)
def modelPos (e : ℕ) (u : PositiveId) := (liftPoint u).val ||| (if (pointNum e).testBit u.val then 1024 else 0)
lemma base_bit (x : Fin 1024) (hit : Bool) (v : V) :
    (x.val ||| (if hit then 1024 else 0)).testBit v.val = x.val.testBit v.val := by
  have h : (1024 : ℕ).testBit v.val = false := by revert v; decide +kernel
  cases hit <;> simp [h,Nat.testBit_or]
lemma seed_bit (x : Fin 1024) (hit : Bool) :
    (x.val ||| (if hit then 1024 else 0)).testBit 10 = hit := by
  have h : x.val.testBit 10 = false := Nat.testBit_lt_two_pow x.isLt
  cases hit <;> simp [h,Nat.testBit_or] <;> decide
lemma compatible_support {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ v : V, (suppNum e).testBit v.val = true → v ∈ fsCode a ∨ v ∈ fsCode b := by
  intro v hv
  have inc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).1).1
  have bit := bitSub_use inc _ hv
  simpa [Nat.testBit_or,fsCode] using bit
lemma compatible_hot {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ r ∈ seedRows (hotNum e), present (fsCode a) (fsCode b) (rows r) none := by
  intro r hr
  have inc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).1).2
  have bit := bitSub_use inc _ (Finset.mem_filter.mp hr).2
  change ((negativeSig a) &&& negativeSig b).testBit r.val = true at bit
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  exact ⟨(negative_has a r).mp bit.1,(negative_has b r).mp bit.2⟩
lemma compatible_neg {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ r z, (modelNeg e r).testBit z.val = true → present (fsCode a) (fsCode b) (rows r) (featureOf z) := by
  intro r z bit
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ z.isLt) with eq | lt
  · have en : featureOf z = none := by simp [featureOf,atFeature,eq]
    rw [en]
    have hit : (hotNum e).testBit r.val = true := by simpa only [eq,modelNeg,seed_bit] using bit
    exact compatible_hot good _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩)
  · let v : V := ⟨z.val,lt⟩
    have en : featureOf z = some v := by simp [featureOf,atFeature,v,lt]
    rw [en]
    have hit : (liftRow r).val.testBit v.val = true := (base_bit (liftRow r) _ v) ▸ bit
    have mem : v ∈ fsCode (liftRow r).val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
    exact negNumber_spec r ▸ mem
lemma compatible_pos {e a b : ℕ} (good : validEnv e a b = true) :
    ∀ u z, present (fsCode a) (fsCode b) (fsCode (liftPoint u).val) z →
      (modelPos e u).testBit (fid z).val = true := by
  intro u z hz
  cases z with
  | none =>
    change (modelPos e u).testBit 10 = true
    rw [modelPos,seed_bit]
    have inc := (Bool.and_eq_true_iff.mp good).2
    apply bitSub_use inc
    change ((positiveSig a) &&& positiveSig b).testBit u.val = true
    rw [Nat.testBit_and,Bool.and_eq_true]
    exact ⟨(positive_has a u).mpr hz.1,(positive_has b u).mpr hz.2⟩
  | some v =>
    change (modelPos e u).testBit v.val = true
    rw [modelPos,base_bit _ _ v]
    exact (Finset.mem_filter.mp hz).2
def inverseNumBlock (i : ℕ) : ℕ := 0x5f2f75616b725727524c231f736a5626534d221e5e2e746077635d2d4f51211d71695525676f5a2b5b2a666e4b4a1b1a43373a4447394135171413113b454236463840341615121076625c2c504e201c706854246d6559296c645828494819183f33323e3d313c300f0d0e0c070a09050b06080403020100
def inverseNum (i : ℕ) := Nat.land (Nat.shiftRight (inverseNumBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def rowPermCodeBlock (i : ℕ) : ℕ := 0xc490d5a21e837b60c452a9d07e831b60e851a9d70c432b60e897d5a12c430b60e137b5a84c290d60e158a3b70c294d60c230b5a48e197d60c254a3b07e198d60c094d3b21e758a60c032b9d48e751a60e731b9d84c052a60e798d3b12c054a60e15a837b096c4d20e13b758a496c0d2096307584ae1cbd2096548370be1cad2090c4d3761eb5a82090367cd4aeb51820eb317cda49056820ebcad3716905482094c0d5861ea3b72094568cd0bea31720ea518cdb09436720eacbd581694307205ae18c4209d376b05ac24e8179d306b09dc04e8715a326b09de78c4025a316b090376c4da52e18b090cd4367152ea8b052316c4ad90e78b052ca4361790ed8b051ea8362097cd4b051326e8ad97c04b097306e8da51c24b097ed8360251ca4b05ac42e1873b906d05ae81c2403b976d03bc02e1785a946d03be71c2045a986d037906e1ba58c42d037eb1960458ca2d058946e1ab37c02d058ea1964037cb2d030976c2ba54e81d030cb2967854ea1d054ca2968730eb1d054986c2ab30e71d037e1b9064cd5a28037960eb1acd54280cd940eba13756280cdeab90463751280c45a290d736e1b80c49d052a136e7b8036512907dc4eab8036970521ac4edb8031e7b5264ca9d08031562eb7dca94080ca542ebd73196080caedb524631970809dc40e7813b526a09de87c0423b516a03be17c0249d586a03bc20e7189d546a094586c0db32e17a094cd0568132eb7a032516c0bd94e87a032cb0561894ed7a031eb7562498cd0a031526e7bd98c40a098546e7db31c20a098ed7564231cb0a058e1a9460cd3b27058964ea1bcd30270cd904eab15836270cdeba94065831270c09d432b156e8a70c03b294d856e1a7056312948dc0eba7056984321bc0eda7051e8a3260cb9d47051362ea8dcb90470cb302ead85196470cbeda32065198470e85a197d036c2b40e89d751a236c0b4036907512ae8cdb4036521970de8cab40ea581cbd03296740eacdb5186329074032c0b5168ea9d74032561cb0dea9874030c2b9768ed5a14030967cb2aed58140edcab97863052140ed987cba23056140c25a430b796e8d10c23b054a896e7d1096370548ac2ebd1096584307bc2ead1097e8d3062cb5a41097360ed8acb52410cbead30269758410cb320eda89756410caebd54269837010ca524edb7983601098e7d5462ca3b01098564ed7bca32010eb371cad45296800ebcda3176529480052c4a3167eb9d80052361ca4deb97800e79d831b256c4a00e73b198d456c2a0056948312be7cda0056321984de7cba0054c2a9867ed3b10054968ca2bed37100ed978cab25436100edcba9876543210
def rowPermCode (i : ℕ) := Nat.land (Nat.shiftRight (rowPermCodeBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
abbrev PIndex := Fin 120
def destVertex (pw i : ℕ) := (pw >>> (4*i)) &&& 15
def coord (p : PIndex) (v : V) : V := ⟨(destVertex (permNum p.val) v.val) % 10,by omega⟩
def inverseId (p : PIndex) : PIndex := ⟨inverseNum p.val % 120,by omega⟩
def coordRow (p : PIndex) (r : Fin 15) : Fin 15 := ⟨destVertex (rowPermCode p.val) r.val % 15,by omega⟩
lemma coord_value : ∀ p : PIndex, ∀ v : V, destVertex (permNum p.val) v.val = (coord p v).val := by
  decide +kernel
lemma coordInv : ∀ p : PIndex, ∀ v : V, coord (inverseId p) (coord p v) = v ∧
    coord p (coord (inverseId p) v) = v := by decide +kernel
lemma rowInv : ∀ p : PIndex, ∀ r : Fin 15, coordRow (inverseId p) (coordRow p r) = r ∧
    coordRow p (coordRow (inverseId p) r) = r := by decide +kernel
def vEquiv (p : PIndex) : Equiv.Perm V :=
  ⟨coord p,coord (inverseId p), fun v => (coordInv p v).1,fun v => (coordInv p v).2⟩
def rEquiv (p : PIndex) : Equiv.Perm (Fin 15) :=
  ⟨coordRow p,coordRow (inverseId p), fun r => (rowInv p r).1,fun r => (rowInv p r).2⟩
lemma permute_member (pw x j : ℕ) : (permuteBits pw x).testBit j = true ↔
    ∃ v : V, x.testBit v.val = true ∧ destVertex pw v.val = j := by
  let f m i := if x.testBit i then m ||| (1 <<< (destVertex pw i)) else m
  have go (xs : List ℕ) (a : ℕ) : (xs.foldl f a).testBit j = true ↔
      a.testBit j = true ∨ ∃ i ∈ xs, x.testBit i = true ∧ destVertex pw i = j := by
    induction xs generalizing a with
    | nil => simp
    | cons i ts ih =>
      simp only [List.foldl_cons,ih,List.mem_cons]
      cases e : x.testBit i <;> simp [f,e,Nat.one_shiftLeft,Nat.testBit_or,Nat.testBit_two_pow] <;> aesop
  change ((List.range 10).foldl f 0).testBit j = true ↔ _
  rw [go]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_range]
  exact ⟨fun ⟨v,hv,mem⟩ => ⟨⟨v,hv⟩,mem⟩,fun ⟨v,mem⟩ => ⟨v.val,v.isLt,mem⟩⟩
lemma permute_set (p : PIndex) (x : ℕ) :
    fsCode (permuteBits (permNum p.val) x) = (fsCode x).map (vEquiv p).toEmbedding := by
  ext v
  simp only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,permute_member]
  constructor
  · rintro ⟨w,bit,eq⟩
    exact ⟨w,bit,Fin.ext ((coord_value p w).symm.trans eq)⟩
  · rintro ⟨w,bit,rfl⟩
    exact ⟨w,bit,coord_value p w⟩
set_option maxRecDepth 10000 in
def prePermStep (p x d i : ℕ) : ℕ :=
  match Nat.testBit x i with
  | true => Nat.lor d (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight p (4*i)) 15))
  | false => d
def prePerm (p x : ℕ) : ℕ :=
  let d := 0
  let d := prePermStep p x d 0
  let d := prePermStep p x d 1
  let d := prePermStep p x d 2
  let d := prePermStep p x d 3
  let d := prePermStep p x d 4
  let d := prePermStep p x d 5
  let d := prePermStep p x d 6
  let d := prePermStep p x d 7
  let d := prePermStep p x d 8
  let d := prePermStep p x d 9
  d
lemma prePerm_eq (p x : ℕ) : prePerm p x = permuteBits p x := by
  have step : (fun d i : ℕ => if x.testBit i then d ||| (1 <<< ((p >>> (4*i)) &&& 15)) else d) =
      prePermStep p x := by
    funext d i
    cases e : x.testBit i <;> simp [prePermStep,e]
  rw [permuteBits,step]
  rfl
lemma preserveRows : ∀ p : PIndex, ∀ r : Fin 15,
    (rows r).map (vEquiv p).toEmbedding = rows (rEquiv p r) := by
  intro p r
  have all : preScan (fun q => preScan (fun j =>
      Nat.beq (prePerm (permNum q) (negNumber j))
        (negNumber (destVertex (rowPermCode q) j % 15))) 15) 120 = true := by decide +kernel
  have h : permuteBits (permNum p.val) (liftRow r).val = (liftRow (rEquiv p r)).val :=
    (prePerm_eq ..).symm.trans (Nat.eq_of_beq_eq_true (preScan_at (preScan_at all p.isLt) r.isLt))
  rw [← negNumber_spec r,← permute_set,← negNumber_spec (rEquiv p r),h]
lemma permute_bound (p : PIndex) (x : ℕ) : permuteBits (permNum p.val) x < 1024 := by
  by_contra! ge
  obtain ⟨i,large,hit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 10) ge
  obtain ⟨v,_,eq⟩ := (permute_member _ _ _).mp hit
  have e := (coord_value p v).symm.trans eq
  have := (coord p v).isLt
  omega
def chooseP (x : Fin 1024) : PIndex := ⟨firstKey x.val % 120,by omega⟩
def chooseRow (x : Fin 1024) : Fin 34 := ⟨firstKey x.val / 120 % 34,by omega⟩
set_option maxRecDepth 10000 in
lemma canonical_row : ∀ x : Fin 1024, permuteBits (permNum (chooseP x).val) x.val = repNum (chooseRow x).val := by
  intro x
  have all : preScan (fun v =>
    let key := firstKey v
    Nat.beq (prePerm (permNum (Nat.mod key 120)) v)
      (repNum (Nat.mod (Nat.div key 120) 34))) 1024 = true := by decide +kernel
  exact (prePerm_eq ..).symm.trans (Nat.eq_of_beq_eq_true (preScan_at all x.isLt))
lemma transfer_layout {a b : ℕ} {P} (c : capacity (fsCode a) (fsCode b) P)
    (h : layout (fsCode a) (fsCode b) P) (p : PIndex) :
    capacity (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (vertexMark (vEquiv p) P) ∧
    layout (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (vertexMark (vEquiv p) P) := by
  rw [permute_set,permute_set]
  exact ⟨Vcap (vEquiv p) c,Vlayout (vEquiv p) (rEquiv p) (preserveRows p) h⟩
lemma meets_insert_bits (a : ℕ) (v : V) (r : Fin 15) :
    meets (fsCode a) (insert v (rows r)) ↔ a.testBit v.val = true ∨ (negativeSig a).testBit r.val = true := by
  rw [negative_has]
  constructor
  · rintro ⟨u,ha,hu⟩
    rcases Finset.mem_insert.mp hu with rfl | hr
    · exact Or.inl (Finset.mem_filter.mp ha).2
    · exact Or.inr ⟨u,ha,hr⟩
  · rintro (hv | ⟨w,ha,hr⟩)
    · exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,Finset.mem_insert_self ..⟩
    · exact ⟨w,ha,Finset.mem_insert_of_mem hr⟩
lemma all_rows_bits : ∀ r : Fin 15, (32767 : ℕ).testBit r.val = true := by decide +kernel
lemma incidence_bound : ∀ v : V, incidence v.val < 2^15 := by decide +kernel
def signature (a b : ℕ) (v : V) := stableSig a b (negativeSig a) (negativeSig b) v.val
lemma stable_witness {a b : ℕ} {v : V} {r : Fin 15} (h : (signature a b v).testBit r.val = true) :
    stable (fsCode a) (fsCode b) r v := by
  have augment (x : ℕ) (e : meets (fsCode x) (insert v (rows r))) :
      (if x.testBit v.val then 32767 else negativeSig x).testBit r.val = true := by
    rcases (meets_insert_bits x v r).mp e with hit | old
    · simp [hit,all_rows_bits]
    · cases bit : x.testBit v.val <;> simp [bit,old,all_rows_bits]
  simp only [signature,stableSig,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,all_rows_bits,
    Bool.true_xor,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  constructor
  · intro mem
    have bit := (incidence_ok v r).mpr mem
    simp [bit] at h
  · rintro ⟨l,rr⟩
    have la := augment a l
    have rb := augment b rr
    rcases h.2 with off | ⟨p,q⟩
    · simp [la,rb] at off
    · exact ⟨(negative_has a r).mp p,(negative_has b r).mp q⟩
lemma overlap_row {a b y : ℕ} (v : V) (nz : signature a b v &&& y != 0) :
    ∃ r : Fin 15, (signature a b v).testBit r.val = true ∧ y.testBit r.val = true := by
  obtain ⟨i,_,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (n := 0) (x := signature a b v &&& y)
    (by have ne := bne_iff_ne.mp nz; omega)
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  have lt : i<15 := by
    by_contra! ge
    have p : 2^15 ≤ 2^i := Nat.pow_le_pow_right (by decide) ge
    have hi := Nat.testBit_lt_two_pow ((incidence_bound v).trans_le p)
    have no := Nat.testBit_lt_two_pow ((by decide : 32767 < 2^15).trans_le p)
    have z := bit.1
    simp [signature,stableSig,Nat.testBit_and,Nat.testBit_xor,hi,no] at z
  exact ⟨⟨i,lt⟩,bit⟩
lemma clique_check_sound {a b c : ℕ} {P} (check : validClique a b c = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) : False := by
  let xs := (List.range 10).filter (fun v => c.testBit v)
  let sig (v : ℕ) := (v,stableSig a b (negativeSig a) (negativeSig b) v,incidence v)
  have H := Bool.and_eq_true_iff.mp check
  have base := Bool.and_eq_true_iff.mp H.1
  have size : xs.length = 6 := beq_iff_eq.mp base.2
  have spec : (xs.map sig).all (fun v => (xs.map sig).all fun w => v.1 == w.1 ||
      (v.2.1 &&& w.2.1 != 0 && v.2.1 &&& w.2.2 != 0)) = true := H.2
  have atPos (i : Fin 6) : i.val<xs.length := by rw [size]; exact i.isLt
  let val (i : Fin 6) := xs[i.val]'(atPos i)
  have inList (i : Fin 6) : val i ∈ xs := List.getElem_mem (atPos i)
  have bounds (i : Fin 6) : val i < 10 := List.mem_range.mp (List.mem_filter.mp (inList i)).1
  let f (i : Fin 6) : V := ⟨val i,bounds i⟩
  have inj (i j : Fin 6) (ne : i ≠ j) : val i ≠ val j := by
    intro e
    have nd : xs.Nodup := (List.nodup_range (n := 10)).filter _
    exact ne (Fin.ext (nd.getElem_inj.mp e))
  have pair (i j : Fin 6) (ne : i ≠ j) :
      (signature a b (f i) &&& signature a b (f j) != 0) ∧
      (signature a b (f i) &&& incidence (f j).val != 0) := by
    have l := List.all_eq_true.mp spec (sig (val i)) (List.mem_map_of_mem (inList i))
    have rr := List.all_eq_true.mp l (sig (val j)) (List.mem_map_of_mem (inList j))
    simpa [sig,val,f,signature,show xs[i.val] ≠ xs[j.val] from inj i j ne] using rr
  apply six_conflict cp lh f
  · intro i
    have on := (List.mem_filter.mp (inList i)).2
    have bit := bitSub_use base.1 _ on
    simpa only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Nat.testBit_or,Bool.or_eq_true] using bit
  · intro i j ne
    have ij := pair i j ne
    have ji := pair j i ne.symm
    obtain ⟨r,rv,rw⟩ := overlap_row (f i) ij.1
    obtain ⟨s,sv,sw⟩ := overlap_row (f i) ij.2
    obtain ⟨t,tw,tv⟩ := overlap_row (f j) ji.2
    exact ⟨⟨r,stable_witness rv,stable_witness rw⟩,
      ⟨s,stable_witness sv,(incidence_ok _ _).mp sw⟩,
      ⟨t,stable_witness tw,(incidence_ok _ _).mp tv⟩⟩
abbrev EnvelopeId := Fin 201
def rejectsEnvelope (e : EnvelopeId) : Prop :=
  ∀ a b P, validEnv e.val a b = true →
    capacity (fsCode a) (fsCode b) P → layout (fsCode a) (fsCode b) P → False
lemma dirty_moves {a b : ℕ} (p : PIndex) (dirty : ∃ r, present (fsCode a) (fsCode b) (rows r) none) :
    ∃ r, present (fsCode (permuteBits (permNum p.val) a)) (fsCode (permuteBits (permNum p.val) b)) (rows r) none := by
  obtain ⟨r,hot⟩ := dirty
  refine ⟨rEquiv p r,?_⟩
  rw [permute_set,permute_set,←preserveRows]
  exact (present_push (vEquiv p) (fsCode a) (fsCode b) (rows r) none).mpr hot
def silentZero (m : Marks) : Prop := ∀ k b, m 0 k b = false
lemma silent_move {m : Marks} (h : silentZero m) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) :
    silentZero (moved m π sw) := fun k b => h (π k) (turn (sw k) b)
lemma silent_value {m : Marks} (h : silentZero m) : represented m 0 = 0 := by
  apply word_ext
  intro k b
  change (rawNumber m 0).val.testBit (slotNum (k,b)) = (0 : ℕ).testBit _
  rw [rawNumber_bit,h,Nat.zero_testBit]
lemma zero_set : fsCode 1 = {0} := by decide +kernel
lemma zero_present (U : Finset V) : present (fsCode 1) (fsCode 1) U none ↔ (0 : V) ∈ U := by
  simp [present,meets,zero_set]
lemma diagonal_limit : validEnv 199 1 1 = true := by decide +kernel
lemma diagonal_neg : ∀ r : Fin 15, (hotNum 199).testBit r.val = true ↔ (0 : V) ∈ rows r := by decide +kernel
lemma diagonal_pos : ∀ u : PositiveId, (pointNum 199).testBit u.val = true ↔ (0 : V) ∈ fsCode (liftPoint u).val := by decide +kernel
set_option maxRecDepth 10000 in
def prePoint (r : Fin 15) (v : V) : PositiveId :=
  ⟨(Nat.shiftRight 0xc57ee59ac0298000030deb55ead2014405d9d24044010403f016e6c7010e0007af00549719f3b00e9c80c600038680193100bf00000d59ae58ad500b0018274a0118044868370000f803668c989ed80003c700172c0262d0054911004000f94a50000000700182e4283a0000d00244078a98a000c14200060212426280000404000 (7*(10*r.val+v.val)) &&& 127) % 100,by omega⟩
lemma point_indices : ∀ r : Fin 15, ∀ v : V, v ∉ rows r → ∃ u : PositiveId,
    fsCode (liftPoint u).val = insert v (rows r) := by
  have good : ∀ (r : Fin 15) (v : V), v ∉ rows r →
      fsCode (liftPoint (prePoint r v)).val = insert v (rows r) := by decide +kernel
  intro r v notMem
  exact ⟨prePoint r v,good r v notMem⟩
def mergedZero (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P none s ∨ P (some 0) s
  | some v,s => v ≠ 0 ∧ P (some v) s
lemma diagonal_world {a b : ℕ} {P} (env : validEnv 199 a b = true)
    (cap : capacity (fsCode a) (fsCode b) P) (layout_ok : layout (fsCode a) (fsCode b) P) :
    ∃ m, world (fsCode 1) (fsCode 1) m ∧ silentZero m := by
  classical
  obtain ⟨O,R,M,uniq,avoid,refs,out,positive⟩ := layout_ok
  let m := marksFor (mergedZero P) M
  have capacity' : capacity (fsCode 1) (fsCode 1) (mergedZero P) := by
    intro v
    by_cases e : v=0
    · subst v
      refine ⟨∅,?_,by simp,by simp⟩
      simp [mergedZero]
    · obtain ⟨S,he,le,_⟩ := cap v
      refine ⟨S,fun k => ?_,le,?_⟩
      · simp [he,mergedZero,e]
      · simp [zero_set,e]
  refine ⟨m,⟨mergedZero P,O,R,M,capacity',⟨uniq,?_,refs,out,?_⟩,rfl⟩,?_⟩
  · intro r s z cut pos pr
    cases z with
    | none =>
      have v := (zero_present _).mp pr
      rcases pos with mem | mem
      · exact avoid r s none cut mem (compatible_hot env _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,(diagonal_neg r).mpr v⟩))
      · exact avoid r s (some 0) cut mem v
    | some v => exact avoid r s (some v) cut pos.2 pr
  · intro U pointU active closed
    apply positive U pointU active
    intro k both
    apply closed k
    intro d
    rcases both d with ⟨z,pz,pr⟩ | ref
    · cases z with
      | none =>
        refine Or.inl ⟨none,Or.inl pz,(zero_present _).mpr ?_⟩
        obtain ⟨r,v,hv,rs⟩ := pointU
        obtain ⟨u,eq⟩ := point_indices r v hv
        have e : U = fsCode (liftPoint u).val := rs.trans eq.symm
        rw [e] at pr ⊢
        apply (diagonal_pos u).mp
        have actual := compatible_pos env u none pr
        change (modelPos 199 u).testBit 10 = true at actual
        simpa only [modelPos,seed_bit] using actual
      | some v =>
        by_cases eq : v=0
        · subst v
          exact Or.inl ⟨none,Or.inr pz,(zero_present _).mpr pr⟩
        · exact Or.inl ⟨some v,⟨eq,pz⟩,pr⟩
    · exact Or.inr ref
  · intro k side
    change decide (mergedZero P (some 0) (k,side)) = false
    simp [mergedZero]
def permittedWorld (e : ℕ) (A B : Finset V) (m : Marks) : Prop :=
  if e=199 then world (fsCode 1) (fsCode 1) m ∧ silentZero m else world A B m
def actualStart (e : ℕ) : ℕ :=
  let d := initialPacked (suppNum e) (hotNum e)
  if e=199 then replacePacked d 0 1 else d
def incidentRows (v : V) := Finset.univ.filter (fun r : Fin 15 => v ∈ rows r)
lemma fiveIncident : ∀ v : V, (incidentRows v).card = 5 := by decide +kernel
lemma opposedSlots {A B P O R M} (h : rooted A B P O R M) (v : V)
    (hot : ∀ r, v ∈ rows r → present A B (rows r) none) :
    ∃ S : Finset (Fin 5), (∀ k, k ∈ S ↔ ∃ b, P (some v) (k,b) ∨ P none (k,b)) ∧ S.card ≤ 2 := by
  classical
  let S := Finset.univ.filter fun k : Fin 5 => ∃ b, P (some v) (k,b) ∨ P none (k,b)
  have mem (k : Fin 5) : k ∈ S ↔ ∃ b, P (some v) (k,b) ∨ P none (k,b) := by simp [S]
  refine ⟨S,mem,?_⟩
  let code (r : ↥(incidentRows v)) (k : ↥Sᶜ) := decide (M r.val (k.val,true))
  have inj : Function.Injective code := by
    intro r t eq
    by_contra ne
    have hr := (Finset.mem_filter.mp r.property).2
    have ht := (Finset.mem_filter.mp t.property).2
    have neq : r.val ≠ t.val := fun e => ne (Subtype.ext e)
    obtain ⟨k,b,mr,mt⟩ := apart_cut h (hot_apart neq (hot r.val hr))
    have idle : k ∉ S := by
      intro ks
      obtain ⟨d,hd⟩ := (mem k).mp ks
      by_cases side : d = b
      · subst d
        exact hd.elim (fun hz => h.2.1 _ _ _ mr hz hr) (fun hz => h.2.1 _ _ _ mr hz (hot _ hr))
      · have side' : d = !b := (show ∀ x y : Bool, x ≠ y → x = !y by decide) _ _ side
        rw [side'] at hd
        exact hd.elim (fun hz => h.2.1 _ _ _ mt hz ht) (fun hz => h.2.1 _ _ _ mt hz (hot _ ht))
    let i : ↥Sᶜ := ⟨k,Finset.mem_compl.mpr idle⟩
    have ee := congrFun eq i
    change decide (M r.val (k,true)) = decide (M t.val (k,true)) at ee
    have link := decide_eq_decide.mp ee
    cases b with
    | false => exact Bool.noConfusion (h.1 _ _ _ _ mr (link.mpr mt))
    | true => exact Bool.noConfusion (h.1 _ _ _ _ (link.mp mr) mt)
  have bound := Fintype.card_le_of_injective code inj
  simp only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool, fiveIncident,
    Finset.card_compl,Fintype.card_fin] at bound
  by_contra! lt
  have small : 5 - S.card ≤ 2 := by omega
  have bad := Nat.pow_le_pow_right (by decide : 0 < 2) small
  omega
def repaint (T : Finset V) (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P none s
  | some v,s => P (some v) s ∨ v ∈ T ∧ P none s
lemma changeFeature {A B X Y T : Finset V} {P : Feature → Slot → Prop}
    (support : ∀ v, v ∈ X ∨ v ∈ Y → (v ∈ A ∨ v ∈ B) ∧ v ∉ T)
    (neg : ∀ r, present X Y (rows r) none ∨ meets T (rows r) → present A B (rows r) none)
    (pos : ∀ U, point U → present A B U none → present X Y U none ∨ meets T U)
    (cap : capacity A B P) (lh : layout A B P) :
    capacity X Y (repaint T P) ∧ layout X Y (repaint T P) := by
  classical
  obtain ⟨O,R,M,h⟩ := lh
  change rooted A B P O R M at h
  constructor
  · intro v
    by_cases vt : v ∈ T
    · obtain ⟨S,mem,le⟩ := opposedSlots h v (fun r hr => neg r (Or.inr ⟨v,vt,hr⟩))
      refine ⟨S,fun k => ?_,le,fun hv => ((support v hv).2 vt).elim⟩
      simpa only [repaint,vt,true_and] using mem k
    · obtain ⟨S,mem,le,strict⟩ := cap v
      refine ⟨S,fun k => ?_,le,fun hv => strict (support v hv).1⟩
      simpa only [repaint,vt,false_and,or_false] using mem k
  · refine ⟨O,R,M,h.1,?_,h.2.2.1,h.2.2.2.1,?_⟩
    · intro r s z cut mark hit
      cases z with
      | none => exact h.2.1 _ _ _ cut mark (neg r (Or.inl hit))
      | some v =>
        rcases mark with pm | ⟨vt,pm⟩
        · exact h.2.1 _ _ _ cut pm hit
        · exact h.2.1 _ _ _ cut pm (neg r (Or.inr ⟨v,vt,hit⟩))
    · intro U hu a cl
      apply h.2.2.2.2 U hu a
      intro k both
      apply cl k
      intro d
      rcases both d with ⟨z,pm,hit⟩ | ref
      · cases z with
        | none =>
          rcases pos U hu hit with kept | ⟨v,vt,vu⟩
          · exact Or.inl ⟨none,pm,kept⟩
          · exact Or.inl ⟨some v,Or.inr ⟨vt,pm⟩,vu⟩
        | some v => exact Or.inl ⟨some v,Or.inl pm,hit⟩
      · exact Or.inr ref
def rawOnlyZero (P : Feature → Slot → Prop) : Feature → Slot → Prop
  | none,s => P (some 0) s
  | some v,s => v ≠ 0 ∧ P (some v) s
lemma emptyIntoDiagonal {P} (cap : capacity ∅ ∅ P) (lh : layout ∅ ∅ P) :
    capacity (fsCode 1) (fsCode 1) (rawOnlyZero P) ∧ layout (fsCode 1) (fsCode 1) (rawOnlyZero P) := by
  obtain ⟨O,R,M,uniq,avoid,ref,out,pos⟩ := lh
  constructor
  · intro v
    by_cases e : v=0
    · subst v
      exact ⟨∅,by simp [rawOnlyZero],by simp,by simp⟩
    · obtain ⟨S,mem,le,_⟩ := cap v
      exact ⟨S,fun k => by simp [rawOnlyZero,mem,e],le,by simp [zero_set,e]⟩
  · refine ⟨O,R,M,uniq,?_,ref,out,?_⟩
    · intro r s z cut pm hit
      cases z with
      | none => exact avoid r s (some 0) cut pm ((zero_present _).mp hit)
      | some v => exact avoid r s (some v) cut pm.2 hit
    · intro U hu act cl
      apply pos U hu act
      intro k both
      apply cl k
      intro b
      rcases both b with ⟨z,pm,hz⟩ | rd
      · cases z with
        | none => simpa [present,meets] using hz
        | some v =>
          by_cases e : v=0
          · subst v
            exact Or.inl ⟨none,pm,(zero_present _).mpr hz⟩
          · exact Or.inl ⟨some v,⟨e,pm⟩,hz⟩
      · exact Or.inr rd
def eraseMask (a t : ℕ) := a ^^^ (a &&& t)
lemma eraseMask_set (a t : ℕ) : fsCode (eraseMask a t) = fsCode a \ fsCode t := by
  ext v
  simp only [fsCode,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,eraseMask,
    Nat.testBit_xor,Nat.testBit_and]
  cases a.testBit v.val <;> cases t.testBit v.val <;> decide
lemma erasedMeets {A U T : Finset V} (hit : meets A U) (absent : ¬meets T U) : meets (A \ T) U := by
  obtain ⟨v,va,vu⟩ := hit
  exact ⟨v,Finset.mem_sdiff.mpr ⟨va,fun vt => absent ⟨v,vt,vu⟩⟩,vu⟩
lemma retainedMeets {A U T : Finset V} : meets (A \ T) U → meets A U := by
  rintro ⟨v,vt,vu⟩
  exact ⟨v,(Finset.mem_sdiff.mp vt).1,vu⟩
lemma eligibleRows {a b t : ℕ} (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (r : Fin 15) (ht : meets (fsCode t) (rows r)) : present (fsCode a) (fsCode b) (rows r) none := by
  have bit := bitSub_use ok _ ((negative_has _ r).mpr ht)
  change ((negativeSig a) &&& negativeSig b).testBit r.val = true at bit
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  exact ⟨(negative_has _ r).mp bit.1,(negative_has _ r).mp bit.2⟩
lemma strippedOrdinary {a b t : ℕ} {P}
    (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ Q, capacity (fsCode (eraseMask a t)) (fsCode (eraseMask b t)) Q ∧
      layout (fsCode (eraseMask a t)) (fsCode (eraseMask b t)) Q := by
  rw [eraseMask_set,eraseMask_set]
  refine ⟨_,changeFeature (T := fsCode t) ?_ ?_ ?_ cp lh⟩
  · intro v mem
    rcases mem with mem | mem
    · exact ⟨Or.inl (Finset.mem_sdiff.mp mem).1,(Finset.mem_sdiff.mp mem).2⟩
    · exact ⟨Or.inr (Finset.mem_sdiff.mp mem).1,(Finset.mem_sdiff.mp mem).2⟩
  · intro r hit
    rcases hit with ⟨ha,hb⟩ | ht
    · exact ⟨retainedMeets ha,retainedMeets hb⟩
    · exact eligibleRows ok r ht
  · intro U _ h
    by_cases ht : meets (fsCode t) U
    · exact Or.inr ht
    · exact Or.inl ⟨erasedMeets h.1 ht,erasedMeets h.2 ht⟩
lemma strippedLinear {a b t : ℕ} {P} (ok : bitSub (negativeSig t) (coldMask a b) = true)
    (cov : bitSub (positiveSig a &&& positiveSig b) (positiveSig t) = true)
    (cp : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ Q, capacity (fsCode 1) (fsCode 1) Q ∧ layout (fsCode 1) (fsCode 1) Q := by
  have step := @changeFeature (fsCode a) (fsCode b) ∅ ∅ (fsCode t) P
  have empty := step (by simp) (fun r hh => by
    rcases hh with hl | hr
    · simpa [present,meets] using hl
    · exact eligibleRows ok r hr) (fun U hu ht => by
      right
      obtain ⟨r,v,miss,rfl⟩ := hu
      obtain ⟨u,eq⟩ := point_indices r v miss
      rw [← eq] at ht ⊢
      have bit : (positiveSig a &&& positiveSig b).testBit u.val = true := by
        rw [Nat.testBit_and,Bool.and_eq_true]
        exact ⟨(positive_has _ u).mpr ht.1,(positive_has _ u).mpr ht.2⟩
      exact (positive_has _ u).mp (bitSub_use cov _ bit)) cp lh
  exact ⟨_,emptyIntoDiagonal empty.1 empty.2⟩
def routeEnvBlock (i : ℕ) : ℕ := 0xc8c7c6c3c0bdbcbbb8b7b4b3b1b0aeada7a6a1a09e9c9b9a989392908f8e8a85848382817f7e7d77767574716f6a6968676662605c5b5a585756555251504c4a4948464544433e3b37363332312e2c2524221e18161211100d0c0a09070601
def routeEnv (i : ℕ) := Nat.land (Nat.shiftRight (routeEnvBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
abbrev RouteId := Fin 95
def mappedEnv (c : RouteId) : EnvelopeId := ⟨routeEnv c.val % 201,by omega⟩
def routeBlock (c a b t : ℕ) : Bool :=
  let e := routeEnv c % 201
  bitSub (negativeSig t) (coldMask a b) &&
    (if e = 199 then bitSub (positiveSig a &&& positiveSig b) (positiveSig t)
     else validEnv e (eraseMask a t) (eraseMask b t))
lemma permitted_moves {e A B m} (h : permittedWorld e A B m) (π : Equiv.Perm (Fin 5)) (sw : Fin 5 → Bool) :
    permittedWorld e A B (moved m π sw) := by
  unfold permittedWorld at h ⊢
  by_cases eq : e=199 <;> simp only [eq,↓reduceIte] at h ⊢
  · exact ⟨move_world π sw h.1,silent_move h.2 π sw⟩
  · exact move_world π sw h
lemma permitted_exists {e a b : ℕ} {P} (en : validEnv e a b = true)
    (cap : capacity (fsCode a) (fsCode b) P) (lh : layout (fsCode a) (fsCode b) P) :
    ∃ m, permittedWorld e (fsCode a) (fsCode b) m := by
  by_cases eq : e=199
  · subst e
    obtain ⟨m,hm⟩ := diagonal_world en cap lh
    exact ⟨m,hm⟩
  · obtain ⟨O,R,M,root⟩ := lh
    exact ⟨marksFor P M,by
      rw [permittedWorld,if_neg eq]
      exact ⟨P,O,R,M,cap,root,rfl⟩⟩
lemma permitted_frame {e a b : ℕ} {m : Marks} (en : validEnv e a b = true)
    (w : permittedWorld e (fsCode a) (fsCode b) m) :
    ∃ O R, encLayout (modelNeg e) (modelPos e) (represented m) O R := by
  by_cases eq : e=199
  · subst e
    rw [permittedWorld,if_pos rfl] at w
    exact numeric_world _ _ (compatible_neg diagonal_limit) (compatible_pos diagonal_limit) w.1
  · rw [permittedWorld,if_neg eq] at w
    exact numeric_world _ _ (compatible_neg en) (compatible_pos en) w
set_option maxRecDepth 10000 in
lemma permitted_start {e a b : ℕ} {m : Marks} (en : validEnv e a b = true)
    (w : permittedWorld e (fsCode a) (fsCode b) m) : insidePacked (actualStart e) (represented m) := by
  by_cases eq : e=199
  · subst e
    rw [permittedWorld,if_pos rfl] at w
    have old := start_preserved _ _ (compatible_support diagonal_limit) (compatible_hot diagonal_limit) w.1
    have step := replacePacked_sound old (0 : Id)
    rw [silent_value w.2] at step
    change insidePacked (replacePacked _ 0 1) _
    exact step
  · rw [permittedWorld,if_neg eq] at w
    simpa only [actualStart,if_neg eq] using start_preserved _ _ (compatible_support en) (compatible_hot en) w
def rowHintsBlock (i : ℕ) : ℕ := (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => 0x1fffbcd003ffcd0003ffc00003ffc4001dffddb01effdf601f7fe6d01fbfe5401fdfec101feef0501ff7f3601ffbf7501ffdf8b01fee70001ffe79001fffbcd006ffc40006ffcf001bffdd501dffddb006ffc0001f7fe6001fbfe7e01fdfeeb01fef72201ff7f3601ffbf7501ffdf8b01ffef9701fef70001fffbc0005dfcc0005dfc4001bffdd5005cdc0001effdf601f7fe6d01fbfe44005cdc0001dcdc0001ff7f3601ffbf7501dcd40001ffef9701ffd78001fffbcd00fffcfa017ffcf001bffdd501cddc0001cffd4001f5fe6001fbfe7e01d5dc0001feff2201ff7f3601ffbf7501dddc8201ffef9701fff7ba01fffbc000fffcfa01682c0001bffdd501cfbd4001482c0001f7fe6d01680c0001680c0001680c0001680c0001480c0001f80e0001680c0001fff7ba01fffbcd00687c00007dfce801aff9c001dffddb00a8780001f0fa0800e078000060780000e0780000e87c2201ffbf6001ffdf8b01ffef8201fff7ba01a0f80000fffcfa015ddc89019fdd81010cdc0001cfdd8201f4de0901f8de0a0150dc0001d01c0001fe5f0201fe9f0101001c0001ffef9701fff7ba01fffbcd007dfcc0007dfc8801bffd8001dffddb01effdf601f0fe0801f3fe440074fc0001f4bc0001ff7f3601febf0001ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffc8801bffdd501dffdd001effdf601f7fe6d01fbfe7e01fdfee001febf2401ff7f3601febf0001ffdf8001ffef9701fff7ba01fffbcd007ff488007ff4b001bffdd501dffddb01effdc001f3fe2001f3fe4801fdfeeb01feff2f01ff770001ffbf7501ffdf8b01ffef97007f700001fff380005ddc88007ffcf001bffdd500cddc0001cfdd8001f1fe6001f1fe0800d1dc0001feff2201ff7f3601ffbf7500cddc8201ffef9701fff7ba01fffbc0005ddc80007ffcf001bffdd500dddc0001effdf601f1fe6001f1fe0000d1dc0001feff2201ff7f3601ffbf7500dddc8201ffef9701fff7ba01fffbc000fffcfa014ddc8001bffdd50149dc0001497c0001f7fe6d01c97c000149dc0001feff2801eb7c3001ffbf75015ddc8801ffef9001fff7ba01fffbcd006ffcd0006ffc8001bffdd501dffddb006f7c0001f7fe6d01fbfe5401fdfec101feff0501ef7d1401ffbf7501ffdf8b01ffef9701fff79001fffbcd00fffcfa017ffc8001bffdd501dffdd001effdf601f7fe6d01fbfc0001fdfee001feff2401ff7f3601ffbf7501ffdf8001ffef9701fff7ba01fffbcd00bffcd0017ffcfd00bffc8001dffddb01effdf601f7fe6d01fbbe5401fdfec101febf0501ff7f3601fabe0001ffdf8b01ffef9701fff79001fffbcd00fffcfa017dfcc901bffdd501cffd0001cffdc201f7fe6d01f9fe4a0179fc0001feff2f01ff7f0201ffbf4101ffdf8b01ffef9701fff7ba01fffbcd | false => (match Nat.blt i 2 with | true => 0x1ffe78001fffbc8007ffce8007ffcd001bffdd501dffdc901effde401f3fe4001f3fe6c01fdfeeb01fe7f0201fe7f2401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffcc2017ffcc501bffdd501dffddb01effdf601f7fe6d01fbfe4601fdfeeb01fefc0001ff7f3601ffbf7501ffdf8b01ffe78001ffe78201fffbcd00cffcc0017ffcfd01bffdd500cefc0000ce7c0001f7fe6d01fbfe4401fdfeeb01ce7c0001ee7d2401ffbf7501ffdf8b01ffe78001ffe78001fffbcd007ff8c80077f80001bffdd501dffddb01eff9c40173f84001f3fa4c01fdfeeb01fe7b0001fe7b0401ffbf7501ffdf8b01ffef9701fff38800627000007ffcc00077bc0001bffdd501dffddb01effdf60173bc4001f3be4401fdfeeb01febf0001ff7f360172bc0001ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffcf801bffdd001dffddb01effdf601f3fe6801f3fe4001fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcd001bffdd501dffddb01effde001f3fe4001f3fe6801fdfeeb01fe7f0201fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00fffcfa017efc0001bffdd501dffddb01effde001f7fe6d01fbfe6801fdfeeb017e7c0001fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00fffcfa0167b80001bffdd501dffddb016f38000173b84001f3ba4001fdfeeb01fe3b0001ee39000162380001ffdf8b01ffef9701fff7ba0162380000fffcfa017ffcf901bffdd501cdfc0001cffdc201f7fe6d01f9fe4a01d9fc0001feff2f01ff7f0201ffbb4101ffdf8b01ffef9701fff7ba01ffbb0000cdcc02017ffcfd018fad10008d8c00008d8c0001f5be6001fbfe7e00c58c0001feff2201ff7f360185ac0000cdcc82008d8c0001fff7ba01fffbc000fbfc72017bfc3401bffd1401dffd1201effdf601f3fe240071fc0001f9fe2201feff2f01ff7f3601ffbf7501ffdf8b01ffef9701fff70001fffb0400effc32016ffcb401bffdd501cffd92004efc0001f6fe2401fbfe7e01fdfea201e6dc0001ff7f3601ffbf7501fedf0201ffef9701fff7ba01fffb84006ffcf0006eec0001bffdd501dffdc1006e6c0001f7fe6d01fbfe6401fcce00016c4c0001ee6d0401ffbf7501fcce01016c4c0001fff7a001fffbcd007ffc30007ffc0001bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd007ffc40007ffcf801bffdd001dffddb01effdf601f7fe6801fbfe7e01fdfeeb01fef72a01ff7f3601ffbf7001ffdf8b01ffe79201fee70001fffbc800fffcd2017ffcd501bffdd501dffddb01effdf601f7fe4501fbfe5601fdfec301feef0701ff7f3601ffbf7501ffdf8b01fee70001ffe792 | false => 0x1ffef94006b540001fffbcd006bf430007ff49801bffdd501cffdd000cbf40001f3fe4c00e3f40001fdfee001feff2401ff7f3601ffb71001ffd78001ffef97006b940001fffbcd00fffcfa016ffcf401bffdd501cffdd2014ffc0001f7fe6501fbfe1001fdfee201feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc4006bf4300063f40001bffdd501cffdd00043f4000163fc440063f40001fdfee001feff2401ff7f3601ffbf7501ffd78001ffef97006bd40001fffbcd00ebfc32016ffcb401afbd1401cffd92000abc0001f2be2400e2bc0001fdfea201e2bc0001ff7f3601a2bc0001ffdf8b01ffef9701fff7ba01fffb84006bbc300062bc0001bffdd501cffd900042bc000162bc040062bc0001fdfea00162bc0001ff7f360062bc0001ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffc9901bff98101dffddb01effd9201f7fa4d01fbfe1a01fdfac001fefb0401ff7f3601ffbf1101ffdf8b01ffef9701fff7ba01b4f800007fe490007ff4b801bfe59001dffddb01effdf601f6fe2d01fbee1401fdee8101f6e40001ff7f3601ffb73001ffdf8b00b8e400003ea00001fff38800fffcfa017ffc9801bfe98001dffddb01effdf601f4fa0801fbfe7e01f4e80001f4e80001ff7f3601ffaf1001ffdf8b01bca80001fff7ba01b4e800006ff490006ff49001bffdd501dffddb006ef00001f6fa0501fbfe1401fdfa8101e6f00001ff7f3601ffbf7501ffdf8b01ffef97006ef00001e4f00000fffcfa017ffcb001bffdd501dffddb01effdf601f2fe2401f2fc0001fdfe8001f2fc0001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffb8000fffcfa016ffcb001bffdd501dffddb016afc0001f2fe2001e2fc0001fdfeeb01e2fc0001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffb8000fffcfa017ffcfc01bffdd401dffdda01effdf601f3fe6c01f3fe4001fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc006b7430006b740001bffdd501dffdd8006b740001f7fe6d006b740001fdfee801feff2c006b743001ffbf7501ffd78801ffef94006b540001fffbcd006b74100063740001bffdd501dffddb006374000163fc440063740001fdfec001fe7f04006a742001ffbf7501ffdf8b01ffe780006b640001fffbcd004ffcd0004ffcc001bffdd5004f9c00004f3c0001f7fe6d01fbbe5401fdfec101febf0501ef3d1401ca3c0001dfdd8101ffef9701fff79001fffbcd00fffcfa01433c0001bffdd5014b1c0001431c000163bc4401433c0001fdfec001fe3f04014a3c0001423c0001cfdd8001ffef9701fff7ba01fffbcd007ffcc0007ffcf801bffdd001dffddb01effdf601f3fe6801f3fe4401fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffe792)) | false => (match Nat.blt i 4 with | true => 0x1ffdf8b01ffef9701fff7ba01fffb80007bec00007ffcf001bfad1001dffddb01effdf601f3be6000f3ac0001fdfeeb01feff2201ff7f3601b3ac0001ffdf8b00bbac0001fff7ba01fffbc000fff4aa017ffced01bfed8501cfe58201cffdc201f6fe0901fbfe4a01fdfeeb01f6640001fe670201ffbf4101ffdf8b019e640000de640001fffbcd00fffcaa017ffcbd01bffd8501dffd8b01effda601f6fe0901fafe2e01fdfeeb01f2bc0001ff7f3601febf2501ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffc9901bfed8101dffddb01efed8201f4fe0901f8fe0a01f0ec0001f02c0001fe6f0201feaf0101ffdf8b01ac2c0001fff7ba01fffbcd0059fc00007dfce8019ffdc00099fc0001effdf601f1fe0800d1fc000051fc0001feff2f01ff7f3601ffbf6001ffdf8b01ffef8201fff7ba01fffbcd007ffcc8007ffcb801affd9001dffddb01affdc401f3fe2801f3fe4c01fdfeeb01feff2f01ff3f0401ff3f3001ffdf8b01ffef9701fff38801fff388007ffc88007ffcf801affdd001dffddb01affd8401f3fe6801f3fe0c01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc8007df488007df4a801afed8001dffddb01afed8401f7fe6d01fbfe0c007de40001feff2f01ff270001ff372001ffdf8b01ad6400007d240001fffbcd00fffcfa017ffcfc01affdd401dffdda01affd8001f3fe6c01f3fe0801fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffce801affdc001dffddb01ab7c0001f7fe6d01eb7c0001fdfe8801feff2f01eb7c2201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd00fffcfa017ffcf801affdd001dffddb01affd8001f3fe6801f3fe0801fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffca801afed8001dffddb01afed8001f7fe6d01fbfe0801fdfeeb01feff2f01ff2f0001ff3f2001ffdf8b01af6c0001fff7ba01fffbcd00fffcfa017ffc8801bffdd501dffdd801ebfc0001f7fe6d01ebfc0001fdfee801feff2c01ff7f3601ffbf0001ffdf8801ffef9401fff7ba01fffbcd007ffc88007fbc0001bffdd501dffddb01effd8001f7fe6d01fbfe0801fdfeeb01feff2801ff3f30017f3c0001ffdf8b01ffef9001fff7ba01fffbcd006b6400007ff48801bffdd501dffddb00eb640001f3f60800e3640001fdfeeb01feff2f00eb240001ff270001ffdf8b00eb24000063240001fffbcd00fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe1001fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc006b74300063740001bffdd501dffdd8006374000163fc440063740001fdfee801feff2c006b743001ffbf7501ffd788 | false => (match Nat.blt i 5 with | true => 0x1ffbf7501ffdf8b01ffe79001ffe79001fffbcd00fffcfa0135b8000135b84001dffddb01effdf60135b84001fbfe7e0135b80001feff2801ff7f360135b80001ffdf8b01ffef9001fff7ba0135b8000071f0000071f00001bffdd501dffddb01effdf60071f8400071f0000071f00001fef30001ff7f3601ffbf7501ffdf8b01ffef970078f0000070f00000fffcfa017ffce8019ff9c0019ffdd001effdf601f3fa4c01f3f80001fdfee001feff2401ff7f3601ffbf6001ffcb8001ffcf8201fff7ba01b3d80000fffcfa017bec0001bffdd501dffdd001effdf601f7fe6d017bec0001fdfee001feff2401ff7f3601ffbf7501ffcf80017bcc0001fff7ba01fffbcd007ffce0007ffcf8019ffdd0019ffdc101effdf601f3fe6801f3fe6401fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7a001fffbc800fffcfa017ffcf8019ffdd0019ffdc001effdf601f7fe6801fbfe7e01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffce001bffdd501dffc0001effdf601f7fe6d01fbfe7e01fdfeeb01feff2801ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00dae400017ffcfd01bffdd500dae40001effdf601f7fe6d00dae40001fdfeeb00dae40001ff7f3601ffbf7501ffdf8b00dae40000dae40001fffbcd007ffcf8007eec0001bffdd501decd0101ee6d0401f7fe6d01fbfe4401fcce01014c4c0001ee6d0401ffbf7501dcc400014c440001ffc78001fffbcd00fdfce2017ffc0501bffdd501dffd0101effdf601f7fe6d01fbfe0400fdfc0001feff2f01ff7f3601ffbf7501ffdf8b01ffef9701fff70001fffbcd00effc42017ffcf501afad1001dffddb00afac0001f7be6001fbfe7e01fdfeeb01fef72201ff7f3601a7ac0001ffdf8b01afa40001fee70201fffbc000fffcfa017ffcfd01bffdd501cffd5201cffdc201f7fe6d01f9fe4a01f9fe6201feff2f01ff5f0201ffbb4101ff5f0201ffef9701fff7ba01ffbb4400fffcfa017ffcfd01bffdd501cffdd201cffd4201f7fe6401fbfe7e01fdfee201feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc400fffcfa017ffcf901bffdd501dffddb01effd4201f23e2001f23c0001fdfeeb01f23c0001f23e0001f2380001ffdf8b01ffef9701fff7ba01ffbb4000fffcfa017ffcfc01afed9401cffdd2018bec0001f3fe6c01e3ec0001fdfee201feff2601ff7f3601ffaf0001ffcf8201ab8c0001fff7ba01fffbc400fffcfa017ffcbc01affd9401cffd92018b7c0001f3fe2c01e37c0001fdfea201feff2f01eb3c0001ff3f0001ffdf8b01ffef9701fff7ba01fffb8400fffc8a017ffcb901bffdd501dffddb01effd8201f6fe2901fafe0a01fdfeeb01f23c0001fe7f0201febf01 | false => 0x1ff3f3001373c0001ffdf8b01ffef8401fff7ba01fffbcd00fffcfa013fbc00012fbc4401dffdc801affdc001f7fe6d01fbfe4801fdfeeb01feff2f01ff3f20013f3c0001ffdf8b01ffef8401fff7ba01fffbcd00fffcfa017ffcc801bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf4001ffdf8801ffef9401fff7ba01fffbcd00fffcfa0136bc000137bc4401dffdc801effdf60136bc0001fbfe7e01fdfeeb0176bc0001ff7f360136bc0001ffdf8b01ffef8401fff7ba01fffbcd007ff488007ffcf801affdd001dffddb01affdc001f3fe6801f3fe4801fdfeeb01fef72a01ff773201ffbf7001ffdf8b01ffe79200fe640001fffbc800fffcfa017ffce801affdc001dffddb01ab7c0001f7fe6d01eb7c0001fdfeeb01feff0801eb7c3201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd006b7400007ffcc801bffdd501dffddb00eb740001f7fe6d00eb740001fdfeeb01fef72800eb743201ffbf4001ffdf8b01ffe79000ea640001fffbcd00eb7400017ffcfd01bffdd501dffddb00eb740001f7fe6d00eb740001fdfeeb01fef70800eb743001ffbf7501ffdf8b01ffe78000ea640001fffbcd007ffcc8003fac00012fac0001dffddb01affdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff2f04013f2c0001ffdf8b013f2c0001fff78801fffbcd00fffcfa012b2c00012b2c0001dffddb012b2c0001f7fe6d012b2c0001fdfeeb01feff2f012b2c00012b2c0001ffdf8b012b2c0001fff7ba01fffbcd00fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe5001fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc007ffcf8007ffcd001bffdd501dffdd901effdf401f7fe4501fbfe7c01fdfee901feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd00fffcfa0173fc0001bffdd501dffdd801effdf60173fc440173fc0001fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa016ffcf401bffdd501cffdd2014f7c0001f7fe6501fbfe5001fdfee201feff2701ef7d1001ffbf7501ffdf8201ffef9701fff7ba01fffbc4007ffcf0007ffcd001bffdd501dffdd101effdf601f7be4501fbbe7401fdfee101feff2701ff7f3601f3bc0001ffdf8101ffef9701fff7b001fffbcd00fffcfa01633c0001bffdd501cffdd001433c000163bc4401633c0001fdfee001fe3f24016a3c0001623c0001ffdf8001ffef9701fff7ba01fffbcd007ffcd0007ffcf801bffdd001dffddb01effdf601f7fe6d01fbfe5401fdfec101feff2f01ff7f3601ffbf7001ffdf8b01ffe79201ffe79001fffbc8007ffcd00077fc0001bffdd501dffddb01effdf60177fc4501fbfe5401fdfec101feff2d01ff7f36))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => 0x1feff2b01ff7f3601ffbf7101ffdf8b01ffef9301fff78001fffbc900ddf48a015ffcd101bffdd5005df40001effde001f5fe4101fbfe7a00d5f40001feff0301ff773001ffbf7501ffdf8b01ffef8100dd740001fffbcd00fffcfa017ffcc101bffdd501dffdd901effdf401f7fe6d01fbfe7e01fdfee901feff2d01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd00fffcca017ffcc501bffdd501dffddb01effde001f7fe6d01fbfe6e01fdfeeb01fe7c0001fe7f2401ffbf7501ffdf8b01ffef8101fff78201fffbcd00fffcfa017ffcc101bffdd501dffddb01effde001f7fe6d01fbfe6a01fdfeeb01fe7c0001fe7f2001ffbf7501ffdf8b01ffef8101fff7ba01fffbcd00ddf488017ffcfd01bffdd500dcf40001effde001f7fe6d01f9fe6800d8f40001dc740001fe772001ffbf7501ffdf8b01ffef8100dc740001fffbcd00effcf2017ffcc101bffdd501dffdd100ef3c0001f7fe6d01fbfe7601fdfee101febf2501ef3d1401ee3c0001ffdf8101ffef9701fff7b001fffbcd00effcd2017ffcc101bffdd501dffddb00ef3c0001f7fe6d01fbfe5601fdfec101febf0501ef3d1401ee3c0001ffdf8b01ffef9701fff79001fffbcd00fffcca017ff8c101bffdd501dffddb01eff9c001f7ba4101fbfe5e01fdfeeb01febb0101ff3f1401f6380001ffdf8b01ffef9701fff3800166b00000fffcfa017ff8c101bffdd501dffddb01ef780001f7fa4101fbfe5201fdfeeb01fefb0101ef7d1001ffbf7501ffdf8b01ffef9701fff7ba0166f80000dffcd8017ffcfd01bffdd500cfdc0001cffdc001f7fe6d01fbfe5c01fdfec101feff0501ff7f1401ffbf7501dfdd8101ffef9701fff79001fffbcd00effcc0017ffcfd01bffdd501dffddb00ee7c0001f7fe6d01fbfe4401fdfeeb01ee7c0001ee7d0401ffbf7501ffdf8b01ffef9701fff78001fffbcd00fffcfa017ffcfd01bffdd501dffddb01ee7c0001f7fe6d01fbfe4001fdfeeb01ee7c0001ee7d0001ffbf7501ffdf8b01ffef9701fff7ba01fffbcd007ffcf8007ffcc801bffdd501dffdd901effdf401f7fe6d01fbfe7c01fdfee901feff2d01ff7f3601ffbf4001ffdf8901ffef9501fff7b801fffbcd007ffce80036bc000137bc4501dffdc901effde40132bc0001f3fe6c01fdfeeb01763c0001fe3f2401363c0001ffdf8b01ffef8501fff7a801fffbcd00fffcfa017ffcfc01affdd401dffdda01affdc001f3fe6c01f3fe4801fdfeea01feff2e01ff7f3201ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017fbc0001bffdd501dffdd801effdc001f7fe6d01fbfe4801fdfee801feff2c01ff3f30017f3c0001ffdf8801ffef9401fff7ba01fffbcd00fffcfa0137bc000127bc4401dffdc801affdd00137bc4101fbfe5801fdfeeb01feff09 | false => (match Nat.blt i 8 with | true => 0x1fdfeeb01feff2a01ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbc000fffcfa017ffcf001bffdd501dffdd001effdf601f7fe6401fbfe7e01fdfee001feff2601ff7f3601ffbf7501ffdf8201ffef9701fff7ba01fffbc000fffcfa017ffcfd01bffdd501ddcc0001effdf601f7fe6d01fbfe7e01ddcc0001feff2001ff7f3601ffbf7501ddcc8001ddcc0001fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffdda01effd8201f7fe6d01fbfe0a01fdfeea01feff2e01ff7f3601ffbf7501ffdf8a01ffef9601fff7ba01fffbcc00eb7422017ffcec01affdc401dffdca00ab740001f3f60800e3740001fdfeeb01feff2f00eb742201ffbf6401ffdf8b01ffef8600e3740001fffbcd00fffc8a017ffcf901bffdd101dffddb01effd8201f7fe6901fbfe0a01fdfeeb01feff2a01ff7f3601ffbf7101ffdf8b01ffef9201fff7ba01fffbc800697c00007dfce801affdc001dffddb00a97c0001f1fe0800e17c0000617c0001feff2f00e97c2201ffbf6001ffdf8b01ffef8201fff7ba01fffbcd00fff48a017ffce901bff98101dffddb01effdc201f7fa0901fbfe4a01fdfeeb01feff2f01ff770201ffbf6101ffdf8b01ffef9700ff700001b7f00000fffcfa017ff88801aff98001dffddb01abf80001f3fa0801e3f80001fdfeeb01feff2f01ff7f3601ffbb0001ffdf8b01ffef9701fff7ba0123b80000dffc9a017ffcfd019ffd91008fdc0001cffd9201f7fe6d01fbfe1a01fdde8201fedf0201ff7f3601ffbf1101dcd80001ffef9701fff7ba01ffdb8000dffc92017ffcfd019ffdd0009fdc0001effdf601f7fe6d01fbfe1201fdde8201feff2a01ff7f3601ffbf7001dddc8a01ffef9201fff7ba01fffbc800fffc92017ffcf501bffdd501dffddb01effdf601f7be6501fbfe1201fdfe8201feff2201ff7f3601f7bc0001ffdf8b01ffef9701fff7ba01fffbc000fffcfa017ffcf101bffdd501dffddb01efbc0001f7be6101fbfe1201fdfeeb01feff0201ff7f3601e7bc0001ffdf8b01ffef9701fff7ba01fffb8000cdfc82017ffcb1018fbd10008dbc00008dbc0001f5be2101fbfe1200c5bc0001feff2f01ff7f360185bc0001ffdf8b01ffef9701fff7ba01fffb8000fffcfa017ffcb8019fed90019cec0001effdf601f4fe2801fbfe7e01d4ec0001d4ec0001ff7f3601ffbf3001ffdf8b019cec0001fff7ba01fffb8800fffcfa017ffcb801bffdd501dcdc0001effdf601f4fe2801fbfe7e01d4dc0001d4dc0001ff7f3601ffbf1001dcd80001ffef9701fff7ba01ffdb8000fffcfa015ffc9001bffdd5015cf80001effdf601f4fa0001fbfe7e01d4f80001d4f80001ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01d4f80000fffcca017ffcf901bffdd101dffddb01effdf201f7fe6901fbfe7e01fdfeeb | false => 0x1fbfe7e01fdfeea01feff2e01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00effcf2016ffcf401bffdd501cffdd2004f7c0001f7fe6501fbfe5401fdfee301feff2701ef7d1401ffbf7501ffdf8301ffef9701fff79001fffbc400fbf432017ffcd401bffdd501dffdd001effdf601f3fe4400f3f40001fdfee201feff2601ff7f3601ffbf7501ffd78001ffef9700fbd40001fffbcd00fffcf8017ffcfd01bffdd501dffdd001effdd401f7fe6d01fbfe5c01fdfee901feff2d01ff7f1401ffbf7501ffdf8101ffef9701fff79801fffbcd00fffcf0017ffcfd01bffdd501dffdd001effdf601f7fe6d01fbfe5401fdfee101feff2501ff7f3601ffbf7501ffdf8101ffef9701fff79001fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7e01fdfec001feff0401ff7f3601ffbf7501ffdf8b01ffef9701fff7ba01fffbcd007ffcf0007ffcf8019ffdd0019ffdd101effdf601f7fe6d01fbfe7401fdfee101feff2f01ff7f3601ffbf7001ffdf8b01ffef9201fff7b001fffbc800fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe7001fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcf801bffdd001dffddb01effdf601f7fe6901fbfe7001fdfeeb01feff2b01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc8007ffcf8007ffcf001bffdd501dffdd901effdf401f7fe6501fbfe7c01fdfee901feff2f01ff7f3401ffbf7501ffdf8b01ffef9501fff7b801fffbc000fffcfa017ffcf401bffdd501dffdd201effdf001f7fe6501fbfe7801fdfee201feff2f01ff7f3001ffbf7501ffdf8a01ffef9101fff7ba01fffbc400fffcfa017ffcf101bffdd501dffdd801effdf601f7fe6501fbfe7201fdfee801feff2f01ff7f3601ffbf7501ffdf8a01ffef9401fff7ba01fffbc100fffcfa017ffcfd01bffdd501dffdd001effdf001f7fe6d01fbfe7801fdfee001feff2d01ff7f3001ffbf7501ffdf8801ffef9101fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffdd801effdf601f7fe6d01fbfe7001fdfee801feff2d01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7001fdfeeb01feff2901ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00fffcfa017ffcf8019ffdd0019ffdd001effdf601f7fe6c01fbfe7e01fdfee001feff2e01ff7f3601ffbf7001ffdf8a01ffef9201fff7ba01fffbc800fffcfa017ffcf001bffdd501dffdd001effdf601f7fe6401fbfe7e01fdfee001feff2e01ff7f3601ffbf7501ffdf8a01ffef9001fff7ba01fffbc000fffcfa017ffcf001bffdd501dffddb01effdf601f7fe6001fbfe7e)) | false => (match Nat.blt i 10 with | true => 0x1f7fe6d01fbfe6c01fdfeeb01feff2f01ff7f2401ffbf7501ffdf8b01ffef8101fff78801fffbcd00fffcca017ffcc901bffdd501dffddb01effdc601f7fe6d01fbfe4e01fdfeeb01feff2f01ff7f0601ffbf4101ffdf8b01ffef9701fff78801fffbcd00fffcfa017fac0001bffdd501dffddb01effdc001f7fe6d01fbfe4801fdfeeb01feff2f01ff2f00017f2c0001ffdf8b017f2c0001fff7ba01fffbcd00fffcfa017ffccc01bffdd501dffdd801effdc401f7fe6d01fbfe4c01fdfee801feff2c01ff7f3601ffbf4401ffd78801ffef9401ffd78801fffbcd00fffcf8017ffcfd01bffdd501dffdd801effdc401f7fe6d01fbfe4c01fdfee801feff2c01ff7f3401ffbf7501ffd78801ffef9401ffd78801fffbcd00fffcfa017ffccc01bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf4401ffdf8801ffef9401fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdc901effde401f7fe6d01fbfe6c01fdfec801feff0c01ff7f3401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffce8017ffcfd01bffdd501dffdc801effdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff7f2401ffbf7501ffdf8b01ffef8401fff78801fffbcd00fffcfa017ffcfd01bffdd501dcec0001effdf601f7fe6d01fbfe7e01dcec0001dcec0001ff7f3601ffbf7501ffdf8b01dcec0001fff7ba01fffbcd00fffcd2017ffcfd01bffdd001dffddb01effdf601f7fe6d01fbfe5601fdfec301feff2f01ff7f3601ffbf7001ffdf8b01ffe79201ffe79201fffbc800fffcfa017ffcfd01bffdd401dffdda01effdf601f7fe6d01fbfe5201fdfeea01feff2f01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcfc01bffdd001dffddb01effdf601f7fe6c01fbfe7e01fdfec201feff2e01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7201fdfeca01feff2f01ff7f3601ffbf5401ffdf8b01ffef9701fff7ba01fffbc100fffcfa017ffcd001bffdd501dffddb01effdf601f3ba4001f3b80001fdfeeb01feff0201ff7f3601f3b80001ffdf8b01ffef9701fff7ba01f3b80000fffcf2017ffcfc01bffdd401dffdda01effdf601f7fe6d01fbfe5401fdfeeb01feff2f01ff7f3601ffbf7401ffdf8b01ffef9601fff79001fffbcc00fffcfa017ffcd401bffdd501dffdd901effdf401f7fe4501fbfe7c01fdfeeb01feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7b801fffbcd007ffcf00077fc0001bffdd501dffdd801effdf60177fc4501fbfe5401fdfee901feff2d01ff7f3601ffbf7501ffdf8901ffef9401fff79001fffbcd00fffcfa017ffcd401bffdd501dffdd801effdf601f7fe44 | false => (match Nat.blt i 11 with | true => 0x1effdf601f7fe6501fbfe7401fdfee301feff2701ff7f3601ffbf7501ffdf8301ffef9701fff7b001fffbc400fffcfa017ffcf401bffdd501dffdda01effdf601f7fe6401fbfe7e01fdfeea01feff2e01ff7f3601ffbf7501ffdf8a01ffef9401fff7ba01fffbc400fffcfa017ffcfd01bffdd501dffdd001effdf601f7fe6d01fbfe7e01fdfee001feff2401ff7f3601ffbf7501ffdf8001ffef9701fff7ba01fffbcd00fffcfa017ffcfc01bffdd501dffdda01effdf001f7fe6d01fbfe7801fdfeea01feff2f01ff7f3201ffbf7401ffdf8a01ffef9701fff7ba01fffbcc00fffcfa017ffcf801bffdd401dffdd801effdf601f7fe6c01fbfe7e01fdfee801feff2e01ff7f3601ffbf7001ffdf8a01ffef9601fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffdd801effdf001f7fe6d01fbfe7801fdfee801feff2d01ff7f3001ffbf7501ffdf8801ffef9501fff7ba01fffbcd00fffcfa017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe7e01fdfeeb01feff2801ff7f3601ffbf7501ffdf8b01ffef9001fff7ba01fffbcd00fffc8a017ffcfd01bffdd101dffddb01effdf601f7fe6901fbfe7e01fdfeeb01feff2b01ff7f3201ffbf7501ffdf8b01ffef9301fff7ba01fffbc900fdfc8a017ffcf901bffdc101dffddb01effdf201f5fe0901fbfe7a00f5fc0001feff2f01ff7f2201ffbf7101ffdf8b01ffef8301fff7ba01fffbcd00fffcfa017ffc8901bffd8101dffddb01effd8201f7fe6d01fbfe0a01fdfeeb01feff2f01ff7f0201ffbf0101ffdf8b01ffef9701fff7ba01fffbcd00fffcfa017ffcc901bffdd501dffdd901effdf601f7fe6d01fbfe7e01fdfee901feff2d01ff7f3601ffbf4101ffdf8901ffef9501fff7b801fffbcd00fffcea017ffcc901bffdc501dffdc901effdf601f7fe4901fbfe7e01fdfeeb01feff0901ff7f3601ffbf4101ffdf8b01ffef8501fff7a801fffbcd00fffce8017ffcfd01bffdd501dffdc901effdf401f7fe6d01fbfe7c01fdfeeb01feff0901ff7f3401ffbf7501ffdf8b01ffef8501fff7a801fffbcd00fffcca017ffcf901bffdd101dffddb01effdf601f7fe6901fbfe7e01fdfeeb01feff2b01ff7f3601ffbf7101ffdf8b01ffef9301fff78801fffbc9007ffcc8007fbc0001bffdd501dffddb01effdf401f7fe6d01fbfe7c01fdfeeb01feff2901ff3f34017f3c0001ffdf8b01ffef9101fff78801fffbcd00fffcfa013fbc00013fbc4101dffddb01effdf001f7fe6d01fbfe7801fdfeeb01feff0901ff3f30013f3c0001ffdf8b01ffef8101fff7ba01fffbcd00dffcca015ffcc9019ffdc1001ffc0001effde601f7fe6d01fbfe6e01fdfeeb01feff2f01ff7f2601ffbf4101ffdf8b01ffef8101fff78801fffbcd00fffcc8017ffcfd01bffdd501dffddb01effde4 | false => 0xfffcfa017ffc3401bffdd501dffd1201effdc401f7fe6d01fbfe4c01fdfe2201feff2f01ff7b0401ffbf7501ffdf8b01ffef9701fff78801ff7b0400fffcfa017ffcfc01bffdd401dffdda01effdf601f7fe6c01fbfe7e01fdfeea01feff2e01ff7f3601ffbf7401ffdf8a01ffef9601fff7ba01fffbcc00fffcfa017ffcfd01bffdd501dffdda01effdf201f7fe6d01fbfe7a01fdfeea01feff2f01ff7f3201ffbf7501ffdf8a01ffef9701fff7ba01fffbcd00fffcfa017ffcf801bffdd001dffddb01effdf601f7fe6801fbfe7e01fdfeeb01feff2a01ff7f3601ffbf7001ffdf8b01ffef9201fff7ba01fffbc800fffcfa017ffcfd01bffdd501dffdd801effdf601f7fe6d01fbfe7e01fdfee801feff2c01ff7f3601ffbf7501ffdf8801ffef9401fff7ba01fffbcd00fffcfa017ffccd01bffdd501dffdd901effdf601f7fe6d01fbfe7e01fdfee901feff2d01ff7f3601ffbf4501ffdf8901ffef9501fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdc901effdf401f7fe6d01fbfe7c01fdfec901feff0d01ff7f3401ffbf7501ffdf8b01ffef8501fff7b801fffbcd00fffcc8017ffcfd01bffdd501dffddb01effdc401f7fe6d01fbfe4c01fdfeeb01feff2f01ff7f0401ffbf7501ffdf8b01ffef9701fff78801fffbcd00fffcfa017ffcd501bffdd501dffdd901effdf401f7fe4501fbfe7e01fdfeeb01feff2f01ff7f3401ffbf7501ffdf8901ffef9501fff7ba01fffbcd00fffcf8017ffcfd01bffdd501dffdd101effdd401f7fe6d01fbfe7c01fdfee901feff2d01ff7f1401ffbf7501ffdf8101ffef9701fff7b801fffbcd00fffcd0017ffcfd01bffdd501dffddb01effdf601f7fe6d01fbfe5401fdfec101feff0501ff7f3601ffbf7501ffdf8b01ffef9701fff79001fffbcd00fffcf2017ffcfc01bffdd401dffddb01effdf601f7fe6d01fbfe7401fdfeeb01feff2f01ff7f3601ffbf7401ffdf8b01ffef9601fff7b001fffbcc00fffcf2017ffcf501bffdd501dffddb01effdf601f7fe6501fbfe7601fdfeeb01feff2f01ff7f3601ffbf7501ffdf8b01ffef9401fff7b201fffbc500fffcf2017ffcf401bffdd501dffdd3))))
def rowHints (i : ℕ) := Nat.land (Nat.shiftRight (rowHintsBlock (Nat.shiftRight i 8)) (Nat.shiftLeft (Nat.land i 255) 5)) 4294967295
def primitiveHintsBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x101102fd187d388d1a8140e07834220112650024100503ff187f788f7a9162f279364002327548ee121400fd187d188d1a9140f05834000112750024101502af182f288f000062a27826000a322548ae000c00af182f188f100140a25826000b1225002e100d03fe1c7e7c8e4a8040226d366b0a02644d2e3a1c03b91c397c890c0026307d302a0907200c280a88033a1c3a7c0a4d0045226d326b0a05204d2a080803bc183c788c18100030793408081334082c1a9c02bf1c3f7c8f5c1066327c36480a16344c2e181c02bf183f788f589062b27836488a103448ae189c03ff1c7f7c8f7f9166f27c366acb36754cee000002dd185d188d1a9142f058340ac912550000121100dd185d188d1a9100305810080912510808181903c7106f708f73810200512602011365000412cd00c7104f508f528140025006400312454006100503ff1c7f7c8f7f9126f03c342ac905200cec088803ff1c7f7c8f7f9145b23010498b153500c8189d03bf1c3f7c8f7f9106b01c300a8937314daa3a99039f103f708f739122b03010228933310088329901fe1c7e5c8e5f9000901814498a1534088c189c01ef1c6f5c8f5f8104a01c24088915250cac188d03ff1c7f7c8f7f9166f27c366acb04204cee088803ff1c7f7c8f7f9145b27812498b101148ca189d03bf1c3f5c8f5f9147b258124b8b1211488a1a9d01ce186e588e5b8040825806488a1004488e188c037f147f740e771062427006634a1244456e325c03631063200b23012362312221022120416a200002ff1c7f040c441066f07c34004836754cec005c03bf183f3887111063b279360102333549ae1014039b183358035b11431250100201133100001a1903ff1c7f1c8f1f9147f25d360bcb17750522121103ff1c7f3c8d7f9127f03d342bc905200dec088803ff1c7f7c8b7f9104307d32080937714dea3ad903ff0c7f4c8b5f9106304d320a0907710c280ad903ff187f388d7b9123f039340988113409ec189c033714375407771106301434020117350424121503771477700f77116372713641021134416e1014020b180350035a01420250024203120140021201021e181e380e3810203208022a0a0000082e08080337143774074001400240066303000545263215033f1c3f7c0f4d0104200c242a0905250c2c080d03ff1c7f7c8f5f8147e25d26630317654526120503fd1c7d7c8d1d9022d0381449c8105408cc18dc03771477740f32112272303641021034006e101403771477740f36112672343600021434046e101402571057700f521142725036424b12114002121103df187f788f5b91021059360a091375080c1add02ff1c7f7c8f5e9146f25c36420316754426121503ff0c6f7c8f6f8126206d262a0927650c2c2acd037f1c7f740f771142425006634b1245456e325d | false => 0x49cb1005408a02c903ef0c6f4c8f5f8142e240024bcb124540ca02c903ff1c7f7c8f7f9147e25d266bcb17654522120101af0c2f4c8f5d8145a24522498b152545aa008903fd1c7d7c8d3f9122f038346bc9000008ec088802df185f788f7a9162b248226acb020148ae0a8902dd185d388d3a9102e018242ac9120108a81a8902dd185d388d3a9122b038302ac9321108883a9903eb0c6b4c8b4f8102c008004bcb076108c80ac902cb084b488b4a8142c248024acb024148ca0ac903ff1c7f7c8f7f9166f27d366acb36754cee024003ff1c7f7c8f7f9145f27d3649cb177500401add00ff1c7f5c8f5e9144f25c3648cb16754422101103df187f788f7b9162d279364002325548ce125403ef1c6f7c8f7f8145e27d260001176504641acd00cf184f588f5a8140c25806400312454006100503ff1c7f7c8f7f9126707d362a4907600c6c0ac801ff1c7f5c8f5f9104705d36084917710c281ad9016e0c6e4c0e5f0045624d26494a05204d2a0808007c1c7c1c0c1e1004301c34080814340c2c181c02fe1c7e7c8e7e9064f24c22620206604426000002fb1c7b5c8b5e9146f25c32420316714422121103ff1c7f7c8f7f9167f2343422c9052004ec088803ff1c7f7c8f7f9167f2753663cb052045ee008803ff147f748f779167f2553643cb173145aa129902b914393489369126b034302289363104a8329903931c3350035311421050104201173100001a91037f1c7f540d56114670143402493775446c3a5d03eb186b28896b8123e039200988212049ea288803ff1c7f74067f9162c27806634232454dee325403ff1c7f788f7f9163f27936610233754dee301402af1c0f788e7c8162827806688a10044c8e388c02fb187b788b6a8162e278226202326148ea000002df185f788f400062c27806624a324548ce004c03bf1c3f7c8f1880228238066b8a10044dae3a9c02eb1c6b2c8b2e8126e23c22088a04200cea088803b91c397c89259160800000638930014da8329903bf1c3f7c8f008165b220266b8b35354dae3a9d033b1c3b7c0b4801400268026b0b00014d2a3a19027f147f340f341124720422224b0461046e004903ff1c7f7c8f4d8022d038146bcb056408cc08cc03ff1c7f7c8f3a9122f238366bcb052008ee088803791c797c090a01225008006b49074108480a4903ff1c7f7c8f7a9162f278366bcb327548ee000002df185f788f7a11627248026acb0241486e0a4903ff1c7f7c8f7a9162f278366bcb002048ee088803fb1c7b7c8b4a8162d248026bcb024148ca0ac902ff187f788f5a8142e258266acb12654022120103ef1c6f5c8f1a8102e218264bcb1201088a1a8902d918593889188100c018002ac9104108c818c903ff1c7f7c8f7e9166f27d366acb36754cee020000dd185d188d1a9140f0583408c91255) | false => (match Nat.blt i 3 with | true => 0x45f27d3649cb377545e2101103df187f788f7b9162d079360000337548cc12dc02fd1c7d3c8d3e9144f07c340001367544e4101503ff1c7f7c8f7f9162d07d3663c33775000432dd03ff1c7f7c8f7f9166f07d3622013775042432dd03ff1c7f7c8f7f9167327d366b0b37754d2e3a1d03ff1c7f7c8f7f9167f27d3622490760046c0ac803ff1c7f7c8f7f9167f27d366acb36754cee024003ff1c7f7c8f7f9167f27d366acb04204cee0ac803ff1c7f7c8f7f9167f27d3649ca177400481adc03ff1c7f7c8f7f9167f27d36414a325148ca125403ff1c7f7c8f7f9167f27d3648ca1674456a325103ff1c7f7c8f7f9167f27d36634b32514002325503ff1c7f7c8f7f9167f27d366acb36754422325103ff1c7f7c8f7f9167f27d366acb36314caa3ad903ff1c7f7c8f7f9167f27d36634b0760456e000003ff1c7f7c8f7f9167f27d36414a1770456a101003ff1c7f7c8f7f9167f27d3649ca15304dea189803ff1c7f7c8f7f9167f27d3641021774456e101403731473740b771167727532630337314522321103ff1c7f7c8f7a9162f278366bcb32754dee321002dd185d388d389160f000002ac9305548ec00c903ff1c7f7c8f3a9122f238366bcb00204dee3a98025f185f380f3811207208022a4b0041086e084903fc1c7c7c8c2d9020d008046bc800444dec3adc02fe187e788e488040e248266aca006448ee08cc03f7147774872200222275366302222445e6321403f71477748f361126727536224b262045ee220003ef1c6f7c8f3e0126627d26080a36244dee3a0c03ef186f788f7a8062a27926488a102449ee3a8c036f106f600f000022623126004a0064416e224c033b143b740b450067327532630b0520452a00080337143774075500672275366302152445261004033e143e740e551045327536410a1534452e101c03ff1c7f7c8f7f9127f03d346bc901204dec3add037d147d740d371105303130410910114148325d03ff1c7f7c8f7f9147f25d364bcb177541003add03bf1c3f7c8f7f9107b018104b893331498a3a9d03bf1c3f7c8f7f9147b258124b8b1211498a3a9d033d143d740d371127303010630932110008321d03cf186f788f7b8143c259260201136541043acd03cf186f788f7b81020059260a091365490c3acd03ee1c6e7c8e7f800080192449881124498c3acc03de187e788e7b9040925936488a1014498e3adc03f7147f748f77912210713663013375000432dd039f183f788f7b91229038142a893335088c3a9d039f183f788f7b91629278166a8b3215488e3a9d03ff1c7f7c8f7f9147e25d266bcb176500201acd01af0c2f4c8f5d8145a20000498b15250088188d03ff1c7f7c8f7f9162f278366bcb325548ee000003ef1c6f5c8f5f8142e258264bcb12454002120101ef0c6f4c8f5f8140a24522 | false => 0x3ff1c7f540e571062d07814434a377548cc125c03ff1c7f7c8f7f9167f27d366bcb37754dee000003ff1c7f7c8f7f9167f27d366bcb32554dee325503ff1c7f7c8f7f9167f27d366bcb05204dee088803ff1c7f7c8f7f9167f27d366bcb37754522321103ff1c7f7c8f7f9147e25d266bcb377545223add03ff1c7f7c8f7f91673275326bcb377500083add03ff1c7f7c8f7f9122d038146bcb377508cc3add03ff1c7f7c8f7f9145f27d3649cb377541c23add03ff1c7f7c8f7f9163d27d3663c3377500043add03ff1c7f7c8f7f9126307d362a0937750c2c3add03ff1c7f7c8f7f9167f27d362ac937754cec0ac803ff1c7f7c8f7f9167f27d3608c837754dea3ad903ff1c7f7c8f7f9167f27d36000037754cec1adc03ff1c7f7c8f7f9167f27d3649ca37754dea101003ff1c7f7c8f7f9167f27d36630337754526321503ff1c7f7c8f7f9167f27d366bcb325548ee124403ff1c7f7c8f7f9167f27d366bcb1764456e000003ff1c7f7c8f7f9167f27d366bcb32554002325503ff1c7f7c8f7f9167f27d366bcb37314daa3a9903ff1c7f7c8f3f9127f23d366bcb25104dee3add037f1c7f7c0f3d1125722d126b4b00414d6e3a5d03ff1c7f7c8f4a8142c248066bcb02454dee3add03ff1c7f7c8f7f9147e25d266bcb176545203add03ff1c7f7c8f7f9145a205206bcb152545a83add03ff1c7f7c8f7f9167b235306bcb373500883add03ff1c7f7c8f7f9127f03d346bcb05204dec3add03ef1c6f5c8f5f8107e01d244bcb172108881acd03ef0c6f4c8f5f8147a24d224bcb0201488a1acd03ff147f748f779107e0000063cb076145e832dd03ff1c7f7c8f7f9127f038106bcb377108c83add03ff1c7f7c8f7f9102c018046bcb17654dec3add03eb1c6b5c8b5f8142c258024bcb124148ca1ac903ff1c7f7c8f7f9142e058246bcb37754020120103ff1c7f7c8f7f9162f078346bcb37750000321103ff1c7f7c8f7f9147e25d266bcb37754522120103ff1c7f7c8f7f91673270306bcb377500083a1d03ff1c7f7c8f7f9162f030106bcb377500c832d9033b143b740b771167327532630b3731452a321903ff1c7f7c8f7f9126707d362a4927604dee2ac803ff1c7f7c8f7f9166f27d366acb36754dee224003ff1c7f7c8f7f9167727d366b4b27604dee080803ff1c7f7c8f7f9167627d366aca36744dee3a4d02ee1c6e7c8e7e8044a27c26488a14244cee188c03ff1c7f7c8f7f9166f07d362ac937754cec02c803ff1c7f7c8f7f9145f27d3649cb377540c01add01ff1c7f5c8f5f9144f05d3608c91775042012d903ff1c7f7c8f7f91))
def primitiveHints (i : ℕ) := Nat.land (Nat.shiftRight (primitiveHintsBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def unitCandidatesBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x80000000000000000000000000000000400000000000000000000000000000002000000000000000000000000000000010000000000000000008840000000000000000000000000000000000060100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000080000000000000000000000000190000000000000000000000000000000000000000000000000000000000000000900010000000000000000000000000006080000000000000000000000000000000000000000000000010000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000400000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000008000000000000000048800000000000000000000000000000000000002a0000000000000000000000000000000018400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006200000000000000000000000000000000000000000000000000000000000000140200000000000000000000000000000860000000000000010000000000000000000000000000000000000001000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000100000000000000000000000000000000800000000000000020000000000000000000000000000000000000004000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000040000000000000000000000000000000000000010000000000000000000000000000000000008000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001 | false => (match Nat.blt i 2 with | true => 0x500000000000000400000000000000000300000000000000010000000000000000000000000000000000000000000000001400000000000000040000000000000000000000000000000000000000000000032000000000000000000000000000000000000000000000000000000000000000c20000000000000000000000000000000000000000000000000000000800000000000000000000000000000000002000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000001000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000008000000000000000000000000000000004000000000000000000000000000000000400000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000000000000000000000000000000000000000a008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180000002000000000000000000000000100010000800000000000000000000000000000000000000000000000000000004200000020000000000000000000000030004000000000000000000000000000000000000000000000000000000000000c400000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000008000000000000000000000000000000004000000000000000000000000000000010000000000000000000000000000000080000000000000000000000000000000400000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000008000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000200000000000000000001000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000 | false => 0x5000000000000080000000000000000008000002000000040000000000000000018000000100000000000000000000000030000000000000200000000000000000050000004000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000004000000000000000000000000000000004000000000000000000000000000000008000000000000000000000000000000020000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000242000000000000000000000))
def unitCandidates (i : ℕ) := Nat.land (Nat.shiftRight (unitCandidatesBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def crossCandidatesBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1ae2f77060000000000000000000000002024010000000000000000000000000000f18018000000000000000000000000000e0004000000009b0004a8100002e200000860000000004d84048c200002b400001402000000000000079f20000000000077060000000000000488000000000000000000000000000005e95c00000000006af00000000000000000019302b586081402000000000000000000a94ae3851008600000000000000000000002a00000000000000000000000000000000184000000000000000000000000000001fd906af0000000000000000000000001ae2f77060000000000000000000000000000000000000000000000000000000000006200000000000000000000000000000008600000000000000000000000000000140200000000985001e154000140000002d000000000642003000000010000000100000000000000030000000000000001000000000000000181000000000000020000000000000001404000000000000080000000000000000001942110aa2e2504000000000000000000681100600000800000000000000000000003a800006200000000000000000000000000a800200000000000000000000000000060000080000000000000000000000000202401000000000000000000000000000000620000000000000000000000000000000000000000000000000000000000000002d0000000000000000000000000000025040000000080000020000000400000000000000000c00e0020000000400000000800000000000003e3f6000000000003d800000000000000a0100000000000004000000000000000600400000000000010000000000000000001a3ccc607100028000000000000000000200840001000000000000000000000000000c200000020000000000000000000000000051000200000000000000000000000000090001000000000000000000000000000f1801800000000000000000000000000000860000000000000000000000000000002d00000000000000000000000000000000000000000000000000000000000001c6b000000001f8e000c30000036000000030000000004800004000000100000000000000000000000140000000000000004000000000000000c20000000000000020000000000000014ca000000000000050000000000000000001000100008000000000000000000000018c410000800010000000000000000000000340000000200000000000000000000000082080400000000000000000000000000fb6ea585000000000000000000000000000e0004000000000000000000000000000014020000000000000000000000000000250400000000000000000000000000001c6b00000000000000000000000000000000 | false => 0x1480200000000000000000000000000a04000010000000000000000000000006010000000000000000000000000000000340000008000000000000000000000a94ae385100860000000000000000000681100600000800000000000000000002008400010000000000000000000000018c410000800010000000003000000000000020000000000000000018400000000000400000000000000002da4001f2000003c000000060000000009000008000000200000000000000000035000000c00000a0000000000000000000000000003000400000000000000000000000000014802000000000000000000000000000000000000000000000000000000000081008004000000000000000000000000e158ca1d90003000000000000000000007200c000300000000000000000000000002a0000000000000000000000000000003a8000062000000000000000000000000c20000002000000000000000000000003400000002000000058301002000a148c2051000200000000a408100000180000002000000000000000001531400000000aa2e2504000000000001248800000001840000000000000000018840080000001900000000000000000000000180000002000000000000000000000000a04000010000000000000000000000008100800400000000000000000000000000000000000000000000000000000000000000190000000000000000000000000000000a22000000000000000000000000000184000000000000000000000000000000a800200000000000000000000000000005100020000000000000000000000000820804000000000580508860046018400090001000000003403298400260340000608000000000000000db40c200000060648180000000000000a9e154000000609002d000000000000088400000000000000000000000000000000001e4f4001b62800000000000000000000060100000000000000000000000000000e158ca1d900030000000000000000000000000190000000000000000000000000000000000000000000000000000000000000000608000000000000000000000000001fd906af00000000000000000000000006000008000000000000000000000000000900010000000000000000000000000fb6ea58500000007007e180006003c000001800000000002002010000000200000000000000000000000500000000000000400000000000000007003200000000005000000000000000018000200000000008000000000000000000000042000000200000000000000000000000034000000800000000000000000000007200c000300000000000000000000000000000a2200000000000000000000000000000060800000000000000000000000000000000000) | false => (match Nat.blt i 3 with | true => 0x320000000000000000000000000000000c2000000000000000000000a24a0501400142010000e00040000000324325800c208340000048000000000002da4001f2000003c00000006000000000001531400000000aa2e2504000000000000db40c20000006064818000000000000050000000000000040000000000000000079f20000000000077060000000000000300000000000000010000000000000003e3f6000000000003d80000000000000014000000000000000400000000180000001000000000000000000000000c04000020000000000000000000000000000003200000000000000000000000000000000000000000000000000000000000000154000000000000000000000a0d84200c2013003400080002000000051800200010080800000000000000000009000008000000200000000000000000000124880000000184000000000000000000a9e154000000609002d000000000000070032000000000050000000000000000048800000000000000000000000000000181000000000000020000000000000000a01000000000000040000000000000000c200000000000000200000000005000000400000000000000000000000032000002000000000000000000000000000000c20000000000000000000000000000015400000000000000000000000000000000000000000000000000000b00b218000a04f400000280000000000100100800000010000000000000000000035000000c00000a0000000000000000000188400800000019000000000000000000884000000000000000000000000000001800020000000000800000000000000005e95c00000000006af000000000000001404000000000000080000000000000006004000000000000100000000000000014ca000000000000050000000f038e00000003cc06000000000000000a0080000000000000000000000000000a24a0501400142010000e00040000000a0d84200c20130034000800020000000b00b218000a04f400000280000000000000000000000000000000000000000000000000000000c400000000000000000000000000000300040000000000000000000000000180000002000000000000000000000001e4f4001b628000000000000000000000042000000200000000000000000000019302b586081402000000000000000001942110aa2e2504000000000000000001a3ccc6071000280000000000000000001000100008000000000005000000000000080000000000000000030002000000000400000000000000000324325800c208340000048000000000051800200010080800000000000000000100100800000010000000000000000000000000000000c4000000000000000000000000000000000000000000 | false => 0xe00000000000000000000000000003c7e0003f60000000000000000000000180000001000000000000000000000000050000004000000000000000000000f038e00000003cc06000000000000000500000000000008000000000000000000030000000000000200000000000000058301002000a148c2051000200000000580508860046018400090001000000007007e180006003c0000018000000000009b0004a8100002e20000086000000000985001e154000140000002d000000000800000200000004000000000000000001f8e000c300000360000000300000000000e000000000000000000000000000000000000000000000000000000000000242000000000000000000000000000000c0400002000000000000000000000000032000002000000000000000000000a00800000000000000000000000000003000200000000040000000000000000000184000000000004000000000000000a4081000001800000020000000000000340329840026034000060800000000002002010000000200000000000000000004d84048c200002b4000014020000000064200300000001000000010000000000c00e0020000000400000000800000000048000040000001000000000000000003c7e0003f6000000000000000000000024200000000000000000000000000000000000000000000000000000))
def crossCandidates (i : ℕ) := Nat.land (Nat.shiftRight (crossCandidatesBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def rawGroups (e : ℕ) (i : Id) : ℕ × ℕ × ℕ :=
  if i.val < 11 then
    let zer := if i.val < 10 then incidence i.val else hotNum e
    let hit := if i.val < 10 then primitiveHints (10*e+i.val) else 0
    (zer <<< 11,hit <<< 11,0)
  else
    let r := i.val-11
    let record := rowHints (15*e+r)
    let neg := negNumber r ||| (if (hotNum e).testBit r then 1024 else 0)
    (neg,record &&& 1023,(record >>> 10) <<< 11)
def groupWord (e : ℕ) (i : Id) (mode : Fin 3) := if mode.val=0 then (rawGroups e i).1
  else if mode.val=1 then (rawGroups e i).2.1 else (rawGroups e i).2.2
def hinted (e : ℕ) : Link := fun mode i j => (groupWord e i mode).testBit j.val
def testLink (e : ℕ) (mode : Fin 3) (i j : Id) : Bool :=
  !(hinted e mode i j) || generatedNet (modelNeg e) (modelPos e) mode i j
lemma link_meaning {e : ℕ} {mode : Fin 3} {i j : Id} (ok : testLink e mode i j = true)
    (edge : hinted e mode i j = true) : generatedNet (modelNeg e) (modelPos e) mode i j = true := by
  simpa only [testLink,edge,Bool.not_true,Bool.false_or] using ok
lemma hint_valid {e : ℕ} {w O R} (ok : ∀ m i j, testLink e m i j = true)
    (h : encLayout (modelNeg e) (modelPos e) w O R) : linkValid (hinted e) w := by
  obtain ⟨z,u,c⟩ := generated_valid h
  exact ⟨fun i j a => z i j (link_meaning (ok _ _ _) a),fun i j a => u i j (link_meaning (ok _ _ _) a),
    fun i j a => c i j (link_meaning (ok _ _ _) a)⟩
def eachBC (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k+1 => match f k with | true => eachBC f k | false => false
def hasBC (x y : ℕ) := match Nat.beq (Nat.land x y) 0 with | true => false | false => true
def bitBC (x p : ℕ) := x.testBit p
def witnessLimitBC (pw : ℕ) (hot : Bool) :=
  match hot with | true => 1267650600228229401496703205375
                 | false => Nat.land 1267650600228229401496703205375 (Nat.xor 1267650600228229401496703205375 pw)
def allowedUnitBC (hw pw r z : ℕ) := hasBC (unitCandidates (Nat.add (Nat.mul 10 r) z))
  (witnessLimitBC pw (bitBC hw r))
def allowedCrossBC (hw pw r s : ℕ) := hasBC (crossCandidates (Nat.add (Nat.mul 15 r) s))
  (witnessLimitBC pw (bitBC hw r || bitBC hw s))
def rowAllowedBC (e hw pw r : ℕ) :=
  let t := rowHints (Nat.add (Nat.mul 15 e) r)
  eachBC (fun z => match bitBC t z || bitBC (primitiveHints (Nat.add (Nat.mul 10 e) z)) r with
    | false => true
    | true => allowedUnitBC hw pw r z) 10 &&
  eachBC (fun s => match bitBC t (Nat.add 10 s) with
    | false => true
    | true => !(Nat.beq r s) && allowedCrossBC hw pw r s) 15
def testBC (c : ℕ) :=
  let e := Nat.mod (routeEnv c) 201
  let hw := hotNum e
  let pw := pointNum e
  eachBC (rowAllowedBC e hw pw) 15
lemma eachBC_at {f : ℕ → Bool} {n : ℕ} (h : eachBC f n = true) {k : ℕ} (b : k<n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases e : f n with
    | false => simp [eachBC,e] at h
    | true =>
      by_cases id : k=n
      · exact id ▸ e
      · exact ih (by simpa only [eachBC,e] using h) (by omega)
def baseUnitBC (r z : ℕ) :=
  let a := unitCandidates (Nat.add (Nat.mul 10 r) z)
  eachBC (fun u => match bitBC a u with
    | false => true
    | true => Nat.beq (Nat.land (posNumber u) (Nat.xor 2047 (negNumber r))) (Nat.shiftLeft 1 z)) 100
def baseCrossBC (r s : ℕ) :=
  let a := crossCandidates (Nat.add (Nat.mul 15 r) s)
  let n := Nat.lor (negNumber r) (negNumber s)
  eachBC (fun u => match bitBC a u with
    | false => true
    | true => Nat.beq (Nat.land (posNumber u) n) (posNumber u)) 100
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma baseUnitsBC : eachBC (fun r => eachBC (baseUnitBC r) 10) 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma baseCrossesBC : eachBC (fun r => eachBC (baseCrossBC r) 15) 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rowsValidBC : eachBC testBC 95 = true := by decide +kernel
lemma unitBaseBC {r : Fin 15} {z : FeatureId} {u : PositiveId} (bz : z.val<10)
    (h : (unitCandidates (10*r.val+z.val)).testBit u.val=true) :
    delta (liftPoint u).val (liftRow r).val = 1 <<< z.val := by
  have q := eachBC_at (eachBC_at (eachBC_at baseUnitsBC r.isLt) bz) u.isLt
  change (match (unitCandidates (10*r.val+z.val)).testBit u.val with | false => true | true => (delta (liftPoint u).val (liftRow r).val == 1 <<< z.val))=true at q
  rw [h] at q
  exact beq_iff_eq.mp q
lemma crossBaseBC {r s : Fin 15} {u : PositiveId}
    (h : (crossCandidates (15*r.val+s.val)).testBit u.val=true) :
    bitSub (liftPoint u).val ((liftRow r).val ||| (liftRow s).val) = true := by
  have q := eachBC_at (eachBC_at (eachBC_at baseCrossesBC r.isLt) s.isLt) u.isLt
  change (match (crossCandidates (15*r.val+s.val)).testBit u.val with | false => true | true => bitSub _ _)=true at q
  rwa [h] at q
lemma allowedWitnessBC {c pw : ℕ} {on : Bool}
    (h : hasBC c (witnessLimitBC pw on)=true) :
    ∃ u : PositiveId, c.testBit u.val = true ∧ (pw.testBit u.val = true → on = true) := by
  let n := c &&& witnessLimitBC pw on
  have nz : n ≠ 0 := by
    change (match n.beq 0 with | true => false | false => true) = true at h
    intro zero
    simp [zero] at h
  obtain ⟨k,_,hk⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (show 2^0 ≤ n by omega)
  have le : witnessLimitBC pw on ≤ 1267650600228229401496703205375 := by
    cases on with
    | false => exact Nat.and_le_left
    | true => rfl
  have nk : n < 2^100 := lt_of_le_of_lt (Nat.le_trans Nat.and_le_right le) (by decide +kernel)
  have bk : k < 100 := by
    by_contra! ge
    have z := Nat.testBit_lt_two_pow (lt_of_lt_of_le nk (Nat.pow_le_pow_right (by decide) ge))
    rw [z] at hk
    contradiction
  change (c &&& witnessLimitBC pw on).testBit k = true at hk
  rw [Nat.testBit_and] at hk
  obtain ⟨hc,hm⟩ := Bool.and_eq_true_iff.mp hk
  refine ⟨⟨k,bk⟩,hc,?_⟩
  intro hp
  cases on with
  | true => rfl
  | false =>
    have one : (1267650600228229401496703205375 : ℕ).testBit k=true := by
      change (2^100-1 : ℕ).testBit k=true
      exact (Nat.testBit_two_pow_sub_one ..).trans (decide_eq_true bk)
    change pw.testBit k = true at hp
    simp [witnessLimitBC,Nat.testBit_and,Nat.testBit_xor,one,hp] at hm
lemma liftedDeltaBC (a b : Fin 1024) (p q : Bool) (ok : p=true → q=true) :
    delta (a.val ||| (if p then 1024 else 0)) (b.val ||| (if q then 1024 else 0)) = delta a.val b.val := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases eq : k=10
  · subst k
    have za : a.val.testBit 10=false := Nat.testBit_lt_two_pow a.isLt
    have zb : b.val.testBit 10=false := Nat.testBit_lt_two_pow b.isLt
    cases p <;> cases q <;> simp_all [delta,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;> decide
  · have off : (1024 : ℕ).testBit k = false := Nat.testBit_two_pow_of_ne (Ne.symm eq)
    cases p <;> cases q <;> simp [delta,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,off]
lemma liftedCrossBC (a b c : Fin 1024) (p q t : Bool) (ok : p=true → (q || t)=true)
    (base : bitSub a.val (b.val ||| c.val)=true) :
    bitSub (a.val ||| (if p then 1024 else 0))
      ((b.val ||| (if q then 1024 else 0)) ||| (c.val ||| (if t then 1024 else 0)))=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro k
  have low := congrArg (fun n : ℕ => n.testBit k) (beq_iff_eq.mp base)
  change ((a.val &&& (b.val ||| c.val)).testBit k) = _ at low
  simp only [Nat.testBit_and,Nat.testBit_or] at low
  by_cases eq : k=10
  · subst k
    have za : a.val.testBit 10=false := Nat.testBit_lt_two_pow a.isLt
    have zb : b.val.testBit 10=false := Nat.testBit_lt_two_pow b.isLt
    have zc : c.val.testBit 10=false := Nat.testBit_lt_two_pow c.isLt
    cases p <;> cases q <;> cases t <;> simp_all [Nat.testBit_and,Nat.testBit_or]
  · have off : (1024 : ℕ).testBit k=false := Nat.testBit_two_pow_of_ne (Ne.symm eq)
    cases p <;> cases q <;> cases t <;> simpa [Nat.testBit_and,Nat.testBit_or,off] using low
lemma unitValidBC {e : ℕ} {r : Fin 15} {z : FeatureId} (bz : z.val<10)
    (h : allowedUnitBC (hotNum e) (pointNum e) r.val z.val=true) :
    unitLink (modelNeg e) (modelPos e) r z=true := by
  obtain ⟨u,hu,live⟩ := allowedWitnessBC h
  apply List.any_eq_true.mpr
  refine ⟨u,List.mem_finRange _,beq_iff_eq.mpr ?_⟩
  exact (liftedDeltaBC _ _ _ _ live).trans (unitBaseBC bz hu)
lemma crossValidBC {e : ℕ} {r s : Fin 15} (ne : r ≠ s)
    (h : allowedCrossBC (hotNum e) (pointNum e) r.val s.val=true) :
    crossLink (modelNeg e) (modelPos e) r s=true := by
  obtain ⟨u,hu,live⟩ := allowedWitnessBC h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa using ne,List.any_eq_true.mpr ⟨u,List.mem_finRange _,?_⟩⟩
  exact liftedCrossBC _ _ _ _ _ _ live (crossBaseBC hu)
lemma primalDeclarationBC (e : ℕ) (z : FeatureId) : rawGroups e (primal z) =
    ((if z.val<10 then incidence z.val else hotNum e) <<< 11,
    (if z.val<10 then primitiveHints (10*e+z.val) else 0) <<< 11,0) := by
  simp [rawGroups,primal,z.isLt] <;> exact ⟨rfl,rfl⟩
lemma dualDeclarationBC (e : ℕ) (r : Fin 15) : rawGroups e (dual r) =
    (modelNeg e r, rowHints (15*e+r.val) &&& 1023, (rowHints (15*e+r.val) >>> 10) <<< 11) := by
  simp [rawGroups,dual,modelNeg,liftRow]
lemma jumpBC (word r : ℕ) : (word <<< 11).testBit (11+r)=word.testBit r := by
  simp [Nat.testBit_shiftLeft]
lemma lowJumpBC (word z : ℕ) (small : z<11) : (word <<< 11).testBit z=false := by
  simp [Nat.testBit_shiftLeft,Nat.not_le.mpr small]
lemma limitNegBC (e : ℕ) (r : Fin 15) : modelNeg e r < 2^11 := by
  apply Nat.or_lt_two_pow
  · exact (liftRow r).isLt.trans (by decide)
  · cases (hotNum e).testBit r.val <;> decide
lemma groupZeroBC (e : ℕ) (i : Id) : groupWord e i 0=(rawGroups e i).1 := rfl
lemma groupOneBC (e : ℕ) (i : Id) : groupWord e i 1=(rawGroups e i).2.1 := rfl
lemma groupTwoBC (e : ℕ) (i : Id) : groupWord e i 2=(rawGroups e i).2.2 := rfl
lemma skipPrimalBC (e : ℕ) (m : Fin 3) (z t : FeatureId) : hinted e m (primal z) (primal t)=false := by
  change (groupWord e (primal z) m).testBit t.val=false
  fin_cases m
  · change (rawGroups e (primal z)).1.testBit t.val=false
    rw [primalDeclarationBC,lowJumpBC _ _ t.isLt]
  · change (rawGroups e (primal z)).2.1.testBit t.val=false
    rw [primalDeclarationBC,lowJumpBC _ _ t.isLt]
  · change (rawGroups e (primal z)).2.2.testBit t.val=false
    rw [primalDeclarationBC]
    exact Nat.zero_testBit _
private lemma incidenceRowsBC : ∀ z : Fin 10, ∀ r : Fin 15,
    (incidence z.val).testBit r.val=(negNumber r.val).testBit z.val := by decide +kernel
lemma forwardZeroBC (e : ℕ) (z : FeatureId) (r : Fin 15)
    (h : hinted e 0 (primal z) (dual r)=true) : (modelNeg e r).testBit z.val=true := by
  change (groupWord e (primal z) 0).testBit (11+r.val)=true at h
  simp only [groupZeroBC,groupOneBC,groupTwoBC,primalDeclarationBC,jumpBC] at h
  by_cases lt : z.val<10
  · rw [if_pos lt,incidenceRowsBC ⟨z.val,lt⟩ r] at h
    exact (base_bit (liftRow r) _ ⟨_,lt⟩).trans h
  · have eq : z.val=10 := by have := z.isLt; omega
    rw [if_neg lt] at h
    rw [eq]
    exact (seed_bit (liftRow r) _).trans h
lemma unitRowBC (c : RouteId) (r : Fin 15) (z : FeatureId) (bd : z.val<10)
    (hit : (rowHints (15*(mappedEnv c).val+r.val)).testBit z.val = true ∨
      (primitiveHints (10*(mappedEnv c).val+z.val)).testBit r.val = true) :
    unitLink (modelNeg (mappedEnv c)) (modelPos (mappedEnv c)) r z = true := by
  have h := eachBC_at (eachBC_at rowsValidBC c.isLt) r.isLt
  have good := eachBC_at (Bool.and_eq_true_iff.mp h).1 bd
  have yes := Bool.or_eq_true_iff.mpr hit
  change (match bitBC (rowHints (15*(mappedEnv c).val+r.val)) z.val ||
      bitBC (primitiveHints (10*(mappedEnv c).val+z.val)) r.val with
      | false => true | true => allowedUnitBC _ _ _ _)=true at good
  change (bitBC _ _ || bitBC _ _)=true at yes
  rw [yes] at good
  exact unitValidBC bd good
lemma crossRowBC (c : RouteId) (r s : Fin 15)
    (hit : (rowHints (15*(mappedEnv c).val+r.val)).testBit (10+s.val)=true) :
    crossLink (modelNeg (mappedEnv c)) (modelPos (mappedEnv c)) r s=true := by
  have h := eachBC_at (eachBC_at rowsValidBC c.isLt) r.isLt
  have good := eachBC_at (Bool.and_eq_true_iff.mp h).2 s.isLt
  change (match bitBC (rowHints (15*(mappedEnv c).val+r.val)) (10+s.val) with | false => true | true => !_ && _)=true at good
  change bitBC _ _=true at hit
  rw [hit] at good
  obtain ⟨ne,pass⟩ := Bool.and_eq_true_iff.mp good
  apply crossValidBC _ pass
  intro eq
  subst s
  simp at ne
lemma forwardUnitBC (c : RouteId) (z : FeatureId) (r : Fin 15)
    (h : hinted (mappedEnv c) 1 (primal z) (dual r)=true) :
    unitLink (modelNeg (mappedEnv c)) (modelPos (mappedEnv c)) r z=true := by
  change (groupWord _ (primal z) 1).testBit (11+r.val)=true at h
  simp only [groupZeroBC,groupOneBC,groupTwoBC,primalDeclarationBC,jumpBC] at h
  by_cases bd : z.val<10
  · exact unitRowBC c r z bd (Or.inr (by simpa only [if_pos bd] using h))
  · simp [bd] at h
lemma reverseUnitBC (c : RouteId) (r : Fin 15) (z : FeatureId)
    (h : hinted (mappedEnv c) 1 (dual r) (primal z)=true) :
    unitLink (modelNeg (mappedEnv c)) (modelPos (mappedEnv c)) r z=true := by
  change (groupWord _ (dual r) 1).testBit z.val=true at h
  simp only [groupZeroBC,groupOneBC,groupTwoBC,dualDeclarationBC,Nat.testBit_and] at h
  have pair := Bool.and_eq_true_iff.mp h
  have small := pair.2
  change (2^10-1 : ℕ).testBit z.val=true at small
  rw [Nat.testBit_two_pow_sub_one] at small
  exact unitRowBC c r z (of_decide_eq_true small) (Or.inl pair.1)
lemma reverseZeroBC (e : ℕ) (r : Fin 15) (z : FeatureId)
    (h : hinted e 0 (dual r) (primal z)=true) : (modelNeg e r).testBit z.val=true := by
  change (groupWord e (dual r) 0).testBit z.val=true at h
  simpa only [groupZeroBC,groupOneBC,groupTwoBC,dualDeclarationBC] using h
lemma safeGeneratedBC (c : RouteId) (m : Fin 3) (i j : Id)
    (h : hinted (mappedEnv c) m i j=true) :
    generatedNet (modelNeg (mappedEnv c)) (modelPos (mappedEnv c)) m i j=true := by
  obtain ⟨z,rfl⟩|⟨r,rfl⟩ := id_cases i <;> obtain ⟨t,rfl⟩|⟨s,rfl⟩ := id_cases j
  · rw [skipPrimalBC] at h
    contradiction
  · simp only [generatedNet,at_primal,at_dual]
    fin_cases m
    · exact forwardZeroBC _ z s h
    · exact forwardUnitBC c z s h
    · change (groupWord _ (primal z) 2).testBit (11+s.val)=true at h
      simp [groupTwoBC,primalDeclarationBC] at h
  · simp only [generatedNet,at_primal,at_dual]
    fin_cases m
    · exact reverseZeroBC _ r t h
    · exact reverseUnitBC c r t h
    · change (groupWord _ (dual r) 2).testBit t.val=true at h
      simp [groupTwoBC,dualDeclarationBC,lowJumpBC _ _ t.isLt] at h
  · simp only [generatedNet,at_dual]
    fin_cases m
    · change (groupWord _ (dual r) 0).testBit (11+s.val)=true at h
      have off := Nat.testBit_lt_two_pow ((limitNegBC (mappedEnv c) r).trans_le
        (Nat.pow_le_pow_right (by decide) (show 11≤11+s.val by omega)))
      simp [groupZeroBC,dualDeclarationBC,off] at h
    · change (groupWord _ (dual r) 1).testBit (11+s.val)=true at h
      have off : (1023 : ℕ).testBit (11+s.val)=false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1023<2^11)
          (Nat.pow_le_pow_right (by decide) (show 11≤11+s.val by omega)))
      simp [groupOneBC,dualDeclarationBC,Nat.testBit_and,off] at h
    · change (groupWord _ (dual r) 2).testBit (11+s.val)=true at h
      simp only [groupZeroBC,groupOneBC,groupTwoBC,dualDeclarationBC,jumpBC,Nat.testBit_shiftRight] at h
      exact Bool.and_eq_true_iff.mpr ⟨rfl,crossRowBC c r s (by simpa only [Nat.add_comm] using h)⟩
lemma chosenNet (c : RouteId) (m : Fin 3) (i j : Id) :
    testLink (mappedEnv c).val m i j = true := by
  cases edge : hinted (mappedEnv c) m i j with
  | false => simp only [testLink,edge,Bool.not_false,Bool.true_or]
  | true => simpa only [testLink,edge,Bool.not_true,Bool.false_or] using safeGeneratedBC c m i j edge
def growUp (d : ℕ) : ℕ :=
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol0) 1)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol1) 2)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol2) 4)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol3) 8)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol4) 16)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol5) 32)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol6) 64)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol7) 128)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol8) 256)
  let d := Nat.lor d (Nat.shiftLeft (Nat.land d ncol9) 512)
  d
def growDown (d : ℕ) : ℕ :=
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col0) 1)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col1) 2)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col2) 4)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col3) 8)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col4) 16)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col5) 32)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col6) 64)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col7) 128)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col8) 256)
  let d := Nat.lor d (Nat.shiftRight (Nat.land d col9) 512)
  d
def bitMap00 (i : ℕ) : ℕ := Nat.mul (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0x55555555) | false => (match Nat.blt i 3 with | true => 0x33333333 | false => 0x77777777)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xf0f0f0f | false => 0x5f5f5f5f) | false => (match Nat.blt i 7 with | true => 0x3f3f3f3f | false => 0x7f7f7f7f))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xff00ff | false => 0x55ff55ff) | false => (match Nat.blt i 11 with | true => 0x33ff33ff | false => 0x77ff77ff)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xfff0fff | false => 0x5fff5fff) | false => (match Nat.blt i 15 with | true => 0x3fff3fff | false => 0x7fff7fff)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffff | false => 0x5555ffff) | false => (match Nat.blt i 19 with | true => 0x3333ffff | false => 0x7777ffff)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xf0fffff | false => 0x5f5fffff) | false => (match Nat.blt i 23 with | true => 0x3f3fffff | false => 0x7f7fffff))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffff | false => 0x55ffffff) | false => (match Nat.blt i 27 with | true => 0x33ffffff | false => 0x77ffffff)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xfffffff | false => 0x5fffffff) | false => (match Nat.blt i 31 with | true => 0x3fffffff | false => 0x7fffffff))))) 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001
def bitMap05 (i : ℕ) : ℕ := (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => ncol5) | false => (match Nat.blt i 3 with | true => ncol6 | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => ncol7 | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 7 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => ncol8 | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 11 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 15 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => ncol9 | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 19 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 23 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 27 with | true => 0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) | false => (match Nat.blt i 31 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))))
def bitMap10 (i : ℕ) : ℕ := Nat.mul (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => 0xaaaaaaaa) | false => (match Nat.blt i 3 with | true => 0xcccccccc | false => 0xeeeeeeee)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xf0f0f0f0 | false => 0xfafafafa) | false => (match Nat.blt i 7 with | true => 0xfcfcfcfc | false => 0xfefefefe))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0xff00ff00 | false => 0xffaaffaa) | false => (match Nat.blt i 11 with | true => 0xffccffcc | false => 0xffeeffee)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xfff0fff0 | false => 0xfffafffa) | false => (match Nat.blt i 15 with | true => 0xfffcfffc | false => 0xfffefffe)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => 0xffff0000 | false => 0xffffaaaa) | false => (match Nat.blt i 19 with | true => 0xffffcccc | false => 0xffffeeee)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xfffff0f0 | false => 0xfffffafa) | false => (match Nat.blt i 23 with | true => 0xfffffcfc | false => 0xfffffefe))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffff00 | false => 0xffffffaa) | false => (match Nat.blt i 27 with | true => 0xffffffcc | false => 0xffffffee)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xfffffff0 | false => 0xfffffffa) | false => (match Nat.blt i 31 with | true => 0xfffffffc | false => 0xfffffffe))))) 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001
def bitMap15 (i : ℕ) : ℕ := (match Nat.blt i 16 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x0 | false => col5) | false => (match Nat.blt i 3 with | true => col6 | false => 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => col7 | false => 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 7 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => col8 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 11 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 15 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)))) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 20 with | true => (match Nat.blt i 18 with | true => (match Nat.blt i 17 with | true => col9 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 19 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 21 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 23 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000))) | false => (match Nat.blt i 28 with | true => (match Nat.blt i 26 with | true => (match Nat.blt i 25 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) | false => (match Nat.blt i 27 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000)) | false => (match Nat.blt i 30 with | true => (match Nat.blt i 29 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) | false => (match Nat.blt i 31 with | true => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 | false => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)))))
def signTableUp (m : ℕ) : ℕ := Nat.lor (bitMap10 (Nat.land m 31)) (bitMap15 (Nat.shiftRight m 5))
def signTableDn (m : ℕ) : ℕ := Nat.lor (bitMap00 (Nat.land m 31)) (bitMap05 (Nat.shiftRight m 5))
def hiBit (x : ℕ) : ℕ :=
  let j := match Nat.beq (Nat.shiftRight x 512) 0 with | true => 0 | false => 512
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 256)) 0 with | true => j | false => Nat.add j 256
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 128)) 0 with | true => j | false => Nat.add j 128
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 64)) 0 with | true => j | false => Nat.add j 64
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 32)) 0 with | true => j | false => Nat.add j 32
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 16)) 0 with | true => j | false => Nat.add j 16
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 8)) 0 with | true => j | false => Nat.add j 8
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 4)) 0 with | true => j | false => Nat.add j 4
  let j := match Nat.beq (Nat.shiftRight x (Nat.add j 2)) 0 with | true => j | false => Nat.add j 2
  match Nat.beq (Nat.shiftRight x (Nat.add j 1)) 0 with | true => j | false => Nat.add j 1
def spanUp (d : ℕ) := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (if overlaps d col0 then 1 else 0)) (if overlaps d col1 then 2 else 0)) (if overlaps d col2 then 4 else 0)) (if overlaps d col3 then 8 else 0)) (if overlaps d col4 then 16 else 0)) (if overlaps d col5 then 32 else 0)) (if overlaps d col6 then 64 else 0)) (if overlaps d col7 then 128 else 0)) (if overlaps d col8 then 256 else 0)) (if overlaps d col9 then 512 else 0)
def spanDown (d : ℕ) := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (if overlaps d ncol0 then 1 else 0)) (if overlaps d ncol1 then 2 else 0)) (if overlaps d ncol2 then 4 else 0)) (if overlaps d ncol3 then 8 else 0)) (if overlaps d ncol4 then 16 else 0)) (if overlaps d ncol5 then 32 else 0)) (if overlaps d ncol6 then 64 else 0)) (if overlaps d ncol7 then 128 else 0)) (if overlaps d ncol8 then 256 else 0)) (if overlaps d ncol9 then 512 else 0)
def rapidGrow (b : Bool) (d : ℕ) := if b then growUp d else growDown d
def rapidSpan (b : Bool) (d : ℕ) := if b then spanUp d else spanDown d
def rapidSign (b : Bool) (x : ℕ) := if b then signTableUp x else signTableDn x
lemma rapidGrow_eq (b : Bool) (d : ℕ) : rapidGrow b d = grow b d := by cases b <;> rfl
lemma rapidSpan_eq (b : Bool) (d : ℕ) : rapidSpan b d = spanBits d b := by cases b <;> rfl
def signComparisonBC (b : Bool) (x : ℕ) := (rapidSign b x).beq (someBits x b)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma signsPassBC : eachBC (fun x => signComparisonBC false x && signComparisonBC true x) 1024=true := by decide +kernel
lemma rapidSign_eq (b : Bool) (x : Fin 1024) : rapidSign b x.val = someBits x.val b := by
  have both : signComparisonBC false x.val = true ∧ signComparisonBC true x.val = true :=
    Bool.and_eq_true_iff.mp (eachBC_at signsPassBC x.isLt)
  cases b
  · exact beq_iff_eq.mp both.1
  · exact beq_iff_eq.mp both.2
def simpleParts (d : ℕ) (b : Bool) : ℕ × ℕ :=
  let item := hiBit d
  if item < 1024 && d == 1 <<< item then
    let z := if b then item else 1023-item
    (allWords ^^^ rapidSign (!b) z,z)
  else (rapidGrow b d,rapidSpan b d)
def fastParts (d : ℕ) (b : Bool) :=
  match Nat.beq (Nat.land d (d-1)) 0 with
  | true => simpleParts d b
  | false => (rapidGrow b d,rapidSpan b d)
def interBitBC (b : Bool) (x k d c : ℕ) :=
  match (Nat.land 1 (Nat.shiftRight x k)).beq 0 with
  | true => match b with | false => Nat.land d c | true => d
  | false => match b with | true => Nat.land d c | false => d
lemma interBitBC_eq (b : Bool) (x k d c : ℕ) : interBitBC b x k d c =
    (if x.testBit k == b then d &&& c else d) := by
  change _ = (if (!(Nat.land 1 (Nat.shiftRight x k)).beq 0) == b then d &&& c else d)
  unfold interBitBC
  cases b <;> cases (Nat.land 1 (Nat.shiftRight x k)).beq 0 <;> rfl
def rawUpperBC (b : Bool) (x : ℕ) :=
  match b with
  | true => (interBitBC true x 9 (interBitBC true x 8 (interBitBC true x 7 (interBitBC true x 6 (interBitBC true x 5 (interBitBC true x 4 (interBitBC true x 3 (interBitBC true x 2 (interBitBC true x 1 (interBitBC true x 0 allWords col0) col1) col2) col3) col4) col5) col6) col7) col8) col9)
  | false => (interBitBC false x 9 (interBitBC false x 8 (interBitBC false x 7 (interBitBC false x 6 (interBitBC false x 5 (interBitBC false x 4 (interBitBC false x 3 (interBitBC false x 2 (interBitBC false x 1 (interBitBC false x 0 allWords ncol0) ncol1) ncol2) ncol3) ncol4) ncol5) ncol6) ncol7) ncol8) ncol9)
lemma rawUpperBC_eq (b : Bool) (x : ℕ) : rawUpperBC b x = upperSet x b := by
  cases b <;> simp only [rawUpperBC,interBitBC_eq] <;> rfl
def orientedWordBC (b : Bool) (x : ℕ) := if b then x else 1023-x
lemma orientedBoundBC (b : Bool) (x : Fin 1024) : orientedWordBC b x.val<2^10 := by
  cases b
  · change 1023-x.val<1024
    omega
  · exact x.isLt
lemma orientedBitBC (b : Bool) (x : Fin 1024) {i : ℕ} (bd : i<10) :
    (orientedWordBC b x.val).testBit i = (x.val.testBit i == b) := by
  cases b
  · change (1023-x.val).testBit i = _
    rw [show 1023-x.val = 2^10 - (x.val+1) by omega,Nat.testBit_two_pow_sub_succ x.isLt]
    cases h : x.val.testBit i <;> simp [bd]
  · change x.val.testBit i = _
    cases x.val.testBit i <;> rfl
lemma singleOverlapsBC (i m : ℕ) : overlaps (1 <<< i) m = m.testBit i := by
  rw [Nat.one_shiftLeft]
  cases hi : m.testBit i with
  | true => exact overlaps_bit Nat.testBit_two_pow_self hi
  | false =>
    have eq : 2^i &&& m = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and,Nat.testBit_two_pow]
      by_cases h : i=k
      · subst k
        simp [hi]
      · simp [h]
    simp [overlaps,eq]
lemma spanSingletonBC (x : Fin 1024) (b : Bool) :
    spanBits (1 <<< x.val) b = orientedWordBC b x.val := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [spanBits,vectorBits_bit,singleOverlapsBC]
  by_cases bd : i<10
  · rw [orientedBitBC _ _ bd]
    simp only [bd,decide_true,Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using signedColumn_bit x ⟨i,bd⟩ b
  · have off := Nat.testBit_lt_two_pow ((orientedBoundBC b x).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt bd)))
    simp [bd,off]
def upperCheckBC (b : Bool) (x : ℕ) :=
  Nat.beq (Nat.xor allWords (rapidSign (!b) (orientedWordBC b x))) (rawUpperBC b x)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma upperMaskPassBC : eachBC (fun x => upperCheckBC false x && upperCheckBC true x) 1024=true := by decide +kernel
lemma upperCircuitBC (b : Bool) (x : Fin 1024) :
    allWords ^^^ rapidSign (!b) (orientedWordBC b x.val) = upperSet x.val b := by
  have pair : upperCheckBC false x.val=true ∧ upperCheckBC true x.val=true :=
    Bool.and_eq_true_iff.mp (eachBC_at upperMaskPassBC x.isLt)
  rw [←rawUpperBC_eq]
  cases b
  · exact beq_iff_eq.mp pair.1
  · exact beq_iff_eq.mp pair.2
lemma singletonParts (b : Bool) (x : Fin 1024) :
    let z := if b then x.val else 1023-x.val
    (allWords ^^^ rapidSign (!b) z,z) = (grow b (1 <<< x.val),spanBits (1 <<< x.val) b) := by
  apply Prod.ext
  · rw [Nat.one_shiftLeft,grow_one]
    exact upperCircuitBC b x
  · exact (spanSingletonBC x b).symm
lemma swapped_bounded : ∀ v : Fin 1024, swapWord v.val < 1024 := by
  decide +kernel
lemma boundedSign (b : Bool) (x : ℕ) (bd : x<1024) :
    rapidSign b x = someBits x b := rapidSign_eq b ⟨x,bd⟩
def quickCross (x : ℕ) := rapidSign false (swapWord (rapidSpan false x))
lemma quickCross_eq (x : ℕ) : quickCross x = someBits (swapWord (spanBits x false)) false := by
  unfold quickCross
  rw [rapidSpan_eq]
  apply boundedSign
  exact swapped_bounded ⟨spanBits x false,vectorBits_lt _ 10⟩
lemma simpleParts_eq (d : ℕ) (b : Bool) : simpleParts d b = (grow b d,spanBits d b) := by
  by_cases ex : (decide (hiBit d < 1024) && (d == 1 <<< hiBit d)) = true
  · obtain ⟨bd,eq⟩ := Bool.and_eq_true_iff.mp ex
    let v : Fin 1024 := ⟨hiBit d,of_decide_eq_true bd⟩
    simp only [simpleParts,ex,↓reduceIte]
    exact (singletonParts b v).trans (congrArg (fun n => (grow b n,spanBits n b)) (beq_iff_eq.mp eq).symm)
  · simp only [simpleParts,ex,Bool.false_eq_true,↓reduceIte,rapidGrow_eq,rapidSpan_eq]
lemma fastParts_eq (d : ℕ) (b : Bool) : fastParts d b = (grow b d,spanBits d b) := by
  unfold fastParts
  split
  · exact simpleParts_eq d b
  · exact Prod.ext (rapidGrow_eq b d) (rapidSpan_eq b d)
def reuseCross (x : ℕ) : Bool → ℕ → ℕ
  | true,_ => quickCross x
  | false,z => rapidSign false (swapWord z)
lemma reuseCross_ok (x : ℕ) : ∀ b z, z = rapidSpan b x → reuseCross x b z = quickCross x
  | true,_,_ => Eq.refl (quickCross x)
  | false,_,h => congrArg (fun z => rapidSign false (swapWord z)) h
lemma reuseCross_eq (x : ℕ) (b : Bool) :
    reuseCross x b (fastParts x b).2 = someBits (swapWord (spanBits x false)) false := by
  have h : (fastParts x b).2 = rapidSpan b x :=
    (congrArg Prod.snd (fastParts_eq x b)).trans (rapidSpan_eq b x).symm
  exact (reuseCross_ok x b _ h).trans (quickCross_eq x)
def trimWord (w : ℕ) := Nat.land fieldMask (Nat.xor fieldMask w)
abbrev Chart := Id → ℕ × ℕ × ℕ
def lanesFor (net : Link) (i : Id) (mode : Fin 3) := strideFlags (List.ofFn (net mode i))
def chartOf (net : Link) : Chart := fun i => (lanesFor net i 0,lanesFor net i 1,lanesFor net i 2)
def quickCut (table : Chart) (d : ℕ) (i : Id) : ℕ :=
  let fields := table i
  let x := laneRead d i.val
  let b := orientation i
  let p := fastParts x b
  let one := if fields.1 == 0 then 0 else Nat.mul (trimWord p.1) fields.1
  let two := if fields.2.1 == 0 then 0 else Nat.mul (trimWord (rapidSign (!b) p.2)) fields.2.1
  let three := if fields.2.2 == 0 then 0 else
    Nat.mul (trimWord (reuseCross x b p.2)) fields.2.2
  Nat.lor (Nat.lor one two) three
lemma mul_empty (a b : ℕ) : (if b == 0 then 0 else Nat.mul a b) = a*b := by
  by_cases eq : b=0 <;> simp [eq]
lemma fastJoin_direct (d : ℕ) (b : Bool) :
    rapidSign (!b) (fastParts d b).2 = someBits (spanBits d b) (!b) := by
  have ok := congrArg Prod.snd (fastParts_eq d b)
  exact (congrArg (rapidSign (!b)) ok).trans (rapidSign_eq (!b) ⟨_,vectorBits_lt _ 10⟩)
lemma quickCut_eq (net : Link) (d : ℕ) (i : Id) :
    quickCut (chartOf net) d i = sourceCut net d i := by
  let x := laneRead d i.val
  let b := orientation i
  let f := chartOf net i
  let u := fastParts x b
  let g := grow b x
  have fst : u.1 = g := congrArg Prod.fst (fastParts_eq x b)
  have one : (if f.1 == 0 then 0 else Nat.mul (trimWord u.1) f.1) =
      trimWord g * f.1 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.1) fst)
  have two : (if f.2.1 == 0 then 0 else Nat.mul (trimWord (rapidSign (!b) u.2)) f.2.1) =
      trimWord (someBits (spanBits x b) (!b)) * f.2.1 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.2.1) (fastJoin_direct x b))
  have three : (if f.2.2 == 0 then 0 else Nat.mul (trimWord (reuseCross x b u.2)) f.2.2) =
      trimWord (someBits (swapWord (spanBits x false)) false) * f.2.2 :=
    (mul_empty _ _).trans (congrArg (fun z => trimWord z * f.2.2) (reuseCross_eq x b))
  exact congrArg₂ Nat.lor (congrArg₂ Nat.lor one two) three
def laneBase : ℕ := 1 <<< 1025
def spacedFlags (x : ℕ) := Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (Nat.add (Nat.mul laneBase (0)) (x.testBit 25).toNat)) (x.testBit 24).toNat)) (x.testBit 23).toNat)) (x.testBit 22).toNat)) (x.testBit 21).toNat)) (x.testBit 20).toNat)) (x.testBit 19).toNat)) (x.testBit 18).toNat)) (x.testBit 17).toNat)) (x.testBit 16).toNat)) (x.testBit 15).toNat)) (x.testBit 14).toNat)) (x.testBit 13).toNat)) (x.testBit 12).toNat)) (x.testBit 11).toNat)) (x.testBit 10).toNat)) (x.testBit 9).toNat)) (x.testBit 8).toNat)) (x.testBit 7).toNat)) (x.testBit 6).toNat)) (x.testBit 5).toNat)) (x.testBit 4).toNat)) (x.testBit 3).toNat)) (x.testBit 2).toNat)) (x.testBit 1).toNat)) (x.testBit 0).toNat
set_option maxRecDepth 10000 in
lemma spacedFlags_eq (x : ℕ) : spacedFlags x = strideFlags (List.ofFn fun j : Id => x.testBit j.val) := by rfl
def directId {α : Type} (f : Id → α) (j : Id) : α :=
  let i := j.val
  (match Nat.blt i 13 with | true => (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => f 0 | false => (match Nat.blt i 2 with | true => f 1 | false => f 2)) | false => (match Nat.blt i 4 with | true => f 3 | false => (match Nat.blt i 5 with | true => f 4 | false => f 5))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => f 6 | false => (match Nat.blt i 8 with | true => f 7 | false => f 8)) | false => (match Nat.blt i 11 with | true => (match Nat.blt i 10 with | true => f 9 | false => f 10) | false => (match Nat.blt i 12 with | true => f 11 | false => f 12)))) | false => (match Nat.blt i 19 with | true => (match Nat.blt i 16 with | true => (match Nat.blt i 14 with | true => f 13 | false => (match Nat.blt i 15 with | true => f 14 | false => f 15)) | false => (match Nat.blt i 17 with | true => f 16 | false => (match Nat.blt i 18 with | true => f 17 | false => f 18))) | false => (match Nat.blt i 22 with | true => (match Nat.blt i 20 with | true => f 19 | false => (match Nat.blt i 21 with | true => f 20 | false => f 21)) | false => (match Nat.blt i 24 with | true => (match Nat.blt i 23 with | true => f 22 | false => f 23) | false => (match Nat.blt i 25 with | true => f 24 | false => f 25)))))
lemma directId_eq {α : Type} (f : Id → α) (j : Id) : directId f j = f j := by fin_cases j <;> rfl
def readyChart (e : ℕ) : Chart := directId fun i =>
  let groups := rawGroups e i
  (spacedFlags groups.1,spacedFlags groups.2.1,spacedFlags groups.2.2)
lemma readyChart_eq (e : ℕ) : readyChart e = chartOf (hinted e) := by
  funext i
  rw [readyChart,directId_eq]
  simp only [spacedFlags_eq]
  rfl
def allLanes : ℕ := spacedFlags 67108863
def guardBits : ℕ := allLanes <<< 1024
def lowBits : ℕ := Nat.mul allWords allLanes
def dirtyBits (x : ℕ) := Nat.land (Nat.add x lowBits) guardBits
def chooseSource (q : ℕ) : Id :=
  (match Nat.blt q (Nat.shiftLeft 1 14349) with | true => (match Nat.blt q (Nat.shiftLeft 1 7174) with | true => (match Nat.blt q (Nat.shiftLeft 1 4099) with | true => (match Nat.blt q (Nat.shiftLeft 1 2049) with | true => 0 | false => (match Nat.blt q (Nat.shiftLeft 1 3074) with | true => 1 | false => 2)) | false => (match Nat.blt q (Nat.shiftLeft 1 5124) with | true => 3 | false => (match Nat.blt q (Nat.shiftLeft 1 6149) with | true => 4 | false => 5))) | false => (match Nat.blt q (Nat.shiftLeft 1 10249) with | true => (match Nat.blt q (Nat.shiftLeft 1 8199) with | true => 6 | false => (match Nat.blt q (Nat.shiftLeft 1 9224) with | true => 7 | false => 8)) | false => (match Nat.blt q (Nat.shiftLeft 1 12299) with | true => (match Nat.blt q (Nat.shiftLeft 1 11274) with | true => 9 | false => 10) | false => (match Nat.blt q (Nat.shiftLeft 1 13324) with | true => 11 | false => 12)))) | false => (match Nat.blt q (Nat.shiftLeft 1 20499) with | true => (match Nat.blt q (Nat.shiftLeft 1 17424) with | true => (match Nat.blt q (Nat.shiftLeft 1 15374) with | true => 13 | false => (match Nat.blt q (Nat.shiftLeft 1 16399) with | true => 14 | false => 15)) | false => (match Nat.blt q (Nat.shiftLeft 1 18449) with | true => 16 | false => (match Nat.blt q (Nat.shiftLeft 1 19474) with | true => 17 | false => 18))) | false => (match Nat.blt q (Nat.shiftLeft 1 23574) with | true => (match Nat.blt q (Nat.shiftLeft 1 21524) with | true => 19 | false => (match Nat.blt q (Nat.shiftLeft 1 22549) with | true => 20 | false => 21)) | false => (match Nat.blt q (Nat.shiftLeft 1 25624) with | true => (match Nat.blt q (Nat.shiftLeft 1 24599) with | true => 22 | false => 23) | false => (match Nat.blt q (Nat.shiftLeft 1 26649) with | true => 24 | false => 25)))))
def repeatWord (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.lor 1 (Nat.shiftLeft (repeatWord k n) k)
def denseSpread (x : ℕ) := Nat.land (Nat.mul (Nat.land x 67108863) (repeatWord 1024 26)) allLanes
def denseChart (e : ℕ) : Chart := directId fun i =>
  let g := rawGroups e i
  (denseSpread g.1,denseSpread g.2.1,denseSpread g.2.2)
set_option maxRecDepth 10000 in
lemma readSpacedMask (x k : ℕ) :
    (spacedFlags x).testBit k =
      (decide (k/1025 < 26) && x.testBit (k/1025) && decide (k % 1025=0)) := by
  rw [spacedFlags_eq]
  have h := scatter_read (List.ofFn fun j : Id => x.testBit j.val) 1 (by decide +kernel)
      (k/1025) (k % 1025) (Nat.mod_lt _ (by decide))
  have eq : 1025*(k/1025)+k % 1025 = k := by omega
  rw [eq,Nat.one_mul] at h
  rw [h]
  have one (j : ℕ) : (1 : ℕ).testBit j = decide (j=0) := by
    change (2^0 : ℕ).testBit j = _
    simp only [Nat.testBit_two_pow, @eq_comm ℕ 0 j]
  rw [one,List.getElem?_ofFn]
  by_cases bd : k/1025 < 26 <;> simp only [bd,↓reduceDIte,Option.getD_some,Option.getD_none,decide_true,decide_false,Bool.true_and,Bool.false_and]
set_option maxRecDepth 10000 in
lemma repeatWord_step (n : ℕ) :
    repeatWord 1024 (n+1) = 2^1024 * repeatWord 1024 n + 1 := by
  change 1 ||| (repeatWord 1024 n <<< 1024) = _
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt (by decide +kernel : 1 < 2^1024),Nat.shiftLeft_eq,Nat.mul_comm]
lemma readRepeatWord (x n k i : ℕ) (hx : x < 2^1024) (hk : k<n) (hi : i<1024) :
    (x * repeatWord 1024 n).testBit (1024*k+i) = x.testBit i := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    have eq : x * repeatWord 1024 (n+1) = 2^1024 * (x * repeatWord 1024 n) + x := by
      rw [repeatWord_step,Nat.mul_add,Nat.mul_one,Nat.mul_left_comm]
    rw [eq,Nat.testBit_two_pow_mul_add _ hx]
    cases k with
    | zero => simp [hi]
    | succ k =>
      have h : ¬ 1024*(k+1)+i<1024 := by omega
      have sub : 1024*(k+1)+i-1024=1024*k+i := by omega
      simpa only [h,↓reduceIte,sub] using ih k (by omega)
set_option maxRecDepth 10000 in
lemma spread_agrees (x : ℕ) : denseSpread x = spacedFlags x := by
  apply Nat.eq_of_testBit_eq
  intro k
  change ((x &&& 67108863) * repeatWord 1024 26 &&& spacedFlags 67108863).testBit k = _
  rw [Nat.testBit_and,readSpacedMask,readSpacedMask]
  by_cases bd : k/1025<26 <;> by_cases off : k % 1025=0 <;> simp only [bd,off,decide_true,decide_false,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false]
  have hb : (67108863 : ℕ).testBit (k/1025) = true := by
    change (2^26-1 : ℕ).testBit _ = _
    exact (Nat.testBit_two_pow_sub_one ..).trans (decide_eq_true bd)
  rw [hb,Bool.and_true]
  have align : k = 1024*(k/1025)+k/1025 := by omega
  have hx : x &&& 67108863 < 2^1024 := lt_of_le_of_lt Nat.and_le_right (by decide +kernel)
  nth_rw 1 [align]
  rw [readRepeatWord _ _ _ _ hx bd (by omega),Nat.testBit_and,hb,Bool.and_true]
lemma correctChart (e : Fin 201) : denseChart e.val = chartOf (hinted e.val) := by
  rw [←readyChart_eq]
  funext i
  simp only [denseChart,readyChart,directId_eq,spread_agrees]
def maskFlag (x m weight : ℕ) :=
  match Nat.beq (Nat.land x m) 0 with | true => 0 | false => weight
lemma maskFlag_eq (x m weight : ℕ) : maskFlag x m weight = (if overlaps x m then weight else 0) := by
  change (match ((x &&& m) == 0) with | true => 0 | false => weight) = (if !((x &&& m) == 0) then weight else 0)
  cases h : ((x &&& m) == 0) <;> rfl
def projectionPositive (x : ℕ) : ℕ := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (maskFlag x col0 1)) (maskFlag x col1 2)) (maskFlag x col2 4)) (maskFlag x col3 8)) (maskFlag x col4 16)) (maskFlag x col5 32)) (maskFlag x col6 64)) (maskFlag x col7 128)) (maskFlag x col8 256)) (maskFlag x col9 512)
lemma projectionPositive_eq (x : ℕ) : projectionPositive x = spanUp x := by simp only [projectionPositive,spanUp,maskFlag_eq]
def projectionNegative (x : ℕ) : ℕ := Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (0) (maskFlag x ncol0 1)) (maskFlag x ncol1 2)) (maskFlag x ncol2 4)) (maskFlag x ncol3 8)) (maskFlag x ncol4 16)) (maskFlag x ncol5 32)) (maskFlag x ncol6 64)) (maskFlag x ncol7 128)) (maskFlag x ncol8 256)) (maskFlag x ncol9 512)
lemma projectionNegative_eq (x : ℕ) : projectionNegative x = spanDown x := by simp only [projectionNegative,spanDown,maskFlag_eq]
def tightParts (x : ℕ) (b : Bool) : ℕ × ℕ :=
  match Nat.beq (Nat.land x (x-1)) 0 with
  | true => simpleParts x b
  | false =>
    match b with
    | true => (growUp x,projectionPositive x)
    | false => (growDown x,projectionNegative x)
lemma tightParts_eq (x : ℕ) (b : Bool) : tightParts x b = fastParts x b := by
  cases c : Nat.beq (Nat.land x (x-1)) 0
  · cases b <;> simp only [tightParts,fastParts,c,rapidGrow,rapidSpan,projectionPositive_eq,projectionNegative_eq,Bool.false_eq_true,↓reduceIte]
  · simp only [tightParts,fastParts,c]
def weighted (m f : ℕ) := match Nat.beq f 0 with | true => 0 | false => Nat.mul m f
lemma weighted_eq (x f : ℕ) : weighted x f = Nat.mul x f := by
  by_cases h : f=0
  · subst f; simp [weighted]
  · have hf : Nat.beq f 0=false := beq_eq_false_iff_ne.mpr h
    simp only [weighted,hf]
lemma weighted_if (m f : ℕ) : weighted m f = (if f == 0 then 0 else Nat.mul m f) :=
  (weighted_eq m f).trans (mul_empty m f).symm
def tightCut (net : Chart) (d : ℕ) (i : Id) : ℕ :=
  let f := net i
  let x := laneRead d i.val
  let b := orientation i
  let p := tightParts x b
  Nat.lor (Nat.lor (weighted (trimWord p.1) f.1)
    (weighted (trimWord (rapidSign (!b) p.2)) f.2.1))
    (weighted (trimWord (reuseCross x b p.2)) f.2.2)
lemma tightCut_eq (net : Chart) (d : ℕ) (i : Id) : tightCut net d i = quickCut net d i := by
  simp only [tightCut,quickCut,tightParts_eq,weighted_if]
def laneReadRaw (d i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight d (Nat.mul 1025 i)) fieldMask
def rawLoop (step : ℕ → Id → ℕ) (source : ℕ → Id) (changed : ℕ → ℕ) (high : ℕ) :
    ℕ → ℕ → ℕ → ℕ
  | 0,d,_ => d
  | fuel+1,d,q =>
    match Nat.beq q 0 with
    | true => d
    | false =>
      let i := source q
      let flag := Nat.shiftLeft 1 (Nat.add (Nat.mul 1025 i.val) 1024)
      let pending := Nat.xor q flag
      let del := Nat.land d (step d i)
      match Nat.beq del 0 with
      | true => rawLoop step source changed high fuel d pending
      | false =>
        let next := Nat.xor d del
        let empty := Nat.xor high (changed next)
        let stop := !(Nat.beq empty 0) && Nat.beq (laneRead next (source empty).val) 0
        match stop with
        | true => 0
        | false => rawLoop step source changed high fuel next (Nat.lor pending (changed del))
lemma rawLoop_keeps {w : Valuation} {step : ℕ → Id → ℕ} {source : ℕ → Id} {changed : ℕ → ℕ} {high : ℕ}
    (pres : ∀ d, insidePacked d w → ∀ i, insidePacked (restrictPacked d (step d i)) w)
    (fuel d q : ℕ) (ok : insidePacked d w) : insidePacked (rawLoop step source changed high fuel d q) w := by
  induction fuel generalizing d q with
  | zero => exact ok
  | succ fuel ih =>
    simp only [rawLoop]
    split
    · exact ok
    · try dsimp only
      split
      · exact ih _ _ ok
      · try dsimp only
        have now := pres d ok (source q)
        split
        · rename_i stop
          obtain ⟨_,empty⟩ := Bool.and_eq_true_iff.mp stop
          have hit := heldLane now (source (high ^^^ changed (restrictPacked d (step d (source q)))))
          change (laneRead _ _).testBit _ = true at hit
          change (laneRead _ _ == 0) = true at empty
          simp only [beq_iff_eq] at empty
          change laneRead (restrictPacked d (step d (source q))) _ = 0 at empty
          change laneRead (restrictPacked d (step d (source q)))
            (source (high ^^^ changed (restrictPacked d (step d (source q))))).val = 0 at empty
          rw [empty] at hit
          simp at hit
        · exact ih _ _ now
def colByIdx (s : ℕ) : ℕ :=
  match Nat.blt s 5 with
  | true =>
    match Nat.blt s 2 with
    | true => (match Nat.beq s 0 with | true => col0 | false => col1)
    | false => (match Nat.blt s 4 with | true => (match Nat.beq s 2 with | true => col2 | false => col3) | false => col4)
  | false =>
    match Nat.blt s 7 with
    | true => (match Nat.beq s 5 with | true => col5 | false => col6)
    | false => (match Nat.blt s 9 with | true => (match Nat.beq s 7 with | true => col7 | false => col8) | false => col9)
def pairNeg0 : ℕ := Nat.lor ncol0 ncol1
def pairNeg1 : ℕ := Nat.lor ncol2 ncol3
def pairNeg2 : ℕ := Nat.lor ncol4 ncol5
def pairNeg3 : ℕ := Nat.lor ncol6 ncol7
def pairNeg4 : ℕ := Nat.lor ncol8 ncol9
def pairNegByIdx (k : ℕ) : ℕ :=
  match Nat.blt k 2 with
  | true => match Nat.beq k 0 with | true => pairNeg0 | false => pairNeg1
  | false => match Nat.blt k 4 with
    | true => match Nat.beq k 2 with | true => pairNeg2 | false => pairNeg3
    | false => pairNeg4
set_option maxRecDepth 20000 in
lemma colByIdx_ok : ∀ s : Slot, colByIdx (slotNum s) = column (slotNum s) := by decide +kernel
set_option maxRecDepth 20000 in
lemma pairNegByIdx_ok : ∀ k : Fin 5, pairNegByIdx k.val = someBits (pairBits k) false := by decide +kernel
def popBelow5 (on k : ℕ) : ℕ :=
  let m := Nat.land on (Nat.sub (Nat.shiftLeft 1 k) 1)
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.land m 1) (Nat.land (Nat.shiftRight m 1) 1))
    (Nat.land (Nat.shiftRight m 2) 1)) (Nat.land (Nat.shiftRight m 3) 1))
    (Nat.land (Nat.shiftRight m 4) 1)
def witnessRowFast (byte : ℕ → ℕ) (t on count k j : ℕ) : ℕ :=
  let before := popBelow5 on k
  let off := match Nat.testBit on k with | true => 0 | false => popBelow5 on j
  let idx := Nat.add (Nat.add before (Nat.mul (Nat.sub k before) count)) off
  let nib := Nat.land (Nat.shiftRight (byte (Nat.add (Nat.add t 3) (Nat.shiftRight idx 1))) (Nat.shiftLeft (Nat.land idx 1) 2)) 15
  Nat.mod nib 15
def scanDown (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => match f n with | true => scanDown f n | false => false
lemma scanDown_at {f : ℕ → Bool} {n : ℕ} (ok : scanDown f n = true) {k : ℕ} (lt : k < n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases e : f n
    · simp [scanDown,e] at ok
    · by_cases eq : k=n
      · simpa only [eq] using e
      · exact ih (by simpa only [scanDown,e] using ok) (by omega)
def checkRawLoop (d u colMask : ℕ) := scanDown fun z =>
  match Nat.testBit u z with
  | false => true
  | true => Nat.beq (Nat.land (laneReadRaw d z) colMask) 0
def checkArcLoop (byte : ℕ → ℕ) (t on count d colMask k : ℕ) := scanDown fun j =>
  match Nat.testBit on j with
  | false => true
  | true =>
    let r := witnessRowFast byte t on count k j
    Nat.beq (Nat.land (laneReadRaw d (Nat.add 11 r)) (Nat.lor colMask (pairNegByIdx j))) 0
def checkGraphLoop (byte : ℕ → ℕ) (t on sw count d u : ℕ) := scanDown fun k =>
  match Nat.testBit on k with
  | true =>
    let r := witnessRowFast byte t on count k 0
    Nat.beq (Nat.land (laneReadRaw d (Nat.add 11 r)) (pairNegByIdx k)) 0
  | false =>
    let s := Nat.add (Nat.shiftLeft k 1) (sw.testBit k).toNat
    let colMask := colByIdx s
    checkRawLoop d u colMask 11 && checkArcLoop byte t on count d colMask k 5
def readLeafFast (pos : PositiveId → ℕ) (byte : ℕ → ℕ) (d tag t : ℕ) : ℕ :=
  let uIdx := Nat.sub tag 26
  if h : uIdx < 100 then
    let on := byte (Nat.add t 1)
    let sw := byte (Nat.add t 2)
    let count := popBelow5 on 5
    match checkGraphLoop byte t on sw count d (pos ⟨uIdx, h⟩) 5 with
    | true => Nat.add (Nat.add t 3) (Nat.shiftRight (Nat.add (Nat.add count (Nat.mul (Nat.sub 5 count) count)) 1) 1)
    | false => 0
  else 0
def sideMaskFast (neg : Bool) (k : ℕ) : ℕ :=
  match neg with
  | true =>
    match k with
    | 0 => sideMask true 0 | 1 => sideMask true 1 | 2 => sideMask true 2 | 3 => sideMask true 3 | _ => sideMask true 4
  | false =>
    match k with
    | 0 => sideMask false 0 | 1 => sideMask false 1 | 2 => sideMask false 2 | 3 => sideMask false 3 | _ => sideMask false 4
def orderMaskFast (neg : Bool) (k : ℕ) : ℕ :=
  match neg with
  | true =>
    match k with
    | 0 => orderMask true 0 | 1 => orderMask true 1 | 2 => orderMask true 2 | 3 => orderMask true 3 | _ => orderMask true 4
  | false =>
    match k with
    | 0 => orderMask false 0 | 1 => orderMask false 1 | 2 => orderMask false 2 | 3 => orderMask false 3 | _ => orderMask false 4
def canonDomainFast (eq fl : ℕ) (neg : Bool) : ℕ :=
  let a := fieldMask
  let a := match Nat.testBit fl 0 with | true => Nat.land a (sideMaskFast neg 0) | false => a
  let a := match Nat.testBit fl 1 with | true => Nat.land a (sideMaskFast neg 1) | false => a
  let a := match Nat.testBit eq 1 with | true => Nat.land a (orderMaskFast neg 1) | false => a
  let a := match Nat.testBit fl 2 with | true => Nat.land a (sideMaskFast neg 2) | false => a
  let a := match Nat.testBit eq 2 with | true => Nat.land a (orderMaskFast neg 2) | false => a
  let a := match Nat.testBit fl 3 with | true => Nat.land a (sideMaskFast neg 3) | false => a
  let a := match Nat.testBit eq 3 with | true => Nat.land a (orderMaskFast neg 3) | false => a
  let a := match Nat.testBit fl 4 with | true => Nat.land a (sideMaskFast neg 4) | false => a
  match Nat.testBit eq 4 with | true => Nat.land a (orderMaskFast neg 4) | false => a
lemma maskNo {x y : ℕ} (h : Nat.beq (Nat.land x y) 0 = true) : !overlaps x y = true := by
  change (x &&& y == 0) = true at h
  simp [overlaps,beq_iff_eq.mp h]
lemma checkGraph_sound (byte : ℕ → ℕ) (t on sw count d u : ℕ)
    (h : checkGraphLoop byte t on sw count d u 5 = true) :
    ∃ rr, graphLeaf d u on sw rr = true := by
  let rr (k j : Fin 5) : Fin 15 := ⟨witnessRowFast byte t on count k.val j.val,Nat.mod_lt _ (by decide)⟩
  refine ⟨rr,List.all_eq_true.mpr ?_⟩
  intro k _
  have hk := @scanDown_at _ 5 h k.val k.isLt
  cases e : on.testBit k.val with
  | true =>
    simp only [e,↓reduceIte] at hk ⊢
    change barredRoot d (rr k 0) k = true
    unfold barredRoot
    rw [←pairNegByIdx_ok]
    exact maskNo hk
  | false =>
    simp only [e,Bool.false_eq_true,↓reduceIte] at hk ⊢
    let s : Slot := (k,sw.testBit k.val)
    have index : Nat.add (Nat.shiftLeft k.val 1) (sw.testBit k.val).toNat = slotNum s := by
      simp [s,slotNum,Nat.shiftLeft_eq,Nat.mul_comm]
    rw [index] at hk
    obtain ⟨hraw,harc⟩ := Bool.and_eq_true_iff.mp hk
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro z _
      have hz := @scanDown_at _ 11 hraw z.val z.isLt
      cases hit : u.testBit z.val with
      | false => simp [hit]
      | true =>
        simp only [hit,Bool.not_true,Bool.false_or] at hz ⊢
        rw [←colByIdx_ok]
        exact maskNo hz
    · apply List.all_eq_true.mpr
      intro j _
      have hj := @scanDown_at _ 5 harc j.val j.isLt
      cases hit : on.testBit j.val with
      | false => simp [hit]
      | true =>
        simp only [hit,Bool.not_true,Bool.false_or] at hj ⊢
        unfold barredArc
        rw [←colByIdx_ok,←pairNegByIdx_ok]
        exact maskNo hj
lemma fastLeaf_safe {n p w O R d} (h : encLayout n p w O R) (ok : insidePacked d w)
    (byte : ℕ → ℕ) (tag t : ℕ) : readLeafFast p byte d tag t = 0 := by
  unfold readLeafFast
  dsimp only
  split
  · split
    · rename_i test
      obtain ⟨rr,good⟩ := checkGraph_sound _ _ _ _ _ _ _ test
      exact (graphLeaf_impossible h ok _ _ _ rr good).elim
    · rfl
  · rfl
lemma fastCanon_ok (m : Marks) (i : Id) (eq fl : ℕ) (ok : acceptMark eq fl (rawNumber m i).val) :
    (canonDomainFast eq fl (!(orientation i))).testBit (represented m i).val = true := by
  let neg := !(orientation i)
  let v := represented m i
  have word : admissibleTable neg v = (rawNumber m i).val := by
    change (if !(orientation i) then 1023-v.val else v.val) = _
    by_cases lt : i.val < 11
    · simp [v,orientation,represented,lt]
    · have := (rawNumber m i).isLt
      simp [v,orientation,represented,lt]
      omega
  have side (k : Fin 5) (h : fl.testBit k.val=true) :
      (sideMaskFast neg k.val).testBit v.val = true := by
    have masks (b : Bool) (g : Fin 5) : sideMaskFast b g.val = sideMask b g := by
      fin_cases g <;> cases b <;> rfl
    rw [masks]
    exact sideMask_ok neg k v (word ▸ (ok k).1 h)
  have order (k : Fin 5) (h : eq.testBit k.val=true) :
      (orderMaskFast neg k.val).testBit v.val = true := by
    have masks (b : Bool) (g : Fin 5) : orderMaskFast b g.val = orderMask b g := by
      fin_cases g <;> cases b <;> rfl
    rw [masks]
    exact orderMask_ok neg k v (word ▸ (ok k).2 h)
  have add (b : Bool) (m a : ℕ) (hm : b = true → m.testBit v.val=true) (ha : a.testBit v.val=true) :
      (match b with | true => Nat.land a m | false => a).testBit v.val=true := by
    cases b <;> simp_all [Nat.testBit_and]
  unfold canonDomainFast
  change (match eq.testBit 4 with | true => Nat.land _ _ | false => _).testBit v.val=true
  apply add _ _ _ (order 4)
  apply add _ _ _ (side 4)
  apply add _ _ _ (order 3)
  apply add _ _ _ (side 3)
  apply add _ _ _ (order 2)
  apply add _ _ _ (side 2)
  apply add _ _ _ (order 1)
  apply add _ _ _ (side 1)
  apply add _ _ _ (side 0)
  rw [show fieldMask = allWords by decide +kernel]
  exact allWords_bit v
def pop10 (c : ℕ) : ℕ :=
  Nat.add (Nat.land c 1)
  (Nat.add (Nat.land (Nat.shiftRight c 1) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 2) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 3) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 4) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 5) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 6) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 7) 1)
  (Nat.add (Nat.land (Nat.shiftRight c 8) 1)
           (Nat.land (Nat.shiftRight c 9) 1)))))))))
def bothSigns (a b r : ℕ) := let s := 32767; (s ^^^ (a &&& b)) ||| r
def chosenSig (a b tt tf ft ff v : ℕ) :=
  let s := if a.testBit v then (if b.testBit v then tt else tf) else (if b.testBit v then ft else ff)
  Nat.land (Nat.xor 32767 (incidence v)) s
lemma chosenSig_eq (a b na nb v : ℕ) :
    chosenSig a b (bothSigns 32767 32767 (na &&& nb)) (bothSigns 32767 nb (na &&& nb))
      (bothSigns na 32767 (na &&& nb)) (bothSigns na nb (na &&& nb)) v = stableSig a b na nb v := by
  cases ha : a.testBit v <;> cases hb : b.testBit v <;> simp only [chosenSig,stableSig,bothSigns,ha,hb] <;> rfl
def cliqueRun (c : ℕ) (sig : ℕ → ℕ) := scanDown fun v =>
  !c.testBit v || scanDown (fun w => !c.testBit w ||
    (sig v &&& sig w != 0 && sig v &&& incidence w != 0 && sig w &&& incidence v != 0)) v
def quickClique (a b c : ℕ) :=
  bitSub c (a ||| b) && (pop10 c == 6) &&
    let na := negativeSig a
    let nb := negativeSig b
    let r := na &&& nb
    cliqueRun c (chosenSig a b (bothSigns 32767 32767 r) (bothSigns 32767 nb r)
      (bothSigns na 32767 r) (bothSigns na nb r)) 10
lemma countBits10 : ∀ c : Fin 1024, pop10 c.val = ((List.range 10).filter (fun i => c.val.testBit i)).length := by
  decide +kernel
lemma quickClique_sound {a b c : ℕ} (ct : c<1024) (ok : quickClique a b c = true) : validClique a b c = true := by
  let sig := stableSig a b (negativeSig a) (negativeSig b)
  obtain ⟨base,ck⟩ := Bool.and_eq_true_iff.mp ok
  have all : cliqueRun c sig 10 = true := by
    have sigEq := funext (chosenSig_eq a b (negativeSig a) (negativeSig b))
    simpa only [sigEq] using ck
  have pair {v w : ℕ} (bd : v<10) (lt : w<v) (hv : c.testBit v=true) (hw : c.testBit w=true) :
      (sig v &&& sig w != 0) = true ∧ (sig v &&& incidence w != 0) = true ∧ (sig w &&& incidence v != 0) = true := by
    have up := @scanDown_at _ 10 all v bd
    simp only [hv,Bool.not_true,Bool.false_or] at up
    have down := @scanDown_at _ v up w lt
    simpa only [hw,Bool.not_true,Bool.false_or,Bool.and_eq_true,and_assoc] using down
  apply Bool.and_eq_true_iff.mpr
  constructor
  · simpa only [←countBits10 (⟨c,ct⟩ : Fin 1024)] using base
  · apply List.all_eq_true.mpr
    rintro _ hv
    obtain ⟨v,mv,rfl⟩ := List.mem_map.mp hv
    apply List.all_eq_true.mpr
    rintro _ hw
    obtain ⟨w,mw,rfl⟩ := List.mem_map.mp hw
    obtain ⟨vr,cv⟩ := List.mem_filter.mp mv
    obtain ⟨wr,cw⟩ := List.mem_filter.mp mw
    rcases lt_trichotomy v w with lt | eq | gt
    · obtain ⟨cross,_,inc⟩ := pair (List.mem_range.mp wr) lt cw cv
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨by simpa only [Nat.and_comm] using cross,inc⟩))
    · exact Bool.or_eq_true_iff.mpr (Or.inl (beq_iff_eq.mpr eq))
    · obtain ⟨cross,inc,_⟩ := pair (List.mem_range.mp vr) gt cv cw
      exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr ⟨cross,inc⟩))
def permuteStraight (pw x : ℕ) : ℕ :=
  let z := 0
  let z := if x.testBit 0 then z ||| (1 <<< ((pw >>> 0) &&& 15)) else z
  let z := if x.testBit 1 then z ||| (1 <<< ((pw >>> 4) &&& 15)) else z
  let z := if x.testBit 2 then z ||| (1 <<< ((pw >>> 8) &&& 15)) else z
  let z := if x.testBit 3 then z ||| (1 <<< ((pw >>> 12) &&& 15)) else z
  let z := if x.testBit 4 then z ||| (1 <<< ((pw >>> 16) &&& 15)) else z
  let z := if x.testBit 5 then z ||| (1 <<< ((pw >>> 20) &&& 15)) else z
  let z := if x.testBit 6 then z ||| (1 <<< ((pw >>> 24) &&& 15)) else z
  let z := if x.testBit 7 then z ||| (1 <<< ((pw >>> 28) &&& 15)) else z
  let z := if x.testBit 8 then z ||| (1 <<< ((pw >>> 32) &&& 15)) else z
  let z := if x.testBit 9 then z ||| (1 <<< ((pw >>> 36) &&& 15)) else z
  z
def positiveLowBlock (i : ℕ) : ℕ := 0xfffffffffffffffffffffffff0000000effffffffffd7ffffffffffff0000000dbbffffffffffffffffffffff0000000cbbfdffffffd7fbffffffffff0000000ff7ffdf7fffffffffffffffff0000000a67ffdf5fefd7f7bfffefffbf0000000db3fbdf7fdfffffffffffffff0000000823f1df5fcfd7f3bfffefffb70000000ffffffefffffffeffdfffffff0000000effef76bfbf97eeff9fffff7f0000000d9bdfacffffffdeffdfdbfeff0000000c9bcd24bf3d97caff9f9b7e7f0000000ff7ffde7efffffeffdffffdff0000000a67af561eab97e6bf9f6ffd2f0000000d93db8c7cdfffdeffdfdafcff000000080381041c0997c2bf9f0a7c270000000ffffeffffff7fffff7fffffff0000000efffeffffff57bfff7effffff00000005bb7efffbfe6fffef7df7fbff00000004bb7cfffbfe473bef7cf7fbfe0000000ff6fedb77ff7efd5e7bffffff0000000a64fedb57ef56b51c7aeff79f00000005b27adb73de6cfd4a79f7ebfd000000002070db53ce44310878e7e3940000000ffffefeffff7ffeff57ffdfff0000000effee76bfb717aeff06ffdf7f000000059b5eacebfe6bdeef55d1dafb000000049b4c24ab34030aef04915a7a0000000ff6feda76ff7efc5653ff9dff0000000a64ae5216a316a414026f950f00000005925a8860de68dc4251d088f900000000000000000000000000000000
def positiveLow (i : ℕ) := Nat.land (Nat.shiftRight (positiveLowBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def positiveHighBlock (i : ℕ) : ℕ := 0xfffffffffffffffffffffffff0000000ffffffffffffffffffffffff80000000fffffffffffffffffffffffc70000000fffffffffffffffffffff80000000000ffffffffffffffffffffc7fff0000000ffffffffffffffffffff07ff80000000fffffffffffffffffe00c7fc70000000ffffffffffffffffe000000000000000ffffffffffffffff1ffffffff0000000fffffffffffffffc1fffffff80000000fffffffffffffff31ffffffc70000000ffffffffffffffc01ffff80000000000ffffffffffff803f1fffc7fff0000000fffffffffffe003c1fff07ff80000000ffffffffffe180331e00c7fc70000000ffffffffffe000000000000000000000ffffffffff1ffffffffffffff0000000fffffffe001fffffffffffff80000000fffffff9ff1ffffffffffffc70000000ffffff80001ffffffffff80000000000fffffe7fff1fffffffffc7fff0000000fffff87e001fffffffff07ff80000000ffffe679ff1ffffffe00c7fc70000000ffffe000001fffffe000000000000000ffc01fffff1fffff1ffffffff0000000fc001ffe001ffffc1fffffff80000000f3c01ff9ff1ffff31ffffffc70000000f0001f80001fffc01ffff800000000000fc01e7fff1f803f1fffc7fff00000000c00187e001e003c1fff07ff8000000003c00679ff0180331e00c7fc700000000000000000000000000000000
def positiveHigh (i : ℕ) := Nat.land (Nat.shiftRight (positiveHighBlock (Nat.shiftRight i 6)) (Nat.shiftLeft (Nat.land i 63) 7)) 340282366920938463463374607431768211455
def positiveHalves (x : ℕ) := Nat.lor (positiveLow (Nat.land x 31)) (positiveHigh (Nat.shiftRight x 5))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma positiveHalvesPassBC : eachBC (fun x => (positiveHalves x).beq (positiveSig x)) 1024=true := by decide +kernel
lemma positiveHalves_good (x : Fin 1024) : positiveHalves x.val = positiveSig x.val :=
  beq_iff_eq.mp (eachBC_at positiveHalvesPassBC x.isLt)
def positiveMemo (x : ℕ) := if x<1024 then positiveHalves x else positiveSig x
lemma positiveMemo_eq (x : ℕ) : positiveMemo x = positiveSig x := by
  unfold positiveMemo
  split
  · rename_i lt
    exact positiveHalves_good ⟨x,lt⟩
  · rfl
def negativeLowBlock (i : ℕ) : ℕ := 0x7fff7eff5fff5eff77ff36fd57ff16fd7ffb7adb4feb4acb77fb32d947eb02c97fbf7ebf5dbe5cbe77373635553614347fbb7a9b4daa488a7733321145220000
def negativeLow (i : ℕ) := Nat.land (Nat.shiftRight (negativeLowBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def negativeHighBlock (i : ℕ) : ℕ := 0x7fff7ffe7ffd7ff07fef7fee7f8d7f807f7f7f7e7f7d7f707c6f7c6e7c0d7c007bff63fe7bfd63f07bef63ee7b8d63801b7f037e1b7d0370186f006e180d0000
def negativeHigh (i : ℕ) := Nat.land (Nat.shiftRight (negativeHighBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def negativeHalves (x : ℕ) := Nat.lor (negativeLow (Nat.land x 31)) (negativeHigh (Nat.shiftRight x 5))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma negativeHalvesPassBC : eachBC (fun x => (negativeHalves x).beq (negativeSig x)) 1024=true := by decide +kernel
lemma negativeHalves_good (x : Fin 1024) : negativeHalves x.val = negativeSig x.val :=
  beq_iff_eq.mp (eachBC_at negativeHalvesPassBC x.isLt)
def negativeMemo (x : ℕ) := if x<1024 then negativeHalves x else negativeSig x
lemma negativeMemo_eq (x : ℕ) : negativeMemo x = negativeSig x := by
  unfold negativeMemo
  split
  · rename_i lt
    exact negativeHalves_good ⟨x,lt⟩
  · rfl
def memoCold (a b : ℕ) := Nat.land (negativeMemo a) (negativeMemo b)
def memoEnv (e a b : ℕ) :=
  bitSub (suppNum e) (Nat.lor a b) && bitSub (hotNum e) (memoCold a b) &&
    bitSub (Nat.land (positiveMemo a) (positiveMemo b)) (pointNum e)
def memoRouteBlock (c a b t : ℕ) :=
  let e := routeEnv c % 201
  bitSub (negativeMemo t) (memoCold a b) &&
    (if e=199 then bitSub (Nat.land (positiveMemo a) (positiveMemo b)) (positiveMemo t)
     else memoEnv e (eraseMask a t) (eraseMask b t))
def memoClique (a b c : ℕ) :=
  bitSub c (a ||| b) && (pop10 c == 6) &&
    let na := negativeMemo a
    let nb := negativeMemo b
    let r := na &&& nb
    cliqueRun c (chosenSig a b (bothSigns 32767 32767 r) (bothSigns 32767 nb r)
      (bothSigns na 32767 r) (bothSigns na nb r)) 10
def dAfterBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x15cc15cb15ca15ca15ca15c815c715c715c715c615c515c415c415c415c415c415c415bf15bc15b515b415b415b415b415b415b015af15ae15ae15ad15ad15ad15ad15ac15ab15a715a515a515a515a515a515a215a115a015a0159e159e159e159e159815981593158f158f158f158f158f1587158715861586158215821582158215811581157f157c157c157c157c157c15781578157715771573157315731573156d1568155b15561556155615561556154d154b1547154615421541154115411540153f15391535153515351535153515311530152c152a1526152415241524151414fe14fe14fe14f314eb14eb14eb14d314cc14c814c614be14bc14bb14bb14ab149d1493148b14731469145b1458144a1443143d143b142d142b1428142814251418141814181418141814181418141014071404140213f713f513f213f213e613d613d613d613d613d613d613d613b713a613a1139f1391138f13881388138713831383138313831383138313831380137c137b1379136d136b13661366135413441325130d12ff12f812e512dc12cb12bf12af12ab12a0129d12931293128c12851279126d1261125a1248123d1236122f12281224121812141209120911e611e611e611e611bb11bb11a911a9117a1167114f114f112e11261119111810f410f410f410f410c610c610b110b1107e1068104c104c1025101a100910070ff00fdb0fad0f880f880f880f880f880f530f2b0f090efa0ee60edd0ec90ec50eae0e990e6b0e400e400e400e400e400e090ddb0db70da40d8e0d830d680d620d5a0d5a0d5a0d5a0d5a0d5a0d5a0d5a0d450d450d3b0d3b0d290d220d0a0d050cfd0cfd0cfd0cfd0cfd0cfd0cfd0cfd0ce80ce80cde0cde0ccc0cc50cab0ca50c910c7e0c4f0c240c100c010bdb0bbf0bab0b990b730b5a0b460b3b0b1d0b130b0d0b0d0b0d0b0d0afc0afc0ae70ae70ae00ada0acd0acd0abc0ab10a970a8f0a770a770a570a400a0c09f109be09980980098009640951091f090b08e208d308cf08cf08c908bf08af08a9088b086a08660866086008560846084008220812080a080a080a080a080a080a080a080a07f707f707e507e507d207c507b407a80794079407740761072e070f06d606ad06990699067a066a0639061f05ef05d805c4059005900590057c054b054b054b050b04cd04ba048e044f041a040703e803e203dc03b20389038903890389038903750361032e02ff02f902f302cd02af02a902a30279024f024f024f024f024f023b022701f401c201bc01b6018e016b01680156015601560156015601560156014c0132012f011a010200ea00dd00b500ad00ad00ad00ad00ad00ad00ad00ad009500950089008900750069004100220021002100210021002100210021002100200020001f001f001b00190012 | false => 0x15d115d015d015d015d015d015d015d015d015d015d015d015d015d015d015d015d015cf15cf15ce15ce15cd15cd15cd15cd15cc15cc15cc15cc15cc15cc15cc)
def dAfter (i : ℕ) := Nat.land (Nat.shiftRight (dAfterBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def dRefBlock (i : ℕ) : ℕ := (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x10c029a029a010c010c029b029b018d01eb01a7011101f201f301f301f301f301f300ba01f301090280027f02800289023c00dd01f4010b021f021f023b00bc023d010a01da01d801da01db014100fa014300f80139018f013901de014500fe01460064023e01dd023e023e00fd00fd023f0139013901ab005f02380016009200160016009200920225013e0225008802430094009200920092028d0092009200920092012b018c013900a3012b00cc011d00a300d70139023500d7023600a200cc013e016400cc01ef00cf010c015e0139015f01ee010c029c010f0191013901aa01ac013e013d013e02270119008a024400f70139009f013900c0011b009f024600c0013901390134009a024000ac013e013e01670096014e01390130013900a500a8010101390139002a002a002a002a002a002a002a002a002a002a002a004a004a004a0049004900490049022f029d0048002a002a002a002e002e002e002e00f100f100f1002a002a002a002a002a002a002a002a009c009c009c00fb00fb00fb00fb00fb019a00fb019a0298029802980298022f00ff00f400240024002400da00da00da00da0176017501760175009c009c009c00970097009701780178017a017a022f023700c3001700170017001700c700c700c700c700b400b400b400b400ca00ca016500ca00e200e201a501a5010e012e01a9010e009c009c009c009c00df019800df00df00b500b500b500b5015b019e014d00e60161016100e400e4012f00e7013100e70125012a008d012f008f008f008d008d01f1008d012f014800f2009c01570118009c015b019b012100be012f0159011c00a0012f00ad011f00ae009c009c009c009c012f0177011e00a9009700970097012f016b00db01690136016a00a6012f0147012f012900af012f0007000700100010002e002e004c004c000700070015001500120012003200320010001000310031002f002f00d600d6002e002e0100010001100110010301160007000700240024001f001f00ee00ee010c010c010001000007000700170017001600160010001001140114010e010e00e500e501070107010e010e012000e8000d000d00bf00bf00e500e500bf00bf00e500e501070107000700070093009300c700c700d10090012000a4010c010c010100a200b700f3012000f5010c010c00bf00ce00b700cb00d100cd012000d3010c010c0101010f00b700d0012000d400d100d2012000d500a5009800af00a10120000000a5009d010100ab012000aa00a5009800af00dc0120000000a500a701010102012000b100af00b0012000b20120000001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x13b01f901560117009b01fa019c009b025901c6009b0154028602a50269015a013200970097009701680154013c01540001000100010001000100010001000100010001000100010001000100010001000100010001000100040004000400040004000400040004000300030003000300030003000200020002000200020002001d001d001d001d001d001d001d001d00440044004400440044004400010001000100010001000100010001001a001a001a001a001a001a001a001a0019001900190019001900190018001800180018001800180040004000400040004000400040004002ce01b701af013f01af00010001000100010001000100020002000200020002000200020002000f000f000f000f000f000f00010001000100010001000100080008000800080008000800080008002500250025002500250025000100010001000100010001000100010004000400040004000400040004000400030003000300030003000300020002000200020002000200020002001e001e001e001e001e001e001e001e001d001d001d001d001d001d001d0078018501b901fb005f01a600010001000100010001000100010001001a001a001a001a001a0204001a021c0019001900190019001900190018001800180018001800180018001802ce020e0144018e015501ea014402600260024d01dc020b017c017902ce02010252000100010001000100010001000100010001000100010001000100010001000100010001000100010004000400040004000401280004008e00030003000300030003000300020002000200020002000202ce016d0186015d02b2012301ae02ce019101b40001000100010001000101e6000100f702ce01580138009e011a0158011a02ce01370261009901330170016f017200ed016602ce01710153016902ce004700470047004700470047002b004b002b002b004b004b0047004700470047004700470047004700470047004700470047004700470047004602280046004602280228004502300045004502300230019f019f029a029a019f019f029a029a019f028e019f019f028e028e0043004300f600f60043004300f600f602870287027c028802870113016c011301d7021f01d700ef029f00ef01a101a101a100ef01a100ef023e01d9023e01a201ad00ef029e00ef0139013901b0011200f000f00016003300160016003300330030003000e300e30030003000e300e3027d01eb029700cc029900d6002b01ec002b002b01ec0108021e021e01da0226014a01050106010601390139014c00c1024500c20023002300920092002300230092009200b600b600b6027e00b600b600b6027e0228022802280228022802280239023902390239023902390239023900cc018b01eb019001ed00cc023a00e9010c) | false => (match Nat.blt i 3 with | true => 0x20002000200020002000200020163015c000202d0026b026301c801bf025f01b80001000100010001000101e10001000101df0001020a0001008902d002ae02b3018a024b026202d00173017002d00011001100110011001100110011001100110011001100110011001100110011001100110011001100270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027004800480048004a004a0048004800480048004800480048028c004900490049004802b900e0004800110011001100110011001100110011001100110011001100110011001100110011001100110011003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f003f01d501d501d500970097009701cb01cb01cc01cc02720278028102bb02bb024102c1006300110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c002c0076002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700270027002700fb00fb00fb00fb00fb01bc00fb01bc026700f900fb00f901420199014200fc0298029801c702230154024c0224022402c201150298007502c0023200ff0020002000200020002000200020002000200020002000200020002000200020002000200020022001f8022001f8020601c101f701c1024e01e400ea009b02b001740122005c0222022202220222020602070206022200ec023300ec020600590097015201510097014000eb01540247017d0154017f0135006a017b022f0011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001100110011001101d301d30277027700c901bd02ab01a0026400c9014b00c9026500c9016500c901a401a4021a021a010d012402b4028502b1012c01a4010d012d012d01a801d5025501f501f500df019700df00df0266012601f500df02bf019700df00df01d401d401d401d40257025802a6028401d4016201d40257006801d501d501d501d5015401ca01f600e601600160014b00e102ba019d004e01c401c401c50154025a01be0268005e026a0097013a013a024f012a0086009b02a101c302830154020c00f2025101270234008c025001490097016e014f0097015401e80150 | false => (match Nat.blt i 4 with | true => 0x100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010008000100010001000100010001000100010001000100010001000100010001000100010002000200010001000101df000102740001000100010001025602d2000100010001000100010001000100010001000100030003000300030003000300030003000300030001000100010001000100010001000100010001000100010001000100010001000300030003000300030003000300030003000300030003000300030003006d0001000100010001000100010001000100010001001900190019001900190019001900190019000100010001000100010001000100010001000100010001000100010001000100030003000300030003000300030003000300030003000300030003000300030002000200020002000200020002000200020002000e000e000e000e000e000e000e006c000e0001000100010001000100010001000100010001000100010001000100010001000900090009000900090009000900090009000900090009000900090009000100010001000100010001000100010001000100010001000100010001000100030003000300030003000300030003000300030003000300030003000300020002000200020002000200020071000200020002000200020067000200370037003700370037003700370037006e0231003700010001000100010001000100010001000100010001000100010001000100350035003500350035003500350035003500350035003500350219003400340034003400340034004f02d0027902a8026c025c000100010001000100010001000100010001000100030003000300030003000300030003000300030001000100010001000100010001000100010001000100010001000100010001000300030003000300030003000300030003000300030003000300660003000100010001000100010001000100010001001900190019001900190019001900010001000100010001000100010001000100010001000100010001000100010003000300030003000300030003000300030003000300030003000300030002000200020002000200020002000200020002000e000e000e000e000e01b3000e01a300010001000100010001000100010001000100010001000100010001000100090009000900090009028a000900090065006000090001000100010001000100010001000100010001000100010001000100010001000300030003000300030003000300030003000301fe020d000300020002 | false => 0x90009000900090001000100010001000100010009000900090009005e000100010001000100050005000500050001000100010001000500050005005d0003000300030003003a003a003a003a0003000300030003003a0056003a000100010001000100050005000500010001000100010003000300030003003a003a003a0003000300010001000100010036003600010001000100010036020f003500350035003502b501d0003500350035003502d100010001000100360036003600010001005000350035003502cf0242004f00010001000100010003000300030003000100010001000100010001000100010003000300030003000300030003000300010001000100010001000100010001000300030003000300030003000300700001000100010001000100010001000100030003000300030001000100010001001900190019001900010001000100010001001a001a001a0019001900190001000100010001000500050001000100010001000500050003000300030003001100110003000300030003001100110001000100010001000500050005000500010001000100010005000500050005000300030003000300110011001100030003001100010001000100010001000100010001000900090009000100010001000100010001000900090060000100010001000100050005000500050001000100010001000500c60005000300030003000302b5025d0253026e0003006502b80001000100010001000500050005000100010003000301c201c9000301f0000100010001000102b501bb0001018300010184019402b50180017e02b5000f000f000f000f00380038003800380038003802c401fc018102c402c401e300b80202010400bb000f000f00130016000f0010000f001300160013000f000f0013001600130016003e003e003e003e003e003e003800390038003c003d003c0038003900380039003c003d003c003d02c602c5003800390038003c003d003c003800390038003902c700c502c900d800b802ca02100214021102ca01e5029300b80293021102cb0181021301810181027002710270021702ca021201e5029600b802a902aa028b021802c3027b01e7004f000f000f000f000f02210221008302210221008301d601fd018102490248022b00b9024a022d00bd000f000f00130016000f0010000f001300160013000f000f001302950013001601e002030254020300870087022c018101ba021d0181026d02a3022e008500c8027502cc00de02920181028f022c02a201ba02050208021d02a3022e008500c802a0028202a4008b01d60181020902a701bb0181025b01e90229029001bb01e20181022a01810181000100010001000100010001000100010001000100010001000100010001000100010001))) | false => (match Nat.blt i 8 with | true => (match Nat.blt i 6 with | true => 0x100010001000100010001000100010001000100010001000100010003000300030003000300030001000100010001000100010001000100010001000300030003000300030003000300010001000100010001000100010001000100010001000100010035003500350035003500010001000100010001004f00350035003500350001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000800010001000100010001000100010001000100010001000100010001000100030003000300030003000300010001000100010001007800010001000100010001000100030003005f000300030001000100010001000100010001000100010018000100010019001900190001000100010001004d0001001a001a001a0019000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010009000100010001000100010001000100010001000100010001000100010001000300030003000300030003000100010001000100010003000302bc000301ff000100010001000101e1000101df0001008902d0000100010001000100010001000100060001000100010001000600060001000100060001000600010001000600060001000100010001000100010003003b00030003000100010001000100030003003b02b600030003003b00010001000100010001000100010001000100010001000100010001000100010003000100010001000100010001000300030003000100060001000100010001000600060001000100060001000600010001000600060001000c0001000100010001000c000100090001000c0001000100060001000100010001000600060001000100030182000300030001000100060001000100010006000302bd0003020000010001000101c000010089018201820001000100010001000300030003000300010001000100010001000100010001000300030003000300030003000300030001000100010001000100010001000100030003000300030003000300030003000100010001000100010001000100010003000300030003000300030003007f000100010001000100190019001900190001000100010001000100010001000100190019001900800019001900190001000100010001000500050001000100010001000500050003000300030003001100110003000300030003001100110001000100010001000500050005000500010001000100010005000500050005000300030003000300110011001100110003000300110011000100010001000100010001000100010009000900090009 | false => (match Nat.blt i 7 with | true => 0x280029002800290028000b000d000b000b000d000b002800280028000b000d000b000d000b000d000b002800290028007c002800290053000b000d000b000b007900260028002800510005000700050007000500070005000700210022002100220021002200050007000500070005000700050021002100050007000500070005002100220021007800050005002100d9001b001c001b001c001b001c0189018901cd027a025e01ce001b001b001c001b01b5026f005700050007000500070005000700050007000500070005000700050007000500070005000700050005000d0005000b000d000b000b000d000b000d000b0273000b000b0005000700050007000500070005000701890189021502c802ad02cd000500070005000700050007000500050005021b0216000500c401df018901df02ac0189018900010001000100010001000100010001000100010004000400010001000400040001000100010001000400040004000400010001000100040004000100010001000100010001000100010001000100010001000100010005000500010001000100010005000500010001000100050005000500010001000100010001000100010001000100010001000500050004000400040004000100010001000100050005000500010001000402af0001000400040001000102d2018702d2002d0007002d0007002d0007002d0007002d000700150015002d000700150015002d0007002d00070015001500150015002d0007002d0015001500070007000700070007000700070007000700070007000700070007001600160007000700070007001600160007000700070294009500b3000d000d000d000d000d000d000d0007000700070007018801880188018801930291000700070007000701b60276019201950007000701b201960007008401b1009102ac02ac0188018801880188000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001007300010001000100010001000100010001000100010001000100010001000100010001000100010001000100030003000300030003000300010001000100010001000100010001000100010001000100010001000300030003007f000300030003000300030003000300010001000100010001000100010069000100010001000100010001005400190019001900190019000100010001000100010001000100010001000100010001000100190019001900190019001900190019001900190001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010063004e0001 | false => 0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100040004000400040004000400040001000100010001000100010001000100010001000100010001000100010004000400040004000400620001000100010001007b000100040004000400550001000100010001000100010001001a001a001a001a001a001a00010001000100010001000100010001000100010001000100010069001a001a001a001a0001000100010001001a001a000100010001000100010001000100010004000400040004000400040004000400010001000100010001000100010001000400040004000400040001000100010001000100010001000100040004000400040004000400040001000100010001000100010004000400040001000100010001000100010001000a000a000a000a000a000a0053000100010001000100010001000a000a0051000100010001007c000100010001000a000a000a000a000a0001007900010001000a0001000100010001000100010001006400040004000400040004000400010001000100010001000100010004000400010001000100010001000400040004000100010004000100010001000100010001001a001a001a001a0001000100010057001a000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000400040004000400040001000100010001000100010004000100010001000102d200050007000500070005000700050007000500070005000700050007000500070005000700050007000500070005000b000d000b000d000b000d000b000d000b000d000b000d000b000d000b000b000d000b000b000d000b0005000700050007000500070005000700210022002100220021002200210005000700050007000500070005000700050007000500070005000700050021002200210022002100220005000700050005000700050021002200210021001b001c001b001c001b001c001b004100420041004200410042001b001c001b001c001b001c001b001b001c001b001c001b001c001b004100420041007300410042001b001c001b001b007b0069004102b7004100550005000700050007000500070005000700130015001300150013001500130015000500070005000700050007000500070013001500130013001300050007000500070005000700050007001300150013001500130015001300150005000700050005000700050013001300130028000b000d000b000d000b000d000b00280029)) | false => (match Nat.blt i 9 with | true => 0x1000100010001000100010072000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001005d000100010001000100010001000100010001000100010001000100010001000100010001000100770001005a00010001000100010001006b000100010001000100010001000100010001000100010001000100010001004f000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010079000100010051000100010001000100010001000100010001000100010001000100010064000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100070001000700010007000100070001000700010007000100070001000700010007000100010007000100070001000700010007000100070001000700010007000100010001000100070001000700010007000100070001000700010007000100070001000100070001000700010007000100810001000700010001000100070001000700010007000100010007000100010001000700010001007e00010001006b0001000700010007000100070001000700010007000100070001000700010001000700010001000100520001000700010007000100070001000700010007000100070001000700010007000100070001000700010007000100010007000100010001000700010007000100070001000700010007000100070001000700010001000700010001007d00010001000100010001000d0001000d0001000d0001000d00010001007900010001000d0001000d0001000d000100010001005100010007000100070001000700010001000700010007000100070001000700010001000100010001000700010001000100780001000100010001000700010007000100070001000700010007000100070001000700010001000700010082000100070001000100010001000700010007000100070001000100070001000100010001000100010001000d00010001000d0001000d000100010001000100010007000100070001000700010001000700010007000100070001000100010001000102be0001000100010001000100010001 | false => (match Nat.blt i 10 with | true => 0x1000100010001000100010001000100010001000100010001000400010001000600060001000100060006000100010006000600010001000600060001000100060006000100010006000100010001000600010001000100060006000100010006000400040014001400010001000600010006000400040001000100060001000100060004000400140001000600010059000100010006000100010004000400040051000100010001000100010004000400040001000100060006000100010001000100010006000600010001000600010006000100060001000600010001000600010001000600060004000401d20001000100010001000100010001000100010001000100010001000100010001000700060001000700010006000100010006000100060001000600010006000401d101d100010001000100010001000100010001000100010001000100010001000100010001006200010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100030003000300030061000100010001000100010067000100030003005f0003000300010001000100690001000100010001000100010003000300030003000100010001004d0001000100030003000300030001000100010001000100010001000100010001000100010001006300010001000100010001004e0001000100010001000100010001000100010001000100010003000300030003000100010001000300010001000100010001004f0003000300030001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001007800010001000100010003000300010001000100010001000100010003000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010003000100010001000100010001000100010001000100010001000100010001000100010003000100010001000100010003000300030001000100010003000100010001000100010003004d000300010006000100010001000100060001000100060001000600010006000100010001000100010001000100060001000100010001000600060003003b000300030001000100060003003b000100010006000100010001004f0003003b0003000300010001000100010001000100010001000100010001000100010001000100010001000300010001000100010001000100030001000600010001000100010006000100010006000100060001000600010001000100010006000100010001000100060006000301cf000100010001000100010001000100010001 | false => 0x100010001000100010001000100010001000100010001000100010001000100010001000100010053000100780001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010006000100010001000100010001000100010001005f000100010001000100010001000100010001000100010001000100010001000100010005000100010001000100010001000100010001000100010001000100050016000100010001000100010001000100010001000100530001000100010001006400010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010006000100010001000c00010001000100010001000100010001000100010001006d00010001000100010001000100010001000100010001000100010001005b00010001000100010001005800010001000100010001000100010001000100630001000100010001000100010001007a0001004e0001005e0001000100010001000100010001000100010001000100010001000100010001005900010001000100010001000100010001006a0001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001007400010001000100010001000100010001000100010001000100010001000100010001000100660001000100570001000100060001000100010001000600010001000100060001000100010001000100010006000100010001006f005a0001000100060001000100010001004e00010001000100010006000100520001004f00060001000100060001000100010001005000010001000100010001000100010001000100010001000100010001005900010001000100010001000100010001000100010001000100010001000100010001000600010001000100010006000100060001000100060001000100060001000100060001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001))))
def dRef (i : ℕ) := Nat.land (Nat.shiftRight (dRefBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def dCaseBlock (i : ℕ) : ℕ := (match Nat.blt i 1 with | true => 0x100123801001233010012270100121a010012190100120e010012010100102d010010260100100401000f5001000f3801000f3701000f3201000f1901000e5301000e3c01000e2c01000e2201000e1f01000e0c01000e0601000d3a01000c5401000c4f01000c3401000c2c01000c2b01000c1901000c1501000c0f01000ba001000a110100091101000893010008430100084201000794010007830100070a010006b0010006a00100065b0100065a010006520100064e0100064d01000648010006360100063501000631010006300100062901000628010006260100061b01000614010006110100060a010006030100044a010002ba0100029c01000246010002400100022d0100021e0100021d0100020b010002060100020501000204010001550100011b010000a8010000940100005e0100005c0100005901000056010000550100004e0100004d0100004c0100004b0100004901000047010000450100004401000041010000400100003f0100003d010000390100002f0100002e0100002c0100002b0100002a01000028010000260100002501000024010000230100002201000021010000200100001f0100001c01000019010000180100001701000016010000150100001401000013010000100100000d0100000c010000090100000701000004010000030100000201000000000004e9000004e7000004e1000004dd000004db000004d9000004d1000004cd000004cb000004c9000004c5000004c3000004b7000004b3000004b1000004a10000049f0000049d0000049b0000049900000493000004870000047f0000047b00000479000004710000046b0000046700000465000004630000045d0000045b0000045700000455000004530000044d0000044b0000044700000445000004430000043f0000043d0000043b0000043900000437000004350000042d000004290000042500000423000004210000041d0000041700000411000003cc000003b8000003990000038e0000038b000003710000036a0000035a000003470000033a00000336000003330000030f000002ab000002970000027a000002730000026d0000026b0000025e000002570000024f0000023b0000022f0000021f000001f8000001e6000001dc000001da000001d6000001ce000001cd000001cb000001ba000001b9000001b6000001b3000001ab0000019b000001970000017c0000017a00000176000001730000016b0000015e000001570000014f0000013e0000013b000001370000012f0000011f000000fc000000fa000000f6000000f5000000f3000000ee000000eb000000de000000d7000000cf000000be000000bd000000bb000000b7000000af0000009f0000007e0000007d0000007b000000770000006f0000005f0000003f00000000 | false => (match Nat.blt i 2 with | true => 0x12213520122135101220e2f01220e1701212b58012110590121104901205037012043d1012040da012040b501202e5101202e3001202b5801202b3701202b3301202a4801202a4301202a3501201d30012013570120105101201046012010400120103a01201026012010120120100d0120100101200e5701200e2201200c3001200c22012004590120044b0120044a0120044401200440012004390120042a0120041c012000b0012000a8012000a201200094011d405d011d005d011c035c011b405d011a305c011907d901181ec401181ec0011805d90116155c0114a45c01142448011418d9011418d6011418d5011418c9011418c601140b430114064501122556011212dc01120fd001120a52011206550112062f011201550111255901110d5b01110949011108c60110a45c01106451011046d001104650011025500110254f01102542011025370110245c01102459011024560110245201102451011024440110244101102431011024300110242d01101c5101101c3001100fb201100d2c01100ac801100ac601100a4501100a4301100a3501100a3301100a2901100a27011006ac0110064c011006400110062c01100625011001550110014b0110014901100147011001400110012f0110012a010e14dc010d805d010c805d010c805c010c1f59010c1955010c0255010c0245010b405d010a805d010a805c010a135c010a005501091e590109125901081e4501081e4401081e4101081e40010805590108044001080423010804210106945c010614560106025c0106025501050e58010502490104465a01041c3a010418590104185601041855010418450104184301041841010418390104182901041824010414a401041446010414270104065a010406480104064701040626010402550104024c01040249010402460104022a010402250103125b0102c05d0102925c0102525001024e500102405b0102405201021456010214510102143f010214300102141701021351010213500102125c0102125b010212520102124f0102124e0102123d010212310102122c01020e53010202550102022f010200550102004e010200160101405d0101405b0101405a010112580101124601010cc901010cc701010cc601010c5b010100590100c05d01008c5401008c5301008c3c0100863e0100861c0100805c0100803d0100803a0100801d0100801c010058530100585101004536010042510100405d0100405b0100405a0100405401004052010040500100404f0100403701004035010040330100243a01001e1101001b3e01001a3c0100193b0100192b010018b0010018510100183e0100183c0100183001001636010016240100160f010016080100144601001412010014010100130b010012d7010012580100125701001246 | false => 0x1ffc05d01d0265c01cbc05d01c217dc01c1c05d01c0a45c01c0275901c0275601c0275501c0273901c0245501c023b901c019d501c019af01c0199c01c017dc01a03a4301a02ed801a02e5901a02e4b019f805d0192155c01910dd901903844019028590190284b0190254501900b4c019001ca018ac05d01881fd9018486dc018436590184364801841c43018418c6018406d50182585b01821855018213d001820edb01820ed2018200550181185901810ed8018086dc0180585001805837018046d4018046d2018046d0018038b5018038480180383a01803659018036440180364001803639018036300180361c01802eb601801d3901801d1c01801a270180184c01801846018018450180182c018015460180113701800eb801800eb301800ea201800b4301800b2901800b14018006d5018006c7018006c1018006ae018006ac018004ca018003d5018003af018003aa0180039c01800355018001c60164135c016230dc016030d801602bb70160235901602348016020cb016020c5016016d7016016d1016010b501600f5701600d5601600d430152265c0150815c0150345c01503459015034560150342f0150342a015026500150263701500155014a165c01483259014832550146315c0145125a0144815c01441b5a01441443014402dc014402d9014402d6014402d5014402c8014402aa014402a9014401550142305c014230520142175b0142163f0142162f01413058014108db014108d9014108c90140563701405237014047da0140345a01403452014034480140342901403353014032ab01403259014032560140325501403244014032390140322a01403151014031300140305c01403058014030500140303701403033014030270140225101401b3401401b30014016570140163d01401625014016190140160d014012400140122101400f2c01400a4301400a3501400a14014008cf014008b4014007a80140079901400794014005400140051c014001300140002b013109d9013025c3013020cb01300bd901300bc4013009c5013009400130074b0130074901300744013007400130072a013006400128045901241f48012419590124185501240e4301240c43012403da012403d6012403d5012403c801240246012400a901221abf0122135c0122135b))
def dCase (i : ℕ) := Nat.land (Nat.shiftRight (dCaseBlock (Nat.shiftRight i 8)) (Nat.shiftLeft (Nat.land i 255) 5)) 4294967295
def acceptRow (i : ℕ) : ℕ := (match Nat.blt i 17 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000080000000000000000000000000000000ac00000000000000a000000000000000a0b0a00000000000c0ccac00800088ab | false => 0xc0000000c000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0c0c0f0f0f0f00000000000000000f0000000f000f0000000000000000000fc000000fc00ff00f0000000f000f000fcf0ff00fcf0fff0c0ccfc00c0ccfcfe) | false => (match Nat.blt i 3 with | true => 0xb000000000000000ff000000b000fb00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0000000fb000000ff00b000ff00fb00b000000000000000ff00b000b000fb00ff000000ff00ff00ff000000ff00ff00b0b0fb0000000000ffffff00b0b0fae8 | false => 0xaf00000000000000af00000000000000ffffaf00af00ffafffffaf00af00ffaf0000000000000000000000000000000000000000000000000000000000000000af000000ffaf0000af000000ffaf0000ffffaf00ffffffaeffffaf00fffffeaeaf00000000000000af00000000000000ffffaf00af00ffaaffffaf00ae00eea0)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0xaf00000000000000af00000000000000ffffaf00af00ffafffffaf00af00ffae0000000000000000000000000000000000000000000000000000000000000000af000000ffaf0000af000000ffaf0000ffffaf00ffffffaeffffaf00fffefea8af00000000000000af00000000000000ffffaf00af00fea8fffeae00ae00e880 | false => 0xb0b0fbfb00000000ffffffffb0b0fbfb00000000000000000000000000000000b0b0fbfb00000000fffffffeb0b0fbea00000000000000000000000000000000fffffffffffffffffffffffefffffffeb0b0fbfa00000000fffffefcb0b0eae8fffffffffffffffeffffffecfffeeea8b0b0fbfa00000000fffcfee0a0a0a800) | false => (match Nat.blt i 7 with | true => 0x8aef8aef000000000000000000000000ffffffff000000008aef8aee00000000ffffffff8aef8aeefffffffe00000000fffffffefffefee8fffefffc8ae88aa08aef8aef000000000000000000000000fffffffe000000008aee8ae800000000fffffffe8aef8aeafffefee800000000fffffff8fef8eaa0fefcec8088808000 | false => 0x800088ab0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008aef8aee000000000000000000000000b0b0fbf8000000000000000000000000af00ffae00000000af00ee8000000000b0b0fbf000000000c0ccec0080000000))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0x8000000080a00000000000000000000080a0000080a0000080808000a0a080a0ac000000eeaf0000a0000000a0a00000eeffa000eef0a0a0fcfcac00eee0eea08000000080a00000000000000000000080a0000080a0000080808000a0a080a0ac000000eeaf0000a0000000a0a00000eeffa000eef0a0a0fcfcac0000000000 | false => 0xc0c0c0c0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0c0c0c0c0f0f0f0e0fcfcfcfcffffffaaf0f0f0f0e0e0e0a0fffffffefef0fea0fcfcfcf8eee0ea80c0c0c0c0f0f0f0f00000000000000000f0f0f0f0f0f0a0a0c0c0c0c0f0f0a080fcfcfcfcfffffea8f0f0e000e0e0e000fffeffe0fee0a8a0fcece80000000000) | false => (match Nat.blt i 11 with | true => 0x80000000c08c0000000000000000000000000000000000000000000000000000ac000000feaf00000000000000000000c0ccac00c0c0f8a0000000000000000080000000c88c000080000000c08c000080c08000c8c888800000000000000000ac000000feaf0000ac000000eca00000ecfcac00eca0a0a0c0cca00000000000 | false => 0xaf000000ffaf0000af000000ffae0000ffffaf00fefefeacfffeae00fefceeacaf000000ffaf0000af000000eea80000fffeaf00fee0eaa0fefcae00ea80aa00af000000ffaf0000af000000feae0000fffeaf00fef8a8a0fcfca800f8f08000af000000ffaf0000ae000000ec800000fffcaf00e8a0a0a0eccc800000000000)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0xc0000000c000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0c0c0f0f0e0a00000000000000000f0000000f000a0000000000000000000fc000000fc00ee00e0000000c000c000fcf0ff00a0a0a0a0c0cc000000000000 | false => 0xc0000000c000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0c0c0f0f0e0a00000000000000000f0000000f000a0000000000000000000fc000000fc00ee00e0000000c000c000fcf0fe00a0a0a080c0c8000000000000) | false => (match Nat.blt i 15 with | true => 0xff000000ff00fe00ff000000fe00ee00fffeff00fefceee8fefcfe00fefceee80000000000000000000000000000000000000000000000000000000000000000ffffffeaffffeeaafefeeea8fefeeea8fffcfea0f8f0a0a0fcfc8000e0e00000ff000000ff00ee00ec000000cc008800fffcfe00a0a0a000ccc0000000000000 | false => (match Nat.blt i 16 with | true => 0xff000000ff00fe00ff000000fe00ee00fffeff00fefceee8fefcfe00fee8e8a00000000000000000000000000000000000000000000000000000000000000000ffffffeafffeeea8fefeeea8feece880fffcfea0f8e0a080fce88000e0800000ff000000fe00ea00ec000000c8008000fef8e800a0808000c880000000000000 | false => 0xc0ccfcfec0ccfcea000000000000000000000000000000000000000000000000fffeffe8fee8eea00000000000000000c0ccfce0c080a8000000000000000000fffffee8fffeeea8c0ccec80c0cca880fefce8a0e8e0a0000000000000000000fffefea0fee8aa00ecc0880088000000fef0e800a0000000c000000000000000))))) | false => (match Nat.blt i 25 with | true => (match Nat.blt i 21 with | true => (match Nat.blt i 19 with | true => (match Nat.blt i 18 with | true => 0xc0ccfcfec0ccfce8000000000000000000000000000000000000000000000000fffefee8fee8ea800000000000000000c0c8fca0c080a0000000000000000000fffefee8fefeeaa0c0cce880c0cc8800fef8e880e8a080000000000000000000fffcee80eea0aa00ec80800080000000fcf0a000800000008000000000000000 | false => 0x80000000c88c000080000000c88c000080c08000c8c0888080c08000c8c08880ac000000eea00000ac00000088800000ecf0ac00e000a000ecc0ac000000000080000000c88c000080000000c88c000080c080008880000080c0800000000000ac000000eea00000ac00000000000000ecf0a000000000000000000000000000) | false => (match Nat.blt i 20 with | true => 0xaf000000feae0000af000000eeac0000fefeae00e8e0a8a0fce8ac00e8a0a0a0af000000eea00000ac00000088800000fef0ac00e0008000ec808c0000000000af000000feac0000ac000000ec8c0000fcf0a000a8800000c080800000000000ae000000ea800000a800000000000000f8f08000000000000000000000000000 | false => 0x800000000000000080000000800088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000088000000800080008800000080000000000000008000800000000000ec000000a800aa00a000000000000000a0b00000000000000000000000000000)) | false => (match Nat.blt i 23 with | true => (match Nat.blt i 22 with | true => 0xf0000000f000f000ff000000ec00a800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fef0eac0eee0aa00eccc8000ccc80000f0000000800000008000800000000000fe000000aa00a800a000000000000000f0e00000000000000000000000000000 | false => 0xb000000000000000ff000000a000a800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0000000ea000000ec008000c8000000b0000000000000008000800000000000fe000000a8008000a000000000000000a0800000000000000000000000000000) | false => (match Nat.blt i 24 with | true => 0x80c080c0c8c8c88080c08080c8c8888080c08080c880800080c0808080808000ece8ec88e880a800ec80880080800000ece0e800c0000000c00080000000000080c080c0c8c8880080c080008880000080c08000880000008000800000000000ece0a800a8000000a000000000000000e0000000000000000000000000000000 | false => 0xb0b0fae800000000ffe8e880a080880000000000000000000000000000000000b0a0e88800000000e88080008080000000000000000000000000000000000000fee8e8c0e8a08000e880800080000000a0808000000000008000800000000000ec80800080000000a00000000000000080000000000000000000000000000000))) | false => (match Nat.blt i 29 with | true => (match Nat.blt i 27 with | true => (match Nat.blt i 26 with | true => 0x8000000000000000800000000000000080c080008800000080c080000000000000000000000000000000000000000000000000000000000000000000000000008000000088800000800000000000000080008000880000008000800000000000ac00000000000000a00000000000000000000000000000000000000000000000 | false => 0xaf00000000000000ae00000000000000eae8a00088000000c0c08000000000000000000000000000000000000000000000000000000000000000000000000000ac000000a8a00000a00000000000000088008000800000008000000000000000ac00000000000000800000000000000000000000000000000000000000000000) | false => (match Nat.blt i 28 with | true => 0x800000000000000000000000000000008000000080000000808080000000000000000000000000000000000000000000000000000000000000000000000000008000000080a00000000000000000000080000000000000000000000000000000ac00000000000000000000000000000000000000000000000000000000000000 | false => 0xc0000000c000a0000000000000000000c000a00080000000c0808000000000000000000000000000000000000000000000000000000000000000000000000000c0c08000a0800000000000000000000080000000000000000000000000000000e800000000000000000000000000000000000000000000000000000000000000)) | false => (match Nat.blt i 31 with | true => (match Nat.blt i 30 with | true => 0x800000000000000080000000000000008080800080000000800080000000000000000000000000000000000000000000000000000000000000000000000000008000000088000000800000000000000080000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000 | false => 0xae00000000000000a800000000000000e88080008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000a8000000800000008000000000000000800000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000) | false => (match Nat.blt i 32 with | true => 0x8000000000000000800000000000000000000000000000000000000000000000808000000000000080000000000000000000000000000000000000000000000080000000000000008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => (match Nat.blt i 33 with | true => 0x8000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))
def classRow (i : ℕ) : ℕ := (match Nat.blt i 17 with | true => (match Nat.blt i 8 with | true => (match Nat.blt i 4 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x1 | false => 0x100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000100000000000000010000000100010116) | false => (match Nat.blt i 3 with | true => 0x10000000000000001000000000001000000000000000000000000000000000000000000000000000100000001000001000000000000000000000000010000001000000000000000040000000201021048 | false => 0x1000000000000000000000000000000000000000000000000000000010000011600000000000000000000000000000001000000000000000000000000000100160000000000000001000000000001010600000001000101120001011400140620)) | false => (match Nat.blt i 6 with | true => (match Nat.blt i 5 with | true => 0x10000000000000000000000000000000100000001000100100000000000010004000000000102000000000000000000000000000100000000000000010000010400000102010010000000000000000000000000120000104000000000000000480002000812084080 | false => 0x100000000000000000000000100010100000000000000000000000000000001060000000100000112000100020014104800000000000000010000000000000110000000000001001200010014000206480000000100000014000101040112002800000006010614000100126004602800) | false => (match Nat.blt i 7 with | true => 0x1000000010000000000000001000101000000000001000000000000010000001400010002011210400000000001060048000200001008000000000001000000000000011000001000000000060100144801021208020040000000000000000040000210681000008000000008000840000200008068808000 | false => 0x100000000000000000000000000000000010000000000000000000000000000000000004000020000100000000000000000080000000000000000000000000000000000000000100000000000000000080000400002000000000000000000000000000000000000800000000000000000000000000000000080000000))) | false => (match Nat.blt i 12 with | true => (match Nat.blt i 10 with | true => (match Nat.blt i 9 with | true => 0x12000000000000000000000000000000000000000000000000000001040000042000000000000000000000000000010004000000000000000000000000000400200000000000000102000000000004020000010010001002000010040000000000 | false => 0x1001000000000000000120000010200021000000000000000010200000104000400200001000400100400010000080420408000000000000001040001000401000040000100100004020000000420040820800000001200001008001002000248200000020040124008001020480000000000) | false => (match Nat.blt i 11 with | true => 0x10000000000000000000001000000000000000000000000000000000000000000080000000200001000000000000040000000000000000000100000000000000000000000000002000000000040000008000000000400000000010000000020000000000000040000000000200000000000 | false => 0x110000101000100100000010002000210000102000000000000000000060000100801000008006800800002000814404000000000004080000000000014000010400100004000000000000200400608080000006880080080000000004800000000122020002080000000000000480000002000800000000000)) | false => (match Nat.blt i 14 with | true => (match Nat.blt i 13 with | true => 0x4000000000000000000000000000000000000000000000000000000100000020000000000000000000000000000000002000000000000000000000000001000000000000000010000000000000000040000000100000000200004000000000000 | false => 0x40000000000000000000000000001000000000010000000000000000000000000000000000200000000000000000000000000000200000000000001000000000000000000100000000000000000000000000000000000400000000000000000800008000000000000) | false => (match Nat.blt i 15 with | true => 0x600000000000000000000001400140648000000000000000000000000000006000000011000000220001412600000280000000000000100020000000000120628000000000010002000140000006000000001010001160420000404000400080001041620002020000440000000000000 | false => (match Nat.blt i 16 with | true => 0x10004000000120000000000000104000404480000000012000000000100100116000000101060020040000000000002000080020800002800000000000102000000000002022810004000010016001000008010080000600000000000000000004080000840004000800000080080008080000880000000000000 | false => 0x2000000040012004000000010001002000000120804084000000001000000042000040200040020000104004000200800102000800000800000010000010004080010040002002080000400200040200004200000008000000002102010480000004008000800000002004800200000004000000000000000))))) | false => (match Nat.blt i 25 with | true => (match Nat.blt i 21 with | true => (match Nat.blt i 19 with | true => (match Nat.blt i 18 with | true => 0x1011601000040000210001000000001000008160840000200000000000000000200401048408012280080600000000008000008800000000000008000000000001008000040001200608000000000020848804000800028000000800000000000008000000000008080008000000000000000800000008000000000000000 | false => 0x60800000000000000000014004000400800000000000000000000000000000008000000122000002000004020000000000000000000001200200000000000200800000000000020000000400000000000000104040004200000040000000000000004002000000000000000000000000000) | false => (match Nat.blt i 20 with | true => 0x120408001002480200400000041240004008001008000048000000010410200420000000402000080080000200008020008000208000000000000001020420100000800020080020008000040020002080000040800000000000000008400040800000480000000000000008008000000000000000000000000000 | false => 0x20000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000040000000000000000000000000000000000000000000000000200000000000000000000100000000000000000000000000000)) | false => (match Nat.blt i 23 with | true => (match Nat.blt i 22 with | true => 0x4002000000000000000200000042000202080000000000000020000000400000000000010040000000000040048000000000000000000000402000004000004480000001000000000000000000000000000000010020002002800000000000000000010600000000000000000000000000000 | false => 0x40000000000200000000000000400000000800000000020000000001000000200000000004000000000000000000000000000080000000000000000000200000000000008000040000000100000000000000000000000000000000000000000008000000000000000000000800000000000000000000000000000) | false => (match Nat.blt i 24 with | true => 0x220000404000468208000100020002020000420688000808000000006000000280004000800000000001460480000000000400080000000000000140000064828000440000008800000006000000000000000000000000000001260280028000000000000000000000060000000000000000000000000000000 | false => 0x14062006480080002860806000000014004880208080002800000080000000126040002800800048008000000000000880000000000000800000000000000012082800400080004880000080000000608000000000000000000000000000000080800080000000000000000000000080000000000000000000000000000000))) | false => (match Nat.blt i 29 with | true => (match Nat.blt i 27 with | true => (match Nat.blt i 26 with | true => 0x1000010000000000000000020000000000000000000000000000000000080000000000000000008000000000000040000000000000000000000000000040000000000000000000000000000000000800000000008000000000000000000000000000200000000000000000000000000000000000000000000000 | false => 0x102104810004000120000000000000002080000480000000000000000000000000800804080000020800000800000000000000080000000000000000000000000004080000000002000800000000000080080008000000080000000000000000000000000000000800000000000000000000000000000000000000000000000) | false => (match Nat.blt i 28 with | true => 0x80000000000000000000040000000000000000000000000000000000000000000000000200000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000 | false => 0x200800004008000800800000402000000000004080000000000000040020000000000000000000000000002000800000000000000000000000000004200000208000000000000000000000000000000000000000000000000000004800000000000000000000000000000000000000000000000000000000000000)) | false => (match Nat.blt i 31 with | true => (match Nat.blt i 30 with | true => 0x2000040000000080000000200000000000000000800000000000000008000000000000000000000000004000000000000000000000000000000000400000080000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000 | false => 0x460280028808000488080008000000060808000000000008000000000000000680080000000000000000000000000008000000000000000000000000000000068800000800000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000) | false => (match Nat.blt i 32 with | true => 0x1208408040000000200000000000000008000000800000000000000000000000008000008000000080000000000000000000000000000000000000000000000000008000000000008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => (match Nat.blt i 33 with | true => 0x6880800080000000800000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))
def orbitPidBlock (i : ℕ) : ℕ := 0x64602d2c241e1918100f0d0c0a0907060504030201
def orbitPid (i : ℕ) := Nat.land (Nat.shiftRight (orbitPidBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def orbitBits (i : ℕ) : ℕ := (match Nat.blt i 10 with | true => (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0xffffff00ff00ff00ffffff00ff00ff000000ff00000000000000ff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000ffffff00ff00ff00ffffff00ff00ff000000ff00000000000000ff00000000 | false => 0xfffffff0fff0fff00ff0fff00ff00ffffffffffffffffffffffffffffffffff000f00ff000f000f0000000f00000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000fffffff0fff0fff00ff0fff00ff00ff00000000000000000000000000000000000f00ff000f000f0000000f00000000) | false => (match Nat.blt i 3 with | true => 0xfff0fff0fff0fff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff0fff0fff0fff0fff00ff00ff00ff00ff000f000f000f000f000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000000f000f000f000f0000000000000000 | false => (match Nat.blt i 4 with | true => 0x3f3303003f330300ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff3f3303003f330300ffffffffffffffff00000000000000003f3303003f3303000000000000000000ffffffffffffffff0000000000000000000000000000000000000000000000003f3303003f330300 | false => 0x3fffffff00ff03ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000003300ff00000000))) | false => (match Nat.blt i 7 with | true => (match Nat.blt i 6 with | true => 0x3fff0fff3fff0fff0f3f0f0f0f3f0f0f3fff0fff3fff0fff0f3f0f0f0f3f0f0f3fff0fff3fff0fff0f3f0f0f0f3f0f0f3fff0fff3fff0fff0f3f0f0f0f3f0f0f030f000f030f000f0003000000030000030f000f030f000f0003000000030000030f000f030f000f0003000000030000030f000f030f000f0003000000030000 | false => 0x3fffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0f3f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030f0f0f000f000f000f000f000f000f000f000f000f000f0003000f00000000) | false => (match Nat.blt i 8 with | true => 0x3fff3fff0fff0fffffffffffffffffff03ff03ff00ff00ffffffffffffffffff00ff00ff00ff00ff3fff3fff0fff0fff00ff00ff00ff00ff03ff03ff00ff00ff003f003f000f000f00ff00ff00ff00ff000300030000000000ff00ff00ff00ff0000000000000000003f003f000f000f00000000000000000003000300000000 | false => (match Nat.blt i 9 with | true => 0x3f3f3f3f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f03030303000000000f0f0f0f0f0f0f0f000000000000000003030303000000003f3f3f3f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f03030303000000000f0f0f0f0f0f0f0f00000000000000000303030300000000 | false => 0x4f4f0404ffffffff000000004f4f0404ffffffffffffffffffffffffffffffff4f4f0404ffffffff000000004f4f0404ffffffffffffffffffffffffffffffff000000000000000000000000000000004f4f0404ffffffff000000004f4f0404000000000000000000000000000000004f4f0404ffffffff000000004f4f0404)))) | false => (match Nat.blt i 15 with | true => (match Nat.blt i 12 with | true => (match Nat.blt i 11 with | true => 0x4fffffff00ffffff00ffffff00ff04ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff004f00ff000000ff000000ff00000004 | false => 0x4fffffff04ffffff00ff4fff00ff04ff4fffffff04ffffff00ff4fff00ff04ff004f00ff000400ff0000004f00000004004f00ff000400ff0000004f000000044fffffff04ffffff00ff4fff00ff04ff4fffffff04ffffff00ff4fff00ff04ff004f00ff000400ff0000004f00000004004f00ff000400ff0000004f00000004) | false => (match Nat.blt i 13 with | true => 0x7fff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fff0000 | false => (match Nat.blt i 14 with | true => 0x50ff0050ffffffff50ff0050ffffffff0000000050ff00500000000050ff0050ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000050ff0050ffffffff50ff0050ffffffff0000000050ff00500000000050ff0050 | false => 0x50ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff00000050))) | false => (match Nat.blt i 18 with | true => (match Nat.blt i 16 with | true => 0x7fffffff0f1fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f7fff0f0f0f1f030f0f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000030f000000007fffffff0f1fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f7fff0f0f0f1f030f0f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000030f00000000 | false => (match Nat.blt i 17 with | true => 0x75107510ffffffffffffffffffffffff00000000ffffffff75107510ffffffff000000007510751000000000ffffffff0000000000000000000000007510751075107510ffffffffffffffffffffffff00000000ffffffff75107510ffffffff000000007510751000000000ffffffff00000000000000000000000075107510 | false => 0x7f3f7f3f373337337f3f7f3f373337337f3f7f3f373337337f3f7f3f3733373313031303010001001303130301000100130313030100010013031303010001007f3f7f3f373337337f3f7f3f373337337f3f7f3f373337337f3f7f3f373337331303130301000100130313030100010013031303010001001303130301000100)) | false => (match Nat.blt i 19 with | true => 0x7fff3fff3fff37ff7fff3fff3fff37ff333f333f333f3333333f333f333f3333ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000001333033303330133133303330333013300030003000300000003000300030000 | false => (match Nat.blt i 20 with | true => 0x7755ffff7755ffff55557755555577557755ffff7755ffff555577555555775511005555110055550000110000001100110055551100555500001100000011007755ffff7755ffff55557755555577557755ffff7755ffff55557755555577551100555511005555000011000000110011005555110055550000110000001100 | false => 0x7777ffff7755ffffffffffffffffffff5555555555555555555577775555775551115555111055555555555555555555000000000000000000005111000011107777ffff7755ffffffffffffffffffff555555555555555555557777555577555111555511105555555555555555555500000000000000000000511100001110)))))
def orbitPatternBlock (i : ℕ) : ℕ := 0x15140311131203110410020f0e0a0d0c0c0b0b01010a0908070605040303020100
def orbitPattern (i : ℕ) := Nat.land (Nat.shiftRight (orbitPatternBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def orbitWords (i : ℕ) : ℕ := (match Nat.blt i 11 with | true => (match Nat.blt i 5 with | true => (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffff53ffffffffffffff5fffffffffffffff5f4f5fffffffffff3f3353ff7fff7754 | false => 0x3fffffff3fff0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f3f3f3f0f0f0f0fffffffffffffffff0fffffff0fff0fffffffffffffffffff03ffffff03ff00ff0fffffff0fff0fff030f00ff030f000f3f3303ff3f330300) | false => (match Nat.blt i 3 with | true => 0x4fffffffffffffff00ffffff4fff04ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4fffffff04ffffff00ff4fff00ff04ff4fffffffffffffff00ff4fff4fff04ff00ffffff00ff00ff00ffffff00ff00ff4f4f04ffffffffff000000ff4f4f0404 | false => (match Nat.blt i 4 with | true => 0x50ffffffffffffff50ffffffffffffff000050ff50ff0050000050ff50ff0050ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff50ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffffffffffff50ffffffffffffff000050ff50ff0050000050ff50ff0050 | false => 0x4f4f0404ffffffff000000004f4f0404ffffffffffffffffffffffffffffffff4f4f0404ffffffff000000004f4f0404ffffffffffffffffffffffffffffffff000000000000000000000000000000004f4f0404ffffffff000000004f4f0404000000000000000000000000000000004f4f0404ffffffff000000004f4f0404))) | false => (match Nat.blt i 8 with | true => (match Nat.blt i 6 with | true => 0x75107510ffffffffffffffffffffffff00000000ffffffff75107510ffffffff000000007510751000000000ffffffff0000000000000000000000007510751075107510ffffffffffffffffffffffff00000000ffffffff75107510ffffffff000000007510751000000000ffffffff00000000000000000000000075107510 | false => (match Nat.blt i 7 with | true => 0x7fff7754ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff75107510ffffffffffffffffffffffff4f4f0404ffffffffffffffffffffffff50ff0050ffffffff50ff0050ffffffff4f4f0404ffffffff3f3303007fff7754 | false => 0x7fffffff7f5fffffffffffffffffffff7f5fffff7f5fffff7f7f7fff5f5f7f5f53ffffff1150ffff5fffffff5f5fffff11005fff11005f5f030353ff000011507fffffff7f5fffffffffffffffffffff7f5fffff7f5fffff7f7f7fff5f5f7f5f53ffffff1150ffff5fffffff5f5fffff11005fff11005f5f030353ff00001150)) | false => (match Nat.blt i 9 with | true => 0x3f3f3f3f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f03030303000000000f0f0f0f0f0f0f0f000000000000000003030303000000003f3f3f3f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f03030303000000000f0f0f0f0f0f0f0f00000000000000000303030300000000 | false => (match Nat.blt i 10 with | true => 0x7fffffff3f73ffffffffffffffffffffffffffffffffffffffffffffffffffff53ffffff0150ffffffffffffffffffff3f3353ff3f330350ffffffffffffffff7fffffff3773ffff7fffffff3f73ffff7f3f7fff37333773ffffffffffffffff53ffffff0150ffff53ffffff0150ffff130353ff010001503f3353ff3f330350 | false => 0x50ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff0000005050ffffff0050ffff50ffffff0050ffff000050ff00000050000050ff00000050)))) | false => (match Nat.blt i 16 with | true => (match Nat.blt i 13 with | true => (match Nat.blt i 12 with | true => 0xffffff00ff00ff00ffffff00ff00ff000000ff00000000000000ff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000ffffff00ff00ff00ffffff00ff00ff000000ff00000000000000ff00000000 | false => 0x3f3303003f330300ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff3f3303003f330300ffffffffffffffff00000000000000003f3303003f3303000000000000000000ffffffffffffffff0000000000000000000000000000000000000000000000003f3303003f330300) | false => (match Nat.blt i 14 with | true => 0x7fffffff3773ffff7fffffff3773ffff7f3f7fff373337737f3f7fff3733377353ffffff0150ffff53ffffff0150ffff130353ff01000150130353ff010001507fffffff3773ffff7fffffff3773ffff7f3f7fff373337737f3f7fff3733377353ffffff0150ffff53ffffff0150ffff130353ff01000150130353ff01000150 | false => (match Nat.blt i 15 with | true => 0x7fffffffffffffff7fffffff7fff77ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffff77ffffff7fff7fff77ff77ff7fffffffffffffff7fff7fff7fff77ff13ffffff13ff55ff13ffffff03ff11ff5f4f57ffffffffff130313ff4f4f1504 | false => 0xfffffff0fff0fff00ffffff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000f000f000f000f00000000000000000fffffff0fff0fff00ff0fff00ff00ff00ffffff00ff00ff00ffffff00ff00ff000f00ff000f000f000000ff00000000))) | false => (match Nat.blt i 19 with | true => (match Nat.blt i 17 with | true => 0x7f3f7f3f373337337f3f7f3f373337337f3f7f3f373337337f3f7f3f3733373313031303010001001303130301000100130313030100010013031303010001007f3f7f3f373337337f3f7f3f373337337f3f7f3f373337337f3f7f3f373337331303130301000100130313030100010013031303010001001303130301000100 | false => (match Nat.blt i 18 with | true => 0x7fffffffffffffff7fffffffffffffff7f3f7fff77ff37737f3f7fff77ff3773ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffff3773ffff7fffffff3773ffff7f3f7fff373337737f3f7fff3733377353ffffffffffffff53ffffffffffffff130353ff51ff0150130353ff51ff0150 | false => 0x7fffffffffffffffffffffffffffffff7fffffff7fffffff7f7f7fff5fff7f5fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffff7f5fffffffffffffffffffff7f5fffff7f5fffff7f7f7fff5f5f7f5f53ffffffffffffff5fffffffffffffff130f5fff53ff5f5f030353ff50ff1150)) | false => (match Nat.blt i 20 with | true => 0x3fffffff3fff0fffffffffffffffffff3fff0fff3fff0fff3f3f3fff0f3f0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f3f3f3f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f03ffffff03ff00ff0fffffff0fff0fff030f00ff030f000f030303ff00030000 | false => (match Nat.blt i 21 with | true => 0x7fffffffffffffff7fff7fff7fff77ffffffffffffffffffffffffffffffffff5f4f57ffffffffff1303134f4f4f1504ffffffffffffffffffffffffffffffff7fffffff77ffffff7fff7fff77ff77ff7fffffffffffffff7fff7fff7fff77ff134f57ff110455ff1303134f010011045f4f57ffffffffff1303134f4f4f1504 | false => 0x7fffffffffffffffffffffffffffffff7fffffffffffffff7fff7fffffffffff53ffffff7554ffff5fffffffffffffff134f5fff11045fff130353ff751075547fffffffffffffffffffffffffffffff7fffffffffffffff7fff7fffffffffff53ffffff7554ffff5fffffffffffffff134f5fff11045fff130353ff75107554)))))
def orbitCut (r : ℕ) := orbitWords (orbitPattern r)
def permShort (pi x : ℕ) := permuteStraight (permNum pi) x
lemma permShort_eq (p : PIndex) {x : ℕ} (_bound : x < 1024) :
    permShort p.val x = permuteBits (permNum p.val) x := rfl
def dirPi (code : ℕ) := Nat.mod (Nat.land (Nat.shiftRight code 7) 127) 120
def dirEnv (code : ℕ) := Nat.mod (Nat.land code 127) 95
def dirStrip (code : ℕ) := Nat.land (Nat.shiftRight code 14) 1023
def dropPi (code : ℕ) := Nat.mod (Nat.shiftRight (Nat.sub code 1024) 1) 120
def dirLex (a b x y : ℕ) := Nat.blt x a || (Nat.beq x a && Nat.blt y b)
def compareMoved (a b x y code : ℕ) :=
  match Nat.beq (Nat.land code 1) 0 with
  | true => dirLex a b x y
  | false => dirLex a b y x
def dirClause (a na b code : ℕ) :=
  match Nat.beq code 0 with
  | true => Nat.beq (Nat.land na (negativeHalves b)) 0
  | false => match Nat.blt code 1024 with
    | true => memoClique a b code
    | false => match Nat.blt code 16777216 with
      | true =>
        let p := dropPi code
        compareMoved a b (permShort p a) (permShort p b) code
      | false =>
        let p := dirPi code
        memoRouteBlock (dirEnv code) (permShort p a) (permShort p b) (dirStrip code)
def orbitMin (b : ℕ) := repNum (Nat.mod (Nat.div (firstKey b) 120) 34)
def orbitPerm (j : ℕ) : PIndex := ⟨Nat.mod (orbitPid j) 120, Nat.mod_lt _ (by decide : 0<120)⟩
def orbitPiece (r j : ℕ) :=
  let a := repNum r
  match Nat.beq (permShort (orbitPerm j).val a) a with | true => orbitBits j | false => 0
def maskUnion (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.lor (orbitPiece r n) (maskUnion r n)
def dirMask (r g : ℕ) := Nat.land (Nat.shiftRight (acceptRow r) (Nat.shiftLeft g 6)) 18446744073709551615
def dirSlice (a na base : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, bits, _ => Nat.beq bits 0
  | n+1, bits, after =>
    match Nat.beq bits 0 with
    | true => true
    | false =>
      let j := bits.log2
      let next := Nat.sub after 1
      match dirClause a na (Nat.add base j) (dCase (dRef next)) with
      | true => dirSlice a na base n (Nat.xor bits (Nat.shiftLeft 1 j)) next
      | false => false
def dirRow (r : ℕ) :=
  let a := repNum r
  scanDown (fun g => dirSlice a (negativeHalves a) (Nat.shiftLeft g 6) 64 (dirMask r g)
    (dAfter (Nat.add (Nat.shiftLeft r 4) g))) 16
def dDownCheck (j b : ℕ) :=
  !(orbitBits j).testBit b || Nat.blt (permShort (orbitPerm j).val b) b
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma dAllDown : scanDown (fun j => scanDown (dDownCheck j) 1024) 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma dAllUnion : scanDown (fun r => Nat.beq (orbitCut r) (maskUnion r 21)) 34 = true := by decide +kernel
set_option maxRecDepth 10000 in
lemma dAllClass : scanDown (fun b => (classRow (Nat.mod (Nat.div (firstKey b) 120) 34)).testBit b) 1024 = true := by
  decide +kernel
set_option maxRecDepth 10000 in
lemma dAllCover : scanDown (fun r => scanDown (fun s => Nat.blt (repNum s) (repNum r) ||
    bitSub (classRow s) (Nat.lor (orbitCut r) (acceptRow r))) 34) 34 = true := by decide +kernel
lemma maskUnion_smaller {r b : ℕ} (ra : repNum r < 1024) (bb : b < 1024) {n : ℕ}
    (bound : n ≤ 21) (hit : (maskUnion r n).testBit b = true) :
    ∃ p : PIndex, permuteBits (permNum p.val) (repNum r) = repNum r ∧ permuteBits (permNum p.val) b < b := by
  induction n with
  | zero => simp [maskUnion] at hit
  | succ k ih =>
    change ((orbitPiece r k ||| maskUnion r k).testBit b = true) at hit
    rcases Bool.or_eq_true_iff.mp ((Nat.testBit_or ..) ▸ hit) with step | smaller
    · unfold orbitPiece at step
      cases eq : Nat.beq (permShort (orbitPerm k).val (repNum r)) (repNum r) with
      | false => simp [eq] at step
      | true =>
        simp only [eq] at step
        refine ⟨orbitPerm k,?_,?_⟩
        · rw [←permShort_eq (orbitPerm k) ra]
          exact Nat.eq_of_beq_eq_true eq
        · have check := @scanDown_at _ _ (@scanDown_at _ _ dAllDown k (by omega)) b bb
          simp only [dDownCheck,step,Bool.not_true,Bool.false_or] at check
          rw [←permShort_eq (orbitPerm k) bb]
          exact Nat.blt_eq.mp check
    · exact ih (by omega) smaller
lemma dirCoverAt (r : Fin 34) (b : Fin 1024) (order : repNum r.val ≤ orbitMin b.val) :
    (orbitCut r.val).testBit b.val = true ∨ (acceptRow r.val).testBit b.val = true := by
  let s := chooseRow b
  have hb : (classRow s.val).testBit b.val = true := @scanDown_at _ _ dAllClass b.val b.isLt
  have hc := @scanDown_at _ _ (@scanDown_at _ _ dAllCover r.val r.isLt) s.val s.isLt
  rcases Bool.or_eq_true_iff.mp hc with lt | compatible
  · exact False.elim ((Nat.not_lt_of_ge order) (Nat.blt_eq.mp lt))
  · have h := bitSub_use compatible b.val hb
    change ((orbitCut r.val ||| acceptRow r.val).testBit b.val = true) at h
    simpa only [Nat.testBit_or,Bool.or_eq_true] using h
lemma dirSlice_at {a na base n bits after k : ℕ} (ok : dirSlice a na base n bits after = true)
    (member : bits.testBit k = true) : ∃ code, dirClause a na (base+k) code = true := by
  induction n generalizing bits after with
  | zero =>
    have z : bits = 0 := Nat.eq_of_beq_eq_true ok
    simp [z] at member
  | succ n ih =>
    simp only [dirSlice] at ok
    have neq : Nat.beq bits 0 = false := Bool.eq_false_iff.mpr (fun h => by
      have z := Nat.eq_of_beq_eq_true h
      simp [z] at member)
    simp only [neq] at ok
    let j := bits.log2
    let code := dCase (dRef (Nat.sub after 1))
    change (match dirClause a na (base+j) code with | true => _ | false => _) = true at ok
    cases tested : dirClause a na (base+j) code with
    | false => simp [tested] at ok
    | true =>
      simp only [tested] at ok
      by_cases eq : k=j
      · exact ⟨code,eq ▸ tested⟩
      · apply ih ok
        change (bits ^^^ (1 <<< j)).testBit k = true
        simp only [Nat.testBit_xor,Nat.one_shiftLeft,Nat.testBit_two_pow,member]
        simp [eq,Ne.symm eq]
lemma dirRowCoverage (r : Fin 34) (ok : dirRow r.val = true) (b : Fin 1024)
    (member : (acceptRow r.val).testBit b.val = true) :
    ∃ code, dirClause (repNum r.val) (negativeHalves (repNum r.val)) b.val code = true := by
  let g := b.val / 64
  let k := b.val % 64
  have bounded : g < 16 := by dsimp [g]; omega
  have picked : (dirMask r.val g).testBit k = true := by
    change (((acceptRow r.val) >>> (g <<< 6)) &&& (2^64-1)).testBit k = true
    simp only [Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · have idx : (g <<< 6)+k=b.val := by dsimp [g,k]; rw [Nat.shiftLeft_eq]; omega
      simpa only [idx] using member
    · exact Nat.mod_lt _ (by decide)
  have block := @scanDown_at _ _ ok g bounded
  obtain ⟨code,h⟩ := dirSlice_at block picked
  have index : (g <<< 6)+k=b.val := by dsimp [g,k]; rw [Nat.shiftLeft_eq]; omega
  change dirClause _ _ ((g <<< 6)+k) code = true at h
  exact ⟨code,by simpa only [index] using h⟩
def badDir (a b : ℕ) :=
  ∃ P : Feature → Slot → Prop, (∃ z, present (fsCode a) (fsCode b) (rows z) none) ∧
    capacity (fsCode a) (fsCode b) P ∧ layout (fsCode a) (fsCode b) P
lemma changedDir {a b : ℕ} (p : PIndex) (h : badDir a b) :
    badDir (permuteBits (permNum p.val) a) (permuteBits (permNum p.val) b) := by
  obtain ⟨P,d,c,l⟩ := h
  exact ⟨_,dirty_moves p d,transfer_layout c l p⟩
lemma reversedDir {a b : ℕ} (h : badDir a b) : badDir b a := by
  obtain ⟨P,d,c,l⟩ := h
  have eq : present (fsCode b) (fsCode a) = present (fsCode a) (fsCode b) := by
    funext U z
    apply propext
    cases z with
    | some v => rfl
    | none => exact and_comm
  refine ⟨P,by rwa [eq],?_,by simpa only [layout,eq] using l⟩
  intro v
  obtain ⟨s,all,sz,occ⟩ := c v
  exact ⟨s,all,sz,fun h => occ h.symm⟩
set_option maxRecDepth 10000 in
lemma leastRep : scanDown (fun x => Nat.ble (repNum (firstKey x / 120 % 34)) x) 1024 = true := by decide +kernel
lemma mkSmallDir {a b x y : ℕ} (yb : y < 1024) (lex : dirLex a b x y = true) :
    x*1024+y < a*1024+b := by
  obtain lt | h := Bool.or_eq_true_iff.mp lex
  · have := Nat.blt_eq.mp lt
    omega
  · obtain ⟨eq,lt⟩ := Bool.and_eq_true_iff.mp h
    have := Nat.eq_of_beq_eq_true eq
    have := Nat.blt_eq.mp lt
    omega
lemma memoEnvSound {c a b t : ℕ} (ok : memoRouteBlock c a b t = true) : routeBlock c a b t = true := by
  have eq : memoRouteBlock c a b t = routeBlock c a b t := by
    simp only [memoRouteBlock,routeBlock,memoEnv,validEnv,memoCold,coldMask,negativeMemo_eq,positiveMemo_eq]
    rfl
  exact eq ▸ ok
lemma memoCliqueSound {a b c : ℕ} (ct : c < 1024) (ok : memoClique a b c = true) : validClique a b c = true := by
  apply quickClique_sound ct
  simpa only [memoClique,quickClique,negativeMemo_eq] using ok
lemma stepIntoEnv (allEnv : ∀ c : RouteId, rejectsEnvelope (mappedEnv c))
    (c : RouteId) {a b t : ℕ} (ok : routeBlock c.val a b t = true) (h : badDir a b) : False := by
  obtain ⟨P,_,cap,model⟩ := h
  obtain ⟨good,test⟩ := Bool.and_eq_true_iff.mp ok
  change (if (mappedEnv c).val=199 then _ else _) = true at test
  split at test
  · rename_i idx
    obtain ⟨Q',cq,lq⟩ := strippedLinear good test cap model
    exact allEnv c 1 1 Q' (by simpa only [idx] using diagonal_limit) cq lq
  · obtain ⟨Q',cq,lq⟩ := strippedOrdinary good cap model
    exact allEnv c _ _ Q' test cq lq
lemma orbitMin_eq (b : Fin 1024) :
    permuteBits (permNum (chooseP b).val) b.val = orbitMin b.val := canonical_row b
lemma excludeDir (checks : ∀ r : Fin 34, dirRow r.val = true)
    (allEnv : ∀ c : RouteId, rejectsEnvelope (mappedEnv c))
    (a b : Fin 1024) (h : badDir a.val b.val)
    (minimum : ∀ x y : Fin 1024, badDir x.val y.val →
      a.val*1024+b.val ≤ x.val*1024+y.val) : False := by
  let r := chooseRow a
  let target (p : PIndex) (z : Fin 1024) : Fin 1024 :=
    ⟨permuteBits (permNum p.val) z.val,permute_bound p z.val⟩
  have minMoved (p : PIndex) := minimum (target p a) (target p b) (changedDir p h)
  have minSwap (p : PIndex) := minimum (target p b) (target p a) (changedDir p (reversedDir h))
  have ha : repNum r.val = a.val := by
    have lb := minMoved (chooseP a)
    change a.val*1024+b.val ≤ permuteBits _ a.val*1024 + (target (chooseP a) b).val at lb
    rw [canonical_row] at lb
    have ub : repNum r.val ≤ a.val := Nat.ble_eq.mp (@scanDown_at _ _ leastRep a.val a.isLt)
    have ts := (target (chooseP a) b).isLt
    change a.val*1024+b.val ≤ repNum r.val*1024+_ at lb
    omega
  have bound : repNum r.val ≤ orbitMin b.val := by
    have low := minSwap (chooseP b)
    change a.val*1024+b.val ≤ permuteBits _ b.val*1024 + (target (chooseP b) a).val at low
    rw [orbitMin_eq] at low
    have := (target (chooseP b) a).isLt
    omega
  have member : (acceptRow r.val).testBit b.val = true := by
    rcases dirCoverAt r b bound with excluded | keep
    · have matchCut := Nat.eq_of_beq_eq_true (@scanDown_at _ _ dAllUnion r.val r.isLt)
      change orbitCut r.val = maskUnion r.val 21 at matchCut
      rw [matchCut] at excluded
      obtain ⟨p,fixed,down⟩ := maskUnion_smaller (ha ▸ a.isLt) b.isLt (by decide) excluded
      rw [ha] at fixed
      have cmp := minMoved p
      change a.val*1024+b.val ≤ permuteBits _ a.val*1024+permuteBits _ b.val at cmp
      rw [fixed] at cmp
      omega
    · exact keep
  obtain ⟨code,ok⟩ := dirRowCoverage r (checks r) b member
  rw [ha] at ok
  unfold dirClause at ok
  cases zero : Nat.beq code 0 with
  | true =>
    simp only [zero] at ok
    obtain ⟨_,⟨z,za,zb⟩,_,_⟩ := h
    have cold : coldMask a.val b.val = 0 := by
      change (negativeSig a.val).land (negativeSig b.val) = 0
      rw [←negativeHalves_good a,←negativeHalves_good b]
      exact Nat.eq_of_beq_eq_true ok
    have bit : (coldMask a.val b.val).testBit z.val = true := by
      simp only [coldMask,Nat.testBit_and,(negative_has _ z).mpr za,(negative_has _ z).mpr zb,Bool.true_and]
    simp [cold] at bit
  | false =>
    simp only [zero] at ok
    change (match Nat.blt code 1024 with | true => _ | false => _) = true at ok
    cases small : Nat.blt code 1024 with
    | true =>
      simp only [small] at ok
      obtain ⟨_,_,c,l⟩ := h
      exact clique_check_sound (memoCliqueSound (Nat.blt_eq.mp small) ok) c l
    | false =>
      simp only [small] at ok
      change (match Nat.blt code 16777216 with | true => _ | false => _) = true at ok
      cases down : Nat.blt code 16777216 with
      | true =>
        simp only [down] at ok
        let p : PIndex := ⟨dropPi code,Nat.mod_lt _ (by decide : 0<120)⟩
        change compareMoved _ _ (permShort p.val a.val) (permShort p.val b.val) _ = true at ok
        rw [permShort_eq p a.isLt,permShort_eq p b.isLt] at ok
        unfold compareMoved at ok
        change (match Nat.beq (Nat.land code 1) 0 with | true => _ | false => _) = true at ok
        cases orient : Nat.beq (Nat.land code 1) 0 with
        | true =>
          simp only [orient] at ok
          exact (Nat.not_lt_of_ge (minMoved p)) (mkSmallDir (target p b).isLt ok)
        | false =>
          simp only [orient] at ok
          exact (Nat.not_lt_of_ge (minSwap p)) (mkSmallDir (target p a).isLt ok)
      | false =>
        simp only [down] at ok
        let p : PIndex := ⟨dirPi code,Nat.mod_lt _ (by decide : 0<120)⟩
        let c : RouteId := ⟨dirEnv code,Nat.mod_lt _ (by decide : 0<95)⟩
        change memoRouteBlock c.val (permShort p.val a.val) (permShort p.val b.val) (dirStrip code) = true at ok
        rw [permShort_eq p a.isLt,permShort_eq p b.isLt] at ok
        exact stepIntoEnv allEnv c (memoEnvSound ok) (changedDir p h)
lemma dirDispatch (checks : ∀ r : Fin 34, dirRow r.val = true)
    (allEnv : ∀ c : RouteId, rejectsEnvelope (mappedEnv c)) (A B : Finset V) (P : Feature → Slot → Prop)
    (dirty : ∃ r, present A B (rows r) none) (cp : capacity A B P) (lh : layout A B P) : False := by
  classical
  let claim (k : ℕ) := ∃ a b : Fin 1024, a.val*1024+b.val = k ∧ badDir a.val b.val
  have first : ∃ k, claim k := by
    refine ⟨_,fsWord A,fsWord B,rfl,P,?_,?_,?_⟩
    · simpa only [fsRound] using dirty
    · simpa only [fsRound] using cp
    · simpa only [fsRound] using lh
  obtain ⟨a,b,atKey,bad⟩ := Nat.find_spec first
  refine excludeDir checks allEnv a b bad (fun x y w => ?_)
  rw [atKey]
  exact Nat.find_min' first ⟨x,y,rfl,w⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR0 : dirRow 0 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR1 : dirRow 1 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR2 : dirRow 2 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR3 : dirRow 3 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR4 : dirRow 4 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR5 : dirRow 5 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR6 : dirRow 6 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR7 : dirRow 7 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR8 : dirRow 8 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR9 : dirRow 9 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR10 : dirRow 10 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR11 : dirRow 11 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR12 : dirRow 12 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR13 : dirRow 13 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR14 : dirRow 14 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR15 : dirRow 15 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR16 : dirRow 16 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR17 : dirRow 17 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR18 : dirRow 18 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR19 : dirRow 19 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR20 : dirRow 20 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR21 : dirRow 21 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR22 : dirRow 22 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR23 : dirRow 23 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR24 : dirRow 24 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR25 : dirRow 25 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR26 : dirRow 26 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR27 : dirRow 27 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR28 : dirRow 28 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR29 : dirRow 29 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR30 : dirRow 30 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR31 : dirRow 31 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR32 : dirRow 32 = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma dirR33 : dirRow 33 = true := by decide +kernel
lemma dirChecks (r : Fin 34) : dirRow r.val = true := by
  fin_cases r
  · exact dirR0
  · exact dirR1
  · exact dirR2
  · exact dirR3
  · exact dirR4
  · exact dirR5
  · exact dirR6
  · exact dirR7
  · exact dirR8
  · exact dirR9
  · exact dirR10
  · exact dirR11
  · exact dirR12
  · exact dirR13
  · exact dirR14
  · exact dirR15
  · exact dirR16
  · exact dirR17
  · exact dirR18
  · exact dirR19
  · exact dirR20
  · exact dirR21
  · exact dirR22
  · exact dirR23
  · exact dirR24
  · exact dirR25
  · exact dirR26
  · exact dirR27
  · exact dirR28
  · exact dirR29
  · exact dirR30
  · exact dirR31
  · exact dirR32
  · exact dirR33
def tapeByteBlock (i : ℕ) : ℕ := (match Nat.blt i 24 with | true => (match Nat.blt i 12 with | true => (match Nat.blt i 6 with | true => (match Nat.blt i 3 with | true => (match Nat.blt i 1 with | true => 0xe80524ec001f1a5d401f190e245c001f1a0592c158ac07e80555245555706e1e190c9c245555000d1c0c9c2455cc000d1c0c99245599020d2bc9245555022c2b0594491324480162999905e801141099c0240a0044e91c011601524040b31dc0220cb004091cc022022004091cc0220cb004091c0d018b269905e8055325d714201f9916201f0c071a2020042a4564681c0c18005618005618005609592ce76ec01b021cc01a51801d51401d0308cd51801d090110005602c9c045601b0210205630c056190120d4001f1a1201d994021d1d1201d994021d1d180c2dcc04281c0c25ac04c81c09022ccc706853991c001a0a0c25cc44e81c14201a0c010517040329c830401f00b00028441c00b00008441c0900b00048841c01040b02d993ae8407e807e90173d13905e85480200c04050300979898170b90900c0189c303103a1947cf090ae8051e74330907e800d9c1e905e81152aaaa40b4541913a63286632909e808e9171502a9cc0275bd191010e01002381a014ba71905e80b060c0315a60ce99505533c94d007e866b0da10e90c0d011211010160132055b3c956d864c90be806e90c03015d18e508e99718b1980d140f00040046a81c09e900040025681c02024202216c1c0ba30004c007281c000c9944081c00044045081c0d1814032f94373506e808e9024242c8241c07e90335c00ce9dca01d07e91085533cb1a608e80ce90289cd0289cd3ec0290145a59905e8014c213905e83e4029130603010015b1016042c405e804e90e16b21970e6113a16d852c40ee804e90e030daf015b056e05e80daf041d5b0da006e803e900100216b32961c1c106e801e90b0287c90b13bb64285dbe06b635d908e80016040207bf010b056e05e81762ba1606e80401021f085cd34b0da00de803e9001502060235ba00011ba09f1a00748b1ba0db1a0602347c70534ae20ae805e9021611ac00112b60bf1a01784b2b803b1a06124c70574ae209e805e902160116b2011012609f1a11b001251b96c306e805e9030d16b1b474174420c52a0309cb021d1b8da106e803e9010f060411b20234cb91010e00c20c46f06217e92113a13706e8090390642851000000c922381c17e90b14060db10241501540371d002152151560331e01188a57095dde669de00ee806e900100411ae0133c23405e84cf0df010c04449480012900cc1e7705e80daa00000090c81b030f06039944085106039944885100009050883e00009050c83e08140610b22974e1e106e80fe90267c40103ee23360007e802e9000c040515b323945b0206e802e9862a53532408e805e9040b0324c9017102805f1a17580202809b1a02335a2224cd7065d2c50ee806e9050d0116b25a1a3c216108e801e936c15a303a86b80be801e910801f04a885db2407e806e9040510201f0e0000 | false => (match Nat.blt i 2 with | true => 0xc110e999e70a9a0d08e810e90d6586d70ce997011a116eb01e011a552fd01e0153b5f505e8970115516eb01e101303020fb15cafd204e912229a618681e53a65154be56b96ef16e805e9028ccd24881dd3190cf44ae512e805e90d020dac023b23b20b40a72301a6c20373cad4cae208e805e90216010015b310af13b303108e6863df2509e806e9050e17b318cdcd03b6e309e806e91416310160db1a0310a76c0ee8ce9908e803060c0417b20fb114b30340f92b297352e40be805e9040e11b102392c6e675c690ae803e9017c9dc405e807e9041402000bb102eea9e89cadc40ae80be902b9cb041014b257288d4f423f260be806e9100510af1553240240971e01532a320260331e0712cd4ef3422509e806e9050d01570bc886b6bdc50be80ee90942951c0f17c6a50ce811e9050326c1310c95b106e818bb4a9bb61909e8060f040eab0eab4252424280032304054ee846a307e805e9030d01000ba800002840bf1a00232828601b1e0101691ea005e807e9001316b1002480008840b51d0db0015ba57b1ea008e807e900130413ae0fae10ad01015992c205e804e90212064a00a00a60271d4ec0d700e9150226c91c202d1804070515b3010140205f1a13af02ce0efa96e408e805e9040b13b31153b40b40571e3897e70704e1529ee207e805e902160116b22533d32206e802e9304c104c400f1b034c114c4c20ab22040bae0fb304020516f4d6c307e805e90301170015b3010140207f1a13af02207a96c406e805e9040b10af1535b04b80b71e10af0402479d2a54aea20ae805e902160114b02953d2c206e802e944304210408f1b0430493010608b1b0303401a012040c71b40a0402060a31c0207a9e152d2c408e805e904010b0013ae2972bb0106e801e904000e207f1a40442e0e403b1d044532e00e20f71e10ad0401132baef0b6e009e801e900021917b22972bb0106e801e9000e0046ee40ed1d17b20400c815d405e80daa0401063cadbe0296bee00ce801e9000219070125554155615a6110e90b1201c0cc001d1a014aa59905e80174cd0101201a055040dc1a051707059143a72c07e80ce99ad942d0eb08e805e910013a220b653254b2810de805e901d111ab1020121c155542b81e050117041109004020b71a725993d32508e805e90b0285cd2172d0f706e8119415e921543b01151104501f110500ec05f21a07010c0403c090204020af1c06000090841a06000030641a06000030a41a016191010118261f02e9cd07061691901438871f1020206606006450051f1220206699006458651f0c0184272c05e8042ccc1508530a0100009002242d00009903242d140e2054001f1a03000030841a0e2054001f1a06000050041a03000010c41a07000030641a190c09205054000d1c0c09205954020d2b10050b0163303405 | false => 0x54023934155555550238340222426c811c0329ca94e43d544245371545455402311e94e47d548265371545455402711d0e0300ecd87705e809229389242d01aec594e4774480c52c060155555454083334155555550832341e4545440011291e454544001129155545540a31340155550a30341005555554140833345555515508323454e4541400032954e454140003290555555414102b3455555155102a340927364b5d1336e30ce806e90921a69a28bb84d90ce85554541410231e1636e9e35554541410431e0ba45a63a57709e812436863aed709e80103052323c9096bae38d2d70fe81b244a8706e816448ed44a8709e84d801c6454541460a3296c601c1704939b25b707e80222126c821a036fa024065555541418233405551518223410042c422c411c8d201c03000500c9020c77e0ed1c01e916b108002b8e2a201c1408002b08002baae01c07148c8ebb956609e802ebba1191d6645d3609e80eeeeeeeee02345301e5558030290e02e3807f1a01e5aa42d05301e55580102901eeae46f06b10e0508085d81a14898f45b4c985c085a65611e802e5cae3ee1e1310c3540ee11e3082540ee11e3102541900003304282417a302e9ca05308899678490d340090fe80ee11e31a254190000330628240000330728240e10802a522be596050108002b00e449a605e80114b6e805e801b2735378990b0ae806669660882b910c22c249841c1403a868ae1707e803a868ae1707e809001c0508002b0633332de22408002b0708002b0174cc66666666010c2b66666666010a2b06666920282b66666666042a336666666605ca2406696901282b0666660428330666660528331110002a0108002b08002b08002b070a030f0402948e8e0b1248ece1900e0cab0226c50191bb07e90e94930110110380821c1a081964f3e707e90be4f244e0dc99ac0ce80de90c04171a49cd06e80ee902eb91e91719cd0ae80ee90d031b73cd9707e807e90234c69401337185101b94090113118ef01f0ce90149212c05e8013371c5101b0149212c05e8013371a5f01b131904000bab0211bf5dd2d844cb08e8031302114adc794ef90ae810b10233bf035010805000ac1a0000600a84270515152368210310055d089a035b4e98ca790fe801ae3460359e330ae808140103653705e806e9652de505118160084405111522c82105111502882908090511188248210de91013040dae2342ae8406e805e909a574c9a886c2640ce806e90408a2648a56da15610ce803e90117000217b214b198030b15b00226c496000e0116b19717b003180308c9392dde920016010415b20312c398031412af28984ab806e8980311010287c99594031875b5351580031e1c201c10010405011202209f1a16b1042e475c3706e801e9979704050d19a60ce96513e013e9120302b0)) | false => (match Nat.blt i 4 with | true => 0xc231b2e892f0406e80e9999999900a333656fe5ba801e019999999900633309066e9c88f3b12c694cf00fe80133cb0905e88898a8994471321e2058150267cc26492c8775ae974ad80ee80267c62443cde7856e984eb80ee82479bcf806e809003e07799748a13e13a99304048f37c0f807e89c801e080169cc410be63030393048c31b01e9ca012c25f505e8020049900021333354c855b60f242f040ee809c1f3be416908c8ae4f242f0414e80e0eaa07797748213e1ac01e09003e1ac01e09799708213e081e4054c8ad74ca6808e8180787778a411b1244df033ab609e80125bab605e80701d0c919001c3289096e360efac2b60ee899dc67c2b608e804017f405404e94cf2e64cf2e608803e9e601e08011405030bb00bb00184a86ba59608e81300703022941b3227a4917ca6c10be801e90b2973c58606e80168c302c8c3051102119261de1a2f94c6c76c22fa42e50ee810e91111111122b8400501f1352172b72f0ae80fe9121700303348341b92272a5b2b08e81330307041541b01030e0b9d11becbcb001b290b9d0b9d2e601c170c42241c821c90013b2e43706201733b0c301b91130062464ede1c00240111111111231c1a111111110718340c011115211201da37464ede130062060335d7e75e201c39f7e7090cc22c5c221c0cc22c5c421c11be3eee41385611bee5be02386b190f05726a32dd3908e8130300b464721b0040045de21c0f19a31ec01c1c2027130300b004321b1e001c0a0e11beeebe0238560c42243c421c24e9d65442e49856f90ee80f0d95d348573709e80111111111013c411111111101384217801c1680249216d9c9d708e8111111110558411111113d04f84101cfc60901311326701b0c25442dd206e801b3e306501b11be3a3d20185601cfc60919030cc00c45821c130300bc24f21b5fa02b1711be3e1121d854050116040eb0036495dece07e83537d9010c422472e41c040f0bb0013337c1b01b04e90e030011ae5d0e8d0cd8a6b70be811b10234cb050f04254321b007e814b1059404020c04000c1c940143c51405e85111e202478a291925a50ae85111e21704026406022c2b14a10124de8805e80ea1a5d323d11408e8110f0b04b28a62263d112ca2e90fe89109099909020c1c00009002485c00060064881c0900303300092412a200009022a85c0492f89d3707e81f13c23706e800070064281c0113c91105e800070064081c00090064281c00009002485c14330030b312095d1f4445f706e817005a0a2913b61706e805160b0000330028240e4a8645ae98aee10be80be9022bcb09090939620c1c7a6573212b08e80653179d7707e80212339313a1f70ae800090386681c14010301e445444480732935d033654427370be80309c804b4004400052c0a224da224e322a90ce80b0301555455 | false => (match Nat.blt i 5 with | true => 0x5317058f35ba54b9117ca6000fe804e902115384c81a5b8895ddb708e800051114b18c2886c6003b6f92c2e310e805e90ba230c1d174d3030ce807e90362c9e50f8649191f0809e81401e7846444c2d70ae806244c053707e84647d662401c0c4c44696222048f143ef807e80106244c06e907e81403050b060209592b65f257df0e0ce80fe90114592c22578652e50de805e90e1020521240db1a4297d305e90d0216b316b30db20205328a5d2d79f2c6d2e00fe803e900100117b217b212b0010e00150000444b1a2684c25806e8050219c844b221f408e801e973614b642908e801e91706422c653407e801e996511c52c108e801e90f05000617b31701b2e006e800e900213320ff1a0013313360571a030caa129fcd8448996d08e80731b172811b4a24db0731b172811b06058db1e24899a508e80122d2e205e800060034621c0703010130031b7030303090a31b17201c0b02829125612db70ae8053151313128e31f1c20290115110c011e1e2029100c201e0c000100db964405e812ab6970913409e810a3601b970d000181116ac41e0e51154a241e1036e884b28965900be8050ba7c3c01b09c0230333c362011b7e605317000301333110011f9928744b28b2c644c2590ee80330b703e90cca1770c8895b6e66c2e310e806e903113148e12003000505c2227a44299005c2227a042905002301313110011f0284ba608a32190ae803111182c120000500230a0306050264401b44801b0200230a030605020e016239f605e804e910af96010c553605e84298dc0f13b532743eab09e80fe90b1794ca16fc1d7408e81020222225b81c0144656f05e82022222227b82c0d1552c09daa743d780be85894cdce87adf80be802c98d6c489ef40ae82053222200581e2053222201581e0d060e01018252b805e804e950f0dd10e90f02495535050033322f0fe20249553505003332014c233705e80401244d6e05e822e4ddad6d921c070184450c502c0cdd36adec4921d60ce8059d9b9e7507e8004d375a249bac9842c88a9f0f13e85939bad13c22e9c4c4b23ac613e895d724608e08e80174489905e802254508f021000724949a9906112b150194dec094d183ae649a1f53e10f15e8141001050183d2d805e807e9508ed90ee90b0093035343002b34616fe20093035343002b34014c233705e80709d709d7606f1b013449f005e80407000314481c66e9bd6c79a2150be815366e79571609e8020249bbd134dde77e11623ceb12e85539bbd12c22e9c481533e0713e801744cf905e802030310e823029ddf3460f008e80409009b9906092d160194dea294d10358f242c8f3e10b15e8140e019999999900a3339999999900833302b9b06f93ac8f3add0c06b612e801e92572491806e8044d0075c25300000049821b00000e48421b0303d303 | false => 0x4800f2b60705e81e42b60706e8111305b058da4407e805e9c4e04605e9040002060eb300e8db2505e805e90b17b20192df2605e806e90c0411b246f8d305e90b17b261e6d506e910040211ac0eac0325000505602b2102c96d2b8b1908e802e9061010b31a601b01035ae505e806e919e024051820240d04010eb38e96060b11b39199061205011c10191140551d5cb9d406e90c0287c4900296cb0619010414b19197040d0329c81925224a5c2909e801e910050329cb00590e901960471a59e91919804329058ae02f040114060202e6c412b00205cb0201010920df1a040b7148b707e806000c09e4684702e90101c1119124da1d000404e488470604140eac066c9c896e07e89e6885ba3208e8052b94ce11952d72add40ee8060c057374ae9707e805510cb5d707e8060c4263d61118911144111f1e20240c3c00331402f6cd329b32f906e80204ce963af007e80154d2d705e82a99c4f906e802060504010171c0ae05e800b742e405e804e914371171774049410ba730644a8742e40ce804e9120116b112b00205cb02eb40220401140600940ad4beee08e80fe9450f4d9b2847250be8222122c372cc22170e0ca2e95b5d2b95f70ce80fe905324722e907e805324ba57207e80f05160605f2545a3207e805e90124db2505e80137b382f01b0b0e0329ca9601373362501b051206030db117a797060b02e9c5bb5646ca1108e897060f0502e9c5bb5e76c9d108e897060b0222120ca2220222122ca22208111e0023060503025b2edb0ee90114dece05e845d6c91164e50e0be805b248a2ce07e80ee9120d309bda4b06e812e96137e41070b07080d81b120b0612b306212299041c017551333300151e017551335500151e175133330234411443711b5f2909e8120e12b30651535084326532dc12e9013231333308d5232344448906e802e48d10f0ada90ae812013231333328d51b071751333300141e1740bd3706e800f436d74ae24c1e980de82445e53406e8031751b53300341e0651533024321751b53300341e0db10651531004320032487ccf1a4a27447296c65413e81751b23300341e0401757133770235411751337502344117513333033441120e101b7b9747401b1a3343e119a21d922dd70ee85cef0e06442e9923a304ae9713e809e916207ca29706e8a216e8932808e800f2423405e81757947900324a1757947900324a039194c69707e80700ea217171308be52b0de8176e663684b23401b77328d01b17b20100eca29705e800f4c2e43d10e85f030de804e901d4cb0bae031c7cbc7c0238571bc7c7cc08315701b7b70a3057171612060510b12616666640092b0289c4030442e89c0d0d0ae82612c26624a91c14a317055db0a1d6e22da50be80be92c12c6cc04291c5e10f827033c8943b88d10e8a2d381e12d08e80320))) | false => (match Nat.blt i 9 with | true => (match Nat.blt i 7 with | true => 0x581777601f15203b0e999914013b15203b19142048170032060c001c00000c4c021c0509c9990c211c0c201c8d0c201c1795a01f94c0480c202b0c201cacc01c0e201c17140403000eac0a4003321719bad70ce814ac050f17b20271cb9805140218b316b317b2020d4e66663f0009e803e90010040eb104a96b89cb07e802e95c56e502e904711773360008e802e9000c12b303194633213a320ae802e92141212140831d04064d09df0007e802e9000c050710ab91288bb1d906e8041614b392011742f905e80416060bb11c98aef106e8051111a8841e041028785c8b06e85e8bdf0f450eba221609e8041806021651102140ef1d3343c64606e806e90c10b3104e32784a8609e806e90c0417184a8406e814e93ce8ba56ec42c40be810e904195919194023320652c810e807e804e91403020501001240df1a011065c305e803e90d10233266603d2314b314b30299b400e91211050112e013ee40151d16b1910319c640d1c91808e800e936a974a38c80c80be800e90c050410013366805d1a0174cb5a598a1dd808e80311c85a39229808e801e92487ad3806e8175b5e13c91809e8141105028c2ec28ca0c72108e90312f0d91807e81542aaa288b41b0442c478c41b08e90d1701f40db296bae50ae80de9ce1396472508e80ce905030402019a9e1505e807e9022c5c520822049c20c777902d1b19b06c95e0a909e8179516af0225cc132822179838f4e59805037077100441167852b906e803707710044103707710044103707710044108714ec6ba9008e802d8cd0295c23295dc0134d5d405e806434aa69807e8a2667431b808e8050bae15ae071006121212db7b60db1d00c9d305448d9ae1350de812a2121212aa22b81e1602b6cc60b6e7999901d06844c6ca980ae80917042e87958cc9bae50be80ee901c74d19974b050ae812e90516b276533752c508e8019456c905e8017322c505e8180c040317b2a258d95f0508e805e90e032b07cb2b402b1b308b8f28c52496bb050ee805e9160617b20db12b1b1b1b40835703060351e532362e9636e20fe805e9021604000eb12e98b96406e80be918d74815121971db040ee816e904243232c006e803e900100183c6012a8d9505e8175ca5d206e800161746130bdaa309e815e9bd412432c308e816e903040614b24a91d211e90caf041d5b0d8006e803e9001014b202e38a4a8407e812e91a7a1a1a60e32904419825132b0d800be803e900150605011002409f1a01774b0505e805e90d112b4202407b2216e95b0506e805e90d045615db10e95470db10e90d0309c517c11d1b60a909e805e90d00020161ceb605e803e90268c612e9190308c6925ae7e0a908e805e9160088581888008548990310af1e42b60706e85dc706d8b808e83057a2d806e814960a973f3209e8040851880024 | false => (match Nat.blt i 8 with | true => 0xb4bef905e8174ac52c896c09e8253ca6476044b3ba390ee80272cd0e59ee963e3509e808140ee0ee4e0e80931da2715ba5f408e840ece30102e9c0288ba57006e8022efa090906e802e9190403009797970f0d02287d12d73ef80ae814af0287c401731d3005e806e90f979702144b5d0956f80ae8050b018342b805e806e9015c34a905e80de917040182ba5805e805e9012c44e805e811e9145165d50be991004000cd301a0040992f902b00b4457205e891004000adf01a1418040312af918d01b5c6110e05f256d70407e805e904ab8b53b5d108e8022222a1e821040ea101c5bb045c2c824407e8159154eddc0bcf08a3d37ca6750ce80206100336634441341c202b1100c29a74aa6ad3d5090de81a202b11030060a2a13491628bdf18a50600bac25105e80dab19001c013cd1098c8e9ac2b80de83232e605042495d61106e80134492ca60ed946570de818001c028892595846b80ae805040e030111ae0ba817ab17140cb7429709e8070502e6c20244c442f02c05070f17b3014819d705e85d34e7050f24ece4ee20f153015a15af05e80caf082c2621e506e80244cc27902c1719070414b301789a3405e85117e7070b0e09e0ee20693b10a0545e13719097c2330be82534256c06e80700090940283b00009927a82d14190502d7138d0719340ae8016819d705e83a08e5904c409c01267400c30084a2750f0b9e4e44ee00054405a770385042653122e90fe802205609444900244404944939642b1419050ece0e0e0023560eeeee00216b050caa04407a15b00248a03bef602d05e9042045042045019604d14132d50ae83115e40188ca96020c00c01a811c0500c4581544e82a81950de802c262df42a1740ae80940606b3b801c171907040310ad52f1de2f444a9306e803910000000042381b9102e8d8ca7607e8060e01633a5605e806e905ae9b4a889592ec070b0fe818e90b07c1e92427023cf08bdaf010e816e91944f074e11709e862e9e6329938f806e8021c89a5d806e8652ee602784ace84cf190ae8001716100308c70194c27805e802dc9cbaf007e80292001603040203c60288c612e913b06265d93808e801e9911180ece0ad1809e80229cc09e902d108e11307e891000997b6482d14120705755b541560271d9a5d89d86608e803e9107dbd3d1d40a36c0b267944d39040ce5d2e14265614e871a099227008e80218070405295cc1ec06e80fe901f4c90124126155409c1e100c0190b6f905e801e96537e317e915070190c69905e801e96514e114e91301a1114ab01e0ce901511189701e01188ea6103b191807030173469705e806e95c34dd14e90f05222272e81e08e90224cca4c81c18e917070300639aa41e09e9000099e8441c18e9147bc01e06e998981920540ecccc180154192054191a2058190021069aa0 | false => 0xa01e0c0114b2f905e881e29ba32908e80d9ddddd03387206d9dddd02716b91070492f8453707e85e2671d2f846f90be80114cab905e80079d90a30721d77c61506e80838efde02b7bd90110dd9d9dd0831728a6e8aa59908e8003336ad102200d9dd0b3072184538da009994a0d0446d001e0e201e0c00994dc1106b035f13b2f507e80c4ccc4c06385d0c4ccccc07381a0ce9edee0a113b0cc9eccc0a113b0ce9ecee0a113b00c99c09101d17060099d942706b195f201e0cb32e8aa5d206e86dc05d5f201e0cb31818654cc4c61809e80fab10ab3ae6439f08d7190be807041403020daf018dcb01acc90195ca091915716a76b1d109e80db3174492dbe52c09e805de84b59907e80ce9158d4ad9454a76b1f70be85939a94ed63e570be80610015e119e4e002b2e0250c8012c22924588533e140de8015e119e4e002b2e01f0c82b245dd406e8011b1106281e01131106a81e0407011be144c85400e84a9805e80127d2d505e811a85aa7de0416af083a4481996452b80be8011bee04685403e143b11207e809190302e55952750027464af4e700f89e8f3b537910b90de802e55952750027463657e20222aa2a44540802225548c41e8d3084d1f806e800fbd23905e88d99078d02a9be328bbe950ae8061005e55955750027463e86da5b80720222220c211e1c20220d0e2054150298cd05e559557500274614b231d7c25b2c52b90be80811ae0c001e02225508241e0c001e0c001e063666666605122f03666605102f1105f095cb1407e8043655656a4114290c201e0c201e0c201e1514002f22222222020c1e0222220224214a89da01607a02222208e41e3fe05d099902225208641e0d14002f14002f0629e04501b545309aa1e60ae80c11ae0cccccefb01a078d0f24553908e80336c60b307231331355003d1a333333330d3222333333330c31223161313100181d0333330d30220e090288bd11248a25b506e806555514812f3cc0223a00721511915500092e15202f140406a5f1be2543a2950ce80603666660503201121106281e14402f1b007204060c201e0115110c211e0c201e990c201e0c0124553905e80366666070325109e61101121166681e5c202214002f0ccccc2f701a07060c201e0c201e0c201e0c201e0c10030201010120401f1a00000461681c04e90b010500100040d91a5c79d204e90b0215b312b2289cd60309e810e95ae2b2275ba5790be802e9030194521505e85a2a9852b908e803020c0112a2028fc6c66543c27208e801d0c60ae6874c235759f20ce8080b0422a2e42822052ccc10285894019510e95532c8ace5be3510e803ea16ba56c8acd5c6540fe8c87225c9f508e80517c9688b553708e805e9059141660707e842b9450542e6a90be80524cc33c8581719aa010f040329bf17a374b29adc4908e80c)) | false => (match Nat.blt i 10 with | true => 0x5e8080cc9e394257409e86510e20232665123c5890ae80222cc032862170225220448229797082b9450f002dc4965090ee80228a2dc43cb280ae80bae022c22042822022c2204282217180020973c401b00262562660429390ea11114b1018ca13705e8065364269707e818ccac889d3709e80b060d01b1c80189232c4c4cd444f40de808e9555544249ce31a626532ca402653041c43b11407e80f20240b060d0200c202050a1c02cc220d221c0b174fc022bc601a6666366621062b06636621043317a35c1c4a1dc408e817a3116d00244f802206040eb8a1d407e81800561de01b001220541c205717190301050200e7c2eb05e80be9099e886bf174aef50ce817e9153044bab606e804e940cedb0ee90d01018252b805e804e950f0dd10e90f0298466b7226350ae804e9022255c8701e11e910010501833ad805e806e9508ed90ee90b0298466d73a6360ae807e9020233d0c81e11e90e01adaf93263808e806e903010911c8051b2687c0c706e811140328adae68d9380ae806e90cd6d74e115b5f090ce80c203e5a601e1a201e0e110267cc2677593106e80267c602479bcf0aa6330ae82479bcf806e80d003e0777974c813e13a99304048f37c0f807e858c01e088cc03e04e91401050315b351174d86c8daf90be85937e3020b3229e33353323706e814ad016cdd39644c9a46770de813ae05f2658dd707e8070fcd52b2467508e8618e7cc8e8ce970be801d47e6a463a340ae8066b4246f907e80601f1c70233c82e9b2dae06e80761d2babed708e803100596019b4a8489d86c9ec90de810019acd943d53681e242e4cc81a0e15e810e90e01535505054073217c6743aed708e83a35e4052c699e3506e80310020116b103400120402f1b11b1020fb1a21e9746d708e803050b004335302360a7230282b802e90e3d37b268f856e30be810e901c7aa6ce846a30ae80ee903050100015c25d705e80154cad705e801833a1205e85709dc02a7c2056d82d70907e821233a1206e8170f928f146116e30401745ab805e808e90295cc838e883e5808e803a4743a0f07e80fe93a55e603cd07a1d43bdc6a22580fe80247451d07d8af0ae80fe91718b10b10ac721f0adaf80ce805b06be11207e822e335d206e80f09190cac91acf9199408e80592c952f807e800191e31ee40f91d3a4fe216ba5d22321809e8070126471405e805aa89628c07e8040e1bee24885414ac12ae0c2543caf506e8047228cadaf808e83912e2024ebb0c091903009592449900354718b1009d0486d01a17b309ca63033889abe066a5d910e80cc2ca9c2a745d0952cccc0334661701b8bc2267c6170ae890096328a9a19236300ce804e95dd7321cf857190be807144e601e0229cc0115110ce21e0115110cc21e0115110cc21e00c9dc2bd0720609991d1162b1442e | false => (match Nat.blt i 11 with | true => 0xbe90e0300b43e067a5d97dae10de817e904939ab20107e80ce9010114e10e0e60531d744866464808e812e9190305046c36a57707e80be9625f1adf2308e803e9100329cb97199746d906e8030b0002e9c92e95d72306e803e90fc8de63e51008e803e932c8d86906e803e9150105029915b315b3100c0cd6c84ca133ad91b13275c66614e811e98d01742c933a58d846d90de89003373adac84a790ae8060e0152325505e804e90268c612e9190518436f55cee109e80be961e156c60108e810e90105f244c67507e804e94cf1de11e91005025cf4e407e90244bf0be90e064d0be53107e806e99502acc702acc7950193c919120511b1014b8d6105e803e9a92974c6a108e804e90107c4f6ca58e94cb585ccb856e314e805e9030d02000d0556fb66e109e817e95ec6439396b1a10be80ce90101010e12ee6019202f63218b06e889e0e5a6f6235322196c45d2e5b1b718e801190311b32e7a5b2606e806e90c0cb311e67e6700171f00cadc2d05e801b1e16f70201177777700913b03116166e644721f1171777760313b3af6251c7a22c90be81177717700313b00ebd89405e897080c38f4d41171777740713b1b73d10eb10c763a880ee8190174593905e80ea1116167660411340c016c648b4b2f66ba990de82e4a1b285b594259ae0ee8071161617604d11f0ce91171777720913b0a1ef622dc7432d90ce836e7722f6433190be809111b7b132906e80d340eb746d909e80143ae2e05e81161636544913402f6cd045c8bdf2da3e50968d77b388908e82dae3346b75ec90be8190cba6cd719a359138cd0f110e82e36b8f406e805c6b6b8f407e801b7110a105601b7110a105643606e01177100f03b01373128b01b01117104701f060001a7b846b6b8f40ae81911616766043134011177043034011117063034110c032ccb17b3010635c605e806e901b77708103f018777a8103f01b77708103f168e17b61390b2d709e801e904ca627be32908e801b65d9c9b84713adc43632912e8116167660431340111770430345d2ed5110c0812050329cb9752e9e7010d05f295b6e107e80be917b2016dcb01b789e974ad990ae88ae974b1b908e8022dcb080103a6499451b108e804e90bae127c57945227711868a28b11e80be90288bf0be90d17be494ba57908e804e914b100ba117705e82574aef906e838f9452ed31d2b0be80101031033e0f91a964f442d3708e802d14598f707e8118a65745d3908e8012ba25905e88ea44877360e08e801b1cb17b3063634ca65745f290be80b1820200c0305326ca1ab07e806e90193c68d05e801871a276ca888928d0de80651489dab07e80de90b14b314b308030ba196c68dab09e803e920202c20a12c2203e917029222e272002b421d2b923406e804e901195e9905e8029222e272002b4200b8caf9 | false => 0x14105cbc1c003b1d0184adf605e802887add08ca960ae805020105c5595502191d105c595c0238292d83a2897ba5912db40ee801edc9c2174b0a5408e80c00cc04685c03100517040eac11a83ed1bae874add20be80dba2343add609e8017a1e5705e80600b3be2705e803f2899d376996e3a5d243e333c51817e8171acef89e4809e8016e3a1f191d190ae81405101555555520d11e06bc686e5c699d360ce80a21697b6a33b5380ce804e2f3a28d1d1c63b6c90fe80744ef5b92db0d390ce81702adba02e79a334457290ae81601155140301e1b4ca23406e803018452f905e847287d86e35ced0be8173510dcb8d609e838c7a5f08cc6970be804e866beb9b5c773b5d70fe805f0345af907e801555140701e26f3ba3406e802e6a232e336d90ae87d071321b908e8173510dcb8d609e80450dae6d707e801644cf5a2223ae6d70de8510fe7092687d4774bc6d71a270ee803d2d8dcc707e805a5b11bcd1b9e280ce88c1402015373567700351e6dc7944e2708e81b5b8e2706e8add2da8e2708e8556034097777142134015555209046152051144e877c6d71c6d70be805c713b5d407e858002fca674c587108e8070314adae33ae970ae84688dc015373567700351e0601555500301e0bb1033393046134000c9911287b1401555500101e02e7add39a21760ae80f001b0e001b0a028bcb1135c59380911e011555a0901e16b26136e50301555500101e0f003e015b0ee969a237c4f80de813405a08004703140f003e1135a59380511e018588588800191d1858588841181d1585858800111e0155580130451885858808112901555841101e130801555500101e0a0eb10f001b105c595000382989d6863b3608e80f001b0a02120510040114b1010a5ae405e804e9120205cb0f844f2c216409e804e914020287ca010b11d605e804e9a5d2d1c08e08e80206c28620230172352e05e8160501b63a67942dae8e2855d0e812e80da3033c330601230120410e67c023099c988cc1470888382851e4f11e07205a17a9201b0204120100017843ed92b2560ae80ce901843e067a58ea5b250de805e9170bb216a519b2050c0317b2017c8eeb05e803e9606fe603e9050143322005e803e900100216b316b30db20200dcd9c505e80ee9032cb90ce90501b14d5b91b6d70ae803e9015c823505e800e9050231aeae4c7653200be806e90003100116b303244b5d2be6c50ae816e915b3051013b013b09305190315b115b19505100bab02b095328844f10ae811e913030216b116b196030e0fab02ce9d328744910ae811e9120511b15cb5d105e9b98e9746c308e806e90365144b637c95e10be805e9010b020002d7bf0be90542441024290f059154e6ec07e817e90c0194ba1705e8064f24d6ef07e80fe917718f2ca61509e8160064f1e407e90244bf)))) | false => (match Nat.blt i 18 with | true => (match Nat.blt i 15 with | true => (match Nat.blt i 13 with | true => 0x483c111d4934c2c782197c9a2e11e800090004283c00090004283c00090004283c00099006283c120303039321cc1b06e9140c0c022c9c417a1a03002202206a240cab0033002221002b1c0300229c012a1c00c300c2c1002b1c060d844ec349194b6036d92e11e809e9cc00cc0c102a53c2002202502a21cc00c0cc1029530c00001028530033032c33012e1ba1e289993908e80c000c1108530a03002203002a24030022c3012a240e170134c19405e80254c290153a6ed8ba5909e800c6d1d205e84a76e5060c00907288550c009052a84804050b0290039003a04f1b0b300231a4200b300231e4200191cb035cd16a73694e990be80000022944240d9dc6d4e6d709e80164c1b105e800d4d73605e8060800300002043f01a9b99b199db10ae8080b030b033128651b0166451405e82166451406e83709b64c8ca5b10be80b203c1202343cecc8a2970ae80b0200003308642400003328c41b0230333024200c3033308420276a5d7906e806020e0133371605e82875b5d606e8020151e13a416508c03510022072190316c498044d33e21807e89806486584081b0844713b666b40f60ce806486584081b085855758710e91d05555518612951804544cdd9028dc60208803503222208c42403222208642408105917e705252e7962460000d007c85cb570b3344b08e818001d18001d0a5917e714b4c6d89ac809e83633d5100aceae19626b2cf143a96aa1b60be80216b99ae11e633d8d53c27611e80deead0182720aceae59626b0aceae59226b06486584c81b844713b666b36a381eb610e806486584081b085256e31b11ccf006e8844d33ae3508e80890909092224c1b90909093222c1b14a5060d005c0a62425252418c1b34c0201480200609898806a82d0ae03c0baa06082c601b0133c1b405e80602124267599b0899d20be8090c0108b1ae05e8031c26c5d107e890890097a4ea1b0eab1044667a2d9209e80eab000006ad4224060122da6eb01a02151cce96c6540ae801089e7505e80222da8e501a060253bc19040501000181de9605e803e93b17e2046e978e2607e82f84268d06e814e90d0b10b00226c496000e010181be5805e803e90227c30fe91402c9c40653510940f21f9600120105018336d805e806e901e3c10de9170248c42502510c402a1e920016010173261805e806e952e9e64c490488e0e546100f960232bd0164353205e80353331221415200410e0855e152e13b4663db36a7dfc595353120431e3995353510031f03933310223403933310024106459412413b1405555500211e0e000fab0da90393331102340920230e4500470864f445d2fa4ab60be806100105040173c91305e80113cb0805e8140f450794cad709e81843e8394e9709e802050b05b09ca21307e80189a26b05e80105cc599902391d6268e1 | false => (match Nat.blt i 14 with | true => 0x9424c6e65406e80711020911c1101160071d173e5144e60009e810e99a135b5d3008e88740460002e9cd4ac9e70b7511dc011a017111e8e11f10ab003ba76046010252e9e708801f5080200aa58578241a970291cd0328a01f020174b69105e87ae01a0288c01f10000c040501a6cd8d240000b470ec1c1706213a58d33c1164cdb70fe858f174cc885ae90be80101d93705e817e919018b32534592c763220de819e90100c008c4613c1a3238592d06e803e902a6c1020dc7c4000000302c1c090daf2c000000306c1c0617020b0275bd2b6ca6b606e83653e702d322cc7826b90ae854909cb29cca760be8990134c2d2a5487965330de8080c03003324a81bb19329a20c08e82c994d0c06e80ce91903003324481b00b6c19705e810ab016a5d7905e806040300330468244269854732213693326636e213e806e9020e010cb3295ca59506e84eb43ba29652b90be80174c00174cd00b7627905e800b7627905e80612b74ed907e8015b259905e808120653559a688c98333ab90fe806e9012cb2f91b986646950de80153467405e852ad98d9132dd30be854d3e20269c6990c07102d91a61906e803e902c9cd036a389a6707e8100c04050ca60c814c7b21740ce832985ec534227425740ee810a0051702ad9407e82e96ccd13d9658ad940ee80c6538c9e0532e740ce8080194261629a113a1740de81201313310642040b2d205e90163465405e8040e0ca5a3b21993c5140ce809e9063274465307e89404cc0000001009530c000c1028530c090c15e86517042793a20c07e8042676361707e8050194593922653a1e0c0de80329c00277b5328b25980ae83287d92c06e80329c00277b5328b25980ae80144592c05e813a110055f004f060228c84232e213b26ed8329109e801a9b21993c5140ae805512a22c99b60cbb6510fe80030002010002b240ca13994cf49220c0ce80269664f06d2570ae8053112e2060009300064491b1660200c44a878ca7909e80232c8040e992c9c920606e801494f2405e804e9163a139810d909e8206a1d1906e82878ca7406e802c9cd045259d212e9287a4a7906e80404ac7a49099e48985cd00fe81089917ca61909e80131111a2420ca2c9a4a7908e8060131111b242001844267add30a4a760de806014ca2764e49089e110de805db03c23407e80134d33205e80601b0c51e0020329bc0ed06e802c9cc910a4a760ae803669c921107e80292c8061e20201f20200c0b33337164200ee9329b219906e803039909020c1b62679c26c8ca6078a19910e803039909020c1b0a03030309000c1b03039309022c1b0e0303039321cc1b06e90b333371e4200ee916ba603a999309e818dca65906e8070211c7015ba59905e8019b192c05e810070803030393412c1b06e90909909904293c00090004283c00090044 | false => 0xc61706e80add70352e984ef90ce80129daf905e819994ed706e802990298cd01184d343cef90e2990de80329c7120279c60279c62698e65606e89e427a665608e801e9269c50394ccf1956d70ee8080c9f08a4e49caed70ce860e8cca934e6d70be80000000006181b0b0a16b1020129a71905e80129e13905e84269e504f268a21807e806e9999907045123a5b707e81400c94ec2c98e96c1740de800c98911a48d06e52b0de817010299bb5327d612014ba57205e85d2be0015c828705e86ba04502c9cb19a103154e6c0a04eb0ae81311a71c00231c00230a1cc02318b318b309a26684da5708e81c00230a060191c11c802315c1d33c229709e80102993c5306e6540ae86534b5c2b8b2170be804e815b65707e806020e050319035c6cc9130ae800e913b3427901b08ca6530be86320e100e9c81940c0f844f286993210e803279df19427320ae83259e219ad080e162993c2ed06e817e9531942667742d70be81980212c8d0e9742f30ee8ca6e784a7608e8060d0a25d79990d85f210ce80de9be52e94f2108e813e9010204035d174ad941432e0be810e92c9a2cc8aad929db220ee802e90e12ae19ac15ae02100515b3016ae58205e80ce902b0b610e902ccd358168108e805e901170414b15c8ee504e9324a1a3906e804e9058e0191c805041214b10142ae8405e805e98d109acee408e809e904940276cb04050d020005b374aee107e80be92a95d33706e804d2bae5d707e80119a8032786535bd86e0ae8059099e5cd07e80ee90d906663a9db074ed90be88e16a8ced83a7909e8060c12b116b100bb36d205e8010e009515b117af131017a9e133332309e806e995add2b342f508e89716985eb906e8030d2e39a2c906e803e900000361501c00000b01503e00002002301c0e00000261501c09e90d0b00024c75e003e90268c612e919016584c905e80be9952676552c06e80311ee37285600c4d59305e8950134313505e819120018da9a1506e806e90328c900c69aa305e81013bc402008e90daf00b64eb705e83133ad13aa6eb636570ee81c002018426eb94eb709e806fdc02013e900c69aa305e803e91000020518b302f4ca97020b0db0960ea702110118b318b09802170309cd9998020d010418b318ac9802140309cd999802110118b35d38e797020f3023a73006e802e91c201b0c0104050191de5605e803e9095a876b24db44cc0ce80ce90e0234bf0be917a5052f019dc607e8110d0205f2371af907e803e96537e417e91602202022201122990905d228a44eb93ad70ce8021b12110431200c201f2d39e40e201f0c0174e6cc05e8972cc8e6d706e8030d0204064704b29907e803e96514e014e9126600606600e93399086107161104291f06076604281f2d19e01620200c0144e64c05e8175b6b6ba5999192b7425411e8)) | false => (match Nat.blt i 16 with | true => 0x743ea0090d53a5f515e80fe915a11395952d148b82e234cf0be802ee95c5a67a3350110f0fe81309d4ce091f1335f30ce8013a3e3905e8be10d9d1f108e8009338cf9811533b270be815e907100502e9cd02b83a269cbae20ae80ee9018453098ccf94b9f70de8020b07de06c1e8b742e50ce80be90ae2e95b8d07cea50ce80fe90504205aa68806e840b5d700e83e80e800071f40f5d712452e9816a909e8205aa68806e819081aa97d10b4e5d10ce805e884e5cf07e83531014d08e2950be87720230211c810b310ab017c563905e8080211c8b5c037071339f3e7003b0080c261308719f006e80cc30c5c221c17cc4ef142a6be52ec40c8add2f84ea518e813e90504010306592d95f257d6ee0ce80fe9328cc6464b1b0a5f250ee805e90e15b102d9cb3e59e3050c0416b3019b11d605e804e96492e704e9050193be6105e804e90114030bae17a515ae050f0bae14a59905110315b102e3ca03e9320ba69506e800e9056533858d08a16d8d2e75ce8113e803e9010f04020fb15cafd204e9120bae00e7d2e405e804e9120310b141e4d504e9140bad217790c706e804e91403020319064f4ba6530ae800e9169c02e90e1c99cb2206e812e932980d3406e8c6512c1d3408e80f0205018e922675bac50ae816e903a48c80d207e8024b8147884055290194b01205e864e8e0130508616fa0ce973ee50ce80fe9a2217ca5e308e80fe90270cb01d4ca03050204013190657606e800e9095a876b24db44cc0ce80ce90e06320b273407e800e96513e013e912050db116b102f6c10119011ce19e0e60731d0492db5f01bd93494d130fe813e919050414b10234cb095ae9cb9113b6f40ce8030b2c03267106e800e923001b296cc2c3c9110ee813e900d3ad1892229bae790de80114056320c9e34c21b30be800e9004040e20447051711a60f0be53309e807e9279330f3be5319e4a60ee805e90d010402926990597208e8164d2466d65609e8050e036c881df807e8036d944df407e802102bcc7c001c570d4db2881df409e812170421233b0b403b1e24dcba5306e8031196ba5307e804622499e5cd08e80516016320c9df8ca1b30be800e90234c702b484c04999b50ae806e994248a40cd06e89369a134431908e80127d21305e80127d21305e80a9a24638cda42b80ce802a6ca1d2236900ae804e902b8c10717c6410b5d3308e800e913b18d0f5c827708e805709b5d1307e808e95509e10315b65373e4130ae8a9e36be51308e808e95537e222528244603121041444d2eb993709e80a22a965c04898f70ce8100d010204e970aece07e80ee90322c20274c22e9c892e0ae80be42b818f71652e0ce80ee916121844f298cf278a2e994ece11e812e919ac4e99e0062874ce9907e80003c33003001c1b8a6603525908e80b3579e2980119ac3194 | false => (match Nat.blt i 17 with | true => 0xa33406e819e914030db2186c25a506e81529509520f71a15519555a4d132c642d29e7808e81a59e13306e8040152501095e2351a03e94e803c141591959904313201515504303200c9a33805e8067047866707e81401155528501e0279c12484e5940ae813ae032cc607060310024305db142048140218b98f0350b4e16f07e89898ca2a96be5808e800d4be7905e80129259c9984c92b54c0482922c29942492205e926742db1c1267461e10ee80fe91416d4d1eb06e8035f44c2b807e81479db84c25909e80105173606e60db38e3ae9db0501c5cd0c03aefba19207e80cac026bc2974275ba19211e7810e8352ee50139110d7dc2f3b6170de8012ba58d05e8051191e19964114001a9cb7ccef7425708e81b74b5d706e805124b04764d1309e81e19119950a54084c923add008e80f84ab74b6d709e8059e0f36484408e807e90268c604d107325707e809189ba24906e8190605cb08a1b307e803286552d9e2f90ae80fb232459648ca5b08cef90ee8011080484f08dd11ad11ad010ba9030cb436f807e80fb2010172a18d05e80db1016dcb12b3010607140300c642ebc6b708e801e901e9a65154ba170ae8839e17120708e80cba18091154c2f10ce817e9110d0153bd7505e807e9035347d3213a16fc55350fe815e9170600e645cb05e80ce9051184e18e07e861cc44a9821e8e0be802e991d186508e0ae80ee9110b05cefba69807e807e90322e60a1807e802b7cc2b779e28905c2236f80ee8970946605102f8b8140b06030cb201f5c00234c902106094dd04e95cf4dd3ee1d71815065702da4598e716e8921806e8021432a0e6018ca19505e848eb44df089d180be8001406030516b15d134b72e85b020be802e90c10a0bc1c403b1a0302b272d756c30ae803e9170602c9c971211a56c608e806e90c10af0315c40218c9061402050db100e8df0505e805e9160286c228663b0506e805e916030db10317c102b6cb06142929191940632b194ce303b1ae09e856d7e606140502000eae0297c24295e6050f0eac35d6e53e75e005100115b12f82dde106e805e90152b6a105e805e9012b843f217a670c16420ee805e902160416b29698051413b0016dca9505180413b0969805113296bac506e813e91e001c050401030ba82eb95dc206e80ee9736a74dd6e08e8020f0319046a869a180ae800e9391000b2873e780be82020cccc04d81c0215ca02abc202965b6887427808e8092020cccc24f81c0117040faf552fd608e9130faf5ba913e6ed89a8889d3510e8248a884804324602e66b8f1365350ae80e4d4cd3c4d509e80f3935e714b22a9a46f906e801329aadc25c8910d1f50ee80c5daeba138c82b70ce8070117e51505e80e3dd31a550f09e801425ccd89de84bf350de80734cd3a2b94d1f50ce845e8e30fb200019bc48ea1a2 | false => 0x60234389607e8c228383c6d08e802d7cd2f945af806e80141b1b705e8996114e509056040604000232d6040604000232d02834c196c15110ae8a21e34b2d808e802000090611a0a0de8a3d36232380ce80518b10144389843d2c8ded80de80507020653036a5f009d89b3a227448c13e804e9c232fb8f07744884c19610e810e01a51c443d2c846f60be8018451f705e80200570393382c623409c9d94241570eae090400240101843ac4a0d097c2380de830401a0899885821470998782cc23409a5c341bee8a3d362323810e861144b20f4c6d70be828343e1106e80316cb028fcc0903a334506f07e80eab0152f80d0684be110be80c21c4a21e965ed80ce8070206050b0001a3cd92520b63b29b8dae0be802110447780d2d07e801193b203f1a1044ea96363909e8022312b3331009612b12b3bb10096101152b523322791e963279a135bc0754b62210e80e2f56ba5106e84dd2c8869ab5d10be8011111111182f9201183111126f81f1111a211001820111111110238200d013b85a2452b774a320de80212111008610d709e8a3a5109e80212315068610c16040650d84ac207e816e916b31782e24b31b109e80204139436c407e8c852bbc0e99e5b1a588810e81265b70d52d259990be8020e65d7db2a899d2f06e8372ee5269756ed06e8102784267006e830880e9006e82f5705134d5b91e20f0ee810e90f9002a3c30213c90faf080316661008340316661008349393031666100834071102aecc4a38da11e90118671111401a460c13a111e913ab13ab01894f2e05e807ade113b5e308e80de910b118aa98110d104d5964ddb909e8856e9aa269cc0ed73e3510e815a710b110b8669cba3809e80302052561e53506e80b2608ca656aa2390ce87d5118229908e807132561e53506e85c6f2d6c3856d70be89648287e6a3442570be812b3992f5c8df206e816af050f0922d507e81f00bed506e801f0c63e4568e27ca2d50be816af490fde0918b4804840371a02d5cd0118dad8dd00316b18dad8dd00316b0323ae510ba5f62cad54469912e80329ca01f5b260d1dd2f0ae80518dad8dd00316b07a6a8a46088ca990ce85f21692e5ae534cc911821f413e818dad8dd00316b070fb6468ca6b309e815e9036171bed507e8ca6c543e9508e80652f84ad507e80726e1b16287d2140ce80faa0352f95b3507e8071302c1cb0261c316b30261c809a5c232be53a5936a85e810e815e96532e1046140cc677c936a86e80fe815e90818060db000d93ac405e804e91101a3c601d2ca0328a25d71b5d20ae802110501a4c601d1c645c9c22b71b6320be8041630189ec906e801e902e7c38de814592f08e81812050600030ca15ccb96150ae810e92ee7cad00c2a96df050ee80de9622496c2f808e80124b21805e805190134e32c05e80ce9313c))) | false => (match Nat.blt i 21 with | true => (match Nat.blt i 19 with | true => 0x9a380de80b017c0e6d839e63ad8f0de80b30bb0ac45d03b0bb12846117b218b118b1013e88a62e379f080be80b060b9e7843ef832db90ce807dc3842c6f356f90ce82276c56f06e809160214b202adc803011b11d1a120131d17a198014bd93805e817a16dce9a5d1808e8ba307b8e6708e80288cc10053011c0f807e801e93c4022989e6eb8c2813dc703d07810e80f026d75c68741f70ae80175be1605e80b4268f9a2b809e8072cc039015a774e301a2971aed706e82971aed706e8a5c775c1f608e8a5c775c29608e808071101f8c401f8c40310bb101b4f8452e309e81191144353970b087c6035d5f711e84237e69391912718051806e89191070602b4c2337b26180ae81214151460181e00e884f805e815b8e889e0edb85361c4f811e8044cd4c4281b2e7a223806e817488cf806e8b87074d5a308e81414541402182f10011bd9135dc2744ed80de802f6cc08dec85dc27452d80ce8a2c67c22f608e809011b41d4a400331d17b202d7cc011b41d4a400331d17b317c0e18446d709e80976e0220230ca0171d93805e89102d7cc0742e784ef84d1180be808e904444408412b014b861805e891910313c82c99c69806e86130e2970714aa6ca01b9707023c402201181104702017b201a8114cf01a090118114450205f03e2017c269605e802e9cc02e9ccba7133d1a389d164baf810e818a505d144e2eb07e817b20144dd7805e802144dc6745d780ae8027719d184c2360ae8017c0e9805e80184c23605e80152f80c6874ae180be860f0e2175d8383c29709e80211cc9d2383c2d708e80214cc0309d0f1b86875e1160ce813181313a0781f06116ba63807e89c6983c2e308e807e96114e4030f0530742dd607e8013155555501ba1e0218c0341c603902e84ae8fc05760ae81315155501181e02ebca02c9bf0fae12a2a41406b81a08013c33133324d91e01118543106f031315131300181f0e1315155501181e0a0702a2e2fb8ed708e802e9c103f08a257807e826da5af806e85d2bdb0174adb605e8030c33cd66681b1151555501521e081151521240321e1151521200521e07c226fc25f708e80c33cd56e81b980626fad17607e808052e89e10ba592dabec30fe809e9030592db8d6f07e80171aed705e85dd13a3f0708e808e9071551551608123201511108303211011211043020011a110490200301511108503204df84b5f707e82783a17406e8030201511108503210060c050411b00eb001e7c5023136744582ba240be805e903a367162407e805e92d84b22263a382b2c40ee805e90400e3c5d605e818e2419606e8056040604000232d30c0330020e51b14a056141a1e9646f809e8051601743e814e2f62c7070de811e96040604000232d000d000421570c1c2887dc2309e8000d0004415701f7b5000d0004e1573ee1d118 | false => (match Nat.blt i 20 with | true => 0x11130201030eb38e96060b0121141420bb1d1b681dae06e819b0060f040bb11cc6d32606e806e91014b22dd1e210b20417000218b39294021118b33321432006e800e9140618b33193332206e806e92f8461e206e808e9020670f3332007e806e90010040512b302d0cd016ca23205e8000e05f21b257107e801e9177c1d095ddf1b8ded0ee80fe90d0218c85a342e5709e801e91ae921c95e3374caf60ee817e916016c26eb05e80be92ebc22814adb719eef0ee817e90f020610ab5d90e75f01e70310cd110612f659ae07e8061974d9cf07e801001217a305d412d4d4202b2917a31c2075051132c78834182381c2f906e80177c1be532a1d144c6e33b63810e80287cc0114b6ce05e8010f0217a1074d74d14d00a72917a31c203756c02c0f1f24c6f906e842e389e8895d360be80177ca0289c30124b5d605e801180ddddd0061710fb11f0023031142da77a25709e82877a17206e85c36e71c0061050eb6be3207e8091802060518b31b15c31906e83534e5000ebe46995e9608e803e95c2fd90fe90b060021c133cc40f5220daa612edd001760efe407e9018b0d2f05e80fe9170604061901339940cd2a11aa610edd0014606fe003e901891d0f05e80fe914061414134440c52a9001b74ce11a1dd80ae8000f029719d90050ef0ae803e9329245ec9784ef0be80fe9180604050289bf6a6885a65608e805ecb3a57107e8020c051b71b6333adf0c1ac20fe806e90596d89e684adf8332390fe8020e02d9450f163ac20ae80ce92b1a1d0c06e801d43c67445d2f0ae8050f19a2c907e81016dddd001b1d50f7dd2145dd3606e802f4ca970211ca010d06d0dd00297101e9a66d708e877a6344592b12e800f8d203a226780d910de811e91e3851a33b131a22c90ee818022341be1106e803e90c03e8899d9007e803066612883411137e12ca35f709e801942dd405e801442db805e8030206055daee401489d9605e802e9ca1b48ae4e0ae81002ebca020e4e6e389d360ae80184321105e81430401029f41a01c5ae36c28708e803000019241b0b04b4004400252c5d14ca6f8430f74cdb6b8e2713e898980160f0b8da78850b83535b8ef613e801c96e6e389d360ae801845ec905e803000018241b0b5c6bd50f0699990184266b05e80b0c0bbb08251c30381d6906e89927842d3906e81705f074352c07e80103ad2c05e8c21316c0ec08e80e065de893a676e2e30be826eadc6706e80b9903b0bb10046103b0bb1004610900d4e5cc05e800d75d2e05e8610bd711b0131b021420045b942d3807e811b0121b6254200e307845ae06e80173adf905e853077dc2b1bef90be8090c06160194aef605e81115e11144d21e060cb99a79bb2908e817a03373b9f006e803174e6e7c21cf0ae80102e3ca2133bf060ae8308cb9e606e8017c21b099f2e7 | false => 0xd409e801d2c84eb7e70134c2b905e80c041100d73ee505e817e9036e84ba3907e882dc26d464a21b94b1d710e86baf4ca13108e8022b33b00b80a73418a300d22ccfba1d4ba5990de8171c09c906e802e902da323ae907e816be4f4ba63908e807e90bc03318a41b0191c8910ba25421d8d8d2d70ce802ee76469907e80616c64f4be53109e807e92e9a5c4806e805ae95d2e207e814a0110336b60ce95d36e6020214bb5746a6d210d11231a612e806e90e0cc90d8c88d32e360ce80de90ca612890f1619770ce8c90c8b269708e864ef84491619770be80d01a6bf0e0e8509942db809e80be90153c50fc1de875b098b72e191ab15e80da500cb21e96e1f91b56f0de803e90147a56d05e800c7363905e80bccbb3c625703652dd917249cb32206e80ce9095328b5d347c7020ce811e900ccd93105e812a048cce70e0930cd1923943296be52b8de8214e817e9020ca275cc848be5310ce812e95d2ce702b09e1343b3280ae802b74e4d43df290ae809e90143df2905e818a2014119a405e802e92744e50c06e80cb356077a6a864f280be8121105010015b15738822a97e6e10be817e919af010c6492e704e905f259a2a9959d1c9a2c0fe811e90c0315b17f003f0fe90191d62105e803e901018ca668965134be353b4cc7d72315e806e903100211b246f8d305e90b11b20fb20fa101f7cc0307c3112583c70806e807e96111e001843e3205e80e326f83be5109e830743e3706e801e89a6f83b5f10ae83174b63306e8042593223806e806e922fba309bbf17214eb0ee80fe90b113ade87cb0409e80fe9115a3077a30409e80fe9910412b89ef84ddf343f240fe80fe9041415b3ba309752b908e897020335c00ce9016ba7289d4ed799930de806e91001960ae905e80ce90eb304ceb711e707e8017c8b2605e802e9a5c477113908e805308ba5d907e80177d05905e80c11030100019249f905e804e9025934287c232f0ae8c653563e485cb04640cf10e812350f8465ee09e80fe90e0308c315a95a30743eb908e8032fcc01cfc4015c3e5905e83e12e7060c3a12dd0f43a984592f09e819028f355365ba150ae80314ae2485bb04921f94d30512e819e90f719e9b35d809e88d6112dd0334c30c051718b10b3e10d7c2b709e8020599409900392b17b30901843e3305e800e5c23705e810ad0ea510ad0413aa905dd7321cf857190be80714027fe03e0ce9ab88d3be2608e811e98e15716a7635d109e8912a76ba3706e8061005f244c67507e804e900f99e3005e811e910020113b39911b20178cd0e0c670e89b098cea20be813e902610be06707df020e5a3077c70409e818e991610bdc6707df0204146491e704e944ceda0ee90cc90ceae53108e804e900e9119005e801cc35130957190ae8085dae84b24640c80be87658443b2708e80ce9)) | false => (match Nat.blt i 22 with | true => 0xde9160e005c94e304e90136c4cd05e80de91006492be53107e804e99602ccc602ccc6960192ca1913030329cb02edb70de914b38676767600233997080318401f78401f78401f02886c2e669eef0ae817e91b695e88590aea04670ee801e90f11000215b346a5d405e90d15b39500c7a73505e82f9ab10906e803d89ae53507e800c4c73505e82f56650906e803d89be53507e813650ce11f33b2e906e89a5e53b0d708e8155599e30ca33289a58f06e8155f354b9e6746770be81ec8daf906e891b9d2b63e3308e8065639e3056535db15e9133a6684bf3509e81212151204381e0c0d0128a85588043946128a55550438462e969f3506e839ace30314cd05b09cd2f507e8307b5df906e8081306327425f707e806325be5a5432333a12f0fe8033344ee563e270ae807e9158d5f35e11284545404382919af05eb94267507e80f061011b346f5d406e90c0cb311e68e6800171f012b06e2251c5aa5cc0de8116166e644521f0172b8c905e80ea36135a1936715100be8017452a905e80c00d819cc05e8118188884071451d031d8806e819248a09d806e80e4d6e9cb1b009e804015c64ef4b2f56c2990de801c961f2cbd5b00ae804512e2a2193a5990be80ce901b7aa5d0a10b0c9988664f112e819e9114b19d74b19d70c658ee0b26eca448b08e80184af3205e80214b210ae2507d31906e8011f0bd72906e802f5bd0c083ab9d73939dc0c065922323407e8abe112321408e80801588808b0460329c212aa1d8ca64809e8057194c91907e80309cd0257b90e0c07130314b19700bc26e805e8140f0fb1019995b74b6e64426f0de813a90c4c974ae485bef80ce80178334a87cef80ae8176adc85bef909e85e4c873ef808e807ce27910d09cbca96e0ef10e802a8c652b7e0ad0ae8ae3256bce908e8174f08dd0670959a0f9a164335f70fe803b382216f07e836f8ca66472d382aef842df813e8018ca16f05e8189be7194ae5742df90ee80700bc25f705e80fe90fa1140137ca9705e80ce10ba49095d1f80ce800b751f905e8073089ddf406e8031b8bbe1207e8a36171e52b2b5f0b9d9410e80da8019c26ef05e806426f322133ae840be807e904f19450e8bbe067c3240fe80fe9041100d32dd605e80ee92dd2d204e91103376e967680531f04e487d2c907e881dafa199208e809391298ced5b88d3258e7d91214e89207c284921967192c0ce87e76967670031f04e487d2c907e83a42e4309b384806e802d8b66136d61900e60cf3bd8c8a3cf20de814b2e863b1c409e806e90183c9095d8c863a990de801d2c801d2c80336c1013ca2f605e801f6cd06041105b295b6f107e817e919b5c8b339a609e806e9112131ac8d3212c74eb990a88be53116e812e900e69de405e806e90621b24be674ddb20ce855976cf28652f90be8129a579331 | false => (match Nat.blt i 23 with | true => 0x67ad9329a2ec0be80ce914017348ac05e802eccc12ad17a656ccddbe0a63d99308e831f2e504145aacdd17b20165be9505e803024c3d530c4a950ae80123cc923d08b2b2770de8149958e962b709e80c715929d2b709e8099313a1d89c4e9609e805aa75b9f007e82d53ba1706e88f0c081913af0227c50227c50194c4f505e80653543e2707e8131402748d46665f190ae803e913ae01f4c70149bf3705e8016ecc5275dd03119415a22a67c67409e82a88ce9906e807100216b319450ec84f3509e8015331113300351f19b1090162b1b105e801e7e111ee2a356f0b95a654553209e81531eeee03345f199011aa01444a79a1d90a56d70de8060e0c3be67a923509e804e92d0fe2612fe2130b23295b5d22a1cd63e53a648e3b29734cf51ce81110020111b092969696120e06e6e32ade9c31d089ad84c6a214e806e90202b7c41e743ee30ae80fe911a8016c263505e8020312a563f29ba1d51197243ceb10e86112d90635c561dc65a1e70ce811019036268745f20ae800b727173216e846530de80c3a422acc8746550ce80701842e3205e8970308bf0302f84bc6c81a350ae802041469588adcf99db28925f68d327ad93118e807e9016a48ac31d6d912c60de811e914151434f0861e04a963322407e806e994254b199106e81644a87846d909e8040e0f9a7372263509e804e9031aebe53507e8017942dae9bc87634d2a1e9512e8111002222222220035202222222200342005494c263507e804e912b22895bed8298f0ae12e11e802cbcc92043b05640d5c26b00be810e91122222222043120022222043020222222221025200222221024200b1709a9dc671e290ce82e535e5943e53a1d350ee8100b75af94d61109e801843cf6ba5d3ac2350de814e0203211e305222222221423200222221421201420200d5931e31a77ce8706e810c1de87523708e866e56190e8d6f90be85d0bcbce8a46b70be81379de85ba9109e826f3ba9106e809030201000308c30ea70da82db0e70da88d98051602d8cd10a21af956d909e8097b8cf4b5d608e801f4c5b29adb250ae809e91479aa95ba1609e88d0c21f033d2c752d90ce805176094e304e901a5bf0be9170218b35fe06212e9000190591940531a029999990701191f0805e807e9129e00f4cb2879e22960860de806e90b14035f603e0ce92a76ba3606e80640763eb907e800e9918e2a76ba3706e8061064f1e707e90226c00ce90e030182263505e804e90226c10de91016561616604332010a9e1905e8b65385c31408e800110302019916b316b30e0c5ea89ba592158f8d4ed7c64613e811e98d19b96a7635d109e88e1529dac752f909e806105892e104e90268c612e9190316b19716b116b10f0dbe4e98cac308e807e90397949404014231a605e804e9179f0173be863ca24619a50de8 | false => 0xd95728d93328d911a2120122360605e804e90c03335468275727e107e902a84cf285c84e0ae812e90e024eba2276491306e80b18e9217906e8090c0bbb10085a990c0bbb10085a02169717af2f944d3506e8010b976537e3018e8d17c8aa7635d109e802f922d8d73e770ae806100269cb6532d507e9100bb1926c43ae3308e811a704ac76363507e88d11a7244636d906e80605d2c3ae3307e88d31b5e5060195c100ccb6b705e80195c15b35e5060300333320a91b058c8666d707e80da60704f285d93707e814b302ef99a26f07e80329c6079bec76363508e88d01612d8d05e806100491612ec607e80be95844e002e90b257068887646790ce86512e40194465605e82594465606e80b0162361105e89012b09612b00b060e030faf0526744aaf07e802a9c3154e50e500171d155ae5552451542c807501645d2b95ae3890ef0de803e91900c9a25505e816a200c9b8e89118689e6f0de80fac00c9a24405e81901017425936d726439f1cd46663e3415e803e90279c90e3573243049966a8a10d311e81f4aa29306e801323049966a8a10d30de81101f1c70c5c864746b909e86491e06491e206071005b64465be3208e802e9490bdd064465920607e85b286ae543a1ee0be80fe90e1705f274c57207e807e9491421d6d89a2e0be811e90e0305c44cd53207e802e99106613452b907e801b9854cd846b70ae8066a66c23207e8070f14c9a15b5d3109e806e95d09df2e9cd4f422d154c2260ee80aa284345358190b0ce819a9ac9ac0f5ba5711550b11e8028859aa988a060ae80e12030500016c1d7305e8038d33af1607e8850e85ced808e898031135d31607e804cf05bad807e894940b091700ebce9605e802d8e9daf807e846063d10b636d70be83697e6020146aef305e896964277e60218b148eb7990e909879a174c5ec913e816e902465b4f333052a216eb62e912e817e90faa60e8da2849091006e80b091944cfe7890cf4c91908e89904b22819e707e802e92d3131e6f4cf280be8991833822e2706e811e991129e5f822e3309e801843e3305e89118a39819071405450de7844ed321b908e899c91a691db108e804e90450d4b24207e8991600d61a2205e806e9b65a45b64208e80de99900d34ad905e816b31a995b1906e8020e14a101e67e676700131e14a250d345af84d0e80be80193bb1100f9d2e6c2687a21d90de81e6e616662b11f00fa10c705e8110fa2719b3a2209e808e913c510e84ed909e8032963893432d90ae816b329842db906e8021205010177d2ee05e80fe902265b65421a8e0ae814e90e063224c65407e802e950f1dd11e90f0506322ba5d107e802e944cedb0ee90d050ce3e53107e806e9066666c22135013911f0e22e1112050100101eeeee00bd6f03dc5326ec07e8184dd8b795c65cac47ccec11e84a))))) | false => (match Nat.blt i 36 with | true => (match Nat.blt i 30 with | true => (match Nat.blt i 27 with | true => (match Nat.blt i 25 with | true => 0x16e916c06674464409e812e91462d4e403173304283f18b0018ca29605e8122e92d614a216950f08cad908e85259450f08cad80be80401133330a82062d4e403173304283f18b0018ca29605e812060e16c85637956495eb6c98f111e801e904a79456c907e809e9180163a9de1790e98cb13b632812e813e94cf8d611e911b22063c53806e8058d83c53807e871df0244f808e80571931d3107e806e913588f2aec1590e98e253ae32813e812e948f8d611e911b258cb74e078a6780be84678d513c44cb71e2409e8aded8c993108e806e9120253cc3c201e3d201e03393308013c1c201e1d201e0e3010191048631b1cc01d0111ac040ba903cf64bad807e80ba9173a5f0bd53109e803eb74b1f707e879ef94c2b608e80137171917c8431b1e49c0c706e81102b6bddc801e11083190d6c906e801e9013448f805e8013448f805e80109a2479df0124a680ce801e9a8203c88e03c111402009699990e0c35d522e59435f6c05c87cb0913e818e99901023c27921aeadb190de8960f8216e956d909e809176094db04e901e1bf0be9170218b3999999120c0301c901e9024b2fae0023b1f10be800e916b918d74a9909e818af02018dc507d0448e6a77c6660ce807e90610056438e401e90244bf0be90e6438e701e9018c911105e811e9120532685d3106e806e93148922b06e811e90b19591919600332650ce398001405020315b1b22a96e6e508e817e90164e33505e8050c16b30154e33605e899050c0317b200d34ce96d6f91daf80de803e9018c871505e801e9052696bab706e8016ca59505e80503100217b20192350f94492d8daf92d6e312e805e9018c871605e801e9032496c2d706e8015ca59605e803050e2626256640652b9700f3c2b805e805110626360640c32405ae9c1dae07e898051103020000e7c2eb05e80be90a650d7daf94aef50ce817e915c64574d2d808e802e9508ed90ee90b03302b5d3906e802e950f0dd10e90f6052e602e9012c1d1105e811e9140305302ba6d506e802e940cedb0ee90d05f274c65607e807e9244b1a2e06e811e90e03018c8b3505e802e902937d2a43b654321f1a9e3012e811e910060c78553107e806e942a2a6109890f10be811e9120305019716b116b10d0b0544c4d84e236353c6660fe811e98e6451a9d8d746f50be88d02f922d8d73e770ae80610018c8b3505e802e900c6c4cc05e80ce9100513b00110e014ee40551d02d3919933c6410ae806e90196979708013456c905e808e9169f2c913be459d8440be804e90c1903063224d2d707e802e916b9e2e33dcd09e80ee90d05f274c65607e807e90244bf0be90e03c6455b5d3208e802e99384d0c8d2b908e82a64361106e8066a66c23207e8070f0646060660e3330167196f05e813b3011103050015b30c000014281c0b15b33328 | false => (match Nat.blt i 26 with | true => 0xd74eb90ce8028bcb060133d5b705e8019b3a8b05e8184b9744b6d709e80403003246be3406e8c2721a4a7808e802004614ad02b6cb17b00809888cc284464e889d3247c6990be8060233c80134b5cbae5375c6540de82b71c4d906e804070005100191d57905e803e9014ba72b05e802696d6c38cceb0ae8a9e48b272b08e80be91002e9bf032bcb0176cb012b2eb905e80dab052794aed707e82eb7e703105e2b44d3944ceb6c0d58468213e810e9055b91d5133adb1819a20fe810e99616ca56664ad909e8028b4b4cc95af90ae82c96ceab06e817a510020e11ac0332c99918b30814cc4667cea708e80fe9940233c80153467405e8194cea663a3209e80710050db00279ca9918b3091702f933e6763e630ae80fe9970133b6b705e801f5cb1944ea6635d609e803102e9c660f06e810e902a9bd4ce3b6b9c0d3099e0f12e810e90f050400db26eb05e80be90164dd7805e836f81dd78425720be80422873e7707e8450fdf2cebaf1906e80714b64468c93808e802e90632889d3107e81403329e32889d380ae80632889d3107e8140f0502b913aa84b6d80ae802e90632968d0d07e81715b612d19d1809e86c33619d2d08e8170f94c4948440034753a0460193ce1105e80193ced505e80255cd0664ce3c272a56d70be8081810ae0eeeee02306b0233c608c9891022460111262cb01a14012ce59e8e00f31d012ce59e8e20b31d012ce59e8e20731d015ce59e8e20931d8ece9e1e30e31e0608c98871824608c98870424651a04696081915ce13744a3409e8330a9a333ba128d2e30ee807e90b67085cdd28d2d90ce8030f05040013af3275d709e91914af5138d6c5aa6654e808e82a74c19606e8061353a12c07e8135933e30143bab644287aa6680de8278456c906e80c6113da6113da448ea5b089dab80be83a0681ec864eb80be8011117e77700393b96963a0ce10954ece10ce901745a81818f5425cc0de805aa64b20707e8131900c9a71905e811a803194d72671d910ae88b12bb633308e85a19e104193c271906e802f018926707e8140319bd13b399193c23333a1409e8990401f089e74c652c0ae819e90c9902ccc21111a7a704385416a61111aea746585403193ced94c2cc0ae80ce915081213af0c203c1413af235c1d1106e8ca715460f108e80184263505e806535c222707e8131554955544512b01f3cd016ca03c2e67c667ca278ca6b40ee815e915c06444466709e813e9149d08e8ceb908e83e93d614a21552794508e8ceb80be80762b4e301585504304618af018ca29505e81301155528901e62b4e301585504304618af018ca29505e81306100212b01420441412b00316345383a2360ae8ca7164609108e80184263605e8018444994d9183a6360de812330093334449240172cd0154e04417191307ca258ca6d40ee8 | false => 0x978e2607e82f84268d06e814e90d0b0601543ed807e800e901e3c10de91704060134be5807e800e90227c30fe914018c821805e800e9013a9e0f05e810e90f0405c64134b65908e800e90226c10de90e018026b605e800e9015b8e0d05e810e90d04018022b205e800e94e87de10e9113575b51560031e54f2e495021004050116b215cd88b45f0109e817e904ee44cac107e804e9012f64497406e812b001040e17064f2452b709e800e94648e20154c828965c96c0740de84648e214e9170b02b901da6a22750ae800e900dad87005e810e917040202c9c8173c668106e814e99601125f201cd3135d350be800e901194cf005e810e914020755b5515500071d0795bc510500271d0ba593ae40cc990c4add2a5ae114e806e975b5135500251e02e9c8ca593a213408e80652c9a13407e812a83284b1ae8996e952d710e80101b1c7064143b27507e80c45b266ba5509e802e7c901d4c60310059e549deb6426750ce808e90227600d51ccf00ae813e91002040518b30eae17b304bd248ba56e08e812e91b131d6d06e805e8b3217107e896020e0db052a29a2496e6c90be809e9170411ac02b7159098e6480ae808e9140955c5505560871d040597b9e48b269708e801d5cb032ecb052794bad707e801d6cb3ab7e7012b3ab905e803b9e48b269708e80014a119a3646d35cf2459340be8a5e26a22e908e80173a68805e80003350055001927000335005500192752f132688ba5b10be80161362605e8000003005324391aa9e48b259908e89a6f4444f408e8000e00d4d2e005e800e9017926f405e80153d2f905e802e7c800976533e797000161362605e8144de8889e9709e8ac4ec44d361a2593d2f910e8b9e48b269708e8000256b60e0b11b365174bb3233a710be80279064695ba370ae84c524dc687ce390be813abca5d233a3808e80c0dcd9193242dd10ce807179d04b2991dd107e80b5d2b8df02746590ce80b8d39338ef32e320ce804cf2ca67107e89999012ca63605e8085cd345c0e32638c88723e53213e812e93068a13206e81c89a64806e817a3190168c26ed7086e32cef8c91912e80114050db35456450e97d5b90be815a714ca736355ae09e802b9064e85b5d40ae8c2639b19ae08e802d8c9d164adb40ae80314a12c3ca2ad06e805b28b0dae07e809d10dc88ce1b6d90ce80a232670de63adb60ce89999016ca1b205e8092b8c9f154d011719096e322b0d1616e816e93064353606e81c9aa2c906e814a2190169c2291708eb70ccf6d93912e801170ce59e50e580071d0ce59e50e540071d0c918843844600e992060f19a13207e8c595111160051e14c595185580e51e02c5951855c0051e0c9888a2c4460001f74613711a320ae8c595950540c329c5959e0544c34414c5950455e0e52f01e91905042d2de50a2c89b9e2)) | false => (match Nat.blt i 28 with | true => 0xc905005030b0e41c0404263a9a7107e813e9057c95ca611fcaa01f10110d02013190417106e800e916b16a241a1d6d08e801abcb0be9110e18c8327952b709e800e95c2fd90fe90b06c64113b27708e800e95c6fdb0fe90d6015e400e9018b0d2f05e80fe9170604c640d1b29508e800e90287c30fe911018c870c05e801e902a0c00ce910046015e000e94f07dd0fe91418781818408329610ce49802130406050eab01908bab6239820ae804e90a22164b5f19b8870ce80ee905c703b5d107e824d6586d81d8e8ceb60ee80402960736cc1dd823b68e0ce88ecb6177092e08e831b6e631b3e402cdc601030306001824010333060218390e1ee150ee06e80ee911040b0227ca288ca5d606e828d740171c0ec93a360ee8020b63208d5171ceb80be800e99801742e7805e801943a9805e8092ef3dc6906e86038d701e9151604060162c0329a1d8e06e828d75d301dc2b932ce0ee802110c64344c4f04ceb80ce801e93297c6b806e8950194c6b705e80003088612f89d150ae842a0d103e9130c0406880880884047295109e6064804804820c7290564a04504a0c7297c80220144613805e809e900b426918606b892a70de804e90f057097e707a63285b1d60fe80154bf001a681aa1f83e10b63a3615e80a5700a610b63a360ce8022b83a1e406e80fe904130605014b65cb05e80be9095a876cad1719cc0ce80ee90c014cca2c05e811e90a4b20450f191a2c0ce811e90c05017cd9ac05e80de90bdb204dc6db19ac0ce80de90c011c51950540531d0adb2389d33618ec0ce80ce91005040234bf0be9028bbc06e89a2d0ae811e90d5234de11e950f1de11e9100505c5095520a52901b3cb184ddb489a9909e805101b74267506e808e9171b22699eb009e813e9100104029696960c0e18ca163adb1909e80326c21ac7640b7d6c363ea912e815e9999870d68a62d908e80917051336d6eb07e80be92adb8ef006e817e91002c64154593208e800e900b1333328341b00d664193b46c852d70de88d309b4ab906e817a11003194da875c2540ae8060e95cca7544ea408e808e900335005050033211d744ea406e808e90400e3b6a9999e76d6e30de803e9100201012a999205e806e91420371002f5b2133919920ae806e9017b22c905e85cf3ae00e326550be8268b26b206e804d164d64807e80c1d424eb706e813af0754c037151757e524093b12e96c4c79d58008e80ce9102679218906e80ce904cf24324907e80ce90b1eee1088752679218906e80ce909198b7505035562e5323ea6d502ebb50176d47505e803e91c2023512be300f352a705e8100328c50170061505e8ca6999217008e805b6b0342a8846870ce810e92eb0a21906e807130c1de9ccaa8b26750ce808e903ea399e7007e813e910040205060134ba9907e800e93b17e2046e | false => (match Nat.blt i 29 with | true => 0xb5d2ca65742f0f0de87696796600e5510bb20ca2774ba57c21eb0ce814c9d334613008e802f84ca742a1e70ae872928272442337066c3b15d007e80259ca9797060d94030bc8030bc894030bc80f64f8d70171aec505e82f83d32806e808e90d04c1de84d16da19a78532410e80de930ef448b631d8e699a77cb0413e80de907997940825114e94d2fe601a9cc1f2057176533a22076cb360be818a93e78e706041102019812b30bb20bb20258cd033084bf0406e807e911ac01942e3205e811ac98980f0414ca5b6bade508e80be95d38450f132da50be806e9183be266372509e806e99701b6cb6135e556f8d7183bea9b5c7409e8190590c89a49c22875d8a60fe811e9c668791a2508e811e9055251d211e952453b232346440be811e9977a6cb6caf908e82af43e875c726637050ee806e90312b6daf807e80128b066626cb6bef80de80501f145d2f3e5123c68ba5b2412e814e919a50183a22b05e8012c217105e80be914c0daf3370508e806e917b026f4bee35b726637050ee806e95aebdb16b101b6cb92999214050163465405e80145ca8405e80be9c94ef3221608e800141cc3330439223193258d06e84a96e60176cd4a96e70501e8cd063264258d07e84a96e60176cd4a96e70517926c8c26e35b1b2331a510e80de9969718ca6465b6d709e8a1a49b2ef908e80518cdc76331a509e80de99716b19258d7daf908e80492d9daf907e8050499329a1d1206e80338c318e90f973611636604293403113304283494312a1e5406e81105328a1d36330e88c8cbb15f195f0416e805e90164496fa1d145c22c0de8012a15b605e800fcd1125be913c5860de811e902d8cd92929214060163465405e8063256d8cc07e80141c3c304382219b016b30c018ca6d805e80db0010c26d905e80503194e58f29b370ae819e917040e092c202224b11a0c20230d11af095c95c900171a036a978e2607e813a10652bc0e2607e85e0ef9a1e708e815a00650bc1da607e81010c922879e6809e804e918b318b3054666df06e93295b6b806e800f99a1105e801f0c901f0c93676e6031754d0ba23322e380be804e9018b9709adc8b81a2f9a171235f715e804e901f1c716fc4a75ba171246530ee804e90714020cb3296c646506e803e90d0cb34cf1e70b64f14e4f08ccd10ce80174ceb905e811a00c4d35da05d356190907e82686493506e81911a60174cf279a6b91c1950de89111aa11a605932ae4b707e806012b259905e80ce90ca00d05cf2c6d2455b1a40ce80ce905d359e5a33b62644eb9658a6646c417e80ce90369229d909d7265c6440fe806e90cdae9ae58d2b2e40ce80ce9040e13af13a107e91013af13af02a7c713af0267c9102753426706e810e95670e102b0c704010ba27505e808e92079d4d106e815e91102a3c703e94eb0e30270 | false => 0xf709e80b4ddc689ef94cf023cf2411e81200b75ae495cf9c1e530de804e91458f1e407e902b6cb15b0090db0048d64d0ed07e83cedd40154b65605e80573633ced07e812a0110333334001236c8867c0f208e81104ac9909a507e8584dd302e9588de012b11a57c0f209e812a01103622b123207e802e9963535e49991919901b1ca0236cb020e01009797970b0f18c916c7ce9709e80162dd2c591f5332270de811e905d953323407e801f1c70caf16af1707106455e402e945a6db0de91001053223c6cf07e802e959a5db0de917063224da3607e802e958cedb0ee90d01000818b3991e206211b13f09e5003f0c4d8cc2a3290be816a0031363232907e8011b80cf85c76365090de816a019a30194b08605e80e120fb20c20230d02990278cd6537e413a1018ccc0705e81f5b5f2906e80c3055a6c571a32c1f080ee811e902ee8196f3ba280ae811e90800cca72c35cab33cf84457274ae415e80ee901c7c4a68746440ae812e918b319b29264f194be5908e83b12d507e9170278cd3138e101d1cb35d1e500083088c96406e80be9025942df13ae240ae811e90198ca5cbc4af90ae80329ca4226e464a9e405e90c9903d329db1907e800c99428f07b0801842e3205e8464ed20ee93077a2f806e800141e9e990439440eac9816b216b1093ac6e55cae340ec326d80be813b216b22dd7e6081997246646f806e8253be13806e809e90e999818ca56794f1909e801f13ad31c4af90ae80898192b4cf85af809e819a309e90c18b3995a58f9df1908e802d309df1907e8080417b217b2017c191705e817b236e6e6112782470806e804e900d3423705e830442e3706e86111e13174adb106e85d6f933a3808e83174b63206e8075f25e505e9036f82216707e80be90f023e78e700d7c6f805e8026e52cac1f308e8036e97c67707e80058eed015b15c65970909e8c8e676540680de75b84e10e80ee917080397939760d83c02e90ce242b8cab7c4d17a1cb9be1214e8019c3ae55dd0e5cb070de80be9075919d004239299a97d86b2cd0f0fe82c35951906e80279bd2a3b156806e81817019c42e37df0883e670de80fe90317cc18b118b11907041411b346d9d608e91211b30cb30da10196cd016c9d1605e81158acd405e9173a6c85c29909e85914e7020cb19a7646790ae80592ccd91907e86ced93c67908e82d94c23306e8045f23de03e936c9cb2d92190c0be80ce9122322198506e80ce902366c89232d850ae80ce9962322198506e80ce9050e0192d6e305e805e90192db2305e805e903cdb174b6ef3a28b6c32410e80be93143ac8606e80de90319bdb0ec532e8708e85600220d5ae54373274b040be80ee938d2d20de90174c91805e81f0c0ec506e80192bac605e805e90d0248cc00300058021b0b50ebe0986513b26f843d6d0be80174))) | false => (match Nat.blt i 33 with | true => (match Nat.blt i 31 with | true => 0x240e13af13af0154ca7605e813af01344aa905e80c1156326320b71e12b0044ce0240133b20e05e810e90550c84c4e07e813e90e01919c2699d6c20ae813e902309d6c99d6c20ae813e99602309d6c99db020ae813e90219010fb21420200e0fb201f7cc01843e3205e817b2b5f077c70808e80b0cb302b320af1b97025420201774bf0e06e80fe9c2577790ae08e80fe90e184dde87cb0409e80fe92dd77c6487cb040be80fe992184dde87cb2409e80fe904140181273505e802e900d744ce05e80ee9c22e9cd73008e815e9650c9d4ed799930be806e9102f93a63206e807e948d1dc11e90e03010017b30333b413e93214de4006e801e90015b312b10001146059e602e90648f9c0f007e810e914b5c8599e5508e804e9050ee298f34c256c55350fe815e919016059e602e900f8c88e05e80ee91464b6e705e9064cd8b88e07e80ee9120116b2052a784a7807e80215c601062720927807e804e918ad0149a58205e85af8e15d2764b04408e812199616b1be046895c908e812064ae361378c9e7be3210fe80fe90c65362b8c794e210ce811e901d62c9393cc8f89d2f95f1912e801071a15ca5f0be0270ce812e9309ce0f706e8857274c6d208e80103ac6857279912f91e210fe801e914009302f8cd02f8cd131001812c8c325f08cf190de80cd7024c99032e33c13265b22714e811e99393033832d8f84a790ae80714b5c8599e5508e804e9035c531d934c256c55350fe815e91901c64584de5708e802e9c95c64acf84de329bcef10e80fe914c96e7ca63608e805e90329ca00c6c6b605e846b7e6024a2020169e0e120100026fc00fe944d0da10e90c612ce509e902d8aa595b96eb0ae817e90b0333bb0fe9011a4de705e80fe9520fda0fe92855a6c233e3481a0c0ee810e90c011a4de705e80fe90329c009e918ca5972e6eb09e817e90b070181573805e802e99184f194b0495ca7822e3510e804e90b4e0cc7c27509e86709844cb7c6130be8194accc7c27909e8070338c612e911405050e0d41a07e9148ce87638d008e807e911b016a38d2c4758b684cec8485210e8038c78c13207e80b1a6764047826920ce819150101411ecf05e802e959a5db0de9176451e402e958cedb0ee90d0116b255f3e22a95c27406e814b20750f1e0010313c612e997be2743ac8764a78131f610e802e902932b0cb7d6f80ae85267b5cacadaf80be8143b0aba56f809e8092b613a0106e80ee94f14cf14e910af9616a60202c7aa713a11900ae885489c4e8408e812010313c612e918ad0149a58205e85938e17e71787e520c3b5938e10ee18e3a843b1219be3295b8b708e809e916b111a18db22744d1be12b95c9210e8016771931b5cf20ae8089b095dc89b9f320ce8140f063224da3607e802e958cedb0ee90d0329c60fb19111a50417b271911d | false => (match Nat.blt i 32 with | true => 0x7140310af14203c1210af6511e35aa7df4939e364f1349098daa70be810026f8d0f945851910b0342ae12e815e96530e50171ca10ab02ca2554c2ae08e810e90236ba0e4b35de0225220428354b30e300c79e1505e8114b35e401981d194c6063c2b60de81995f024553609e82e24e40e01d6cb4b35de0224220428354b30e330f0e311050d11b01c20220e11b05727a6087426960be852b8ca26f850f60be80325bd1a9ae4f606e811032c58d8d107e805e95ce02203373342c13407e9169e0e01d13d910a5b240ae816e90a9a87c222e32cae88a9645b0414e816e9910c26b0696c6a1e2e35b2885b0414e816e90412030117b217b213af13af13af020195bd01518526f0460552c3a32907e80195bd0181552cb04619a30184b0ef05e8131002f8cd0fb20fb20278cd056533bd4c84c6d70be89515a902a85e133ba2360ae8cdd33abed708e80313a9268626b94b0c88cdf50ee80248ba5648be780ae811ad11ad6708dd032687d6f907e88e010a0989990039448eca59844ab708e80656e8e60269cc18a30169cc177c110906e8921954ceb808e86133d617c12e55be4809e8190717b2013c266805e813a2013c266805e89817a50ba35d68e60f0305cb010e99595500194413a20bba2c31d2f9cab80ce86132e198080195bd0195bd1f199e6806e8adcac3259508e80154ca7805e808199503194ccc87c6550ae80313a931945d2f98b2643131ad86663e3916e801533e3305e8018ca23205e82a971649b65194ce360ee82e64beb606e8018c91f105e80311ad5d0ce7016bd51905e8017ae50905e8164df247a16909e805ca6926b907e85cc8d705d9933d0907e89966e5d44ef9d63ef9d63ef9d6180309c002f8bc0169cc177c110906e8015c266805e86133d6056e64b30807e8190703f192ad8907e80be90195cd997285b27908e80195cd02df72ad9707e899990255cd0134331905e809063354d86407e82b94cd0f06e85cacd419a0169e12a205d3619a6807e864c8d72d94486606e8329b0e6806e8199f0194be6605e8179f9946c3d90328bd0134e32905e83299a19906e8244b958606e8032979a68c65090ae8169e0e01a5550e70659905d78456f907e8993e38e799999918b3019c219705e80931944ab906e803172d7284c6b90ae80612e63e7707e8184d86c4bb242d50c6c5f311e8019456f905e80602b8cd19a3105c5c100738210154613905e818a315b3b5728ae32908e8105c5c100738211707109946006966042933040099042833902af819f006e811081050805080981a612b83e2432df70be82e0fdf0802b816572232780ae802c95be1195f190ae85726626ab7c6110be80801843e3305e89700797704293c09009904283c9905af8c896407e8120570964b3807e818ca71922e5309e815b102b6cb0c08071413af0c20 | false => 0x87c22c95c2950ce80308952265b6960ae803051715b32edc644606e802e90c13b3995913e72e63b67906e801644f2805e80329c7628744f28ba6790be84f28d70c5ca743333332670be806e903171d8ad021930ae805b20b099307e8b0dc864ef908e811199e7c216d75f25a5af911e816b8ec56826c09e8096322e702e936d74b4134e4650be805e915017194f905e803e915b115b1032e7a8e6706e803e9f0e035f0e0350c1001040289cb6322d602e91215b100c7a6b705e801f5bb014ca6d705e815a1100327c3a1eb633ceb4b2d0342c910e850f9d61756f0e5016c3590c85e990ae8042e782ef107e8025537dc17e93d39b81f53c0ce0be810e90e7c135ba60e08e810e9973e95e43eb4e519a6025aefe319a62ed4e50001f5bb0c11913dcd4ca2e90ce80335cb019bbe9505e8000205312031a4f9230205332233041923100317ca139b32a20ae804e9104e10faa7175c3373323411e802020531225184f92115a110020535225504392101f5bb100e0d0faf0c203f12014219c794c3223e350de806e9026fbb9a5f10198f08e848ccdd04ced331e707e815061a28912674552f0ce815e94c6075232050953ca61890ef0ee80fe9b610964ea008e815e919cccc7635e008e80fe91343ea663e2009e80fe999335ba58f8d4cc7c7000ee80fe900100518c8295ba67609e800e90164b28e05e894923a57e70405d184dd146bad733e670fe83a89ca193b10f10be816e9110b0011041111000b1d0031045131804b1d01033e6705e8930061046161000b1d13a105518adaf94ba42912670fe817b317b30804d3745089c9dae84a660fe8110236cd990232cd990236cd000c0513b3013be48705e804e91112ad9311ad11ad931226294d1106e811e9939309013b10b205e804e9139c19032975a42346c00ae811e9033344642346400ae811e999032975a42346c00ae811e9000c01030fb15d2fd406e90d14af6514dd308854c706e8319441f806e819c41f531d2f09e80d298aa307a112d2b5f50ee80fe90020400c0000391c2d83c1ed06e82d83c1ed06e80cbf0543614ce2b60ce8a3e063bdb508e898984e8fdb0954efde0fe9015c212f05e8ae1097c0c708e80d1716b105ae9c228f07e8016ba5ed05e80fe916b10ba642a11cfb19d70ce8048ec844c87d6c975aed0fe817e90d00d7a6d705e80c26a7ba286c3e320ce812ae051e9b5db207e85ecfde041afb26d706e804ac2891a607e80e97030fc802440a0a04385318a90fca7084d1f709e850f4dd0fe915050b0bb20c20230e0bb20238bc0926d744b16214f20ce8011926d805e80490f3c70807e80b30a6b1de899e374e2c95962613e80be94c8023497125cabb270e0be818e96d8a68c96408e80be90e0489842f0707e80be904b099216707e80be900499908b04704b099216707e80be9)) | false => (match Nat.blt i 34 with | true => 0x571ae9c0eed1bccd0ee80194acccb232961ae58546f3261715e80434acde4b095df03235f70be817b20177c06d05e819af010601b0ba11042c6425f107e8054ad7dc3107e80922c9b2281c0922c9f2281c0b2db1784c85ba330be803095c82b446440ae80be92d11e00171b8a644b099216f885688ca6415e80be9450f9056dba3040be817e932995677c216f0c1f10ee802d94e1b745f240ae817e90171c315b3982d82a577462e32ba068965342daf16e89301251322f806e8054ac32e32ba1d2c05370fe83173256e0956d89b080ee8980b192d7650e945120ce8035358451907e80197071ad532189c5d2d0ce8030fae606425b808e82c85df0106e8017c052b2c226c26680de8190c5d2bbe023326680ee8189d0f0401f15b426442320ae83c004401b3cc04013c21e105e801e9140016b31420661716b30192cd0249cd12b300c9632905e8160daf9903744066016ca19905e80ce9249b64ac06e80ce9172f62998406e80ce95f09cb2c5332c40be80ce9922f62998406e80ce9040e0bb10c206c180bb20152ba2605e808a1d2cd4cc2a6d80ce80164513805e8032862655b14d60ae80b2488d12b0ad382e52b0ee809e90bb20bb2092f04d904e902b6b9172c5722e9ce16c32dc30ee80be90956d72a6cb347030ce80be901f5cb058b145d2ea616c32e230fe80be9030d020712ae1719504606e802e90e0ba802e9bf0194517610ee9b0d770de83284d17706e80194dd7211e8891d740de80e6136dcb5c434d9c608e812a08ee350e809e80b10a859c23c91459dd40be816763a1606e806535005743b2035bad70fe80184c32b909943baf90de82d2a1e039228b3ba970ee806194ba971196e09e80be9066e991d0b07e8032bb25923dd620ae80e1123619a5606e803e90327452e9642320ae80b8da425b21209e810ab90ec9bac7708e816b30296cb020228ca5f758e970ae80600003232003827000032320038270ca16c85ae664a960ce80000323200382796000032320038270202979593210ec9850e85c4ce12e811e9000336626604393900336232043839110e0d12ae15ca653a1e9109e814e91114b30329c6332acd0906e86532e1aa5d29a19308e814aa5d34552cc80d2a1e9110e812e99402c8638554653508e465ba9312e8634669be7408e8b25c2737200bc723329510e80cc87532d0e9d2b90ce8592b736a3919d40be8075112df12e914a11108802168a02168a021033213a4334e270ae811e90b721f89004c6bc6644e2711e811e914100502d9bc14201f0c3277d30206e807e90dab5306e40184d2b605e830ea4ad906e87a238a198d08e802000cccc010695c8f950bc192d742b609e8050ed85b1907e8030ca1f1adb29ae3230ce809e90faf95a1f096c2b908e80143c31905e80305000ccc10685c184512c83db909e80946 | false => (match Nat.blt i 35 with | true => 0x1aec017aa7087321109e83590e501b0c52e5731f106e812b0975936e610ab0231aede398dde35d0e515ba5af84ef509e8060b19c5b1b089a5cc0ce80284c713ae49c4e2110311a1aaaa0431540111aa04305418a3236b9a57c046c24b090ee81511a1aaaa0431540111aa0430542e5899cc06e801b0cb10b00315018eee08507a854a66b06da85774d30210e809e9018eee08b07a13ae0211a1aaaa0431540111aa043054039372c4cc07e83e3785ae3b26ec0be815081917b202d7b703e90d0db21c5899f806e81c5899f806e80288bd00e2d4cf05e80d2d81b70906e803e916b216b2030000c072212206e9189f17081ab622688c5d2f19ae5c21966c6846c6611ce80de9304b968106e805e99809c938b9688b27174b6246cb2114e80de9010b95388d29935426330be815a01015b352b9e60caf4659e614ad17b3085728e708e914ad8e0b97284b1aea8db10ce8552cdfb26b7438856c4654b73510e84689ae5154b2710be831d4e116aa2898cf3509e82c5ca23506e8c6516c8da4708ac8d2b910e8bd728a4f3508e80605f28aa72d29a99455310fe8016b95a6aa634ca1340de81314ad0441448445205c2910361519191326900be854ce2b0c8c65090be802d7c653564068c648b6191412e8031d03653407e80da002b921519a22a60ae8110be4ce24846436a9844d51c69014e86c2a46b8ccac06c8a21410e81314ad0ca12c70509a5eb80ce81b7a84d706e8970e6d235c950d4dea1336b711e891052774553907e80c17af1965b212225809e897172b6a96d6f909e8060254d519332c4722582b233a5eb617e8034ab7c50232ba448d3284d27013e813e914ad17af970289cd08c89846531a31a60ce894a6111ad02408e80332adccc4d6e1215154b23412e89448414845100c291d2a0444a1a28aa6340ee813018ca19405e802b6c9994455310ae89494130314ad8e138910c88dae09e800c7527105e8a11a55e1148ce97c8db510e80e666342527109e86c48c7469308e80229c6674452750ae80229c6674452750ae817aa249c508809e8309ae66806e8110229c6674452750ae8060841855848023c4645415548122c461314ad45414845304c291014ad0c922975cad36535a212c846669a191852631ce813e914ad0313aa01944dd19736350ae8249655b906e804d36ca59107e803101784b1d9191185c6700ee8610be63089c23306e81413aa010f98035373613107e8189d0f17b202f1124f0807e804e95f25e505e93569c16e1245a6b9709694d113e897612de502f04585b007e8018ba5b105e8017aa57805e81a95ddb806e8016ca57805e8030ae4ab4df064b4a60ce80212ba110da80be50b89258ba5b00ce899992424003b1c0605da35e02307e803e90f177c0d65be12dc0caf0ee801a6b95664add00ae863a1733a1208e82e | false => 0x2c8cd19a60ce99902c8cd126492e704e9016214d205e804e90e11af0194c6a805e808e91313af13af05f0743e7507e813af0183be7505e8115f07a4e333a6ad0be811e9959502b6cb54cbe495052f92263306e804e915a00d02f0744693a8ced94ea60fe813e9744676cee608e813e991053084be33bd4676cee60fe813e9061002010190ce9905e801e902a3c30fe9106077df03e90301c30fe9140018b30652cace0007e810e90652dc51e007e80fe90015b31f4a85e34508c332750ee86533de13e914ad03ea34b0d307e81017b2c3ee12e10f08e85f23e503e9184ac85c22ef09e83d0bd2140018b3015be32305e803e910992667484406e89d4d0981f308e806e913b319ad54cfe1109302c93435f807e80093139a01e3c701e3c40194613005e816593c43ca644321f00ee810a20194613005e807165712cb03490f0ce865322230f004690be89013187c3330be6809e801e912ad12ad01018680ee9780730ae803e92707a26406e80fe914992b999a1306e8930194b70f05e80004c9091a6007e806e918face1306e803cc8591f807e8004cd0d20426033e0407e800e900c6c0d305e806e931afe19090030319c70319c70300c6be1305e83e13e30da90015b10319c7030604d0f9066807e801e90186c261379a040ae80fe961a130dc697c0cf4426410e80fe9141102e9c75f01d201e90b15b32794313106e8066686666907e8014ca13305e82994326906e815045942451409aa364eaf0fe813e917af0bb5d19e49142693094d19d2f514e81a99d6f906e8158b2666367709e865b1e316b301a5729c4c3808e8036533dd13e919a3221230d1265099d46f11e815e90f15ad9404a912232907e814ca2c96449409e81313aa63333ef509e8059399d22c2bc372ccd50fe80d039f5ba59907e87d531234cc08e802b124729635e60ae806e913954e34e14161515104382e14ad066742223307e80c0310044924c29224931c0c20210d0fab8a3066a71108e8154e1780b46509e8042468a31107e80d2ad38299b109e80f34cb4bc6b215f10be80fe94c8058016fc06036bcd10ae811e960656a578784af0be80fe91702cb123e2807e80fe9184be647c64809e80fe904899908b048ba5f123e2808e80fe908140017146d81953509e802e90106964258c8f846e60de806e90c02edb70de902c5731f0adcd1a5c2ca5f0312e806e902afb70fe916c19c588a4e15ae671138342ad8198319e810e92e583ea306e80fe90217c902d7431b54c2f50ae89e1b74b2f508e817ae0c84c5f309e8011ae2555500351e011ae255ee00351e11b103e36bd4d107e81046d82ae684b5f0bd52c8570313e809e901313e87ee00393b97025a5ae846f508e806017c26f505e85f15d701b0ba06116aa6f507e8017c26f505e80c8e6116add2d7cef50be8919031aede)))) | false => (match Nat.blt i 42 with | true => (match Nat.blt i 39 with | true => (match Nat.blt i 37 with | true => 0x719965b1aa95c61811e8018ba6a5b1b09658700de86717299cb2a6f80be895552be60393338e501b0db10db10393334ed01a99990946152b92c6daf80be899030734cca96c68a5d80ce8c0d89a964e08e8017c64527098d915380de80b16a715aa0393334e101b15aa060fca6329d2f808e897975ccee05cd0e1057255bee907e80329c70329c618000004bb041c56c3695d04b6b60be80da0110226ca61794e980ae8015b27055ba129d2f90de83384ba4bb9653bd3080ee80be905ae96dec807e817e90819c5cb64c6b709e806709952b707e849d4e66254e55ae5a992f847190be80812c232ca94d109e802a8c5015c964805e809009707144a3e1405738454af07e8015c970805e8909900d0144a3e02a8c3140b0718b3043268591807e815a10f18b3ce12b6970908e805e96322e702e99915b008935533e2056c968e7407e84268e6011c99b505e82686c27506e82b6ca56d06e8070cd909c8a0769a680ce816a3180176b901a63cd352b6a90ae818042676d46707e807e90fca2b84ce8808e8959503356c2a9818ecb2333460f312e846c864d39c26740be8030328c5b26634571908e800c826b62d468852330de8070274bb0f0c00e0f6281b03e99605bb36c0da97db050ce80de902c9c104d0c825b9b0da97db050fe80de92704c32506e810e966b0e602d8cd02d8cd032704c32506e810e90269c43299a22681e1343f090ee80329c40195ba0d0329c70328c1a19426180ae8042b9c22a907e80327cc0f0164adb605e80329c70328c1a19426180ae8042b9c22a907e80327cc0f0556077a1934d2b80be81c805c0274cd030552fc0d2f07e803e9170416b3019b5c6705e803e91015b30cb30da10196cd016c9d1605e81158acd405e9173a6c85ce9909e85b29e15b29642c899e390be80592ccd91907e89d6d93c67908e85b29e104017c8e7505e803e942a9cb2d92190c0be80ce9121b62998406e80ce94d35cb2c5332c40be80ce9921b62998406e80ce9040e11af0194c6a805e808e91313af13af13a113af0134d4f305e8112a69c4ed06e811e99715b15ae5e3005300f4811c02cec911b0032f92263306e804e915a00d45a59d4679d6c60be813e9744676cea608e813e991022d2cea33cee60ae813e906106475e703e90226c00ce90e19a60ce99902c6c50323c903e99901689da605e80c19a60ce90192d8cc05e80ce90e16b3019b5c6705e803e91015b30cb30da10196cd016c9d1605e81158acd405e9173a6c85ce9909e85b29e16511e20592ccd91907e89d6d93c67908e85b29e104017c8e7505e803e942a9cb2d92190c0be80ce9121b62998406e80ce901b28d8b632d840ae80ce9921b62998406e80ce9040e19a60ce99902d9bc0323c903e99902d9bc19a60ce99902c8cd1219a60ce9990196ba19a60ce9999999990c99 | false => (match Nat.blt i 38 with | true => 0x26c73098d8ce06e864cee164aee61200cb0a468ba13a5f190de82ce13aa806e80ee90652f952f807e800330307aa541b449759492b742b0eac012ae53905e89599556666560572320300eb5cc905e81832d6c606e81054a9c5d65819d20be80da88d0da809777b5ac41a99990230abe005c457425507e89909779c9ac43e062d781ad74af055c2560ee804ad7a892cb6465ad8d00fe82c96e3297d44c2cb170ee80b6538ba5b5160b20ce891aa96171708e80b02b6cb02b6cb09779c3a843e0daf03110c96a9636e66c1350ce8159d0f0861f4d50fe9981d6196a984654ba2130ee8980b26e896113332264b6b09d70314e803e90f7d0687c67408e80fe910ad149d0f32974a3406e806530952d707e82e9756d106e8082ef4195f1322130be806e9b16a8999b04c69742df410e83334513106e80162a2666c233aa5740de8b15137d46908e82d31b0d0fa25740be817019078ea5b22668a6974257412e817a33912df0fba6379a17209e83cab345c6596e90be8012440ce44df71a5710de80dcdcd368871149402e9c8940274bc18c94d1a22f408e814e916ca688ba5f409e89418be0496be3908e802e96511e02e6ca23206e80137e603b95868c8ab0de80fe90bb15a9c0cac89af842df810e88e00b6c9d705e82e2ee40eb0456ee412a512a519c0871957264396c7daf911e89223542d9906e815b217b39710af039305909c5d6d07e824b8bad806e801b5ca5d8bad990ae893970211c903019ad9381a2f84dd6c0de800d34f1905e89602b610d8ea9b190ae8083266c64e356e35b1f50ee80598275b651606e808e90734af1b44b1cf2863a11321f514e808e9118584379659431d13217611e808e9c906090c130c1c02d915b266c6c50ae80906090c130c1c09969c1b242d0b034a9c9a2e07e8312da8de5c9a2e0be8652d754cc6baa50be80670968da907e80206ca5b1a8de50ae84a2e44c666d92d78dc6432a513e80b034a9c9a3007e8312db1563c9a300be8652d858cc6c2c30be806709695a907e802c8ae52db15630ae80230b2325336a95b4b0332c312e80f09929c3ba41c02a5c302c5bf171400c7461205e816b30daf0daf96b158dae53808e8990cb3990309c101d9c601d8cd3b12e70309c202061379567807e80129df1905e80232c70232c74232e1046d794f3807e8054b9c26a55b9f08caf80fe8058b9c26c35b9f08cef80fe8ae12c90a1608e815b1062cc148b706e83675d10f02cec40da80daa06329bca7806e808184c6f2acf0809e808e914c9a321371908e802e900f4e0ae05e87a6cdad8ae08e8194b5f5b0de909e87a706445d408e8065361b6c507e80b00b2bd3805e8170129df1905e84653e2064ce8ca9807e8793396962b543317b200c4e32905e844444444116c298d9906016c5c6905e80652cad86607e8100e6a71 | false => 0x99709f443a340fe8941211be4467c65509e802e92e89d92da89e3748a6c653242e3216e8926537e609c4d0ca5f8c94cb0ce80ee91f84bef806e80b646db25f8ba5a3744d24397513e800b6e1d705e89800d4ca7905e89600d7a65305e8082df6e53174aeb806e805f087adb707e800c4352e7daf85b2b90de83296bf171b2265b2350ee89716b13d76e518a518a504b0984f2343d375ba390fe8910caa13ab15b3069830b7cad706e891018fc498060503ed7ca13507e808e9390330300d12245b236bd2db5f050be8390300300d12240393930f302d0b0293332f70240bd4ab8992dc6533ca21778d1114e808e90122b4d705e801b91c4cc6d6e50ae82d9909a606e813aa32c4d84d7dc71332a511e8c15ac344b708e80323815ac79a250ae80b0186c580d36ca2e908e808e900d2c8d005e801b91acad856c60ae82d9909a506e8194cd0fc95a280d6d2d6c611e84d2db5f05599300be8030f9a6cdc15660ae81102c6bf0e1418a90184e613346485ba510de89801143e134ddf2ccf080de8140326644aebbe320ae81a68957206e8048b84ce3607e8033845f097c6560ae80da005b3843e3207e80e06656445f807e80da3aa5f82adf808e800b4e1f605e806656445f807e817016c271905e80eb3130b19912baef8ca790ce8030b0899855baef8cb380fe83ef8d717b3138e0124baef05e80faf4b29e10209c71d5299d006e80209c311108bd319df1909e80553078ea55baef8e3320fe897976131e50329c74133e5825b9c261708e854b1e50f0211cb01d0c3652ee50226c202a5cb0b081401afc915b300b839f705e80501f8cb6c539b5dc6b09972a69710e85f0fe25f098e674461f70be867099e2954370f0be896ca67444e3708e813ab050b2a9b19a2644a6c2570bbe88a3a7916e84400909d6a941c4d11d30b12048ce84a7807e80129df1905e81f08e65306e8154adf29df1909e801f3cc030d9909855ba307caf80fe801f3cc058d990ac65baef846530fe815b200c3353605e80316b10db016b102a9c5d2e5b1b90ae800badaf905e816a896024ecb0db00caf154e2e972db909e800dbadf005e80caf58d1e0053e77e600c896a905e813b26b8ba5a309e80f9515b115aa030812335cf94f0809e808e91415be12f1cab609e803e90122c4d705e801f94b1b6be4b70ae8b651690a2608e8b64c99229708e8013ae52c6cad9336c50de80b0191ba0e00bb9628a612fc51130de85c71d410950eab3aa9e40301d2c552b9148aeb5f23756c5425d413e83a51e202f033e3343a510ae89601d094e884b66f0ae8022664a7444a360ae813ab050b0c899f51b7297d4b210d6e846889d2f919e80000076eb01b4d2fd30b1852f8e702f84be11cca740ae838d0899729d2f80be80226b6538be16e2ba53a632812e80be93e74e68e2ee9e618b302)) | false => (match Nat.blt i 40 with | true => 0x11013648d605e80175c4cd05e82ebc998d06e8196c4c84c65609e80cac985d72e4980264cde418a3612fe61702677c298465320ae809d5147e0e84d3320ce8030863e743ce950ae828fae4f206e811056586e718b1033c11308123033c113081230f12cb0a75b61409e818b10610930a65ca9609e803079d4cf8a2910ae8021868c84606e802e90e0314b80be915b60a97ae5809e80be90309c300fc223205e860b7e605e900e8cac505e805e90b030fbf0fe9980452cc95ae07e80309cb90203030534c240b02efc70129a23305e811ad0129a23805e82dcfe002285bf174e2e90ae80236ba0e2329a1f106e80f888d27665509e801233912714d3446780de8049cb2e1f207e89801952a732ba1d20ae898960aa6e8999896d9d20ce8050b24e5965806e80701243f0b05e80258bc1402b6c15697dd720ae80be911ac00fc2ca905e80eac0eac023296be5506e80194be1505e8276ca5b806e811b00194b65805e816b20300fc2ca905e816a8392be4039a3b270b07e800eb257805e801933a3205e8612fe005036c54e1eb07e86165d7036c97e16507e805e917030bc30fe90309c31f13cb0806e800fbe07705e803e9030fbf0fe917a800e4b23905e89605930228c711ad2119a27806e81945d2e7a25309e8650fdf00e9653205e801134d1805e85912e60b4613448d11a6110ce89319b203139d0f0235b21d2b96580ae8074ae3d704af84e2e307e804af84e2e307e8015ba70305e80f0255b9e324612f0ae81f13cb0806e818ca642c222709e80400400499023c2b0919c7c26371a2670ce82a7b8cc906e80f0305cb05e99020303092ec24933e28e111ad01190dcf2c66884ef80de8965354322533f087425310e8012c21f105e812b312b00e00e88d122b8d3442f80de80164b5d905e80174b5d605e80512b2070440440449023c2b440040490a342b0269bb5351a1d1354b84dc6912e854f7d10f0b02df13e16f07e807e94d18d90440440449423c1c4d18d94940404932ac2b4d18d90990093a042b0f144a34d511e9cd10f9c22708e810e913ab920b2257ca651714d08cef842f0f14e80be04381a32ccf080ce814c962673c68c26349511310e800f33a2605e810920ad8c97c314ca2130ce892258a2303736a278ca8641ae94ee616e806e9118d0ce4427408e80ee90184426e8993443a340de8940329a38d74426384d0e11a9112e80ee9ca1e34cd1408e807e0a9ca2c9899740ce8042d943cd1a08b3425740fe866772d90984e260be80e0274bc06537c3e7407e8ca5d09e29708e8309b5df006e80802b089985ba26373c4ea217412e89408996ea1a232a2130ce803e900b439f805e801743f1705e858b0339f99a1780be813716113384b09e80b8d0fc15d13212b0ce80737373ca23c140274bc125f097d1147c6920be814e905d2fc25 | false => (match Nat.blt i 41 with | true => 0xd8b6123096d865a996e7c6170ee808059329df1907e8058a994ef807e858a65b9f184af90be80da88762d53009e8006999043048131c9b198d2996e7c6170ee8080596960505583303f38435e607e8110944940409142b047324362307e80fb647132e1594f1943e2710e808e9035329df1907e8b99a9ad8a95ba53be71910e806d46eb152bc66570ce816c89a674af909e80654adca56e8df190ce8b156e7c6b708e808071415b31c20571616b319b00336c919b00336c90c00ca998d05e813e9959515b002a6ca95056322e702e915a00d0271adb23a99870ae80ce91b51998706e80ce93226e11b51998706e80ce90710a1f289ca2e08e811e90308c6b66425b4a608e80308c608e90175e29505e89808612bbe28891d900be8ca70b641b408e8030fc89406113296d843b1674463320ee814a1110324289a2e07e811e90e0289595194df0f3d3089464e12e811e9936688e10232bc10053085be5107e84ef8e716b956f8d2f809e8995af8e799035329d2d807e8993537dd5af8e76137e72e95d2d906e802f8cd30d34ddf1953190be82eefe508930217cc9464668c117c65330be800b4bef805e805f08ba56607e8c5d2ba99a308e80f1430884a7106e8b15794e2f808e8329be1f406e813b334d0e602efc70832c299b62acc96e4703352bb21f816e89805538c8df807e80329c3154e3235a1f809e898108cdf51ad1809e80bb20fb28f0168cc1702f8cd66539952f808e83389d6d706e855b7e3030805b384aef807e807163e5347cad709e8189b0cac33e13a9e980ee808930c4df28b265409e8333336930631340712b201a6c80161a6665c10da3e130de80756e9c8d654358f99b08a3cf213e81100b355303a298b95120de815b5d3964eb909e8034333cc501c0532c458cc9e052351120ee808e90cac9e12ba54c7b26974365910e80202c9adf099d72c0ae803c3332c301c0343332c501c03c3330cd01c070533776737023441be13660a8808e812036853652f84cebb96c90fe8308a2e7506e817b202019614065a65090ae8658503d30808e81205f145990c69592a5af90fe801a97d6f8451f20ae8c56f8425f4c896c6961610e802ea55b61407e8980601a6c895cad640d408e8066c3aa56dbe0a85b2570fe807960db002c6c102b811e885be570ae8b1b079c19708e85670e703c333ac101b0516b203c3332c301b030fb10610d7d27707e80ba60fb106101bf055c916148ad64cd411e80be12c6dc4b2ad920ce80711a610fbe13308e80cac020103d92d29e7733e870de8184adf74dae544ccfa1f0811e80f4cec86c27809e810ae0684cf94e6ccc0865a5b0810e8120258cd03095d2d7451f30ae8070a4f035dcb0c2193351f53a17214e811960a59098c96c88a530ce802e942c9e50636033b6c67a2f20ce80176993705e80194bb | false => 0xcc07e815b10300658498880035480654989800344891b8ee97e11108e8136509de0eb14cbba56809e800b7e2e305e803e9119555f0e50b21924adb38deb80ce813a95bb2883e7708e8194b2c85bf1909e812a86a59643a4608e81118a99505b1945df807e89616b311a006516ca6f807e80154593805e8ca6426d8b708e80b950ba2562b537c2df00ce8024bc50310ab97970b0893065174e2e907e80235ba102df7464495e1130be831335d6f8dc774ade80ee802d933d09c3e330ae88f05ae54bf0807e8009405050b342d0b10016c271905e8016c271905e81212b54cc88d2fbae1194f1911e86586e899837dd708e71910e801c9cd17b312904137d912b04139e001c9c601f7595a9b19d00ae801c9bf115b53195f1908e89997976131e5169f0329c63932e5012ce13705e80b0592e596c37dd708e3330fe88e9741f1e5169f0107dcae05e80b0803509be32707e808e96509e0ca668b261208e85d3274f266ba120be8010b95194b8d84ca680de8352f86653ba2f80be8009707090a943e16b22c64b6f506e8030b1d145d2d91b2974af80ee8326722e976645321d20ee8017c964e89b09922f80de800090707000ad53e009707090a943e336ba5b606e89616b115b5c71331f509e8050b07199336c3b9638425f30ee801836c8d1c21330ae8100199a1f105e80329c72b7c25f306e800d7d6c32c4d7c26330de810328ba5d806e80c64c9ba3267a1d20ce819426ef94d1809e82e96db1706e8174c26973ed809e820f95b1906e802a9c4652eb36774b6a30be80f050b02df1921f307e839f7e616b105f09adccc07e8050228cc12ca1d19e11209e80124e2f91bd381cd170de8ba5b275b1708e839104b63995b170be816b12c9ca27006e803354d9d8131a60ae811050b02df1c223307e80255cd16a861aa96ba3208e80501c8b26a369ac90ae800c715a9abcd171ac50de80b59114dea64b4780be85ea3b19afb8ec50be80b2329a1f106e802d91c4d094ef80ae80159df1905e802e12ccef807e8164adf29df1909e80172cc01f91b4b7c26a2345cb7427912e80172cc2c64bb32131375c2790ee816c64554e06973eeb84b3311e8196148c98baeb863330ee80194b27205e899be12d74ab608e80184b67505e89932974f1906e8be12eccab808e801b1c963f297431308e816b39632974f1906e801b5cc00bb3a5705e8022e57e69616b116a8050832874af806e809e5154ba45c21d20ce8ce0a9922f808e85658e701a963a55be7190ae801a9663329d6f90ae81a674af906e800d4df1905e802c5c9080b826c54ba3308e819a282cae1163308e8066269a1d107e816fc21d106e816fc21d106e8129702d7ba5723db16a00e0705f2571ad707e80154b70305e80fb5d2f84f1908e858a95b9f08df190be8058a67625307e81a5ba56e06e802))) | false => (match Nat.blt i 45 with | true => (match Nat.blt i 43 with | true => 0x8e2b93a27506e80552f84cf207e80328c605f32599e707e813c9ea99e51209e8ba6a8ca64b6990f99d1210e832992eb706e8124e5125b5c609e80ea5194ba4b6d6d709e84cf2d948cfd501d2bf119600db25f805e89718a317a30309ca0d972b93a27506e8055308ccf807e80328cc0335c64f3455380ae8923194ae1108e818ca70b6dc6809e817a50923194cd185b5d00ce8015ca6ce3611199d180de8309b36e95b47199d180ee80164df0b05e86071d502f8bf0f971b63363206e88652e7e2eb08e88652e7e2eb08e819b00215ca01d0c619b09915b117b2023658e79918b3029998999802052513e11206e82513e11206e80309c392990329c60e9190e8465809e800d99e3305e8999992011921d305e892061e74c6f807e802024ebf0ee917b39616b10210ab989817b30200e8d8d9425ae946d80de80328c60328c6015be0e805e811050b0044488988003944044489890038449032660dc232632ca20f0ee8130127196505e82f84dcaea992b2b2c60ee810004448988800394404449898003844908b8468c90f08e8136509de058b27423733a58426130fe800b93a2605e806e90f8d02c8c16e95b66f0ae835d0df13ab12ab8d963284c23308e805b194261207e818b318b301f7bd015b21d205e856c8e0b17096d8ae08e80b8d104d7287c6d909e818b10184aee305e80f3097dcad1427543a4b0ee8030bc30619b2990eab960397970eab0eab030802b6cc309b157506e80da8061c87e32906e8018fb71045c2723295c9130be801579a2e10ccb8a1330de81746132ba1f309e891058ce2c64807e80409050507382d0b10030fcb10a910a90b0802e9cd02e9cd1805b037d4c972e0f94f190fe802e9cd0eb318900226bf17b22e6ca61806e802e3cc00b744d005e85ccbde0f2c64baeb2b5307e6570ee8057055d8c972e0f94f190fe8998e17b248cedd5ccedd4b29e65caee600f844ce05e80b058d7596c6745707cb330fe80211cb97422ee502c6c504605b19d707e80b080585544b2707e808e94b29e60b15af3263094d0e0ce805b191cd1807e801945d3243a66846b80de801a676677c21d20ae808090d0906983e16b1ce10fc25cd08e8060b9307a6a5744d7c21320ce81745729c5cb209e8036f9c164e8990e4c6f80fe80090900d0006f93e09090d0906b83e018325b605e8960eb0184b6ce3323509e8050b070309c30309c35d30e3979597018ba5f105e89700fba5f305e8971943af54bed809e897174593243e3809e803108e4f243f1709e8030fbf0fe99797980317b317b218b10271ca020be13031de96daf80ce80269cd3613d70328cc0f050b00568689880035480566898900344891ca565ad8d71a5f8ca21110e81305ae5c25d707e80ca5b81dd65356c30ce80f19ad9917a997069118b317a917a9060812b205f09b5c | false => (match Nat.blt i 44 with | true => 0x32994e9806e8082f84b1f306e802d9c60fad3539458c8ca5f30be864c95be17465330be814916cb325687d2743361210e80096360c70330164b1a259708636530de89494065cacd402db52b58607e816b316b317b217b20212070333366322d14108e910b10288c60096660ed033014a8f08635f0b1a740de8059a5ca59207e8071136c98c8468cb050be811e934d74ae36146450be811e900033308d01b012cc4f6ba6d75b6590de89797022a9a40ecc9e143a329646423472516e811e9050ebe4b03652b08e8232c232906e81f13cb0806e812744c74632909e807e90b140194be5705e8919190900fab0174ae5805e8012aa72675d687c6580de807990104df0905e819a3000008998800194419144d8425f209e802e964d1e016b212b0652fe60652f95af807e815b318b30215b3050b19a33287c65806e898920fab17b299072279232906e81f13cb0806e800000899880019441f13cb0806e81f13cb0806e8232c232906e81f13cb0806e81898e2f806e82a993a1206e80fab017c263205e85af8e7070b03e279610b07e80be90258bc145117e67c470a22f808e8c3cc88d20308e803e90b6509dc7c4d0a21d208e80328ba5a5b9a56425d07d20612e806e90b01f1c80eb136f84d2c874af80be80d4e2f84ca8809e808e90b07130193a28b05e807e989e885cac208e802e90e0147e68705e80fe95aebd50be903194c7147ce870ae80fe90000b323e4b81b0ce910ad01580e2e32274ca2070de810e92d7a4466ca677c21f30ee864ceb5d33a22a90be8105aebd50be9070317b90be904131a62eb07e804646badb607e84911d964d7d90e0171396d05e802e902db1b227907e810ad10ad17b20703f09762eb07e80be99919b2021b0b8d7006e8901d858eeb06e80f17b20714209a2218a1f284dd740ee807e903277a232a1f08b26e64c23612e80c99344592c6c6d90ce8056d93469907e805b264b65907e803086ce194ceb60ae803364c1a644a750ae82663c90c6a674adaf90ee86537e4525944cc9636f90be8017c26f605e8037299d2b607e80204646badb607e8015bd92da6512c9e08652561197215e802e91433534432d909e800303323ac321b0336cc00000b2e901b0336cc0396283899f0ca5b3b5f1910e812b02343365906e8017c26f605e85234e30264d7d90e01814a3505e802e94f27e107e9015c9e3205e807e90090e0ee101b07e91405612fd90be918b3046533cb0807e86322e702e90309c33ac9dc3297465706e800e4bed805e8963296c71706e823934a3206e84aa9df0510b10fb117b2030b23243f0b06e80be90119a7199087132e78448f343e2715e807e91418b3249be13106e80309c30194be5805e8652de40329c4050b9618a315a30309ca0d16b19918b110ab990216a89512b318b395039618a317a00309ca0d | false => 0x18a2140b28892e265cac25bef80ee802e901eba610b95af80ae814ab3e878b4cb8cac20be806e914ab0294012cdaf805e83eede519b00317c402040e0db11667597809e80be914b20166ac8605e814b214b207018ca29205e83136e7016c19b205e818ab3518e70311c8020166ac8605e801943e9805e812ae510bdf05242899ab07e8510bdf01943e9805e80404644336cb07e83564d4046466d96407e804e90e02cbc10de9592ee21af1db0906e800d7585605e802e902cdbf0de90209c9ca1cda26b808e80289cc091df0aa70779a0f0ce89519b00615a00d12ae0143be7905e89404950faf20faa6b606e8652ddd4a89e60103d53605e80530e2611607e80361c2d462c279994191c60be8061d6159c607e81d11bac606e80d032369b087a5d60ae81af1db0906e8143e10eb25e309e80020020c2c023c222a3611c606e80e60c92a11c609e80d02c4c204e935e9e33191552f21ece6a6b80ee86134e00154c65405e80400c209096ab41c950faf49f4890c87a6150be8016c25af05e818b318ac140c21f4351154ba160ce816b2030022022c22023c22020202c20638220c22323b2143c90eb09f1c11c614e8308ed40d0b02daf1d96d07e803e96136d90022022c22427c1b6136d90c2202c24a14226136d900cc0c2e70220d170fb2017ce06605e803e91018b34d39e613a14d39e613a11001924b0805e804e99313aa0650c8ceb807e83048465506e83287467706e83154b63206e8076322e702e9328ba7194b271340ef0ee810e90f00c4d7383c1e88cb040de80fe93299a1e406e80fe90171c63299a1e406e80fe904140518b3016be32505e805e90b0eac9901d2cc05af943a5307e82799091206e89301733a5305e84845d40b05d9b51a5f82b8cb94ce99a16e14e80ee9920664899d7207e812a000c6957205e8199f27944ce906e80d909a542e6709e832894d6606e80e6322e002e9173496e32dc709e80be9114a68dc08e900000669660439330000066966043933000006696604393312ad12ad00000669660439330806be065a1d299e680ce807e91c894ceb06e80be95cae42cc874a670be80be9111450f1e007e9017431d9191a2e0ae811e90e319a591206e801b4bb11319a591206e80bae42658b9909650ce806658a591207e808e900d8196505e814a21201b4bb00d8196505e801b4bb01b4bb00b60a8805e81211274cd90966322351120ee800f99ad742578a3ce80de8110324289a2e07e811e90e06059a591207e802e9056c67d0c84b6129d3070fe807e91106059a591207e802e999995059e00332c805ae563606653221e6540fe80da59999989898029902c9c00361532d9207e898020332c850a7e0989702c6c19701632d8d05e898980db01531d2c6c29609e80db005086656d005e9993265b1b206e8020194caf805e8)) | false => (match Nat.blt i 46 with | true => 0xe80b1805f045c5f307e804e90224c304e903cd07a1d25c678221770fe804e94f08dd1f7c267106e80211c63e37e693931d619a32adf38426f80ee897627174b6b708e8030f0189217205e802c5b652b1c0d50ae802a5bd179202e6c205ccca95f707e8009090c24a311c0b0bac94ef8ca17108e80309922f84ae530ae800fbe13305e80189217305e803372ad2d9df190ae8040194265705e817b39997973937e7184b299df3845c980be8258ca2f806e802f8cdb5c712571208e8050040c09c9064991c016b8ea54c658b90a60de80b05909adf0f07e8065377a22407e84d18dd5df3c22244dcaf0be80b390d4e56f962f80be8164dccd4d4ab7490b7df3811e89257371bd2b6df190be81afc5f1906e8040758b03552b74657c1de88cb0413e807e998066d71a5c5ca5703a2f80fe8989717af090f5729be0b1339783bd0f95f0413e807e94b08d99802095c4f94e2f80ae89802b7c16c35a2f80ae80f041414b20303bd03e91714b29914b103d34c5c9407e80144df0905e80297cc02e4c80144df0905e80b01412ec405e802e9972c4a1d7706e80176bd2eb6e5174aec3a1d1709e897c2e89be12b21f08a1e1710e8169adae906e80f3ee9e609e9ca28b22ee608e80be90d5db8b5c466cac40be80de9016fbb6e2b19a40ae80de99418bb6c23372409e80de9040e05d13cdd3807e808e900c59db73a613adae30de803e90fce0929a13808e804e999995d19e602f9cc0172460699e7745f380de811a59999979797089944d2e101999d7805e8970802f9cc5d19e610b1971942db0c56d709e81942db0c56d709e82d90448f0b5f380be8979e3285db3808e810b102f9c21933b6170ae802f843a675c2770ae803090324c604e9993275c67806e80801945af805e8328adaf806e8090124d73805e80259cc0daf4d194c8f06b9350be82133353506e8170650bc1d096deb73c2780fe800c4440c702c01245d31c4d0b242380de89797070244bb4f28e113b312b313b313b30818030449944422317b09e90eaa02e9cc00c4440ed02c08dcd64b61199eb70ce80194cccc3c4c84aed80de8030f0251360ef437040ae80fe938d13adf243f040be80fe900099908902d0310899e85c6530ae80fad8e07018db5f29add19c25f343f2412e80fe90414018136d805e802e901e3c10de91700ea62cb05e80be914b203ad8125e3b11c64adf80fe8610be20be9c22263ba8b08e80c5a8742ec97d4780ce80d0184b6cb05e80be96136d905b084bc6b07e86136d916c0dcb4bc6609e80d170bb15f07d607e91417b30194bf1705e818a2612fe501f8bc140328c344f9d61a9b508906e817974236e511b019ac020db90c9c593709e8000933003300191b012b62f805e84ad7e60337cc0701f8bc1f8b913706e85b37e602f9cc07146137d917e903cf84271707e8 | false => (match Nat.blt i 47 with | true => 0x41418b32394cb0206e802e90309c3ca5b3adae508e805e90b18b39919a23088c88f06e84726df19a31093f08899e709e84726df0090c9001f1a31131d1806e8c21cf8c88608e8189f2188992f06e8c25af758a608e8189e0b02533adf9c212b0ae80be99898059999050215c30215c3036322e702e94726df59397cf08899e70be80f4b8cdb170909e80849f8444cf99e260ce8016ce06905e803e9022fc40211cd022fc415b20211c903c25afb15c608e8b270f89f08746444d8a610e83096bec506e80b2638790ce29deb0ce80fe90b606fe603e9652be601f0c998652be60215c3980175cc95980329c31b54adf806e802d92b4c9abe390ae8652be60329c316ce0abae12f09e898033032bd3806e803e9989803152992b7d70309e805e90e854a95bf0309e805e915b25538dd0315c402d8cd0bb00bb3050154c23905e803652be6652be60175cc02a9c35709dd652be60317047299605907e802e99898089999080233c30233c3070278bb08e919a108e90233c30701844ef805e801844ef805e8033845d31911f30ae81f34448f06e801844ef805e8026fc50233c30194caf805e807031d0890d7c261194d180fe819b202f8cd00eccab805e809045e8891f307e8045e8891f307e8899d9c26e8c12267cd1810e8026fc50233c31133ab7ce13209e807000004494404392b0000494904382b17a10f1f84bef806e81f84bef806e8612fdf6111e01f84bef806e804990124470805e8017b613805e80119130805e80119130805e818a30119130805e8019c22444c4c7c22e90de805ed84b8d807e805d382d870b8d09c10d7c2648890c717e8004040090004392d988e2e42c4f808e818a16091d52f82162706e80194b46e29a3821a270de802f9c0d17c1e240ae875b032df0708e80f01229d0e05e8017b26f805e8980194dd1805e80194df0805e80194df0805e80f0fc150e8caf809e86111e00fb20fb20fb200fc19d105e80fb205040308c398652fe617174e0b61c2e34c4c7922f811e8174bb25c22f809e80949494d01d8470592e2df0707e80f0b0309c3985738d7000199809f1a9819a31760b7e605e911911187df0509e805e90b05b38426f807e8194ba5384518b8c8534f0811e803a304608607e804a79c22f807e816b113b1a3045af809e8050040c09c9064191c329635c684d194be519e2f82151716e80b652f8cc91446670be811e9036c97d865744d29a16fc5f0442e1817e804e9650be6026fcc026fcc13a90b2119911806e804e902c8bdca6151e70908e8013b670805e803491335e471a684e7090fe8019c26c805e80184b6c505e80652db166807e80b650be66065d70990c0992c113e060752a5f807e81700b899f29e10b891e70de80be997016ba592a96c26962678e4445d7715e89717ad875ca5e309e803d36b8ec507 | false => 0x10b32373368406e804e9b99b08df2308e807e9030f01e7cd214be4a606e805e90d01e631634320931f52e4d304e90e030114b1043200c322208d1b0fb1042342bf2306e805e9030d0eab0eab4262424240a32304229c95e306e805e9030d010018b3179f05e90b18b36111e00194265705e86111e00194265705e80194423205e86512e5040193cf0805e807e96111e001843e3205e86111e001843e3205e83288465706e802e9c1046322e702e9c25d7790ab08e80fe90b0175bbee87cb040ae80fe90175bbee87cb040ae80fe99215bbee87cb0409e80fe9))))))
def tapeByte (i : ℕ) := Nat.land (Nat.shiftRight (tapeByteBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def initialOffsetBlock (i : ℕ) : ℕ := 0xbc798f7d861000000000835700000000814e000000007f0d7b16771f00000000735c6fe0000000006f5f6e1600006d786c0e00006b806a8b00000000000000000000679f65ae000000000000000062a661fe00006169000060d4600d5dbd00005c1c0000000000000000593158630000579d5268514e0000000000004ffb00000000000000004f9b4e964e0f46f9443100004263419841240000000000000000000040c83efa3e863df0000000003d4700003a70000000000000000039fe38ef38a937943113000000000000303800002d130000000000002c9d2c372b9000002ae127102631254b0000000020c31fb11ea00000000000001d7f00001c981bb81b4d00001acb1a1e19021883000000000000000017df0000000017870000000000001731166b0000000015d6138613050000000011db00000ee90000000000000000000000000989086e000008230000000000000789000000000000000000000728000006a3000000000000064705eb058400000000052502cd000001dd016c000001030060000000000000000000010000
def initialOffset (i : ℕ) := Nat.land (Nat.shiftRight (initialOffsetBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def finalOffsetBlock (i : ℕ) : ℕ := 0xbcd9bc798f7d00000000861000000000835700000000814e7f0d7b1600000000771f735c000000006fe06f5f00006e166d7800006c0e6b80000000000000000000006a8b679f000000000000000065ae62a6000061fe0000616960d4600d00005dbd00000000000000005c1c593100005863579d5268000000000000514e00000000000000004ffb4f9b4e964e0f46f9000044314263419800000000000000000000412440c83efa3e86000000003df000003d4700000000000000003a7039fe38ef38a937940000000000003113000030380000000000002d132c9d2c3700002b902ae12710263100000000254b20c31fb10000000000001ea000001d7f1c981bb800001b4d1acb1a1e1902000000000000000018830000000017df0000000000001787173100000000166b15d61386000000001305000011db0000000000000000000000000ee909890000086e00000000000008230000000000000000000007890000072800000000000006a3064705eb0000000005840525000002cd01dd0000016c0103000000000000000000600000
def finalOffset (i : ℕ) := Nat.land (Nat.shiftRight (finalOffsetBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
abbrev EvalState := ℕ × ℕ × ℕ × ℕ × ℕ
def layer (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) (next : EvalState → ℕ) (state : EvalState) : ℕ :=
  let (t,D,eq,fl,q) := state
  let d := settled D q
  if d == 0 then t else
  let tag := byte t
  if lt : tag < 26 then
    let i : Id := ⟨tag,lt⟩
    let cand := laneRead d i.val &&& allow eq fl (!(orientation i))
    match optionsBy high 1024 cand with
    | none => 0
    | some vals => vals.reverse.foldl (fun loc val =>
      if loc == 0 then 0 else
      if bd : val < 1024 then
        let raw := rawFrom i ⟨val,bd⟩
        next (loc,replacePacked d i.val (1 <<< val),eq &&& sameMark raw,
          fl &&& freeMark raw,1 <<< (1025*i.val+1024))
      else 0) (t+1)
  else leaf d tag t
def play (f : (EvalState → ℕ) → EvalState → ℕ) : ℕ → EvalState → ℕ
  | 0,_ => 0
  | k+1,s => f (play f k) s
def assisted (f : (EvalState → ℕ) → EvalState → ℕ) (tip : ℕ → EvalState → Option ℕ) : ℕ → EvalState → ℕ
  | 0,_ => 0
  | k+1,s => match tip (k+1) s with
    | none => f (assisted f tip k) s
    | some v => v
def canonSearch (hint : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_,_,_ => 0
  | fuel+1,t,D,eq,fl,q =>
    let answer := hint t D eq fl q
    if answer != 0 then answer else
    let d := settled t D q
    if d == 0 then t else
    let tag := byte t
    if lt : tag < 26 then
      let i : Id := ⟨tag,lt⟩
      let cand := laneRead d i.val &&& allow eq fl (!(orientation i))
      match optionsBy high 1024 cand with
      | none => 0
      | some values =>
        values.reverse.foldl (fun loc val =>
          if loc == 0 then 0 else
          if bd : val < 1024 then
            let raw := rawFrom i ⟨val,bd⟩
            let d' := replacePacked d i.val (1 <<< val)
            canonSearch hint byte high settled leaf allow fuel loc d' (eq &&& sameMark raw)
              (fl &&& freeMark raw) (1 <<< (1025*i.val+1024))
          else 0) (t+1)
    else leaf d tag t
lemma canonSearch_impossible (P : Marks → Prop) (mov : ∀ m π s, P m → P (moved m π s))
    (hint : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hintSafe : ∀ (hist : Trail) (m : Marks), P m → fixedHistory hist m → ∀ t d eq fl q,
      ordered m (hist.map Prod.fst) → flagsMatch m (hist.map Prod.fst) eq fl → pathBounds P hist d →
      hint t d eq fl q = 0)
    (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ)
    (settles : ∀ m, P m → ∀ t d q, insidePacked d (represented m) → insidePacked (settled t d q) (represented m))
    (leaves : ∀ m, P m → ∀ d tag t, insidePacked d (represented m) → leaf d tag t = 0)
    (adm : ∀ (m : Marks) (i : Id) eq fl, acceptMark eq fl (rawNumber m i).val →
      (allow eq fl (!(orientation i))).testBit (represented m i).val = true)
    (fuel t d eq fl q : ℕ) (hist : Trail) (m : Marks) (hm : P m) (fixed : fixedHistory hist m)
    (ord : ordered m (hist.map Prod.fst)) (flags : flagsMatch m (hist.map Prod.fst) eq fl)
    (bounded : pathBounds P hist d) : canonSearch hint byte high settled leaf allow fuel t d eq fl q = 0 := by
  induction fuel generalizing t d eq fl q hist m with
  | zero => rfl
  | succ fuel ih =>
    let dn := settled t d q
    have bn : pathBounds P hist dn := fun n hn pin => settles n hn t d q (bounded n hn pin)
    have dn_ne : dn ≠ 0 := by
      intro e
      have hv := bn m hm fixed (0 : Id)
      change dn.testBit _ = true at hv
      simp [e] at hv
    rw [canonSearch]
    simp only [hintSafe hist m hm fixed t d eq fl q ord flags bounded,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    change (if dn == 0 then _ else _) = 0
    simp only [beq_eq_false_iff_ne.mpr dn_ne,Bool.false_eq_true,↓reduceIte]
    split
    · rename_i lt
      let i : Id := ⟨byte t,lt⟩
      obtain ⟨π,sw,ordered',same⟩ := extend_ordered ord i
      let n := moved m π sw
      have hn : P n := mov _ _ _ hm
      have fixed' : fixedHistory hist n := fixed_move fixed same
      have flags' : flagsMatch n (hist.map Prod.fst) eq fl := flags_move flags same
      let val := represented n i
      let cand := laneRead dn i.val &&& allow eq fl (!(orientation i))
      have member : cand.testBit val.val = true := by
        rw [show cand = _ &&& _ from rfl,Nat.testBit_and,Bool.and_eq_true]
        exact ⟨heldLane (bn n hn fixed') i,adm n i eq fl (accepted_order flags' ordered')⟩
      cases opts : optionsBy high 1024 cand with
      | none => rfl
      | some xs =>
        have inList := optionsBy_covers opts member
        dsimp only
        by_contra notZero
        obtain ⟨loc,nz,ran⟩ := checkedList _ xs.reverse _ notZero val.val (List.mem_reverse.mpr inList)
        let hist' : Trail := (i,val)::hist
        have extendPin : fixedHistory hist' n := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | h
          · rfl
          · exact fixed' a h
        have bound' : pathBounds P hist' (replacePacked dn i.val (1 <<< val.val)) := by
          intro z hz fixedZ
          have old : fixedHistory hist z := fun a ha => fixedZ a (List.mem_cons_of_mem _ ha)
          have pin : represented z i = val := fixedZ (i,val) (List.mem_cons_self)
          rw [←pin]
          exact replacePacked_sound (bn z hz old) i
        have recursiveResult :=  ih loc _ _ _ (1 <<< (1025*i.val+1024)) hist' n hn extendPin ordered' (advance_flags flags') bound'
        change canonSearch hint byte high settled leaf allow fuel loc _ _ _ _ = 0 at recursiveResult
        have raw : rawFrom i val = (rawNumber n i).val := rawFrom_rep n i
        apply ran
        rw [←raw] at recursiveResult
        simpa only [val.isLt,↓reduceDIte] using recursiveResult
    · exact leaves m hm dn (byte t) t (bn m hm fixed)
def wrapCanonHints (hint : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (base : (EvalState → ℕ) → EvalState → ℕ)
    (next : EvalState → ℕ) (s : EvalState) : ℕ :=
  let answer := hint s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
  if answer != 0 then answer else base next s
lemma canonWrappedPlay_spec (hint : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (byte high : ℕ → ℕ) (settled : ℕ → ℕ → ℕ → ℕ) (leaf : ℕ → ℕ → ℕ → ℕ)
    (allow : ℕ → ℕ → Bool → ℕ) (fuel : ℕ) :
    ∀ s : EvalState, play (wrapCanonHints hint (fun next s => layer byte high (settled s.1) leaf allow next s)) fuel s =
      canonSearch hint byte high settled leaf allow fuel s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 := by
  induction fuel with
  | zero => intro s; rfl
  | succ k ih =>
    rintro ⟨t,d,eq,fl,q⟩
    rw [play,funext ih]
    rfl
def traceIndex (v : ℕ) : Id := ⟨Nat.mod v 26,Nat.mod_lt _ (by decide)⟩
def traceApply (cut : ℕ → Id → ℕ) (d : ℕ) (i : Id) : ℕ :=
  Nat.xor d (Nat.land d (cut d i))
def traceMany (step : ℕ → Id → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,d,_ => d
  | n+1,d,p => traceMany step n (step d (traceIndex (Nat.land p 31))) (Nat.shiftRight p 5)
lemma traceMany_keeps {w : Valuation} (step : ℕ → Id → ℕ)
    (safe : ∀ d, insidePacked d w → ∀ i, insidePacked (step d i) w) :
    ∀ n d p, insidePacked d w → insidePacked (traceMany step n d p) w := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => ih _ _ (safe _ h _)
def finishTraceBy (pick : ℕ → Id) (d endPos : ℕ) : ℕ :=
  match Nat.beq (laneReadRaw d (pick d).val) 0 with
  | true => endPos
  | false => 0
lemma finishTraceBy_safe {w : Valuation} (pick : ℕ → Id) {d : ℕ} (h : insidePacked d w) (v : ℕ) :
    finishTraceBy pick d v = 0 := by
  have keep : (laneRead d (pick d).val).testBit (w (pick d)).val = true := heldLane h _
  have ne : laneRead d (pick d).val ≠ 0 := by
    intro z
    rw [z,Nat.zero_testBit] at keep
    contradiction
  have nb : Nat.beq (laneReadRaw d (pick d).val) 0 = false := beq_eq_false_iff_ne.mpr ne
  simp only [finishTraceBy,nb]
def finishTrace := finishTraceBy (fun d => chooseSource (Nat.xor guardBits (dirtyBits d)))
lemma finishTrace_safe {w : Valuation} {d : ℕ} (h : insidePacked d w) (v : ℕ) : finishTrace d v = 0 :=
  finishTraceBy_safe (fun x => chooseSource (Nat.xor guardBits (dirtyBits x))) h v
def traceBytes (byte : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.lor (byte (Nat.add t 1))
    (Nat.lor (Nat.shiftLeft (byte (Nat.add t 2)) 8) (Nat.shiftLeft (byte (Nat.add t 3)) 16))
def spanBytes (byte : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,t => Nat.lor (byte t) (Nat.shiftLeft (spanBytes byte n (Nat.add t 1)) 8)
def checkedHint (byte : ℕ → ℕ) (step : ℕ → Id → ℕ) (rounds : ℕ → ℕ → ℕ → ℕ)
    (leaf : ℕ → ℕ → ℕ → ℕ) (t d q : ℕ) : ℕ :=
  let op := byte t
  match Nat.blt op 26 with
  | true => 0
  | false => match Nat.blt op 126 with
    | true =>
      let a := Nat.shiftRight (byte (Nat.add t 1)) 5
      let b := Nat.shiftRight (byte (Nat.add t 2)) 5
      let fuel := Nat.shiftLeft (Nat.lor a (Nat.shiftLeft b 3)) 1
      leaf (rounds fuel d q) op t
    | false => match Nat.blt op 128 with
      | true => finishTrace (rounds 400 d q) (Nat.add t 1)
      | false =>
        let first := step d (chooseSource q)
        match Nat.blt op 232 with
        | true =>
          let desc := Nat.sub op 128
          let group := Nat.div desc 26
          let second := step first (traceIndex desc)
          let next := traceMany step group second (traceBytes byte t)
          finishTrace next (Nat.add (Nat.add t 1) (Nat.shiftRight (Nat.add (Nat.mul 5 group) 7) 3))
        | false =>
          let n := byte (Nat.add t 1)
          let width := Nat.shiftRight (Nat.add (Nat.mul 5 n) 7) 3
          let next := traceMany step n first (spanBytes byte width (Nat.add t 2))
          finishTrace next (Nat.add (Nat.add t 2) width)
lemma checkedHint_safe {w : Valuation} (byte : ℕ → ℕ) (step : ℕ → Id → ℕ) (rounds : ℕ → ℕ → ℕ → ℕ)
    (leaf : ℕ → ℕ → ℕ → ℕ) (hout : ∀ d, insidePacked d w → ∀ i, insidePacked (step d i) w)
    (rnd : ∀ fuel d q, insidePacked d w → insidePacked (rounds fuel d q) w)
    (leaves : ∀ d tag t, insidePacked d w → leaf d tag t = 0) (t d q : ℕ)
    (inside : insidePacked d w) : checkedHint byte step rounds leaf t d q = 0 := by
  simp only [checkedHint]
  split
  · rfl
  · split
    · exact leaves _ _ _ (rnd _ _ _ inside)
    · split
      · exact finishTrace_safe (rnd _ _ _ inside) _
      · split
        · exact finishTrace_safe (traceMany_keeps step hout _ _ _ (hout _ (hout _ inside _) _)) _
        · exact finishTrace_safe (traceMany_keeps step hout _ _ _ (hout _ inside _)) _
def proofHint (byte : ℕ → ℕ) (e : ℕ) :=
  let step := tightCut (denseChart e)
  checkedHint byte (traceApply step) (rawLoop step chooseSource dirtyBits guardBits)
    (readLeafFast (modelPos e) byte)
lemma proofHint_ok {e : EnvelopeId} {w O R} (h : encLayout (modelNeg e) (modelPos e) w O R)
    (tested : ∀ m i j, testLink e m i j=true) (byte : ℕ → ℕ) (t d q : ℕ) (ok : insidePacked d w) :
    proofHint byte e.val t d q = 0 := by
  have one : ∀ x, insidePacked x w → ∀ i, insidePacked (traceApply (tightCut (denseChart e)) x i) w := by
    intro x hx i
    change insidePacked (restrictPacked x (tightCut (denseChart e) x i)) w
    rw [tightCut_eq,correctChart e,quickCut_eq]
    exact sourceCut_keep hx (hint_valid tested h) i
  apply checkedHint_safe byte (traceApply (tightCut (denseChart e)))
    (rawLoop (tightCut (denseChart e)) chooseSource dirtyBits guardBits)
    (readLeafFast (modelPos e) byte) one _ _ t d q ok
  · intro fuel dd qq inside
    exact rawLoop_keeps (high := guardBits) (source := chooseSource) (changed := dirtyBits) one fuel dd qq inside
  · intro dd tag pos inside
    exact fastLeaf_safe h inside _ _ _
lemma replaceGroup_sound {d x : ℕ} {w : Valuation} (ok : insidePacked d w)
    (i : Id) (bd : x < 2^1024) (keep : x.testBit (w i).val = true) :
    insidePacked (replacePacked d i.val x) w := by
  intro j
  have vlt : (w j).val < 1024 := (w j).isLt
  simp only [replacePacked,Nat.testBit_xor,Nat.testBit_shiftLeft,ok j,Bool.true_xor]
  by_cases e : j=i
  · subst j
    have eq : 1025*i.val + (w i).val - 1025*i.val = (w i).val := by omega
    simp [eq,laneRead_bit,ok i,keep]
  · have ne : j.val ≠ i.val := fun h => e (Fin.ext h)
    by_cases lt : j.val < i.val
    · have no : ¬1025*i.val ≤ 1025*j.val+(w j).val := by omega
      simp [no]
    · have ge : 1024 ≤ 1025*j.val+(w j).val-1025*i.val := by omega
      have pow : 2^1024 ≤ 2^(1025*j.val+(w j).val-1025*i.val) := Nat.pow_le_pow_right (by decide) ge
      have f := Nat.testBit_lt_two_pow ((low_lane d i.val).trans_le pow)
      have g := Nat.testBit_lt_two_pow (bd.trans_le pow)
      simp [f,g]
def canonLane (a : ℕ) : Id := ⟨Nat.mod a 26,Nat.mod_lt _ (by decide)⟩
def canonHint (byte : ℕ → ℕ) (allow : ℕ → ℕ → Bool → ℕ)
    (normal : ℕ → ℕ → ℕ → ℕ) (t d eq fl q : ℕ) : ℕ :=
  match Nat.beq (byte t) 233 with
  | false => normal t d q
  | true =>
    let i := canonLane (byte (Nat.add t 1))
    let cand := Nat.land (laneReadRaw d i.val) (allow eq fl (!(orientation i)))
    normal (Nat.add t 2) (replacePacked d i.val cand) (Nat.lor q (Nat.shiftLeft 1 (1025*i.val+1024)))
lemma canonHint_safe (P : Marks → Prop) (mov : ∀ m π s, P m → P (moved m π s))
    (byte : ℕ → ℕ) (allow : ℕ → ℕ → Bool → ℕ) (normal : ℕ → ℕ → ℕ → ℕ)
    (hs : ∀ m, P m → ∀ t d q, insidePacked d (represented m) → normal t d q = 0)
    (adm : ∀ (m : Marks) (i : Id) eq fl, acceptMark eq fl (rawNumber m i).val →
      (allow eq fl (!(orientation i))).testBit (represented m i).val = true)
    (hist : Trail) (m : Marks) (hm : P m) (fixed : fixedHistory hist m)
    (t d eq fl q : ℕ) (ord : ordered m (hist.map Prod.fst))
    (flags : flagsMatch m (hist.map Prod.fst) eq fl) (bounded : pathBounds P hist d) :
    canonHint byte allow normal t d eq fl q = 0 := by
  simp only [canonHint]
  split
  · exact hs m hm _ _ _ (bounded m hm fixed)
  · let i := canonLane (byte (t+1))
    obtain ⟨π,sw,ord',same⟩ := extend_ordered ord i
    let n := moved m π sw
    have hn : P n := mov _ _ _ hm
    have pin : fixedHistory hist n := fixed_move fixed same
    have ff : flagsMatch n (hist.map Prod.fst) eq fl := flags_move flags same
    have inside := bounded n hn pin
    let cand := laneRead d i.val &&& allow eq fl (!(orientation i))
    have keep : cand.testBit (represented n i).val = true := by
      rw [show cand = _ &&& _ from rfl,Nat.testBit_and,Bool.and_eq_true]
      exact ⟨heldLane inside i,adm n i eq fl (accepted_order ff ord')⟩
    exact hs n hn _ _ _ (replaceGroup_sound inside i (Nat.and_le_left.trans_lt (low_lane d i.val)) keep)
def peelWord (d : ℕ) := Nat.land d (Nat.sub (Nat.lor d guardBits) allLanes)
def prioritizeFew (d : ℕ) :=
  Nat.xor guardBits (dirtyBits (peelWord (peelWord (peelWord (peelWord d)))))
def guidedPick (q cap tiny : ℕ) : Id :=
  let pref := Nat.land q tiny
  let avail := match Nat.beq pref 0 with | true => q | false => pref
  let before := Nat.land avail cap
  chooseSource (match Nat.beq before 0 with | true => avail | false => before)
def guidedLoop (step : ℕ → Id → ℕ) (pick : ℕ → ℕ → ℕ → Id) (changed : ℕ → ℕ)
    (dead : ℕ → Bool) (priority : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,d,_,_,_ => d
  | fuel+1,d,q,cap,tiny =>
    match Nat.beq q 0 with
    | true => d
    | false =>
      let i := pick q cap tiny
      let flag := Nat.shiftLeft 1 (Nat.add (Nat.mul 1025 i.val) 1024)
      let bound := Nat.sub flag 1
      let pending := Nat.xor q flag
      let del := Nat.land d (step d i)
      match Nat.beq del 0 with
      | true => guidedLoop step pick changed dead priority fuel d pending bound tiny
      | false =>
        let next := Nat.xor d del
        match dead next with
        | true => 0
        | false => guidedLoop step pick changed dead priority fuel next (Nat.lor pending (changed del)) bound (priority next)
def emptyGuided (d : ℕ) : Bool :=
  let empty := Nat.xor guardBits (dirtyBits d)
  !(Nat.beq empty 0) && Nat.beq (laneRead d (chooseSource empty).val) 0
lemma empty_pres {w : Valuation} {d : ℕ} (ok : insidePacked d w) : emptyGuided d = false := by
  cases hh : emptyGuided d with
  | false => rfl
  | true =>
    have ht := (Bool.and_eq_true_iff.mp hh).2
    have zero := Nat.eq_of_beq_eq_true ht
    have hit := heldLane ok (chooseSource (Nat.xor guardBits (dirtyBits d)))
    change (laneRead d _).testBit _ = true at hit
    rw [zero] at hit
    simp at hit
lemma guidedLoop_keeps {w : Valuation} {step : ℕ → Id → ℕ} (pick : ℕ → ℕ → ℕ → Id)
    (changed : ℕ → ℕ) (dead : ℕ → Bool) (priority : ℕ → ℕ)
    (pres : ∀ d, insidePacked d w → ∀ i, insidePacked (restrictPacked d (step d i)) w)
    (live : ∀ d, insidePacked d w → dead d = false)
    (fuel d q cap tiny : ℕ) (ok : insidePacked d w) : insidePacked (guidedLoop step pick changed dead priority fuel d q cap tiny) w := by
  induction fuel generalizing d q cap tiny with
  | zero => exact ok
  | succ fuel ih =>
    simp only [guidedLoop]
    split
    · exact ok
    · try dsimp only
      split
      · exact ih _ _ _ _ ok
      · try dsimp only
        have now := pres d ok (pick q cap tiny)
        rw [show dead (Nat.xor d (Nat.land d (step d (pick q cap tiny)))) = false from live _ now]
        exact ih _ _ _ _ now
def guidedSettle (p : ℕ → ℕ) (e d q : ℕ) :=
  guidedLoop (tightCut (denseChart e)) guidedPick dirtyBits emptyGuided p 400 d q 0 0
lemma guidedSettle_ok (p : ℕ → ℕ) {e : Fin 201} {w O R} (h : encLayout (modelNeg e) (modelPos e) w O R)
    (tested : ∀ m i j, testLink e m i j=true) (d q : ℕ) (ok : insidePacked d w) :
    insidePacked (guidedSettle p e d q) w := by
  apply guidedLoop_keeps _ _ _ _ _ (fun _ h => empty_pres h) _ _ _ _ _ ok
  intro val hv i
  rw [tightCut_eq,correctChart e,quickCut_eq]
  exact sourceCut_keep hv (hint_valid tested h) i
def sourceEventWordBlock (i : ℕ) : ℕ := (match Nat.blt i 2 with | true => (match Nat.blt i 1 with | true => 0x3bdb0a803ff7b8803f7f86800f7d0080000000000000000000000000000000003fb000802abcbff02ff083803fdd9bf01ef8bfb01d3ab9b0000000000ad6bcb02ed600802c73bfb0000000001f140080000000000000000002d0bc80000000003fb7ada03f7218802ffebdb008b2bc000000000000000000000000003f300080000000003fff3e80000000003f7f8e902fff82802fff80a000000000000000002f7fb4b01f3000800d2e8c80000000001bbebec03fffbdf02b1980803fffbfa02bff3fe02ffd20a0000000002b198880000000003fffbf803fbf01902bbf0f803fffbfc03fffb7e0393f02903f950080000000003faab8e03ffebaa02ef080803153004026f700403f773f50000000003ff7af4000000000000000003d7fbf502ff43cc02b8008c02fe000403dddabc03f74bb403d70b9403ff732602fd780402dd73d70291087f02ff6b47000000000000000002ff13fc02ed7bce0000000003f77bcf03fffbfe02d7b9c6029e69c400000000004703c1037fd19403fffbfc0000000003fff0340000000003f6432c02fe900402fe5bc40000000003fffbd402d67bd40000000002ff50240000000003ffdb6c03ffd35f03f7d9de02fec00403d66a5c02f710040089033f004440040000000003ffeb470269780403de402403fffbfc03d7780403d7680403fffbe70000000003fffbee03effb9e00000000000000000363a3ba03f6000203fe000203fffaf7000000000000000003d733fb03fffbfb03dfd9b2009a03e103dc400201fefb9e029303b003ff682603bd480203dffad303ff08af00d448ca01f1cbd700000000000000000000000003d7fbce02d73bcf03bd582603d2dbeb000000000000000003f7ebcf03ef43fa01d500320000000001d6e3fe0000000003f6000200068bd603b7ba0a0000000003d6a0220393fbd203ffebf701f1c8260000000003ffdbfe03f763f303ff8abe03f7ebfe03d7f3fe03ba43fe019be83e0393dbe20000000003bbfbea0000000003d660f203fffbee03ffbb7f0393238f0000000003ff5bcf03dbeb8e03ffebde03decbd703b923bb037f73a703f8500103fbdbf503ffdbff000000000000000000000000004702e502fbd3d100000000000000000000000002873b93029f33ef00bd7bdb03b902d103fd3bff006d03c901f54bd50000000002fb00cf02ed7bc90000000002936bdf03fffbcd02d7faf9029f7be10000000003ffe3c903ff43fb03f753ff0000000003ffc3fb00000000033713fd02fffaf102fffbdf0000000003ff48010000285102a3c0d103ff93f500000000037b8bf903f773f003fb800103fff3f502bbd0f103bb43ef0000000002f111430000000003f97be703fb03bb03bb636f03fffbfc03fbfbff03b98bdf03fb7ba303ff7bff03fbfb8b03fa200103f7dbd5 | false => 0x3bfb3f60000000002f3e23003efdbf803fff8d00000000000000000038ff9ad03fbb3f803bbebf700000000000000000000000000140b82029203e901f6da0800c921d1000000000000000001fdc3d50000000002bb03ee000000000281038c03ff7bdf03fffbdc02d76bc3029203fa0000000000000000033e81b802ffd3ee000000000000000000000000000000000000000002bed3ce00000000038ffb9003d3ebd90000000002b208800000000003aa08d003fff3f80097cbfe027f43fe03bffb9c00000000039ae08002ffdbe50000000003fffbfa03bffbe6039ec08003fffbfc03fffbff0191a3fa03ed334603fb83ef03fbfbae03f7e3ba0000000003bf73f603fff84003f378440000000000000000000000000000000003d013c003fff3e702ff7bce0000000003ff784003fffbff03d76bd80393704002d532c903ff2bf302813a590000000001e123d5000000000000000002ef68c80000000002fe8b5e0397b3f802dffbea000000000000000003ff63cd03ff50f803f2f3cc00000000024c43fc00000000000000000000000002ff7bd60000000003ba20e803d7dbd100000000000000000000000002f7007003f6f3f0026103fc03f7f3fd03baf0c00000000000000000000000000000000003fb7bf7026b4bcb0000000003fffbed03fffbff0397f84003fffbee03f7facd03fffbfe016fe3de000000000111b22201b373b603f7fa7c00000000002102e400000000000000000000000003fffb6802fff8200000000003fffaa903fffbe203d76bba03fff82202ed402002de426003fffbfa00f6402003f16bf50000000002ff587c02ed402003d3502002d76bff03fffaf203dfebe9000000000000000001f768200000000003ff7afc0000000003f7f87a0000000003f6e82002fff02802e7f0280000000003fff82202c67a2003fbf83002fbda3c000000000000000003f7fbf002338a2200f7e06003fefb6c000000000000000002ffdae70000000003fffa7000280bbb03df503403fffbec03fff27e03d7782003c7402003fffbff03fbfb7e03f7e07403ffe820039db3fe03f7f3b703ff4bd3031fd3f403ffdaf6000000000000000003dffbf503fffbfb03ffdbfe02ffdbb303fff89003fbf91303d6ab9b02ff7bd902bf581002dfd1d103ffe81002ff785203fdebd70000000002ff31340000000003d77bd402d76bff03fffbfc02d7caf0029f7bf80000000001f76bd803ffdbfa03ffebff00000000000000000000000000000000000000000000000000000000039ff3fa0252385003f7ebf5000000000000000003ffdbfc03fffbfd02b7dbf401b7ebf503ddfbfc039e8bd40000000002ffdbf70000000003fffbd403f77bff039f037203fffbfc03fffbdf03d7781003fd703803ff6b9b005258300257681000000000) | false => (match Nat.blt i 3 with | true => 0x1331b9202b3a83000000000000000000000000000000000000000000200084002884be5000000000000000001eb8bdf01d40bbb009a0b49000000000000000002d2080000b10bc30271ca15000000000000000000842bca02920800029048cb03ff7bfc03f7ebe3000000000000000002d208000000000002bb082400000000000000000000000000000000029a2b7e00a8abdc000000000000000000136bd10000000002bb0b3c000000000000000003478bf40237cbb602b7cbf70000000001c20bf40000000002901bf5000000000080bbc4000000000000000003fffbfc03de7b7e02000842000000000000000003f38bfe00000874028e0bd00390000003f0000003d0000003d00000039000000000000000000000039000000398000003f000000390000003b0000003d60000039100000390000003b0000003dc278303b75f9302f0000003f00000000000000291000002cc0000039000000390000003da6d4402d74fe3029020000000000003f000000390000003dacfc80000000003dc000000000000039000000392000003ec00000000000003b008000384000003f2000002e800000000000003f0000003f0000003f0000003f2000003900000039000000390000003f15fc40000000003f0200003f000000390000003d0000003920000039200000394000003f1000003d24f0003d200000390000003cffbb6000000000000000003fe9bf403d602040000000000000000038093e1020103e8037bebc500000000000000000000000000000000039023af03bf03cb00000000000000000000000003e1420000000000000000000000000000000000039003cf03ff7bcc0294eb00029f63c00000000000000000037b5b1002f0ebc80000000000000000000000000000000002ce8bf602af7b500000000003fffbd403d77bdb00000000000000000000000002b2130803f7fbf002b313e60000000002a05376000000000200037f03d9dbe50000000000000000000000000000000003ef6b0c03b753480282030b000000000000000003b9bb800000000003fecbf700000000000000000000000003efd91003f20100000000000000000003effbe5014803a10000000000000000000000000000000000000000000000000000000003ff03c6000000000000000001edcb95000000000000000000000000000000000000000003fffbdc0000000002bf7be80000000001f9a3c803ffdbfa03dbebe8000000000000000000000000000000000000000000000000000000000000000003da7b9a01e3cbd5000000000000000001ffdb9803fff3e000000000012403e003b7fb560000000000000000000000000000000003a9bbc7030013760000000003fffbfc01ffdb9e0000000003f7fbae0000000001399b8a03ff83aa00000000 | false => 0xa09af000000000000000000382bbd9005680a00080c08602bb83eb00000000008283d100000000000000000000000000000000000000000000000000000000000000000000000000000000020183cc0000000003f7abc802d3c3fb0000000000000000014583c8000000000000000000000000000000000000000000000000008683d0000683d20000000000000000000000000000a164006282d8000000000000000000a0d2a0008083e600000000009083e00000000000000000029483e5000000000110a380000000000004c0bb03fffbff03bffbff024081cb0107eb8a0001838b03ffeb8a0000000000000000000000000000000003f3ebf503efdbfc02d662f4000000000000000003567bf803da7bf80000000000000000021078000286c32003d66b9b00000000027ddbc902fff3e3000040740292405001f9cbd500000000000000000084634a0000000002d66bcf03bf7bfc03ff5be90000000000000000004743cd03d6c3fa00000000000000000392437800000000000000000092435802fe7bd40000000003fe7bfe0000000000000000026b528800000000022f73f8000000000000000003b66bff03dffbdc00000000000000000000000000000000001a4048000000000000000003fffbfc03907b7a000000000394400003f7584c03f8fb4c03f97bfe02f3d854000000000210380003f73bf400000000021123e40000000000000000021023e903fb73f800000000000000000000000000000000020428000000000000000000008923f100000000000000000000000000000000029223f802ef7bca020123cc02f73bc8000000000000000000000000000000000000000000000000000000000000000002cdf0720000000000000000000000000000000000000000009223fa03d67bd3022262fc0000000000000000003b23f0008032200000000000f4e2f402fab8e4000000000000000000000000000000000208239400000000029262fc03fffbff03befb7f0000000000000000029638480000000003f323fe0293384002017384000000000000000000000000000000000000000000000000000000000000000000c513a000a113e1000000000128138f00000000000000000000000000000000028510b40000000000000000000000000000000002fb584000000000020113cf03ff73de00101000000000000000000000000000037952d20265f35100000000039313e200000000031013e000ee9bf4000000000000000003a13bea03de7bdb0000000000000000000000000000000003b6b3f002111bdc02c47370022252740081104200000000024353e6000000000318dbf0000190740380535d00000000031913cf00000000014013a202ba13ec03ebfbcc03bf720c02de9bf5))
def sourceEventWord (i : ℕ) := Nat.land (Nat.shiftRight (sourceEventWordBlock (Nat.shiftRight i 8)) (Nat.shiftLeft (Nat.land i 255) 5)) 4294967295
def scheduleFlags (e q : ℕ) :=
  let p := match Nat.beq q guardBits with | true => 26 | false => (chooseSource q).val
  let k := Nat.land (Nat.lor (Nat.shiftLeft p 6) (Nat.land e 63)) 1023
  Nat.shiftLeft (denseSpread (sourceEventWord k)) 1024

def scheduledSettle (e t d q : ℕ) :=
  match Nat.blt (tapeByte t) 26 with
  | false => guidedSettle prioritizeFew e d q
  | true =>
    let allow := scheduleFlags e q
    guidedLoop (tightCut (denseChart e)) guidedPick (fun x => Nat.land (dirtyBits x) allow)
      emptyGuided prioritizeFew 400 d (Nat.land q allow) 0 0

lemma scheduledSettle_ok {e : Fin 201} {w O R} (h : encLayout (modelNeg e) (modelPos e) w O R)
    (tested : ∀ m i j, testLink e m i j=true) (t d q : ℕ) (ok : insidePacked d w) :
    insidePacked (scheduledSettle e t d q) w := by
  cases test : Nat.blt (tapeByte t) 26 with
  | false => simpa only [scheduledSettle,test] using guidedSettle_ok prioritizeFew h tested d q ok
  | true =>
    simp only [scheduledSettle,test]
    apply guidedLoop_keeps _ _ _ _ _ (fun _ h => empty_pres h) _ _ _ _ _ ok
    intro val hv i
    rw [tightCut_eq,correctChart e,quickCut_eq]
    exact sourceCut_keep hv (hint_valid tested h) i

def workLayer (e : ℕ) := wrapCanonHints (canonHint tapeByte canonDomainFast (proofHint tapeByte e)) (fun next s => layer tapeByte hiBit (scheduledSettle e s.1) (readLeafFast (modelPos e) tapeByte) canonDomainFast next s)
def workRoot (e : ℕ) : EvalState := (initialOffset e,actualStart e,30,31,guardBits)
def blockFieldBlock (i : ℕ) : ℕ := 0x32bcd9bc79c8001030b8eab6edc701082fbbfeb6a0c700102db3c4b223c701082cb6a0b1b0c700102ab07faf40c7001028af40ae22c7001026ae22ac96c7001823aab8a8a2c7001820a845a631c700181da631a42cc701101bac3da35ac7001019a2c09f78c70010179ed09d1dc70018149bf69a99c70018119a7f99bec700180e982f972fc700180b965e94f9c7001808943a933bc70110069d1d92e9c700100492e991a5c7010803b1b091a4c7010003bc798f7dc70010018ade8895c60108008cce86cec60100008f7d8610c600000086108357c30000008357814ec0000000814e7f0dbd0000007f0d7b16bc0000007b16771fbb000000771f735cb8000000735c6fe0b70000006fe06f5fb40000006f5f6e16b30000006e166d78b10000006d786c0eb00000006c0e6b80ae0000006b806a8bad0000006a8b679fa7000000679f65aea600000065ae62a6a100000062a661fea000000061fe61699e000000616960d49c00000060d4600d9b000000600d5dbd9a0000005dbd5c1c980000005c1c59319300000059315863920000005863579d90000000579d52688f0000005268514e8e000000514e4ffb8a0000004ffb4f9b850000004f9b4e96840000004e964e0f830000004e0f46f98200000046f9443181000000443142637f000000426341987e000000419841247d000000412440c87700000040c83efa760000003efa3e86750000003e863df0740000003df03d47710000003d473a706f0000003a7039fe6a00000039fe38ef6900000038ef38a96800000038a93794670000003794311366000000311330386200000030382d13600000002d132c9d5c0000002c9d2c375b0000002c372b905a0000002b902ae1580000002ae127105700000027102631560000002631254b55000000254b20c35200000020c31fb1510000001fb11ea0500000001ea01d7f4c0000001d7f1c984a0000001c981bb8490000001bb81b4d480000001b4d1acb460000001acb1a1e450000001a1e1902440000001902188343000000188317df3e00000017df17873b00000017871731370000001731166b36000000166b15d63300000015d61386320000001386130531000000130511db2e00000011db0ee92c0000000ee90989250000000989086e24000000086e082322000000082307891e0000000789072818000000072806a31600000006a3064712000000064705eb1100000005eb058410000000058405250d000000052502cd0c00000002cd01dd0a00000001dd016c09000000016c01030700000001030060060000000060000101
def blockField (i : ℕ) := Nat.land (Nat.shiftRight (blockFieldBlock (Nat.shiftRight i 7)) (Nat.shiftLeft (Nat.land i 127) 6)) 18446744073709551615
def blockMoveBlock (i : ℕ) : ℕ := 0x536b0740074014500700070013000540128005401240054053da12100540537a12100540535b121005401210054011100540103005401e40101405401e20101405401d01101405401c24101405401c11101405401014054010100540054000301d401d40
def blockMove (i : ℕ) := Nat.land (Nat.shiftRight (blockMoveBlock (Nat.shiftRight i 9)) (Nat.shiftLeft (Nat.land i 511) 4)) 65535
def pointerSaltBlock (i : ℕ) : ℕ := 0x200020000000201050106000011000d020100030200030000000000000003
def pointerSalt (i : ℕ) := Nat.land (Nat.shiftRight (pointerSaltBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
def pointerSlotBlock (i : ℕ) : ℕ := 0x51063b6d000000002414000039000000000036000000200000550000006a0900001169000c73002800003f00000047001c000000210002001200000000004f00000000000000000064005d0000005900000000004a2500442a00000000003d4c004822565808383300003a10000000350b00460e0018001e57006b53545000006500004e00000000005f002c230400005a00001a6600150f0000753200000000007200630000002926000000000d37270000000007011b450017000000006f0000000000130030001f49001d00000000006160052e000a0041003c00705c4000342d4b6200036c5e7468671600000000006e4331193e004252712b5b002f004d
def pointerSlot (i : ℕ) := Nat.land (Nat.shiftRight (pointerSlotBlock (Nat.shiftRight i 10)) (Nat.shiftLeft (Nat.land i 1023) 3)) 255
abbrev BlockId := Fin 118
def blockCase (i : BlockId) := blockField i.val &&& 255
def blockPointer (i : BlockId) := (blockField i.val >>> 8) &&& 65535
def blockEnd (i : BlockId) := (blockField i.val >>> 24) &&& 65535
def blockBase (i : BlockId) := (blockField i.val >>> 40) &&& 2047
def blockLength (i : BlockId) := Nat.land (Nat.shiftRight (blockField i.val) 51) 31
def blockFuel (i : BlockId) := 28-blockLength i
def selectRecord (t : ℕ) : Option BlockId :=
  let first := Nat.land (Nat.shiftRight (Nat.mul t 17857) 16) 31
  let second := Nat.shiftRight (Nat.mul t 50905) 16
  let key := Nat.land (Nat.add second (pointerSalt first)) 255
  let i : BlockId := ⟨Nat.mod (pointerSlot key) 118,Nat.mod_lt _ (by decide)⟩
  match Nat.beq (blockPointer i) t with
  | true => some i
  | false => none
abbrev TrailState := ℕ × ℕ × ℕ × ℕ
def replayMoves (e : ℕ) : ℕ → ℕ → TrailState → TrailState
  | 0,_,s => s
  | k+1,a,(D,eq,fl,q) =>
    let w := blockMove a
    let tag := w >>> 10
    let v := w &&& 1023
    let x := if tag < 11 then v else 1023-v
    let d := guidedSettle prioritizeFew e D q
    replayMoves e k (a+1) (replacePacked d tag (1 <<< v),eq &&& sameMark x,
      fl &&& freeMark x,1 <<< (1025*tag+1024))
def blockState (i : BlockId) : EvalState :=
  (blockPointer i,replayMoves (blockCase i) (blockLength i) (blockBase i)
    (actualStart (blockCase i),30,31,guardBits))
def genericTip {ι : Type} (pick : ℕ → Option ι) (grp left stop : ι → ℕ)
    (input : ι → EvalState) (e fuel : ℕ) (s : EvalState) : Option ℕ :=
  match pick s.1 with
  | none => none
  | some i => if grp i == e && left i == fuel && input i == s then some (stop i) else none
def tipFor := genericTip selectRecord blockCase blockFuel blockEnd blockState
lemma mixed_assisted_eq (f : (EvalState → ℕ) → EvalState → ℕ) (tip : ℕ → EvalState → Option ℕ)
    (checked : ∀ k s v, tip (k+1) s = some v →
      f (assisted f tip k) s = v ∨ f (play f k) s = v) (fuel : ℕ) :
    assisted f tip fuel = play f fuel := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    funext s
    simp only [assisted,play]
    cases hit : tip (k+1) s with
    | none => simp only [ih]
    | some v =>
      rcases checked k s v hit with h | h
      · exact (ih ▸ h).symm
      · exact h.symm
def nestedBlock (i : BlockId) := Nat.testBit (blockField i.val) 56
def checkBlock (i : BlockId) : Bool :=
  let e := blockCase i
  let k := blockFuel i-1
  if nestedBlock i then
    Nat.beq (workLayer e (assisted (workLayer e) (tipFor e) k) (blockState i)) (blockEnd i)
  else
    Nat.beq (workLayer e (play (workLayer e) k) (blockState i)) (blockEnd i)
lemma tableHit {ι : Type} (pick : ℕ → Option ι) (grp left stop : ι → ℕ) (input : ι → EvalState)
    {e k v : ℕ} {s : EvalState}
    (hit : genericTip pick grp left stop input e k s = some v) :
    ∃ i, grp i=e ∧ left i=k ∧ input i=s ∧ stop i=v := by
  unfold genericTip at hit
  cases hp : pick s.1 with
  | none => simp [hp] at hit
  | some i =>
    simp only [hp] at hit
    split at hit
    · rename_i ans
      obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp ans
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp x
      exact ⟨i,beq_iff_eq.mp a,beq_iff_eq.mp b,beq_iff_eq.mp y,Option.some.inj hit⟩
    · contradiction
lemma normalizedTip (all : ∀ i, checkBlock i = true) (e : ℕ) {k s v}
    (hit : tipFor e (k+1) s = some v) :
    workLayer e (assisted (workLayer e) (tipFor e) k) s = v ∨
      workLayer e (play (workLayer e) k) s = v := by
  obtain ⟨i,he,hf,hs,hv⟩ := tableHit selectRecord blockCase blockFuel blockEnd blockState
    (e := e) (k := k+1) (v := v) (s := s) hit
  have good := all i
  unfold checkBlock at good
  split at good
  · left
    have h := Nat.eq_of_beq_eq_true good
    simpa only [he,hf,hs,hv,Nat.add_sub_cancel] using h
  · right
    have h := Nat.eq_of_beq_eq_true good
    simpa only [he,hf,hs,hv,Nat.add_sub_cancel] using h
def checkRoot (e : EnvelopeId) : Bool :=
  (tipFor e.val 28 (workRoot e.val) == some (finalOffset e.val)) && (!(finalOffset e.val == 0))
lemma assisted_hit (f : (EvalState → ℕ) → EvalState → ℕ) {tip k s v} (h : tip (k+1) s = some v) :
    assisted f tip (k+1) s = v := by simp only [assisted,h]
lemma completeRun (all : ∀ i, checkBlock i = true) {e : EnvelopeId} (ok : checkRoot e = true) :
    play (workLayer e.val) 28 (workRoot e.val) ≠ 0 := by
  obtain ⟨raw,nz⟩ := Bool.and_eq_true_iff.mp ok
  have hit : tipFor e.val (27+1) (workRoot e.val) = some (finalOffset e.val) := beq_iff_eq.mp raw
  rw [←mixed_assisted_eq (workLayer e.val) (tipFor e.val) (fun _ _ _ => normalizedTip all e.val)]
  rw [assisted_hit (workLayer e.val) hit]
  exact beq_eq_false_iff_ne.mp (Bool.not_eq_true' _ |>.mp nz)
lemma cannotModel (e : EnvelopeId) (scan : play (workLayer e.val) 28 (workRoot e.val) ≠ 0)
    (net : ∀ m i j, testLink e.val m i j = true) : rejectsEnvelope e := by
  intro a b P env cap lh
  obtain ⟨m,hm⟩ := permitted_exists env cap lh
  apply scan
  rw [workLayer,canonWrappedPlay_spec]
  apply canonSearch_impossible (permittedWorld e.val (fsCode a) (fsCode b)) (fun _ π sw h => permitted_moves h π sw)
    (canonHint tapeByte canonDomainFast (proofHint tapeByte e.val)) (canonHint_safe (permittedWorld e.val (fsCode a) (fsCode b)) (fun _ π sw h => permitted_moves h π sw) tapeByte canonDomainFast (proofHint tapeByte e.val) (fun x hx t d q ok => by
      obtain ⟨out,refs,model⟩ := permitted_frame env hx
      exact proofHint_ok model net tapeByte t d q ok) fastCanon_ok)
    tapeByte hiBit _ _ _ (fuel := 28) (hist := []) (m := m)
  · intro x hx t d q ok
    obtain ⟨out,refs,model⟩ := permitted_frame env hx
    exact scheduledSettle_ok model net t d q ok
  · intro x hx d tag t ok
    obtain ⟨out,refs,model⟩ := permitted_frame env hx
    exact fastLeaf_safe model ok tapeByte tag t
  · exact fastCanon_ok
  · exact hm
  · simp [fixedHistory]
  · exact ⟨fun _ => le_rfl,fun _ _ _ => le_rfl⟩
  · exact flags_nil m
  · exact fun _ h _ => permitted_start env h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verifiedRoots : ∀ c : RouteId, checkRoot (mappedEnv c)=true := by decide +kernel
def indexedBlock (n : ℕ) := if h : n < 118 then checkBlock ⟨n,h⟩ else true
lemma eightChecks (f : ℕ → Bool) (a : ℕ)
    (h0 : f (a+0)=true)
    (h1 : f (a+1)=true)
    (h2 : f (a+2)=true)
    (h3 : f (a+3)=true)
    (h4 : f (a+4)=true)
    (h5 : f (a+5)=true)
    (h6 : f (a+6)=true)
    (h7 : f (a+7)=true)
    (k : Fin 8) : f (a+k.val)=true := by
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb0 : ∀ b : Fin 8, indexedBlock (0*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb1 : ∀ b : Fin 8, indexedBlock (1*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb2 : ∀ b : Fin 8, indexedBlock (2*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb3 : ∀ b : Fin 8, indexedBlock (3*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb4 : ∀ b : Fin 8, indexedBlock (4*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb5 : ∀ b : Fin 8, indexedBlock (5*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb6 : ∀ b : Fin 8, indexedBlock (6*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb7 : ∀ b : Fin 8, indexedBlock (7*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb8 : ∀ b : Fin 8, indexedBlock (8*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb9 : ∀ b : Fin 8, indexedBlock (9*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb10 : ∀ b : Fin 8, indexedBlock (10*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb11 : ∀ b : Fin 8, indexedBlock (11*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb12 : ∀ b : Fin 8, indexedBlock (12*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb13 : ∀ b : Fin 8, indexedBlock (13*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma gb14 : ∀ b : Fin 8, indexedBlock (14*8+b.val)=true := by
  apply eightChecks <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma verifiedBlocks (i : BlockId) : checkBlock i=true := by
  have groups (g : Fin 15) : ∀ b : Fin 8, indexedBlock (g.val*8+b.val)=true := by
    fin_cases g
    · exact gb0
    · exact gb1
    · exact gb2
    · exact gb3
    · exact gb4
    · exact gb5
    · exact gb6
    · exact gb7
    · exact gb8
    · exact gb9
    · exact gb10
    · exact gb11
    · exact gb12
    · exact gb13
    · exact gb14
  let g : Fin 15 := ⟨i.val/8,by have := i.isLt; change i.val < 118 at this; omega⟩
  let k : Fin 8 := ⟨i.val % 8,by omega⟩
  have eq : g.val*8+k.val = i.val := by dsimp [g,k]; omega
  have done := groups g k
  simpa only [eq,indexedBlock,dif_pos i.isLt] using done
lemma noPossibleLayout (A B : Finset V) (P : Feature → Slot → Prop)
    (dirty : ∃ r, present A B (rows r) none) (cap : capacity A B P) (h : layout A B P) : False :=
  dirDispatch dirChecks (fun c => cannotModel (mappedEnv c) (completeRun verifiedBlocks (verifiedRoots c)) (chosenNet c)) A B P dirty cap h
end PEqualNP.Outside.L_meta_905

theorem PEqualNP.Outside.L_meta_905 : ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
  ¬ (∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
    (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
    (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true)) := by
  rintro G rfl ⟨C,wf,small,bare,spec⟩
  exact PEqualNP.Outside.L_meta_905.reduce_problem PEqualNP.Outside.L_meta_905.noPossibleLayout C wf small bare spec
