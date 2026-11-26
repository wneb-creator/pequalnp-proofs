import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_9033

def boolGate (op x y : Bool) : Bool := if op then x && y else x || y

-- Two causal evaluations agreeing at the sole reader agree at every other wire.
-- Before that reader, the reader-agreement premise is vacuous.
lemma sole_reader_agreement
    {n k v : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j))) :
    ∀ i, i < n + k → i ≠ v →
      (n + p.val ≤ i → w₀ (n + p.val) = w₁ (n + p.val)) → w₀ i = w₁ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hiv hp
    by_cases hin : i < n
    · exact hraw i hin hiv
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      by_cases hjp : j = p
      · have hip : i = n + p.val := hij.trans (congrArg (fun q : Fin k => n + q.val) hjp)
        rw [hip]
        exact hp (by omega)
      · obtain ⟨hav, hbv⟩ := hsole j hjp
        have hea : w₀ (a j) = w₁ (a j) :=
          ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega) hav
            (fun h => hp (by have := ha j; omega))
        have heb : w₀ (b j) = w₁ (b j) :=
          ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega) hbv
            (fun h => hp (by have := hb j; omega))
        rw [hij, heval₀, heval₁, hea, heb]

-- An output change forces the sole reader's other input to the identity value.
lemma sole_reader_boundary
    {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hleft : a p = v) (hright : b p ≠ v)
    (hv₀ : w₀ v = false) (hv₁ : w₁ v = true)
    (hout : out < n + k) (houtv : out ≠ v) (hflip : w₀ out ≠ w₁ out) :
    w₀ (b p) = op p := by
  have hu : w₀ (b p) = w₁ (b p) :=
    sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      (b p) (by have := hb p; have := p.isLt; omega) hright
      (fun h => by have := hb p; omega)
  have hg : w₀ (n + p.val) ≠ w₁ (n + p.val) := by
    intro heq
    exact hflip (sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      out hout houtv (fun _ => heq))
  rw [heval₀, heval₁, hleft, hv₀, hv₁, ← hu] at hg
  cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [boolGate]

-- An absorbing other input makes the output insensitive to the solely read input.
lemma sole_reader_saturated
    {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hleft : a p = v) (hright : b p ≠ v)
    (hout : out < n + k) (houtv : out ≠ v) (hsat : w₀ (b p) ≠ op p) :
    w₀ out = w₁ out := by
  have hu : w₀ (b p) = w₁ (b p) :=
    sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      (b p) (by have := hb p; have := p.isLt; omega) hright
      (fun h => by have := hb p; omega)
  apply sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁ out hout houtv
  intro _
  rw [heval₀, heval₁, hleft, ← hu]
  cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [boolGate]

def crossed (a₀ b₀ a₁ b₁ : Bool) : Prop :=
  (a₀ = true ∧ b₀ = false ∧ a₁ = false ∧ b₁ = true) ∨
  (a₀ = false ∧ b₀ = true ∧ a₁ = true ∧ b₁ = false)

lemma boolGate_distributes (op merge a₀ b₀ a₁ b₁ : Bool)
    (h : op ≠ merge → ¬ crossed a₀ b₀ a₁ b₁) :
    boolGate op (boolGate merge a₀ a₁) (boolGate merge b₀ b₁) =
      boolGate merge (boolGate op a₀ b₀) (boolGate op a₁ b₁) := by
  cases op <;> cases merge <;> cases a₀ <;> cases b₀ <;> cases a₁ <;> cases b₁ <;>
    simp_all [boolGate, crossed]

-- Unless a gate crosses the two rows, evaluation preserves their union or intersection.
lemma causal_merge_agreement
    {n k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = boolGate merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = boolGate (op j) (wm (a j)) (wm (b j)))
    (hcross : ∀ j, op j ≠ merge → ¬ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j))) :
    ∀ i, i < n + k → wm i = boolGate merge (w₀ i) (w₁ i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · exact hraw i hin
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      have hea := ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega)
      have heb := ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega)
      rw [hij, hevalm, heval₀, heval₁, hea, heb]
      exact boolGate_distributes _ _ _ _ _ _ (hcross j)

-- A union accepted above two rejected rows forces an AND crossing; the dual forces OR.
lemma crossing_gate_exists
    {n k out : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = boolGate merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = boolGate (op j) (wm (a j)) (wm (b j)))
    (hout : out < n + k) (hflip : wm out ≠ boolGate merge (w₀ out) (w₁ out)) :
    ∃ j, op j ≠ merge ∧ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j)) := by
  by_contra h
  apply hflip
  apply causal_merge_agreement a b op merge w₀ w₁ wm ha hb hraw heval₀ heval₁ hevalm
    (fun j hop hc => h ⟨j, hop, hc⟩) out hout

def boundaryCube {r : Nat} (l u : Fin r → Bool) : Finset (Fin r → Bool) :=
  Finset.univ.filter (fun c => ∀ i, l i ≠ u i → c i = l i)

lemma boundaryCube_disjoint {r : Nat} (l₀ u₀ l₁ u₁ : Fin r → Bool)
    (h : ∃ i, crossed (l₀ i) (u₀ i) (l₁ i) (u₁ i)) :
    Disjoint (boundaryCube l₀ u₀) (boundaryCube l₁ u₁) := by
  apply Finset.disjoint_left.mpr
  intro c hc₀ hc₁
  have h₀ := (Finset.mem_filter.mp hc₀).2
  have h₁ := (Finset.mem_filter.mp hc₁).2
  obtain ⟨i, hi⟩ := h
  rcases hi with ⟨hl₀, hu₀, hl₁, hu₁⟩ | ⟨hl₀, hu₀, hl₁, hu₁⟩
  · have hc₀ := h₀ i (by simp [hl₀, hu₀])
    have hc₁ := h₁ i (by simp [hl₁, hu₁])
    simp_all
  · have hc₀ := h₀ i (by simp [hl₀, hu₀])
    have hc₁ := h₁ i (by simp [hl₁, hu₁])
    simp_all

lemma boundaryCube_card {r : Nat} (l u : Fin r → Bool) :
    (boundaryCube l u).card = 2 ^ ((Finset.univ.filter (fun i => l i = u i)).card) := by
  classical
  let e : {c : Fin r → Bool // ∀ i, l i ≠ u i → c i = l i} ≃
      ({i : Fin r // l i = u i} → Bool) :=
    { toFun := fun c i => c.val i.val
      invFun := fun f => ⟨fun i => if h : l i = u i then f ⟨i, h⟩ else l i,
        fun i h => by simp [h]⟩
      left_inv := by
        intro c
        apply Subtype.ext
        funext i
        by_cases h : l i = u i
        · simp [h]
        · simp [h, c.property i h]
      right_inv := by
        intro f
        funext i
        simp [i.property] }
  have he := Fintype.card_congr e
  simpa [Fintype.card_subtype, Fintype.card_fun, boundaryCube] using he

lemma boundaryCube_packing {m r : Nat} (l u : Fin m → Fin r → Bool)
    (h : ∀ i j, i ≠ j → ∃ g, crossed (l i g) (u i g) (l j g) (u j g)) :
    (∑ i : Fin m, 2 ^ ((Finset.univ.filter (fun g => l i g = u i g)).card)) ≤ 2 ^ r := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => boundaryCube (l i) (u i)) := by
    intro i _ j _ hij
    exact boundaryCube_disjoint _ _ _ _ (h i j hij)
  have hc := Finset.card_le_card
    (Finset.subset_univ ((Finset.univ : Finset (Fin m)).biUnion (fun i => boundaryCube (l i) (u i))))
  rw [Finset.card_biUnion hd] at hc
  simpa [boundaryCube_card, Fintype.card_fun] using hc

def coreHigh (s : Fin 32) : Nat :=
  (List.range 5).foldl (fun z i => if s.val.testBit i then z ||| ([74, 140, 272, 608, 896].getD i 0) else z) 0

def mateHighAllowance (v : Fin 3) : Nat := [24, 640, 80].getD v.val 0

def earliestMatePairs (v : Fin 3) : List (Nat × Nat) :=
  [[(1, 2), (1, 6), (1, 18), (1, 22), (2, 5), (2, 9), (2, 13), (6, 9)],
   [(2, 16), (2, 20), (2, 24), (2, 28), (3, 16), (3, 20), (8, 16), (8, 18), (8, 20), (8, 22), (9, 16), (9, 20), (10, 16), (10, 20), (11, 16), (11, 20)],
   [(1, 8), (1, 12), (1, 24), (1, 28), (3, 8), (3, 12), (5, 8), (7, 8)]].getD v.val []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma earliest_mate_classification : ∀ (v : Fin 3) (a b : Fin 32),
    a.val ≤ b.val → a.val &&& b.val = 0 →
    (coreHigh a &&& coreHigh b) ≠ 0 →
    (coreHigh a &&& coreHigh b) &&& mateHighAllowance v = (coreHigh a &&& coreHigh b) →
    (a.val, b.val) ∈ earliestMatePairs v := by
  decide +kernel

end PEqualNP.Outside.L_meta_9033
