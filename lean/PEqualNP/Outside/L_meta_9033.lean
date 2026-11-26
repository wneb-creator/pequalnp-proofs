import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

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

/- Counting distinct non-atom port values by their first occurrence. -/

def freshPorts {α : Type} [DecidableEq α] {m : Nat}
    (atoms : Finset α) (ports : Fin m → α) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ports i ∉ atoms ∧ ∀ j, j < i → ports j ≠ ports i)

lemma freshPorts_injective {α : Type} [DecidableEq α] {m : Nat}
    (atoms : Finset α) (ports : Fin m → α) :
    Set.InjOn ports (↑(freshPorts atoms ports) : Set (Fin m)) := by
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2.2
  have hj' := (Finset.mem_filter.mp hj).2.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hj' i hlt hij
  · exact hi' j hgt hij.symm

lemma freshPorts_card_le {α : Type} [DecidableEq α] {m : Nat}
    (atoms : Finset α) (ports : Fin m → α) :
    (freshPorts atoms ports).card ≤ ((Finset.univ.image ports) \ atoms).card := by
  have hinj := freshPorts_injective atoms ports
  calc
    (freshPorts atoms ports).card = ((freshPorts atoms ports).image ports).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((Finset.univ.image ports) \ atoms).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        (Finset.mem_filter.mp hi).2.1⟩

lemma port_cover_complete {α : Type} [DecidableEq α] {m budget : Nat}
    (atoms : Finset α) (ports : Fin m → α)
    (h : ((Finset.univ.image ports) \ atoms).card ≤ budget) :
    ∃ representatives : Finset (Fin m), representatives.card ≤ budget ∧
      ∀ i, ports i ∈ atoms ∨ (∃ j, j < i ∧ ports j = ports i) ∨ i ∈ representatives := by
  classical
  refine ⟨freshPorts atoms ports, (freshPorts_card_le atoms ports).trans h, ?_⟩
  intro i
  by_cases hatom : ports i ∈ atoms
  · exact Or.inl hatom
  · by_cases hearlier : ∃ j, j < i ∧ ports j = ports i
    · exact Or.inr (Or.inl hearlier)
    · right; right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hatom,
        fun j hj heq => hearlier ⟨j, hj, heq⟩⟩

lemma port_cover_sound {α : Type} [DecidableEq α] {m : Nat}
    (atoms : Finset α) (ports : Fin m → α) (representatives : Finset (Fin m))
    (h : ∀ i, ports i ∈ atoms ∨ (∃ j, j < i ∧ ports j = ports i) ∨ i ∈ representatives) :
    ((Finset.univ.image ports) \ atoms).card ≤ representatives.card := by
  have key : ∀ N, ∀ i : Fin m, i.val < N → ports i ∉ atoms →
      ∃ j ∈ representatives, ports j = ports i := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi hnot
      rcases h i with hatom | ⟨j, hji, heq⟩ | hrep
      · exact (hnot hatom).elim
      · have hj : j.val < i.val := hji
        obtain ⟨r, hr, hrj⟩ := ih j (by omega) (by rwa [heq])
        exact ⟨r, hr, hrj.trans heq⟩
      · exact ⟨i, hrep, rfl⟩
  calc
    ((Finset.univ.image ports) \ atoms).card ≤ (representatives.image ports).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨himage, hnot⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp himage
      obtain ⟨j, hj, heq⟩ := key (i.val + 1) i (by omega) hnot
      exact Finset.mem_image.mpr ⟨j, hj, heq⟩
    _ ≤ representatives.card := Finset.card_image_le

lemma three_atoms_covered : ∀ (g : Fin 3) (S T : Finset (Fin 3)),
    S.Nonempty → T.Nonempty → Disjoint S T →
    (g ∈ S → 2 ≤ S.card) → (g ∈ T → 2 ≤ T.card) →
    ∀ a : Fin 3, a = g ∨ a ∈ S ∨ a ∈ T := by
  decide +kernel

/- Causal cuts for reader-dependency arguments. -/

lemma causal_cut_agreement
    {n k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool) (blocked : Finset Nat)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ∉ blocked → w₀ i = w₁ i)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hcut : ∀ j, n + j.val ∉ blocked →
      (a j ∈ blocked ∨ b j ∈ blocked) → w₀ (n + j.val) = w₁ (n + j.val)) :
    ∀ i, i < n + k → i ∉ blocked → w₀ i = w₁ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hioutside
    by_cases hin : i < n
    · exact hraw i hin hioutside
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      by_cases hblocked : a j ∈ blocked ∨ b j ∈ blocked
      · rw [hij]
        exact hcut j (by simpa [← hij] using hioutside) hblocked
      · have haoutside : a j ∉ blocked := fun h => hblocked (Or.inl h)
        have hboutside : b j ∉ blocked := fun h => hblocked (Or.inr h)
        have hea : w₀ (a j) = w₁ (a j) :=
          ih (a j) (by simpa [← hij] using ha j)
            (by have := ha j; omega) haoutside
        have heb : w₀ (b j) = w₁ (b j) :=
          ih (b j) (by simpa [← hij] using hb j)
            (by have := hb j; omega) hboutside
        rw [hij, heval₀, heval₁, hea, heb]

lemma two_reader_dependency_agreement
    {n k v u : Nat} (p q : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → i ≠ u → w₀ i = w₁ i)
    (hsolev : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (hsoleu : ∀ j, j ≠ q → a j ≠ u ∧ b j ≠ u)
    (hsolep : ∀ j, j ≠ q → a j ≠ n + p.val ∧ b j ≠ n + p.val)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hq : w₀ (n + q.val) = w₁ (n + q.val)) :
    ∀ i, i < n + k → i ≠ v → i ≠ u → i ≠ n + p.val → w₀ i = w₁ i := by
  have hagree := causal_cut_agreement a b op w₀ w₁ ({v, u, n + p.val} : Finset Nat)
    ha hb (fun i hi hioutside => by
      apply hraw i hi
      · intro hiv
        subst i
        simp at hioutside
      · intro hiu
        subst i
        simp at hioutside) heval₀ heval₁ (by
      intro j hjoutside hsource
      by_cases hjq : j = q
      · simpa [hjq] using hq
      · have hjp : j ≠ p := by
          intro hjp
          subst j
          simp at hjoutside
        obtain ⟨hav, hbv⟩ := hsolev j hjp
        obtain ⟨hau, hbu⟩ := hsoleu j hjq
        obtain ⟨hap, hbp⟩ := hsolep j hjq
        rcases hsource with hsource | hsource
        · simp [hav, hau, hap] at hsource
        · simp [hbv, hbu, hbp] at hsource)
  intro i hi hiv hiu hip
  exact hagree i hi (by simp [hiv, hiu, hip])

/- Structural OR frontiers and a finite single-injection obstruction. -/

def orFrontierAtom {k : Nat} (n : Nat) (op isProtected : Fin k → Bool) (i : Nat) : Prop :=
  i < n ∨ ∃ j : Fin k, i = n + j.val ∧ (op j = true ∨ isProtected j = true)

lemma or_frontier_avoiding_exists
    {n k : Nat} (a b : Fin k → Nat) (op isProtected : Fin k → Bool)
    (blocked : Finset Nat)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (havoid : ∀ j, op j = false → isProtected j = false →
      a j ∉ blocked ∧ b j ∉ blocked) :
    ∀ i, i < n + k → i ∉ blocked →
      ∃ frontier : Finset Nat,
        frontier.Nonempty ∧
        (∀ x ∈ frontier, orFrontierAtom n op isProtected x) ∧
        (∀ x ∈ frontier, x ≤ i) ∧
        (¬ orFrontierAtom n op isProtected i → ∀ x ∈ frontier, x < i) ∧
        Disjoint frontier blocked ∧
        ∀ w : Nat → Bool,
          (∀ j, w (n + j.val) = boolGate (op j) (w (a j)) (w (b j))) →
          (w i = true ↔ ∃ x ∈ frontier, w x = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hioutside
    by_cases hatom : orFrontierAtom n op isProtected i
    · refine ⟨{i}, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have hxi : x = i := Finset.mem_singleton.mp hx
        simpa [hxi] using hatom
      · intro x hx
        have hxi : x = i := Finset.mem_singleton.mp hx
        exact hxi.le
      · intro hnot
        exact (hnot hatom).elim
      · apply Finset.disjoint_left.mpr
        intro x hx hblocked
        have hxi : x = i := Finset.mem_singleton.mp hx
        exact hioutside (hxi ▸ hblocked)
      · intro w heval
        simp
    · have hin : ¬ i < n := fun h => hatom (Or.inl h)
      let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      have hop : op j = false := by
        cases h : op j
        · rfl
        · exact (hatom (Or.inr ⟨j, hij, Or.inl h⟩)).elim
      have hprotected : isProtected j = false := by
        cases h : isProtected j
        · rfl
        · exact (hatom (Or.inr ⟨j, hij, Or.inr h⟩)).elim
      obtain ⟨haoutside, hboutside⟩ := havoid j hop hprotected
      obtain ⟨left, hleftne, hleftatom, hleftbound, _, hleftdisjoint, hleftsem⟩ :=
        ih (a j) (by simpa [← hij] using ha j)
          (by have := ha j; omega) haoutside
      obtain ⟨right, _, hrightatom, hrightbound, _, hrightdisjoint, hrightsem⟩ :=
        ih (b j) (by simpa [← hij] using hb j)
          (by have := hb j; omega) hboutside
      have hstrict : ∀ x ∈ left ∪ right, x < i := by
        intro x hx
        rcases Finset.mem_union.mp hx with hleft | hright
        · exact lt_of_le_of_lt (hleftbound x hleft) (by simpa [← hij] using ha j)
        · exact lt_of_le_of_lt (hrightbound x hright) (by simpa [← hij] using hb j)
      refine ⟨left ∪ right, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨x, hx⟩ := hleftne
        exact ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hleft | hright
        · exact hleftatom x hleft
        · exact hrightatom x hright
      · intro x hx
        exact (hstrict x hx).le
      · intro hnot x hx
        exact hstrict x hx
      · apply Finset.disjoint_left.mpr
        intro x hx hblocked
        rcases Finset.mem_union.mp hx with hleft | hright
        · exact Finset.disjoint_left.mp hleftdisjoint hleft hblocked
        · exact Finset.disjoint_left.mp hrightdisjoint hright hblocked
      · intro w heval
        have hsem := or_congr (hleftsem w heval) (hrightsem w heval)
        rw [hij, heval j]
        simpa [boolGate, hop, Finset.mem_union, or_and_right, exists_or] using hsem

lemma or_frontier_exists
    {n k : Nat} (a b : Fin k → Nat) (op isProtected : Fin k → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val) :
    ∀ i, i < n + k →
      ∃ frontier : Finset Nat,
        frontier.Nonempty ∧
        (∀ x ∈ frontier, orFrontierAtom n op isProtected x) ∧
        (∀ x ∈ frontier, x ≤ i) ∧
        (¬ orFrontierAtom n op isProtected i → ∀ x ∈ frontier, x < i) ∧
        ∀ w : Nat → Bool,
          (∀ j, w (n + j.val) = boolGate (op j) (w (a j)) (w (b j))) →
          (w i = true ↔ ∃ x ∈ frontier, w x = true) := by
  intro i hi
  obtain ⟨frontier, hnonempty, hatoms, hbound, hstrict, _, hsem⟩ :=
    or_frontier_avoiding_exists a b op isProtected ∅ ha hb (by simp) i hi (by simp)
  exact ⟨frontier, hnonempty, hatoms, hbound, hstrict, hsem⟩

def optimisticPort (row injection mask : Nat) : Bool :=
  decide (row &&& mask ≠ 0 ∨ injection &&& mask = injection)

def optimisticMiddleOutput (row injection : Nat) : Bool :=
  let h := optimisticPort row injection 88 && optimisticPort row injection 160
  let q := decide (row &&& 2 ≠ 0) || h || decide (injection &&& 2 = injection)
  (q && optimisticPort row injection 40) ||
    (optimisticPort row injection 16 && optimisticPort row injection 64)

lemma single_injection_obstruction : ∀ injection : Fin 256,
    injection.val ≠ 0 →
    optimisticMiddleOutput 64 injection.val = false ∨
      optimisticMiddleOutput 128 injection.val = false := by
  decide +kernel


-- Two different source wires either have different readers already, or share
-- a reader whose output has a second reader. Causality makes that reader new.
lemma two_sources_have_distinct_consumers
    {n k u v : Nat} (P : Finset (Fin k)) (a b : Fin k → Nat)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (huv : u ≠ v)
    (hu : ∃ j ∈ P, a j = u ∨ b j = u)
    (hv : ∃ j ∈ P, a j = v ∨ b j = v)
    (hpair : ∀ j ∈ P,
      ((a j = u ∧ b j = v) ∨ (a j = v ∧ b j = u)) →
      ∃ l ∈ P, a l = n + j.val ∨ b l = n + j.val) :
    ∃ j ∈ P, ∃ l ∈ P, j ≠ l := by
  obtain ⟨j, hj, hju⟩ := hu
  obtain ⟨l, hl, hlv⟩ := hv
  by_cases hjl : j = l
  · subst l
    have hpins : (a j = u ∧ b j = v) ∨ (a j = v ∧ b j = u) := by
      rcases hju with hau | hbu <;> rcases hlv with hav | hbv
      · exact False.elim (huv (hau.symm.trans hav))
      · exact Or.inl ⟨hau, hbv⟩
      · exact Or.inr ⟨hav, hbu⟩
      · exact False.elim (huv (hbu.symm.trans hbv))
    obtain ⟨m, hm, hreader⟩ := hpair j hj hpins
    refine ⟨j, hj, m, hm, ?_⟩
    intro hjm
    subst m
    rcases hreader with hread | hread
    · have := ha j
      omega
    · have := hb j
      omega
  · exact ⟨j, hj, l, hl, hjl⟩

lemma two_sources_require_two_consumers
    {n k u v : Nat} (P : Finset (Fin k)) (a b : Fin k → Nat)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (huv : u ≠ v)
    (hu : ∃ j ∈ P, a j = u ∨ b j = u)
    (hv : ∃ j ∈ P, a j = v ∨ b j = v)
    (hpair : ∀ j ∈ P,
      ((a j = u ∧ b j = v) ∨ (a j = v ∧ b j = u)) →
      ∃ l ∈ P, a l = n + j.val ∨ b l = n + j.val) :
    2 ≤ P.card := by
  obtain ⟨j, hj, l, hl, hjl⟩ :=
    two_sources_have_distinct_consumers P a b ha hb huv hu hv hpair
  have hsub : ({j, l} : Finset (Fin k)) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  simpa [hjl] using Finset.card_le_card hsub


def bcHNeighbors (i : Fin 5) : Nat := [20, 28, 11, 22, 11].getD i.val 0

def bcHRectValid (a b : Fin 32) : Prop :=
  a.val ≤ b.val ∧ a.val &&& b.val = 0 ∧
  (∀ i : Fin 5, a.val.testBit i.val = true →
    b.val &&& bcHNeighbors i = b.val) ∧
  ((a.val.testBit 1 && b.val.testBit 4) ||
    (a.val.testBit 4 && b.val.testBit 1) ||
    (a.val.testBit 3 && b.val.testBit 4) ||
    (a.val.testBit 4 && b.val.testBit 3)) = true

def bcHRectangles : List (Nat × Nat) :=
  [(2, 16), (2, 20), (2, 24), (2, 28), (3, 16), (3, 20), (8, 16), (8, 18), (8, 20), (8, 22), (9, 16), (9, 20), (10, 16), (10, 20), (11, 16), (11, 20)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_h_rectangle_complete : ∀ a b : Fin 32,
    bcHRectValid a b → (a.val, b.val) ∈ bcHRectangles := by
  unfold bcHRectValid
  decide +kernel

lemma bc_h_rectangle_count : bcHRectangles.length = 16 := by rfl



def bcCleanNeighbors (i : Fin 6) : Nat := [10, 41, 24, 23, 12, 2].getD i.val 0

def bcCleanRectValid (a b : Fin 64) : Prop :=
  a.val ≤ b.val ∧ a.val &&& b.val = 0 ∧
  (∀ i : Fin 6, a.val.testBit i.val = true →
    b.val &&& bcCleanNeighbors i = b.val)

def bcCleanRectangles : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (0, 20), (0, 21), (0, 22), (0, 23), (0, 24), (0, 25), (0, 26), (0, 27), (0, 28), (0, 29), (0, 30), (0, 31), (0, 32), (0, 33), (0, 34), (0, 35), (0, 36), (0, 37), (0, 38), (0, 39), (0, 40), (0, 41), (0, 42), (0, 43), (0, 44), (0, 45), (0, 46), (0, 47), (0, 48), (0, 49), (0, 50), (0, 51), (0, 52), (0, 53), (0, 54), (0, 55), (0, 56), (0, 57), (0, 58), (0, 59), (0, 60), (0, 61), (0, 62), (0, 63), (1, 2), (1, 8), (1, 10), (2, 8), (2, 9), (2, 32), (2, 33), (2, 40), (2, 41), (3, 8), (4, 8), (4, 16), (4, 24), (5, 8), (6, 8), (7, 8), (8, 16), (8, 17), (8, 18), (8, 19), (8, 20), (8, 21), (8, 22), (8, 23), (12, 16)]

def bcCleanNonemptyRectangles : List (Nat × Nat) :=
  [(1, 2), (1, 8), (1, 10), (2, 8), (2, 9), (2, 32), (2, 33), (2, 40), (2, 41), (3, 8), (4, 8), (4, 16), (4, 24), (5, 8), (6, 8), (7, 8), (8, 16), (8, 17), (8, 18), (8, 19), (8, 20), (8, 21), (8, 22), (8, 23), (12, 16)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_clean_rectangle_complete : ∀ a b : Fin 64,
    bcCleanRectValid a b → (a.val, b.val) ∈ bcCleanRectangles := by
  unfold bcCleanRectValid
  decide +kernel

lemma bc_clean_rectangle_count : bcCleanRectangles.length = 89 := by rfl
lemma bc_clean_nonempty_rectangle_count : bcCleanNonemptyRectangles.length = 25 := by rfl

lemma bc_clean_nonempty_filter :
    bcCleanNonemptyRectangles =
      bcCleanRectangles.filter (fun p => decide (p.1 ≠ 0)) := by
  decide +kernel

lemma bc_clean_nonempty_rectangle_complete (a b : Fin 64)
    (hv : bcCleanRectValid a b) (ha : a.val ≠ 0) :
    (a.val, b.val) ∈ bcCleanNonemptyRectangles := by
  rw [bc_clean_nonempty_filter]
  exact List.mem_filter.mpr ⟨bc_clean_rectangle_complete a b hv, by simpa using ha⟩


def bcHAt (i : Fin 16) : Nat × Nat := bcHRectangles.getD i.val (0, 0)
def bcCleanAt (i : Fin 89) : Nat × Nat := bcCleanRectangles.getD i.val (0, 0)
def bcNonemptyAt (i : Fin 25) : Nat × Nat := bcCleanNonemptyRectangles.getD i.val (0, 0)

def bcCrosses (a b i j : Nat) : Bool :=
  (a.testBit i && b.testBit j) || (a.testBit j && b.testBit i)

def bcResidualEdges (a b : Nat) : Nat :=
  (if bcCrosses a b 0 1 then 1 else 0) +
  (if bcCrosses a b 0 3 then 2 else 0) +
  (if bcCrosses a b 1 3 then 4 else 0) +
  (if bcCrosses a b 1 5 then 8 else 0) +
  (if bcCrosses a b 2 3 then 16 else 0) +
  (if bcCrosses a b 2 4 then 32 else 0) +
  (if bcCrosses a b 3 4 then 64 else 0)

def bcHEdges (i : Fin 16) : Nat :=
  [0, 16, 32, 48, 8, 28, 0, 32, 64, 96, 8, 76, 0, 80, 8, 92].getD i.val 0

def bcCleanEdges (i : Fin 89) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 6, 16, 32, 48, 18, 20, 22, 64, 66, 68, 70, 80, 82, 84, 86, 96].getD i.val 0

def bcNonemptyEdges (i : Fin 25) : Nat :=
  [1, 2, 3, 4, 5, 8, 9, 12, 13, 6, 16, 32, 48, 18, 20, 22, 64, 66, 68, 70, 80, 82, 84, 86, 96].getD i.val 0

def bcCoverTriples : List (Nat × Nat × Nat) :=
  [(2, 6, 23), (2, 8, 21), (2, 8, 23), (3, 6, 19), (3, 6, 23), (3, 8, 17), (3, 8, 19), (3, 8, 21), (3, 8, 23), (5, 2, 24), (7, 6, 23), (7, 8, 21), (7, 8, 23), (9, 6, 15), (9, 6, 23), (9, 8, 13), (9, 8, 15), (9, 8, 21), (9, 8, 23), (11, 2, 12), (15, 2, 11), (15, 2, 12), (15, 2, 24)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_h_edges_correct : ∀ i : Fin 16,
    bcResidualEdges (2 * (bcHAt i).1) (2 * (bcHAt i).2) = bcHEdges i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_clean_edges_correct : ∀ i : Fin 89,
    bcResidualEdges (bcCleanAt i).1 (bcCleanAt i).2 = bcCleanEdges i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_nonempty_edges_correct : ∀ i : Fin 25,
    bcResidualEdges (bcNonemptyAt i).1 (bcNonemptyAt i).2 = bcNonemptyEdges i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_h_one_clean_not_cover : ∀ (i : Fin 16) (j : Fin 89),
    bcHEdges i ||| bcCleanEdges j ≠ 127 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_clean_empty_edges : ∀ i : Fin 89,
    (bcCleanAt i).1 = 0 → bcCleanEdges i = 0 := by
  decide +kernel

lemma bc_covering_clean_nonempty (i : Fin 16) (j k : Fin 89)
    (h : bcHEdges i ||| bcCleanEdges j ||| bcCleanEdges k = 127) :
    (bcCleanAt j).1 ≠ 0 ∧ (bcCleanAt k).1 ≠ 0 := by
  constructor
  · intro hj
    have hj0 := bc_clean_empty_edges j hj
    exact bc_h_one_clean_not_cover i k (by simpa [hj0] using h)
  · intro hk
    have hk0 := bc_clean_empty_edges k hk
    exact bc_h_one_clean_not_cover i j (by simpa [hk0] using h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_nonempty_clean_index : ∀ i : Fin 89,
    (bcCleanAt i).1 ≠ 0 → ∃ j : Fin 25, bcNonemptyAt j = bcCleanAt i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_covering_triples_complete : ∀ (i : Fin 16) (j k : Fin 25),
    bcHEdges i ||| bcNonemptyEdges j ||| bcNonemptyEdges k = 127 →
    (i.val, j.val, k.val) ∈ bcCoverTriples ∨
      (i.val, k.val, j.val) ∈ bcCoverTriples := by
  decide +kernel

lemma bc_covering_triples_count : bcCoverTriples.length = 23 := by rfl


lemma bc_index_of_mem {α : Type} {xs : List α} {n : Nat}
    (hlen : xs.length = n) (fallback x : α) (hx : x ∈ xs) :
    ∃ i : Fin n, xs.getD i.val fallback = x := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hx
  refine ⟨⟨i, by omega⟩, ?_⟩
  exact (List.getElem_eq_getD (l := xs) (i := i) (h := hi) fallback).symm.trans heq

def bcRawAMasks : List Nat := [24, 25, 26, 27, 28, 29, 30, 31]
def bcRawCMasks : List Nat := [18, 19, 22, 23, 26, 27, 30, 31]

lemma bc_raw_a_complete : ∀ a : Fin 32,
    a.val &&& 24 = 24 → a.val ∈ bcRawAMasks := by
  decide +kernel

lemma bc_raw_c_complete : ∀ a : Fin 32,
    a.val &&& 18 = 18 → a.val ∈ bcRawCMasks := by
  decide +kernel

def bcCoverPorts (ta tc : Nat) (tr : Nat × Nat × Nat) : List Nat :=
  let h := bcHRectangles.getD tr.1 (0, 0)
  let c₁ := bcCleanNonemptyRectangles.getD tr.2.1 (0, 0)
  let c₂ := bcCleanNonemptyRectangles.getD tr.2.2 (0, 0)
  [2 * ta, 2 * tc, 2 * h.1, 2 * h.2, c₁.1, c₁.2, c₂.1, c₂.2]

def bcAllCovers : List (List Nat) :=
  bcRawAMasks.flatMap (fun ta => bcRawCMasks.flatMap (fun tc =>
    bcCoverTriples.map (bcCoverPorts ta tc)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_all_covers_count : bcAllCovers.length = 1472 := by
  decide +kernel

lemma bc_cover_ports_mem (ta tc : Nat) (tr : Nat × Nat × Nat)
    (ha : ta ∈ bcRawAMasks) (hc : tc ∈ bcRawCMasks)
    (ht : tr ∈ bcCoverTriples) : bcCoverPorts ta tc tr ∈ bcAllCovers := by
  simp only [bcAllCovers, List.mem_flatMap, List.mem_map]
  exact ⟨ta, ha, tc, hc, tr, ht, rfl⟩

lemma bc_cover_complete_of_members (ta tc hL hR a b c d : Nat)
    (hta : ta ∈ bcRawAMasks) (htc : tc ∈ bcRawCMasks)
    (hh : (hL, hR) ∈ bcHRectangles)
    (hab : (a, b) ∈ bcCleanRectangles) (hcd : (c, d) ∈ bcCleanRectangles)
    (hcover : bcResidualEdges (2 * hL) (2 * hR) |||
      bcResidualEdges a b ||| bcResidualEdges c d = 127) :
    [2 * ta, 2 * tc, 2 * hL, 2 * hR, a, b, c, d] ∈ bcAllCovers ∨
      [2 * ta, 2 * tc, 2 * hL, 2 * hR, c, d, a, b] ∈ bcAllCovers := by
  obtain ⟨i, hi⟩ := bc_index_of_mem (n := 16) (by rfl) (0, 0) (hL, hR) hh
  obtain ⟨j, hj⟩ := bc_index_of_mem (n := 89) (by rfl) (0, 0) (a, b) hab
  obtain ⟨k, hk⟩ := bc_index_of_mem (n := 89) (by rfl) (0, 0) (c, d) hcd
  change bcHAt i = (hL, hR) at hi
  change bcCleanAt j = (a, b) at hj
  change bcCleanAt k = (c, d) at hk
  have hidx : bcHEdges i ||| bcCleanEdges j ||| bcCleanEdges k = 127 := by
    rw [← bc_h_edges_correct i, ← bc_clean_edges_correct j, ← bc_clean_edges_correct k,
      hi, hj, hk]
    exact hcover
  obtain ⟨hjne, hkne⟩ := bc_covering_clean_nonempty i j k hidx
  obtain ⟨j', hj'⟩ := bc_nonempty_clean_index j hjne
  obtain ⟨k', hk'⟩ := bc_nonempty_clean_index k hkne
  have hnj : bcNonemptyAt j' = (a, b) := hj'.trans hj
  have hnk : bcNonemptyAt k' = (c, d) := hk'.trans hk
  have hncover : bcHEdges i ||| bcNonemptyEdges j' ||| bcNonemptyEdges k' = 127 := by
    rw [← bc_h_edges_correct i, ← bc_nonempty_edges_correct j',
      ← bc_nonempty_edges_correct k', hi, hnj, hnk]
    exact hcover
  rcases bc_covering_triples_complete i j' k' hncover with ht | ht
  · left
    have hm := bc_cover_ports_mem ta tc (i.val, j'.val, k'.val) hta htc ht
    change [2 * ta, 2 * tc, 2 * (bcHAt i).1, 2 * (bcHAt i).2,
      (bcNonemptyAt j').1, (bcNonemptyAt j').2,
      (bcNonemptyAt k').1, (bcNonemptyAt k').2] ∈ bcAllCovers at hm
    simpa only [hi, hnj, hnk] using hm
  · right
    have hm := bc_cover_ports_mem ta tc (i.val, k'.val, j'.val) hta htc ht
    change [2 * ta, 2 * tc, 2 * (bcHAt i).1, 2 * (bcHAt i).2,
      (bcNonemptyAt k').1, (bcNonemptyAt k').2,
      (bcNonemptyAt j').1, (bcNonemptyAt j').2] ∈ bcAllCovers at hm
    simpa only [hi, hnj, hnk] using hm

lemma bc_geometric_cover_complete
    (ta tc hL hR : Fin 32) (a b c d : Fin 64)
    (hta : ta.val &&& 24 = 24) (htc : tc.val &&& 18 = 18)
    (hh : bcHRectValid hL hR)
    (hab : bcCleanRectValid a b) (hcd : bcCleanRectValid c d)
    (hcover : bcResidualEdges (2 * hL.val) (2 * hR.val) |||
      bcResidualEdges a.val b.val ||| bcResidualEdges c.val d.val = 127) :
    [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ∈ bcAllCovers ∨
      [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
        c.val, d.val, a.val, b.val] ∈ bcAllCovers := by
  exact bc_cover_complete_of_members _ _ _ _ _ _ _ _
    (bc_raw_a_complete ta hta) (bc_raw_c_complete tc htc)
    (bc_h_rectangle_complete hL hR hh)
    (bc_clean_rectangle_complete a b hab) (bc_clean_rectangle_complete c d hcd) hcover

lemma port_functions_budget {α : Type} [DecidableEq α] {m budget : Nat}
    (atomWires paidWires : Finset Nat) (ports : Fin m → Nat) (values : Nat → α)
    (hpaid : paidWires.card ≤ budget)
    (hports : ∀ i, ports i ∈ atomWires ∨ ports i ∈ paidWires) :
    ((Finset.univ.image (fun i => values (ports i))) \ atomWires.image values).card ≤
      budget := by
  have hsub :
      ((Finset.univ.image (fun i => values (ports i))) \ atomWires.image values) ⊆
        paidWires.image values := by
    intro v hv
    obtain ⟨hport, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hport
    rcases hports i with ha | hp
    · exact False.elim (hnot (Finset.mem_image.mpr ⟨ports i, ha, rfl⟩))
    · exact Finset.mem_image.mpr ⟨ports i, hp, rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hpaid)

lemma port_cover_of_wire_budget {α : Type} [DecidableEq α] {m budget : Nat}
    (atomWires paidWires : Finset Nat) (ports : Fin m → Nat) (values : Nat → α)
    (hpaid : paidWires.card ≤ budget)
    (hports : ∀ i, ports i ∈ atomWires ∨ ports i ∈ paidWires) :
    ∃ representatives : Finset (Fin m), representatives.card ≤ budget ∧
      ∀ i, values (ports i) ∈ atomWires.image values ∨
        (∃ j, j < i ∧ values (ports j) = values (ports i)) ∨ i ∈ representatives := by
  exact port_cover_complete (atomWires.image values) (fun i => values (ports i))
    (port_functions_budget atomWires paidWires ports values hpaid hports)

def r2FrontierMask (S : Finset (Fin 3)) : Nat :=
  S.sum (fun i => 1 <<< i.val)

def r2CleanAllocations : List (Nat × Nat) :=
  [(1, 2), (1, 4), (1, 6), (2, 1), (2, 4), (2, 5),
    (3, 4), (4, 1), (4, 2), (4, 3), (5, 2), (6, 1)]

def r2Allocation (i : Fin 12) : Nat × Nat :=
  r2CleanAllocations.getD i.val (0, 0)

def r2Ready (mask : Nat) : Nat :=
  if mask &&& 4 ≠ 0 then 2 else if mask &&& 2 ≠ 0 then 1 else 0

lemma r2_frontier_mask_membership : ∀ (S : Finset (Fin 3)) (i : Fin 3),
    (r2FrontierMask S).testBit i.val = true ↔ i ∈ S := by
  decide +kernel

lemma r2_allocation_count : r2CleanAllocations.length = 12 := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
lemma r2_allocation_complete : ∀ (S T : Finset (Fin 3)),
    S.Nonempty → T.Nonempty → Disjoint S T →
    ∃ i : Fin 12, r2Allocation i = (r2FrontierMask S, r2FrontierMask T) := by
  decide +kernel

lemma r2_allocation_ready_distinct : ∀ i : Fin 12,
    r2Ready (r2Allocation i).1 ≠ r2Ready (r2Allocation i).2 := by
  decide +kernel

lemma frontiers_AC_disjoint {α : Type} (S T : Finset α) (negatives : Finset Nat)
    (value : α → Nat → Bool)
    (hdirty : ∀ wire ∈ S, ∃ row ∈ negatives, value wire row = true)
    (hA : ∀ wire ∈ S, ∀ row ∈ negatives,
      value wire row = true → row = 25 ∨ row = 37)
    (hC : ∀ wire ∈ T, ∀ row ∈ negatives,
      value wire row = true → row = 37 ∨ row = 76)
    (hpin : ∀ wire ∈ S, wire ∈ T → value wire 37 = value wire 32)
    (hzero : ∀ wire ∈ S, value wire 32 = false) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro wire hs ht
  obtain ⟨row, hrow, hv⟩ := hdirty wire hs
  have ha := hA wire hs row hrow hv
  have hc := hC wire ht row hrow hv
  have hr : row = 37 := by omega
  subst row
  rw [hpin wire hs ht, hzero wire hs] at hv
  cases hv

lemma frontiers_disjoint_of_disjoint_support {α β : Type}
    (S T : Finset α) (negatives allowedS allowedT : Finset β)
    (value : α → β → Bool) (hallowed : Disjoint allowedS allowedT)
    (hdirty : ∀ wire ∈ S, ∃ row ∈ negatives, value wire row = true)
    (hS : ∀ wire ∈ S, ∀ row ∈ negatives, value wire row = true → row ∈ allowedS)
    (hT : ∀ wire ∈ T, ∀ row ∈ negatives, value wire row = true → row ∈ allowedT) :
    Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro wire hs ht
  obtain ⟨row, hrow, hv⟩ := hdirty wire hs
  exact Finset.disjoint_left.mp hallowed (hS wire hs row hrow hv) (hT wire ht row hrow hv)

def bcUnionAtoms : Finset Nat := {0, 1, 2, 4, 8, 16, 32, 64, 128}

def bcUnionDecomposable (S : Finset Nat) (m : Nat) : Prop :=
  ∃ a ∈ S ∪ bcUnionAtoms, ∃ b ∈ S ∪ bcUnionAtoms,
    a < m ∧ b < m ∧ a ||| b = m

def bcUnionClosed (S : Finset Nat) : Prop :=
  ∀ m ∈ S, m ∈ bcUnionAtoms ∨ bcUnionDecomposable S m

def bcIndexedPorts (a c : Fin 8) (t : Fin 23) : List Nat :=
  bcCoverPorts (bcRawAMasks.getD a.val 0) (bcRawCMasks.getD c.val 0)
    (bcCoverTriples.getD t.val (0, 0, 0))

def bcRequiredFamily (ports : List Nat) : Finset Nat := ports.toFinset \ bcUnionAtoms

def bcFamily (a c : Fin 8) (t : Fin 23) : Finset Nat :=
  bcRequiredFamily (bcIndexedPorts a c t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_union_positive_control : bcUnionClosed {5, 40, 41, 44, 48} := by
  unfold bcUnionClosed bcUnionDecomposable bcUnionAtoms
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_family_cardinality : ∀ (a c : Fin 8) (t : Fin 23),
    (bcFamily a c t).card = 4 ∨ (bcFamily a c t).card = 5 ∨
      (bcFamily a c t).card = 6 := by
  decide +kernel

def bcUnionAtomList : List Nat := [0, 1, 2, 4, 8, 16, 32, 64, 128]

lemma bc_union_atom_list_eq : bcUnionAtomList.toFinset = bcUnionAtoms := by
  decide +kernel

def bcUnionCheck (L : List Nat) : Bool :=
  L.all (fun m => bcUnionAtomList.contains m ||
    (L ++ bcUnionAtomList).any (fun a =>
      (L ++ bcUnionAtomList).any (fun b => decide (a < m ∧ b < m ∧ a ||| b = m))))

lemma bc_union_check_spec (L : List Nat) :
    bcUnionCheck L = true ↔ bcUnionClosed L.toFinset := by
  simp only [bcUnionCheck, bcUnionClosed, bcUnionDecomposable,
    ← bc_union_atom_list_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq,
    List.mem_append, Finset.mem_union, List.mem_toFinset]

def bcRequiredList (ports : List Nat) : List Nat :=
  ports.filter (fun m => !(bcUnionAtomList.contains m))

lemma bc_required_list_eq (ports : List Nat) :
    (bcRequiredList ports).toFinset = bcRequiredFamily ports := by
  ext m
  simp [bcRequiredList, bcRequiredFamily, ← bc_union_atom_list_eq]

lemma bc_union_bool_positive_control : bcUnionCheck [5, 40, 41, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_0 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 0 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 0 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_1 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 1 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 1 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_2 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 2 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 2 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_3 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 3 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 3 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_4 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 4 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 4 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_5 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 5 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 5 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_6 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 6 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 6 c t)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_small_family_check_7 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 7 c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts 7 c t)) = false := by
  decide +kernel

lemma bc_small_family_check : ∀ (a c : Fin 8) (t : Fin 23),
    (bcFamily a c t).card ≤ 5 →
      bcUnionCheck (bcRequiredList (bcIndexedPorts a c t)) = false := by
  intro a
  fin_cases a
  · exact bc_small_family_check_0
  · exact bc_small_family_check_1
  · exact bc_small_family_check_2
  · exact bc_small_family_check_3
  · exact bc_small_family_check_4
  · exact bc_small_family_check_5
  · exact bc_small_family_check_6
  · exact bc_small_family_check_7

lemma bc_small_family_not_closed (a c : Fin 8) (t : Fin 23)
    (hc : (bcFamily a c t).card ≤ 5) : ¬ bcUnionClosed (bcFamily a c t) := by
  intro hclosed
  have htrue : bcUnionCheck (bcRequiredList (bcIndexedPorts a c t)) = true := by
    apply (bc_union_check_spec _).mpr
    rw [bc_required_list_eq]
    exact hclosed
  rw [bc_small_family_check a c t hc] at htrue
  cases htrue

def bcFourMasks : List (List Nat) :=
  [[5, 41, 44, 48], [5, 41, 44, 50], [5, 41, 44, 52], [5, 41, 44, 54], [5, 41, 44, 56], [5, 41, 44, 58], [5, 41, 44, 60], [5, 41, 44, 62], [7, 33, 44, 48], [7, 33, 44, 50], [7, 33, 44, 52], [7, 33, 44, 54], [7, 33, 44, 56], [7, 33, 44, 58], [7, 33, 44, 60], [7, 33, 44, 62], [7, 41, 44, 48], [7, 41, 44, 50], [7, 41, 44, 52], [7, 41, 44, 54], [7, 41, 44, 56], [7, 41, 44, 58], [7, 41, 44, 60], [7, 41, 44, 62], [10, 22, 40, 52], [10, 22, 40, 54], [10, 22, 40, 60], [10, 22, 40, 62], [17, 36, 41, 56], [17, 38, 41, 56], [17, 41, 44, 56], [17, 41, 46, 56], [17, 41, 52, 56], [17, 41, 54, 56], [17, 41, 56, 60], [17, 41, 56, 62], [19, 33, 36, 56], [19, 33, 38, 56], [19, 33, 44, 56], [19, 33, 46, 56], [19, 33, 52, 56], [19, 33, 54, 56], [19, 33, 56, 60], [19, 33, 56, 62], [19, 36, 41, 56], [19, 38, 41, 56], [19, 41, 44, 56], [19, 41, 46, 56], [19, 41, 52, 56], [19, 41, 54, 56], [19, 41, 56, 60], [19, 41, 56, 62], [21, 36, 41, 48], [21, 36, 41, 50], [21, 36, 41, 52], [21, 36, 41, 54], [21, 36, 41, 56], [21, 36, 41, 58], [21, 36, 41, 60], [21, 36, 41, 62], [21, 38, 41, 48], [21, 38, 41, 56], [21, 41, 44, 48], [21, 41, 44, 50], [21, 41, 44, 52], [21, 41, 44, 54], [21, 41, 44, 56], [21, 41, 44, 58], [21, 41, 44, 60], [21, 41, 44, 62], [21, 41, 46, 48], [21, 41, 46, 56], [21, 41, 48, 52], [21, 41, 48, 54], [21, 41, 48, 60], [21, 41, 48, 62], [21, 41, 52, 56], [21, 41, 54, 56], [21, 41, 56, 60], [21, 41, 56, 62], [23, 33, 36, 48], [23, 33, 36, 50], [23, 33, 36, 52], [23, 33, 36, 54], [23, 33, 36, 56], [23, 33, 36, 58], [23, 33, 36, 60], [23, 33, 36, 62], [23, 33, 38, 48], [23, 33, 38, 56], [23, 33, 44, 48], [23, 33, 44, 50], [23, 33, 44, 52], [23, 33, 44, 54], [23, 33, 44, 56], [23, 33, 44, 58], [23, 33, 44, 60], [23, 33, 44, 62], [23, 33, 46, 48], [23, 33, 46, 56], [23, 33, 48, 52], [23, 33, 48, 54], [23, 33, 48, 60], [23, 33, 48, 62], [23, 33, 52, 56], [23, 33, 54, 56], [23, 33, 56, 60], [23, 33, 56, 62], [23, 36, 41, 48], [23, 36, 41, 50], [23, 36, 41, 52], [23, 36, 41, 54], [23, 36, 41, 56], [23, 36, 41, 58], [23, 36, 41, 60], [23, 36, 41, 62], [23, 38, 41, 48], [23, 38, 41, 56], [23, 41, 44, 48], [23, 41, 44, 50], [23, 41, 44, 52], [23, 41, 44, 54], [23, 41, 44, 56], [23, 41, 44, 58], [23, 41, 44, 60], [23, 41, 44, 62], [23, 41, 46, 48], [23, 41, 46, 56], [23, 41, 48, 52], [23, 41, 48, 54], [23, 41, 48, 60], [23, 41, 48, 62], [23, 41, 52, 56], [23, 41, 54, 56], [23, 41, 56, 60], [23, 41, 56, 62]]

def bcFourIndexTable : List (List (List Nat)) :=
  [[[80, 52, 108, 0, 0, 0, 0, 0, 0, 0, 80, 52, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [88, 60, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [90, 62, 118, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 90, 0, 16, 62, 118, 0, 0, 0, 0], [98, 70, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [100, 72, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [101, 73, 129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [102, 74, 130, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [103, 75, 131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 53, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 91, 1, 17, 63, 119, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 54, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 92, 2, 18, 64, 120, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [100, 72, 128, 40, 104, 32, 48, 76, 132, 0, 82, 54, 110, 10, 92, 2, 18, 64, 120, 0, 24, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 55, 111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 93, 3, 19, 65, 121, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [101, 73, 129, 41, 105, 33, 49, 77, 133, 0, 83, 55, 111, 11, 93, 3, 19, 65, 121, 0, 25, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 36, 84, 28, 44, 56, 112, 0, 84, 56, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 37, 89, 29, 45, 61, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 38, 94, 30, 46, 66, 122, 0, 0, 0, 0, 12, 94, 4, 20, 66, 122, 0, 0, 0, 0], [0, 0, 0, 39, 99, 31, 47, 71, 127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 40, 104, 32, 48, 76, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 41, 105, 33, 49, 77, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 42, 106, 34, 50, 78, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 43, 107, 35, 51, 79, 135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 57, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 95, 5, 21, 67, 123, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86, 58, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 96, 6, 22, 68, 124, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [102, 74, 130, 42, 106, 34, 50, 78, 134, 0, 86, 58, 114, 14, 96, 6, 22, 68, 124, 0, 26, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 59, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 97, 7, 23, 69, 125, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [103, 75, 131, 43, 107, 35, 51, 79, 135, 0, 87, 59, 115, 15, 97, 7, 23, 69, 125, 0, 27, 0, 0]]]

def bcSurvivorFamilyIndices : List Nat := [0, 4, 6, 24, 25, 26, 27, 28, 30, 34]

def bcSurvivorCovers : List (List Nat) :=
  [[48, 44, 16, 44, 2, 41, 5, 8], [52, 52, 22, 40, 1, 10, 4, 16], [54, 54, 22, 40, 1, 10, 4, 16], [56, 36, 4, 56, 2, 41, 8, 17], [56, 44, 4, 56, 2, 41, 8, 17], [56, 44, 16, 44, 2, 41, 5, 8], [56, 60, 4, 56, 2, 41, 8, 17], [60, 44, 16, 44, 2, 41, 5, 8], [60, 60, 4, 56, 2, 41, 8, 17], [60, 60, 16, 44, 2, 41, 5, 8], [60, 60, 22, 40, 1, 10, 4, 16], [62, 62, 22, 40, 1, 10, 4, 16]]

def bcFourIndex (a c : Fin 8) (t : Fin 23) : Nat :=
  (((bcFourIndexTable.getD a.val []).getD c.val []).getD t.val 0)

def bcFourMaskAt (i : Fin 136) : List Nat := bcFourMasks.getD i.val []

lemma bc_four_masks_count : bcFourMasks.length = 136 := by rfl
lemma bc_survivor_covers_count : bcSurvivorCovers.length = 12 := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_0 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 0 c t).card = 4 → bcFourIndex 0 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 0 c t) []).toFinset = bcFamily 0 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_1 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 1 c t).card = 4 → bcFourIndex 1 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 1 c t) []).toFinset = bcFamily 1 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_2 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 2 c t).card = 4 → bcFourIndex 2 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 2 c t) []).toFinset = bcFamily 2 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_3 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 3 c t).card = 4 → bcFourIndex 3 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 3 c t) []).toFinset = bcFamily 3 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_4 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 4 c t).card = 4 → bcFourIndex 4 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 4 c t) []).toFinset = bcFamily 4 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_5 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 5 c t).card = 4 → bcFourIndex 5 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 5 c t) []).toFinset = bcFamily 5 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_6 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 6 c t).card = 4 → bcFourIndex 6 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 6 c t) []).toFinset = bcFamily 6 c t := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_family_lookup_7 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 7 c t).card = 4 → bcFourIndex 7 c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex 7 c t) []).toFinset = bcFamily 7 c t := by
  decide +kernel

lemma bc_four_family_lookup : ∀ (a c : Fin 8) (t : Fin 23),
    (bcFamily a c t).card = 4 → bcFourIndex a c t < 136 ∧
      (bcFourMasks.getD (bcFourIndex a c t) []).toFinset = bcFamily a c t := by
  intro a
  fin_cases a
  · exact bc_four_family_lookup_0
  · exact bc_four_family_lookup_1
  · exact bc_four_family_lookup_2
  · exact bc_four_family_lookup_3
  · exact bc_four_family_lookup_4
  · exact bc_four_family_lookup_5
  · exact bc_four_family_lookup_6
  · exact bc_four_family_lookup_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_0 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 0 c t).card = 4 →
      bcFourIndex 0 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 0 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_1 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 1 c t).card = 4 →
      bcFourIndex 1 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 1 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_2 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 2 c t).card = 4 →
      bcFourIndex 2 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 2 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_3 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 3 c t).card = 4 →
      bcFourIndex 3 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 3 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_4 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 4 c t).card = 4 →
      bcFourIndex 4 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 4 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_5 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 5 c t).card = 4 →
      bcFourIndex 5 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 5 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_6 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 6 c t).card = 4 →
      bcFourIndex 6 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 6 c t ∈ bcSurvivorCovers := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_survivor_cover_lookup_7 : ∀ (c : Fin 8) (t : Fin 23),
    (bcFamily 7 c t).card = 4 →
      bcFourIndex 7 c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts 7 c t ∈ bcSurvivorCovers := by
  decide +kernel

lemma bc_survivor_cover_lookup : ∀ (a c : Fin 8) (t : Fin 23),
    (bcFamily a c t).card = 4 → bcFourIndex a c t ∈ bcSurvivorFamilyIndices →
      bcIndexedPorts a c t ∈ bcSurvivorCovers := by
  intro a
  fin_cases a
  · exact bc_survivor_cover_lookup_0
  · exact bc_survivor_cover_lookup_1
  · exact bc_survivor_cover_lookup_2
  · exact bc_survivor_cover_lookup_3
  · exact bc_survivor_cover_lookup_4
  · exact bc_survivor_cover_lookup_5
  · exact bc_survivor_cover_lookup_6
  · exact bc_survivor_cover_lookup_7

def bcNoSmallUnionExtension (L : List Nat) : Bool :=
  (List.range 64).all (fun extra => !(bcUnionCheck (extra :: L)))

lemma bc_no_small_union_extension_spec (L : List Nat) :
    bcNoSmallUnionExtension L = true ↔
      ∀ extra : Fin 64, bcUnionCheck (extra.val :: L) = false := by
  constructor
  · intro h extra
    have hx := List.all_eq_true.mp h extra.val (List.mem_range.mpr extra.isLt)
    simpa using hx
  · intro h
    apply List.all_eq_true.mpr
    intro extra hx
    have he := h ⟨extra, List.mem_range.mp hx⟩
    simpa using he

lemma bc_union_closed_remove_large (S : Finset Nat) (extra : Nat)
    (hbound : ∀ m ∈ S, m ≤ extra)
    (hclosed : bcUnionClosed (insert extra S)) : bcUnionClosed S := by
  intro m hm
  rcases hclosed m (Finset.mem_insert_of_mem hm) with hatom | hdec
  · exact Or.inl hatom
  · right
    obtain ⟨a, ha, b, hb, ham, hbm, heq⟩ := hdec
    refine ⟨a, ?_, b, ?_, ham, hbm, heq⟩
    · rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_insert.mp ha with rfl | ha
        · have := hbound m hm
          omega
        · exact Finset.mem_union.mpr (Or.inl ha)
      · exact Finset.mem_union.mpr (Or.inr ha)
    · rcases Finset.mem_union.mp hb with hb | hb
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · have := hbound m hm
          omega
        · exact Finset.mem_union.mpr (Or.inl hb)
      · exact Finset.mem_union.mpr (Or.inr hb)

lemma bc_extra_below_64 (S : Finset Nat) (extra : Nat)
    (hbound : ∀ m ∈ S, m < 64) (hnot : ¬ bcUnionClosed S)
    (hclosed : bcUnionClosed (insert extra S)) : extra < 64 := by
  by_contra hn
  apply hnot
  apply bc_union_closed_remove_large S extra ?_ hclosed
  intro m hm
  have := hbound m hm
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_indexed_ports_bound : ∀ (a c : Fin 8) (t : Fin 23),
    (bcIndexedPorts a c t).all (fun m => decide (m < 64)) = true := by
  decide +kernel

lemma bc_family_masks_bound (a c : Fin 8) (t : Fin 23) :
    ∀ m ∈ bcFamily a c t, m < 64 := by
  intro m hm
  have hm' : m ∈ bcIndexedPorts a c t :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hm).1
  exact of_decide_eq_true (List.all_eq_true.mp (bc_indexed_ports_bound a c t) m hm')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_001 : bcNoSmallUnionExtension [5, 41, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_002 : bcNoSmallUnionExtension [5, 41, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_003 : bcNoSmallUnionExtension [5, 41, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_005 : bcNoSmallUnionExtension [5, 41, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_007 : bcNoSmallUnionExtension [5, 41, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_008 : bcNoSmallUnionExtension [7, 33, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_009 : bcNoSmallUnionExtension [7, 33, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_010 : bcNoSmallUnionExtension [7, 33, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_011 : bcNoSmallUnionExtension [7, 33, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_012 : bcNoSmallUnionExtension [7, 33, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_013 : bcNoSmallUnionExtension [7, 33, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_014 : bcNoSmallUnionExtension [7, 33, 44, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_015 : bcNoSmallUnionExtension [7, 33, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_016 : bcNoSmallUnionExtension [7, 41, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_017 : bcNoSmallUnionExtension [7, 41, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_018 : bcNoSmallUnionExtension [7, 41, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_019 : bcNoSmallUnionExtension [7, 41, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_020 : bcNoSmallUnionExtension [7, 41, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_021 : bcNoSmallUnionExtension [7, 41, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_022 : bcNoSmallUnionExtension [7, 41, 44, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_023 : bcNoSmallUnionExtension [7, 41, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_029 : bcNoSmallUnionExtension [17, 38, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_031 : bcNoSmallUnionExtension [17, 41, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_032 : bcNoSmallUnionExtension [17, 41, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_033 : bcNoSmallUnionExtension [17, 41, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_035 : bcNoSmallUnionExtension [17, 41, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_036 : bcNoSmallUnionExtension [19, 33, 36, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_037 : bcNoSmallUnionExtension [19, 33, 38, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_038 : bcNoSmallUnionExtension [19, 33, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_039 : bcNoSmallUnionExtension [19, 33, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_040 : bcNoSmallUnionExtension [19, 33, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_041 : bcNoSmallUnionExtension [19, 33, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_042 : bcNoSmallUnionExtension [19, 33, 56, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_043 : bcNoSmallUnionExtension [19, 33, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_044 : bcNoSmallUnionExtension [19, 36, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_045 : bcNoSmallUnionExtension [19, 38, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_046 : bcNoSmallUnionExtension [19, 41, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_047 : bcNoSmallUnionExtension [19, 41, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_048 : bcNoSmallUnionExtension [19, 41, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_049 : bcNoSmallUnionExtension [19, 41, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_050 : bcNoSmallUnionExtension [19, 41, 56, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_051 : bcNoSmallUnionExtension [19, 41, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_052 : bcNoSmallUnionExtension [21, 36, 41, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_053 : bcNoSmallUnionExtension [21, 36, 41, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_054 : bcNoSmallUnionExtension [21, 36, 41, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_055 : bcNoSmallUnionExtension [21, 36, 41, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_056 : bcNoSmallUnionExtension [21, 36, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_057 : bcNoSmallUnionExtension [21, 36, 41, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_058 : bcNoSmallUnionExtension [21, 36, 41, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_059 : bcNoSmallUnionExtension [21, 36, 41, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_060 : bcNoSmallUnionExtension [21, 38, 41, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_061 : bcNoSmallUnionExtension [21, 38, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_062 : bcNoSmallUnionExtension [21, 41, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_063 : bcNoSmallUnionExtension [21, 41, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_064 : bcNoSmallUnionExtension [21, 41, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_065 : bcNoSmallUnionExtension [21, 41, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_066 : bcNoSmallUnionExtension [21, 41, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_067 : bcNoSmallUnionExtension [21, 41, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_068 : bcNoSmallUnionExtension [21, 41, 44, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_069 : bcNoSmallUnionExtension [21, 41, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_070 : bcNoSmallUnionExtension [21, 41, 46, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_071 : bcNoSmallUnionExtension [21, 41, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_072 : bcNoSmallUnionExtension [21, 41, 48, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_073 : bcNoSmallUnionExtension [21, 41, 48, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_074 : bcNoSmallUnionExtension [21, 41, 48, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_075 : bcNoSmallUnionExtension [21, 41, 48, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_076 : bcNoSmallUnionExtension [21, 41, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_077 : bcNoSmallUnionExtension [21, 41, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_078 : bcNoSmallUnionExtension [21, 41, 56, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_079 : bcNoSmallUnionExtension [21, 41, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_080 : bcNoSmallUnionExtension [23, 33, 36, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_081 : bcNoSmallUnionExtension [23, 33, 36, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_082 : bcNoSmallUnionExtension [23, 33, 36, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_083 : bcNoSmallUnionExtension [23, 33, 36, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_084 : bcNoSmallUnionExtension [23, 33, 36, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_085 : bcNoSmallUnionExtension [23, 33, 36, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_086 : bcNoSmallUnionExtension [23, 33, 36, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_087 : bcNoSmallUnionExtension [23, 33, 36, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_088 : bcNoSmallUnionExtension [23, 33, 38, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_089 : bcNoSmallUnionExtension [23, 33, 38, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_090 : bcNoSmallUnionExtension [23, 33, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_091 : bcNoSmallUnionExtension [23, 33, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_092 : bcNoSmallUnionExtension [23, 33, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_093 : bcNoSmallUnionExtension [23, 33, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_094 : bcNoSmallUnionExtension [23, 33, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_095 : bcNoSmallUnionExtension [23, 33, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_096 : bcNoSmallUnionExtension [23, 33, 44, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_097 : bcNoSmallUnionExtension [23, 33, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_098 : bcNoSmallUnionExtension [23, 33, 46, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_099 : bcNoSmallUnionExtension [23, 33, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_100 : bcNoSmallUnionExtension [23, 33, 48, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_101 : bcNoSmallUnionExtension [23, 33, 48, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_102 : bcNoSmallUnionExtension [23, 33, 48, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_103 : bcNoSmallUnionExtension [23, 33, 48, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_104 : bcNoSmallUnionExtension [23, 33, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_105 : bcNoSmallUnionExtension [23, 33, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_106 : bcNoSmallUnionExtension [23, 33, 56, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_107 : bcNoSmallUnionExtension [23, 33, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_108 : bcNoSmallUnionExtension [23, 36, 41, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_109 : bcNoSmallUnionExtension [23, 36, 41, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_110 : bcNoSmallUnionExtension [23, 36, 41, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_111 : bcNoSmallUnionExtension [23, 36, 41, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_112 : bcNoSmallUnionExtension [23, 36, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_113 : bcNoSmallUnionExtension [23, 36, 41, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_114 : bcNoSmallUnionExtension [23, 36, 41, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_115 : bcNoSmallUnionExtension [23, 36, 41, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_116 : bcNoSmallUnionExtension [23, 38, 41, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_117 : bcNoSmallUnionExtension [23, 38, 41, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_118 : bcNoSmallUnionExtension [23, 41, 44, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_119 : bcNoSmallUnionExtension [23, 41, 44, 50] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_120 : bcNoSmallUnionExtension [23, 41, 44, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_121 : bcNoSmallUnionExtension [23, 41, 44, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_122 : bcNoSmallUnionExtension [23, 41, 44, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_123 : bcNoSmallUnionExtension [23, 41, 44, 58] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_124 : bcNoSmallUnionExtension [23, 41, 44, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_125 : bcNoSmallUnionExtension [23, 41, 44, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_126 : bcNoSmallUnionExtension [23, 41, 46, 48] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_127 : bcNoSmallUnionExtension [23, 41, 46, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_128 : bcNoSmallUnionExtension [23, 41, 48, 52] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_129 : bcNoSmallUnionExtension [23, 41, 48, 54] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_130 : bcNoSmallUnionExtension [23, 41, 48, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_131 : bcNoSmallUnionExtension [23, 41, 48, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_132 : bcNoSmallUnionExtension [23, 41, 52, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_133 : bcNoSmallUnionExtension [23, 41, 54, 56] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_134 : bcNoSmallUnionExtension [23, 41, 56, 60] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_reject_135 : bcNoSmallUnionExtension [23, 41, 56, 62] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_four_extra_cases (i : Fin 136) :
    i.val ∈ bcSurvivorFamilyIndices ∨
      ∀ extra : Fin 64, bcUnionCheck (extra.val :: bcFourMaskAt i) = false := by
  fin_cases i
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_001
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_002
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_003
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_005
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_007
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_008
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_009
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_010
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_011
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_012
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_013
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_014
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_015
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_016
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_017
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_018
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_019
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_020
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_021
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_022
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_023
  · left
    decide +kernel
  · left
    decide +kernel
  · left
    decide +kernel
  · left
    decide +kernel
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_029
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_031
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_032
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_033
  · left
    decide +kernel
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_035
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_036
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_037
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_038
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_039
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_040
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_041
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_042
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_043
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_044
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_045
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_046
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_047
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_048
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_049
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_050
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_051
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_052
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_053
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_054
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_055
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_056
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_057
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_058
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_059
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_060
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_061
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_062
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_063
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_064
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_065
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_066
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_067
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_068
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_069
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_070
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_071
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_072
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_073
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_074
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_075
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_076
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_077
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_078
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_079
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_080
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_081
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_082
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_083
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_084
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_085
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_086
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_087
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_088
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_089
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_090
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_091
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_092
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_093
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_094
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_095
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_096
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_097
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_098
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_099
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_100
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_101
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_102
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_103
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_104
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_105
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_106
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_107
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_108
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_109
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_110
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_111
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_112
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_113
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_114
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_115
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_116
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_117
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_118
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_119
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_120
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_121
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_122
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_123
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_124
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_125
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_126
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_127
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_128
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_129
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_130
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_131
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_132
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_133
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_134
  · right
    exact (bc_no_small_union_extension_spec _).mp bc_four_extra_reject_135

lemma bc_card_four_extension_cover (a c : Fin 8) (t : Fin 23)
    (hcard : (bcFamily a c t).card = 4) (extra : Fin 256)
    (hclosed : bcUnionClosed (insert extra.val (bcFamily a c t))) :
    bcIndexedPorts a c t ∈ bcSurvivorCovers := by
  have hextra := bc_extra_below_64 (bcFamily a c t) extra.val
    (bc_family_masks_bound a c t)
    (bc_small_family_not_closed a c t (by omega)) hclosed
  let smallExtra : Fin 64 := ⟨extra.val, hextra⟩
  obtain ⟨hbound, heq⟩ := bc_four_family_lookup a c t hcard
  let i : Fin 136 := ⟨bcFourIndex a c t, hbound⟩
  have hi : (bcFourMaskAt i).toFinset = bcFamily a c t := heq
  have htrue : bcUnionCheck (smallExtra.val :: bcFourMaskAt i) = true := by
    apply (bc_union_check_spec _).mpr
    rw [List.toFinset_cons, hi]
    exact hclosed
  rcases bc_four_extra_cases i with hsurv | hbad
  · exact bc_survivor_cover_lookup a c t hcard hsurv
  · rw [hbad smallExtra] at htrue
    cases htrue


lemma bc_subset_one_extra (F S : Finset Nat) (hsub : F ⊆ S)
    (hcard : S.card ≤ F.card + 1) : ∃ extra, S ⊆ insert extra F := by
  have hdiff : (S \ F).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  by_cases hnonempty : (S \ F).Nonempty
  · obtain ⟨extra, hextra⟩ := hnonempty
    refine ⟨extra, ?_⟩
    intro x hx
    by_cases hxf : x ∈ F
    · exact Finset.mem_insert_of_mem hxf
    · have hxs : x ∈ S \ F := Finset.mem_sdiff.mpr ⟨hx, hxf⟩
      exact Finset.mem_insert.mpr (Or.inl ((Finset.card_le_one.mp hdiff) x hxs extra hextra))
  · refine ⟨0, ?_⟩
    intro x hx
    have hxf : x ∈ F := by
      by_contra hxf
      exact hnonempty ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxf⟩⟩
    exact Finset.mem_insert_of_mem hxf

lemma bc_subset_equal_at_budget (F S : Finset Nat) (hsub : F ⊆ S)
    (hcard : S.card ≤ F.card) : S = F :=
  (Finset.eq_of_subset_of_card_le hsub hcard).symm

lemma bc_equal_one_extra (F S : Finset Nat) (hsub : F ⊆ S)
    (hF : F.Nonempty) (hcard : S.card ≤ F.card + 1) :
    ∃ extra ∈ S, S = insert extra F := by
  obtain ⟨extra, hext⟩ := bc_subset_one_extra F S hsub hcard
  by_cases he : extra ∈ S
  · exact ⟨extra, he, Finset.Subset.antisymm hext (Finset.insert_subset he hsub)⟩
  · have hSF : S ⊆ F := by
      intro x hx
      rcases Finset.mem_insert.mp (hext hx) with rfl | hxf
      · exact False.elim (he hx)
      · exact hxf
    obtain ⟨f, hf⟩ := hF
    refine ⟨f, hsub hf, ?_⟩
    simpa only [Finset.insert_eq_of_mem hf] using Finset.Subset.antisymm hSF hsub


lemma bc_closed_production_classification (a c : Fin 8) (t : Fin 23)
    (S : Finset Nat) (hsub : bcFamily a c t ⊆ S) (hcard : S.card ≤ 5)
    (hbound : ∀ m ∈ S, m < 256) (hclosed : bcUnionClosed S) :
    bcIndexedPorts a c t ∈ bcSurvivorCovers := by
  rcases bc_family_cardinality a c t with hfour | hfive | hsix
  · have hnonempty : (bcFamily a c t).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨extra, hextra, heq⟩ := bc_equal_one_extra (bcFamily a c t) S hsub
      hnonempty (by omega)
    apply bc_card_four_extension_cover a c t hfour ⟨extra, hbound extra hextra⟩
    rw [← heq]
    exact hclosed
  · have heq : S = bcFamily a c t :=
      bc_subset_equal_at_budget (bcFamily a c t) S hsub (by omega)
    exact False.elim (bc_small_family_not_closed a c t (by omega) (heq ▸ hclosed))
  · have hle := Finset.card_le_card hsub
    omega

lemma bc_all_cover_index (ports : List Nat) (hp : ports ∈ bcAllCovers) :
    ∃ (a c : Fin 8) (t : Fin 23), bcIndexedPorts a c t = ports := by
  simp only [bcAllCovers, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨ta, hta, tc, htc, tr, htr, heq⟩ := hp
  obtain ⟨a, ha⟩ := bc_index_of_mem (n := 8) (by rfl) 0 ta hta
  obtain ⟨c, hc⟩ := bc_index_of_mem (n := 8) (by rfl) 0 tc htc
  obtain ⟨t, ht⟩ := bc_index_of_mem (n := 23) (by rfl) (0, 0, 0) tr htr
  refine ⟨a, c, t, ?_⟩
  unfold bcIndexedPorts
  rw [ha, hc, ht]
  exact heq

lemma bc_all_cover_closed_production (ports : List Nat) (hp : ports ∈ bcAllCovers)
    (S : Finset Nat) (hsub : bcRequiredFamily ports ⊆ S) (hcard : S.card ≤ 5)
    (hbound : ∀ m ∈ S, m < 256) (hclosed : bcUnionClosed S) :
    ports ∈ bcSurvivorCovers := by
  obtain ⟨a, c, t, rfl⟩ := bc_all_cover_index ports hp
  exact bc_closed_production_classification a c t S hsub hcard hbound hclosed

def bcCofactorPort (mask row : Nat) (h : Bool) : Bool :=
  decide (row &&& mask ≠ 0) || (decide (mask &&& 1 ≠ 0) && h)

def bcCofactorOutput (ports : List Nat) (row : Nat) : Bool :=
  let h := decide (row &&& ports.getD 2 0 ≠ 0) &&
    decide (row &&& ports.getD 3 0 ≠ 0)
  (bcCofactorPort (ports.getD 4 0) row h &&
    bcCofactorPort (ports.getD 5 0) row h) ||
  (bcCofactorPort (ports.getD 6 0) row h &&
    bcCofactorPort (ports.getD 7 0) row h)

def bcMiddleCovers : List (List Nat) :=
  [[52, 52, 22, 40, 1, 10, 4, 16],
   [54, 54, 22, 40, 1, 10, 4, 16],
   [60, 60, 22, 40, 1, 10, 4, 16],
   [62, 62, 22, 40, 1, 10, 4, 16]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_survivor_cofactor_classification : ∀ ports ∈ bcSurvivorCovers,
    bcCofactorOutput ports 20 = true → ports ∈ bcMiddleCovers := by
  decide +kernel

lemma bc_middle_cover_shape (ports : List Nat) (hp : ports ∈ bcMiddleCovers) :
    ∃ W ∈ [52, 54, 60, 62], ports = [W, W, 22, 40, 1, 10, 4, 16] := by
  simp only [bcMiddleCovers, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨52, by simp, rfl⟩
  · exact ⟨54, by simp, rfl⟩
  · exact ⟨60, by simp, rfl⟩
  · exact ⟨62, by simp, rfl⟩

lemma bc_required_family_clean_swap (ta tc hL hR a b c d : Nat) :
    bcRequiredFamily [ta, tc, hL, hR, a, b, c, d] =
      bcRequiredFamily [ta, tc, hL, hR, c, d, a, b] := by
  ext m
  simp only [bcRequiredFamily, Finset.mem_sdiff, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false]
  simp only [or_assoc, or_left_comm, or_comm]

lemma bc_geometric_closed_production
    (ta tc hL hR : Fin 32) (a b c d : Fin 64)
    (hta : ta.val &&& 24 = 24) (htc : tc.val &&& 18 = 18)
    (hh : bcHRectValid hL hR)
    (hab : bcCleanRectValid a b) (hcd : bcCleanRectValid c d)
    (hcover : bcResidualEdges (2 * hL.val) (2 * hR.val) |||
      bcResidualEdges a.val b.val ||| bcResidualEdges c.val d.val = 127)
    (S : Finset Nat)
    (hsub : bcRequiredFamily [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ⊆ S)
    (hcard : S.card ≤ 5) (hbound : ∀ m ∈ S, m < 256)
    (hclosed : bcUnionClosed S) :
    [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ∈ bcSurvivorCovers ∨
      [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
        c.val, d.val, a.val, b.val] ∈ bcSurvivorCovers := by
  rcases bc_geometric_cover_complete ta tc hL hR a b c d hta htc hh hab hcd hcover
    with hp | hp
  · exact Or.inl (bc_all_cover_closed_production _ hp S hsub hcard hbound hclosed)
  · right
    apply bc_all_cover_closed_production _ hp S ?_ hcard hbound hclosed
    rw [← bc_required_family_clean_swap]
    exact hsub

lemma bc_cofactor_clean_swap (ta tc hL hR a b c d row : Nat) :
    bcCofactorOutput [ta, tc, hL, hR, a, b, c, d] row =
      bcCofactorOutput [ta, tc, hL, hR, c, d, a, b] row := by
  simp [bcCofactorOutput, Bool.or_comm]

lemma bc_geometric_closed_cofactor
    (ta tc hL hR : Fin 32) (a b c d : Fin 64)
    (hta : ta.val &&& 24 = 24) (htc : tc.val &&& 18 = 18)
    (hh : bcHRectValid hL hR)
    (hab : bcCleanRectValid a b) (hcd : bcCleanRectValid c d)
    (hcover : bcResidualEdges (2 * hL.val) (2 * hR.val) |||
      bcResidualEdges a.val b.val ||| bcResidualEdges c.val d.val = 127)
    (S : Finset Nat)
    (hsub : bcRequiredFamily [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ⊆ S)
    (hcard : S.card ≤ 5) (hbound : ∀ m ∈ S, m < 256)
    (hclosed : bcUnionClosed S)
    (hEG : bcCofactorOutput [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] 20 = true) :
    [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ∈ bcMiddleCovers ∨
      [2 * ta.val, 2 * tc.val, 2 * hL.val, 2 * hR.val,
        c.val, d.val, a.val, b.val] ∈ bcMiddleCovers := by
  rcases bc_geometric_closed_production ta tc hL hR a b c d hta htc hh hab hcd hcover
    S hsub hcard hbound hclosed with hp | hp
  · exact Or.inl (bc_survivor_cofactor_classification _ hp hEG)
  · right
    apply bc_survivor_cofactor_classification _ hp
    rw [← bc_cofactor_clean_swap]
    exact hEG

namespace R2CleanKernel




def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)


def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)


def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

lemma bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

lemma bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]


def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)


def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true


def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

lemma litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl




abbrev Trie := BinaryTree (Option Nat)

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  BinaryTree.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := BinaryTree.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t


def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel


def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

lemma All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (Trie.get r _) (Trie.get l _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

lemma All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

lemma All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

lemma All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

lemma All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie



lemma bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

lemma bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

lemma bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

lemma bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]




def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

lemma bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩




abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool




def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))


def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))


def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))


def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)


def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode


def stop : Cont := fun _ _ _ _ _ _ => false


def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks


def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w


def fuelW : Nat := 1024


def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words


def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e


def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B


def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))


def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))


def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0


def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0


def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0


def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0


def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0



section Soundness

variable (a : Nat → Bool)


def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true


def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false


def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail


def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)


lemma witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩


def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

lemma stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

lemma tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    ·
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    ·
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

lemma runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

lemma runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

lemma runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

lemma clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

lemma maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

lemma verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

lemma loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

lemma loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness


lemma check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h


lemma checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h


lemma checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h


lemma checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h


lemma checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h




def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w


def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words


def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks


def renameLiteral (variableMap : Nat → Nat) (literal : Nat) : Nat :=
  2 * variableMap (literal / 2) + literal % 2

lemma litVal_renameLiteral (assignment : Nat → Bool) (variableMap : Nat → Nat)
    (literal : Nat) :
    litVal assignment (renameLiteral variableMap literal) =
      litVal (fun index => assignment (variableMap index)) literal := by
  have hmod : literal % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdiv : (2 * variableMap (literal / 2) + literal % 2) / 2 =
      variableMap (literal / 2) := by omega
  have hrem : (2 * variableMap (literal / 2) + literal % 2) % 2 = literal % 2 := by omega
  unfold litVal renameLiteral
  rw [hdiv, hrem]

lemma unsat_map_literals (formula : List (List Nat)) (variableMap : Nat → Nat)
    (unsat : ¬ FormulaSat formula) :
    ¬ FormulaSat (formula.map (List.map (renameLiteral variableMap))) := by
  rintro ⟨assignment, satisfies⟩
  apply unsat
  refine ⟨fun index => assignment (variableMap index), ?_⟩
  intro clause member
  have mappedMember : clause.map (renameLiteral variableMap) ∈
      formula.map (List.map (renameLiteral variableMap)) := List.mem_map_of_mem member
  obtain ⟨literal, literalMember, literalTrue⟩ := satisfies _ mappedMember
  obtain ⟨originalLiteral, originalMember, rfl⟩ := List.mem_map.mp literalMember
  exact ⟨originalLiteral, originalMember,
    (litVal_renameLiteral assignment variableMap originalLiteral) ▸ literalTrue⟩

-- These finite conditional CNF subformulas do not prove the posted gap.

namespace LZPacked

def appendBlock (width payload count : Nat) (history : Nat × Nat) : Nat × Nat :=
  (history.1 ||| (payload <<< (width * history.2)), history.2 + count)

def copySlow (width : Nat) : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, history => history
  | count + 1, distance, history =>
    copySlow width count distance
      (appendBlock width
        ((history.1 >>> (width * (history.2 - distance))) &&& ((1 <<< width) - 1)) 1 history)

def copyTokens (width count distance : Nat) (history : Nat × Nat) : Nat × Nat :=
  if count ≤ distance then
    appendBlock width
      ((history.1 >>> (width * (history.2 - distance))) &&& ((1 <<< (width * count)) - 1))
      count history
  else copySlow width count distance history

def literalRun (width : Nat) : Nat → Nat → Nat × Nat × Nat
  | 0, word => (0, 0, word)
  | fuel + 1, word =>
    if word == 1 || word &&& 1 == 1 then (0, 0, word)
    else
      let rest := literalRun width fuel (word >>> (width + 1))
      (((word >>> 1) &&& ((1 <<< width) - 1)) ||| (rest.1 <<< width),
        rest.2.1 + 1, rest.2.2)

def decodeWord (width : Nat) : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, history => history
  | fuel + 1, word, history =>
    if word == 1 then history
    else if word &&& 1 == 0 then
      let run := literalRun width 32 word
      decodeWord width fuel run.2.2 (appendBlock width run.1 run.2.1 history)
    else
      decodeWord width fuel (word >>> 21)
        (copyTokens width (((word >>> 13) &&& 255) + 3)
          (((word >>> 1) &&& 4095) + 1) history)

def finish (width : Nat) (history : Nat × Nat) : List Nat :=
  PEqualNP.Outside.L_meta_9033.R2CleanKernel.unpackWord width ((1 <<< width) - 1)
    (history.2 + 1) (history.1 ||| (1 <<< (width * history.2))) []

def decode (width : Nat) (words : List Nat) : List Nat :=
  finish width (words.foldl (fun history word => decodeWord width 32 word history) (0, 0))

end LZPacked


-- A bounded unit guess; correctness is enforced by the existing checked step.
def unitGuess (P : Nat) : Nat :=
  [2048,1024,512,256,128,64,32,16,8,4,2,1].foldl
    (fun u shift => if P >>> (u + shift) == 0 then u else u + shift) 0

-- A data-saving wrapper: infer a proposed unit, then use the existing checked step.
def autoTokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  if mode && !(P == 0) then
    tokenStep (tokenStep k x) (unitGuess P) db id mode C F P
  else tokenStep k x db id mode C F P

lemma autoTokenStep_good (a : Nat → Bool) {Q : Prop} {k : Cont}
    (hk : Good a Q k) (x : Nat) : Good a Q (autoTokenStep k x) := by
  intro db id mode C F P hdb hinv h
  unfold autoTokenStep at h
  split at h
  · exact tokenStep_good a (tokenStep_good a hk x) (unitGuess P)
      db id mode C F P hdb hinv h
  · exact tokenStep_good a hk x db id mode C F P hdb hinv h

def runAuto (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => autoTokenStep k x) toks

lemma runAuto_good (a : Nat → Bool) {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runAuto e toks)
  | [] => he
  | x :: xs => autoTokenStep_good a (runAuto_good a he xs) x

def checkAuto (F : List (List Nat)) (fk toks : List Nat) : Bool :=
  runAuto stop toks (loadF F fk .nil) 0 false 0 0 0

lemma checkAuto_sound (F : List (List Nat)) (fk toks : List Nat)
    (h : checkAuto F fk toks = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runAuto_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

abbrev Certificate := (Nat × Nat × Nat × Nat) × (List Nat × List Nat × List Nat)

namespace Certificate
def formula (c : Certificate) : List (List Nat) :=
  decodeF (unpack c.1.1 c.2.1)
def variableLookup (c : Certificate) : List Nat := unpack c.1.2.2.1 c.2.2.2
def originalFormula (c : Certificate) : List (List Nat) :=
  c.formula.map (List.map (renameLiteral (fun index => c.variableLookup.getD index 0)))
def valid (c : Certificate) : Bool :=
  checkAuto c.formula (List.range' 1 c.1.2.2.2) (LZPacked.decode c.1.2.1 c.2.2.1)
lemma unsat (c : Certificate) (h : c.valid = true) : ¬ FormulaSat c.originalFormula :=
  unsat_map_literals c.formula (fun index => c.variableLookup.getD index 0)
    (checkAuto_sound c.formula (List.range' 1 c.1.2.2.2)
      (LZPacked.decode c.1.2.1 c.2.2.1) h)
end Certificate


-- Exact retained CNFs only. The circuit-to-CNF semantic transport is separate.
-- B01/B07 retain budget-6 clauses; the other 34 cases use budget-11 cores.

def cA00 : Certificate := ((10,10,11,460),
[0x10008c26400250922408e0d0970008225400108950007e24c00100930003e244001c08f0008a2208621028234000c88b00030224000b8870007021400204820008020c001f881000801fc001f07f000761fc001e8780707d000261ec001c079000741c80e1dc0006875000701cc001b8710006c1c4000206f000021b400198551ac001a868158001a86915c001a057000400c4450004410832000420cc000981b,0x1000be344002e8cf000ca33400310cd000c83181e32c002f8c9000ba31c00308c0040c5000be30c002e8c1000bc2fc002e8bd000b82ec002d8bb0000a2e400010b7000b42c8002c0b5000a42d4002cc002b8ac2a8a8298582c400260af000662b4001f8ab000642ac00188a90007029c00288a02789c2684629400260a30005628c0020c5528000208a100054284001f89f0005227c001409d0007026c0025899,0x10f10d0010842c00419090010441c004090005010414000690300018404003f8fc000fa3fc003b8ff000fd000f83d8f43c8f0168fb000e23e4001a0f9000663dc00330f5000be3cc002e8f1000ec3a8e8398e4120ef000e315cec000e23b400158ed000543ac00330e9000be39c002e8e5000e038c00358e3000de370da3603638400108df000cc374002f8db000ba36400350d2340ce0a8d70003235400330d3,0x15214b0014252c0051944091490013c51c004e145001404f81650c004f141001384fc004e93d001384ec004d939001344e40003137000064d4004c9300012e4cc0048933001310012c4a928499241705a4bc004592d000664ac0041929000644a4001892700060494004811e4711a4604a1212300056484004291f00106474001411b0004e4640045117001124410e430380d9150010a44c00419110003e43c00,0x1001890cd8c001830bd8a001880018661400608005f9810017f0017c5e8005e17d0016c5f4005ec005d9745c9705b85e5e40058177000665d40052973000645cc004f171001385bc005a968599645884c5b4001596b000545a400529670013c594004e1630015e58400551610015c569585583a57c001095d0014a56c004f1590013855c00549505394c0b1550003254c005295100030544004f14f0013853400,0x171c00719c5001c60d4006cc4371000109c5001ae70c006b1c1001a86fc006e9b86d9b40a1bd001bc6ec006f029001b30cdba000326ec006b9b9001ac6dc006a1b5001b2001b06bc006a9ad001aa6a40069c006959d69800691a3001a4684006919f001951a5a20018919da00018318d9e0019c66c00671990019c65c006545766800624556600060c516580064d8f65000649910018910d900018e634006398b,0x115e04002017fe02002000dc0080035001fe0ac007f829001fc7ec007e1f7001f5001f37bdf4001f27c4007ac697c0007b9ed001eb15dec001e979dea001e80dc007982b001e478c00785dd78800781df001e007c0076c277780077011001da001d875c007540074dcf75000749d1001d2164007246974000739cd001ce72c0073847001c915dcc001b3155ca001c76f5c8001c6724006f1c9001c4709c06f834,0x1914579180090a410023f8ee400023e8f4008f8230023709e3c0023a8e4008e8150023706e3800236002348cc008c4008be298c0008ba2d0022e8ac00894698b00088c678a8008a2270022515e26002220021e88400862210021c8682087c0084a1d0020e86c0085a1404a190021285c0083a150021084c008420f0020d0020b81e0c0020a824008285b0020a1640080c698200081a0500206124008184700203,
0x1a0a7d002731a6800026519e7e002631967c0027a9e4009ea770027a9d4009e8470027315e7800265156760026314e74002719ae72002709bc009c26d0026510e6e002631066c0026a9a4009aa670026a0a400994339a00098c319980099000982630025a98c0097a5c0881c984009525f0025097400962560500e96c00952590025095c0094a55002529440093c0093649938009324b002451a64a0024891c00,0x1b0000afabd002bb15ebc002b8adc00ad2b3002b1002afa9eb0002aeab400abaab002aeaa400ab85b0029f1a6ac0028918eaa00287186a8002a6a9400a9aa3002a6a8400a98490029f15ea400289146a20028713ea00029da5e9e0029ca6c00a72990029c0dc00a243fa6800a1c3da6000a582b00294a4c00a468da4800a428f0028909e8e0028ca2c00a1c19a2800a2000a1400a0e7ba1000a0a81002829fc00,0x1bd6f8002f607400bd00f002f2bc400bbeedbc000bb809002ec00c00bac00ba6e3ba800ba2e7002e8b9400ba05f002e817400b7469b9800b1c61b9000b8ae1002e2b7c00b884d002e212c00b7457b8000b1c4fb7800b6ed5b7000b6ad9002dab5c00b683b002da0e400b243fb6000b1c3db5800b502d002d2b4400b3ecdb4000b3823002ccb2c00b3017002c7066ca002c8002c5002c3afec4002c2b0400aec69,0x10032100311002fb002b5002530023500211001f9001d9001ab0031900303002f3002dcaea9e9ca44892027a9c865000b42b6a4a62902207e9e26b984002c6aca8694232839f6759a860000c831f0031dc6f1e0031c09400c681700318c5c00c5713c5800c500d0031201c00c430f0030dc2f0e0030c08400c28130030900307c17080030616c00c104900302c0400bfefdc0000bf80b002fc01400beaf9002f7,0x1002d3002b90029500243001fd001e5001b100187],
[0x1678e88be16a0002a9983a02f4598000a2658e78ba16a0002199039c2dc5a800066630e68b61660001798a398,0x1000139de3ac388670000aa728ea8db19c000219c43a834c670000666e8e98c416a000339a03a430c598000c6,0x15089d8000869b8ed93d27600019a683b44989100004e8f0ec9232440000da383b046c8c0000ce8a8eb8ef1da,0x1aa8f09642aa00028aa23c0578aa80007ea68ef9582aa00013a8e3bc5389d8000ce9f8ee9472760002aa763b8,0x1790da173262484870fd1d832c591c037e6f8de9bc3766e85880058ca18f19842f60001fad83c45acaa8000c6,0x1728e49c838e718e29c43826fc000770e48f8f29aa3526a08a91222e4588a111226440d590f21c708de800442,0x166cdb8000e27980000d3b20389419c33c6749c1272746d4f213726c604ba15b2543f8798cd16867c99131396,0x115d019e91842fc648c818a010650000ae654f40fb1f03e87b8f90083f0000573d679ccd1993300240400b014,
0x115cf61792ec5e0ba9770085e8000575767acb49652e25c0b60042e40002ba9f3d441c8210c2164200210d000,0x1344680cf19a330659c5374001391bd32810cf698f316658ca99136c79cf41e93d67a8cb8004e4911121c80d2,0x6de54013cf78de20240c7f8da1c0358690011be364688d81a035c08029808e48423dc348ed0d62804f8a29443b6,0x13b82184808e114210400881041f9f01e6718000cd3e2688d09a00780ec1f03d3466e0000bb3e0628f1963000,0x1798da9e4070050e3874050e5aa83281b80014419cf980600801c629d219031c648c13a0328001950aa7c8780461e4,0x11002e85507e7c0330650ce69c320001c41a0fa0c7192300e782705e0a8141dc28c52ca51492a6544e91dd04c,0x42c0520bc131e60700e8000a32702a8461407d4d21a60b86942c06300e180f980605a168308040be15cf885e0ac,0x10480780c3cc4e89c80055a9a136266131548fe064fb8770f21d83686c104210408002404688c04a090418fb017028,
0x16b4d608610a220439af3720009c9f82ae558ad1e32f8564bf1de3005fc08138022674cf19c26a490949e5026,0x10d02b1fa3046244c19113c654558ac32629c4a08a14c24c449f815e2c0568005b65d0b91522a01a5741f935c,0x42d0386943003a000738003a5342661983283904039c6707407071b4e65cb915421a3ac6506406e000a91501f03b04a0920d2,0x154c750c905652c728c13ea770ea9d00ea09c2c1e00b85a0b39053485c4861a62da428d28631541801a1f30f0,0x1044c419d3c46780f06933808cec13504a494920352520d8341e51500c8189f7026048a69d102a540740c602c,0x5c837a388fe0070b0170d21a634a18c300344da7c0ec0d6198fd86b0d47d8770741e47bc7898e318758cb0103f2,0x5f40b42540181f28250ca293e1ac3484b821004004ea0dd1b8384311b53c8001f58284eccc196050a0b744c0900004e4,0x56c0ae7c42b04005076c583ba0c1dfa7d019eb2a45404a0920681a4fe92f25c4b09692b3d84648d11f23a75cfd8053f4,
0x5fc1c2140259f109e1282004e0920fcf805432a021997f8761d52a81a1052d059cb31f32185c43c05905a42cb81ea210,0x11a0ff9fb0c2018fe81039e7b0d63e6164169ea1e83d46902100440cb11002b8408af84d0a425c260510086b4540a6,0x16f0900ec14416d010743de7d8c718c000a809011a20c121712013fe010000684007ecf986100c164168000ac,0x45c12e06cd21d31540d0d30d51a87ccd2a0014e2684608a14c264458893f0050fb8300825d95e0a0f7960101e595a000f4ce4,0x5242521a0f28004320a8160567d43a8273c05a0b39712da4148610a0480d41b032062534e88003ea001f7000fc8007edf20b0,0x1738ed89c13a618fc89b12c2444697d3005fc4f800a12cb2012702a03586a1dc3c8789d6020002a48d2670ec13524a,0x54b1ca2eca20d51a8770ea9ce3b60c00c000db21c83cdb2758ca00856c5508680c0e0190347309e0b827e2f0a28bb288,0x1529020c63a23246083106c0d0f982e1d07401a824038064e60b81787c81901a29a4f0a813f03654c751453a6,
0x16c04808d1242444788c114238001b16cce18002968144f8ab13a2b0c309b3267e44b00030200183032fbdd05d0b915c2a4,0x46340674c550600b0355011f30b82a502a000be15c2804b00151c4f094002a1808d141cc161242f09218a1a1900624f121031b2362,0x11acfb1f50ea1d0139e03de638c61682ce65902105002635622be2700099740c811002b8148268540a618828897098,0x10e01b2c7412088118160400540e9e600025c480340fc8202406b040798a1fb5050fe81ceb0f10203c8088ee33a1a81a23b,0x50e1502403305c0b41601c036068191051900f42003f8730e41b8c1883002286e45ac4a8941262244408705c0b4,0x12003907a0dc5a8ae9e34121c4368700d81ad03a080f80940037b1f81a0303cc20c1c8840742041b8000735429824c,0x1284450a01127e02f8044520222b138248008c213004662570830cc0e40ca032c04201c8de02475328568810111d4ec1441590587f0e6,0x4541aa3503d8312105b0f090b2125c0b796e2185c48316640c14c310634041e05507e002134a41522884b205400,
0x53f30e614fc994324658c68a51460a9019452882eced9ce0a21bc0f1df0a45840d902202580025b11344b84c3a6,0x101416a0c3fc800048653b1068623f616c02a0b3e68000415f830121611f40215f0cc1b0107ae628c8012aec2828c00560aa0001e0c14,0x1798001c11941c0043a2d380081e758103bf0800806f0705941a8009800002f0791f23c4688e1193d88000203515d2220e04a05c620b6,0x57134c63483166348000ec94a170f98a40b20b4718a30b00a8ea8e61ca390750e91ce37d078203722b8047c6023e5000dc84c,0x58730a400ae1f9000805da280514a20102e6149db05e09ce78c0003735ed3dc14c3d86200076c63328648858003aed2996218,0x10107ebe62942e00020651858290770a614b2a6548a7a100a04240421a0010f023b380044c000644190881c332379022c078881962310,0x5092de0207280306c981ca02a03798570017d6008330206f80a12c3242407070ac01c4b106d0de408c39852b80007cbc440cc410000835c3c2060010b,0x6000bba4e1304a08c1a82203c4041b0163c440c1982002a620802073f213435897098844298310c4420f0863216,
0x25e0bb172738e6801424041ef85a0a8141483b8518a6001d2a020ad],
[0x117a2f05d8ba1722e05b8b616a2d0598b21622c0548a814e298528a4146288508a013e2704d89a1322604b89612a250498921222404788e11a2304588a1122204388610a2104187c0f61e83c8780ee1d83a8740e61c8388700de1b83686c0d61a8348660ca1902d85a0b21602b8560aa150290510a013c2704d09812c2504808e0d41a0330640c41802f05a0b01582a05209c120230380680c81802e0580a8140260480881001e0280380600a00800800,0x15d8b9972add5b8b656bad65a2b4162ac457eae55c2b756cad158ab055eab1552a9548a8d5129852ea594aa94526a4948a9051ea3946a8c516a1141a824fe9f53e27b4f29dd3b2754e69ad352694ca991312604be9792ba554a6895122234448851021f43c8750e21b4348650c21142083d0720d41882d0520941081d02203404805001ff3fc7f4fe1fb3f47e4cf19d33866ccd19933065ccb19532864cc9191314624c418730c614bf97e2fa5e4bc177,0x1995326544a794d28e4fc9e93b2720a4128230360640b80f001ffbfc7f6fe9fa3f37e4fbdf6bec7d4f9df2be47bef79e9bc778cef9debba770eddda3b3764ec5d73ad74ce95d13a1740e69ccb9872ee55c9b92720e35c5b8a712e21c2b84706e09bcb786eedd9b9b726e2db9b636b6d4da5b43676ccd95b23636c0d79aeb586aed31a033f67ccf59db3a670cdd9b333662cc197b2b654c7d8a312622c4187b0e61ac3185b0a612c19823035fcbf5792f1,0xd5cab756aabd53aa5546a8502a034027ecf59e73b6664cb])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA00 : ¬ FormulaSat cA00.originalFormula :=
  cA00.unsat (by decide +kernel)

def cA01 : Certificate := ((10,10,11,476),
[0x1178a30008428400170a10005a27c001f09d0009826c00258990009425c0023097000922408e0f0950004a24c00120910007c23c00228882182c234000e88b00038224001f08700082214002007e0588300022204001f07f0007a1f4001e07d0000c1ec00008790007217c77000761d06000074184001103514400140460d84f000460dc4f0004e120381340012039134001304a0e8001283b0002a08c000500b,0x1040e30000638400378dc000da37c0037400360d6350d23405436c00180d90005e35c00338d5000c034c002f0d1000cc33c00318cf000ca3202433400300cb000bc32400310c2060c7000c0314002f0c3000be304002f0bf000ba2f4002e0bd0000e2ec00010b9000b62d0002c8b7000a62dc002d4002c0ae2b0aa2a0622cc00268b1000962bc001c0ad0006e2ac001f0a9000a4288a02789c148a70006029400,0x1484000180447c004711a00118474004311d0011b00116451124410e199190010045c003f115000f31c5120007044c001b911000e443c00429084190440856434001810b0005e424003c9070005c41c0016905000e440c003f901000fc3fc003e8fd000f83d8f40c0fb0003a3e4000e0f7000e43d4003c0f3000ea3cc003b8ec098f10002a3bc00390ed000e83981a3ac00088e9000e439c00388e5000e039400,0x159c00559650004858c00119610015c569580c82e57c000e95d0003856c000d9590015455c005495007018554000895300020544005314f000120394d0014a520005194b0014900144509404f93c1986451c004e9450013650c001c1410006e4fc001b13d001384ec004d939001344dc004c9304b8400f9350012c4cc0012131001204bc004a92d00128498260912b001244a400481270012249400481230011e,0x1689a50019a694006819e6704468c00649a10018467c006019d00198659940d19b00192664000e9990018465c00601950019064c00629930018e63028644006118f0018063400621860798b0018462400601870018261400601830017e604000297f0017c5e8005e17d0017b001765d1725c16e1a0645e4005b177001685d4001c1730006e5c4001b16f0016a5b4005a16b001665a4005796900164589601083e,0x1001e71d5ec001ea7a4007a853001e1175e8001e6001e478c00779dd001db001d9755da001d875c0073c7575800751d3001d4744007245d7480071c5b7400073800731cb001c6001c27140070c00701be001bc704006c1c1001bf001ba6e1b66d1b21a9bd000746ec00691b9001926dc001c1b7001846d400601b3001ae6b1aa6a1a6161b1000606bc00691ad0005e6b400649ab0005c6ac00611a90018069c00,0x18dc008a235002308b81a8cc008c81b0022c8c4008a22f0022a8b4008aa290022700225886260022488c0089063002111c6220022087c0088055002111761e0021c86c008661586800862170021112e160021484c008502d002110ee120020f836100020e09400830190020c05c0082a0900206814007f203002007fc007dc2b7f8007e9f8061fd000227ec007c9f9001f6001f47cc007c4007bdeb7c0007b9ed,0x199e6c0026a9a40098c2b9a00099a65002660740098c2399000988009825f0025d96e5e0025c04c0096809002590025794e58002569540093c759500094a510025215c008ec5d940009380092a4d0024293400922469104092c0092a490023b12e480023a9240012a490022c91c008a245002408fa3c0c2430023a904000ea410022c8fc008a23d002398ce3a002388ec008ca3b002368d0268e4008e0270022c,
0x1ac800abeabac000abaad002ae0a400a9c2bab000aaaa9002aa07c00aa819002a5086a8002a6002a3a86a4002a205400a80050029f0029da5e9e0029ca6c00a7299002911d69a0028f1ce9800296a5400a5a930028f17e940028517692002900028ca3c00a2a88a18420f28d00284a2c00a0a890027ea1c00a0283002809fc009f4009ee779f0009ea79002731d678002769d4009b45d9d0009c8009c26f0026b,0x1002de0a400b7827002dc06c00b6ad9002d7b56d8002d605400b5811002d402c00b5007002d3002d1b26d2002d0b3c00b42cd002d0b2c00b4065002b11c6ce002a71becc002a51b6ca002c8b1c00b2059002b1176c6002c4b0c00b06b9b0800b02bf002c0af400b02bb002c011400b003f002b112ebe002a7126bc002a511eba002b8adc00ae2b5002b8acc00ae035002b80bc00ac43bad800a9c39ad000a9437,0x1c4035003100cc00c243bc3800bf439c3000bec37c2800c1f03c2000c0b0900306c1400c1829002fd0af0400300bf81e0730300302bfc00c081f00022c0400bec21bf800beaff00020bfc00bf000be2fb002f6bec0005012be40002808bdc00bd400bceefbd000bcaf1002f219c00b8471bc000bb859002ecbac00ba6e5ba800ba2e7002e811400ba041002e112ee6002e4b8c00b9031002e10eee2002dfb76e0,0x100347d17480034603c00d100500342d0400cff3dd0000cf83d0033c0b400ceb3900337cd7380033603400cd0030033300331cb73200330cbc00ca475cb800cb32b003291872a003280032700325c7f2600324c8c00c9321003241ac00c9069003091c722002fb1b7200031ec7400c7859003091771c0031ac6400c5f11c6000c5b1500316c4c00c58430030912f14002fb11f1200310c3c00c430d00310c2c00,0x10031b002ed002c5002710021d00207001e5001cd00343002db00281002610022b0020b001f5001df0034b0033b00318baac2a3a6e9321a811e272800c22e0ac2849b23a84202781c8002fab62a49fa5e8a2087c9dc71000d2b49],
[0x1990f091d2320003aa543c0398710000567f8ef8dd1b20003a9ec3bc34c670000ea758ee8cf1980002d9d03b8,0x10001cab43cc538a4800056ab0f29412760003aa9a3c84c0968000ea9e0f192924a00015a683c449892800046,0x16d4da0000c2ca8f599b31a0001cb0c3d4654c6800056c10f496829200037acc3d056ca4800092af0f3953292,0x173c0024b5d07b8e39752684907f0ea1c235c659d23a2740e79ce39a730650005f4a90f69b73680003ab2e3d8,0x142c821003043fc7f1da39e001269ef2f25dcbb107206424841132fa4488b1802fc44482901220410800ff1fc,0x44a2ea748000e53e2640f694a000bf9540213e041cbb9792ec0001ea1c5e88690f2f85ecc09ee23045c86105202,0x59e34e694d11ed2b457cb115635058ced9d90000d4239f32e25d0b980014028400017604f91720925d0b8048096,0x12dc511f219031c649b318c000dc1b63586a83a1f500c01c029f3010010f39602c4558b19d9000134220353e8,
0x168c011a83b60001db093ee3c4778f41e63c8010f53ae0001da113ec6c8d51af17c3145e8c40123005c0a317e,0x1358348005d0b741d9f91ca3a0a59c82a238c709cd000c21702af5089b11d2103f4780e42b03f0684ce1a734c,0x12c4538a23e416c279f13927bc351a830458c960f51d23606686c3b6768ec9d83ae758ea9d4374514999201c0,0x16e0f21e33c0778ee9ec3ea30c5e0b61683085d0b31562a4bc1772285e48a97d3dc600bf9f63ee008590a8146,0x14b89e0da1a01782e8610be1703013d3b87ac9f93e25e46c6e0d21a26d8a213223e37c6a9b92864c48f0de1a8,0x17b4d61673605acd916e354594d996f000164369fa2c4564b09542b87e0721e12504ac951503c4794280510a6,0x157cae15a05cc40fe0983d0270d716c2d426c4b9b22dc258fd1aa2ca2684a89e13e6ccb789d0005c82c9683f6,0x1100a21b906c50cdc03f06a790f61c93de1180a15911c0e159114000750a80905e1fd2a47b4cd08b11c67cce800564,
0x4183b61007f4806b0690001e6203fe0c8e21c53860c41a03338c72c000bd3fc0f01f03b074104220420864f4f593f36c,0x4ec0823b87b0441da7f42e8420863e07b8143368d8003468f80034e8f000356f01dd3d81001c03607e0dc1a9fe0b6010ee88c,0x107108a0237a6f0dd80d01803c071be3940003ea010560b00f82a03c0bc1802d0002b0550a80c42590003907a,0x1800141e81285b0fd96e1320a40b1651f209c0a20135058c7a9db3b275cb780060eabd112012a41882c84b074,0x491114224439f029a52cc9951120664ae1e7346584b015f2ba698d29a42c469cac1a03cc7a80a8171e0001a1838,0x1740002a429c015020740e61dc390780e01d83a8710de79cb015d000b009a84004c090902033da568d108f124,0x162891123242624001732e8630b818b2ea490e91d0000bec03a0524648491189314000a398c316520f6946248,0x1740e5800548015038811001f03d87d3f41fc3d1e830a5b0b51872dc60cb2883108620b78820005002c93640c,
0x10511fb844d49a01447ae99d1000a28af88d074ae1041212466249100010a51ce214838a218c5946386810f692438c,0x1814a518f31c0015411f5fe824fe1a73484e4461c03826fc0b8153cc234ac1572aa0580a201274724f793726c,0x5612c4820499fb40c010f5ad85b89c1651321f81482740258cec96f000c000c4d3000f78800e8130240381c10506d40e,0x418a2e6386a05c0507b9921b01801866ad996f00142cfd1c03586306905a0028289682d0486e32880ccc07929a530a89f82b8,0x46104c2f82f8240b80845e86004a052949b6062939f63e8065233f0065217fcfa8bc1860a28fbf20028eafc080082011700028c96e,0x13b4770eb40404873813322044ef8231c8220f092824e002a2b2e788f29e90a0144d896d0114f5b22dc178111aa2ca,0x17b4d6000640b2836a0d37e7040b9c002a06c02019030051009c23a60004a89211a228268484187e0b49ad414,0x10700180012e1201d04a41e2704b89b41a2584c16b2d46c0d709a12a7a0b609e13e274003245a05c8b420e2ce,
0x18045c0a51462dc520a23e41882d854098010e78d6130e6b10000e7818746b0228448880f81ec1d42582b4208300e816034,0x100368b0e148971830bc0885f06104c2e85d81034a550003465313f25e46c6d8d136c530061a5544061a74a8a800c34af11e5040,0x4004da04797023cc80834c2040216c2784c0097c42e0317c4300397c4001e2000f31d4152110ce1683405930a1602b97b30282cbb04e09a,0x1030bfbc47940617f844fb80014e1a0a90843a82029c3b4244188505120414c2804e09a0042911a0bc088308260082fc0c4ce8e11b1b6,0x5672be5008911012e1d48a21301a18d7a2f87d8c0a0b0045d8270e40085fc521a03688d12e27805060828ca51c048c9d2a2a0,0x53825c4f011026048084080d536c020dd0006f800e95432620006f800e6c563c878c020dd8480e020402724f78181c6120e53806b02d000,0x1012a08007540c1d65606e0ea8500e6fd64ccc9a3001c45a73407a82aa1029a52ca895c41e240f3888009ba5e12c44a093a08256,0x4660018ed76426070272000ac220269272701487d063050848001d34f0970303b600361020f081840410a0e000fd04280c2209c001d91502c1d7,
0x1308599af3646a85f00181e5d0c01702c856801812588ac00b0156319276400c016b0cc07432485422131001c4a9a82c0612b1600012d,0x41431a0a191514000770be85ca79512982a4530ab1542a0528a314e0024f800ac0c9a1616c2d0af1622ac2c05a8c318a,0x1015ba97c0001b97a0250b0c443008664ade006638e86a90ca1515e2ed0b80a0120003a192430500a100b2884fc9e9c93de,0x17d00195c15c7dcb095e332658c90a914c858558aa000124ad000314bf15829c5200008202d0d1d16021a182314b49af2da,0x59932c550549592ac2acb119214c8585521818886812063000b580817e1b1826b4629b135e6c8d59a9172864618b5160,0x11f8320292d27a0b696c2dc598b2094126061e5808b2c04ad20256b00172c36141f3ade514023e7ac4b4a1c18a304d79ad3620503095c,0x16ac5d0be3546c9070992d25b4000a787011026176090108bd0482959700828de93c801242c3606371801bb41cde2148c10037a8002261d428,0x1194f416c010a8cba42c8742f06117617c2e0bd07b2a40029e5c0a316e004b78125c41cf4a120b3480007a90008921e324664531a9154,
0x4ba2a28590e805e2a046c5030c1829b2c253ea951500313ac109da021630005780859ce3038594e103858dcd3746ccc40049c20415b87d0a09412683800a55,0x1720c20f935a1910f1b130c6c8c38e835460c728be296],
[0x119832c630c518830c610c11802fc5f0bd1782e45c0b716c2d4570ad1582ac550a912e2584a8941262484889011e2384688c1162284488810e21842884106208408800fe1f83b8760ea1d0398720e21c03786e0da1b0340670cc18c310610b015c2b0550a814c290510a013c2704d09812c2504808c114220350680cc190310600bc1702d0580ac1502905009c1302504808c0e01a03005c0a8140260480881001e0280480800e0180280400600800800,0x1532a5d4b295528a4d4928f51aa3143a844f69e93ca704d099d322624c29712ca584a093d2724547c8f11d20e41a83105a0a41282103a0640a81101a024027e0fb9f63ea7d0f99f23e27c0f79ee3da7b0f59ea3d27a0f39e63c8634c618b314624c418730c5e4bc1772ec5d4ba1732e45c4b816f2dc5a8b49682ca5909b93626a4d0999322624c0919222424808f91e23a4608b91622a4448810f21a384700df1bc3746e0db1b43646c0d71ac3546a0cd,0x1784f05dfbbe77aef1dd3b7768e9dd33a5748e85d039d738e65cab94726e49c8b8f718e2dc538970cdf1bdb7a6f2de1bbb766eadd1b9b726e2dc1b736c6d6da5b43676ccd91b1b626bcd71adb526a0d3da734d698d1da033f67cced9cb38666cc193b2664ac718db1a630c5d8ab14626c4988b1061cc35843055f8be97caf85eebd97aaf45e6bc978af05debb976aec5d6ba974ae85cab8d702dd5b4b4167ace59ab2964ac658ab095f2bd54aa914da9a,0x64bc9692b2523f47d8f91e23646b8d51a6344668cb1822fc547cef95f13e07bef71e93d17a0f3de6bcc796f29e4bc878ef19e23c3])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA01 : ¬ FormulaSat cA01.originalFormula :=
  cA01.unsat (by decide +kernel)

def cA02 : Certificate := ((9,8,11,155),
[0x100198d2002f1a40064311802c6700158ca002418c004430800b85a2c048be002b17400482d800885900150ae002715c005228038aa002414c004428800984a0513c004826800884b0011892002211c004222800804500020860002104003e1e000743f000f400381b0d064300d0ec00241c8004437000806a000f0cc002e18800582f000a85e00030b40002158005025,0x1002916e00502d400b05980154b3002b958105880148af002815a005429818ab0029152005029c00a25280144a1002793a004f26c00984b80130950024922004923c008c4580118890021908004121c0076438010a00401f8f87a3c09906001420400683f800ac7d00120f600221e40074391c0dc6c0e1dc00243a800d07300158e200241bc004436800d05635800d469,0x18280207018200204070040006007f3f400fe7d801f0f7003e1ea00793c400f277801da0075b9dd800753a400e114ba000e672801cce30039836006f88dc8006e885c40070001b6006cb55b4006c35c00cf14b5800d469801a8d10033c4ad20031c3ed00033800cc6580198c90031800c26280174c5003017cbc0c30c00b26080148bf002817a005c2d968145d80164b9,0x801fe007c801e600668013e004c80126004680262008e8014600878020e007e3d9e0de6531138964822800fa7a3b9b8c859269288e44002612f004c2520096cae5c0096064012a0a8024f25940024c11004901a0091802431f910024027004783a008e46c011c8a80233178d002301700458260089c4628008903c0110058021d0d0042e130c004281200840140106],
[0x18a209012490002cd3e663000052e84f170ae0014b593a592b8004ad24e160a8000fb4136,0x10022a851288439449a5329140989f2792c9c4a4580804b8aa04321508472212490462191484,0x17d3e1ec461f128904e220f0843a131007024a13fa44006b2b288ec753a03c1c11081dd1e,0x1a5391c4e002008100673470005ea43d1e4f0190b06c34180a84c2e1409284fc910015d46,0x11250a3540361a830de6d359587e3d1d8e46e0d4d26530974b2552893419a4680b000d1a8,0x165318240c6833a78643340a09002d16271365b2d015483115898602a5128c5e29098b850,0x16c351547c3c1d0e00a0bb692f8014e82402045a33160c8000b02c9b0d46e831a00050a60418814,0x41cc2a532178d05d33a753ca64627cdc],
[0x17a4f45e43a774ce75be37b6e4d99b23636bcd71adb526a0d1d9db39670ccd9932f64ec9992b1c62abe97caf85eebd97aaf45e6bc978af05debb976aec5d6ba974ae85a0b3d632a5548a6d3d2794e093d2724516c2d45a0b31642c4580af15c2b4560ab1542a4508a013e2784e89c1362684c89812e2584a8941262484889011e2384688c116228418821022003f87e0c61883085709e1342604b0941142202d0580941201802e0440800700c00800800,0xcd49a734a674ca99331a5f4bc96d2a6544a794727e4f49b92f25a4ac948d91ae35469])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA02 : ¬ FormulaSat cA02.originalFormula :=
  cA02.unsat (by decide +kernel)

def cA03 : Certificate := ((10,10,11,554),
[0x128c00210a10007627c001c89d0009826c002389b00096250922403c264001189700084254001d89300072244002308a220860b88f0003a234002108b00076224001c88700082214001f085000801f82420c001d881000721fc001e8780607d000761ec001c879000741dc001c875000701cc001b8730000c1c4000086f000681546d0006c1a8560006a15c001183b0002c08c000480905c0005814028000500b,0x1374002f0db000d6350d234030364000e8d700038354000d8d3000bc34400334ce000cc33c00328cd000cc32c00320cb000c232c00318c4098c90002c31c002f0c5000c02f81a30c00088c1000bc2fc002e8bd000b82f400038bb000042e4002d8b4000b22dc00298b7000b5000b02b8ac2a8a8160b30009a2c4001a8b1000682bc00210ad000762ac001c8a9000a4288a02789c120a70009a29400158a500054,0x14301c444004290f00106434004210b00106424004150341800411070010241c00041050010404400019030010201c00400fe000fc404003c101000ff000fa3e0f63d0f2168fd000e43ec0033c693e0001a0f9000ca3dc00198f7000643d4002f0f3000ee3b0ea3a0e6128f1000563bc00338ed000543b400328eb000523ac00140e9000bc39c00388e5000d839400380de370da0f8e3000ce38400328df00044,0x1544005314f000100314d0014a520005194b0013a52c0052400511425013e4f05c51c004b9450006850c00461410010a4fc004193d001384d9344c9301313b000564e40015137001184d40042933001064c4004b12f001224bc004a928499241012d000464ac00461290010a49c0041925001204791c4683248c000e9210011847c004291d0010646c00459190011046400451120a1170010a45400419130010e,0x164c006398c0a026644006298f00186634006218b001866240061187000060118500182600005f9830017260c00604005f17a5e1765d05c1617f001665f4001a17b001565e40019177000625d4005c16e5b16a5a04c12173000565c4005696f001565b4001416b0014e5a40059167001625815e570400f1650015a58c00559610004457c001095d0015856c00559590015455c005495007018554000895300020,0x1001cf74000739d1001cc73c00739cd001ca734000500c72c00721c6001c47240071c00709c06f9bc6e84e71400159c3001b870400151c1001b46fc00149bf000506f4006b1bb001b66e4006d1b7001b26d4006c1ae079b3000226c4006b1af001aa6b400029ab000086a4006a009001a669000689a7001a5001a06799c669981304a68c00159a10019667c006499d0005066c00619990019465c006499500190,0x1834007d451828001420b001f2824008160181800802070020480c007ec4780800801ff002007f4007ec3b7f8007d4377f0007e8007e1f7001f4001f07cc007c4007b9ec001ea7bc007b4007a1e6791e27804e121eb000567a40077c5579800779e7001da79400141e3001cc78400775de001dc77c00769dd001dc76c00765d376800761db001d67502a091d9001d875c007442d75800741d7001cc754007481f,0x11ae40002231963e0023c8ec008f2390023c124008dc578e80088c518e0008d6318d8008d233002340f40088c458c8008c02f0022e8b4008ae278b0008aa29002230b6280022689400898190022308e24002220022087c008740086e138700086a190021a85c0086a15002071ae18001fb1a616001f5196140021083a0c82a0884c0084a110021283c0084a0b0020715e1000056844007ec55838001520f001f6,
0x1a04009a27f0027b9e67c0027a0fc009e83d002780bc009d277002749cc009c66f9c8009c0250026e06c009b8190026a9b4009aa69002670026597e660026498c00992610026416c009646b9880093c699800097a5d0025e96c009784b0025915e5c0024f1565a0025794e58002569540093c479500094a51002520c40093c3b94000938009324b0024891c009140090e3d9100090a41002428fc009085900237,0x1ad2bf002b30debc00036af400ababb002b8002b6ad400ac800ac2af002ad002aba9eac002aaaa400a8c6baa000a9aa5002a613400a8c57a9000a829f0029da669e0029ca6c00a5c2da6800a601d0029600292a5400a429500010a4c0001a910028f0028da268e0028ca2c00a305b0028c164009f46ba2800a1a84a0a809f84a1228900288a1c00a204b00288124009f457a18009f28700276a14009ca830026c,0x112400bcc57bd000bc6edbc800bc2f3002f0bbc00b7443bb800bb02f002eaba400b9ee3ba000b9ae5002df0b6e4002e2b8400b7421b8000b7800b6add002d8b74000480cb6c0002002b6400b5c00b56d1b5800b52d3002c91aed2002d0b3c00b42cd002d0b2c00b2457b3800ae455b3000acc51b2800b1ec3b2000b0ac9002c6b1400ae447b1000b02beaf2ba0d2c3002c2b0400b0abd002b90eec00003ab0400,0x1cb800cb32b0032cca400cb3270031d1af2a003131a7280031119f2600324c8c00c932100324c7c00c7457c8800c4c55c8000c4453c7800c6f17c7000c6b190031311f1800316c5400c4439c5000c4800c3b110030cc282a09b0f0030e0ac00c230d00304c2c00c1b0900306c1400c0f01c1000c08150030203c00c0005002ff002fdbdefe002fcbec00bf2f9002fc17c00bcc6bbe800b7463be000bdaf5002f6,0x1da000d8c39d9800d9000d7b610035ed7400d6f59d7000d68150035a04c00d600b0035802400d5c00d5751d5800d53530035418400d505d003451af520034ed334ad23461384cd4400d434f0035013c00d404d0034515f4e00344d3c00cfb4d0033ad2c00cd34900330d1c00d0f41d1000d0841003400cc00cf33f0033ccec00ce737ce800ce02b003380a400cd81f0033607400ccb3500332cc400cbc00cb725,0x104400e600700396e5400e4f91e5000e48270039006c00e3b8d0038be278c0038a03400e20030038700385de78600382e037edf37a1805ee1400e138300384e0400e137f003711af8200370e0c00d9469e00001a3810036319f7e00362dfc00d837d0035cdec00de37700378dd400de3730037813c00dc457dd800d9455dd000d8c53dc800dbf6bdc000dbb6d0036511f6c0036ada400dab670036a0d400d943b,0x10035f0033300307002b10026b00249002210039f0038f0033d002eb002b7002a1002750024d0022f001f90039700370d131cbcac8a8a7c9623681800d8b3ac42e8ad29e9ca4a8b1f60035ccc304b72aea526891a1e7c800e9400e8fa1e9000e885d003a013400e7b9d0039be679c0039a],
[0x184d179051ee0002aa0e45c4087a8000a2829168fc1ee00023a024583e47b8000767f9158f81ea0001b9fc454,0x10b51423322c454000234488c8868f70001a50b2312183d4000654288c0859032003d87a2191e60010820e414,0x14c0000474a88e0989300000ed2823724e4540006547c8d8911150001451c23523c454000454648d08c915000,0x18f8bc9730000ed6023d2ec5c4000375788f0b29630000b54d23b2784c0000694c08e89b9300001552d239268,0x1155902433666c000047630908c918f0000b5722413045cc00055598900c09710001456523f2fa5cc00047588,0x179c00069700920f89e7000155ba2473da79c000476d8918f49e70000edb424537a6c000069650910db9b0000,0x181d02808016029042210001cd252153ca710d49702864b88a0f44528a113a2644a891118f3000b714a2493f8,0x10440700c4945250e00010a930008003c6008f21e031681503a06318638c69e54108a5108005ba0492580940c,
0x10cd1021f43c8750e21b434865021c32844b4300300003b8730b01488492694529051c0981002a0500900f01a,0x14b0920280a809428a2e45a4248402b0489301502301a0a41100c49418419031396654b91682924bc8e0f60c6,0x192cf11e43c030cf2a10452888001a949c858db1f00a415c9c9f4372505019c227e800e023a4909101602f252,0x14c8f58474845e89b1ef26a7b91ea3848c5ec0a0af05059800dc18e2c24b03646804749e83d0720d2c057cb1161492,0x4620c600096a26180003111f4155289a606a6a0d283406e0d8d4a270002f5281b142c7a0231b20906d4229b4478,0x10c0000ae12c23028a523786fc2d05f0b21711824827c43d001c2282449019ba274424faa434728b9238584a0,0x14848f91d03e068108202500b81682f2564a49612546a0ac0e8184980a80e01701a0a40d8160189281903325a,0x48c3ba76c440760d821c3a86b4a623c4808d000d0ca114024047835b544a8000938ce19434868420888001074a6,
0x182ce520938e0e8640c70720e1281ac3566a8d49cb41889d10218000c3cd99ae1860892a87939a1fce788b3b4,0x1128652581a232c698cf1943546b0d4000708de1ba09c6d12b91846446c8d2330064710d000046958d71c9414,0x1718e51c80e41bc3a0730e21b8360700da1ad299cb4400008ca590aa15c21053082141280610c6180000ee1d0,0x4660d41900025994c002954b63706c8e01d2384778e41d6394740ed1e23c8780003d0788e985509c120169e64b4,0x1368001d9054090e625d1782e05f0b71722d85a8b41642cc588c01822fc001a03386682604a050098c325c2c0,0x1794d4a08396654b41492388305703345289d10a2043e8750e21a4302ac18000510158283504bc37c710db1bc,0x4cc18c314622063c281cf22053c462d2598d49296c638940729592983b0709406124e0489301180d000d4cac062,0x18ed1983c07a82905a094aa0e81f83e4b0320770bd1463a85d0a02ac3252b9d704a0a06905604c334289553ac,
0x13984f8e728e720520ec290728510a14b46b4a31c71ba2604b89612a24cc81912c845cca16723664cb311a482,0x57e47c1112800078b642581b211d2f8b516c2d05d8b24b82cc588b015e694d41a70c835c350d80cc974488e3124,0x6a24b08183584a512984458801181f8ed9ce4a82243e0774b22203d86c10e1e8062b7d50951200d65093024f300,0x185ccf9283444acd192c338490ac1532b2570ae95029e548a8944286528a4a25438690af12d000dc1a231c590,0x43a6a298ca714c296011d984e550141572aa98483824000edc23000edc22008edc310660c008053840510961181ac250574c4,0x19212208a4c07503e9da3ba1e00c81e3bc141281d13a074ce906138a710e6018b0f14018b0eef9c32de0022a8103fc6b08c,0x62c0080010303b4c8022d08ac988b616d2dc5a8ec8510a809516a43272428841f43e66e8dc941224002bfa20002bec62,0x4575e69982d1fa0be4f8ffa164a21712420028280c9d1f5472012988302d41816ea10600003e87a0554ca3ed158ff1fa,
0x14b48981035b3e25846e81835a694ce014002370ae9a09612625648c9412d000056374ce674cd9a334467cd20000d6,0x11641623049043d00112406424faa2e48e094141242580641312b4c89a09402b048012b98006e400d820456f0c419a042bc,0x10b118910224934168064d2158132680a09400a7510204984025e0646e9a8081f30b81795a2ba9792926303c97c2705e4ca,0x40038f3599903285d3526404c110a2b48578100ad1593602409e2b02605a01820053bc4460560d49ac9212c0504a41282f00e,0x108034ce01305baaa574ae1590329b9320260215fc001a20c0d30006a8d69bd3526d0290067c4dc99802a174d80604ec6c9b4006f31b0a5b38,0x4000aed153996b2d25b8b696c00a5bc000575469c8ab95400029e6e00a9c0af0000ae00437819512710587a66f0ac0981a197,0x115d8ea762764e0a094027a014a10000ae9653a90a2244448390e00a44c0005740e9d0ec1de3ba754ed0053be,0x161d38a724e69d13aa764ee014c50000ae9e0fb1f2406804ff0054080002bb714ee6ecdc1c23826f8029c3000,
0x5ee48c0780f91f2f04848e81a032990002510012a808965742ee5c0b922643c001b82c346c26447a064f2618c1989310,0x410426fc1f71aa238189e63ca052509ac24019a2904154da41a823418000704b41c2a7a4543e8ba8ff2f83f4f522c3de,0x134c6808404a3352023f3e87ccc2984406348428264f0330628c43c2790f124b49296c41a591041b04086b4a6,0x45809200535abc4b4300001f03702483e1949ed011fb3b8680fca44380708dc9b642c778d19f03ac67067086050,0x52d15600088de4a893e2364025e87c08f0b81241d27c09a13c2605e0be108ad85b0961042ca3625457496155248,0x1068ce1240f006442a7849296c448830ee964008a10108780a2642952e5688e064654b40011324803343e8750d21800845d8a284,0x18242183a0800fc1f27b1322682519746829453059330534a612033c8d8cd14e2426849512932c52c8e9a3258,0x63948e210431d63bc950e709d13c2a44e0aa13029c4d8211720f00116e0f80116a1083c05c0b41e82f4142281620b0ba,
0x10c448033428010a9da0b0c0014fdc13ea5f37c61c9e9fe382620a020109c708c4941406178dd1852747d532a43480,0x400e433d2793fa848108204260b908a4d10c0a11790410809480a4047e614c210610a158132780208cc504a00411791c,0x463040c14003deb795e2844b46a08d0037546b5929fc9b1352668e11b8040009601da7e3de7b8f624648a0113e0fe150,0x55d258670aa92410c0a04205404a900288001f2003fd5fc830d210a158003113180e30f9580a0d90047080238c0040a6a88e0c20c410307,0x45307c954d785c018d3df019c32469a573e67d00046b9f40089b0801724d45e5a8820d0202334cf959250688ae12b346,0x5a425a2ac0017a2f0588b015e2b85089006b0920f026a800949ed1a14d2405389094b00110e7e27a500a09390ae,0x14807c06b0920bd4089e13a2a4e70aa14a9510919e3bc84c531a13ac8451b12a25201518800b7c774b22b4572143be,0x5213444a02ca363465349592a338530a70015c6aa99623a007bccfe52c42a780005f42c6ee00379001bd8189280637f031c080064c0032e00231,
0x1a092f9be000d84046c602365011b3808da680138001bb88b0c4a811482c0f01f0420b81782c020ddc994f665c4d04a3308d0cd12033e,0x600488005978ac9e000e7b0e54c81beac69508600bf17b47c8f4020005900ed4182f011c7c004a2007239301500d0520178c801cb458160,0x5295064b13f9240b8a100c24c02e0340032d0054c892a1404b1d145169b92724202a1f4384700a093f224441239f5406,0x63000055d0f4020183d8320183cd060183bcfe09414285058a101327804314c0910ae195e28444c003a9a183c28103408017282032,0x40912f4100705a019430001020a9130184cd0e04555ab20b8ae28204256dbe27a],
[0x11782ec5d0b91702dc5b0b51682cc590b11602a4540a714c294520a31442845009f13c2744e09b1342644c09712c24c4909112023c4708d11822c4508911021c4308510820c3e07b0f41e43c0770ec1d43a0730e41bc3706d0d81ac350690d019c330650c816c2d0590b015c2b0550a814c290510a013c2704d096124240470680c81882e05a0b01582a052098128240460700d01802e0580a8140260440800f0160280480800e0180280400600800800,0x14c89893025f4bc95d2aa534a49452524949091d232454668c918a3045e8b916a2a4528a113a254488750e21b4348650c20640a811001ff3fc7ecfc94528850c9e13b2744e49c13724a490919222424808e11b2344608b91622a450899122224408790e21a4308590a206408809001fe3f87c0f71ec3c8788f01da3b0750e91d039c730e51c838c710e11c037c6f0dd1ac3546a0d31a4344680cf19c334660c919031c630c518830c610c11802fc5f0bd,0x171ae2dc538670ae11bcb786e8dcdb6b6c6d6da9b43666cad8db13616c0d79aeb586aed59aa34c696d29a3345688d0da1341680cfd9c33766cccd98b30656ca98fb13624c458830e616c258430760cc1181afe5fabf17dafa5f2bc978aec5ceb9972ae45c2b796eadc5b2b5d6b2d55a2b4167ac5588b0d5fabe574ae55c2b055eab1552a954ca9151aa0530a5d4a292518a2d4528950ea19422835049fd3ea7c4f69e53ba764ea9d139a724d69a934a65,0x348a9051a9f33e27bcf69ab35269cd093f27a4ec9c82904a08c1081f03a06c0c81702a04c007feff9fd3f97f0fd5f9bec7d6fa9f4be87cef95f23df7bcf75ee3db7b4f4de93cd790f1de33c5784efddf3bd774ee1dbbb676aec9d8bb075ee99d2ba4740e79cdb99730e5dcb392722e41c7b8e])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA03 : ¬ FormulaSat cA03.originalFormula :=
  cA03.unsat (by decide +kernel)

def cA04 : Certificate := ((9,9,11,217),
[0x12c1c4003a38800706f00138da00221ac003635800cc6431180bc2634800b867000c0ce002c194002e32800586300138c2002217c002a2f800b45d00160b6002b1640054291402c5700070aa002714c0044288003451001309e002413c004a08134004425800284b001181449001108e000711c004222800804500018860001104003a178fc003e1e0c0003c18800481d,0x1548013ca7000b94e0046294008851800fca1000a942004e27c00944f80134984b0813a004626c00884c800fc97000892e00492411c184a80038930022122003f23c001a47801148d00221160043224008244801081243800fc85000510a004003106003f204000e40800f87f001e8fe00041f400043d800f076001d0f200341e40077001c8e06e361a86475000f0e600,0x17404400e10ab9800e471801c80b003841ee20037dbae000379c2006e38400066f801bc0700009ba006e00c00da6c801acd500349a200678019ac96700198cb0030c7aca003218e006431400c318b1800bd16b1000c2003017e005e00174b8002d97600552ec00b9002d164b0572b068b7000f16a004f2cc008c5880110af001f95a001b2b400a85329144a0142ac0030,0x19400c012692802460090c6e44009047c01208e8022a3d8f002263b8e00235190046a2e008a8c63000898be2c008a002210f00434010b83c30010a8480214330040c7b080041a0a008309c00e115c100102003fa02007b40400fc7d3e03cff003b9fa00753ec00e07c80044f9003d1e4f00b3dc00ee7a801d4f300381e2000d3c400ec77801d8eb003a5caea003a1ce00,0x10ed80015e00574015babd70015aac802a239ac002ac2900552a600a80029e00a6d269c00a652c014c1a8029833004b46f4a005228e00a40a4012d15d180144a1802833da1002813f005004200a007c012d11cf8013c9d8027819004f02e009686e74009c4dc013598cd80134998026813004b42b32004c25e0098034012d07cb8012b94cb0012a048025407004a00a00,0x802aa00a28024e0088801b6006b801a60060802e600b5802720076802a5429244a1d006c351a0be005cae200b7db6e000b7084016c0c802d5690059ec7680059aca00af896c800b1584015f],
[0x18f1bc4811c000628c1ba441080007a841b8308b80007a651b62f0b800062631b42e8b40005a621b2,0x1571003f8ee3b19a001fea01c4621820004ab21c2611820003ab01c05e97400072ac1be4a11c0007a,0x13c94e3c0f855150579c4419043d8f4580ee3b1ae66800809c64f1384d0d6348da360fc558fa40958,0x658229cc6318a619c2700006399e0003a72818068e63a8e0050120781c000309104f3906b2709e26800035,0x5ca0003995d3c3a4081bc0a1c470000e1124e43a01105012390133940015c16110e700012c0a0200e03000,0x1040158000d40410ee40102c49e750163901a3a0e63a9d00781c09028080dc350d05380a021cc0380c7395055026,0x8e037298ce000893b4a202008c6a1a06c521460010e9a1d8201564f13a4d85c16860178820027c4b9d6,0x868ea15c2b0a8590b0c02e46415829000a6280721c06a19864179063b89f0200ac641886650940529d8,
0x20005d460080be04061391de5a850121be5f1705f9645e09c268026d8c4318be6c8361010c250742487276846,0x23e3942a2c0cb0b0d73408c19029000a02386a178213c0df2f8242fc282f089000145b8451167700c0b20005b,0x10d8406c90c2f91631914311b86d84e7783e0b84c0e82c0a8987488a1f99057994569921e9da0d1d4,0xb78932589525c9123c1c3bccc38cbb2c099234671986516cd835cd6354d434cd23449801843cbc331e2,0x22a0281d4b2160140e2b92608c0085dd645614c500d42f0e47992e4b1246f1ba0083c4c000390ce7900400806,0x5647a0201fe54154b62e0b21384d374920708f2449725493094f13c8521283a144490e4000f3661c62c0ae,0x400530fc350bc7a8400e03c0d91e6d1b24890c300be4b9163192c450c46f0002baf300822c1811e2c03040c042ca04097,0x2af3d4ad12cf62c0d7000a00008edee010060081030e2218b179ec7a0a02988c2208278078240861d0841c9da,
0x2000c4f92a43f0eca72a8af2b8eb110461140009f1e8727687c7280005b2d0809f3e0f00eca7010c5d541805e,0x2141c9299f07b89e5a010776f52dc041ad0f1f2258387b0183725815c003575c8003be002af2f0d47d0c06d0c6311b6008c8,0x4387b03475054160043ea5e0f4fc088e62d0212dcb82c8fa1384d3e44b3d8043632b8b25c8ac000bc501f6,0x2b102032490239f62a1f82907428808262582c0cb164d7340020657e9b22f836318403110c6d916451b80f1f2,0x14396e5b10a5c0dc598d434162022cb864183f418065460ac001fc1d94e1f954021debe04514c5513cb400038d66,0x21406f2a1b84509e45968],
[0x15acb556a2d35a4b45682cf59cb35662cb594b25642c758cb1557aae50ca152ea5c49291d232414808f91aa344668a8fb9f63ea7d0f99f23e27c0f79ee3da7b0f59ea3c2780ef9de3ba770ed9da3b2760eb9d63aa750e99d23a2740e78d81ae3586a8d41a6348688d019e338668cc196310618c217a2f05d8ba16e2d85a8b41662c8588b00aa150298520a013c2684a092120230450860bc1682c05409c128240440680c81702804c0880a01001401800,0x676cec9d739dfbbf67eafd1f8bf07daee9dc3b5764e95d239b722e3dc5389708df1bdb7a6eedd9b9b716e0dbdb736d6d8dadb53696a6d499fb3d678ced9bb3666acad94b01600bb575aea5cab816cad7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA04 : ¬ FormulaSat cA04.originalFormula :=
  cA04.unsat (by decide +kernel)

def cA05 : Certificate := ((9,9,11,168),
[0x137800a86d001a0cc640f1ac006234800bc6700150ca003018c005e30800b85f00160be002d068ba002a16c00560b16400542b800a45500020a60028138004c288009e00251208c44210909a001612c002a248005047001008a001b10c003e208007441000f0303f000d87a001c05076001b0e400341b8006437000286a00010cc0030168001c07098002410040002009,0x15e80008bb002e16e005c2d400b25880164af002b15600562a400a70029542a60029146004e8c544005027c009714a78009c0026932004b00124950024c009047001189100201220047801148843211042e46800608b001d112003121c005e42800a883001f8f87a3c1d84c81000b0fe003a1f400623d800bc7900150ee00391d4006a3a800e06e36088e600311c4005e,0x18341401068180202ff810020011004001e007f02400fe03801f8fb003f1f2007b3d400f679801e20077bade000773b400e718bb000ea74801d4250039456e80039800e071801bce30003814e10001804df00371b6006e36400d46b80198d700349a0ce1035400c46980180d1002f99e00653218c1c6680188cb0030192005f31c00c26280184c1002f17e005d2fc000c,0x15b2c1549800409f0f2713617cb4572a12800a38028b43a3002882f005084e00a04fc013d9dcf8013c11802741f004e26e009acce6c009a06c01320b802612f004c2520096cae5c0096084012a0e8024f25940024c0d004900a009146401208f8023b1b8f0023819004682a008bc5630008b02c011401802260088c3624008843c010918c38010c85802122d850021000,0x8020e007e801ee006e8017200598015a004d80282009880246006180272009080208fa7a391b4d6],
[0x15f15a3c0ea00062871583b0ea0005a85156330c400062761542107e00062511522007a000524f150,0x15790c42908268982789c4513c0017e57130398d8350b825090230785394c529485194450876001c4,0x13e8fc3e0080380c4193a0006e581124410e2c8aa2d8b42b0a4570b02a0ae29916288a04f138001ae,0x10a0001896600800010e2380e4370e65380003964409003f8160481a060140416041134000825880a,0x99077110681e84319c792a4aa2b00f2c40e2c0992bc151d06d1ac5d12c4911c3e058080c1500f63488a,0x8641805c6f1c87017c000c12f164308c05695c399064794e4e936000be5a026080220915031956208ca,0x880320b01f2d02f0d4032cc310ac180471c870399061d14e4e92e1b8003a16a4711a460380d03c0e836,0xa40280902a0a4b509c23080260881f2d0250841a09d499065393e4e8005b12c4a9281b0601a05c1985a,
0x149122],
[0x1724df1bdb6b6a6d49a133f67acf19bb35656ca58cb1862ec05802f05aeb596aad45a6b4968ad059eb3966acc58eb1962aaf55ca79432854ea9752e24c49291d2324147c8d51a23345488d109f73ec7d4fa1f33e47c4f81ef3dc7b4f61eb3d4784f01df3bc774ee1db3b4764ec1d73ac754ea1d33a4744e788610a1f83e87c0f61e83c8650c818c310610c017c2f05409e1282484808a1041602a0480880c81502603c0580a0120200300500800c00800,0x1a054027d4ed9d93ae73ce29c33826f49b9352664ac8a91322224c3e87b0f21d43886f0da1ac338650b61642174ae91ca393])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA05 : ¬ FormulaSat cA05.originalFormula :=
  cA05.unsat (by decide +kernel)

def cA06 : Certificate := ((9,8,11,144),
[0x12d1a4005633800986500180bc5c0918c005a30800ac5f00130ba002c16c00562616400542b800a05700148205500130a60027030a2002613c004a26800904d0002096000212400462200084470011400401f0f074380d10c002220800403f000787a001b0ec002c1c8006837000c06e00190386a00160cc002e050c4002c17800542d000a05a00030ac0002148004c23,0x1002b95a005580152a55500150a70028c4ea600290360051001409f00274009b4ba70009a4c80122274c0012c950025926004888d28004587d2400480011c8d002280088430010889001e112004380104803f1f0f424428004c83001b102002d1fc00563e800987b001d8e872381b8387900088ee00361d4005a39800ac7100130de00351b4006236800d06632058d600,0x10040e03040040822008003400fd7dbf800fc04801f405003e1ee007c3c400f579bd800f407801e40b003bddaf0003b80e007600c00ea74801cce500389c2006f801bad96f001b8db003544eda00361ae0069885ac006a001a0cf003299a006133400c86331030cb002e992005b31c00b46280180be5e05186005d30400b65f80168bd002e176005c2dc00b85a80164b1,0x20075801ce0071801a200598015e00508011e008e8021e005c8020e007c801d0e4703499ccc582b13c8c0047236008cc5e34008c06401160a8022a0089c4628008909401100e8021d0d0042e130c004282e008404c0106828020cff],
[0x1cd4a97cb80013b692848230004ea649904780013a61243e1e0004694488f474000fa4920,0x1080301c0a0a049b50600160dd2c803f9f8b0542d164ae532b148aa51409409e4e43a1400,0x11c3aa10004c2ba6480912190924002200046983419ccc0200810066c418005a97359a8d2,0x1653218cb64d26114761347a391a8c45a2912883112c88110009d3473391c436190d0603a,0x1602f158244c4d8401c0d2ea40bc471f984944330124849449a481e980625816974125424,0x18400135387c3d9e86a2f198b45023100c8581f0f0c4602a1a2685c981c0dc727d1b000e0,0x1273b9e0ec9b190b04c2200017cac4a21180a848994e00c0a6f2394300009f3a70379b82a140b858e8,0x4100d252],
[0x18c31822fc3e87b0f21d43886f0d9d2ba46f8deda9b5267ecf59e33766acad94b01600b5d6b2d55a8b4d692d15a0b3d672cd598b1d57aae50ca15392704de9a92f25d4b892523a464829011f2354688cd150af15c2b4560ab1542a4540a714c294520a31442644c09712c2544a0931242444808f11c2344608b1142244408710c2143f07d0f81ec3d0790ca190318620c21802f85e0a8130250490901082082a0520881081602a0400780700c00800800,0x326e4d49992b21e42c7f8e51c63846c8cf19a32c63])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA06 : ¬ FormulaSat cA06.originalFormula :=
  cA06.unsat (by decide +kernel)

def cA07 : Certificate := ((10,10,11,557),
[0x10008c29400178a50007e28c001e8a10009c27c002509f0009a260961089d0008c26c001389b0007e264001e897000922408e0c8950008c24c00100930007e244001e88f0008a234002108d000882182622c001f8890007a21c0020880060850007e20c001e8810007c1fc001e87d000781ec001d87b0000c1e400008770007418c001303f144001404e100001384100030094000480905c0005814028000500b,0x1000dc37c00350df000da360d6110dd0004e36c00130d9000be35c00348d033834354003344134800330d30004034c000f8d1000be33c00328cd000c433400320c60a0cb00030324002f8c7000c23001a31400090c3000be304002f0bf0000e2f4002e8b8000b62ec002a8bb000b9000b42c8b02b8ac190b7000742d400278b30008c2c4001c8b10007e2bc001e8ad000a8298a4288a0148ab000622a400278a7,0x1469180d91f00040474004211b0010446400451170010e45c00449100a9150010844c00411110010c4281c43c000910d0010442c00419090010441c004090500100414000410300006404003f8fc000fa3fc003b8ff000fd000f83d8f43c8f0198fb000e23e400378f7000723d4001c0f3000be3c4003b0ea3a0e6390543bc00188ed000de3ac00180eb000cc3a400178e90005c39c002f8e5000e038c00378e1,0x10014254400139510004c53c004c94d0004a5340052146510360c94b0014a524005283700143105480014252400101490003e51c000f145001414f5420013c50c005013f0014009c004dc314f8004e938070184f4004f1390013c064000913b0013308d38000224e4004d536001344cc004c12e0012c4c4004bc004a92849924488564b4001892b001204a400181290011649c00421250010448c00479210011c,0x10003c62c0062186001846240061c00609805f97c5e858151850006260c0018181001785fc001717d0016c5ec005d979001745c82c0a177001705d4005b1730016e5c4005b16f0016a5b400020045ac005a166001645a40059c00589605795c56868191650015858c00551610014257c001c95f00070574001b95b0015656400551570015352d54001525540052955001505394c1184254c00549510014313d50,0x174c001c1d1001aa73c00729c8719c47085a73400189cb00060724006c9c70005c714006a9c3001be704006f1bf001ba6f4006e1b66d03a6ec00101b90003e6dc006a9b5001b06cc006b9ac081b1000246bc006a9ad001a86ac00029a9001a669000689a7001a5001a06799c669981a86868c00659a10019267c001c99d0007066c001b9990019465c00649950019064c006398c628380d9910004063c000f98d,0x10020e84c00844008320a822068106c1920f00202834007fa0b001ec824001c207001e08140080203001fe804007f1ff001f47fc007e9f87d848109fd001ec7ec00131f9001e07dc007c9f07b83a0c9f5001ec7cc000f9f1001e07bc007a9ed001e87982e099eb001e47a400781e7001e279400781e3001de784000500c77c00771da001d877400731dd001db001d6751d2741ce1b1d9001c075c006f1d500072,0x11364e0024c92c00930330023b0fe4a002479064800240924009124209a470024691400918270023b0c64400030914008da430023e8f018904009023f00240064008ec258f8000923f002368f4008e8008e23700235002338b634002328c4008ca2f002271d630002191c62e0022c8ac008b2290022718e2a0021917628002260022488c0087a210021c86a1f000248740085a1b002180021485c008540084a10,
0x10028c0d400a2441a2800a1e85a2000a1a890028609c00a101b0028406400a0a810027f9f6800027e03c009f0030027a9e4009d2770026e9dc009ca700a275002689cc00992710026c9a81a9bc009a26d002649ac0099a69002669940098c009865b988009825f002609740098065002491ce5e0024897c008ec719700096a590025a14c009245f9600095a550025393654002529440094a4f0024913e500023b,0x1002bbad6bc002baae400aeab7002ba11c00abc4fae000a9c4dad800ad2b3002b4ac400ad037002af106b2002a70feb0002adaa6ae002acaac00a9c31aa800aa01d002a6002a3a86a4002a2a9400a82a500010a8c00a881100006a8400a80070029f0029da669e0029ca6c00a7067002891ce9a00298a5c00a60550029814c00a245fa5800a529300291a369200290a3c00a40450029010c00a244fa3800a328b,0x1bcc00bc6ebbc800bc2ef002f0bb400b8c75bb800b7473bb000baae9002eab9c00baae5002ea16400b8c63ba000b745fb9800b3c5db9000b8800b82df002dbb56dc002dab7400b52dd002d8b582cb6c00b6ad9002cf0c6d800030b6400b2ad7002d2b401eb5400b52d3002d407c00b3c25b4800092d3002cab4400b3800b32cb002c9002c7b0ec8002c6b1400b1869002af1cec4002c2b0400abc5fb0000afabd,0x1c7400c78530030717f1c0031ac6400c5f0fc6000c5b1500316c4c00c5b110031610c00c1c4fc5000bec4dc4800be44bc4000c3b0d0030ec2c00c3b090030e0e400c3833003071070c002fb0ff0a002f90f70800305c070600300c1c00c1303003040b400c1027002fb0c702002febf01e0630100300bf400c001f0030006400092ff002f908efc00022bf400be800bdaf9002f4be4000480cbdc0002002bd400,0x1d444fd5800d435700354d4c00d503b003540dc00d4441d4800d3f4dd4000d382b0034c08400d2b490034700345d074600344d0c00d1067003391d74200340cfc00d033d00340cec00d005b0034015400ce463cf800cdc61cf000cd45fce800ce000ccf31cd000cc82f003320a400cc01b0032ecb400caf29cb000ca8150032801400c9c00c971fc9800c932300324c8400c906b003071cf22002f91bf200031e,0x104400e40070038ee3400e2f89e3000e280d0038800c00e1c00e1781e1800e1383003791d78200380dfc00e037d00380dec00de463df800ddc61df000dd45fde800de000dcf71dd000dc82d0037008400dbb6d0036bda76c0036a05400da8130036802c00da0090036700365d876600364d8c00d906d003641a400d4473d8800d835f0036015c00d445fd7800d735b00359d575a00358d5c00d60490035811c00,0x400dbc00d2c00cbc00b3400a0c0099c008e400e7c00e5c00e3c00d7400c6c00b8400afc00a54009ec0095c0089400ddb5acdb18b7abca4a789522200374d4334c1adcaba889da4888000db348cb2f8b2aa4a02648da160039ee7400e6f99e7000e68130039802400e5b9500393e479400392],
[0x1440850000ea8c11890f20800038a2e460430850000c68a91790b2080002ea2845c41c829032040010e21f45a,0x1aa91b93122c00038a5c46c4a08b00009a9391a92522c0001fa4a46847c8b0000629111991922c00012a3e464,0x10002eae4478620bf800062b611d9822fe00012ad24745c0b300009aad91c96b2cc0001fab04705a0b3000062,0x16e0d080009ac49209b03420001fb0a4806a4d0800062c091f99831e0003aaee47c648c78000c6ba11e9902fe,0x18a113a262040017c2a448c821008000eae0922a0440200031b7e48876ce90000ead09219d53a400031b3e484,0x183d16223000be4092480128350720c01002c0520f4460003da474307f4f01cd2fc51c9c9152068b115a2a452,0x16c80d0190420800e01701a06c0b00c48e6fd1080011827d248010007ecfe1f80046750620e41a678d019f3fa,0x14dc9a02f05a0981502302403c068290440440700c48e0c8188332700c0000b41602a02f89e4940780f9ba37c,
0x4040eaaa92d43c870002dd13e9300f82103a0103d8300800201c0f64f84e4964909011a0260400a81404a4b81413025e,0x1930cd02a04600062828326dd5e09340c01a29a498a792c2a84aca99292a0490a614a240520040639252582002e0003982c,0x40060cb552402749e04076a660b0158001160208d0012f0b149c4bc9b82826809017a4a05665ccc82705c01c1682647c,0x63f3586b8d31853028c89111b49e490c011d2fc45514a2600808e474a0604c2a3234c46cd7124354480c017e452,0x171c9b1c826e7049782804e0911e99132c6541319b4989341180d00032d863000c4bf033452724ce00418239a5123c,0x59c2701680007b94d09211420588b01642c684d1200054a948d31ae356614c518130e00d199214a0630c59c4266,0x64833e919290102e22d83206251d0b9ee37e638bb1552864b48485d0668a112a224428810fa1e43a8710da0b3be,0x14d09b92f05014813a3d09c090c884d478658ca9940560b41324c3369352884c06a0d0a29462886750a21642a,
0x155cae95b3bc770022c1021618620ccef95e060000530674a8868ea2030a014d031d93ac828ef2093ba9152182e05e,0x4ea0e62352b01044e9700409f1790e000c35352264451b23003012c0048e8a00009638a552ac530a5148010b0c2405009d211593b4,0x11381212e2604bcae9372b84d8ad133298490083210b0a484605c0206f0018380050400286aa92d00853e1e4385789c114000576871d8,0x60948a01d058000c6960c223a31a6251d8034a600012a57040d464b0400981402700e8c48911321a8b8268532b0,0x19582b0590b012c2a8570a21292aa540a409d2c0374ae1502603608887c5c010874041baef80c1be6f0a650e96503a44414,0x11852d04d0a68b8279d621a0f0ef113070774891494868c4a602e2b40bcae1342ba4dcab92f05a0a12482c04a,0x182cfb9df3920208493c3792e17b2f25f0bc1772fa0003985f55e96c00275765031de41477504a4348a0516f838b9c000ea,0x14d00441d0b0128150265292ca540084942d04c00091a108b4830374ae94c1a11b002b78095c40c48e4fc9f0082269d13900843e2744a,
0x1154a114039e744e703807874d0104f09c14c26a2e3b075886a053bc44d051dd22482521a3148a0b8179c726c,0x116c1011377ce480422f4409e0e617d2425e3ea7c8fb1f13de7dc00111d452e9f63ea7c4f91ef43271099a5b0005fd4b096,0x42804a054a1013280528e794c3a2524000e713c2984d3a68b9010181d2280001cf2d24505c929270262640608486042c0021a0610f,0x10006a80035c2e05e0b42724e26c01283848010ea8914841c606061fb1793013726c4c09992e4bc4e0040cd97ce21c74329752d9c8382,0x16286e86a0be1101c2af4c411c230452e28e4ba1730880a033a8e85d14225000abc6e844574984002d9758869de226,0x189cef8005109dd3197c2f45e0620c317c3085e8bc1765b4baa612ee318bb0c743e5f462800338668cc18e318,0x40812202093c39320004f2e99d83bc7752182e4949812482c000aad4c2927389e94228209d2c01201a010eaa784f89d93a272,0x1415330690d61a0398770c61c4310764b01e43d0780004a0921100ac0a8822654c42e0d79b43669192900055e,
0x13506f0d31b6324641f93f87e9242464a438cfe8e4458384001d23a01b0de2672ca584af85f0bc18430252000,0x1570ad0680c855134923238865319a535c4211691820c95d2991722a898003746a0cd182aae510c19340df1c0,0x1524043010811a80855c1449c0409b1480114d43061e0780d0098640047a0023f4502d0004c0a11350a21462705089b14a298520002bc,0x1948df97625a8850fa1c00054ca803f4da210438800099ec15232a108d4d853ca69542a65400215543c001448414d6,0x45b001c8c5d001c9e0b0084075660cab86808c09e9b84b8901246dd1a9bb3745c8951be2ea4b0da96e24e9011c23448c,0x400146000a50006f8d81a01393794e2a810ca98402a09ad341e93588fc1d03b0093dc3d0a103448494970002510308087c0e4160fd,0x5b636a6d0d90001fad2000a161e0f9004b0aaa1740096f878020f7ae8aa94261c9c0238462a4550a7043080124240040880f8140a1,0x19b8f61ed3ca0a090bb008114ae21212526f11e9713009208a2241f8884920b11ca4035e9b04a08b2e85ccb9099130,
0x12491c8991285cd232520030d555284ae9389a20fc6a04088010e214419830f86343d9891226b51d8972a20106cb62,0x4088baf80720c619c312661b209d2c0cb4ae3546501473671000736ef9141c2000463604e4240db8973766e8df2702e4,0x13380a087005ca80286dfd0668b0fb8014c7591b61180e957a733c478d329ef3c21d0f88cc19a35c6d0d645c75c040db360000db,0x1555160003fb0fa1e3ee00084e2c9d0ad25f2b8374aea672ae370691f4050954689f64c009868272492094b60274b0,0x42619e0fc229754e492536a411329c53609437a6f0dd0044c6671461925106419d3f2850fe2163f4020ffbfa000ffaec,0x154d339541a4538688431a0100f21e84dc9ccf39e63da7a84b89036e248dd8dc3727d0242554de5bcfb25c4c0,0x4056bafb9c900337d424ec9c4ba96d11e220d79b43646f93a0894da25045899130011f3c4287c001422aa9d52f9501ba,0x6553ec0a1300264e409414053578000515504f08c4ee9d53489d386718048c1278f98284aa7d81300026b360a004e96004141,
0x4c60f20124898e1e80248d024e498a1e02d00061c550a52782b497c4fa692b8274ae89e386718e41c12ae4d09b9f325e,0x19812e27704c0800d0400302305c8b83662384683f4806bc003bf9d83906d0c61c4360640c49983b0007563284094e0cebf,0x1151f680249d361781c0e11372602ec37952380300970491741b8aa1ae248538d512034a468218130201200a8144aa,0x1948bb21f000551872790e61dc351f00cc7d8f99672d4990620bf18670c608be38c714998c217a1d4e416946e,0x5aa34a115209bd3786f93ca6b023716774b80234180c174003d33d1734725d42296d0012348a4960104a8961349e0004850306ec8c,0x52b2524909000012a0c0430902293e9f09301a25806095a6b252530920220eb3d01836696a1c0005513d80500c0fd379b935c,0x16f4df1b52e25d0ba96e25849c49800ee736a604f82653d8864ec001218fe001218797cc00e6e0025b003988097bc3f4fa0680c126258,0x1450708b50b40003a96c4fc1f4d188234e59c8d1ae2d4490d61692428fd1ba330740ec1e8043f2221fb4c89492b372,
0x5cf1ac2c0eb8d81649151f0af1562a4220b99813e0d91661492c0cb02235cd51940a2688016f4b60b6002659c82dc2e80099601049,0x10cd1522844a88cfb8017ae7f8017aa131fe4fe7fc56a0015c7f8588cc4042d066a0532635d0519b1583690499a154,0x10007bcfc4dcfa02e25e7d9250284e4016de9f4955300264f8074d9c1a519071444180c65ea0016c189cd28e85d079010ba,0x13ec7c9341f83dc760eb3a0744e70ea0703a01e0e91ce13c730531ca134e59d345c730000fd728ef11314e0007c950,0x10026384c9f0089a50207899c519070c9288830121c9005e8802a4dfd0083adee00429e2c00839e2243c870fb80451efc0261a4a007e8fe1f0,0x139c730e539674ce61d8394778539dd15090d3f02e49454c161541ec3d40a94e4fe04c218ee19e0fd3e8dc090,0x15413784546a4a8961261e0798f69eb1e83cc7780821606aeb434899f4224140fb1d6462968a8a721d43a0788ed1d2,0x18850f9df000130133565045d4ba16f2e25b1370006b2d903f4fa0237ceac23027841066a04692671a23746825f084,
0x10809ab9c0b81c24a0783d87aa810581053f84002aa01378131e41147703f4fa9812e27c0084d4244560e145020a4b7e5d80414d,0x4403c879cf69ec3d0a08791ee4440006cd065d0b89752de5b1371b136c6f8dd0f43d67b4f30f000844410272e80e53a2,0x15402026f0015868308aa101fa7d0909713e04968e262850500949781426e0413514804c0005e846009678014840ab1342284500,0x40411400462b6c6d0b796d24c00652b785cc952414728d542a841120fd3e8984f6040b5bdc002a9c4401644d0c550a7153086,0x179cf69e43d87a137005d66b61b14d6],
[0x116c2d45a0b31642c4580af15c2b4560ab1542a4510a114027c4f09d13826c4d09913025c4b09512824c4909111c2344588a1122204388610a210418821022003f87e0ea1d0398720e21c03786e0da1b03586a0d21a0338660ca190318620c215c2a8540a61482885009e1382684c0961282404708c114220330640c41802f05a0b01582a0520a01382604a0901181c0340640c01702c0540a0130240440800f0160280480800e0180280400600800800,0x144688910a2043e8790ea1c4368690ca1842e84d0921142083906a0c41682904a0840e81902a04406809009fa3f27e0f99f23e27c0f79eb3d47a4f31e43706dcdb1b53686ccd91b134868cd119d33866ccd18d318614c2183304604c016e2da5b0b59672cc594b190c2164288490820e418828f81ee3d87a8f41e63c8788f01de3b8768ec1d63a4740e71cc394720e11c03646c0d71ac3546a0cb18c314620c3184304600bf17c2f45e0bb1742e45c0b7,0x1684d05a033e67acf19db39670cd999b32660cbd93b2664ac718db1a632c618bb1662ac5189b1061cc2d843055f6be97caf85eebd57a2f35e2bc177aed5d4ba173ae65cab8d702dd5b4b4167ace59ab2964ac658ab095f2bd578aed52aa4536a694ca9852ea594aa94526a4947a8d514a2543a844f49e53c2774ec9d1392704de9b936a6c4d69a934a684ce991312614bc9712da584a093d272454829011fa3e4788e91ca3846e8d91aa344668c912a24,0x19db3b275cea985306604bf8d91ae354697cef95f23df7bcf75ee3d37a2f21e3bc4780efddf3bd778ee9dbbb4762e9dd33a5748e85d039d738e65cab94722e3dc7389710e1dc337d6f6dc9b8b6e6d4da5b43676ccd91b0b5f6bcd6da8b5069ed39a6b4c696d29a4b4868ed19a2b43])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA07 : ¬ FormulaSat cA07.originalFormula :=
  cA07.unsat (by decide +kernel)

def cA08 : Certificate := ((9,9,11,216),
[0x13a8007873001a0e2002b1bc005236800906b000d8d600331a4005e34800c862300b8ce002b1940052318009061000c0c2002e168b02a2f800ac5d00148b60024164002c2c800a85700148aa002814c004c298009c1a28800904f000909e00250389a002412c0018258008c490011092000411c000222800843d000802a29000a04416138004417138004c240c0004819,0x11cac800b0002b95a005500150a70029144005029400a300279389a4c25868a1000f13e001d27400384d8012899002292e001b25c00924a8011c9500240389300229220012244008c0823c008a46800308d0022116004322c000a4480008870021104004021400744280106003f1f0f4783b0f90200211fc00683e800ac7b00148f200241dc00403b800e470371b0d432,0x10039dcae80039816007201400e300385bae200381be00700fc00c120b7800dc6d801b833003046eda00361ae006ab45ac006a34c00d417801823169001a0cf003405600608b59c006632c00c962b2800c60d32400c863801901b003044ac6003018e001231c00c461801880f0030432c2002fd7ac0002f812005e00c00bb002e56aba002e16e005890d6c005a2cc00ab,0x1004ba5a00954a40124938024127004883d250009246008f04a42008e47c00188f802351d004623a000646c00068c8022d150044a220087c2e200087434010e0e8021c1b0041c4b0c0042a120085044010a078020d090041401037fc10010280801f64380001fcfd003a46efc003e800f87b801e8f3003c5daf2003c1de007807400e912bb800ec75801d811003a432ea,0x1bf084017c0a802f600bcdd6f400bc5dc017121dd80174b9802de3bb9002e000b65ac0169b3da8016811802cc1500592c600b057c015dadd78015c11802b81f0056ab200ad04c01570cd600155a9d58015406802a40700544014fa5d40014ea68028a43a600295490052a8e00a50d401451ed2001431dd180144005027e009e4ec01369c8026814074dc00189a8026531,0x1005b4016100504012f0044c00f50033400a90060c0165004f40133004ac0117003e400d9002bc016eb150a753094451ecd656002d55e9f4e25926883c994a60060b0200bfdf70000],
[0x1bb1ba5394200086a61b8519420007aa41b63f8f800086801b427096000865b1b22609200072591b0,0x1078b62e000289906f98a5c96850134460f42f8906b9ac6a9a8699a4689a000270931bc5e97400086,0xac0af00121568e10200ac162a814060ae2b0bc6f822080be68800299c02a0a62900e030120401c2d01a,0x10e8c8330c20c02a0f83c0e02e098360b024700ce64000240d27115a561564791c489205712649128,0x11d9c8370d83485a13056121c41404212858028541182614844091c01805e188de170002408471834,0x1729765e18c5f9445f14a6e952541b85a93e4d932468f6338946719a66196651926418e6015400086,0x8009810ce71d4731e4781d8080211b8001b0f4690008411a730fa390e2380661906a1a07e1f0007e12e,0x100268070467408820886729b06d8fc2694c52102281524009e540846d1b26e1c82308e551042888a,
0x14c12e5a1ac00244939d461186021826219e000520a9d25b1704e93c6f12e709665916e5c9686b9ac,0x12b0ba2b8bc460be699a200192631d84e9d24f0066f004751d04a938008001201c0c1d6589664b1c2,0x21b0107ed82349dc0a0c00c0c43082e098003b6003045f340ed3ac55168081f9719ce200781c10a7310c45910,0x5dc2a8b22c0ae760bc368d815026148003f67a17c31348d10b800324e03bc1918c1d19464198ed0007dc26,0x81019cd4348dc77846098004be2f01018cde00030bc0081a31d0ec1d8f03b8f23a0701e878201ce1605a138561b0d6,0x23d0ec8922c843ac39000ee1685c3c006065460626985c001826e1e20c0348d8550081940a1284c10048341dc,0x1138080a66b22c841b46c0aceb1b8ee0e400168f1170f00184440008e6f000115e413040128d002848350d273880,0x11c0e83c9e81e00405e8c1e8d3348003d4080d13b0741c80019e3d100e738cf3000f03d0081c179000249e616858,
0x1451164390c418007306c],
[0x1526a3943a8650a9ed3d2794f09dd3b2754e89cd392704d69a932a5d4b896d2c2574a894928a5049e93926a4c49692924a4748c9051f2354688cd152294502bc570a714c294520a31442384688c1162284488810e21842884106208408800fe1f83e87c0f61e83c8700de1b83686c0d61a8348680ce198328640c6188308600be1782a0500961282484808c1082082d0500941001c0360680c81802e0580a8140260480881001e0200380600600800800,0x65ccb896f2d5dd3b876eec9d83a6748e69ccb9872cdf1bdb716e0dbdb6b6c6d6da9b4b686ccd95b035f6bcd51a934868eca994b1e636c6980b005ecbd56c2d7598b2d652c9590b1d632c555eab9522a3544a855029f53ca6d4ca98])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA08 : ¬ FormulaSat cA08.originalFormula :=
  cA08.unsat (by decide +kernel)

def cA09 : Certificate := ((9,9,11,193),
[0x1361f4007b001d8e872381b87079000e8ee00301d4004e39800947100100de00351a0cc64310a8da001b1ac0060348009c67000c0ca001718c005e30800ac6100170b4581117c00282e8004c5b00090b2002a148a01a2b800405500078a6000e144004c27800944026800904b0011096002305092002011c0042071140040218007c41000f08200040fc00021e8007437,0x1003385a006600194c9003198a006330c00c05f80178bb002f172005b8016ab15b00168b3002b476b2002c15e00538cd5c005600154a90029800a4518013ca10027c009c4d001309d0026c00964a249208e1626400364b8006895000c9260046244008247801148d002191a004405916004122400840821c0082428010083001f906000520400043f800f87a001e0fa00,0x18d001fe2f8c0022d150044e17140044a22008943c01128680224230040c5310004044f0e003fc4b0c0042a12008541c010a82802141b0040c4308004043f06003fc3b040040800fc7d801f0f7003e1ea00793c400ec77801d0ef003a830ed00391d60073049d2007239c00e272801c0e500031c6000338400de6e801b4d900369ae006a801a6cf6a001a4d10033476d0,0x1b3d96d000b302c016402802c5610058ab600afd76c000af054015c07802b357ad002b009005580600aa802a74faa002a5510052477500053a9a00a752c01491bd3001471ad280148005128600a2504013e9e8027539004ea6e009a802672f9a0026531004ac7730004ba5a00948d65800950024d250049a4600908023f1d900023c390047236008e464011c158020231,0x40145004ec0127003e400db0031c00bd00294017f005c40163004fc0117003f400f30037c00cb0030400ab0051a79288a3e9e0dc642f95000a14e249007b3b9b0c45d28801409b489fcf47235984b850002fd7d005faee00bdde6f800bd064017809802eb73bb002e80d005c80e00b85bc0170b4802db6bb7002d817005a82200],
[0x19818c368c6000528818a330c600042841882709800076681862107e00076591842007a0006657182,0x129092230766017e5f17a5e1765d074001fc721924791400076a8190461140006ea618e408fc00076,0xa94a428c561545815ca92e000394cb2b0892187d18453128470f0080295c800801dc651564410a3e0c0,0x10701a620ca320d4348d03399466192658002ba14669505394c2e0b42f0ba2d8b2659545c00077998,0xb1c91240c8000920003733c1404c12044c51b06b1c4701bc6e1c8cd0581500809ce65a0003099c0801e,0xa50930080101003264b6000413441c060171d4741e0771d81b33c1a338020471204c11800332386811c,0x15b800469a84e9384d85013854149425b800419a64c12e4b010030140480e029a24d16c000966912a,0x12407c1c84c5a96859964589605795c491083d8a22286e118006a9404f93c170581805e1685669944,
0x1278864818c6198464042110f23d1a00f832060160f1a40e9a21a99e1019c1c04a438e6310be2a096,0x1568fe458681b0646a062698666090026882469062808848904],
[0x1632c05802f65eabc16c2d7598b2d652c9590b1d632c555eab9522a353ca6d4ca98526a1d432854f69e93aa5d4b894928a4c49291d2324147c8d51a2334548a5142234422bc570a714c294520a31442384688c1162284488810e21842884106208408800fe1f83e87c0f61e83c8700de1b83686c0d61a8348680ce198328640c6188308600be1782a04b0941242404708c1082082f05c0b41402704c0941001702c0540881001e0200380600600800800,0x192123e4748c915226444678cd19631c618c117e1f43d8790ea1c43786cee9dc3b7764ec5d83a6748e69ccb946f8dedb8b706d6da1b33656c0d79aa352690d1da133f67acdd99b32654ca59432764cc9592323644c859031e])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA09 : ¬ FormulaSat cA09.originalFormula :=
  cA09.unsat (by decide +kernel)

def cA10 : Certificate := ((9,8,11,133),
[0x100150ca0031800bc5c2d160ac2030800445f00120ba001b16c00322c800505700148a04e261282c5500078a60024144003627800644d000a0960023124003e248008842200508e001b1140032218005041000f07438090fc00361e800643b000a072001a0dc00321a8006033000b06600170386200140bc002a050b40028158004c290009052000309c000212800441f,0x15a2cc00b05780158ab002a400a751aa000a652801422352001441900280009e4e80134990025c009548a580094498011a2349001208f0021c368e00230008a448010c004220800804280106003f1f0f4783b06102000f1fc001c3e800347b001d0f200351dc00723a800dc75001c02073001a8e20036030de00351b4006835800cc6b00020d2000219c006431000c065,0x180bfe04008004400fe06801f6f97e001f409003e00a007b801eaf37b001e821003c82e00783bc00f070801daeb77001d815003a826007439c00e571b9800e407801c40b0037dbae0003780e006e00c00db00365aada00361ae006788dac006a34c00d4688019e1f690019a1d680019c006532400c70031582c60031186005e88d8400602fc00bb0eaf800bc002e16e00,0x40105003a400cb002e400b5002c400ad0027c009b0022c0107003c400cc642e96cb2572a93898440020cfd004120600],
[0x1d645164ae000fb4912522780046c24411c8a0011a910e3f1e0004692430f474000da390a,0x18d31184c00200810066a3c800528c32990c6080301c0a0a049990600198a1165c2b80046,0x18f2da24bc5d45000be000fa38d2683385020160a84c1e0c09038168b08835186b3c80092,0x11e0c02c3a1745a304a242b1389a4c25910863b1320902803f9f8fa7c3d9bcbe55118003a,0x14a210dc460035240f0502c144b4542f14cba8845084446d371b0381b47080348d0f86418,0x12e160c05e321b0c45a2b1a23c6685230f89241241010e8601817cd41805d3812890ec3913210de,0xb91c4e028138a852903b9e800913a9d0e6],
[0x18c71863045f8bd1722b44989111e21c3e87b0f21d43886f0d9dd3b876eec9d8bb074ce91be37b6d0d99b2b606bcd51a932a652c05802d85aeabd5729b532a6149a8750ca152ea5c49291d2324147c8d51a2334542bc570a714c294520a31442384688c1162284488810e21842884106208408800fe1f83e87c0f61e83c8700de1b83686c0d61a8348680ce198328640c6188308600be1782a04b094124240420820a01001602a0400780700c00800800,0x18e519e33465])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA10 : ¬ FormulaSat cA10.originalFormula :=
  cA10.unsat (by decide +kernel)

def cA11 : Certificate := ((9,8,11,137),
[0x12e168b01e31800406100128be001c174002a2d8004c5900150a45027130245700070aa002514c003828800544f000989a002412c0040258008c442104092001c11c002a228004c43000f8783a0710400381f800543d0009876001b0e400301c8006832060dc002a1a8004c33000b8580a18800542f000985a00140ac0026148004827000884e0003094000211800401d,0x15b0016800592c400b2578015800552a400aa5380148a30029142004f8013a994f001389b0025c429a002602a004b0012893002512200478011a8b47001181f0022826004421c008842801048100208fe003e1e800783e800f6003b1d0e47037050f2000e1dc001a3a800307300058e200361bc006a36800d06d00020d600021a4006632000c46700158ce0032800c05e,0x181c06080081044010007801fafb7f001f80d003e816007c3dc00f579bd800f403801e403003c400ef75bc000ee76801ca2176001d4e9003a9ce007186dd00070865cc0072001bcdd00379b6006c801aed36c001acd50033442d400349a2006933c00cb0db4000c90cb3800cc003198a006330c00c1002fd76c0002f97a005a88578005d2e400ba5b8016a1d5c0015a17,0x10043c00f90037c00c7002cc00ab0029400950022400830041c00e26e32988b054289248640001c0da643095ca650241087e0043a1a0085c261800850240108028020d0500419fe00],
[0x1ec47174b00010b511a522680042bc4613c9a000eae1164e250002eb645108800010a6912,0x10c048381a0b04018140702a3cec7e000e5206e369b004010200cde870009d1e683180042,0x12c159ed100036a48ea743985824180b85422900a0400c13078151e773f0009691391c4e0,0x16a2f1a51a8e3115c9849238fc723743215088341205007f3598000210da4cf4793c0a852,0x1060f8640a8f1a09c4c612b12c90461f0e06c351401c08e8a3d1989400ba4a1f4b4652e19cbe,0x144349788630472351293188b846241d8f0741e0ea2d1451280b524220e244421b4808034,0x9e0e8761e1207446004614ca8940501b49c4c282a8f44a004a9f0b264178c8cc5b209a8be],
[0x18e91ce3846c8d71aa34be77caf91efbdd7b8f4de8bc874ee99ceb9171ee39c4b8770cdf5bdb726a2d41a3b3b672ce199b3265ec9d93325638c557dafa5e2b4167ac6574ae15bab254ca955229b51ea3543a7a4f29c127a4e48a2d85a8ae15a2b0558aa1522384688c1162284488810e21842884106208408800fe1f83a8740e61c8388700de1b83686c0d61a8348680ce198328640c61883085709c1342604b0941142202b0460580780700c00800800,0x192f25a4ac948fd1f63e478])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatA11 : ¬ FormulaSat cA11.originalFormula :=
  cA11.unsat (by decide +kernel)

def cB00 : Certificate := ((10,10,11,528),
[0x12282a24c000d0910008623c001e08d0007422c0022000210870007e21c0020880078850002820c00098810007c1e8161fc000707d0001a1ec001dc78000761e4001d077000761d4001cc711d0001c875000701d4000307300072034000107100070014001a8591bc001b86c168001b86d16c001b05b000400c449000481083211c001083311c00118440d000110350002807400040090540005012028000480b,0x1000c831820078cb000c432400300c7000c231400300c3000be304002f0c10000e030bf00006010bd000ba2e0002d8bb000aa2ec002e4002d0b22c0ae2b05c2dc00278b50006c2d4001a8b3000862c4001e0af000742b4002a0a6290a22804a2ac00278a90005a2a4002245929800160a700086294001e0a300074284002709f0009227c0026898258940d89d0004426c00218990007825c001d095000902388c,0x10004443c001090d0004042c003f10900104409003f82c41c000d1050003240c000c101000fc3fc003e8fd000083ec003e0f6000f43e4003a0f9000f7000f23c0ee3b0ea1785c3d400370f30006a3c400330ef000663b400190eb000e6390e2380de1304a3a400168e7000d039400330e30005438400148df000da37400360d6350d20e03636c00340d9000cc35c00100d50003e34c00338d1000cc33c00328cd,0x10f94d0014852c00519490014451c005094008820514004f9430013a504004f13f0013a4f4004e13b001364ec000400e4e400020064dc004d8090013601c0016935000544cc00149310012e4b0004a92f0011e4bc004b4004a12649122480604ac00449290006a49c001a1250006648c003f1210011c46918459141391f0005a474001611b000564640015117000fc45400441130010644c004390c429080e911,0x10018c63c0062988619840f18d0018262c005f9890004061c005d9850018060c005f9810017c5fc005e9780617d0001c5ec005d979001745dc0002975001725c0005b973001625cc005c4005b16a5a166590601796f001565b4001a96b001465a4001996700064594005815e5715a5604e131630005a584005295f00146574001515b000525640055157001525414e5303a0e1550014a54c00519510004053c00,0x174c006c9d1001ae73c00729c8719c40b9cd0003472c00701c9001b271c006b9c5001c2001be704006e1c1001bc6e8246fc006c9bd001ae6ec006d9b4061b9001b26dc006b9b5001b06cc006b9b1001ac6bc00029ad001ac02c006a9a8001a66ac00669ab001a9001a4689a06799c189a70018e69400609a30017e684001999f001766740066196651926405066c00169990018265c005f9950005464c005d991,0x18440084a0f002128340082c5b8400080459838007ec558300082605828008220700201116060020480c008043580800800007f9fd001fa001f67e4007dc007d1f2001f07d400791f5001f3001ee7b1ea7a1e6189f1001d87bc001a9ed001c07ac006c9e9001ae79c00789e0779dc7685079400169e30005878400701df001b2774006b9db001d676400731d9001d4749d07383c75c0070c4575000111d5001c0,0x195c009681f0024f0a6580024d09e560025494c00952510025405c0093c1d948009341b940009380092a4d0000400a4b002490024790e4800246914008fc6d9100090a410023f16e400023c8ec008e23700235002338b634002328c4008ca2f002291b630002271ae2e0022c8ac008a45b8a80089800892230022087c008740086e138700086a190021a85c0086a150020b1b618002011ae16001fb19e1400212,
0x1a4000a3a8d0028ea2c00a3a89002870d68c002850ce8a002830c68800286002820027ea04009f2810000e9fc0001a7d0027b002799c67a002789dc009e275002789cc009e05d002691b6760024f19e740024d19672002709bc009c26d002709ac009c04b0026916e6e0024f1566c0024d14e6a0026798668002669940099a63002660dc0093c41990009343f988009802b0025e9740096e559700096a590025a,0x1002b7116c800044b2400acac7002b0b1400ab2c3002beaf2baae02cb0400b02bf002c00b400adc35af8000d2bf002b2af400ac2bb002acae400ad800ad2b3002aeac400abaad002ab002a9a86aa002a8a9c00aa2a5002a8a8c00a646da9800a1c6ba9000a1469a8800a829f002a0a7400a829b0029916e9e002871669c0028515e9a00297a3e9800296a5400a5a9300296a4400a1c45a5000a1443a4800a0c41,0x1002fc13c00bd45bbe800b9c59be000b9457bd800bceedbd000bcaf1002f2bbc00bc83b002e7116f0002e510eee002ecbac00bb2e9002ec0b400b9c35ba800b9433ba000b9800b8ae1002dfb76e0002de04400b7009002dc00c00b6c00b66d3b6800b62d7002d8b5400b346db5800adc6bb5000b4ad1002d2b3c00b345bb4000adc59b3800b2ec1b3000b2acd002c0b3400b22c6b12c20eacb002cab2400b283b,0x1cc0190032ecb400caf29cb000ca8130032801c00c9c00c9721c9800c93230032418c00c905d0031d1b72200320c7c00c80510032012c00c745bc7800c6f19c7000c683d0031a0dc00c602b00316c5400c4f11c5000c481f0031006400c3b0d0030bc270c0030a04c00c280d0030801400c1c00c16fdc1800c130300304c0400c12ff0030418400bd46dc0800b9c6bc0000b9469bf800bf2fb002fcbe400bf2f7,0x1d8c00d90630036418400d746dd8800d835f0036014400d804f0035d16f5e0035bd675c0035a0f400d683b003580bc00d602d00356d5400d4f51d5000d48250035208c00d40190034ed3400d2f49d3000d28130034802c00d20090034700345d074600344d0c00d10630034417c00cf46dd0800d033f0034014400d004d0033d16f3e0033bce73c0033a0f400ce839003380bc00cdb3500333cc7340033208400,0x1c5c00ad40097c008f400894007fc00dd400d3c00cbc00c3c00b8c00abc008e40088400e2400d733cc72f4b32989a23e8a20a00354cd314b92b2a125c8ea227f000d332cc32e0ab28093236879f800388e1c00e1783e1800e100f0038201c00e0400dff7be0000dfb7d003771af7c0037ade400ddc59de000dd800dd37300371db77200370dbc00da429db800db36b003690776a003680036700365d876600364,0x400d5c00cdc00],
[0x18390a8fa1e40002aa0c4283dc7a00008a819098f51e80001aa024243706900008a751088310400002c8a6420,0x100014a5843447c8e80003a9490c90d21400035a2e4304047a0000d68590b9001e400033a1442c3ec7a0000b2,0x1524a300006aa310f94728a00018a8843c4e48e8000ce9d10e93223a0002aa6c4384b08e8000829910d92423a,0x1b211296a2ca0001aabe44856ca30000d6a911195528c0002ca9c44453ca300008aa511094d28a00020a90440,0x10002caf845463cc400008abc11498a3100001aaea4505f4b28000d6b51139792ca0002cace44c5c8b280008a,0x17d0f88000d6df1179f23e20002cb7845c7b4f5000052db9169eb3d40000eb6a458670c40000d6c0115995310,0x17e4fd1f8282510a19fb3fe00140a313f8754df1a830e588899081e281902a0440680900a001e00014024c460,0x10610c91e2444849012846407c0f2304624a50580010e8cc0e81c0368689192724c495182310002152d232284,
0x1030180342684fc9d83b0720d4168140640d8170170700241b82f4660f81e83f2800f0000780d41b11a01a032,0x1c911b802002000c29d330c750c21d10c418cea98740c80c000fd46c750e99d200029c541d540c000bba35016,0x1000cc17e0ba8e05a0bf166300d78be1642f4589b036a2b8dc1b715a2ec57a3518631060800632678c317e0da,0x1a151d0f91f03d909a12008001050354726d8dc9b31742d90e0b826c2b89f8b715a4ec5aa35184310dd140182,0x15f89312213a1e0368606488eca40660d01b83d07b0f05683b06446c1f83f87c000a894512624441080060058,0x5b800018c284661f8ed1c2358590949142123cc3fa0f41c8350620b4148250407c000c657f2f4598a894c20a33c,0x11a03c066336624fea3a31862cc99924520a4151ae3601950f14b29454ca802644019c0a0b036a8e41381746e,0x18a91121500028cb546a0a011a331840604d9880604cb7468cc116128041c6087c0004752613a24c3c06d0b28f03d06e0f6,
0x1050c097b15c05d130b715a19c122391781dcce95c204858d099f33c57cae905206688b01063325607f027044,0x47547a0707c80842d8c31654cc9952324884000eb4b49813a27c4fc9b21c16c2e8d99b94765f8c00b82546b412826042,0x4760d2020f8dfcbb965126244428302e547e5b1121782e8894020005980d51f1a502069cd200e024044d4204000,0x13ac648e61b0334640ee1de3b0001ec3d47a0ea1d00c40f0121ae4801b43786c0d65cc3d07b44a1e0ba19b31c,0x1900750eb1ce36465800092650c84823b8ed0ef41e01021ba81881e242008c6cc618e0018db5e9046d0dd1a237c678ea19c,0x55809c130a32453a4750e980018c00035b5a910f79ee3d88b5160033e081c0001d4863746d0df1a0330eb1d93b0,0x174cde1d537c8190280026e04d2388c11a22845889000514110202749184e09a132240478a414c28c001602b4,0x117ced1a81de18507a043a03b02f0006b27a8ea1342644c0730e01bc1a82502204007809a483a2214dd9d437a,
0x112c2a04a0921202384508c1102104034869c418d6008844d32341d291c738d419c000729a6334000e30580aa3d1dc,0x40010604087010d6e76728e006a688924ec9d83ac33c660d11a03546b9c31bc718e28ea396908759ce39a73ce40570aa,0x10000a809496778ef9e44848d0749e73cc0001d8083646a6c8928e19c61ae378751cb1d68d0748e81aa738e68e71a8,0x1218005dd2144408748c23922a3d2388c11885f30e7ec30a033fe178021870009389c010938101312600230a618c2187406,0x4007bf1823107a001ee87e001f4bd2740005cbd64ea09a0d40d01809f49a15c2a854096040898861040781301a46cc198630a,0x14b49502a04a8d0748791ac0901602b18a9105524319c324668c84820b81382202c0b41302102a8f454a3505e,0x16acec9bf352758558ac4780c01a0b91362082b0321302042989710014899a1c2624dc9b1352684fc9f13a260,0x101260ac65881f80498f010081b36606a0cc0c160a4e38a909248003cb2624b3c2004f42484943a0688cf3806a8ec1d7382,
0x14d4026f70e9268db052894ba1db2f05b4b48d647c8d0748380303943605c0581a82d0083a43705e00075ad059cb303e07a,0x100193808cadda41e000e0a4f0283ac01490208f09e80683a63817226c2b00a018204400300680cc4c05312e1490e13126c,0x5b83626d4dd00002b8ea522c0564af9562b858400015a65289a2342668ce9963460003685b5ea940ec0cf3b2758002d9,0x45b67a9588810e22243085912000056294aa4187f9051f84088380002b05a542324588c11522e468000158fd299b4372,0x18080006a0b69649b9330008fd40000056694b078cf01e83ce790f480006baea5739c73ce59ca46871c0031b740001ca0d4,0x5714525d4c919032662cb69772ec7f92b1691ac8e52a2514a0955292534ae960049702d05bcb396e2cc000e5c18,0x154ca521e029d1c14e9602635a6105126244180238314b863514000ed6020005e80d52d81406eb49772ec09028de8b34350344b4,0x5070f80017a2f20d41652f14e2a20180887f54ca5a3a02a1e6980121e447058a152e80700c538fea3f0101a9101502a2,
0x193832a5c2ea5c402a5a3226403b800fc20c7e319d14800fbf2d9924681e4007db000d880018d702de5b80c7db58cb1018fb3011a32c2,0x65b1d0389278e1192380004710580038f0bd198ed07a3bc1f9d03743b01e0005e81a97925f00c638060ad66cfea5d2d6,0x15a8b316429c5303005e0740e0a326045236d211c54926dce79b93926c8728341c60c12f1921c80c86b2591d2,0x46001113d873f63bc3080489b019ff3d2740dd1401d81781e0000d40d05326112c254508941442404f89311e294006eb,0x53a0764f89d93f2680d0190d6048964004673a0710d549e0122f9ce3840065b380698048ae110008aa1080c8a611a330016a4ee1da,0x4bc13c1644e8583b8003559d66dc72a1b2568749c1b91c64bc971ad27a4f0d90e414016d0812d2604a81282b074,0x44f0ba12c2d04e099a1e4b00291c00681980ee9df3c879cf29c4398700d50189231b9e83c4924e79c916024826891098,0x10e12fa5b06c09c0019d0136d86e0036f87c0fc0030b01130cf098c0e9fb02583aa4884002a10f58f8025b6e8002c8c005be3002c08a988288500b8,
0x10044224b18a910000094c800385a740a8128290484f81602b0740ec9da62008bdc255b600303630c583032619d30a340f2,0x40cfd2000f5001aace01a80ca6600989de13d079802663000cec384c4001990032b9361580018f9911823100038408f12002700b406431a6548e,0x18890a89b0ac4d89a8e93ac6fcd4a6533a684d11994540c01a0322689651a0794c83a06aa4f0123e4186d6002b10115b9de,0x6161bc630c595d20601064bae700d50ea3263583395c2be580ac10220a4187f21c262764e09ab1d697d2d99f33c,0x18f0021ad8e0560ab0021ac324cc1e41c00017255243031f140dd1e003a39c1339c849873d249e138a7a12124a1b6988ee0771ae,0x50244287d1c8044c20c039a2a332660cb9a23426753193f0e896533a3400148c7046c1f41c28368cb09400014bc6a4d0,0x1550ab9982c0688af1a04468ad340141020e0830002ba692b857ca99602ae550fe9940e41d438a141fa41882952298,0x59a32e7ccc0960222418d11f62fe578879043407d513a2343085d15a2f4d0000578fe7dce8001bae89000193351fd328,
0x173ce71ca39671cff004ef27e10b2ac5e8cb0090e81d4392690e21cd0a22e2f8564860ff1fa],
[0x12a651ca2944286508a094027e4f89e93c2764e89c93826e4c09792e25a4b09592524848c911212404708d91a2324605e8bc1762e85c8b816e2d85a8b41662c8588b01522a0538a614a290518a21422804f89e13826c4d09913025c4b09512824c490910b61682c8580ae1582a8540a61482804f09c1342604b0941242403606a0d0198320620c01782e05a0ac1502904e0981201c0360680c81802e0540a01302002c0500901001c0280400600800800,0x14be9792ba554a6895122234448851021f43c8750e21b4348650c21142083d0720d41882d0520941081d0320440680900a003fe7f8fe9fc3f67e4fc1f73ec7d4fa1f33e47c4f81ef3dc7b4f61eb3c878cf11e13c077cec9d83ae74ce91d139c730e59ca392720e39c638a710e19c2382700df9be36e6d8da9b43666c8d61ab3546a4d41a7346688d09a033e654c91912e25c0b796e2da5b0b596a2d25a0b39662ca590ae95c2b6568ac9582ae558aa954,0x1710e15c2383704de5bc3776ecdcdb93716dcdb1b23636c4d85b035e6bad71ac3576acd31a5b4a692d21a3b4668ad11a1b42682d019fb3866ecd999b31660cbd9732b654ca59431f63cc758e31b632c618bb16628c4985b09610c1d83304606c017fafe5fabe97caf25e2bb976aec5ccb95722e35c4b85702df5bcb716d2d95aeb5968ad058aae55c2b055eab1552a9550a9151a9851aa3145a835049fd3ea7c4f69e53ba764ea9cd35a6a4d299532260,0xcf99f13de7b49b93325e49c918f90861041f83d0720dc1982904a08c0c817001ffbfa7e8fcdf93ef7d6fa9f4be87cef95f23df7bcf4de93cd78ef19e2bc277cef5de3bb774ee1dbbb2762e99d2ba0734e65cc395722e41c7b8e71ae2dc5389])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB00 : ¬ FormulaSat cB00.originalFormula :=
  cB00.unsat (by decide +kernel)

def cB01 : Certificate := ((11,11,11,833),
[0x1000010578001582a8000a815a0004e0ab000298520a2140278360a90002685380012c294000781460003b0a10001d04f80013026c000961320004a0970002304b8001242404704412a000420930001384880009823c0008a1102181b08d000108458000802240003e10e000410850002003f01c106000140810000983f8000041f40007a0d6000280430000d01480001c0140d80003404003019000040038190000600900802e0000b0140140000a00b,0x10f23a0000c41d20003c0e90002d873800164394000e01bc3706d0d80b438c0006a1c20006b0df0003106e8000cc374000b61b6000590d90003506b80019835c000d21a0338230d5000310698000a034c0004e1a2000260cf000328640c6070334000c4196000210cb0001006480007c31c000c218a0005e0c50003005f02a1860001a0c10000c85f8001742e00f0bd0002d85d8001642e4000261720005a0b70002c85a8001602cc000ae166000070b1,0x100046c8991c0004688e8002244740011822c4502411b00046824800214464000502320007e1170003e08a8002204388603a2260008903b00042888800084444000fc21e0007c10d0004208580020442c001062080b0848002100b4000fc20e0007c1050004007f0202060007e1010003e07f8001f43f4000f81f60007b0f90003d07c8000203dc000061ea000790f00003b8798001c43cc000f10003b0750e81cc390370ef0001e8768001ac3ac000c5,0x1000548a8020038554000282a6000a7151000098a880029853c0014a29e0000800c29a00003002296000a4146000510a48002705240012c28e000a114027c4f09d07028a0003d143000470a08002144fc0007827e0007e13d0003e09d80026c4d09913025c1709c8002404dc0006a26e0008e1350001a09a8002144cc000662660007e1310003e0978002544a093124244148968000ac4ac0011c25200085127000150928001f048c0011e2420008e11f,0x131e0000800e31a00003004316000c4186000610c48002f062400187000608c017e2f85e83806c30a000b61830005a0c08000f05fc000762fa0003a17b0005d8ba1722e05b82e0582f2000351770001a0ba8002ac5cc000642e2000a716f000188b78002d45b4001682d6000b3169000578b48002c8588b004808859c001570a2590001562ca00028165000138b18000985840015c2b45601d0362be000ab15d000108ae80008056c0003e2b2000aa157,0x1000708e01be3786e83806e38a000db1c30006c8e08000f06fc0007637a0003a1bb0006e0298003686dc001b236a000d81b30006a0d980035c6b0d504808c6c4001a035e000281af000648d680031c6ac001a63486881d038352000d4039000108d3800326104d20003246940018e346000cf1a1000660d08003386681602a33e000c919d000638cd80032c6501001e33200014197000638ca80032264800190326000c7191000640c780031863c0018a,0x100010905800080824001fa40e00101205000800ff024406000142010007e8ff8003f8000fc1fb000028fc8003ec7d0001f23ee000f81f70007d4001ee3d87a8f41e60bc7c40006a3de000341ed000770f58000cc7ac000643d2000e71e7000788f28003c078c001de3c2000ed1dd000750ee8003b0758171db0000d0ec80039c75c001d23a0088ea80005074c001ce3a2000e61cf000728e7800024734001cc026000041cb000720e3000388724001c7,0x148e001202450008f12180047e9000023e4820011e23f0008f91e8004768e51e0004708f40023a02a000052390008e00580046c8d00023246e001132370008d40023045c8b1152280e48cc0021a4620010b22f0001e1168000ec8ac001fa452001122224408790e06044e000352250001a1118004088840006443e000fd21d0008610d80042c8640021442e001062170008490820e0948540020442600028213000139088003f483c0020a4108181e20d,
0x14fea300028a5120013c87b51000143285000a194180050ca04002790d6a100026b0cea08002610caa000027e4fa0013f27b0009e42ba7c0009842aa7a0009e0002764ea0013927100098427a700009b9368004c2105360004d2995350004d099c0026106a998002644c6001308294c4001300004b497c0025d00096c002584ac0012a25900095c002524a09392624a0c09540006a4a600034251000921278000c89340023c4960012324900091121030,0x15a0b3c002cd592b38002cc5960016385159400164039000b1560ac6000b0163800588b0c002bb06ab08002be5780796080058007c0002857e0015b2bd000ae8002b856e0015aab356c0015a00f000ac80280056200157aab560001572ad000a9c3daac000aa954800554164002a10ceaa0002a6000a915180053ea6d5000053ca740029906aa700029a03a0014c00052ca5400293522a500029201a00001291000a400180051e00146800516a1d47000,0x1000c082d8005d219d800005b618d7f0005f8bec002f95e2be8002f85ee0017c2f5000be1798005f011c002f808a001748515ec001742f7000b7427af4000b6c26af2000bc1778005e0bb4002f05d600178039000bc01b8005d210d770005ba105760005b60fd750005ceb85740005ccb94002e65c60017302b000b741aae4000b6c19ae2000b816f8005c007c002db04eb78002dc000b616d8005acb6c0000e018b6400004004b5c002d5000b4d6a000,0x166a00199b2d66800199331000cc9978006641c4003210f6cc00031d0f2cb80032c65600196329000cb193800658c940032c0ba0019086b6540018f8696500018e86764c0018a86564800191053000c800031b62ec700031a6320018d02d000c541ab18000c581080062800188313000c3989800020c440000661e00186800616c0d86000614c240030a60e00185305000c28378006141b4002e90f2c20002dd0eec18002db0eac1000302602001812ff,0x107a001bf039000dec21b7c000de5bbb7a000de0188006f00ac0037604a001bb01f000dc9ba8006e4dc40036f000db5b4b6e000db1b58006c61edb50006d0d9c003686ca001b08696cc001af8676c8001b10006b808c0035a6b2001abb556b0001ab013000d58068006a802400354006001a98006a2001a7b4b6a4001a3b50000d39a680068a1eda6000694d240034a0be0019f867690001a2000684d040033d676cf80033c05e0019d023000ce19b800,0x10e6001da071000e7c3cbb2000ec1d78007601840039f0ceeb8003aa75a001d53a9000e9dd1ba8000e99d280074c12c003a6092001cf851748001cf3a5000e89d08007440f4003a2076001cf843740001ceb9b73c001ce39f000e70188007380b40039a04a001cd021000e59cc80072ce5400393000e440038f716e4800389720001c738d000dec3cb8c000e282d80070ce14003836fee1000382702001c104b000e08238006f6145c00006fcdf40037e,0x1000fea018007fcff2008007e8ffc003f07fa001fc3f67f6001fa3f9000fc1fb8007e4fd4003ec7e2001f78007da001f53e9000f99f28007c60d5f20007c4001f08007be001ee8007b6f5dee0007b4f64003c70f2f60003d67aa001e38677a8001e93d1000f3de5bd0000f39e680078e145e6000794f24003ca07a001e3843790001e23c7000f09e003005cf14003bc786001dc3c1000ef811800774ef4003ba772001db80076aec5db000768ecc003b4,0x189f148004500920022703b00112a268008911181044b0011122480088111c0044288a002214410010fe1ec400010f80880087801c0043a0720021b4390010d2198008321ee1900085d0b21542884d0c40006a85e0020a42d00100a158007e90a4003f084e0021142083d0720d42500015a118008290840040283e001fa41d000fc20d8008300020b4150010420740c82600201411000fd2078007e10340040880d01205800805024003f480e001f8405,
0x16b0d563880056cace388005af1bc002d78da0016bc6b00052e3480052119c003d3000eac00387000d0c002fd000b44002a50009dc0045d00115400417000fac003bb000e5c00373000d6c00339000ae400297001194004430010dc003f3000f41d43846c0d018f2fa59ca893a00078ce79bd35e67cc71742c65409a8003b8728dc1ac336624b695b2944bc002324630011862fc620011800a8008bc02c0045c8b60022c023001158298008a914c00451,0x1932000eac970007564a8009252424748c915222434849052023f47c000d51abc91000a45494910009e52e48f0009852e48d000b395ac8b000a8949c8b0011321fc89000ba16cc89000b1d5a489000d61abc87000ad95ac87000b66428005b320c002d99020015a47f0005363f80087f1f4002928fa0011dc7d0007363e8008f51e23b4748e51c23746c8d51a2330004f296a3c8004c296a3b80059cace3a800544a463a8008990f63980040a7e239800,0x198930a604be9792ea5c4b69692ca584ae00099134cc7000f81f3cc5000f79f3cc3001066004c1000e61cecbf000648cfcbf000fa1f3cbd0009a934cbb000738edcb900076e5b8007cf2d4001db966000edcb100076e578009592aa544a694928a5049e93926a4c496928001ab35d9560016cae095600148a9a952000fc2039520020cbfa94e001ba37794a000fea0294a0022d4599460019f33b942000e71d593e000eac9d00080e4d80033326c001d5,0x10008110acf5000558b3cf50004288dcf50007e90acf3000e0a788003633c4002159de0010aced0008567580042b3a4004e69c938a704de9b936a6c4d69a934a684ce999328003786ff394002e75e13940044a89f38c002c059338c002d95e13840025c4df384001f841b37c004198153740043887736c0019235336c0045289f364002fa5e33640044c89f35c002e85e335c001fa41b354001a99a600106cd10008366780041b3340020d996002644c6,0x1000acd6951d0001f04ed1d0009e53f51b0009853f51900047096d1700042896d150003e096d13000e228880068d43c0009da1a0016950b0004b684800a0d412815009fd3f27d4f89ed3d2794f09dd3b2754e800113e28505000bc57c5050004488dd05000b9d7c5030004248d503000efde7501000dddc15010004088dd01000b657c4ff00097139cff000730efcff0007e10acfd001066094fb000b757c4f9000648d8cf900114a28cf7000be97ccf7,0x15f0c0ea4800744ec6a38005e0c0ea38004d2a1aa2800676d2aa18006aeda2a08003987c6a08003947c69f80015c38e9f8008330c29e80016c38e9d8001ac38e9c80073cec69b8005d0c0e9b80016438e9a8001c74cc000e3a6200071d2f0005e6968001c74ac00528a4d49291520a3d4728d518a2d45289510a1d432855080011422bd270002504ed2700113a2bd25000dfdc45250009a53f523000c5991d21000ad56951f000630dcd1f0010f22bd1d,0x1a0f39e64c938f6002b9570add5b2b5568acd592b1560abd572ad558aad552a9550a9c00218435ae200212435ade00209435ada00205435ad600200435ad2001fd435ace001f7435aca001f6435ac6001d63b5ac20010d233ac2000f21f3ac20005b0efabe0006b0efaba00201435ab6000590efab200077d570003beaa8001df54c00185aa200077d4f001532a5548a8d512a1540a7d4f29d538a6d4d299530a5d4b295000646cb2a580074cec6a4800,0x2002b9d4da5341e73cc995a002b9d4da0f39e64cad926002a6d29a0f39e64cad926002b9d4da0f39e64cad8f6002a6d29a0f39e64cad8f6002a6d29],
[0x150868c28a26a0000ca50068a27a26a00009e4e068827626a0000824d868627026a00006a4cc68426c26a0000524c4682,0x100006a5c86962da2d000006a5846942c02b80000f65586922b02ac00006a5386902962800000f651068e28e2800000d6,0x13683580000ca6486a035c35800006a63069e33e2f80000ee60c69c31e2f800009e5e869a30e2f80000825d86983022f8,0x18626ac45e45c00006a7c86aa3be3b40000f66d46a839a3920000f66986a637c3640000f66606a436e3640000d66546a2,0x14ea4e84e64e42640006245b46b04a648c0000f68646ae4a449e4784704a049c46e49a46c48a46a4684f44dc46400085c,0x12b64fc0005228ea6b65163b04ea0006aa8e26b45142ce4e60005668e26b24d64303f63c63b03882ce2aa2684f04ee4ec,0x152028026a2640008f48e88e48e08dc8d88d48d08cc6bc6b82c82f02a26b60005ae8ea6ba51e2ea4fe0005668ea6b851c,0x16c86c42ca2f22a66c20005b29166c654400035ab548b3622a10001ad49a459b094e8000d6d5d21cd80a700006b56a90e6be524522,
0x194a6ce5621f400040494a6cc5604cc4f80008b29466ca54e54854628026a26600092492091491090c9089049008fc8f8,0x195495094894494093c93893493092c9286d04d24d04ce0001f01f21f61fa6cc3cc5641f868226e3c84d44ec4e20004c8,0x15884580007ce9866d65843f84ee00073a97e6d45804624f20007ce97a6d257056647046e46c46a4684dc48c464000958,0x2660a00000bc5364db8b1cb0c8ec8e88e40606599098c98898497c97897497096c96896496095c6da58a45a0007ce98a6d8,0x19bc9b49b09ac9a89a49a099c9989946e45ac2660004de9c26e25a64aa4de0008769b66e05a24c64f600089e9b26de5a0,0xcff3762ea17c0002f84f93752e80001ce28a7b9ba1738000e6be53dcdccb70b509008fc8f08e08f88dc8f4080cf9cc9c89c49c0,0x3474de0be0bac91090c8f08e09088dc90408073a0ca08a04a009fc9f89f09ec9e89e49e09dc9d89d49d06ee5dc2660004e6,0x3479471459451449431420df0c287dc7e4000dfd494decc2453453c0009a548cde8c1c0000d56aa3e6f26082ec2ee000566,
0x1a726fc62809c0a009a000164a6a6fa61c5fa5f85f46046023ee39e2ec29a3f23a22ee29e28026a000a50a4ca48a44a40,0xa7000023853f38331b0f50f70f40001ca53f38231a00806c5729f9c098c92300021829e9c018c00401e2d94ecdfcc5c0200f1ac,0x34d0e14c700204b398a827084b24b04ae3523503563546b02f62f23aa3ae3a81ba7042ca2cc2c80467023b02ce4b44ea4e6,0x356ce1ccac13c020ddab270c64a62062261e62462616209c1660a016009a000a98a94a90a8ca88a84a80a7ca78a74a70a6c,0x2ed5584e30cc046846c460000869584e2ccbc3d80008f3c8ac271465c09e0107bd5f38932d04f0083deae9c419611e0085920045b86a,0x10412b820086b69c919b0105520802fad672266a0017d81805eb49c819a0180ff59ce3cccc8cc0010d5594e38cc800067ac671a66241c506000,0x6b32b22b12b02af2ae2ad2ac1ca19c12612491e12591c0a112512411b92391b0a2000aaa5340055329e28000086aade72666e,0x4c21ac1ca8000619731cb0d492c12c92b80039a9689c0000c4ce54ce8c9cca4ca0c98ca82c813c0416fae4ae0adcad8ad4ad0,
0x2ba4354be0e6059859459009008c09809409c0a00ac0b00a45f45fc5f8d60e540052717a5c072e05a30005e05c306304696,0x41b0198190c41a60c30c68c60c58c50cb9cc01e81e1ac1ca80077635cba4e640e40ec0e00dc644d3463865865465064c0004b,0x10607360001ae7380003c99334d18e19519419739a03d03c03a03501812c621cd80003e628d3061863062c0005119a1945e0734068,0x5d01528aa0aa9390002489489cf9ac8b20bc0e99ad0bd00002b1c4e78d7c5945e4754d805ec0005990e73a72e30a73272c062,0xba039d36329b29a2990180c4aa93a9399390002491639599d09530eb8ea8bc8b28b3000d06e7c5ec0002d3b02ce4ea4e6000922,0x222422070c0005244703e0428e8801000c008004378960a58000478a50a4c75075c754014d90a78a605e054455054c00035,0x137837437000063a27226025c23865874610a6a410c38237e3843700fe0fc0e00de1060f41020f00ac1000ee0aa1080f8,0x2708e8c2042002102246c46bc6b41741641e016c1601581dc16815c15422017c1780205d2161f07480f80fe0fa0f26a236a,
0x42680018e9991d401200028e00257001358b33a73a43a23a5000175d30290004f614415014c0027b1f274a10c10a10437e6a437a382380,0x108208008833a33634c34409808e37a3800860960106a438208c07e05605008a07c05404e74e09408473809e09c0a034e,0x5d28080f68948347cc7206605d456c4fc140a10a0ca08a04a009fc9f89f478870c0005727263a75230a2fc72c058062060334,0x9a004804704c04b3541e01e11de1dc26d1b607b000574d28d10d30cd82202182000029e6ec6e86e0708ea00c0850f00ac0ee0aa,0x5d480834e17c178ea8e982200019f000d0800525d583183293013113083583683603483383082b03303002a9d2800db6474428ea8060a1,0x40807a818810830eb01b0184000370c00101ba0d28300011d3ad06806b06d2082021ff1fd0100bd0590483380005a1980402b23a74c758,0x8f404d00010b3b01d40dd1d71d60df0e10e000260ce79d780c1d612068011c0ac0a00012b0006101d275c0c44064043fa0ca3fe,0x26f06e43bc1006d46ec6e8708ea06c46bc17417c6b41641783b4ebc1180fc001ad04e74e020898106ac7a81c3523dc0e1a73a438634e,
0x9e01c13543520282ac1c4ae0001ec1a4ec49b47706d83c43cc77872c784740780738d50d4c12c130eb8041c51e40866a21dc6a0,0x2d18d1473072c5285207405387385303c4d4cd1cec43b4394388ebc3d43dc7485403d00000d01ecec8000413bc3763c2384,0x8000790673c73b43ae04c018ad42082580400822a1034b1880f47661ce1cc38c38e38a1c81c600c1d21d03941e01de1e61e41dc,0xbb13b23b30ed3af03f02800019c211ce0b487a8270b387b82813990b8fd00434a58c540001a10f218876a45444e45244c450456,0x4a30001e210c000ef3ba3983963742be2942922903c23a03842c429c3082723c039c3822c22981e26966846a86a66a469268e,0x20205400001aced885484885884483c9b07d47d87e07d05bc5b05f8614680ed0694000bf0822d468226e2743b639436a2ba,0x4791db0768103ca7a81ecee03b83ccd1472c0c1b1051138ef0400f20433b603091c0c4aa3dc14074869c020d50cc76e29468c29c29868e,0x17760362fa6a2710001fb3ba01023cce8cd0c29cb0bf0006b6ecc12cedc1180048101284b9c04f0087043d1dc8798770e58789a280806200033,
0x9ba1b815f15e14914800069cd80c20ac89c80034e29cd3cd2cd20d08041a777276e15076c6b072a1621663862c62a0160000604,0x8001f5ac1ca80010a000bd8594ef028c2a429824c24823c5f45fc614668664674670244d046b455c4dc6c45684e82940019368a,0x25205385304b0d1cec4ee44b4ed84c04c45404bc0001800c0900ef423c24824c2700006b322136050378001c4dd0af8a481c0f20807b,0x93914c10f3420104dc881db08c88d8a808c0001cf0301df80427a47447c0013d47a77c25625025c24e25224a24224c24825468a,0x2124ed4eb8694698eec69c0001e4f004383f83f47f8808800444ef448c488ef84303ecee83f0002a521a28c68a29229029c,0x2648008d72ce0905f078415c15e14415a14215878015615469c33c34834634234c7766b072a16416634e1600000e02d0782,0x2ba014410cf147b47a87c87c47b87cca0800014410cdecf10640ef027425c62001c258000bb8574f0c278268264ef004999,0x80012011d3be0002393c622322422122221f26c000ed5e20c2818782774730001b7091ea808f5c0c3665a489459ca109cc788748021a973c,
0x46c86906b86886b1e006a86a004252688021291b61b834e1b40000e03647907081be3ac63a3c23c06a87723c4000a8278e23c,0x4d983b17f8399d818003a1d697f17c8438451d58389d280146e1d41c850850451050c9685349c070c08da329a13a0187921b0,0x22482902402837d041bf840e041070a538f28c14df0de49645949605e4230becc206c46d46e8de87086c04e4704d3cd08d48001094c8,0x9ad000364e10d80c20e09a79a58041b61a4ec0eb419c00829003a197b002d640154e968a0000aa34e0386000ac2a0c52223679614c126152,0x15c05be5bc5ba2ca4b013e1a02122f21183ae7827902142a63a64262160c82a82a47187160dc11c7941f023878c7740b2,0x2250f0c04c4731232e5e86ee5da1d41d61be1d83ac7145ea5e05c86e84c20d65d217417216c1682c84ae2cc4b25c25d85c6,0x1001df8bd3411ad1371b113a1b51461ba1491c214e0006d4a6000366022bb00074a0d19826300039d4194013d8041ca540020e370479813012a,0x45e05c84a84a05b0001962d0020c92c84ae6e632e2cc4b2784050778a00103b4041de1a884c42c550f2ce30e2cb887c47c07bc040eb206,
0x2b98418024595e63fe0b81823ce3d25e23ca17c1861843dc41019a19841619c4185ee4c45d21961804084c017413019417e,0x27b07c8f30f2c28027c420f0442884c42ce30e2c3fcee80010f3e6330506504500000ac2522a0c79a27c6886ec2086ee20e,0x4a68001229ec022890241f800d9c000ee120f3c620f1482001c000e90bb810cf38f1482082c62001c8304048104082604000e1737840d4,0x5289db00074e1ccec0388ebc1d0eb4003ab6fe0506fa04e74e0e274a74073a6fc738016a8820e452e92e0a20a180013e98c002934b64b4,0x164800272b1f36c36b3692bc2be2bd2bb2ba2b92ae2ad2aa2a92a81d00219f5180748740e7010cead543c0044bb77077276e7006ac,0x88e3ca3c70f838311c3c601c3c001b01a0217747f9dd18f1579b28ec8e293287212f87192f1a08d69631b380472eafc024e5398,0x9642573c22cc2cd2cb2ca2c92c82d51662590009fc678840b292c15b8004f60035f42621652a2a63a671871679a56a2a82a452e,0x4808081e71059b918690616c9b796793110213016906584c05d08004a80784a00706505c8003b62d8c80b68b5c021d316832e,
0x167c70a64662c7926da6d042004058255677e04418618441004219a19803e19c03c3de0326f63e403a0303d802c204022,0x2a08a009fc9ec9e00025b02353800984289cf1e89079df90890810b1099e084f81c7d20081542e0007483523483440745e07a05406c8,0xa1310b3cf15438c38b08e3ca0010d4057163f038c1e6cf2721d002367b420f035402884c711d780049a87086c7cc6605d498c86486000403,0x27c05d07c85c47ac32431cf14410644d3465865465cf4081c3142e8310085074c02ca4b019e2124c42f21187902144c22a6,0x800dbc046e2023730e1ba8120fcb70086ea048376942f1ba800de40023a02377001bc80046c286ee021157a43d23d03cc43a1fa43c1fc4d820c2e43dc20e2e63e2,0x14027a279a5a4050f0830df4678848841031029859300006f2f20428830988043774124c2021b9bcf098dcc8187f87d8106de001910166822ae,0x813012004e156c1910053ce5c0db865cdc45c87b86304f0001ed6986862e83e42002e23d62041926426da20218e4226d440641e,0x104404203e03c03203a03002e6e402a5b60283d201a6d03cc0185581fa0141fc2fa20c70a2fe6c820e62a59c30a53e208,
0x9010c71050073d20cf3c821338c10910810a10b38b030b4c091e254c550002eb1fe7742f601320819d3d41008e9a002417a667c792618040,0x2690698eec448ee8edc46846c85c69c460000858f50d3465441065c41c6307c0d307c84000010340a4c04184c44124c279e,0x111c11a79474073c029d9a8928828735d00ceac027df53541d39d3252b52211c95ccf540442d42822e22c21622a21422878022669c,0x810da5cf1c41bf1ce00c10a06367438436031b180120c0c6ca9e09cc9c085c7880c365a485e24140727ac52a6c82a850a6bc67a67e52e50c,0x408e1ade81839502281b9038f38e38d3913873923933391b0018dfc0c9ca950d3c043790326cb57028dd4d986983b17f8046e60aa8f7126fe05070c,0x400682db8bd85c4b303207c47c87ac95865865c0697b031b89091083d428608d028eac01a8e103a50029eb1e2af1c7365020e8d840ab810e2206525,0x2bc40236b13a2e02e43d23cc5685585183dc32220a0260242e61fa1fc20c20e20869a31c2e85c43e06e07786445e85de6ea,0x10182784d801468670a6426ee6e85ca43c2fa20020440a4184124c278414078242642c42077a43a6d056c2fe5b05b63d0,
0x2690f5cc30df0bec0c3bb6f067802a60c16a2ca4b02cc4b22c84ae6bc2f011650a2a27a67287aa0286da6d401a6e46e2402,0x2634008f600876114078441241840a20420018c17617018819218e2022107a81fe77476e41a50642e0005f0352084074070,0x10847b60103abb70003b03da0b4164166257021084a89ec05b85b0471e500083e004270121798f3d9020254bc0458469e50bd00304a96801a47,0x2f58f5cc2c0154d78432e20214019e78279042642c7b418a1741727b24c80033a8743ad01366c0cd3266098c534a009ec85c023575e2,0x101563804fed3d93a93913810b8187d2a44f7480cf1481864483082465801cf0865cf6c280f040002f41a33050650042e0005e27b8,0x2f70ba4b84b48b3000aeb030ed8cb0c00ba00b45dec83077a3076b4340056c8fc0e30bd0fab542879608ac3021e781ab04087a61c749091ed800f742158a013fd4c63b0,0x162c044006c7822b95790f88f780c9120055be88006add6e679c7846464164146e461a4c20dc4185ee01567864204260098012b4c0147a08ad9,0x20426f074de85191409366066490532585898c104ce0426b02136bde3683402b73c91d73941531d33d300218dbb9bb09f1a2082029b36db4794e1400ae917c,
0x9513dd07890cb817d9b68f28b580047aa623f0e2fe8988f4e290d01048ac206b4b1800f6557e36a28c6483740930b9d01c214e0018dc0c4d65300063f,0x16766bc6f874251a60c2c84ae6067b02f011601250a],
[0x11782ec5d0b91702dc5b0b51682cc590b11602bc570ad1582ac550a914027c4f09d13826c4d09913025c4b09512824c4909112023c4708d11822c4508911021c430851081f43b8760ea1d0398720e21c03786e0da1b0340670cc1842b8550a814c2905009e1382684c0961282484808e118228440861001e0320620c01782d0580ac1502905009c128240460700d81a0320600b81502804c0901102003c0680c0160280480800e0180280400600800800,0x137c6f4dd9b92c4584b015a2b2560ab9562aa538a694c29650ca11412804fc9f13d2744e49c13726c4d49a1332644c4981292464889092023e4788e91c2364688c91822e4588a9142264488891021e4388690c2164288490820e41882904206408809001fe3e07b8f61ea3d0798f21e23c0778ee1da3a4740e71c838c710e11c037c6f0dd1b836c6d0d91b035c6b0d51a834c690d11a033c670cd19832c650c919031c630c518830c610c11802fc5f0bd,0x15b0b4167ace59ab3165aca592b2163ac658ab1161ac2580afd5eabc576ae5562a5548a8d5129f536a694ca9752ca554a293524a454828f51aa3143a844f69e93ca704de9b9362694d099d332654c898d312614b896d2ca584ac9552925049e93926a4b49291d22a444869052023e4788ed1d20e41a81902a04406809009ef3dc7b4f61e83ce798f29e43c6788f09e03be778ee9dc3b6768ec9d83ae758e79ce39a730e59ca392720e39c638a710e01bf,0x188f11a22c4488710a20c4087f0f9febfc7e4fc5f63e97d0f9df2be27bef71e93d17a0f3de63cb790f1de33c5788f05e03bf778ee9dbbb4762ea1d3ba674ae91d0ba073ae71ccb9672ae51c8b9071ee31c4b836f8dedbd3796ecdd5b93716dcdadb53696ccd91b1b5e6b8d6da935068ed0d9fb3e67acf19db3a672ce199b3065ac9d93325638c6d8c314626c418730d616c2183b0660ac11812fc5f4bc5782ef5daba9742e75ccb9571ae05beb796eada,0x1b1962ec5589b1161ec3585b0960ec1581b015febf57daf95eebd579af15debb575ae95ceb9571ae15beb756dad95aeb5569ad159eb3565ac958eb1561ac157eaf55dab956ead559ab155eab555aa954ea9551aa153ea754da9952ea5549a9151ea3545a8950ea1541a814628bd16a2b3fe7f4f19b735269cd299d32a634c598930e614c19812fe51c9892f19a32c608bf17a2ec5c8b716a2cc588af15a2ac548a714a28c5089f13a26c4c89712a24c48,0x6e35c5b8970ee15c1b816fedf5bdb796eedd5b9b716dedb5b5b696ced95b1b616bed75adb596aed55a9b5169ed35a5b4968ed15a1b4167ecf59db3966ecd599b3165ecb595b2964ec9591b2163ec758d])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB01 : ¬ FormulaSat cB01.originalFormula :=
  cB01.unsat (by decide +kernel)

def cB02 : Certificate := ((9,9,11,177),
[0x1381b8d8323b800687500178e600261c4003e37800746d001a0cc64311804c6b000c0d2002f19c004c328007c63000e8c2002e17c00542f800b4582b080ba002616c00242c800445700148a04e0d154004c298003c51000709e002513400442680090460a12c0018248002c4700108800e2280024430004082001e0fc003a1e800703b000d87600040e400021b8006831,0x10780186136300182116200184005f2f400be5d80170b7002d166005a2c400ae56801560054a9554005429c009f1aa9800a45180148a10027c62a20025c56a000278009c4d80138990025800924a801260048238008c488011e00452210c84410a11a001822c002e448005887000a90a004020c007e40800f88100030fe00031f4007a3c000ec7b001a8f6003c800e872,0x100418520082002050100409fe007e3ec00f9003dde6f8003d9ea00768d5e800793c400f277801d62f78001d22d77001d8007239c00e27380014e500011c6007037c00e068801bad76f001b8db00371b2006e08400c312b6800c111b6000d66a801acd30035836006187da80060875a40067b25a0006733400ce658019c150030c32cc003042eca003218e006431400c8,0x1733016cac4a002bd5d0056eb35c005681a00ac01c0156aa802a751aa002a40b005400a00a78029b4ba70029833005284e00a451c0145a1d180144048028403005027e00a04f4013a9c8026d35004da6600984bc012c9580259290049a4a0091802431d91002411f0045c6b1e0047236008e464011517c68011316c600116004421e00868021707860021509004146b08,0x1005040137004b401030038400bf002d4009d004ec01310049c0111003f400b9002bc015f0055c0149004fa692a8a401d4de5e2c934009e4ca51127f3a1a0ba582600138974921cfa],
[0x16a16c28894000326616a260940002663168200760006a531661e87600062511641e0700005650162,0x1001cc601763f8f40006a8f1743a8e60006a84172360ce0006a7a1702e0940004a6d16e2b8940003e,0x12599c5e92c4a928320c6330ca4b940001ce5e1384490c418f23808e2206e5414e5314a521465106c,0x16e17e04810039682589e2709a2a97a0701a5d978309580009a5f018058145a8a02a0a6291765e000,0x582090200796c2b0b42c8b03017e0c02e08800042622b00017cc00581404cb716c5f1785d054be000104ba,0x15615655152499043784a0005e6191c4691801002020064793e000766107e59084209660008600062,0x14803c100340303e0c80a6103a608440e180108365f04e131164410a390c42488c1d0505815e5715a,0x53a340f63e8d41a039a28872107118448114390581cc5a6213c348f83f0d6408dc400da5d1701184848924,
0x4641798818186171623a07c3b8843b0825c9660a02e8c40a05b1a04e131361a850509263c0861984a0018a,0x14d1324c054148581585a],
[0x1638c5189b1061cc358430660abf17d2f15d0b9d732d059eb39662cb594b2163ac658ab1161ac2582b015fabd54aa914da935249e93ca704d099d322624c29712da584a093d2724547c8f11d1622c2568ac9582ae558aa93a2724e05b0b51682cc590b11602bc570ad1582ac550a914027c4f09d13826c4d09913025c4b09512824c4909112023c4708d11815c2784d09812c2504708a0c41802c0520a01201c03605c0a8140200240400700800c01000,0x19db3b275cea985306604bf97d2f25b49792d2564a3d27a2f21e03bf74ee99ceb95728df1bdb726d4da5b33646c6d79ae35b6a4d41a3b3f67cced9cb38666c9d93325])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB02 : ¬ FormulaSat cB02.originalFormula :=
  cB02.unsat (by decide +kernel)

def cB03 : Certificate := ((10,10,11,474),
[0x1258990009425c002589500092254000380c24c002408e0008c24400200910008f0008a22086210821488d0007422c00180890005e21c00170850006820c001f87c1e8781d840204001407f0004e1f4001307b0004a1e4001a077000721d4001c06e1b06a09873000321c4000c06f0002e1b4001a06b000661a400030670006013c65000641885000062144000f8330002406c000400705400050120200004809,0x1188d1000a433c00180cf000a033400178cd0009832c00170cb0009432400310c2300be2f042100c70005031400290c3000a030400260bf0004a2fc00250bd000b82ec002b8bb000b62d0b22c0360d0b9000a42dc00280b5000982cc00250b1000ac2a8a829828098af000a42b400280ab000982a400250a7000a229400280a30009e284002709a0781c27c002789d000990949c00098274002509b0009726000,0x1421064104443c001410d0004e42c003b109000de41c00369050010040c003d903000fe3f0fa3e038404000f8ff000ec3f400378fb000da3e4003d0f23c0ee0a8f7000323d4003b0f3000de3c400368ef000ea3b400390ed000e8398203ac00378e9000da39c00388e0058e5000de38c00368e1000dc37c00368dd000d836c00018d9000d635000348d7000c635c0035400340ce330ca32054148d3000ba34400,0x154c004b9510005c53c001694d0014851944509401104252c00141490013251c004b9450004a50c00121410013c4fc004e9384d9340e0364f4004c93b0012e4e4000f137001224d4004c1330012e4c4004b12f0012a4a0200792d001264ac00489290012449c00489250012048c0001804484004791c0011a47c004391f0011d0011845914449101591b001024640018117000ec4540037913000da444004310a,0x1629881199300050644001398f00170634005898b0015e62400611870017a61c00609805f97c0e9850003e60c005c181001625fc005797d001785d9745c82c5ec000c979001705dc00589750015e5cc005b971001685c4005b16a0896f001625b4005796b00166590185a400589670015e59400581630015e584005715f0000857400569580015656c005295b0015900154549505394c1585455c004f95500060,0x1001b8734006d1cb0004a72400699c7001c271400701be6f1ba0e9c3001c2704006e43f700006e1c1001b46fc000f1bd001a66ec006ddb8001b66e4006d1b7001b66d4006c9b5001ac6d4006c1ae089b3000246c400699af001aa6a0186b400069ab001a66a400691a70000869400689a00019e68c00649a3001a10019c66998659941619f00186674001899d0006066c005c1990016265c0057995001906398c,0x18700086a19002130fe18002168540085827002130ce14002120021083c008320b002090020780e0800206814007fc638100080a01001ff14600001fc7ec007e1f7001f5001f37bdf4001f27c4007ac637c0007b9ed001eb145ec001e879c00789e5001e3001e077800771e1001d07840077c00769d8759d47485877400711db00060764006d1d70005e75c00171d5001a674c00739cc729c87184674400141cf,0x1002529440094a4f002529340090c63940008dc61938008d45f9300092a490024a91c0092a450024a1040090c51920008dc4f918008d44d910009063d908009023f002370fe3e0023c8ec008f239002370ce3a002350c63800236002328c4008be2d8c0008b80d0022c00c008ac008a6238a8008a22700228894008a0530021d18e260021318624002228840088a1f0022210400874518800084c4f8780086e17,
0x1a0a81002829fc00a0a7d002829ec00a08550026f18e80002611867e0025f17e7c0025d1767a002789dc009e275002789cc009e2710027810c009bc519d8009844f9d00097c4d9c8009744b9c0009b6699b8009b26b002610fe6a0026899c009a2650026898c009a029002610ce660025f0c6640025d0be62002600025c0025995e5a0025896c0095a5b0000e964009600f0000495c0095805002550025392e54,0x1b1019002c2b0400afc00af6b5af800af2bb002bcae400af2b7002bc15c00ab463ae800a845dae000a7c5bad800ad2b3002b4ac400ad2af002b411400ab451ac800a844bac000a7c49ab800aaea7ab000aaaa9002aa0e400a843daa000a982b002a4a8c00a8000a729f0029aa7c000400aa740001802a6c00a6400a5e93a6000a5a950028f18e9400292a4400a3c51a4000a328b00288a1c00a1400a0e79a1000,0x1002fabe2f6bd2f211842bf400bf2fb002fc11c00bf043002f1146fa00050bec00baaf9002e6bdc00b82f5002dcbcc00bbeedbc000bb83b002ee0dc00bb02d002e8bac00ba2e7002e5b8ee6002e407c00b8819002deb8400b7add002db002d9b56da002d8b5c00b6059002d814c00b4463b5800b52d3002d411c00b5041002d1146d2002cfb36d0002ce0ec00b3835002cc0b400b2ac9002c7b16c8002c607400,0x1d00230033e06400cf33b00339cdf3a0033803c00cd80500334ccc00cc72fcc800cc00b0032e00c00cb32b00329c972a00328c9c00c8425c9800c93230032106f22003200031f0031dc671e0031cc6c00c5463c6800c6317003151471600312c4400c3f0dc4000c38210030c06400c30170030ac2400c1f05c2000c18130030604400c10090030401c00c0c00c06fdc0800c02ff0030016400c0055002f118efe,0x400c2c00b7c00b0c00a24008cc00834007e400cf400cd400c4c00ba400b2c00a9400a3400844007f4007a400d1400cb400c52f0b42aca3a6e90a1c7f9ea00310b9ac8a8a8a97a34839fa79800c22dcb029ea1a5a8c20a7d9e400344d0c00d073fd0800],
[0x18f8ef91322200019a3a3bc4187d0000c2890ee9011f400027a1e3b83f87d00007e860ed8fb1f400019a143b4,0x10001fa6a3c84cc98000066998f193125e00017a623c4484888000c2938f091a22200027a463c04588880007e,0x1578ad80007aaa0f494626000030a7e3d0510978000ba9e8f393d26000027a743cc4ec978000969c0f2938260,0x1754ea1d31ce0014f25a3dc6d0d880004ac98f69b23620000db223d85a8ad8000baae0f59632b600025ab03d4,0x1694881d93aa000349f037c6f4de12b2524b4961bf3a40012d9ef388694c297229e4407c0f01d0764ec1d73ac,0x11602a8570a81582985a0b2148289aa3a0000768da3e200400002346688d21a02ae4348790e010024ac9ee3de,0x1688ac1b93746e0ab9f32b401045b7670cec9d1390000b89f402005c00036039f30201044f0a0694ec8001b67c8d31a9350,0x1000289eb3ec6d8da9b33da7b0019b738e0000d9f5140704e11c013a2885089f1382684f09b1322604b9a1348,
0x13a4e81cf39c734e61cb394724002644700c4fc14327c534a614700a538000514de7dc770eb1da3a8760051de,0x1554a91542a254c02956000145479fa330654cf19d334014cf8000a2bc4fc91238a4c8d518a2ec570a80f91e2,0x1590b816f2d6014b88000a2ab4fe91f2364989292200a49c000514867f0829022164288380521800028a1d3f6,0x17f0fe9fe3fe0147b8000a2800d79ac35c6acd680536000028b153fe5f8bd9833045fc02984000145689fe2d0,0x45f07497d010d11a8340660cb19c304600302feec9d100070cde03a3688047b0f51e63d0791c63ec7dcfc9fa3f6,0x12a44d0dc16a2a04c8c11303000e1db040f80040ae728be03a694dd8e617e07cec9d1308538860e3178070001d4384,0x12ec700b83ba604849832165f081815026048089e6278794a11412805347094a1aa34ca28144002dc551f416c,0x6021c2354598001ae588001aa580041a6578501a25e80019e0a1f90205f8287bd8429c49c060af0e82fa031a42ac668ac1942b86f8ba1c4,
0x4ca19a37c690ab1582b8040e17a0a594d2807940881523834cc09832fa2d0590130247808c91e23a4989192038a,0x14988e919024054088133ca770a01042065348594b2127a0ee814400040f801d03e5389390c0380011a861408,0x12ecc08a62fe2ac0218216e2a85280037a5209a16a2a0518347365f1a53762fcec9d1178000cd06307cb61029243c2,0x6a722c3f831abc40e2b0570ab31c63cc60a715a2e85319a176010ce99c1181b70040c5e4bd17715829c570ad174,0x4005b6ec9d11c6000e4046368820320662be5843896b0e45bcb606e0c21bc310523e21b4300513e41d43b073000,0x4872c423045166112200b287f116800f71ef128258498005685082112e4123646d8cc1b032c6d2001ac0c1979c8,0x5d139e738003831cc258005f8330252b44161f4d407c3521e8d387b0f2620c4987354628e81cf0004b40c922414,0x43f40030cfa8c20183250e37243cdd10d00030c680d2148f88670a27c8020b51d02684c34a440dd98a2ec1d8271d93aa,
0x11f90484208c35c4403b20e51c0300717079cee94c2925208510921053485942208798ee06a0d865ccb1650d6,0x10c01602b0700a82482f04e128120410740b8130230420809512e2501dcc41740f0624baa0a30e5cc620c8410,0x4af06897cbd09a1300025b138044932f0258001402517e20c0644d07e13a2004e47f9e43b6814c197c0800f81882d07a,0x10e02484a290100cb008216ee94c0304444707c0c42183c05e2c816824168114000850004a84665c5983f4002c4fa0b0134,0x60c0820cc1199407e8005b80065e003310e199b22640c999217c00065b0c614dd98b31400061bb0744e799f3080305f884834120bf,0x142485903080668bf84807c0f01e83a0721242518230060cbe99908e0d8ce99c33610c1a02d33c09022835058,0x57d3066005985032a043f50006e80014d0703731a5e0c797a3185dc538a63b43f4800ff15a76c5d2061762e0839dd214,0x18342083305c1141a83005809011a0e166002d894a002d88004a4af07916cbd09a030fdb3e030fc92828107908216410ee0b2168,
0x57726811c1b03131a0025094c78c9b93a0087bcad28e818cd0ba1722ec5c1e829852ca693f05a10c1a02f0004b59e418,0x11601d1c242209c1202a04c08c0009f03c0704a2102fe608bd1832f05f41b8b41647708200105e800fc0640e40021d,0x4930e6070003000c00f01d03657884c1102541e0a0158290000944f2121c437870a031aa370104af0235a8212bdd83a8,0x4c216a023b584927c6e0b81bc2e800b2a2d8513e4040f800832a4a87503a69488018e9ee18bf12c1d80f9d93aa063a4b9000336978,0x59b1c0240678822dc5b49c9171fe790ef9db2d6818328b90e22ec3919c1701c0b796c0280025896e7d05b09a18a,0x1828408780ee4a09712a0400850821218c31cc4174382624ba9c230e5cce00c419232100a111ba238469eb2d2,0x14988594c24a428a392220e4e88c10026e4547e9e33bc7682f05f2ba584af88510c2444209210023c4187f0fc,0x1001748326710706b400010b296a0619083984c16014030bb8e80780e8cb2fc3b021196b880430202183000c28c0850e293c021e9541280474007a1,
0x5da26c4d48a0fd1f84e80b91820051cf392220e530a514924a48c850001c6a111e208798f0000c56b2970426030abc0c,0x179400a5b52c099dc20840c8580121ee2a0401242c141e20f8141f2a70011da30a1538a480a28180360680780e01802c069f83c4,0x43c3e60837b0856884ab4c04412000a90cd0b84020e002190409c82e0d07c80c0007b80e2e00ca1541c800001430781c061000ae8005844f42c05409011278,0x1c010c13c38a0116da3a40cf28019de8c11500932cfd282500099de3b4006ac9724e8000bb2ec9b80016f0b19c3c60105c215028,0x61600a8dc00b525305e17685cce80082f0a86b079bec0484a3405c0de1a40242119c0041f020538ea1d0005b91d8ec9d12e22f03980006c,0x1480a512329a498a111e3cc7800a16d070ba80013c2fa192d6584b79602ba17c328710e45b0b81653d21b10a06a31c,0x4063cc01c000891c0002f10d0408415dc087fa040671d4003fd02206829076fc06486d059ea08859d0c8b216865c2a7090457fdf8ad10d1c528a,0x15742f80f0ca068911070e206c9290a0e405c9310b2d879c8f1040305c0a49e03b88650d05e01a51ca614d284,
0x1790591e30082d10d99742a1a0a0a9c0009fc38030fc00e2283f0059182007888b8ff26c4d4ef9db2744e4f206340e,0x2c60a731e0113bb1a2985da180009d59e4382e10a8104ee24ca7004289780010e94c29a51ca10062744e4f300726e],
[0x12b6568ac9582ae558aa9542a6540a794e29a530a594a292520a394528850ca11412804fc9f13d2784ec9d1392704dc9812f25c4b49612b2544a49412724c494921232444849011c2364688c8bd1782ec5d0b91702dc5b0b51682cc590b11602a4518a21422804f89312416c2d0590b015c2b0550a814c2905009e1382684c096128248480680c81802f05c0b41582a05209c130250480700d01903005c0a81302402c0500901001c0300500800c00800,0x1530a3145a835049fd3ea7c4ee9d935a5f4bc95529a2544888d1122144087d0f21d43886d0d2194308450820f41c8350620640a81101a02402800ff9fe3f67e4fc1f73ec7d4fa1f33e47c4f81ef3dc7b4f61eb3c878cf11e13c077cef1dd3b876ced1d73ac754ea1d33a4744e81cf39c730e59ca392720e39c638a710e19c2382700df9be36e6d8da9b43666c8d61ab3546a4d41a7346688d099f2e25c0b796e2da5b0b596a2d25a0b39662ca590ae95c,0x17c8f7def3dd7b8f6ded3d37a4f35e43c778cf15e13bf77cef5dd3b876eec9d8ba674ae81cd399730e55c8b9071ae2dc538770ce15c2381700de5bc3756e6db5b63656c6d89b0b606bcd75ac357698d019fb3766cccd98b3065ecb996b2b654ca59432763ec798eb19630c5d8b314624c2d84b0860ec1982303604c057f2fd5f8bed792f15e0bb175aea5ceb956eadc5b6b696cad75acb5568ad059eb15622c357eaf95d2b9570ac157aac554aa5522a3,0x3572add5aaaf3e67c4f79ed27e4f49d9391ee3d4798f11da3ac7382904a08c0c817001fa3f37e4fbdf5bea7d2fa1f3be5])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB03 : ¬ FormulaSat cB03.originalFormula :=
  cB03.unsat (by decide +kernel)

def cB04 : Certificate := ((9,9,10,156),
[0x1338007c65000d0c6001618c005e2e168b0560f18400282f800a85d00108b6001f16400342b800445700148aa0025154005027130345300108a2001f13c003426800384d001208c440b12c0042248007c47000d08a000c1140040218007c41000f07e001c0fc003a080f400341d800283b000d81439000d06e00070dc00321a8006035000186600010c4002e14800280f,0x15200144a1002645ea0002793a004f26c009914a70009312a680098002592a0049001208e00231220047801148843211042046800508b0009912001221c008042800ec830008906003f204007a40800f8123f800ec7d00050fa003c030f6003b1e4000e3c800e877001c8ee00041d4000439800e06e001b0e200301c4006f001a8d06632188546d000b8d6002a1a40042,0x17302400e402801c60070b75c4007037c00d917b7800dc6d801ae276d001b0006a34c00d10033d96d0003399a00670ac00af16b3000ca64801941f002bc46c8003198a0061afd88006130400c20d8015e1d600017cbd002f82e005786578005d2e400b759ae000b65a8016c11002bc2ab4002c962005902c00af07ac000ad55ab800ac038015403002a14e0052801469f,0x4011f0046c0117003e400d50031c00a90025c00f5002ec011c8c4520cf66b34988a64a0023d1d0046a32008b4540113004461b12004421e00848be1c008642c010713c2801080041401037fc10010280801f62f80001fcfd003f842007488df8007d001f0f7003d1e60078bb5e400783bc00f009801d21577001d8eb003b01a007483dd40073b95d000],
[0x187142418fe0005e80140378d80005e6f13e2588c0005e5013c2408c000524e13a238880004a4d138,0x12a8a82c944068182d1240007e518ac290a2280060100a02014048162c0ae0007a5b1444510e0005e,0x8501106c1a0601303c170480e28c62258000d0552944a2744d1309e0044e00029290530200ac0e03010,0x880a50901d084a40981f03c250780e28c2c0ac2d1a82a0006a0d0a702015c005706a5302c0c8be308b8,0x25e0646017c612a0000930782e0204babc552a41016c141745c04c0f0001dc00578965f150348ce320521104e,0x1328c8548d253154538425203e07800146060a55584633052138d0339525314e1301e128000f22d0001f59c5502a,0x138916381424f850559204791c3f0d63109e229364d1324c12e4b12a4a11a39000139580e0c611040,0x14309c208000a15c400ea3a0e61785c188601d8744110a4214014156430004195a488da4411237118,
0x11b8f43e0ee1a064000721c0782015a1f1581e938408924289a420985013c141561f948210fa21926,0x2080591b0f21b8f63d0f85795c1c86013ab01d80809f198641a0f03b84809243008135d85786a],
[0x1c3b09c0b01c02f6bd6f4bcef2bc6f0bbeeebb6ebbaae5b8ed9b5eafaba9ba6694a4e8ea1a85a1281a027d9ee7a9e6789de769d6749ce5d9724991e46906408fa358d2338a9535494b5294952147519324c5304bd2e4b52c4acaf2b8ad2b0ab2a8a92a0a7298a5290a328899260972589525093248912408f2388d2308b2288922087150501304a12448118441082d0a4250841a06016050120400901c0400800,0x1e97a4df37bd4f52cff3dcf337cd72bca716c5313])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB04 : ¬ FormulaSat cB04.originalFormula :=
  cB04.unsat (by decide +kernel)

def cB05 : Certificate := ((9,9,11,190),
[0x1371b0d468181cc003238800b06f00118da00211ac003834800c86230178b824338005c6500160c6002318400422f800705d00160705b00168b2002b164004e2c800a85228088ae002315400422980070510013094481013c004626800844b000e092002211c0042228008043000f086001f06082001c0fc003a060f400381d8006c39000d07200030dc00021a800642f,0x1003017e005eae57c005d0617a005e06400b65d801700d002d166005a2b400b057801560054a9554005429c00a119a9800a451801362b5100140004f274009a002612e00492540093002411c0046244008f002291086422084c8d000b9160016224002a438010085000a106003f204007a40800f81c3f8003c7d001e0207b00050f2003b1d000723b800cc77001d40070,0x1848020f03840020d05004183a008305c00ff0fc1001028080204110040816007f85600007e3ec00fc7a801f0f7003cc00f176bc800f077801d23377001d8eb0039c5aea003a000e272801bce50038034e300369c2006e039be006d37400d86d801acdb00021b2000235c00d469801a8c700339a2006534400cc0c0599e006333400c80602996006332400c46180188b7,0x1ad0940158ab802b15100556a756005504600a9084014fa6d40014e0380298030052c0149a2d280148a38028233a30028943005045f4200500013e9e8027d37004ea72009a4cc013496802612f004aa52009547c01269280247219200244190048026008e80237178e00235190043c67180045a2a008b44c0116888022c270043c5f14004345b12003fc531000438010a,0x8027e009a80256007e801aa00628016a004f802de00ac8027600988024e0085801f2006080162004c802da009e4ca510c7d399a4c25927001389749210f6723417cae4b0026d2c8f3f9e8da632d95894005baca00b65ac0169b3da801680d802cc0f0058ec364005881200b0014015f00576b75e005706200],
[0x1a11863e8ea000668c1843c0ea0005e8a182320c200066771802007a000665317e1f076000565117c,0x16315045910428d22a89a228725e9785d9745c9705b870001fc6d18a4811a00066a31884711a0005e,0x151142500b02b8b42c94e5a8006d98e54914439083a0d0260881d166591625815e5715a56000721a0,0x10a82607824070300881a06016641365a0002d87064810248962380c0380a050122615c0007021990,0x11b04e1306e1413e2186a12800869088b1964b12a4a00400808019345a0001c9944c9304b8280802c,0x14f0624e0680f0660e982190ee3e0f6178ec3d0f210836060440e0400d0160b9900f832649946298e,0x43a11800610fc3f9961805c16056378e4388340ca270982827c800001ac24831985f882118841207e4e97c,0x2430d4002f4cf0281642c0de02073128001919c52948518bc2e0c02f8ba2d98e53156001ca6693c4e13a0f048,
0xb10ce14cc6334c531c4f12036230892186a158551384d1183c21074130370207fd6c5896057126400ce,0x1660e6361022810623904258941885e1997c3b1863187e3d0f2478cc210fe490ca208fc489805f984,0x8a46b1b86d1cc701484933c2a09d2a00413a5102827c8c1e0e806052ac0060a968056160de170e4388601a06431154,0x131064550686586016854],
[0x1632c05802f65eabc176aeb5d4b9571ad95aeb3165aca592b2163ac658aabd572a3544a855029f53ca1942a7b4f49e53c2774ea9752e2524a293124a4748c9051f2354688cd1522945088d109532a452ca514929051ca31322624c09792e15e2b8568ac1562a8548a814e298528a41462884d09913025c4b09512824c4909112023c4708d11822c4508911021c2a04c09412424046088108148210340600b81602a050098120220400780800e00c01000,0x193724247c8e91922a44c8890f2163fc728e31c2364618c117e1ac338650b61642174ae91cd399728df1bdb716e0dada9b52690d1da3344684cfd9eb3c66ecd99ab32656ca58fb1e63ac718db1a])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB05 : ¬ FormulaSat cB05.originalFormula :=
  cB05.unsat (by decide +kernel)

def cB06 : Certificate := ((9,9,11,201),
[0x13b800e470371b0d4343a8006c7300170e200251bc004636800786b00198c862301785469000c8ce002e194004a318008c61000f0be002d17400522e800b0562a088b6001416400262b8004855001409c4c0d14c0020288003c4f000709a002412c00461e1240044238008047001082845000f086001f03882001e0fc003a1e800703d000207600010e40036198005021,0x16180188c1002f97a005d2e400ba5b8016a0059abd6800592c400a91bac000ae568015cab002a466ac0028c5eaa002a000a65280144005027c009a4e80136004c25800944c8012e00492411c8c450b12a001924c0030488005c8f002211a003f22c0086448010489002103087001f90a004004906003f204007c3f800f47f00030fa00031ec00783b000e879001a0f200,0x1004321200838020b01830020903003f46f0200401fe007d8c5fc007e001ecf9003c9f2007a059ee00773d400f0083cc00ee78801d8ef003a9de00053b4000475801d0e700395bae600391c6007238400e46f801c8230035c52e2003544ee00034c4ade00371b6006e36400dc0d801aa1f6d001a61d6c001ac006833c00cd64b3800cc658018e2965001901b0031800c4,0x1005a2ce00b45840165b1d9801640a802c40f0057ebb60005781200ae00c015aac802af53ac002ad550053c53540054aa200a7886a000a7002994b005228e00a45140142a08027d3d004fa76009c4dc0134998026931004bc012d94cb8012c958024a379500251270048c63260049001208f802411d0046c01198ac6801188b80226378b002282d00448011087802190b,0x174801a2005f8014e00ad80292009f8026a00908021a00628017600508031600be802d200a55026d22873e9ccce5e29001469e4ca3d0a7c35184b84f002893a9847210ee693016c9c0062b1200c560c0187c2e2001860c803081300606ff82006001a00bf01c017cbd802f975005e6ef7a005e02e00bb0440173b8dd0017205802e005005bc016db5db8016c1a802d42b,0x200a680286009c8022200],
[0x18119c2e0a8000527119a2809c0005265198228800006e581962108000066561942087c0005e55192,0x1001dc691a64911e00052aa1a44811e00042a81a2410fe0006e951a03c8ee0006e8b19e380da0006e,0xacc8d228871f8751344a0f4080295c0007c1a86a16446112430fa3a098248785f97c5e9785d9745c876,0x1000b62c1c86b94e5314a350d0360d6348ce6a9525b0007c9ac52146510c8318cc329505b000779aa,0x83c0e1585516458184d705c14040000580202331188000ba141b00a826090b62d0be2f0ba6a1ac699aa,0x4666d00008e1015855344591604f24461148941805124ccd330d2360060372992a62186600002e9b22b822,0x10480e058140400c6d93a5a800239b84c12e4b0060100a021385a8001e9b6221942388c6580224000,0x1068180f8326e03c0c1b61b0386d0420d9b21c84c12874139423e0901c04800120090fc6e9364d132,
0x114056151605b8003f9bc16860160661b8641a1923c0863d88e3d08c67996110464f9404f03a10034,0x5886198460942428e6120007005e57062578665686e6e864171bc20040ac43a09cb70201f5be5615655052,0x568400dc1a9be408de420e4418e26819c0d04281021c4c1291c459103b0c4298961f84e6418e6318a],
[0x15c6b656bacc596b2964ac858eb1962aaf55cab5562ab554aa553aa654aa8d4f28650aa1141a804f89ed3d2754ba9712925149892523a464829011f2354688cd1522945088d109532a452ca514929051ca31322624c09792e25a4b0958af15c2b4560ab1542a4540a714c294520a31442644c09712c2544a0931242444808f11c2344608b114224440870a8130250490901102102f05c0b41482704c0941081802e058090110200240400700800c01000,0x65ccb896f2d659cb296324247c8e91922a44c8890f2163fc678cd19631c618c117de73cd798f2de43c7788e95d239a732e51be37b6e2dc1b5b536a4d21a3b4267ecf59e33766acad94b1f63cc658b314626c3981301600bd97aaf05dabad752e5])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB06 : ¬ FormulaSat cB06.originalFormula :=
  cB06.unsat (by decide +kernel)

def cB07 : Certificate := ((11,11,11,837),
[0x114028c0009e1420004b0a10002704d09807827c0009e07a0004709d0001204e80010026c0007c1320004a0921200b84b80011c2540003a12a000400930001f04880011823c0008611e00045088044234000801160003e0890002104101610e000400850001f0418000fc2040007c0fe0003d8790f80003d07d0001e03e8000141ec000020f20003c0030001d83280008c0e4258000941201d0000900ec0002c0420000800702a0000a01201000009009,0x10003706f8001ac37c000da1b00906e80005836c000d01b20006a0d203035c000201aa000680d30003386880001833c000cc194000640cd0002f06680016032c000c6188308600be0cc3240007618e000500c5000238618000e830c000801820003e0bf0002e85c0b61682c82a0bd0002905d8000c82ec000a0172000470b70001805b8001002d40007c166000570ac1542a05304c162000290af0002805680011c2ac000501520003e0a700028852800,0x1000478908002384680d11f0000808e80022846c001162320008a1170004488a80000844c0011021c000861110004008880021e0008510820c4108106821a0007a10b0003c0848000e841c0007220a000681030003f87e0fa1f03d82b1010001907f8000c43f4000de1f6000300fb0001787c8001a03dc000f21ea000780f30003b8788001cc3c4000ec1d43a01f0ef0001207680008c3ac000d01d2000720e21c00c073800074394000381c6000680e1,0x12c859c001622ca000b0163000018b08002bc5700015a2be000ac15f000574001562a8548a814e0b0150ac8000c855c000622aa000a3153000178a880027c53c0014b2925300014829a000a503d0005201980028851c001422800680b145000080a180027c5040013c27e0000700a27a0009d1380004d89d8002544e4001342644c09712c0b04dc0006426a00031133000480988000bc4bc0011425a000931242440c89480024049c0011824a0008a123,0x10e869400166346000b11a1000670cd19832c6502d19f000190ce80030c66c0017433200030199000598cb8002c46540019031c630c518809c64c00052322000c318f0005d0c68000a062c00162312000c21870005f0c3800304600bf04230a000ba183000120c18002cc604001622fe000bd1782ec0d0be8002e85ec0003a2f6000b3179000588bb8002e45d40016c2ea000b816e0505cc001662e2000b116f0005a8b401c2da000b316b000588b4800,0x10001c0ef8003b076c001d63b2000ea1d7000730eb8003a4740e7042080754001c43a6000241d30006d8e880036473c001ca3907181a03239a000e21cb0000e8e580036c72400038392000d91c7000708e2800378714001c037c0a0131c30006d8e08003646fc001ba3700700d1bd000080dd8003646e4001b436e000d91b50006c0d980000c010d880035c6b0001aa35e000cf1af0006b4001a834c690d11a00d86ac00076352000c31a70005d0d2800,0x140486c001f4432000f82170008490a8004148540021041c8302221300080908800090844001f441e000f820d0008210320406c82c002024120001d2090007d1038003e081400200406000fd2030007f8fe02a402000fa1ff0007c0fe8003f07d80f1fb0007d0fc8003e07dc001f23ea000f81f30007b8f88000107bc001ec3d4000f41ed000770f68003d6000f31e43c4780ef06c0d47a4001da3ce000eb1e5000710f18000e878c000723c2000d91df,0x14b60012c8004ac950002524ae0012a8004a09392624a4901b92980048c9440024249e0011824d0001d1268000e492c00228492001222470009092280048090c002384860011f23c474111208004608fc0004847e0002323d0008a11d80046c8d1190364720001d2370000e11a8004508cc0022e4620011622a03c8bc0002045a0011422b0008991480001089c002244440011022500088c0021e4388690c2160b88840006443e0010a21d0001890e800,
0x105e0014e83b53c0014da975380014d299000a68118005260b54c00052ca540029602e0014982152800149000520a3c0028c0060014580051200143a835140013da88000a19428004ea1dd42000504a04002824fe0014127d0009d432a8000099c30a7e00097c2fa7c0009e93c8004f49dc002750a69e00025f0a29d8002740009c9388004d89a93426f000999368000709ac0025c4d20013226700098930265000081318004b89840025e0009612e800,0x15be0016eadb5bc0016e00d000b68018005b20016b8005aab456c00059ab58002d45a6001658775a4001682cf000b402b80058a18567000594001642c7000b0d60ac4000b0812800580064002be57a0015d800572acd5d000570adc002b856a0015c067000aac3bab6000a743aab4000ac958800564abc002b255a00159055000aac32ab0000a7430aae000a4c2faac000aa8002a854e00152aa154c001522a3000a901e80053a12551000540a7c002a0,0x1634c618b03263a0001d31b0000e18c800614c5c0031361ec50003126220018682d6200018701b000c300030960ec28003086160018330b0000398480061003c0000460e00183005000c14003035fec10003026020017b8776000017f2fd000bf97d8005fcbe4002fe0aa0017b8655f80017a8635f4001748615f00017b0005e4bd4002ea5ea001782ee5d80f81e2f3000ba1788005c4bbc002de5da00173ae55d000173023000b900c8005c0b8c002e0,0x1000d58278006a8d4c00351696d480035069e001a834d000d402180068a125a700067211da6000694d240034a68e001a5035000d141db48000ce41cb46000d0d9fb44000d09a280067cd1400342682001a1029000ce416b40000cf19d01c67e0019f01d0000819e800668cec00338000cd99a800664044000066620019780065aca597000658cac003230eeca80032864e00194325000ca02c80064218d9300062a185920006440018f321000c7190800,0x1714e4c00390032001c638f000e31c5800712001c3b81710001c3385000e19c18006de1d5c20006d61c5c100070016c0037e09a001be37b000de5b9b7a000de1bb8006f0dd400378086001bc03d000dbc24b76000db423b74000dc9b88006e40d40036f076dc00036c000da1b58006ccdac00010014da400006004d9c00365000d8c003616b6d90003576c4001b035f000d81ae8006c01b4003450ead78003390e6d700035a6b2001ad05b000d1430b58,0x10c2f30003ca792001e3bc3790001e33c5000f1820800782125e20007840dc003c2066001dfbbd780001df3c1000ef81580077c09c003bc03e001dc3bb000ee1db80076aecddb00076803c003b200a001d880075e001d6bab760001d3bae000eb034800754ea4003aa0ba001cc861750001d23a3000e85ceba2000e81cf8007400fc00399092e780039c736001ce031000e641db9a000e5dc8b98000e59cc800728e481502472e001cb02b000e39ca800,0x1000fea008007f8ffc003f87f6001fc8007ee001fabf17ec001fa3f3000fd0378007c61d5f90007e0174003f00b6001f73ed000fadf3bec000fa9f48007d4114003ea086001f18497d0001f33e5000f981b8007cc0d4003e3076f90003e17bef88003e0056001f0029000f780f8007bc074003dc7b6001ecbd77b4001ec013000f60088007ac024003d600e001ea8007a6f3dea0007a4f44003d20de001e906b000f043abd0000f39e680079c174003c1,0x189d132254488a60022345100110a278008811340005e896002194490011122380088910c0043a8820021f43d0010d416c3c0010e21b43b0000821c8008650dc004340010c2198008620021642a85109a1242f0001921680083d0ac0040c852001ff427000fea128008440021041f00106a0c41683a0020641b000ffa0c8007f505c0041282103a0a80081904c003fe822001fd40f0010120680081101a058007fd024003fa80e0020140080a001ff403,
0x18ee0022b475000f74003b9000e3400337000b84002bf000a440045b000ff4003ef000f2c003a5000df400355000b24002a90009cc0046d00118c00445001084003ec790e89bd352640bd1632a64e0001f13c0730db9a23145d0b114e266000f69db38a6d4cd1852de578a392e0008e600238c6f8e40023806d0011b82d8008d91ac004698cf1a80046606a0023201100118a308008bc0c40045c0320022d45900115e2ac58001158058008a800c00450,0x1000d0e548005852a40034394e0006eca7001292514a093d2724d49892d2524949091d230000ce1af28c0028d52d2840025f4c927c00423809274004608bb26c002c4583264000d01af25c000d792a0006bc9300035e4880067f23c0022f91e0006bc8d00122a4448690920a4047e8f91ea3c4768e80022ac569120012fa5a90e0013aa5a90a001bd369906001a23339020006f8ce9020022c4578fe0019a3338fe001b4c7d0004f63d8006d31e400369,0x15bcbae668004508e6668001a039e668005d732c001cd996000a4ccb00039e658006953240023999200175cc70008e6638001cf31c0023998a000a4cc50008e6618001cf30c004c097d2f25d4b896d2d2594b095d2b2554a894c00160ac297e000670dd97a001983439760003c88c976001dd3bf972000db1c397200211c0a96e0022143f96a001a934396a0022043f9660019a343962000680dd962001a1caf000376578001bb2b4003439560006ecab,0x15e73b4001c43ab3b4003346a33ac002284833ac003519d2000eace9000bce7380048339c000ef9ce001a8ce5000906728006a338c002419c6001a8ce1000906708009bd3726d4d89ad352694d099d332654c898d312610007c0f9e6e800686d2a6e80067ed2a6d8003787366d80076af0a6c800666d2a6c8006cedca6b80060cc766b80044c8e66b800672d2a6a80036c7366a800847052698008d519e688008c117e6880068ad2a6780038873667800,0x116343c0008e1634340007c16342c003a6a12001ab5070002c68280059940c0012ba020027f4fc9f53e27b4f49e53c2774ec9d53a2734e49c5380003c278f3f40034a6a33f4003bf78d3ec003977413ec003436a13ec001c23ab3ec0008c13f3ec003917413e4001bc3ab3e4004658d13dc002dc5e73dc000ce1df3dc003306a33d4002264833d4002e25e73cc001b63ab3cc004238393c4003c878f3bc003526a33bc003997413b40031463f3b4002e8,0x1a7e001a535ba7e0021fc52a7a00160ad0a7600067101a72000b019fa6e000b319fa6a00211c2ea66000c319fa6200101221a5e000ba19fa5e000a3159a5e00090137a5e00068101a5a00080d2b0004069480020349c00159a4a00080d230014828f51ca354628b514a254428750ca1542283504a05400003786ff47c003516ad47c0039d74d474001282574740008c16346c0039174d4640007a16345c001122574540025f4f544c002754f5444000a0,0x1ac5582af55cab5562ab554aa5542a754ca95522a30006b6d82b48004f4a1eb38006a2d82b28004dca1eb1800686d82b080067ed82af80019c436ae8002c06aead8002cc6aeac80048c94eab8003b47a6ab80030c6aeaa80068ad82a98001a0436a880021b53c0010da9a00086d4b00056ea480021b51c00544a855029f53ca754e29b534a654c29752ca554a293524a44001ab35ba86000c919fa860023446fa82001d03aba82000ea1dda82001e13cf,0x800ad751690cdf98329645800ad74867fcdf98329645800a8b4867fcdf98329645800ad55a2b3564],
[0x24cc0001dca10d244e84cc000194a00d204e04a400017c9f0d1c4c44b8000114d84d44de68c25825425024c0004c44ca68a,0x169e2be2ac0000ee56c69c2b22ac0000ca56069a2ae28c0000be55869829428c00005a53069628e28c00004252869427c,0x105a6806a834c3400000ee6546a632e32a00005a6206a43143040000ee6006a230a3040000ca5f86a02dc2d40000ee5a4,0x147000085885e6b23b23aa00008e6e86b039035a0000e66b86ae37a35a00008e6986ac37035a00007268c6aa36435a000,0x18988948a66b84b04a800005a8786b64ae4aa4a64a40008708766b44a249c48247a49a47849e4984764744944725024ea,0x16bc4e444240a3d23582ee2ca28a25051251050e50c50a50850624c0006d46146ba4c44c24c04ba4b84b64a64ec4a4000,0x140640432231e3263246ba3a83a43566bc4c86be40a5100008ca8fe6c05204cc5040008ae8fe6be51e35850c0006668fe,0x14d24ee0008ba9366c652e52852a26625224e0009149109049008fc8f88f48f08ec8e86c45263c04fa0006d29066c2408,
0x16cc54a54247a47847647447250249647000094894494093c93493092c92892492091c9186ca5442520004c893e6c8540,0x32c12b92b12a92a1298da8ad8818a20000efd2e4da4acc96c9d80010fd2d4da0ac870c9f0000d0d2d4d9cac0000bf686962,0x56793693c000233a689b696700018317d344db0b2c5dca14000bad334dacaecad09008fc8f80606998097c978974970968964,0x2dc0b70b409149109048f490c8f0908080d39bc9b89b49b09ac9a89a099c99899499098c9889846de5a435a0006949aa6dc,0x6772762752742732722712701ba1790bc142800179a799b997790913f8001e3a779b91770001bad453bcdc4ba4000dd6a29d6,0x5a8a8f9bb98880001ae75474dd8c387f8800000e45464dd4c04bc09249209048f491c8f0918080779fc9f89f49f09ec9e89e4,0x160a6066146163fc39a2e028040039e2e4284266252000a40a3ca38a34a30a2ca28a1ca18a14a08a006f062439a39e000,0x121020c000404a5e6f863a17a17e1780002e8a5e6f663811a11e11800028ca5e6f46340c80cc0c60001a0a5a6f262860c,
0x10003a8a827046460103d8ce53938132200803cb029b9c01908040365994d4dfcc8092c0010b94ccdf8c7c0201f30ca626fa63c20e,0x4330460318002a22a12a029f29e29d29c29b29a2992982972961c29960001ead6d50ce10cac0202f324a867066501c81cc1c6,0x9241251230002465573893360e500020ced2ab9c419a85f00417f554e1cccc194020efaa270c65a62c62e62a63063211a0c811e,0xd5e55c55a55855655455255038e33f14014200028756738d33a06500834eae9c619c85f0041a756ce2cce02f8020d3ab271466e,0x9d335d38f2211772892850000d1390204202203008fd400806c2ce3cd04cbccc4cc0cb8cc8238194040b5ad4ad0accac8ac4ac0,0x5c98051321329318048060058008e61f4e480801b1201224425120002c672200200000443e43c4404383a22e82ec2ea080082,0x105c01e06a05a01c7242c800019a11c7280400442a42a829e03803604804603c03201e03a03001c7242aa4f400011c142,0x102802201e05a02602001c72400019a14056472a07469c0762c42c02c62b406806604c04a07006007206207c07a72606c,
0x172a07c0720401cb940360000fc1a8098080000f60003d72c06805e06406207a2b42b029a29629002a02402e02c69a7282ba2b805c,0x20780003903a026020020908cd39801a14e01c02315014f02010dcb1ca00c8000820600608154072e07607406e2c069c2bc2c42c22c6,0x115c12e12812472217c17a17e3a017800053a30c57073203e2a20442a62a429a2900242a804802c72e72c29602a02e728,0x21dce686dc6cc6c026425826c2687142c42c02d071c7187387282ec2cc2e801cd382dc000b317216416c15e13012a12616a,0x12de6a66a269e0ac7200c84604243f23c03862d22aa2640cc5004fe4fc4fa4f84f64f44f235231a2e60c60001fc1f41f0,0x45982d9a685802c0ac02b9a60ae8ae0ad8b19cc83417a9c48dc590020b97364e83083440b40b82d834a3103503182e234e316,0x100030e2e873a36613236e3600001180017c040c6000d105d4e70898890888020cf46617016e17646a4de46c4e04624dc174168734,0x22802986e4e70e746f06e827424c2700004f30e69473c14814a45845e45014013e14e14c14413a126142138124722460500,
0x4e30591cf8578498570491c880495ed14670d68e8028c2946f8e70e747046fc708e7829c28824c284248e44005ef30e73e13c,0x129269669400673673e0004cc0427442f62f22f408808669429229a29673673e0847200005d01ae04674238a16038e168,0xb901d400109c8385f03291093308405f8331449411008e80a188305e0318001a290e07803a17f1d201077a003c100e74629a298,0x22cc16cd4017c1801506242dc4003bc3a83fc3b83a43a039c874880878748003fb3a274617273e16c12616a1247220ba084,0x13f83f63fe3fa0c43d60880867440c22722780bc0aa0900b20b07340ae68e27628227e6921746ae17639639439c740208,0x2738730724e9474050c0203974c39c39474001181b5118b18c3a40b701028c004a22fc7406342f0040c774a1e03dc1e43e22023f420a,0x150000068a6a07503f03ec3e60a209a0a60a409c0947203f24fc0001d81d41c81c41e274e28227e27a69269000e166740,0x47e07b87f07e8819d31d382580300287a82607d0280020df0e08279ab0e007c87a07507c0798242467500255f4cc460512504,
0x8213aa2262252230f00ed0f20f10fb22b0fa0fc22e22d22f22900014c7c87a0778760000de3b83ac2806b41042a75245e45a452,0x87f0433aa39b39f04504239008d08f0010dca18460000aa03b89f1d609e9a400037601c50c000194eac524d28534530d2c02255,0x129033229a3302986a469608c08e2ce2d02cc0880920902d6342021069a41a316d13b0010c4a080085e4fc0042d6920fc1140b6756,0x23bc3b0002d91d61016b810b747285f0005ba3982fca24a0886c002dd1c6178000a8a9be68a0c43ac75a11611010e30c10c10210032c,0x215c650d1c6404ec1f05041f44fceb0d242e82ec3782dc374724d5c73072c728384738368408224e80380364002d1756200,0xa8628528228027f27c1d0008594001aad14c741893eceb882c82481c0218b20242620a42a42843442e1c41b81820b018073431c,0xb0403c03f39801400f01300e39238a0103ddc302500032ed84a38a30a2c000e533471e35c17c4423582ee4cc46042438617e512,0x121243a4406c071843c3564d40803a42ea61a5144c82ec01a52c4ca7162e82880104c63541203a274673670e17273e60e,
0x16ce6cc55c55655254e5342041120ec75074036c36a1660ee0b67562604b46c825a6b468a4ac35e2560d808675421e214,0x125e22009616e59258a5805783726aa3920a45b259a5b45ac6dc58837837667c67867666839839474c6ee38468039c570,0x9a318716d13b28d07c000a4d9e9c68a090783e804516844af8dd8db0eb0022814181043e64d017433a68c09a176338222098336,0x55c95214f14e94e14d94c1d082206c06906103983594880056260c684eb43041a0164160dbc30019ce68b506381d0021b9348,0x132c54633229a5623302984b26a46966b608c61208e6107262ce61e02e57453e2d06ea6c61a602a2cc3d64ce1866c4558,0x119018e4561a81ac45c45845e45222423023423671271c6883626d456a5f65fc6f06186040f20f60f40f00ea0dc0da6ca,0x4084c21426324820e17c4422ee4cc003fb9c31251080bf289285282001fd53e11b8084b648c418005436420c4a8a75e44819244c444410,0x1001e4ba62ff2f43713773702e72e22e02de1c2068994820044c6968d9000267011348019ac8e087800cce4283a042439c002570a12c81096c004ba1225f,
0x133833633e33c1e12eaf908096c1c4ba0225f0013085098c049ee042696ec3f0031358009bc2685d88882608802588f05b88e97197a8104e2d5c14c0c26d,0x146c22446445220a45e2024581e41ac1e01aa4121966d256a6d46846e85d875c5e21b075a6de5a841e42257c41810433a,0x5c00ba131800972df42e4e7cdfc0426d6f209408a0344d8309dc184f27405cc50c00281a8868a3aa364aae760242244236240234468230,0x13783763743983941a619c38470839c1867507401a41981846fc6b24a0012f3a5f25a35a25601092c1c49ae04878002514c82ec4ca,0x42c82c1ae1cd0fb92f02b8fc1a38f98b689d8268b88a08290b789f9d31a79a488185d1d485d88887a8678260009060021964c,0xbb13291fb38510537c1010f20f01ee1f11f50d40d6028fa50790890606886b86c86d1c419292c9ad800df6c905a05987ac026f7,0x593000702368001591c01b27507401b0000ad82057401016007390139d85858404c360e15f040b08e5008584e18730042ce9f086c7406a45cc50c38c021693a8,0x4c810983e10583e90490383f0780768400790788409be1bd1c29c100508ac94042f3020a18220f404286978008390041d8020f40107ed3c0a74f1c2,
0x2e987307280029d20670839c3847527407502021ec0b1538ea0ff0e90e8128ac41056a0e2b94047641b81821c418042e31c43432842a,0x80192ea21d98fd9949c29be19292c82029e081512da2762e22822de27e69e6923f01743e617609a16e0980960a43923726aa20a,0x26d4082b90145f80995c3f83600855a4703b83ac0440901457b8105a2b5c001d156df4148a96fe03453b7904e0298fc04232490021190071f92500845c01c8286c06649,0x14266d20454bbb23340018540064218613648024378098541cc32046210617898704acac045d20064b0980963926ae3726aa00172829944e701ccae0a65974075036c,0xafd1f51f1001d04299a310c0f70a41c697c8fb8fb000dfa7cc9a0134af0148e9840cea43d44bcc98e10d000099b76243442a6d4,0x11840d61820d01800ce31c3286c432051a0f80fa0fc1005aa3be3ba1026b06f409e70a6520a23f80a05da3f45c65ea67a,0x26886946a069cd4c2e82ec2dc72473000eb17661667560771d9a900a3ddda008cf6460afcdbcd0ce38066bd6367606e85e20dc1860da,0x2102eb4e8051748f00ed3a03a83b43b31b61b50f20f10424fc18b2e4e9470918397d17c0015b4bc0bb93301627a0455d0589a808bb400a9a0004140676a75e,
0x8590583a63ac39a0027943a02b8c2001c6e62018307000ba8dd0cf04c0cd010c157b1b99729b59641611b49058185ea0071d30230041240e,0x86830904717f0c0067000d057c8fb0c701175a85c002c132801199a1a1f326819004250d0a9758bf02695e14683e00063684c003190a40fa,0x21227b085d9cc13b60de0e20e10da0e00d90d70d10822be36f3420525d5b500d2e6b54dd00035b3be5f41b81980e60d608c3b6042182,0x174c20a01125b6b2c2103040954c08c01d48e70e113a08087b0044f6ed408bbb6c868a2560d80136691c0ff0095bcd44fe49041c1427d24a210,0xad50088f4ef80047e022413b60212397f190028944bf14683e008aee0025f7587340d1319f6008984fc1b600d7468d02e8134af08d82ec1488c804555,0x10312290705930c84030982634008c10126094c3b702940da11ba17d0109759b114897c9bc1bb000696b200c3756ca5340610f9962a301c3a40046a0023b,0x8107cc0c3ea001f9010fe8087fc044020220542e17409a4341760a44280222b82081c044160246d0310b8211fc00412ed4ed86d8028db0a46e82237cba1318d50062be0c23d,0x2384388063d910a1b81061be19656a6d45624b21866b619818408c18208e1802ce31c5742d03282cc2fe3205585720882fc,
0x1040dbad92cd11d3571cb1ce3a01103551bb1ba1c23a82743b43b31013b53b63b71b61b503865c01ed6043a5010c79ab098634887a60a3d5770,0xb6a2b10d300069c6902434a021a7120d48006ac0cc2233c13041440c4787244446e4dacb08ea4b18af873072833412c043c53023001ec108,0x135200b548633b9018dac8911491791606b005b2236035ceb4dbcb5477c76c5fc7d8db07e0028cd1aa1960a456a2fc46846c46474c,0x4ea81b9dd13a0d10c20072fa69c62cd4cd442e82ec9bc9c09b82d02e02c4e70ee00089716473e16c15e00c8d80e47c143922fc0a1d34e2,0x87c07d3ac0893b91b01961b71991b419835435205574c2db320e083000fb8c50433aa0154441c0e20021f001108be0bd0008b45f8004829c46a403435,0xb4512b3aa39b048524fc85f93f13880ea3ef90f10dc00eceec83484483c02eeb1aa1941a618c1861a418818418218031c328320,0x28847a87a4998003c750e5044e246e4363d035231a02710a4d3bc1f81f71f41f51f227320e1d622700400180c2c1cd035702180d125a,0x48688708f88f0811dc80439e04c731307a9e623526f1e72362701e22310183a48200c1ce430050cd2160386683da9c20176063b53da3d820e17c17a,
0x24704284240c0f504d8e81384c5e910933092802f428dc74000e2b48477a42c4324e63c843442820a2023e01e43de1e044a44c466446,0x20049577442041e23077a40193805bdc0c11a183190129c810c5c032aa78070c2fc0194f4fa4f804187bc63be010e15de0008ee8d07388d87188c42d004315,0x13c03864da39a2800115a8099ed3e93e13c1388e780455a5084cc4a44180011739a77e2242222207766aa3b03764543be3b838437e,0x121818a03b1e91310b03d8f42dfce02fe90493d8b20ab02a9ac138014d2dfc0415f150008848429845601585481409a89a0f68f60e209b89b00c58a02679,0x584815001f7e0a4aa059cadc12fb955e55a55855454c0664383becc3a0075ba2242d70616815a6f6170162154524738770007f5802a2401fce08fe9,0x86e0700c60c306d06a0cc0c40c207306f06b069023d45018c814680047e00d270011daa31b7003f2db41588da0018ce784d5000c6705808c,0x2dc8844b44b60b30b1cbe0bc4ba8b98ef8ba0b90b84b7cb74bccb28b0cb04afcaf4b4c464460ef406a8d1a00ea0e219419c,0x13b445622c22a22e2286f06e86ac6263bc5f838045c45a6545ee3be38445e6da4d83ae3744504d66201a20e45ae418600,
0xbb9027bb4207e617c150d1f48211c40056201c0f001f8a71009625e71e01b49b51051a11399c28f81b79938f796d8008c63c8004676ca44653221a21c,0x4650630620a894636c3742e878cd5c2ec79472c9bc79c7389c0788718367b701acf801ed47305f94113890d8f4012b4a758f0413bf1204,0x2efc36035cf04000f0804afd42e4347801be],
[0x115a2b0558aa152288508a013e2784e89c1362684c89812e2584a8941262484888e11a22c4508911021c4308510820c410811001fc3f07d0f81ec3d0790f01dc3b0750e81cc390710e01bc3706d0d81ac350690d019c330650c818c310610ae1542a0530a41442804f09c1342604b0941202384608a1102184007a0e8198320620bc1702d0580ac1502904e098128240460700d01903005c0b0150260480881001e02c0500901001c0300500800c00800,0x1384704e01bf37c6f4de1bb3726e0db9b636a6d0d99b23626c0d21a3344684d019f33c674ce19b334664cc19732c654ca193324644c818e2c4584b015f2bc574ae15b2b4564ac1572ac554aa1532a4544a814f29852ca514929051ca314528850ca11412804fc9f13d2784ec9d13821842c85104206408809001fe3d87a8f11da3a4740e71c838c708e01b23606b8d61aa350698c618a310618c217c2f45e0bb1742e45b8b616a2d0598b21622c0578ae,0x15bab716dada5a2b3d672cd598b2d652c658ab095fabe57aaf15daba572ae15bab255eab1532a5548a6d4d297526a4947a8d518a2943a86508a0d3da7a4f29e13ba744e69c137a6e4d89ad34a684ce995322634c49852e25b4b29612b2554a494127a4e49292123a4648a9052023f47c8f11da3a41c8350620b414825042073f47e4fc1f73ec7d4fa1f33e47c4f81ef3d67a8f49e63c878cf11db3b4764ec1d73ac734e61cb394724e41c738c714e21c3,0x17d8fadf53e87cef95f13df7a4f45e83cf798f2de43c7788f01dfbbe77aef1dd3b7768ec5d3ba674ae91d0b9d738e65cb395728e4dc9391720e3dc4b86706df1bdb7a6f2dd9bab726e2dc1b7b6e6d6da9b4b666c8d85afb5e6b0d45a834f69cd35a5b4a68ed019f33d678ced9d33966ccd599b3065ac9992b24646c899031f63cc718db1a630c5d8b315628c4d89311620c3986b0860cc157e2fa5f2bd57a2f35e4bc5782ef5daba9742e75ccb9571ae2,0x1b2163ec758db1962ec5589b1161ec3585b0960ec1581b015febf57daf95eebd579af15debb575ae95ceb9571ae15beb756dad95aeb5569ad159eb3565ac958eb1561ac157eaf55dab956ead559ab155eab555aa954ea9551aa153ea754da9952e8a512a193fe7f4fd9f33ae54ca894726e3646b8d51a63045f8bd1762e45b8a914e2944989111e22c4488710a2043e8150260440780d015ff3fd7f8fedfd3f97f0fddfb3f57e8fcdf93f17e0fbdf73ed,0x6e35c5b8970ee15c1b816fedf5bdb796eedd5b9b716dedb5b5b696ced95b1b616bed75adb596aed55a9b5169ed35a5b4968ed15a1b4167ecf59db3966ecd599b3165ecb595b2964ec9591])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB07 : ¬ FormulaSat cB07.originalFormula :=
  cB07.unsat (by decide +kernel)

def cB08 : Certificate := ((9,9,11,207),
[0x139800dc71001b0e200061bc000636800d06b001983c1a34800486700190c40030194006300178b85a2c1586861000f8be001e174003a2d800a85900128ae001c15c00522a8009c5500140385300128a20012144004c0813c004a26800304d0012096002312c0008248000447001107e000f04c5600150842a29000802a29000a04416138004417138004c240c0004819,0x15680156005329144a04f10152002229c009052800fca3001e942003827c00424f80134984b25124364e8007c9b0024132003f25c007a4a800e093000e1260047244008648801188a440c11e003f234007a45800e089000c9120042209002c43800fc85001e9060038204002e40800f87f001e8fa003c1ec00743d800ec223c800e07700090ee0039058ea00381cc0018,0x1003e9f2007a8f5f0007b001e4f1003bc00ed74bb800ec75801ca4575001d0e7003a06a00698e5cc0072001c4e100379ba006db5db8006d36400da0e801a6256c001acd500358220069865a80068b3da4006802400ce0180198cb003218e006280186bf6200184c1002e48ac0002f97a005f2ec00b91faf000b31dae800b8002d96a005900160af002b15400542b4009c,0x19fd100142a08028431004dc6740004fa7a009f0b4013717cf0013a9c8026b339b002680d004c80e00984bc012a968025014074ac0018948024d250048a42008f8023b198f002391b004548b1a004622e00898f62c008a0021d110042a22008607a1e00834340024868021012858020d090006212008241c010283800150500012060080801fefb80001fcfd003dc8afc,0x19749224f4703296800b455a712c90441e0dc632b80176ba802e771ba002e41b005c01e00b75b4016ab4802ce00b2d86cc00b258c0164208029a43b1002c15f005806e00a68e6bc00ae56c0158ab802ab51ab002a953005504600aa07c014d12d48014e0b04aa200a853c01500b802a01300534334e000629e00a5d269800a5034014a058029007005200a00a35140143,0x4016b00564013b0048c00f30037c00c9002c40177005bc015d0051c01310049c00e30033400b7005b2b544],
[0x18d1a8398e00008a7e1a6358ce0008a751a42a8a00008a601a2290a00007e5e1a02889c000765d19e,0x1088c631000299b46b1785b15849914378ca2c89a6719a66196651926418e00258881aa431060008a,0xa8ca50010b540d81780802b06818070c02f8c86b026090ca648002a9ae308ba2e0b604810058140801e,0x8002a0a4153680802b538fe3f10055150559b0411025619a002226c9404f1383c0ee3d0f23e1443d8fa,0x11705a0026e438f49f1b81a8704c1344a8661806e1905c1b062168741c93661800488f4381b602808,0xa44de0d0970e0992609a37092240370d83a0e4210b8230b4db0001266a3d1226e85e4a066190624b12a,0x13a1a86996e5693647916330b42798a62186611826017e5f1123b0002287a6f922110486d9ba000f4,0x1170800c9bc2207a1682c6b896250382603a5a8dc2c0920d8003d0e01f1c05e9083890a391103a90e,
0x8fce1020694d00a8280d02e678d4348a6368ae360ac0c1a4689be23890219645a15e208782287c2307e,0x930490014d298a4288a0590e30a8174327082c6b8380e8dc2c036000d4229c42a1a02b8ac6880e2c000,0x1009504614e5515255944201c2471aa6c894561762619a6316a24800a8a9ca69c8211622416659096,0x44811800a60e272876570825815e5a1c6239c41003e5c9745c11a6d00c0194c010082160210f160541403c,0x5ca1304a529ce000e674142001c8539ca730001020029da89ce15058149c070800110e0731404f93a11042,0x5d2229ca23000076440180ec0c2ceb5008595d4020448f8e50fc2e380de0f42d0ac273a0a439c403844a000386c074944,0x22c1e771968],
[0x1584b055e2ba560ab9522a3536a654c29351ca1d432854f69e93ca784ee9d93aa744e69752e2524a292523a464829011f2354688cd15229450738e69cc396728e49c838e718e29c4386708e09b836e6d8da9b43666c8d89b035e6b8d69ac3566a8d49a834e698700df1bc2bc570a714c294520a31442384688c1162284488810e1502804f0941242404608a1081682c04a0900e81c0360680c81802e0580a8140260480881001e0280400700a00c01000,0x187d0f61e43a74ae91cd399722e3dc5389708df1bdb716e0dbdb736d6d8dadb53696a6d49a8b4e69ad29a4347684d05a032a652c798db1a602c017b2f55dabad752e55c6b656bacc596b2964ac858eb1962ac4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB08 : ¬ FormulaSat cB08.originalFormula :=
  cB08.unsat (by decide +kernel)

def cB09 : Certificate := ((9,8,11,135),
[0x12c19c005432800946300178b85a0918400582f800a85d00128b6002b16400542515c00522a8009c5500140205300128a200260309e00251340048258008c4b0002092000211c00442100080450010c003e1e0e870360b104001e1f800383d0006876001a0e4002a1b8006435000b86a00180386600150c4002c050bc002a16800502b000985600030a4000213800481f,0x15680156a75600154a90028c4aa8002994a00508754800510013e004ea653c004e26c009512a6800984b8013017002543e96002500092488011c8d00229120043210008243800ec870021400803f1f0f4781020c002440800d47f00160fa00111f400543d8009479001d0e470371b0307700078ea00351cc005838800a86f00128da00341ac006035800cc6431050d200,0x17dbf800fc0a801f413003e1ee007c3c400f579bd800f408801e40d003bddaf0003b812007601400ea74801d4e30039dcae8003981e007202c00e16fb8800e003801bc0300371b6006c35c00d469801a0cf0033400cb63b3000ca6480194210030446c80031832006230c00c0002fc00bd5caf800bc5d80166255d00170b7002e16a00588756c005786d6800590015c00,0x400f9003ac00dd0036400d50034400c50024c008f0022c010100369acd26730960a0482311000838020b03830020821004083200803fc00fd],
[0x1c84614c9c0012ae9164f2680036b4451248c0012aa112421f0004a9a440fc7c000fa590e,0x1450007d1e6d361ac2a140b858e2860012d1c653218c04010200cd285000ad1a5a2b80046,0x136192306a8b2a154a25c2da28601a0c23872721d218ac3700328fc1b481050e4421a2000,0x16a499a0ce66040181409038151a6a428006a920200740006ee486001552270379b836190e87062,0x18e05a34723809188c2602f9607a3c1d8e8268441a0902803f9f8fa7a2f15898451b84400,0x1542510d1689440d41a36481e0ba792c9dc5e341683124331607c3c3115a445c0f478c054,0x1743989c46291424c4c220f8784a2148890408e3b1f000943d9408e0e0814890402a92c88,0x2ea],
[0x198730a5f4b99712de5acb39652c633c668cb18e30c608bee95d237c6f6d4da932a652c598a31161cc05802f75dabad752e55c6b896cad759cb11612c1578ae9582ae536a654c293524a1d432854ba9711a2332a6548a895029e538a694c296528a494828e5189e93c2764e89c93826e4d89a9342664c89893025e4b89692c2562bc570a714c294520a31442384688c1162284488810e1502904e094124240440840ac1181802c0480800900e01001000,0x19b335e68cc4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB09 : ¬ FormulaSat cB09.originalFormula :=
  cB09.unsat (by decide +kernel)

def cB10 : Certificate := ((9,8,11,144),
[0x100198d2002f1a4006431180306700158ca002918c004830800b85a2c058be002b17400522d800905900150ae00291540050298009853001382451001209e00250309a002412c0046248008849000208e00021140042200007c4300104003c1d0e06c340d0fc00241e800443b000807200190dc001e1a8006033000b066001704062000a0bc002a050b4000e158005025,0x1002d1660058ab56400582bc00b00880152155700158ab002b016005483d54005329400a651801409f002813a004d80132954d0013097002445296002512600458852400480011c8d002280086448010e0042208008042800e8850020c007e3e1e8f0761320400283f800d07d00158f600291e400483b800e470371b0d41c3a8004873001a0e2002b1bc005236800906b,0x184034010581c18010404802040500401fe007ebedfc007e01c00fa01801f0f7003e1ea00793c400f277801d8eb003b1d2007339400e671801c0df00381ba006d801b2d56d001b0d70034452d600351a6006788da4006800194cd003219a000332c0002648018e0062b058c006230c00b914b0800c05f80180bd0030176006006c00b912af800b711af000a90fae800b8,0x2005a8021e007c801e60076801ce00708014e00508011e008b80202007b3c1d4e46f3396ca44f23000f4773a1c4dc662a1449c440023a008dc6638008d09c01180e8022d150045a0e0089c4628008906401100b8021d0d0042e130c004282600],
[0x1a84a980ba0014b5928552680052c2499409a0012af9243d1d0005296488ec700010a4920,0x197381bcdc5a2c970b671420019a96411b0d4683319086411ba35188b4522510871b00198,0x132002dc38284c9dcec750b85432180b0512e7847000a6983a1cce4110804c247c4280092,0x10e021ac004083347b3d1e4461f12890522b1500050220f06c4e210e8693026100712e333e8d50a,0x10223918969b030152a962623c00334e00c9004251252a96000c5609b03813648a8572b24d32,0x12e0d8b434981625d2a961a0386a0f409608032068016e9e020184000ea020770003cbea1400694e8048a,0x1c04f93ca60a0602c0e094913920542914478571f9587c93488c0627f401f9342f4e82138,0x15141a785e2900822ca0362d1380010e4c971a0cc1c6d359a4ce65221087235078103b70c81318040ce68,
0x1803f1fc5631150c0000002e848184d50232000a1400c05024bc902f8f0c43f308f92891058081320213f,0x839393e520006e6812a962c00142],
[0x1915226443a5748e51be37b6d6d4da9342654ca58cb01600bc176aeb5d4b9571ad95aeb1d632c5588b0960abc576ae95bab055ca9151aa2542a814fa9e50ca153aa5d4b893124a4748c9051f2354688cd1522344254ca91512a053ca714d29852ca514929051ca313d2784ec9d1392704dc9b1352684cc991312604bc9712d2584ac578ae14e298528a41462884708d11822c4505409c1282484808c1102102b0460680c0160280480800901001001800,0x33666bcd198930e614be9732e25bcb59672ca58c9b])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB10 : ¬ FormulaSat cB10.originalFormula :=
  cB10.unsat (by decide +kernel)

def cB11 : Certificate := ((9,9,11,179),
[0x136800d06632078d6002d1a4004c33800906500180bc5c0e18c005a30800985f00120ba002c16c00522d800ac540d164004c2b8009055001409c18298009851001209e00251340048258008c49000208e002210800402280086001f0f074381b0808200150fc00281e8004c3b0009072001a0dc00321a8006035000386600020c4002e1580024090b8002c1405000280b,0x11080174005c2dc00b85a80164b1002b95a00572ac00a8538014aa353001480d002880600508013e9b500013c9d0025c5e9c0026932004789530004b001289300251220047001148d0022c0088430010889001e112004380104803f1f0f42c428005c83001b102002d1fc004c3e800907b001d8e872381b84479000a8ee00361d4005a39800987100120de00351b40062,0x18a44c011087802210d0042a120083414010681801fd01003f2020009031fe0004009fa007d3e400fa7b801e8f3003c400ef75bc000ee76801ca2f76001d4e9003a9ce00718a5d0007089dcc0072001b8df00369be000837400066d801b2006bb4db0006b35400cd17b5000d268801a4cf0032c52d0003244ece0033000c662801860060af58400602fc00bb17af800bc,0x1582991800b0802bf5db0002bc2d005704600ad564015aa9802af55ac002ac1f005503a00a8d3ea400a806c014e0c802994b005268f4a005202600a30240144a1802833fa10028011004f80e009e4ec01399bce80138078026c05004d4013397cd0013298802562f980025d2d004ac572c004a801289380251250048a42008fc7640008f054011c0480235190046a2e00,0x10048c01150042c00f50031c00b3002a4014d00514013d004a4011b004440107003ec00b9002bc00950056c01268c43a08f8713296cac49002491686409ece0642d15490004822508803c9bcc4],
[0x196170328c00005e7616e2c0a60005e6a16c270980005e5f16a1f8780005e4e1681e8720004a4c166,0x15d93a3d8ea390d22909223070591625815e5715a5606e002006f174408fc0005e981723f8fc00056,0x15d1763d88c59158000245e90e4310a028080380c441520006a5e116451122e8b82f8bc46154001be,0x10c82c0a0300a826090224691e4717a4812e55940000b65f002000f23d0f0010d82188a220da378dc,0x4b60005e149804b12a4a0481004c128460f97c1103c0a0420e814066980000ccda5f926491220d02e0e036,0x107000179824f8c42a8c82b8ce2d0cc2c96e5b0fa3b8e8388d6258901d9505394c5294851944508d0,0x904831985913c402080b2dcb62d4b42e4c0020bc03c7c1d8731c06a128470e81002811d08340b628884,0x8b8280502d09c080f71a8684806c55938198006113c308a80501a0481859970318ac2687c400ce2d0a0,
0x5364c934160641586201982180545f85e1497c],
[0x167acf193325638c5189b1061cc358430660abf17d2f15d0b9d732e55c6b896eadb5b4b4567ac657caf55d2b856eac9532a5548a6d49a924f49e5382684ce99932a644c49852e2584a093d2724547c8f11d1622c2580af95e2ba570ad95a2b2560ab9562aa530a594a292520a394628a510a19422825009f93e27a4f09d93a2702d85a8ae15a2b0558aa1522384688c0ae1442684c0961282384505c0980c8120160280480800e0180280400600800800,0xd14a254327fcfe9fb3e67acf49e33b6764eb9d530a60cc097f25e4b49592904a0840f815025ff3d27a2f21e03bf77cef5d3ba673ae55ca37c6f6dc9b53696a2d41a3b3e])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatB11 : ¬ FormulaSat cB11.originalFormula :=
  cB11.unsat (by decide +kernel)

def cC00 : Certificate := ((10,10,11,464),
[0x10004e26c00130990007825c001a8950006624c002389100084244002308a220860d08f0003e234001e08b0006a2240019887000822007e1f028214001ec33208000c88300078204001a87f000661f4001e8001d879000701e4001d072070770006a1d400198730006e1b00e1c4001a86f000661b4001a06b000661a400190670006219c00020650000218c001704d184001805e138001784f0003e0cc000981b,0x10d8d90003e35c00310d5000b634c002c8d1000cc328c83182a33c000c8cd000c432c002d8c9000b231c00308c5000bc31400300be080c3000b6304002c8bf000ba2e0122f4002d8bb000b22e4002d0b7000b22d4002c0b3000ae2cc00028b1000042bc002b0aa000a82b400270ad000ab000a6290a22809e140a90009029c00178a70007b174a40005c294001e0a30006a284001989f0009a26096250921009d,0x14640040917000fe454001211300046444004310f0010a42106410360d10d0010242c003f9090003c41c000e9050010040c003f901000fc3fc003e8f80480e3f400068fb000183e4003d8f4000f23dc00398f7000f5000f03b8ec3a8e8148f3000da3c400170ef000c43b400168ed000b63ac002c8e9000e4388e0378dc108e70004e39400130e3000c4384002d8df000b237400360db000ce36c00358d4348d0,0x1509550013e54c000f1510013053c0052948519440b14d0014252c000c94b0013e524000c1490002e51c004c1450014050c004f9410013c4fc004d93f0013a4e0224f4000993b001304e4004d132051370001a4d4004c1330012e4c4004b1310000c4bc000192d0012a4a0004992b0011a4ac004a400491224811e47052141270010e4940017123000fe484001611f00056474004611645112440421011b0004e,0x1644006398d001810fd8c00188619846098b0018a614000c9890017c61c005ec2f610000b9850017860c00600005f97d0017a001765e4005dc005d172001705d40059175001730016e5b16a5a16615171001585bc001716d0013e5ac001696b000585a4004c167001625815e5715a111650015858c00139630014258400131610013e57c001295f00048574004c15b00156564005315900154549505383855c00,0x172400721c7001c87040072051001b717dc6001b671c006b9c5001aa70c0068c5970000161c10019e6fc006f1bb001bc6e4006f041001b713dba001a3125b8001b56c5b6001b46cc006d035001a30f5b2001b00a4006b1af001ac6ac006a5a56a8006a1a7001a80740068c27698006900f001a2001a067c006740066d9767000669990019117d980019665400659930019113d9400181135920018f62d900018a,0x181a05001ff09e0400202804007f419800007f8007ec007e5f17e8007e1f7001f87d4007e1f3001e917df6001dd175f4001d1165f2001f07bc007c1ed001f07ac007a44f7b8007744d7b000744497a80079de37a000799e5001dd0fde4001e278400789df001dd0cde0001d10bdde001dc001da7640075dd376000759d5001d607c00744277500074811001d0001ce7340072c00725bd72800719c4709c06f850,0x18fc009023d0024010c008ec4f8f8008ac498f0008e6378e8008e037002360ac008d233002318b632002308bc008ac278b8008b0130022a002268a400892290000a89c0001225002230022186e220022087c008821d002201440084c5f878007f4578700086a190021a85c0086a150021a1040084c4f860007fc49858007f447850008460d848008420f002100d4007f43b83800830290020a8240081e0382000,
0x1a0c00a027f0027d0027b9de7c0027a9e4009e8550027a144009cc5f9e0009da7500276114009d8410027313e74002719be72002700e4009c0350026e0b4009b8290026c9ac009a267002650026397e640026298400988550025917e600025e9740097a5b0025913e5c002511365a0025794e5800256954009443f950009482d002500024e9340092a490024700245906460024490c00910530023b17e4200240,0x113ec0002bcaec00ae6b7ae800ae025002b808400ad813002b4acc00ac400abea7ac000abaad002aeaac00abaa90029f17eac00293176aa0029116ea8002a6a9400a9aa3002a6a8400a7c4fa9000a4c4da8800a444ba8000a7699a7800a729b002930fe9a00298a5c00a6295002930ce96002910c694002920028ea4400a22910028ca282407a8f00282a34009fa8b00286a10160428900282a1c009fa8500280,0x1bcc00bdaf1002f615400b9c5fbd000b6c5dbc800b645bbc000bbaed002eebac00bbae9002ee11400b9c4fbb000b6c4dba800b644bba000b96e1b9800b92e3002db0fee2002e0b7c00b82dd002e00b400b6c33b7800b6431b7000b6800b5ed1b6000b5ad9002d4b482408ad7002d609400b5823002ceb5400b2ad3002d005c00b4015002ccb3c00b32cb002c9002c7b0ec8002c6b1400afc5fb1000b0ac1002bf,0x173c0068400c7c00c5c00c3c00b9abea7a729623a849e86d990002d8aea909aa4c8ca08761aa5f000b2ab29fa66922287f1cc6797800326c9400c8f21c9000c88230032005400c7b1d0031bc671c0031a03400c600700316c5400c4f11c5000c480b0031001400c3b0d0030bc270c0030a02400c200300306c1400c0effc1000c0b01002fb09f00002febf400bec1bbf000be800be400bdeefbe000bdaf5002f6,0x400af4009b40093c008d40082c0076c006b4005fc00c9c00c1c00b3400ad400a04009a40092c00],
[0x1630ea0b51642bc568ab3902a80018830862ce98b1158000179843a40ac098000ba290e8818026000198823a0,0x10002c9c03b2340618000926e0ec0cc1860001e9b23ae3146180004e698eb0ba15c000269923aa2d85700007e,0x13c8718000927a8ef0ef1d40001f9e43ba3b075000066780ee0eb1c6000179de3b63947180004e750ed0d7186,0x18b8f210d20000024a163c640c8000004e810f10f91d40002e9f43c23e0718000b27c8f00f31d4000269ec3be,0x10001fa9a3d2578ae000066a58f413826600026a5a3ce4d49980007e950f312723c00024a3c3ca4808f00004e,0x164cc480009aba8f718f3120001fae23da62cc4800066b78f616b2b80002eaaa3d6594ae00009aa88f51612b8,0x1308559c538870ce11c13806fc550004507f0f91a534400013b003e268cd1000036bf0f819a3120002eaf23de,0x101cd61bc00019cfa0c60203206200d01e0300700b02404405009192724000790cc7ccdc97e2e4548a09311c4,
0x17cc138210127d018830064384178000b8178fb11b35c6bcd691a23a470d81bd0008a4fa9ab3546a403005010,0x151ca201b038028f981a0127d0002724b023c169f700800c120261a43806e02e0580941500205008814823014,0x4160082041a028024fa0a814e0c4180a9064684a8940182298178003f04f89804e3787e09b1373cc4d00e81e28a,0x17b8fb0a30542804b8243c2780439d804c3f07d8a213222c4309f12c220698d21380941402203605414823038,0x17484488e3ee0800f82d2980b8a794d2a05284f09b11a2505213c17c2949f0bf3384fc601a02742f0cb9e73aa,0x10106d81837c041c2708041c6a313e2609b8fd0ee3b83c4781dd002000f40333f2514a39430320780b81d0027505b8b9168,0x49d128238a20973b0528699501c05346e02e05a07c0c88c02e7e47d004186f09e0000344fd1f83ec000cd50c14015052,0x57d2a250098119008296723f06409f1302987f0b49662e05bcb617100017c27a9f3f665cd01ee3382685289e148,
0x49d3287ec12826134090f719832e528a49a02a0670a70fa14a7d85180014a520fd0085bc9f12c250110004121080415a0218f,0x1020a98188dc3f4e47f4be1792f65e0bd1bb2584b89792a22845c8c1113ca78c9c93b27e4f46d8de1c034cec09713c,0x48e3f82e0e994628e7e8580893b63b4788f01667740a161248c800044af680416a4880044a478880500880022f0211880854c31060,0x5fe29c29452095126240eb8ce19e32c0c81f05a36c171501bc370a48e004c7e0128243280006eb4067ccd991318,0x4c03402f0cb9d53dc0901302529052ca495029e530fe88b1187e47d0082de5b99000885c88144750f68142da040c9304080c9,0x12902f84e27c800d99b23621ec3d07d0f86d0df0002627fc449d211c2d0c6094172644520be3362945f99f338,0x1724e40005b8a5018a0119e3346581e0320800210b3786e0e03f0074ff0002867e9ff050001cb810e641a0280020c864384000a9,0x56d33a5c0d016832e7a8f7034062d09710001342da022ba6e8c51772844c8919061d2324569cf39c734e61cb394,
0x5cc396724e30005b04f47e8174080786682019e0205885006c1481c00831c04192178003622904605f39080cb51ba332,0x147cf20600bc17c809f0204310d210519069c820c734c788eb1f110420cc2188302204ff9f23ea48c830c9350,0x11341b0b240c620c01851001fc001da2b256c738e63741f8ff9582ae0506baa65480a0d370c002d826e75902922242,0x43306c0d4006172cd0384c0941602c85508c15cf08fc0a83f81c0f60a60dcefa020b81747f85a0003586a0d20a4,0x4530820dd0380c0e62f84d488824ba03e2ec5cc1d84007e0f41d0380780e41ba072ee73c000c54106bcd71ad068,0x13f56c20a40c4949312408a12c2c0440b27e42b8fa3c23f47e0fe1ec4b0ef92e25a1582404341015023842070,0x4810fc000e2b06608bb9061926e0bf97e39e72ce49c738a0002283482c721561d056902a0410a210dd1552a81108fa7e,0x16a0e30000368302f1010c0408621051905cc820c72ec788eb175104618419b636e6d4401870fe17d05085108,
0x40471e450b94022dcaf98d318750b19912c4640f49ed1107fc002e653c960c814d2940fd069a734c690f89f0000,0x12a03b831060328648c21521e4191c937e684b8940232384608a60ec0bc001c02303f8520820be108201c941c,0x137c8590700135c2e22a002cca204303506f0d6760368d30d828ce888c3a0280318d43b21887009f0003d434e866c8d81aa,0x60d128290cd8a52d84f05f19f3385bc9f0bf3405c09f8c032e5a09d0bc1427b8f51e73aa808004713446d109040,0x13585019b2d84f07d1e13c00204e80155c0412e7f00412a7b008126ef80412237010a030609f3fe102efae2003429fe01286ce617d0781e03a,0x4a90392bcff14c0002f21003e064168cb05c80c6e20e2524bd0484903a8343089441629046017400294fc8a3054,0x45d4226e8b21921302784b89a3bc7b87a96732e658ca8fe2e06807e16e33c784f59ef3ec270010963fe29c0a2b9,0x45c0b60c4180790ba0c8008291d82d02f0003f827032098848060657787a8fe1f859cb816e1347b80005d6800206516035ac4,
0x4660c414422050029d25d905c3786e8dc1c00a86921104c270128170488402b04f00104c4e00104c4d001045f23ea0a0d08f0,0x1498341240d21143a04b0c81d42c1080e0164851130ce4b4859160c60041fa52148328cd20e1c439857000a5d0f0e4,0x4a30548440b89c42027cff8a8152684b880056e003970007f03209c851018cb008bfcdc420054d081986ca4118208e421324a,0x1001989ac290528a03c066ccf99c34065cb616f2e05a09e13e27e4e85f0bf1802f0508fb010ca4fe1ec77d0908c0dc,0x13f47d2101fe000279e942e024a4c205f40004f57e858cc19400226e1034200027ae742a4a50712f41234870213092,0x14b10813000013d1da1a27e4ec9f139278840a000009e9650c8d41a23806f0db4203840004f36e8607b8f41fc,0x12f85d9bb3f68550b2174308650d21b41e8406080009e8708c11222e4388a21023200027a134364bc9592e250,0x17787b0f51fc800510991222190586102e8500016f27012a1c41e8410609f12c23c103fb086079fe014eb864874600bf17a,
0x1254a38cf14850c658a50322800f8db3b20b46f0dd05c380a68d22a00984919c294090439a032a2784d0973be,0x56f33e3d87a96c3363f8b19911fa588c816031c3e8f49ed3d07b0fc80143a2710e2100b0dee1e12024ceb94619c,0x1021cdace658ca89a12e5c0d01df3bc],
[0x11ec3c8788f01d43a4740e71cc394720e31c4384700df1bc3746b0d51a834c690d11a033c670cd198324640c718c314620c3184304600bf17c2404788e11a2304588a1122204388610a2104187c0f61e83c8780ee1d83a8740e61c83886f0dc1b43606b0d41a4340670cc1943205b0b41642c0570ac150298510a013c2704d098128248470680c81882f05c0b01582a052098128230380680c81802e0580a8140260480881001e0240400600800c00800,0x15bcb716cad75acb5569ad15a0b3d66ac5588b0d5fabe578ae95cab856ead95a2b1560abd562aa552aa153aa654aa9151aa0530a5d4a29251aa3145a8a512a1d422835049fd3ea7c4ee9d93aa6b4d49a532a644c698930a604be9792ba554a65c4b816f2dc5b4b616b2d45a4b41672cc594b215d2b856cad1592b055cab1552a854ca91512a053ca714d29852ca514728c5148b91622a450899122224408790e21a4308590a206408809001fe3f87c0f7,0x183906e0cc148250460840f81902e05409800ffdff3fa7f2fe1fabf37e4fc5f83ef7d8fadf53e77caf91efbde7a6f1de33c5784ef9debba770edddb3b5764ec5d83af74ce95d23a073ee79cdb99730e5dcb395728e4dc9391720e35c5b8a70ae11bcb786e6db5b63646c6d81af35d6b0d5dab34c696d29a3341680cfd9bb36666cc59832b654c9d8fb1e632c4d89311620c3985b09610c1d83304606bfd7f2fd5f4be5792f15dabb1732e55c8b8d70adf,0x1a5f4ba96d2aa4d496925239f33e27bcf693f27a4ec9c8430820fc1e])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC00 : ¬ FormulaSat cC00.originalFormula :=
  cC00.unsat (by decide +kernel)

def cC01 : Certificate := ((10,10,11,503),
[0x11e8a10009c27c002509f0009a260961009d0008c26c001389b0007e264001e897000922408e0c8950008c24c000f8930007e244001e88f0008a234002108d000882182622c001f8890007a21c0020880060850007e20c001e8810007c1fc001e87d000791dc7a000781ec001d87b0000c1e4001e00d000021dc001d8030007418c001303d144001404e0f8001383f00030094000480905c0005814028000500b,0x13505637c00188dd0006036c00348d90005e36400310d7000c035400340d3000ca34c00338cc0a8d1000c433c00300cd000c83181c32c00310c9000c031c00308c5000c030c002f8c1000bc30400040bf000062f4002e8b8000b62ec002a8bb000b9000b42c8b02b8ac190b7000742d400278b30008c2c4001c8b10007e2bc001e8ad000a8298a4288a0148ab000622a400278a70008c29400178a50007e28c00,0x11a06648c00459210011247c001c91d0007046c001b9190011445c00449150011044c004390c42844109110010843c001310d0004a42c0041909001044081c06907000244140008903001003f8003f101000ff000fa3e0f63d0f21a0643f4003c0fb000ec3e4001c8f7000703d4001b8f3000ee3c4003b0ef000ea3b4003a0e6390340c8eb0003e3a4000f0e70003a39400388e0000de38c0038400370da360d6,0x14b15f0015a56156551521615d0006256c00181590013a55c00179570005c554004b1530014e544005314f0014a534005094d00148519441194b0004e52400131470012c514005013e4f03650c000f9410003c4fc004b13d001384ec004c93b001364d02c4e4000c1370012c4d4004c12e07933000244c4004b12f0012b4a52c001284b4004a813000084a4004a00900126490004892700125001204791c46918,0x168c006799c66838684000f99f0003c674006419b001966640065192081970002465400641930018e644000298f0018c628006218d0018b00186611826017e16054624001898700060614005f1830005c604005c17f0017a5f4005e1760b0285ec005d179001705dc005c975001705cc005b971000080116f0016c5a8005a16d0015c5b4005ac0059964589605786a5a400541670014c594001c9630007058400,0x1779dc0e03278c00769e10003e78400749df001ce77400761db001d67502e099d9001d275c00739d5001d074c00739d1001cc73c000280273400729c8001c672c006e9cb001c9001c4709c06f9bc1b1c7001ae714006a9c300072704001c1bf001906f4006e1b66d1b26c05a6ec00189b9000606dc00661b50005c6cc00641b1001ac6bc006a9ad001a86ac00681ab001a6691a2121a90004e69c00131a500190,0x18a227002250022387e24002228840085c758800087a1d0021e86c0087a190021718e1c0021117e1a0020717618002160021484c0083e0b8400083a0d002070c60c0020a8240081c25820008180080a0500203002007f8007f201001ff001fa7e1f67d1f21b0647f4007c1fb001ec7e4001c9f7000707d4001b9f3001ee7c4007b1ef001ea7b400789ed001e8799e4120407ac00769e9001d279c00739e5001e0,0x1014009640095e4b96000952529424e9306495c0095a510025693c0095865002469540090a53002371ce5000072944008ac71938001c24f002269340092a490024a14c008dc5f92000912470024490c009063b908009023f002408f400900410023713e3e0022b1363c0023a8e4008e833002370fe38002358c636002308dc008d2330023409c008ac318c8008ba2c0623100230064000922f002268b4008a800,
0x1a5000a4a9100292a3c00a4a8d0029210c00a0c4fa40009e44da38009dc4ba3000a2a890028aa1c00a2a850028a0cc00a0c3fa20009e43da18009dc3ba1000a067da0800a027f0028009c009e4319f8009f27b0027c06c009f0190027708e7a00278002749dc000380c9d4009cc009c66d9c8009c26f002691d66e0026c9ac009b0550026317e6a0026800266994009825f0025d96e5e0025c03c000125b0025a,0x1002c815c00ad45fb1800b12c3002c1aeec2002c0afc00b02bd002c011400ad44faf800ab44daf000aeab9002baadc00ae835002b50feb8002ad0f6b6002b3abeb4002b2ac400ac82b002ad0c6b0002ae07400ab000aa2ab002a6aac00042a900006a9c00a9400a8e9ba9000a8aa1002a2a7c00a8a9d002a219c00a8865002831cea0002791c69e002771be9c0029aa6400a68530028317e9800296a5400a4e8b,0x1c1c00c1701c1800c1303003041ac00bc473c0800c02ff0030014c00bc45fbf800bf2fb002f9bd6fa002f8bdc00be047002f810400bc44fbd800bd2f3002f40dc00bd033002f10fef2002efbb6f0002ee09c00bb01f002eaba400b9c00b96e1b9800b92e3002dd1d6e2002e0b7c00b8059002d717ede002dc002dab6400b52d3002d1002cfb26d0002ceb3400b3acb002ce1a400ad473b3000ab471b2800b22c7,0x10034804c00d18090034500343cff4400342d0400d086d003421a400cbc73d0000cfb3d0033e15c00cbc5fcf000ceb3900337ccf3800336cd400cbc4fcd000ccb31003320e400cbc3fcc000cb72bcb800cb02b0032a07400ca3270032500323c7f2400322c8400c6475c8000c7b1d0031ec6c00c5c61c7000c545fc6800c6000c4f11c5000c48290031008400c3b0d0030bc270c0030a05400c200b0030801400,0x1dac00d5338c5afab62c2a526490a1200352cbb14bc2d6ad28298a3684000d2b26c32e8b4aaa9da5e89a040037ade400ddf75de000dd849003740e400dcb710036fdb7700036e04400db0070036ada400d9f65da000d980d0036400c00d8c00d875dd8800d835f003571d75e0035cd6c00d73590035c16c00d5461d6800d4c5fd6000d5800d474fd4800d402f003500b400d381f0034cd2c00d2747d2800d2015,0x400cec00bf400b6c00b1400a5c0099c009140085400dec00d3400ca400c3c00bac00b5400984008a400dcc00],
[0x18c8fe0fe1ee0003aa203f63e87b8000c6870fd0f81e00002ea183f23cc78000062830fc0f11e000012a083ee,0x10001ea864024f49c0000629f90013225c0003aa6e3fe474818000e2938ff11020600026a3c3fa42081800062,0x15b4b100009aaf1031682c40001eab640a590b1000062ac10215527000038a9e4065249c00009aa3901142270,0x17a4f41e71dc00155276416748e60000ead79051ab34c0003ab20412610c00000eab89041772c400038aca40e,0x18308b1f000027c4620d3b075ceb00b012034061d93ca0003da0c3c471cd79a23105f8961021de7b4f61eb3d4,0x10600ba0d21c0680a8120200640a01101e8300009f474838108222244548701d0380901181f0340400f01901e,0x5603ba798002ab420080888222284480a03b4550702403e0001b83c0500880c0bf0781b21a0741190f21842483016026,0x184c00021008e30753861dc3a21100006d2942471001001000714e31c30e81d8e39ed0004b50895f3b6770ed15e2c2,
0x1700de9c13786e8f1a132ac47ce10006a4c51782d6540989282100be1cd0a17b2f05f0bb1742fa0003985f56a,0x1000570af3447ac0019142c18c331482de530a597229e5aca320540282d081732a07ccf90002224388603d42a,0x1858670cf198000e01be0d86a90c05b0ae168ff0552461642a1220ba1782e0004ac3d8790681d885ccf9a1340,0x1988839040628683706f0d21a8ac06d0d0550aca0b4201c439070000a888e11a0d04490c8ca1962fc648be18c,0x13d8fb1f53e87ccf91f13e07bcea9ae0001d430a1b0be4e43093c27658cb39402cc4fd02200416840002b4504,0x43043a1810d1f71e43d47a1f80081b61020e0c50e1e4350738d51d135a750d61d3412828dc9952fe5cca812d22c,0x12484888d3f47e4c10fd1f6740c31003a86147f8903a6820fda1b4142303d8784222684e1d530e4044c8000ea,0x59d2ba264001620a65310f86442a808a694f28c804a800433a1ea1e0fa1fc3e1c93967203d0790061f8e688f11c,
0x54327c13d78a213b876ced03806e0e81c80050260a201282610199a2b425cce15c11665ca909611424d0889b138,0x5b9204270fb1e73aa6b8c393520226400109684ce14327c1d427a221046304198f31c650c9990100844ca9f5000,0x13eca01d035a6189a10027e3d0ea1ac30a4cc7f8904007e0e9a094107fcfda1b43a829108b442c23108904134,0x150c888eb0eaa09119b336a2d85b9b43706dcdb1e321641c828002fec092f1f2734d380c24a9d1a9306608988fd1f8,0x12042821e0ca1890e12f1f20304881025c0013a020a502056918210402114168404d1952e65408b09c3ea7ccf91f00182ada1296,0x150c2703c0ea890278522825a8a290e2e453c8a97029a44d032023fa21443992328638418820a22180222216a,0x43d0768805c0002e6000c14849011b134134b995022e458f0902138138000b57b8f39c230e5f4ae901132130002b4506,0x44b11c120490431221284683f3f47e4b1800526b39862005985b051000a3c494082e802208000354b50a01181f03c08a,
0x177cf01de0a62dd0b8bd1784950c11e1901602b11c18e558aa2072b6564ab9bf2f45e4ae1c12f854cdd9752a2,0x10b007a0c06a0d8ae80004a3a2262a254c1382b2a40a50782602009407a0c0680d8198005062a14d22506040cb9176,0x42e04c7391414f29a5190120100c89113005008540f90082b31382e2ac0c8ad9572b88941503100e0c10782d020,0x14d8d092a33c4ac94937416841061a22587acf400039a96d148e01be3746b8d61aa34c6a0d20007acf3048080,0x5a90006a40864606327011958010c4791802c10b08c0f0844668ac13433c5689c010caccc1560020d8485c1150081a00380000a340,0x17b1159a5346690590a3166290610a7144314550a0392310548c114c4c0e78c31502c4528a113e0021e8fc69c0a43f,0x11e00234f134ca9503c2270271f53e47b8ea9c230e0314ea86a0d160e91d4390740e31d83b4758003ec7d0f906c0c8,0x4f52b6568ac9570fc3e4e695c11e2391289212212815008a427e004a3e7a1d4008a35f83a6820024138980828f1cd0908c100,
0x151ca314429e538a52271bc364698d81a4345149ca25072c4e9893902783d22a0f27dc738e61ca3c8ab2032a8,0x18b4f01df3bc8a06e0e21c28acdf9c137612c2404307e58cb3966408644c5194316639108831b420840943402,0x5723f47e4b880820eb700420a43000206fc1d310e02081b242d10b00021a42000c22b99e11387ccf7008c135a9eb34252ca30755f0,0x10c0d48206ac0015a0c6c1bc83a9e145c8a0003972dcc518b3203785b0b5326644698281ee0050d1f87c8003eab4a051245b0b589111a,0x4044b708800b62f0800b66f700829af69ab29650c3a84c45e7286b1cb1ae628c598c1aa350e40db1b401047a50274c481812a0428b,0x15a4b61722e25b85d0049866e00045e040a78b84f18f454638c699445a2f4710e11720004c9f20704f80028404146020a52f0428b842c,0x4fd2804009f8ff4007ed0ea0b420002698240401281100133c00cca1b000b62808330007b4d59620099b63040a5ac40883104,0x11344e04e30e011d38eab21189692d81442905009e804a096a28c0829ec5e88c5e08911087c1582802e0a8099fa274,
0x59d011acc00b1e3a94c46459cba1652c65d82103f08810c2404b2ea23800379020988004cc0470600135118208007162000071246211134,0x15584b08a3121e80225f56c3f0f9019004148070380036ebd00436abe0043671889300096c001ee0a81004a05007a0c1362681a09c06c,0x5720a0514b820128c53ca6a06404045769d63a01904d4666684c19c33025ccb08b12862cc50160300a015a1f12a,0x4c73043f4020fb5e8bca2c0085e57c112220288001e718a320305b418f1a8b916001e4df0031e65ed0ea0f8192834681482796a282,0x6b528600064bda8d4d91b1360020d7b7412cde1bb3826fd0c22f46614d0b92523c4702b154190160ac9574265700c4ff,0x104c9d1404683204a86c0b084c470141a63580c1a29f97a2f201068c00030e48403542055e4d04d0682702703600833d2700033433000,0x10615dc420235eaf8204180eb0135f820a84401d2f61431d63a03a83c06413d1b0301c71805342e15833954432564ae1262a4464002fb,0x18c8151fa1fa032318206dc0526e004735883a94c46e0b077c56394aa1592440307b830058c518b010af4e71ea1f9098f911e050769cc,
0x17e0410811128dc4a8584263e4470007a60c58d01105af8144041218d400b3f0b0968686544e0363ea030978004c5460088643c47087c06169,0x57a1ce84d1c2350107dc0ca7a002eb0317790a1b176aa000100be40c1748988e4aa0562b285c1813314d1b2211ea21802b3f1f87a08311e,0x1230029c7270021230176187c0641923b44a5009d01302e0a0159520a07ec755348e8201fd0717aa94538a794600a39903a0100c,0x114d1ba1712a1608f92424c4688c10c2145e5001fc2f88751880cec62b0001e2aa186200564000ef5709d1060003c63a0a2,0x1500fe93e27444c0b01322a0600b90e10884401161018b1b2a5408b1f53e47c00014b11a0cd1e2394585009fa33110,0x400566040cb067d5a186188010920c0006d82c04c000dd0600b88c01014c043d2a809c3e461c040d32351e99210e6504308531a000a4a88,0x4003031e88c4220467d809cd5d535c674c395d26a0004c8006cc7347e0200b80b1c68307e8f8a794e28e528a19400088ec9f13a478,0x1734d3981003b059912474002f5966c469d40030e59c3f274c00c3765c488fc1f656c4820a0030bd2424c464158043967f95c050,
0x101158c8404159b741202384b0921290d9bc3760104abf60618989a138808010a39f24122a43889a333fa458f8000e3a26a40428,0x4e618e1ac728561fa80caa08911040000bff8dcdf9be1fe57073804c42e09fb4740a11ea3f48282d08019bd6e115d24e,0x656488460093d50a08d02b2320a803a4200935c120013541101b9ac5f49490d2022f0a28b11f2300ce14d0c21945685c0411b,0x42705690c8c9264880003b8303fd27066001228100828f82f05c0c89212206290800e8b0001f85805008801d060003f],
[0x12164288490820e418828f81ee3d8788f01de3b8708e01b23606b8d61aa350610c11802fc5f0bd1782ec5d0b91702dc4588a1122204388610a210418821022003f87e0ea1d0398720e21c03786e0da1b03586a0d21a0338660ca190318620c215c2a8540a61482885009e1382684c0961282404708c114220330640c41802f05c0b41602b0540a41402704c0941181c0340640c01702c0540a0130240440800f0160280480800e0180280400600800800,0x14708dd1b2354688cd1922544888d1122144087d0f21d43886d0d21943085d09a1242283cf19e23c2780ef9de3ba770ed9da3b2760eb9d639e738e69cc396728e49c838e718e29c43806fcdf1bb372634c618530860cc11813005b8b696c2d659cb31652c6588b09602be578ae95c2b6568ac9582ae558aa94e29a530a594a292520a394628a510a19422825009f93e27a4e89c93826e4d89a9342664c8989302464889092023e4788e91822844c8910c,0x16b6d45a834f69cd2da534768cd0d9fb3e676ce59c333660c9d93325638c5189b1061cc2d8530860abed7d2f95f0bdd7aaf45e6bc5782ef5daba9742e75ccb9571ae05beb796eada5a0b3d672cd598b2d652c9590b1d632c5588b09602bf57aaf15d2b856eac957aa654aa914da93524a454828f51aa3145a8a512a2143a844f69e93ca784ee9d93a2734e09bd3726c4d69a934a684ce991312614b896d2ca584a093d2724548890d20a4047c8f11d239,0x695529a51492614c19812fe3646b8d51a5f3be57c8f7deebdc7a6f45e43c7788f01dfbbe77aef1dd3b7768ec5d3ba674ae91d0ba073ae71ccb95728e45c7b8e712e1dc337d6f6dc9b8b6e6d4da5b43676ccd91b0b5e])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC01 : ¬ FormulaSat cC01.originalFormula :=
  cC01.unsat (by decide +kernel)

def cC02 : Certificate := ((9,8,11,137),
[0x12e168b01e31800406100128be001c174002a2d8004c5900150a45027130245700070aa002514c003828800544f000989a002412c0040258008c442104092001c11c002a228004c43000f8783a0710400381f800543d0009876001b0e400301c8006832060dc002a1a8004c33000b8580a18800542f000985a00140ac0026148004827000884e0003094000211800401d,0x15a2cc00b4588015cad002b956005429c00a85280144a1002893e004e80136994e001341f0026026004b254009649801220047a2d200047234008710a30008a44800fe17440010c004220c008440800fc003e1e800783e800f6003b1d0e47037050f2000e1dc001a3a800307300058e200361bc006a36800d06d00020d600021a4006632000c46700158ce0032800c05e,0x181c06080081044010007801fafb7f001f80d003e816007c3dc00f579bd800f403801e403003c400ef75bc000ee76801ce2176001d4e90039c3ae80039800e50038dbee400389c2006c885c0006f37400de6d801bc150035c36dc0035432da0036000d268801a4cf0033400cb63b3000ca648018221640018cc50031986005f86d88005e86584006000174b9002e96e00,0x10034c00bb002d400af002a400a30025c00850041c010f003e400d6682f970b256299409441001a8ce5e2d960aa5227924800043a1a0085c261800850240108028020d0500419fe00],
[0x1ec47198ca000eba11a612d80042e046154a00010b21163c1c800428c450e86c000ba2112,0x10c048381a0b04018140702a3cec80000e5206e369b004010200cde7e0009d1e683280042,0x126141144a0010248ea743985824180b85422900a0400c13078151e77400009691391c4e0,0x1854220d04813216000194991084430f0903a230008838911086d20200d0183e1902a3c4e,0x14d259248e411c02008236943e144b8532f95cc6563122d18922c938984a2411880374421d0c,0x18d1d978ce3e319a87a6234a29188e490d0f6353f9acc83f198012a7d29174a860020105689e,0x17a3c9e05429160ac5a32182505e93170c512],
[0x18e91ce3846c8d71aa34c3d8770ea1ac34852f9df2be47bef75ee3d37a2f21d3ba673ae45c7b8e712e1dc337d6f6dc9a8b5068ec9992b1c5f6be978ad059eb1952aa4536a3d46a874f49e5382644c49852e2584a093d2724547c588b095a2b2560ab9562aa4e89c9381162284488810e21842884106208408800fe1f83a8740e61c8388700de1b83686c0d61a8348680ce198328640c61883085709c1342604b09411c2202b0460580780900c01000800,0x19db3b275cea8fd1f63e478])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC02 : ¬ FormulaSat cC02.originalFormula :=
  cC02.unsat (by decide +kernel)

def cC03 : Certificate := ((10,10,11,509),
[0x10d4000f8970008a254000f0950003a24c001e8910008d238002308f0008a234002308b0008822c002088b0008621020224000b0870007a214002007e0488300082204001f41f20000078810007a1fc001f0001e07b000761ec0002879000021dc001b05b1d4001d06e170730006e17473000721c45f0007017c001303f0002606433000320a01a0c4000c02a0702f0002a0742f0002e0b01e0002c07c0004009,0x131c00308c70000c31400010c3000c02f8002f0c1000b0304002fc002e8b82d8b42c8602f400290bb000702ec001b8b90008a2dc001b0b70006a2d4001e8b3000ae2b0aa2a0a6138b1000a517cae000a42bc00178af0008f174ac0008e2b400170ad0008a2ac00168ab000582a4001e8a7000a229400260a5000a02789c2684028c0023c4d28000238a10008a27c001289d0007a26c0025894248900d09900098,0x1000d6404003f0ff000f23fc003e8f83d8f4110fd0004c3ec003a0f9000da3dc00358f5000f03b8ec3a8363cc000f8f1000e83bc00368ed000d63ac0039ce13a000398e9000e03a400390e2098e7000e609c00368e5000d638c00378dc060e1000e006400368df0001e37c00358dd000d836c00358d9000d435c00348d70000e35400018d3000ce330143440034015000ca33c00318cd000c832c00318c9000c4,0x14d934148504fc001793d001264ec0048939000584dc0015935001304cc004b92c4a928110424c4004992f001224b4001292b000484a400491270012249400481230011e47018051210001e47c000711d0011a460004591b0010a46c0046400451124410e4306445c003fc71450003f91500070454001b913000e8444003690f000d64340042106411024005242c003f9090005e4240017107000e84140036903,0x15497d001785ec005b97b001765d1725c0465e40013177001645d40055973001525c4005b16a5a1660e16f0003e5b4005916b001565a40054967001625940057165001605782858c00559610015257c00569580695d0015656c00549590015455c00549550015054c00021510014e530005294f0013e53c00534005214651142500641894b00132524001b94700122514001b1450006a50c001a1410013c4e938,0x16f1b7001b517dba001a9175b8001a3165b6001b36bdb4001b26c4006a44d6c0006b9ad001ae6ac006a43f6b00068c3b6a8006a000699a5001a20019e6840067c0066d99670006619d0019a04400021990019802400659940019265c006199700195001906398c62988199930017a644001c1910006e63c005918d0015662c005498900184609805f97c151870017a61400179850005c60c0059181001565fc00,0x17f43f800007bc3b7f8007f0007e9f9001f77cdf8001f67d4007d823001ef0b5f4001f27c4007bc1f7c0007b8007b1eb001e9001e778de8001e67940079861001d31bde4001e27840077c5f78000771df001da761d675034774000f9db001ce76400731d7001c87540074800741cf001ca73400729c9001c7001c56f5c6001c470c00711c1001c46fc006d471708006a46f7000068c6b6f8006f1bb001bc6e400,0x18a233002248c4008b22a050128bc008a22d002248ac0089a29002268940088c00886158880087a1c86a1885862884008821f002208740088219002091c61e0020887c007f46f870001ba1d001f886c007bc6b860001aa19001ea85c0084a1083a0c82850854008521300214834008245f84800822130005c844007e20f001ef1660c00058834007aa0b0020780e0800206814007f44d8100080a01002027fc00,
0x100266990249a4009726700258994009825e05a630025c984009625f0025a9740096a590025700255936560025494c00952510025493c0095061002451c652002391be50002371b64e0024c92c00932490024c91c00930510024c13c009145f928008e45d920008dc5b9180090e3f9100090a4100239136400023e8f4008fa3b0023e0d4008e43f8f0008dc3d8e8008e0008d2370022e8dc008ca30088208d400,0x1aa6a5aa800aa2a7002a819400aa061002a11c6a6002a4a8c00a9053002a413c00a845fa8800a7e9da8000a78450029e10400a70370029c0d400a6a9900296a5400a4c00a468da4800a428f0029019400a1c71a3800a328b0028ca2400a30530028717e8a0027d1668800285a0e860028411400a0837002809fc009f0009ea7900277002759c676002749cc009b4719c8009c26f0026d17e6e002689ac0098a6b,0x1b6400b5ecfb6000b5ad5002d6b4c00b5ad1002d619c00b5863002c71c6d4002af1aed2002ad1a6d0002ceb3400b3acb002ceb2400b3855002ce14400b1c5fb3000abc59b2800ab457b2000b16bfb1800b12c3002c4b0400b1047002c410c00abc4bb0800ab449b0000afabd002be0e400abc3baf000aeab9002b7aceb8002b6ad400ad823002af0b6b4002b2ac400ac81b002b205400ab41dac000ab800aac00,0x1c3c00c4b0d0031214c00c2c5fc4000bc459c3800bbc57c3000c2703c2800c230700308c1400c2045002f112f06002ef1270400302c0400c0839003020dc00bc43bc0000bfafd002fbbd6fc002fabe400beaf7002fa0a400be827002f10b6f8002ef0aef6002f4bcc00bd01b002f406400bbc1dbc800072f3002f0002ed002ebb9eec002eaba400b8c71ba000b9ae5002e615400b8c5fb9000b82df002dcb6c00,0x18d9f8739a4002eeb6aaca5278962247a9c868000d334b00349d1f4a0034804400d180900344d0c00d073fd0800d000f0033e01c00cf33b00339cdf3a0033809400cd81700334ccc00cc72fcc800cc00d0032e01400cb32b00329c9f2a0032808400c981300324c8c00c871fc8800c800b0031e00c00c7400c6f13c7000c6b190031ac5c00c6b150031a19400c2c71c6000bc46bc5800bbc69c5000c4b1100312,0x1002dd002970027b0025b00227001ed001cb0034d003450033500325002ff002e1002bb0029b00281001fb001d1001a70033d0032d0030ab8ac6a82869b244821de6d000bf2deae2989fa6a],
[0x16e1010d919e0002c9b64023586880009a6c1000d31a20001f9ac3fe348678000766a8ff0140220000f8803fa,0x1000169f440e3e87c80003e7c1030f31d4000379e440a380688000de701020df19e000359be406368688000ba,0x14547c8000d68610610b1f20002ca0c4164188080009a811051032020001fa004124087c8000767f9040fc1f2,0x1a210913d25600037a504224d4958000ba9210813125600026a4041e4b49580007e8f10711820200037a1c41a,0x100035ad242e62cbb0000b2b290b1842ec00025ac242a600bb000076af10a17b2ec00016ab442656cab0000b2,0x1714d28000d6c590e1be34a0002cb0e4366e0d2800096c190d1b334a0001db004326b0d280005abe10c1932ec,0x1738e680e01a040079d03e40003da1e3ca670b295528a4847c0e719c7f0fd9fa3f27e0fb9f619a001772ac43a,0x19ad101df3bc774288500a61482b05a0ae8187d8ff1fc81cd41b1360860f01b22007d0f89ec00038416a1f39e,
0x12491f2223ae758ea84708c124241d83e600063a213b6768ec94c292538a694b290528a394628a770fc9e9000,0x16751192c0444bc1312e048838981e64400810f1b233a5fcb31572003a4681f13e07bcf71ed3d87acf5000132,0x1294510a013e278642243647c4002442de2655f225194000660c9446000cca243c6788f080019232cf21f5000,0x5a93626b80202b0002283811d6544c6c4d71a914e290548a81582b85680741e4c899a22042850c1181156298518a1154,0x11503f0800fa000841062081486b22816661859189302000339622b1130b0156284578aa0100b40058c5e4b784c44e,0x5670465acb482c0520700f82b04e0810f00054028c4e09912c248268a0454040c5bc07d0000d74521d03786e0aa,0x61e24e49891121028695d43f0050d0bd0000418d14586b42f1b13501683005f0b81602a85b0ac1511480018a74a2b04c,0x11f4002d644019022018028ab51680102684c0b17d3a274ce91282f85f8bc04f09a12c2604a4424a8f3220024,
0x62b0ec1543a8544522fc5622617c2ac508bd0185d52a25279910127248498918c61381fc1007931c4e8800381ccc4134,0x189cbe0fd16a2d08d1942503083c9d21861f0e989318025c3c0943a264906a0c24a664cb99632a4748e11b0ee,0x1854c198830e61446189130228c089910c2b84b08910a2b442209106414408822105dd031072f43ed0517e1fe,0x4c318025c4a20d418664041030b8168704560f08382e878061030a08283841dcc2ea5106209a000b5921a2014a8b84588810e,0x56e3808a03907126c8409d93a2865089f000687041b50484104402842a620c280456b0490521041d052270083bcc2182,0x11647da1843e3fc0c0fd0324a0e91d33a24942722c0360680e81e0548a8dd1b93785c0e3173394720e3974396,0x10011a80092c044bf77ad64405009131a45e23045898114264430002d64208310221c499a736e710d521d1046c516a06360,0x4981322580013d1b0e30002723d0791861f00022f2284a20d10c8700412f224429ca39271c3b8644561d8318550ea18818225,
0x4f820031c4e9f73d87306209a0083061528014091230302624c288b110868571bb15a21cdb800206da0660ca020a2918,0x48e11a86cde9c2382700e5a2f21c468608c31203004320d32c23c4291d2382fd130be1422f4040c9424860c6136,0x1000f2c3e7442ca2b00107454843778130328c90c0020066c0d59af3626a8d38008537781e03a8c40500921a24489092214,0x40425e911211f009192bee0603e80842400216280145de8cc021ab00a018d79ae0ba6c4bc8020c26a118a061f65f87f97c1fa,0x50e01402448892028585c838824d1809010c23c0227f8c441000e3a7e91a250304e90c33a6301191d141a6589281027e1442f,0x5e64400e90f0440280fc450280f4420002e85c0b44a88d40613c28050c9c9343cc8801a705510000750b68d08910d214,0x11c4003d300216b485d47b800614b194324c4106d03886146e54ca815229e544aa0000e217d36a360781049f93c280,0x4209b6cd9642403986207d0840012606e1488e0d19a2340684cf1e72d85bc7893646c1c91416e2e85c4790f61e8,
0x182d008300720cc18a102684e89c9370800dc6007807c071dd8386dd2900033c2f02e8789212318c1fc220430493748008a,0x130ccc996334640e31ca396708b00e10f24750b21b2701b03d03b0f880cb11611c8388b191f1ca578880dc424,0x4373cc88017a1e0860e0ea9cc000969488e516a1d4661650f8180320527187a104043e57fd1b8d52343606ba00000fa4c2328,0x11a0318550ce0009c800a187f84c4763606a0d73fc80010a222664c9078004886d04c84d4748e1020e31ca3700e0d3,0x18985b8a116c020db8082ccc50302c4c70302bd9b240310210003681352623c2b4560ac8660d6194350070da1b034864456,0x5441cc108022af0015889a8f48820b23e8b8cd18e0602f01c8ba06c4d91d02d4722e4198312648409a20f27600062970,0x60e0800dc9802d2668e81f13e422508a09432648f10780059a17a1e1d83ac768431d039c748453ec7ace61a42ea,0x5a13ce3c0b81732e85b41c8314683bc058ee04a024002f91c419830404804e00dd1b872c729c91c48710183b46a,
0x117c2605c47e688d09a33ce8d8cf9943326680418e34866c0030a540a19222083bc6d02f85547c680cf1a3344,0x17183e1ca38e72ce02280f41cd1d8b90e20203b87001a37c1c28a6287f18e200e619b2ea4807b8c40fa00143244368,0x641014001309ba808730000e61752019a332644ca18c000b4cbb1788f8788f21ec43c8891f2383d506a050002ad6e0f0,0x6044060c0718e242450c7295e274374b1a10404900b080056e229752c8010c98ca1745624247e900048080082ac4c0be,0x1818bd008d1e0287563492814bfa4d82089a1092d268002ce2784d8290014732181f0380d4190392da5d0b90360120fd1a83e076,0x5441cc3100005d5ac9144908d12023cc69bd10c063318102261d24a90c3c087c317900810b6724431463c4689202177c822ee,0x18e85a8b405a6507093e1841001f8c346a3001f204284390719431ca0ec9d0dd42e841011993306580450f0346898e,0x4000d292123042fec803f0062268008947d000c497785d02891c0a9fd4581389280580a7e8ff1f6819189a602834c50fcf79a4644e,
0x55e424239221c14649191d09105a3840493e0800fd1a878008984001ea711431ca4e86e99a42080922a4038049408bd7,0x642068002bcc740d82208d078002f10c80e8770d20033e8d00033d8014fc008ae3f84310002168801b3c5d1149211d87a2c01f0b11612c6,0x106c0d0002b32424003183c082a600761090de841dbc0429a0005d1fe924b516b0111d430424578b19622d0580358664761b43607a0f8,0x1574b19622c01651da1f4742440c02d27c384048190800fce92353a60f81d9d140880c928041a6271431ca8b00015d,0x137508202334914127a59203d2494800211983037c25c56400201b6062291752506b001d0c6a0cc1940386d001d7e4743a90c472122bc,0x4710669280a5d9799100044b20c2e5063998188ec7122892c48a430128752383f11c72ce3a352864e8020c15843e00836e718e21ca,0x44d0de9309b2412768f06d8360720c4181344024e49b8de1b850c729411c6845020780f8580002a9575140730f6,0x16dc0c52d062dc93815298e28c10a31442844a8320620881080c0145de9341c83106c0c09a0db4028f00e0670cd2504d0ea025a1,
0x4992f43ec498872fc3fcc91832f83f50e92849a24049da0b000a08f0500c24e38824c4c89811822c450861120229890e,0x1095a4848c04008fa6200015c1c42984f4a00a81601e05207413a1e00028c4e04011493c4508b01029c8c1022084c17740c,0x561394724e4142282500b19cb0f450cae9c04964dc5ca4a0c88ac3185500ad1cb844c2f85b8a117a2d80ab41025a298a,0x4c3378018bfb6c6690c98e0422f1110ba2660e01693208083d1aa3b1280ec6009707c254b01c64384f90893c2c4,0x17490f9d30b274527008767279692d65a0331700ca5cd071740504c01706c2da2210a802256c4a25168308dd1b9328,0x5c00644c86003e41e4f908a3b284504b01432c44e43d16326892cae8311729283e1330a21a809c94710a62ad28819030,0x18889e197128728e401b0348949989728058402c5f00832b346385e0ba1b6378728e41c28e81684046a0ed0e1c9396,0x192802997108000a80e214c5725243e0602c81949c748dd1b93a66f0e888836c4950aa1909c00098842254e322c312,
0x4714a84648f0014731713222845ccaa0f06e85ccc24c06c44c8b0f82007dcf6120000b58268af4a69401ca51066,0x13100406f954189340724e49b94346a1001c0724509492983e4988ec1da170f4661258009ae00b97142298840016b286150,0x150d1e2273280071cb32384013610131a801c6c05b1b2a8352f60007395806075505088c01860d8608084a865819a4a0124cc199166301d9160e071,0x1810718c01866580224d304041602c458caf0e51b88490081c4fa060673146399b2c800031d0e1652b82d4741009f235284,0x11ad2da584b2958002d64b41c8ae2282be013ff8e2010f5ac8001438714b20609a86030d2b83632c3052b0081304c4704b0,0x5c322272c8f9c9236001ad9c48710620344e9645a8b43180205d8ba178644c719a4b42e5250219ea639cc336480000ff,0x8287f65c07696c1f24c44e0504e8780ec00b1f2e8e51c8378708db0102e85e0300c20016300032b6a9711e9bf21e],
[0x12ba570ad95a2b2560ab9562aa550a995029e538a694c296528a494828e518a289812e2584a8941262484889011e2384688c1162284488810e218428841061f03d87a0f21e03b8760ea1d0398720e21c03786e0da1b03586a0d21a0330650c81702d85a0b21602b8560aa150290510a013c2704d09812c2504808e0d0190310600bc1682c0560a81482704c08c0f81e03a0700d81a0320600b81602a050098120220400780a01201c0300500800800800,0x1578ae95cab856ead95a2b3562ac157aac554aa1522a3530a4948a9051ea3946a8c516a1141a824fe9f53e27b4f29dd3b2754e69ad352694ca991312604be9792ba554a67ecfd1f93f07dcfb1f53e87ccf91f13e07bcf71ed3d87acf21e33c4784f01df3bc774ee1db3b475ceb1d53a874ce91d13a073ce71cc33c674ce19b334664cc19732c654ca193324644c518931061cc31852fe5f8be9792f05dcb89702de5b8b696c2d65a8b49682ce598b2964,0x17e8fcdf93f17e0fbdf6bec7d4f9df2be47bef79e9bc778cef9debba770eddda3b3764ec5d73ad74ce95d13a1740e75cd399730e5dcab93724e41c6b8b714e15c23796f0dcdb6b6c6c8d8db035e6bad61abb54698d2da334067ece19bb36666cc59832b654c7d89311620c3d8730d618c2d8530960cc1181b02602bf97eafc5f6bc978af05d8bad752e75cab9171ae25c2b816fade5bab716cad75acb556a2d35a4b45682cf59cb35662c5588b0d5fabe,0x354ea9551aa149a92d24a4740a80d009fb33265cca9932a253ca694727e4f49d9390520941181d0360640b81101e003ff7f8fedfd3f7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC03 : ¬ FormulaSat cC03.originalFormula :=
  cC03.unsat (by decide +kernel)

def cC04 : Certificate := ((10,10,11,339),
[0x1200830007820c001f87c1e82a204000d87f000710d47c000701f4000d07d000661ec000c87b000761d07207879000281dc001c075000261d40019873000241cc001b8710006a1c4001b0161bc001986d000680386b000661a400190670006219c00020650000218c001504518400180561185f0005e164491740016049174001705a128001684b000320943b0003a0d0260e4000d0270e4000e0360a0000d829,0x1148bd000b82d8b42c8b00f8bb0004a2e400120b7000462d400110b3000a42c4002b0af000aa2a0a6080ad000282ac00098a90002429c00288a5000a029400028a300004284002789c0009a27c002389f0009d0009825894248901309b0005a264002089700056254001c0930005424c001989100052244002308a220862103c23c001288d0008222c001208b00046224001c0870004421c00198850004221400,0x13d400344533c800340f3000523cc003b8ec3a8e8398403c400128ef000483b400118eb000da3a400340e70004239c00388e5000e0378dc088e30002838400098df0002437400360db000d436c003581a36400340d70001c35c003481235400340d30001434c00338d1000cc34400030cf0000633400328c8000c632c002e8cb000c9000c4308c02f8bc138c70005a314002b8c30005830c00158c1000542fc00,0x10012f4a5300012e4b4004b92b0012e0ac0048c374b000474334a8004a12700128494004a01f001230a5260011d09524001220012047c0046d19470004691d00118474000211b0011a02400009190011800c0045c004551145800451130010d16d120011043c0041c47438004300042909001060010440c00400fe000fc404003c101000ff000fa3e0f63d0f2140fd0005a3ec00390f9000583e400158f7000da,0x1001695856a0016859c005a1650016858c005a04d0014515d6600143155640014114d620016057c005815d0016056c005803d0014511d5e001431155c0014110d5a0015855c005554d558005515300154544005514f001540b400514375480050c355400050433538005314b0014c52400531470014c07c00514295280050c27520005042551800510004fd3d500004f8090013c00c004e939001364d4004c931,0x168999001a213c00639a10018a67c005f457670001599d0017b1559a0017a66c005c453660005c19900196654006599300196644006583f0017d11d940017b115920017110d900018c63c006318b0018960d8a0018861c00621850017d0dd860017b0d58400182604006097f0017b09d80001710957e0017c001785ec005d17b0017606179001705dc005c8105d4005c1730016f5b5700016e02c005b0050016b,0x1001e278400789df001d916de0001d7165de001dc76c0077041001d7125da001d8001d475c00749d0738300b1d5001cc74c00721d10003273c00729cd001ca7240071dc372000719c5001c606c006fc1d71000709c1001c204c006fc15700006f5bb6f8006f00d001ba01c006e1b7001b56cdb6001b40bc006c81f001b06bc006b1ab001a869c006940068d97690006819e6719a6604e68c006899d001a266c00,0x100223886240022205c008800f0021f0021d85e1e0021c86c00872190020f16e1a0020d16618002168540085a130021684400858410020f12e140020d12612001fd10e100020e0020a8340082206810300ba0b00202824007fa07000328140080203002007fc007edf97f0007e80d001f801c007dc007d5f37d8007d04f001f2104007c1ef001ed7adee001ec0c4007a823001ea084007a1e7001e5001e3775e4,
0x1001f1001b9001ad0018d001590013b001330010b00201001e9001cb001b1001a90013700121001050022f002270020c7b9d66d9aa629564e130420007f9e6721ae6997a50934479020023f0023d8e63e0023c8ec008f0510023514e3a002388dc008e0410023510e36002338c63400232034008c0070022e8b4008ae298b0008a819002280440089a25],
[0x1548ac09f1380001494a2ae2444500006e4b0ab08c114000149262aa1f83d8000b6448aa07c0f20002390e2a6,0x10002b99c2ba3506300008e650ae0cc18c0001b9862b62d84e0000ae598ad0af1380002395e2b22984e00006e,0x1528a494828e518a2944286000bd1422c249c8f0000b6868b012123c00025a142be414800000b6780af0de18c,0x54f29c5300001d0dcb188b11c2204100b01a0580a81a11a0008d8790ec1d09416227e45c850f91d43a04b8890f0,0x1038068962980004187c06819cb20ce2b633c650c82c22780b9620325545108f156254550942b0558680ac12c,0x1080ab021128248000810f81e89716503624010893124254b10170040640082000058c4408410403005823044,0x108c11008116b392e25a4b00901002804c0c01a0325544788d12a5940e0230440580880f12c4bca6141000144662cc,0x4c42c2294548ab142274680ac26653ca71420005041a8252d006c48165126254b101803e5900c81011a0700d2cc,
0x4a52c25a45614e0000556a19e328668c8196340a780006a09cbd9692644c4980c3182308600c719233c668cb18a,0x1004001581542a0001540e65b04d89a1320105bad0000cf83255c518a002e5a80e9670440004194c2d62884f0ab152,0x43c076000b80a52de0406598a310999420005ecb816e006008020355a0020a40000bc252825b4018020085a05200c046001c5,0x4dc16a38c5c8e61763605995c2b239c5e00008e154b88082ea0880f02804c979410001983897017e2f85e83a072,0x4332b45505d0b70fe0c85d8802ce2cc3e83003c564a997006e0e05e08106a000238662e6040c6800470339722c2,0x4ee1d23405609812c1e88c1171f43e4290382a4544a814f29c534a614b294520738bc10213c000375d017034062,0x4e11cc360250312b42e85b8bb1661f4ae1592a61241797100052c8701802cb900e01a5cc8d91a1fa3f02883721e,0x13b4759191f6068520170325b4b60a814e5a8000ab03a58cb59670440c82703409a0ccaa04805a2d03f8b8100,
0x15a80208f088060d7074558001a6b396b008344241aa0e0d9000718671065d4a011d1fe4707f10d21c42c2004107a0f81f84c1d8,0x11602f05d1f2520000db1a05d87f94023a3f88e10d1d84387690c1d61880d0610324647d8000c005c2f8a42c6,0x13c0778f80100a5770bc0101faf015c790590ba3d0798f11e03bc2a0530ac154bb0001b6708bb85b0b83d87c0f30b2,0x11d43b92b0e80002d97a20e57884103202500901242544a4b00141e60a0fb4ac848000b6124bc85a1ea170788f71ec,0x10d81c0e71780d40011d1242404104c2f64588a91423e010458ca190350692be494919220000bc682f2198bc0672e8,0x10981602415a35c590b11603985d8e417426cae95a134264188851060d0438860640a81583300a5e81417406e,0x12dcbd82d0d20ac0304d00a5e8000d70a0ba0750a20d80a0f31dc290380383b4e71781d0278000b6410521245f0b08d315c,0x11a00404b09c0242500a092384ae8dc1c838c730d71a65840008b190120ad136268428991060a8438860900003c976,
0x1498a017d0080e43836a000492fc40c8090820c4100380600a5e88480009275cbe940208498831282104a8811220d4,0x4044323b075030514141029f12b2121d0000f2084600020c735c160b20105655d2b40a4bf02b0085b40c2de420572fe4909012a250,0x40888ec006b0013dc670a4208c080020e380730de5fc121062504ec8412a27a408911380d41903417e0d21c80297a0dc,0x567302600358281225607729c4f873874000148339821c6370730d61a45b8b08b51722ec588ad1360bc4d0992f8,0x57004a608168292fc06165800574523064d89a934010b5d370d44e49c13d2761cc3795d1c801029801a5c7115618c0e96b2ea,0x153c738bc09e000b804e3466146b0e61c43486d1831ce000219713082dc1a0bb1600c8161670620c01381e2fe,0x13c8c30bb1742c8ad0ae1ba10c728470845846d8d52de5b86c8e608a5f8230052f4110ba0e01be140688d00a4,0x4102823618630860c9f00008661c021d50109bb0a444831282244209513b2204089113d2701a83286d3061d0e4a26000e3ae0,
0xa6c4e89a9342781502993d0ac1549c06c0d4600321870081dc052f40322fa7c1d0001882724dc9e93c274],
[0x139a730e59ca392720e39c638a710e19c23826e0d99b23626c0d69ac3566a8d49a834e6986c0d71ac3546a0d31a4344680cf19c334660cb1842f45e0bb1742c8588b010c214420831042044007f0fc1f43e07b0f41e43806f0dc1b43606b0d41a4340650c818c310610c017c2f0570ac1542a0530a41442804f09a12c2504909011c230450861041883005e0b81682c0560a41402704c094120220400680c81702a0500981101e0280400600a00c00800,0x1732e51c9b92722e3dc4b7c6f6de9bb3716e0da1b33656c8d81af3546a4d45a834f69cd25a434768cd15a2343684d05a032a652ca19231f63cc05802f65eabb575aea5d2ba173ae65cab8970ae05b2b616bad65aab51692d059eb39662cb594b25642c758cb15622c257eaf95eabc572ae15baaf55cab5562ab554aa5542a754ca9551a9e53aa71432854f69e92ea5c4b69692c2574ac95129a524a293125a4a49291d2324147c8d51a2334548a5141ce,0x1a054027dcfa9eb3726dcda92123e4748c87d0f61e43a774ee1dbbb6764ec5d83ad74ce91d1ba2742e81cdb9a])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC04 : ¬ FormulaSat cC04.originalFormula :=
  cC04.unsat (by decide +kernel)

def cC05 : Certificate := ((9,9,11,200),
[0x132188586d000b8d6002a1a40042338007c65000d0c6002f170b4582b088c2001517c00542e800845b000f8b2001a15c00522a8009455001409c4c0e14c0020288003c4f000d09a00241188816258003449000608e001a1140041210008043000f88200200fc003c1f800703f000e8203d000d076001b02872001a0dc00321a8006035000186600010c4002e15800401b,0x1002c15e00548bd5c00562ac00a313aa800a8002994a0051001409f00271340049274009b0021c5e98000b932004125c00764a801208e462291024498010e2b480005491002091e001423c002646801008b001d9120042a18008441800fc81001e902003e050fe003b1f40078071ec00763c800e877001c8ee00041d4000439800e06e001b0e200301c4006f001a8d066,0x1803cc00fa7e801ecfd003e024fb003c9f2007a031ee00793d400f077801dae777001d8eb003b1d2007607400e310ba800e10fba000e672801cc170038432e40038800df00375b2de00371b6006a8bdb4006c35c00cf13b5800d400349a2006700198cb0032400c762b2000c61680188230030982005faed80005f2f400b910af000ba0b80170005b2d400b3002c55ab2,0x1acd70015a03802b0030055c0155a8d580154a98029a2fa9002a14f00534574e00530014aa48028f43a40028d45004fc43440050a82009f86e80009f0027a009dcde78009d4e4013317ce001369a8026c25004c45334004c8012e9680255290049a4a0091802431d91002411f004645f1e0047236008b8a634008c0022913004421e008642c010883802090300401fe00,0x802560088802120080801e20069801860053802fe00b38029600978024e008a8021a00828019a005b8014200be802de00b280261288b43a0cfe7734180a4004b2491285409f8e0652d13c00bf5d4017cbd802f377bd002f015005d81e00b9dc6e800b9024017002802dd6d005aed36c005a82600b40340166ae802c96300586bf62005802200af02c015b],
[0x17519a300ba0005e6d1982f0b60004e6b196290a0000425e194258900005e571922488c0004e55190,0x100056a71a44891c00042a21a24791c00036a01a04510c0005e9c19e3f8f80005e8f19c348c800042,0x10006a6a960429063d8f23b8b42788a5e1765d1725c16e5b16a001f8701a84c12a0005ea91a64b12a,0x10c0206a8dc61800708aa101ae0a8d00b8d6350286a800708a6281d86b13c4e93801804028085197c,0xa406d150931b053248cd328d135c0202f2a928619825e8002a9c26c0cc09822328ce369ac0c82c09000,0x14b1284811c44100211b06d14c52948390e03a0e6388de3a94e62166001fa6c82608824329a0338a2,0x1461101e870658be10836060440e01e1b8460e9b06a1b2100346a8861404e22052468b22104c00130,0x1000ee6e0140a6cc18462000175b4078440e0140ba2809c2918c5902818c84401b62c0ac2b83e1283c1200267916,
0x10400c6a944590001f9bc56958558621786619060171b857168001026e9545495015854168585797e,0x298244e002029c782086a1a0746d8440e01c10836069bc6e87c1b1b80804d810275206f9425013e0480e05814,0x2c3308c13009b2348213842000e3384e000098388100611f9be040308601a52070802699324d12e690764d800,0x1269024613426100459326499c679a6201c41b9ba1b1b8219083d0f03b0dc2e0aa238886398c62988,0x1588fa438721e8701d990690943f1124412e],
[0x15aeb3165aca592b2163aaf55cab5562ab552a9d52aa3536a654c293520a1d432854f89ed3d2724e09a92ea5c4b69692ba534a494524a4748c9051f2354688cd1522945054ca915029e530a594a292520a394627e4f89e9322624c09792e25a4b09588610a210418821022003f87e0fa1f03d87a0f21c03786e0da1b03586a0d21a0338660ca190318620c21802f85e0a812c250490901102082f05c0a0138260400600b8150240440780900c01000800,0x19892e65c4b796b2ce594b192123e4748c8930fa1ec3c8750e21bc3681902a04c04806fe1e73cd798f2de43c7788ee9dc3b7764ec1d33a4734e65be37b6e2dc1b43666cad81af3546a4d21a3b2a652c7d8f301600bd97aad8])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC05 : ¬ FormulaSat cC05.originalFormula :=
  cC05.unsat (by decide +kernel)

def cC06 : Certificate := ((9,8,11,132),
[0x12a194006300178b85a2c158406100088be002417400362d8006459000a0ae00291409c4c25058aa000f14c0048288006c4f000c89a001412c0046248007c490011084400a11c0036228006443000a082001e0e870121f8006c3d000c87600140e400341b80064281a8006033000b06600170386200140bc002a050b40028158004c290009052000309c000212800441f,0x15c00168b3002c15e00562ac00a85380148a300284009f4ea80009e1080138170026932004b8012a914b0012893002344692002411e004386d1c004600114890021800844100100850020c007e3e1e8f0760c204001e3f800387d00068f6003a1e4006a3b800e475001b8ea0038040e600351c4006c061bc006a36800d06b00198d600041a4000433800c86200180ca00,0x17fc08010008801fc0d003edf2fc003e812007c01400f67a801e6f17a001e415003c02600773b400ee73801d6e976001d40f003a0160072b8dcc007201c00e201801c2006fb6dc0006f37400d711b7000da6c801ae1f6c001ac006a801a6cf6a001a4d10032c46d0003399a006706400c90eb3000ca003198a006180182bd6100180bf002e446be002f176005b8757400,0x200638016a00588015a00548014a004d80116007b8020a007780190c45b2c95caa532893088004120600823f40101],
[0x1dc44978ba000fb6110592a80046d0439409a0011af90c3f1e0004692428f474000da3908,0x111068582a0c05a28de7b00124508b349a0ce080301c0a0a049acf200140cd14602e80046,0x12c168ac602f3b9e8006a3aa34cc65320080204019a8f20014a30dc6d360502013078481c,0x1311c150984b2512490431d8e5068240a00fe7e3e9f0c65c299086e003508d1c753a1cc5c,0x123000891e78271586836198d508881f13cb0572f904a45b31100a25a308c90a8643a251a,0x1294723cec7a002408c4422870441b108003e190602c3c1810069141d0ba2d1825120988e,0x5c8e2701409c54],
[0x196b2ce594b189312223c4387d0f61e43a8710de1b40c815026024037f0ee9dc3b7764ec1d33a46f8dedb43666cad81af3546a4ca994b01600b616baaf55ca1942a724e09a92ea5c49291d2324147c8d51a23345454ca914b294524a414728c4c89893025e4b89692c25621842884106208408800fe1f83e87c0f61e83c8700de1b83686c0d61a8348680ce198328640c6188308600be1782a04b094124240440820a01001802a0480780900c01000800,0x32e65c4b7])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC06 : ¬ FormulaSat cC06.originalFormula :=
  cC06.unsat (by decide +kernel)

def cC07 : Certificate := ((10,10,11,501),
[0x11b0ab0006a2a4001d0a7000a22809e2709a130a50005c28c00168a10008227c001609f00056274001d09b000962640025097000922540022895000902388c0f8930004a244001208f0007423400220862103022c000f0890003a21c001d0850008020c001e8830007e1f024204000b87f000741f4001e0760587b000221e4001d077000721d4001c0750000c1cc00008710006e174001283d0002e08c000500b,0x13b4003ac00398e4388e0378623a400340e7000cc394001b0e30006a384002e8df000da360d6350d2140dd0005c36c00168d9000c235c00158d5000ba34c00338d1000cc33c00328cd000c8318c40d0cb0003c324000e8c7000ba31400300c3000be2f01a30400088bf000ba2f4002e0bb000b62ec00040b9000062dc002d807000b42c8002c0b5000a42d4002cc002b8ac2a8a82985e2c400260af000942b400,0x10012c4a8004a12d0012b00126491224811e1404e4a400171270005a494004712300056484004411f0011a47400461160a02646c00451190011045c00449150011044c0043911000060110f0010c428004210d0010b0010641102400fe1404c42400171070005a414003f10300056404003c0ff000fa3f4003e0f60a0243ec003d0f9000f03dc003c8f5000f03cc003b8f100006008ef000ec3a8003a0ed000dc,0x1001545bc005416d00168599640d8325ac00589690003c5a400551670015059400581630015a58c005795c0a826584005515f0015057400561560701856c00551590015055c00549550015054c0053951000120394f0014e04c005314a001485340052c0051944509404f85252400171470005a514004f14300056504004c13f0013a4f4004e1360a93b001344e4004c137001324d4004c1330012e4c4000492f,0x1001a66c400689af0006c6b4001a9ab000686a400691a7001a269400681a30019e6719a11042684006619f00048674006319b0019666400651920a82865c00641950018c64c00639910018c63c006298d000080198b00188618006118900187001826017e5f17a19060614005e18300174604005897f0006c5fc005517d001505ec005d979001745dc005c9750016a5d4005c16e5b04410173001625c40012971,0x1001ba7b4007a1e6791e2780547ac00171e9001de79c00731e500058794006f9e3001ba78400771df001d477c00769d87584677400731db0004a76c006f9d9001ba75c00749d07383875400731d30003c74c006f9d1001ba73c00729cd001c473400721c60b1cb001be724006e9c7001c27001e714006f9c3001ba704006f1bf001ba6f4006e1bb0000a6e4006d9b4001b26dc006d4006c1ae6b1aa6a064189b3,0x11663400232002308bc008b62b8b8008b03f0022a0c40089e258a000898250022405c0088a210021f0021d8661e0021c86c008446f868008621700218854008621300211176160020b166140020115e12002100020e83400826058280082207002010be060020480c008042380800800007f1ff001fd001fa7e0007d9fb001ea7ec007e4007d1f27c1ee7b0667dc001b9f5001de7cc00731f10006c7c4006f9ef,0x1002671667c0027a002769e4009ba79002749ca701003e9dc0099a75002609cc00972710026c9aa680c8309bc0099a6d002609ac00972690026598e660026409c00988170025e9840097a5d0025b002599565a0025895c009446f95800952530025413c0092c59948009400093a4d002499164a0024891c0090c2f918009101900242002408fc008f4008ee378f0008ea39002331be38002368d4008d84d00229,
0x114c00b0ac1002bcafc00aeab8072bd00022aec00ad2b9002b6ad400acc00ac6adac800ac2af002a71beae002acaac00ab2a9002ac14400a945baa800a4c59aa000a9800a8aa50029aa9400a829ea7042a8c00a4aa10028ca7c00a229d00298a5a940d29b00292a6400a329700288a5400a468fa4800a40290028e06c00a2a8d0028aa2400a1c00a1681a1800a12830027b1be82002809fc00a027d0027916e7e,0x100022bec00bd2f900020be400bd800bcaf5002f0bd4000500ebcc0002804bc400bbc00bb6e9bb800bb2eb002ec19400bb05f002d91b6ea002e8b9c00ba053002d9166e6002e4b8c00b86ddb8800b82df002e011400b644bb7800b72db002dc0c400b643db6800b5ed5b6000b582b002d405c00b4ad1002cfb36d0002ce04c00b380d002cc02400b3003002cb002c9b16ca002c8b1c00b2065002bf1b6c6002c4,0x1c9723c9800c90150032404400c880b0032201c00c8400c7f17c8000c7b1d0031ec6c00c7b190031e18400c0c6dc7000bdc6bc6800bd469c6000c5b150031615400c0c59c5000c4b110030fc27100030ec3400c3b0b0030e11c00c38410030312f0c002f71270a00308c1c00c2305003080e400c2033003030f706002f70ef0400301bf702002fcc0c00c02ff003000b400bdc2fbf800beaf807818bf400bf01f,0x10035c0dc00d5c3dd6800d343bd6000d5751d5800d53530034d0bf5200350d3c00d401f0035007400d2c21d3800d3000d2747d2800d234b00346d2c0005012d2400d20150000a023470034602400d1400d0f3fd1000d0b410034218c00cbc6dd0000cfb3d0033e15400cbc59cf000ceb3900337ccf3800336cd400cd8430032f12f3400332cc400cc8350032f0f7300032dcaf2e0032c0b400ca81b00328c9c00,0x100364ce310b8ac0a92789322e83000d5b2ec0ad8afa9299a4a8a20a0034ac9af4b42b4a225c8fa207f800e1c00e1781e1800e13830038419c00df46de0800e037f0038015400df459df800def79df000de82d0037807c00ddb7500373dc7740037203c00dc0050036f0036dda76e0036cdac00d5c6dda800da05300366d9400d8f5dd9000d8b6100362d7c00d88450035712f600034d1275e0035cd6c00d7359,0x100329002d3002b70028b0025f002410022300377003670033b00313002e5002c30024f002310020f],
[0x18e0fd0f71e000037a1a3f23cc780000ba858fc0f11d20002ba123ee3b07480005e818fb0ea1d200011a023ea,0x100017afe3fe51ca08000deab8ff12e25200037a823fa458890000de958fe10e21800017a463f641c818000de,0x1708dd000076d61021bf37400017b52406648ba8000d6c69011862ea00024b0a402600ba800076c110017b2ea,0x1570f98000ea81cf119f2b852c9911a2163ec741f43e67c8f89f03de7b873800694bd1031c737400024b5e40a,0x1614650c5184300648c41822fd040003aac210499b33c674000bd17c67cfa000376820ac8052b655c0200700c,0x5ea00077d0597c2fe020199a261c680d231262c6780006667008066eeb0e4145fcbe17918c30c640c7198604658cd306,0x136ced8da418365058d600017cd500817ce41cc38c0038041a3d8fc0f91f07e4018fa0001750620a3188246a0d331a,0x6020746bccb0393626602183635863c2584c364664248001c4320630550682e9071da1ae770ec9d83ae010309b0,
0x5040de0a0120f04223b8768eb3ec7d40080041408d0802f3380c4cf19a05c0c0001212ed078470900f022046076,0x1150298570a4168280560aa144279f72884147a1492123e4a41081f07f8fd1f90b28302e05d2944287d05b000,0x55b2b46d8da1b836e8180021233a0004ab3e570fa1f30002dd099723a8754e99712e85cc001d63da0000a2f5424,0x10003785b42a3f07f00a012840820f220c3d4848f92103e0071fa3f207c0f00840e4287d00044e1bc4fa142b0,0x11bc882162867909594625a5249814825e7f8fe9cd354634b3950222408779ec3d67a8f49e83ce798f294a262,0x1080ff1fd3f87e8fca1507a0c90786a0820850601c01081c3684a0541b82602c2944c48c90a1f41b024829000,0x40a0660250803501c4a8a10f207e07c0f0420440f80e9f728a510961051ea3d0a493023000098a5e45c840f8080,0x1805029cd31a7b0f50002d65a0b316409285c328640d018c358610ce450348660c41809a91d26c4789a11c068,
0x18500a0c74147a8083fe040d10006a85a84c000d101069c0e1281515c3ac130161f33da000ee80035d4f0de860c518c304244e21cc394,0x18340031b0118ebc2000f8a19102568ea15b3aa55ce984d0bc1382fa110b08589a9362680d019a1006a3f47914207e,0x4d94163746b0c21803706a80008e0e00b40e3947202a1cc0b0f090a1f438c1480062c868003177740231537c6f1df3c0,0x131cc80d81b663cbe9ff0180347e80f42807c0f02203a7dc828f40089342000036ce11c4864ef1e041a36810a0c1c0,0x40011aff0181160008d82c6e8c01b80004bc0e4f09c13b26e394151332646a87302c3e27acf094a01021ea54365e4bf8c331c,0x4008fe1a0c643a5b8b596f2d45a0101011103a9ca01088ae0020438dab650e13e34e6a4d213a2804fc9e939284078110002c206365,0x1680022633c81f80c4d21026b050818860f41b03241e010c2882040c198a000c19880003a8006144b0940a87304c058784d91990083c449052,0x1290161e13320109a9440a4002d92e8878005171181d83a0726bcd89ad356688d08c61903606da0e088808cb198434,
0x187cb68a113a5bc5016a134870b409f132650cc21a00851c9c20a3d0421091f226c4180027e4100015f0c03c2765182a1cc,0x1400b31012c23fc0a2072ce408f49e6000b644988e062880631a11906886c1ab1b66b4d60742921e85829a0614f040a9e7c,0x14bc8b80430afe9fc0886041001681c9011f1ca0a88d91a029634e60587c00a5877849891900033c002b24a83c442058b18172ca,0x48f0240640c1273c886c8691038043d019fb018034908fd01e44c9500c7c64988e10c4b08a8003220257724846885106,0x1008b39e9000b641ea2210e22cde1c13902504a896396724e618838a6310218202248809a2002a85c4c09743c,0x11f400431890b516f2d80a012a1c2d009c0d82603488511024008c246876a118003de1582a1cc0113c818486232ca598b11632c0,0x4730e25149611520c001418e0023808de0237f8f4080401fe0486247b03023c00dd27287e0543983f82c3c2748d91992ac528041a5,0x1744aa9ce2a21f03c8760ea578afa233606c50f997330868ae800fb6070f220844c9514200065c740f0074391f70ee,
0x1898138280006ac254485b0b79690202ec0032e0a0bd08062808334001a6040d90806f8385bc081ba158001b60216903072928894e79e335c64ca91d02a8,0x1478ae91c0103552a02834c9c1120006780a27c840e04c0004b52204186f25e01060904200fe84c33a004a51f8004a30105eaac4c40249f0005cae8,0x4890003b40082a004172204192f01106c4883a0406483a042fd220182271402844d09f13254caa9510f82783c88c0ec228020d700270a3a,0x10707c830da4ba0fa002ed8960f1141c539872502096022620c618224404c4c2260308944a88c11400071801034101c6908001c206413,0x40425e063b723444083020ec440040208103ad024e68088144102042c051ea04207298490918e51761f82502a296080809781fc2602c3e4,0x51e38043c9a15d23880cfd834014030bc14d06602406a1024a0d47e80f010f1c0141600ad10011387c0011291c224023bb510003b9,0x1400808ff44e0485721712e8985b0454480113592005135b5e6c50f9283c886c5aa0232c654cc21a21a4d48e91026c,0x5bb2ee5d8bd17e34e78cd31a83526910e9be37a0dca794e0016cdcb39871100091308608b218c31059893161070,
0x168cd32283547ac0004b65e8a45c0b91662dc590b11602bc560ab1542a0568a914e298529b33722d0da991424,0x4e60587c8f080c482002478b0c6185316604c3a2800394c4b6068ace61c639670ce422839a7b00004b6ae8a8d49a5350,0x10b0f30107bf1694e37853ce09e34528a915a2338080c0614d01a8407e80f01071c0ce4a025990a64e80b27c34c6a04af95307282a296,0x5011fe401138170240580122c02a0010c83289448008762083b7051dc91c041dc800a3c647720a008002a45021cc],
[0x11fe3b4760eb1d4398728e41c4384700df1bc3746e0db1b43646c0d71ac3546a0cd19832c630c518830c610be17a2f05c8b816e22c4508911021c4308510820c410811001fc3f0770ec1d43a0730e41c43806f0dc1b43606b0d41a4340670cc18c310610ae1542a0530a41442804f09c1342604b0941202384608a1101903105e0b81682c0560a81482704c094120230380680c81802e0580a8140260480881001e0280480800e0180280400600800800,0x14788e8f19e23c2780ef9de3ba770ed9da3b2760eb9d639a730e59ca392720e39c638a710e19c2382700df9be37a6f0dd9b93706dcdb1b53686ccd91b134868cd11a134067ccf19933065ccb192322640c718d31862cc518931061cc31792f05dcbb1752e85ccb91712e05bcb716d2d85acb51692d059cb31652c8588b095a2b2560ab9562aa50ca11412804f09d93a2724dc9b12f25c4b49612b2544608b91622a4448810f21a4308590420640880900,0x16e0db9b6b6c6d6da5b43676ccd91b0b5e6b6d45a834f69cd2da534768cd0d9fb3e67acf19db3966cccd93325638c618bb16628c4d8830e61ac21833055f8be97caf85eebd97aaf45e6bc978af05daba974ae85cab8d712dd5b6b6968acf59cb35662cb594b25642c758cb15612bf57caf55d2b856eac957aa654aa914da9a532a5d4a293524a3d46a8c50ea113da7a4f29e13a2704de9b1342674c898930a5c4b69652c25049e93922a444869052023e,0x1a7f4f69d537a694828fd1c92f25a4ac947cef95f13df7a4f45e83cf79cf31e5bca790f1de33c4784f05dfbbe77aef1dd3b7768ec5d3ba674ae91d0ba073ae71ccb95728e4dc939171ee31c5b8a712e19be37b6f4de5bc3766eadd1b9371])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC07 : ¬ FormulaSat cC07.originalFormula :=
  cC07.unsat (by decide +kernel)

def cC08 : Certificate := ((10,10,11,298),
[0x1038870000621400208800007e20c001c883000810007c1e8781d8741187f000541f4001487b000501e400198770005c1d40013075000701b86c1a8680d873000441c4001086f000401b4001986b0005c1a4000f0690006419c001806700062060650005c18c00070630005e048610005c17c000585f0005a174001605d0000a16c00008590005210c57000561504400054114000c0270d4000d0320a0000c829,0x1000542fc002a0bd000502ec00248b90004e2e400220b70004c2dc002c8b02b8ac2a83a2d400110b3000422c400100af0003e2b400220ab000a62a400278a9000a4288a00b0a70003229400248a30003028c00220a10002e284002709a2602027c002589d00028274002489b0002626c00220990002426400250970009225400240930008c24c002381a244002208f0008a0508d0008822c00218890008422400,0x13ec4140800400003f8fd000fa000f83dc003d0f2000f03d4003cc003b8ec3a8e83984a3c400150ef000e43b400140eb0004e3a400130e7000e239400380de3702238c000a0e10002637c00368dd0002437400360db000d636c00040d90000835c00350d2000d03540034c00338cc328c83183a0e0d10004433c00108cd0004032c000f8c90003c31c00310c2000c0314002d0c5000c3000be2f0ba2e0b6120c1,0x1519450014650c00519410014611c004dc55510004d453508004bc4d500004f93d0013e4ec004f9390013e0e4004f837001371153c0013510d3a0012f0f53800136001324c4004b52b4b8004b00b0012a00c004a1270012448c004811f0011c46c0046515468004611700118064004441d45800451130011404c00444174480043d0d440004380b0010c00c0042c0042505428004210700101155060010440c00,0x10016d0f58400182604005fd7b600005f97d0017e0b4005b42f5f0005e1765d0205ec005e9750017a084000a1790016e5dc005b4255d0000917500172001705bc005ad695b0005a80f0016801c00591670015c59c00589605782a594005516300150584005395f0002e57c00569585581e574005515b0015056400539570002455c005495500152544005314f0014a53c000314d0000452c005240051d3f52000,0x17281f001c3095c8001c671400705bf708007000d001be014006f4006edb56f0006e9b9001ba6dc0067c516e0006744f6d8006d1b3001b46c4006d0390019f105b20019d0fdb0001ae6b4006ada56b0006a9a9001aa69c0067c336a0006743169800691a3001a468400690230019d09da20019b095a00019e0019965d9a0019804400658090019464c006418f0018d0018b61d8c0018a624005cc516200061985,0x1001ff001fd7d5fe001fc7ec007f1f9001fc7dc007f04b001fc12400774517e80076c4f7e0007644d7d8007d1f3001f47c4007d03b001dd105f2001db0fdf0001ee7b4007ade57b0007a9e9001ea79c00774337a00076c3179800791e3001e478400791df001e408400774297880076c277800076425778007700075dd5760007580f001d401c00749d1001cf72dd0001ce734007382b001c30bdcc001ca72400,0x40071c00644005c40054c004cc0049400474003e40084c007bc0074c006bc006540060c004a400484003fc007b1d06b192601664d126478fc001da7119c6396e541304891a3d80084a110020f836100020e06c00830150020b002098160a0020881c00804518180081203002011060200200],
[0x16a0978c01620002898825c250448000aa5109688c1120002293c2581cc380000aa418958710dc00020902254,0x1000209f22683e0778000667a0998f21de000149e226436c648000a26e0988d6192000209b226034064800066,0x14a49412724c49492123244000ed19c27043c860000a28189b90d21800020a0226c410778000a27e89a8fe1de,0x10404092300019c9d07d0f21e03b80700c0240400e01a03c3f87e0001948c13922e38c620b013e220418810da,0x128c5009f1d64988f80029c59c9e0e21c23804e09b13c274001c229e4ec0002d1e80202b02c0500c0f81ec40139022,0x12544c88e0384c46e8de1ae06c9d02204637c4d0200004d43a03927a29c550e81d4394528a21582ac548a4150,0x4fd1bc374801312144249a90b1be0002883f27e2484388610a01049834064001400ea4f80f81e03a4b44989812e,0x41f03c0100181d27a4b44993e13025c4b0950364e82c04e0441642802322442c6185709a00038a8c5006a8d8270,
0x10941202704c0fc288bf088158610ff1824288485208014c2092e26a4fc2a04226c4388891026e07002855086,0x44d0001044414322a4508982b0520a81402d0584589080011024ca101018a450130240009c0692822f8578ae15a,0x10e81982e2841181c031096124959370e8414880752144443910121c4a89a13609e3f05e8502404708910b0ec,0x10cc139450602cc1b0b716c000b689f138268bd1440764cc1e0fa1743ec5e0f316c0d81a82f07c0f42504c090,0x5471b83686f138206364841302144049a0003162084f28c4e0658f119c3d4698fb1a43e8979331f83509011e000,0x14ac9b8ee0e841c831101da3b0000dd094120001b2138260ca180000d150ca31450d63f06a06c240478000cb1a800041066,0x4ce19634c688cf0043508f00033a0d4139482643d83086219834c6905e1e03d07d80012e318670d219034066204,0x151c0a81802e0589608b2822444808f11a264a00142741ac278211a82f436050046478001672683b06a0088859d292,
0x10e41e0371722ec5d0bc2880c8a40610ca010d388a12c2480019a578001968291015c3b45680c18e1a00101030c47076000040c1,0x108458000496119272400206f8083849a294320638c60b61682e85c19417c2f06219a330318d30ce344348cf0c00007aa0c,0x538064524a50fc2400009a94b1643c05c0f41e63ec7c8f7028374581ca060e92d41a03b01039c00058395382920509d0b409e,0x12a05009f1f83ac6a0c517a2104106f24c4808f91e23a4708d91a232000e714c1ee3e4010fb0023d4000f128a,0x942390528e61ca3a8a613b2782ac8c14b14828c22041534530e71543a47413b2782b08c14b152],
[0x14688cd15229450738e69cc396728e49c838e6e0d99b23626c0d41a734c5f0bd9742e65c8b89702de54ca91512a053ca714d29852ca514929051ca313d2784ec9d1392704dc9b1352684cc991312604bc9712d2584ac4308510820c410811001fc3f07d0f81ec3d0790ca190318620c21802f85e0aa150298520a21402784e0961282484808e118220420820c01782e05a0ac1502704c094120230440680c0150280480780a0120200300500800c00800,0x1774ee1dabb4766ec9d7bae74ae91d1ba2742e7dcf39d738e6dccb94726e49be37b6f4dddbb3736e2dc1b5b6a6d2da1b33636c4d81aeb5c6a6d49a8b5069ed35a5b4a692d1da1341680ca994b1f63cc598a31161cc2580b005febf17dafa5f2be17baf65eabc177aee5aeb596aad45a6b4968ad059eb3966acc58eb1962ac4584b05602bd578aed5d2b7560ab9522a353ca754e28650a9ed3d25d4b894928a5049e93926a4c49692924a4748c9051f235,0x65ccb896f2d60640a80f01200bed])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC08 : ¬ FormulaSat cC08.originalFormula :=
  cC08.unsat (by decide +kernel)

def cC09 : Certificate := ((9,8,11,145),
[0x12f1b4005a35800a06900190c4600a19c005e32800b46300140c2002e17c005a2817400582d800a85b00158205900140ae0029030aa002814c004e288009851000209e0002134004a240008c4b001240044211007c3c0d11c00222280040430007882001d0fc00301e800703b000d076001b0387200180dc0032050d40030198005c31000b06200030bc0002168005423,0x156885600057001560054a8d54005429c00a8528013a2b530012e275200144a1002893e004e88d40004b87d3c004e001349900258009449801208f00231140044234007c4680116004321104803f09112001521c00704280050850017906001320c005a40800a07f001e8f0763a1c8387d00088f600381e4005e3b800b47500140e600371c4006638800d86a34060de00,0x18001400fe7e801f6f97e001f417003e026007b3d400f677801e6f17a001e40f003c0160076baddc007601c00ea01801d0e700391c6007037c00dc6d801b0d700349aa006535400d0673302cd300309a2005f33c00bc6680190c66204996006132400be6380178c5003018600602fc00c05e80176005cacd74005c2dc00b85a8015e2b5b0015a295a00164b1002c83600,0x400c10043400f7003a400e50038400dd00364009b0025400910045400ff00399c4de6d359a8ac4c2491c008d80233178d0023025004583a008a44c011187c4801100c8021c1500432160086414010983c280108088020c0d0040e0304004081200],
[0x1314b140960015ad92a462000056a64a1147c0013a9126422000046a0491047c000fa7922,0x1553924108006aa60d86b350200c0a0481c0a9637238003b4b9a4d06701004080336a3800,0x13f1e8f0268d4622d14894421d0c11002896499389c0de5f2d984c05e2d174b25c2c15cac,0x18541150700051040a09a080341c912603c864e26a4888834c0312e0b4b048cc653218cc4,0x1261107c6c340f0c4562510a549e1d291445c1b29a48602a12080349900014ce8720502cbf0ec0a057,0x17a0382963c160a39c3a9d0e6150a05c2c7947800a29b3e9f0f627118a4502d179fd02801b8cc58,0x1184d9e91e002da74140b1341b2549e52288cca62e4900413e040a31c0c9d8f0774d26488010528c26c020a7,0x101043ce8b86c001925126482392538301526c74391da089438001c13c783b9d836190e87034,
0x20808f9e0082bc94429d12081367e428013e81401fc6e2f1a8b458],
[0x193726a4cc9587d0f61e43a8710de1b3a5748df1bdb536a4ca994b01600b5d6b2d55a8b4d692d15a0b3d672cd598b1d622c2582b015e2ba560ab94da99530a5949a92520a1d432854f89752e23446654ca91512a053ca714d29852ca514929051ca313d2784ec9d1392704dc9b1352684cc991312604bc9712d2584ac430850fc1f43e07b0f41e4328640c6188308600be1782a0530a4138250490901102082b05408c1101802a0480780900c01000800,0x66ccd79a331261cc297d2e65c4b796b2ce594b1])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC09 : ¬ FormulaSat cC09.originalFormula :=
  cC09.unsat (by decide +kernel)

def cC10 : Certificate := ((9,8,11,138),
[0x100158ca002918c004830800b85a2c048be002b17400522d800905900150ae00291540050298009853001382051001209e00250309a002412c0046248008849000208e00021140042200007c4300104003c1d0e06c340b0fc001e1e800383b000687200190dc00281a8006033000b06600170386200140bc002a050b40028158004c290009052000309c000212800441f,0x1582bc00ab0eab800ac002a14e0052801469f5200144a10027446a0002782e004e00134990025c009548a580094498011a2349001208f0021c368e00230008a448010c0042208008042800e8850020c007e3e1e8f0761020400223f800d07d00158f600291e400483b800e470371b0d4183a8003c73001a0e2002b1bc005236800906b00198d2002f1a40064311802867,0x1004182a008204c010280801fefd80001fc11003f01a007cbddf4007c02400f602801e8eb003c9e20077bb5e0007703c00ec05801d2e775001d00700398060072801c6df72001c4e10036c46e000379ba006d87db8006d001b0d700351a6006833c00cc6580190c70031400c35fb1000c2608017623600017cbd002e43abc002e800b7002d562b6002d166005688d6400,0x20081801e6006c801aa00688019a006480152004d801160085801ea006b3499cca632e154a64c22001110043e1b1000438420086064010a8480214fb0041e0b08],
[0x1dc47954a40011b011c4e2580046b246918880011a81183f1e0004692458f474000da3914,0x104019b0fc0014a48d469340200c0702828126b44000662848984bc0011b81205f2f0003e,0x1420880046943b1d4e8271189844241009442291407c3c783f800a44834a4cce663280802,0x16247235188b48030169149048ba5c2d968b24a218ec26874321508834120500642c14492,0x1150a05c2c773f80092953e930a60e080341e8a479509a451f180ae5024104c6562791c80,0x130152545c340025070371c9f06c004b9c8e2700d8643a1c0d0612a7344800a696379b8da,0xbd9e8f235178c858331687d2631158792c],
[0x196f2d659cb29631261f43d8790ea1c43786cf8df0be07b6f69e7ba5748df1bdb536a4ca994b01600bb575aea5cab8d6cad7588b0960abc574ac15728650a9c93826f4d49792ea5c49291d2324147c8d51a23345454ca91512a053ca714d29852ca514929051ca313d2784ec9d1392704dc9b1352684cc991312604bc9712d2584ac430850fc1f43e07b0f41e4328640c6188308600be1782a04e094124240440820ac1181802a0480780900c01000800,0xcd99af346624c39852fa5ccb8])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC10 : ¬ FormulaSat cC10.originalFormula :=
  cC10.unsat (by decide +kernel)

def cC11 : Certificate := ((9,8,11,139),
[0x100178c2002b184005c2d160205f00138ba002016c003c2c800a85228038ae00271540040298007851001309e002313c004a240309a002012c003c2480088420511c0040228007843000f882001e0fc003a1e800703d000207600020e400361a0006437000d40030170b05428090cc001c18800342f000605a000b0ac0026148004827000884e0003094000211800401d,0x1002a94e0052801469f5200144a10027442a00027826004e0013499002692e004a801268f4a0012491002244290002391a004722c00890ea3000810ba280088002190a004320c0080001f8f8003d1fc006e3f800fa003c1d8e87238078f600101e400603b8009c7500100e6001e1c4006c351a0cc640a1bc001c36800c06b00138d2002019c003c32800c04e31800c461,0x10780202ff81002000d003f816007e3ec00f97bbe800f804801ec05003d1e60078bbde4007801c00ee01801d8eb003b1d2007339400e671801c0df00381ba006d36400da6b801a8d300351a200678019ac96700198cb0030c42ca003218e006431400c10db1800bf0cb1000c2002f400bb5baf000ba5c80162215c0016cb5002d966005786d68005686564005800154a9,0x801fa007a801da0073801c2006d801aa0055801360043802160075391bcd8693015ca84c21000e871371acd05f2b14c9641002220087c3620008707c010c0a80215090042a060083c161000830440104],
[0x1ca4814c9c0010ae11e482300042a047100760010a411a3d1d8003a8c460f070000ba2916,0x100319392670379b81e0e08840e28a000f5246c359a804010200cda890009d225c2b80042,0x11a0c05426170a0492478400009e943b9d8ea230f894482711078421d098803812491e500,0x1374421d0c854220d04813e97cac340006d2c3f46108828d0010c001d4a9d0e6720c85836,0x132199ecf87a168b12a3115898602a49a505e29098b85012490d86a6933994c6612691474,0x1911b0d4186833190c460261107237068200f296431a02c00973f964a05b29178aa5d2a2411e,0x2fc582781c14084b019165a2891c7c5e2a928845d2a124829047a391a04041848301020a],
[0x19e33b6764eb9d51b235c6a8d2f49e8bc874ee99ceb7c6f6dc9a8b5068ec9992b1c620c3986b0860cc157e2fa5e2b9571ae25bab6d6d2d159eb1952aa4536a3d46a8c50e9ed3d2794e0991312614b896d2c25049e93922a3e2c4584b015f2bc574ae15b2b4564ac1572ac554a694c296528a494828e518a2944286508a094027e4f89e93c2764e89c938116228418821022003f87e0c6188308570a21342604b09411c2202e04c0640900900c01000800,0xd14a254327fcfe9fb3e67acf4])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unsatC11 : ¬ FormulaSat cC11.originalFormula :=
  cC11.unsat (by decide +kernel)

-- v=0,1,2 selects A,B,C; a=0,...,11 selects the retained-case index.
def certificateAt (v : Fin 3) (a : Fin 12) : Certificate :=
  match v.val, a.val with
  | 0, 0 => cA00
  | 0, 1 => cA01
  | 0, 2 => cA02
  | 0, 3 => cA03
  | 0, 4 => cA04
  | 0, 5 => cA05
  | 0, 6 => cA06
  | 0, 7 => cA07
  | 0, 8 => cA08
  | 0, 9 => cA09
  | 0, 10 => cA10
  | 0, 11 => cA11
  | 1, 0 => cB00
  | 1, 1 => cB01
  | 1, 2 => cB02
  | 1, 3 => cB03
  | 1, 4 => cB04
  | 1, 5 => cB05
  | 1, 6 => cB06
  | 1, 7 => cB07
  | 1, 8 => cB08
  | 1, 9 => cB09
  | 1, 10 => cB10
  | 1, 11 => cB11
  | 2, 0 => cC00
  | 2, 1 => cC01
  | 2, 2 => cC02
  | 2, 3 => cC03
  | 2, 4 => cC04
  | 2, 5 => cC05
  | 2, 6 => cC06
  | 2, 7 => cC07
  | 2, 8 => cC08
  | 2, 9 => cC09
  | 2, 10 => cC10
  | 2, 11 => cC11
  | _, _ => cA00

lemma certificateAt_unsat (v : Fin 3) (a : Fin 12) :
    ¬ FormulaSat (certificateAt v a).originalFormula := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  have ha : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 5 ∨ a.val = 6 ∨ a.val = 7 ∨ a.val = 8 ∨ a.val = 9 ∨ a.val = 10 ∨ a.val = 11 := by omega
  rcases hv with hv | hv | hv
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · simpa only [certificateAt, hv, ha] using unsatA00
    · simpa only [certificateAt, hv, ha] using unsatA01
    · simpa only [certificateAt, hv, ha] using unsatA02
    · simpa only [certificateAt, hv, ha] using unsatA03
    · simpa only [certificateAt, hv, ha] using unsatA04
    · simpa only [certificateAt, hv, ha] using unsatA05
    · simpa only [certificateAt, hv, ha] using unsatA06
    · simpa only [certificateAt, hv, ha] using unsatA07
    · simpa only [certificateAt, hv, ha] using unsatA08
    · simpa only [certificateAt, hv, ha] using unsatA09
    · simpa only [certificateAt, hv, ha] using unsatA10
    · simpa only [certificateAt, hv, ha] using unsatA11
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · simpa only [certificateAt, hv, ha] using unsatB00
    · simpa only [certificateAt, hv, ha] using unsatB01
    · simpa only [certificateAt, hv, ha] using unsatB02
    · simpa only [certificateAt, hv, ha] using unsatB03
    · simpa only [certificateAt, hv, ha] using unsatB04
    · simpa only [certificateAt, hv, ha] using unsatB05
    · simpa only [certificateAt, hv, ha] using unsatB06
    · simpa only [certificateAt, hv, ha] using unsatB07
    · simpa only [certificateAt, hv, ha] using unsatB08
    · simpa only [certificateAt, hv, ha] using unsatB09
    · simpa only [certificateAt, hv, ha] using unsatB10
    · simpa only [certificateAt, hv, ha] using unsatB11
  · rcases ha with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
    · simpa only [certificateAt, hv, ha] using unsatC00
    · simpa only [certificateAt, hv, ha] using unsatC01
    · simpa only [certificateAt, hv, ha] using unsatC02
    · simpa only [certificateAt, hv, ha] using unsatC03
    · simpa only [certificateAt, hv, ha] using unsatC04
    · simpa only [certificateAt, hv, ha] using unsatC05
    · simpa only [certificateAt, hv, ha] using unsatC06
    · simpa only [certificateAt, hv, ha] using unsatC07
    · simpa only [certificateAt, hv, ha] using unsatC08
    · simpa only [certificateAt, hv, ha] using unsatC09
    · simpa only [certificateAt, hv, ha] using unsatC10
    · simpa only [certificateAt, hv, ha] using unsatC11

end R2CleanKernel


lemma before_AC_readers_agree {k : Nat}
    (pA pC : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (value : Nat → Fin 256 → Bool)
    (ha : ∀ j, a j < 8 + j.val) (hb : ∀ j, b j < 8 + j.val)
    (hraw : ∀ (i : Fin 8) (row : Fin 256), value i.val row = row.val.testBit i.val)
    (heval : ∀ row j, value (8 + j.val) row =
      boolGate (op j) (value (a j) row) (value (b j) row))
    (hsoleA : ∀ j, j ≠ pA → a j ≠ 0 ∧ b j ≠ 0)
    (hsoleC : ∀ j, j ≠ pC → a j ≠ 2 ∧ b j ≠ 2)
    (wire : Nat) (hcomputed : 8 ≤ wire)
    (hbeforeA : wire < 8 + pA.val) (hbeforeC : wire < 8 + pC.val) :
    value wire 37 = value wire 32 := by
  have hbitsA : ∀ i : Fin 8, i.val ≠ 0 →
      (37 : Nat).testBit i.val = (36 : Nat).testBit i.val := by decide +kernel
  have hbitsC : ∀ i : Fin 8, i.val ≠ 2 →
      (36 : Nat).testBit i.val = (32 : Nat).testBit i.val := by decide +kernel
  have hrawA : ∀ i, i < 8 → i ≠ 0 → value i 37 = value i 36 := by
    intro i hi hne
    rw [hraw ⟨i, hi⟩ 37, hraw ⟨i, hi⟩ 36]
    exact hbitsA ⟨i, hi⟩ hne
  have hrawC : ∀ i, i < 8 → i ≠ 2 → value i 36 = value i 32 := by
    intro i hi hne
    rw [hraw ⟨i, hi⟩ 36, hraw ⟨i, hi⟩ 32]
    exact hbitsC ⟨i, hi⟩ hne
  have hwire : wire < 8 + k := by have := pA.isLt; omega
  calc
    value wire 37 = value wire 36 :=
      sole_reader_agreement pA a b op (fun i => value i 37) (fun i => value i 36)
        ha hb hrawA hsoleA (heval 37) (heval 36) wire hwire (by omega)
        (fun h => by omega)
    _ = value wire 32 :=
      sole_reader_agreement pC a b op (fun i => value i 36) (fun i => value i 32)
        ha hb hrawC hsoleC (heval 36) (heval 32) wire hwire (by omega)
        (fun h => by omega)

lemma causal_AC_frontiers_disjoint {k : Nat}
    (pA pC : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (value : Nat → Fin 256 → Bool)
    (ha : ∀ j, a j < 8 + j.val) (hb : ∀ j, b j < 8 + j.val)
    (hraw : ∀ (i : Fin 8) (row : Fin 256), value i.val row = row.val.testBit i.val)
    (heval : ∀ row j, value (8 + j.val) row =
      boolGate (op j) (value (a j) row) (value (b j) row))
    (hsoleA : ∀ j, j ≠ pA → a j ≠ 0 ∧ b j ≠ 0)
    (hsoleC : ∀ j, j ≠ pC → a j ≠ 2 ∧ b j ≠ 2)
    (S T : Finset Nat) (negatives : Finset (Fin 256))
    (hcomputed : ∀ wire ∈ S, 8 ≤ wire)
    (hbeforeA : ∀ wire ∈ S, wire < 8 + pA.val)
    (hbeforeC : ∀ wire ∈ T, wire < 8 + pC.val)
    (hdirty : ∀ wire ∈ S, ∃ row ∈ negatives, value wire row = true)
    (hA : ∀ wire ∈ S, ∀ row ∈ negatives,
      value wire row = true → row.val = 25 ∨ row.val = 37)
    (hC : ∀ wire ∈ T, ∀ row ∈ negatives,
      value wire row = true → row.val = 37 ∨ row.val = 76)
    (hzero : ∀ wire ∈ S, value wire 32 = false) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro wire hs ht
  obtain ⟨row, hrow, hv⟩ := hdirty wire hs
  have haRow := hA wire hs row hrow hv
  have hcRow := hC wire ht row hrow hv
  have hr : row = (37 : Fin 256) := Fin.ext (by change row.val = 37; omega)
  subst row
  have hp := before_AC_readers_agree pA pC a b op value ha hb hraw heval hsoleA hsoleC
    wire (hcomputed wire hs) (hbeforeA wire hs) (hbeforeC wire ht)
  rw [hp, hzero wire hs] at hv
  cases hv

/-- Delete the A and C coordinates from an eight-bit mask. -/
def bcCompact (x : Nat) : Nat :=
  ((x >>> 3) <<< 1) ||| ((x >>> 1) &&& 1)

/-- Insert zero A and C coordinates into a six-bit mask. -/
def bcExpand (y : Nat) : Nat :=
  ((y >>> 1) <<< 3) ||| ((y &&& 1) <<< 1)

lemma bc_compact_or (x y : Nat) :
    bcCompact (x ||| y) = bcCompact x ||| bcCompact y := by
  simp only [bcCompact, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_or_distrib, Nat.and_or_distrib_right]
  ac_rfl

lemma bc_expand_or (x y : Nat) :
    bcExpand (x ||| y) = bcExpand x ||| bcExpand y := by
  simp only [bcExpand, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_or_distrib, Nat.and_or_distrib_right]
  ac_rfl

lemma bc_compact_bounds : ∀ x : Fin 256, bcCompact x.val < 64 := by
  decide +kernel

lemma bc_expand_bounds : ∀ y : Fin 64, bcExpand y.val < 256 := by
  decide +kernel

lemma bc_expand_avoids_ac : ∀ y : Fin 64, bcExpand y.val &&& 5 = 0 := by
  decide +kernel

lemma bc_expand_compact : ∀ x : Fin 256,
    x.val &&& 5 = 0 → bcExpand (bcCompact x.val) = x.val := by
  decide +kernel

lemma bc_compact_expand : ∀ y : Fin 64,
    bcCompact (bcExpand y.val) = y.val := by
  decide +kernel

lemma bc_compact_arithmetic : ∀ x : Fin 256,
    bcCompact x.val = (x.val >>> 3) * 2 + ((x.val >>> 1) &&& 1) := by
  decide +kernel

lemma bc_expand_arithmetic : ∀ y : Fin 64,
    bcExpand y.val = (y.val >>> 1) * 8 + (y.val &&& 1) * 2 := by
  decide +kernel

lemma bc_compact_singletons : ∀ i : Fin 8,
    bcCompact (2 ^ i.val) = [0, 1, 0, 2, 4, 8, 16, 32].getD i.val 0 := by
  decide +kernel

lemma bc_expand_singletons : ∀ i : Fin 6,
    bcExpand (2 ^ i.val) = [2, 8, 16, 32, 64, 128].getD i.val 0 := by
  decide +kernel

lemma bc_compact_injective (x y : Fin 256)
    (hx : x.val &&& 5 = 0) (hy : y.val &&& 5 = 0)
    (heq : bcCompact x.val = bcCompact y.val) : x = y := by
  apply Fin.ext
  calc
    x.val = bcExpand (bcCompact x.val) := (bc_expand_compact x hx).symm
    _ = bcExpand (bcCompact y.val) := congrArg bcExpand heq
    _ = y.val := bc_expand_compact y hy

def bcTraceMasks (N : Nat) (mask : Nat → Nat) : Finset Nat :=
  (Finset.range N).image mask \ bcUnionAtoms

lemma bc_trace_mask_mem (N : Nat) (mask : Nat → Nat)
    (i : Nat) (hi : i < N) :
    mask i ∈ bcTraceMasks N mask ∪ bcUnionAtoms := by
  by_cases ha : mask i ∈ bcUnionAtoms
  · exact Finset.mem_union.mpr (Or.inr ha)
  · apply Finset.mem_union.mpr
    left
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩, ha⟩

lemma bc_union_closed_of_causal_trace
    (N : Nat) (mask : Nat → Nat)
    (hcausal : ∀ i < N, mask i ∉ bcUnionAtoms →
      ∃ a b, a < i ∧ b < i ∧ mask a ||| mask b = mask i) :
    bcUnionClosed (bcTraceMasks N mask) := by
  intro m hm
  have hmem := Finset.mem_sdiff.mp hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_image.mp hmem.1
  have hex : ∃ i : Nat, i < N ∧ mask i = m :=
    ⟨i, Finset.mem_range.mp hi, hmi⟩
  let first := Nat.find hex
  have hfirst : first < N ∧ mask first = m := Nat.find_spec hex
  have hnonatom : mask first ∉ bcUnionAtoms := by
    rw [hfirst.2]
    exact hmem.2
  obtain ⟨a, b, ha, hb, hab⟩ := hcausal first hfirst.1 hnonatom
  have haN : a < N := Nat.lt_trans ha hfirst.1
  have hbN : b < N := Nat.lt_trans hb hfirst.1
  have hane : mask a ≠ m := by
    intro heq
    exact Nat.find_min hex ha ⟨haN, heq⟩
  have hbne : mask b ≠ m := by
    intro heq
    exact Nat.find_min hex hb ⟨hbN, heq⟩
  have hor : mask a ||| mask b = m := hab.trans hfirst.2
  have hal : mask a ≤ m := by
    rw [← hor]
    exact Nat.left_le_or
  have hbl : mask b ≤ m := by
    rw [← hor]
    exact Nat.right_le_or
  right
  refine ⟨mask a, bc_trace_mask_mem N mask a haN,
    mask b, bc_trace_mask_mem N mask b hbN, ?_, ?_, hor⟩
  · omega
  · omega


lemma bc_union_closed_of_raw_causal_trace
    (N raw : Nat) (mask : Nat → Nat)
    (hraw : ∀ i < raw, mask i ∈ bcUnionAtoms)
    (hcomputed : ∀ i < N, raw ≤ i → mask i ∉ bcUnionAtoms →
      ∃ a b, a < i ∧ b < i ∧ mask a ||| mask b = mask i) :
    bcUnionClosed (bcTraceMasks N mask) := by
  apply bc_union_closed_of_causal_trace
  intro i hi hnonatom
  by_cases hiraw : i < raw
  · exact (hnonatom (hraw i hiraw)).elim
  · exact hcomputed i hi (Nat.le_of_not_gt hiraw) hnonatom

lemma bc_trace_masks_bound (N bound : Nat) (mask : Nat → Nat)
    (hbound : ∀ i < N, mask i < bound) :
    ∀ m ∈ bcTraceMasks N mask, m < bound := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hm).1
  exact hbound i (Finset.mem_range.mp hi)

lemma bc_required_family_subset_trace (ports : List Nat)
    (N : Nat) (mask : Nat → Nat)
    (hports : ∀ m ∈ ports, ∃ i < N, mask i = m) :
    bcRequiredFamily ports ⊆ bcTraceMasks N mask := by
  intro m hm
  have hmem := Finset.mem_sdiff.mp hm
  obtain ⟨i, hi, rfl⟩ := hports m (List.mem_toFinset.mp hmem.1)
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩, hmem.2⟩

lemma bc_all_cover_causal_production
    (ports : List Nat) (hp : ports ∈ bcAllCovers)
    (N : Nat) (mask : Nat → Nat)
    (hcausal : ∀ i < N, mask i ∉ bcUnionAtoms →
      ∃ a b, a < i ∧ b < i ∧ mask a ||| mask b = mask i)
    (hports : ∀ m ∈ ports, ∃ i < N, mask i = m)
    (hcard : (bcTraceMasks N mask).card ≤ 5)
    (hbound : ∀ i < N, mask i < 256) :
    ports ∈ bcSurvivorCovers := by
  exact bc_all_cover_closed_production ports hp (bcTraceMasks N mask)
    (bc_required_family_subset_trace ports N mask hports) hcard
    (bc_trace_masks_bound N 256 mask hbound)
    (bc_union_closed_of_causal_trace N mask hcausal)

def bcBroadRawA : List Nat := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def bcBroadRawC : List Nat := [36, 37, 38, 39, 44, 45, 46, 47, 52, 53, 54, 55, 60, 61, 62, 63]
def bcEGTriples : List (Nat × Nat × Nat) :=
  [(5, 2, 24), (11, 2, 12), (15, 2, 11), (15, 2, 12), (15, 2, 24)]

def bcBroadCoverPorts (ta tc : Nat) (tr : Nat × Nat × Nat) : List Nat :=
  let h := bcHRectangles.getD tr.1 (0, 0)
  let c₁ := bcCleanNonemptyRectangles.getD tr.2.1 (0, 0)
  let c₂ := bcCleanNonemptyRectangles.getD tr.2.2 (0, 0)
  [ta, tc, 2 * h.1, 2 * h.2, c₁.1, c₁.2, c₂.1, c₂.2]

def bcBroadIndexedPorts (a c : Fin 16) (t : Fin 5) : List Nat :=
  bcBroadCoverPorts (bcBroadRawA.getD a.val 0) (bcBroadRawC.getD c.val 0)
    (bcEGTriples.getD t.val (0, 0, 0))

def bcBroadFourCovers : List (List Nat) :=
  [52, 53, 54, 55, 60, 61, 62, 63].map (fun W => [W, W, 22, 40, 1, 10, 4, 16])

def bcBroadCaseSummary (a c : Fin 16) (t : Fin 5) : Prop :=
  let ports := bcBroadIndexedPorts a c t
  let R := bcRequiredFamily ports
  (R.card = 4 ∧ ports ∈ bcBroadFourCovers) ∨
  (R.card = 5 ∧ bcUnionCheck (bcRequiredList ports) = false) ∨ 6 ≤ R.card

lemma bc_broad_raw_a_complete : ∀ a : Fin 64,
    a.val &&& 48 = 48 → a.val ∈ bcBroadRawA := by
  decide +kernel

lemma bc_broad_raw_c_complete : ∀ c : Fin 64,
    c.val &&& 36 = 36 → c.val ∈ bcBroadRawC := by
  decide +kernel

lemma bc_broad_cofactor_raw_independent (ta tc : Nat) (tr : Nat × Nat × Nat) (row : Nat) :
    bcCofactorOutput (bcBroadCoverPorts ta tc tr) row =
      bcCofactorOutput (bcBroadCoverPorts 0 0 tr) row := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma bc_eg_triples_complete : ∀ tr ∈ bcCoverTriples,
    bcCofactorOutput (bcBroadCoverPorts 0 0 tr) 20 = true → tr ∈ bcEGTriples := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_0 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 0 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_1 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 1 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_2 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 2 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_3 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 3 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_4 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 4 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_5 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 5 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_6 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 6 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_7 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 7 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_8 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 8 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_9 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 9 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_10 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 10 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_11 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 11 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_12 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 12 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_13 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 13 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_14 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 14 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_case_summary_15 : ∀ (c : Fin 16) (t : Fin 5),
    bcBroadCaseSummary 15 c t := by
  unfold bcBroadCaseSummary
  decide +kernel

lemma bc_broad_case_summary (a c : Fin 16) (t : Fin 5) :
    bcBroadCaseSummary a c t := by
  fin_cases a
  · exact bc_broad_case_summary_0 c t
  · exact bc_broad_case_summary_1 c t
  · exact bc_broad_case_summary_2 c t
  · exact bc_broad_case_summary_3 c t
  · exact bc_broad_case_summary_4 c t
  · exact bc_broad_case_summary_5 c t
  · exact bc_broad_case_summary_6 c t
  · exact bc_broad_case_summary_7 c t
  · exact bc_broad_case_summary_8 c t
  · exact bc_broad_case_summary_9 c t
  · exact bc_broad_case_summary_10 c t
  · exact bc_broad_case_summary_11 c t
  · exact bc_broad_case_summary_12 c t
  · exact bc_broad_case_summary_13 c t
  · exact bc_broad_case_summary_14 c t
  · exact bc_broad_case_summary_15 c t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
lemma bc_broad_four_summary : ∀ ports ∈ bcBroadFourCovers,
    bcUnionCheck (bcRequiredList ports) = false ∧
    (ports ∈ bcMiddleCovers ∨ bcNoSmallUnionExtension (bcRequiredList ports) = true) ∧
    ports.all (fun m => decide (m < 64)) = true := by
  decide +kernel

set_option maxHeartbeats 5000000 in
lemma bc_broad_indexed_classification (a c : Fin 16) (t : Fin 5)
    (S : Finset Nat)
    (hsub : bcRequiredFamily (bcBroadIndexedPorts a c t) ⊆ S)
    (hcard : S.card ≤ 5) (hclosed : bcUnionClosed S) :
    bcBroadIndexedPorts a c t ∈ bcMiddleCovers := by
  have hsummary := bc_broad_case_summary a c t
  change (_ ∧ _) ∨ (_ ∧ _) ∨ _ at hsummary
  have hle := Finset.card_le_card hsub
  rcases hsummary with ⟨hfour, hshape⟩ | ⟨hfive, hnot⟩ | hsix
  · obtain ⟨hnot, hcases, hbound⟩ := bc_broad_four_summary _ hshape
    have hnclosed : ¬ bcUnionClosed (bcRequiredFamily (bcBroadIndexedPorts a c t)) := by
      intro hc
      have ht := (bc_union_check_spec (bcRequiredList (bcBroadIndexedPorts a c t))).mpr
        (by simpa only [bc_required_list_eq] using hc)
      rw [hnot] at ht
      exact Bool.noConfusion ht
    have hnonempty : (bcRequiredFamily (bcBroadIndexedPorts a c t)).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨extra, _, heq⟩ := bc_equal_one_extra _ _ hsub hnonempty (by omega)
    rw [heq] at hclosed
    have hextra : extra < 64 := by
      apply bc_extra_below_64 _ extra ?_ hnclosed hclosed
      intro m hm
      have hmports : m ∈ bcBroadIndexedPorts a c t :=
        List.mem_toFinset.mp (Finset.mem_sdiff.mp hm).1
      exact of_decide_eq_true (List.all_eq_true.mp hbound m hmports)
    rcases hcases with hmiddle | hreject
    · exact hmiddle
    · have hr := (bc_no_small_union_extension_spec _).mp hreject ⟨extra, hextra⟩
      have hc := (bc_union_check_spec
        (extra :: bcRequiredList (bcBroadIndexedPorts a c t))).mpr
        (by simpa only [List.toFinset_cons, bc_required_list_eq] using hclosed)
      change bcUnionCheck (extra :: bcRequiredList (bcBroadIndexedPorts a c t)) = false at hr
      rw [hr] at hc
      exact Bool.noConfusion hc
  · have heq : S = bcRequiredFamily (bcBroadIndexedPorts a c t) :=
      (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    rw [heq] at hclosed
    have hc := (bc_union_check_spec (bcRequiredList (bcBroadIndexedPorts a c t))).mpr
      (by simpa only [bc_required_list_eq] using hclosed)
    rw [hnot] at hc
    exact Bool.noConfusion hc
  · omega

lemma bc_broad_cover_classification (ta tc : Fin 64) (tr : Nat × Nat × Nat)
    (hta : ta.val &&& 48 = 48) (htc : tc.val &&& 36 = 36)
    (htr : tr ∈ bcCoverTriples)
    (S : Finset Nat) (hsub : bcRequiredFamily (bcBroadCoverPorts ta.val tc.val tr) ⊆ S)
    (hcard : S.card ≤ 5) (hclosed : bcUnionClosed S)
    (hEG : bcCofactorOutput (bcBroadCoverPorts ta.val tc.val tr) 20 = true) :
    bcBroadCoverPorts ta.val tc.val tr ∈ bcMiddleCovers := by
  have htrEG : tr ∈ bcEGTriples := by
    apply bc_eg_triples_complete tr htr
    rw [← bc_broad_cofactor_raw_independent ta.val tc.val tr 20]
    exact hEG
  obtain ⟨a, ha⟩ := bc_index_of_mem (n := 16) (by rfl) 0 ta.val
    (bc_broad_raw_a_complete ta hta)
  obtain ⟨c, hc⟩ := bc_index_of_mem (n := 16) (by rfl) 0 tc.val
    (bc_broad_raw_c_complete tc htc)
  obtain ⟨t, ht⟩ := bc_index_of_mem (n := 5) (by rfl) (0, 0, 0) tr htrEG
  have heq : bcBroadIndexedPorts a c t = bcBroadCoverPorts ta.val tc.val tr := by
    unfold bcBroadIndexedPorts
    rw [ha, hc, ht]
  have hresult := bc_broad_indexed_classification a c t S
    (by simpa only [heq] using hsub) hcard hclosed
  simpa only [heq] using hresult

lemma bc_broad_geometric_closed_cofactor
    (ta tc : Fin 64) (hL hR : Fin 32) (a b c d : Fin 64)
    (hta : ta.val &&& 48 = 48) (htc : tc.val &&& 36 = 36)
    (hh : bcHRectValid hL hR)
    (hab : bcCleanRectValid a b) (hcd : bcCleanRectValid c d)
    (hcover : bcResidualEdges (2 * hL.val) (2 * hR.val) |||
      bcResidualEdges a.val b.val ||| bcResidualEdges c.val d.val = 127)
    (S : Finset Nat)
    (hsub : bcRequiredFamily [ta.val, tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] ⊆ S)
    (hcard : S.card ≤ 5) (hclosed : bcUnionClosed S)
    (hEG : bcCofactorOutput [ta.val, tc.val, 2 * hL.val, 2 * hR.val,
      a.val, b.val, c.val, d.val] 20 = true) :
    [ta.val, tc.val, 2 * hL.val, 2 * hR.val, a.val, b.val, c.val, d.val] ∈ bcMiddleCovers ∨
    [ta.val, tc.val, 2 * hL.val, 2 * hR.val, c.val, d.val, a.val, b.val] ∈ bcMiddleCovers := by
  obtain ⟨i, hi⟩ := bc_index_of_mem (n := 16) (by rfl) (0, 0) (hL.val, hR.val)
    (bc_h_rectangle_complete hL hR hh)
  obtain ⟨j, hj⟩ := bc_index_of_mem (n := 89) (by rfl) (0, 0) (a.val, b.val)
    (bc_clean_rectangle_complete a b hab)
  obtain ⟨k, hk⟩ := bc_index_of_mem (n := 89) (by rfl) (0, 0) (c.val, d.val)
    (bc_clean_rectangle_complete c d hcd)
  change bcHAt i = (hL.val, hR.val) at hi
  change bcCleanAt j = (a.val, b.val) at hj
  change bcCleanAt k = (c.val, d.val) at hk
  have hidx : bcHEdges i ||| bcCleanEdges j ||| bcCleanEdges k = 127 := by
    rw [← bc_h_edges_correct i, ← bc_clean_edges_correct j, ← bc_clean_edges_correct k,
      hi, hj, hk]
    exact hcover
  obtain ⟨hjne, hkne⟩ := bc_covering_clean_nonempty i j k hidx
  obtain ⟨j', hj'⟩ := bc_nonempty_clean_index j hjne
  obtain ⟨k', hk'⟩ := bc_nonempty_clean_index k hkne
  have hnj : bcNonemptyAt j' = (a.val, b.val) := hj'.trans hj
  have hnk : bcNonemptyAt k' = (c.val, d.val) := hk'.trans hk
  have hncover : bcHEdges i ||| bcNonemptyEdges j' ||| bcNonemptyEdges k' = 127 := by
    rw [← bc_h_edges_correct i, ← bc_nonempty_edges_correct j',
      ← bc_nonempty_edges_correct k', hi, hnj, hnk]
    exact hcover
  rcases bc_covering_triples_complete i j' k' hncover with ht | ht
  · have hports : bcBroadCoverPorts ta.val tc.val (i.val, j'.val, k'.val) =
        [ta.val, tc.val, 2 * hL.val, 2 * hR.val, a.val, b.val, c.val, d.val] := by
      change [ta.val, tc.val, 2 * (bcHAt i).1, 2 * (bcHAt i).2,
        (bcNonemptyAt j').1, (bcNonemptyAt j').2,
        (bcNonemptyAt k').1, (bcNonemptyAt k').2] = _
      simp only [hi, hnj, hnk]
    left
    have hresult := bc_broad_cover_classification ta tc (i.val, j'.val, k'.val)
      hta htc ht S (by simpa only [hports] using hsub) hcard hclosed
      (by simpa only [hports] using hEG)
    simpa only [hports] using hresult
  · have hports : bcBroadCoverPorts ta.val tc.val (i.val, k'.val, j'.val) =
        [ta.val, tc.val, 2 * hL.val, 2 * hR.val, c.val, d.val, a.val, b.val] := by
      change [ta.val, tc.val, 2 * (bcHAt i).1, 2 * (bcHAt i).2,
        (bcNonemptyAt k').1, (bcNonemptyAt k').2,
        (bcNonemptyAt j').1, (bcNonemptyAt j').2] = _
      simp only [hi, hnj, hnk]
    have hsub' : bcRequiredFamily [ta.val, tc.val, 2 * hL.val, 2 * hR.val,
        c.val, d.val, a.val, b.val] ⊆ S := by
      rw [← bc_required_family_clean_swap]
      exact hsub
    have hEG' : bcCofactorOutput [ta.val, tc.val, 2 * hL.val, 2 * hR.val,
        c.val, d.val, a.val, b.val] 20 = true := by
      rw [← bc_cofactor_clean_swap]
      exact hEG
    right
    have hresult := bc_broad_cover_classification ta tc (i.val, k'.val, j'.val)
      hta htc ht S (by simpa only [hports] using hsub') hcard hclosed
      (by simpa only [hports] using hEG')
    simpa only [hports] using hresult

namespace CnfTransport

abbrev Literal := Nat × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause
abbrev Valuation := Nat → Bool

def ClauseHolds (w : Valuation) (c : Clause) : Prop :=
  ∃ literal ∈ c, w literal.1 = literal.2

def CNFHolds (w : Valuation) (f : CNF) : Prop :=
  ∀ clause ∈ f, ClauseHolds w clause

lemma clause_nil (w : Valuation) : ¬ ClauseHolds w [] := by
  simp [ClauseHolds]

lemma clause_cons (w : Valuation) (literal : Literal) (rest : Clause) :
    ClauseHolds w (literal :: rest) ↔
      w literal.1 = literal.2 ∨ ClauseHolds w rest := by
  constructor
  · rintro ⟨item, hi, hv⟩
    rcases List.mem_cons.mp hi with hi | hi
    · subst item; exact Or.inl hv
    · exact Or.inr ⟨item, hi, hv⟩
  · rintro (hv | ⟨item, hi, hv⟩)
    · exact ⟨literal, List.mem_cons_self, hv⟩
    · exact ⟨item, List.mem_cons_of_mem _ hi, hv⟩

-- Tags: free input, constant, copy, AND, list OR, pref equality.
-- The remaining product fields are value, left, right, optional pref, sources.
abbrev Definition := Fin 6 × Bool × Nat × Nat × Option Nat × List Nat

def inputs (d : Definition) : List Nat :=
  match d with
  | (tag, _, a, b, pref, sources) =>
    match tag.val with
    | 2 => [a]
    | 3 => [a, b]
    | 4 => sources
    | 5 => a :: b :: pref.toList
    | _ => []

def evaluate (d : Definition) (w : Valuation) : Bool :=
  match d with
  | (tag, value, a, b, pref, sources) =>
    match tag.val with
    | 2 => w a
    | 3 => w a && w b
    | 4 => sources.any w
    | 5 => (pref.map w).getD true && (w a == w b)
    | _ => value

def andClauses (out a b : Nat) : CNF :=
  [[(out, false), (a, true)], [(out, false), (b, true)],
    [(out, true), (a, false), (b, false)]]

def orClauses (out : Nat) (sources : List Nat) : CNF :=
  sources.map (fun a => [(a, false), (out, true)]) ++
    [[(out, false)] ++ sources.map (fun a => (a, true))]

def copyClauses (out a : Nat) : CNF :=
  [[(out, false), (a, true)], [(out, true), (a, false)]]

def prefixClauses (out a b : Nat) (pref : Option Nat) : CNF :=
  (pref.toList.map (fun p => [(out, false), (p, true)])) ++
  [[(out, false), (a, false), (b, true)],
   [(out, false), (a, true), (b, false)],
   pref.toList.map (fun p => (p, false)) ++ [(a, false), (b, false), (out, true)],
   pref.toList.map (fun p => (p, false)) ++ [(a, true), (b, true), (out, true)]]

def definitionClauses (out : Nat) (d : Definition) : CNF :=
  match d with
  | (tag, value, a, b, pref, sources) =>
    match tag.val with
    | 0 => []
    | 1 => [[(out, value)]]
    | 2 => copyClauses out a
    | 3 => andClauses out a b
    | 4 => orClauses out sources
    | 5 => prefixClauses out a b pref
    | _ => []

lemma andClauses_holds (w : Valuation) (out a b : Nat)
    (h : w out = (w a && w b)) : CNFHolds w (andClauses out a b) := by
  cases ha : w a <;> cases hb : w b <;>
    simp_all [CNFHolds, clause_cons, clause_nil, andClauses]

lemma copyClauses_holds (w : Valuation) (out a : Nat)
    (h : w out = w a) : CNFHolds w (copyClauses out a) := by
  cases ha : w a <;> simp_all [CNFHolds, clause_cons, clause_nil, copyClauses]

lemma orClauses_holds (w : Valuation) (out : Nat) (sources : List Nat)
    (h : w out = sources.any w) : CNFHolds w (orClauses out sources) := by
  intro clause hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    cases hva : w a with
    | false => exact ⟨(a, false), by simp, hva⟩
    | true =>
      have hout : w out = true := h.trans (List.any_eq_true.mpr ⟨a, ha, hva⟩)
      exact ⟨(out, true), by simp, hout⟩
  · have heq := List.mem_singleton.mp hc
    subst clause
    cases hout : w out with
    | false => exact ⟨(out, false), by simp, hout⟩
    | true =>
      obtain ⟨a, ha, hva⟩ := List.any_eq_true.mp (h.symm.trans hout)
      refine ⟨(a, true), ?_, hva⟩
      simp only [List.singleton_append, List.mem_cons, List.mem_map, Prod.mk.injEq,
        and_true]
      exact Or.inr ⟨a, ha, rfl⟩

lemma prefixClauses_holds (w : Valuation) (out a b : Nat) (pref : Option Nat)
    (h : w out = ((pref.map w).getD true && (w a == w b))) :
    CNFHolds w (prefixClauses out a b pref) := by
  cases pref with
  | none =>
    cases ha : w a <;> cases hb : w b <;>
      simp_all [CNFHolds, clause_cons, clause_nil, prefixClauses]
  | some p =>
    cases hp : w p <;> cases ha : w a <;> cases hb : w b <;>
      simp_all [CNFHolds, clause_cons, clause_nil, prefixClauses]

lemma definitionClauses_holds (w : Valuation) (out : Nat) (d : Definition)
    (h : w out = evaluate d w) : CNFHolds w (definitionClauses out d) := by
  rcases d with ⟨tag, value, a, b, pref, sources⟩
  fin_cases tag
  · simp [definitionClauses, CNFHolds]
  · simpa [definitionClauses, CNFHolds, clause_cons, clause_nil, evaluate] using h
  · exact copyClauses_holds w out a h
  · exact andClauses_holds w out a b h
  · exact orClauses_holds w out sources h
  · exact prefixClauses_holds w out a b pref h

lemma evaluate_congr (d : Definition) (w z : Valuation)
    (h : ∀ i ∈ inputs d, w i = z i) : evaluate d w = evaluate d z := by
  have hlist : ∀ sources : List Nat, (∀ i ∈ sources, w i = z i) →
      sources.any w = sources.any z := by
    intro sources
    induction sources with
    | nil => intro _; rfl
    | cons a sources ih =>
      intro hs
      simp only [List.any_cons]
      rw [hs a (by simp), ih (fun i hi => hs i (by simp [hi]))]
  rcases d with ⟨tag, value, a, b, pref, sources⟩
  fin_cases tag
  · rfl
  · rfl
  · exact h a (by simp [inputs])
  · simp only [evaluate]
    rw [h a (by simp [inputs]), h b (by simp [inputs])]
  · exact hlist sources (by simpa [inputs] using h)
  · cases pref with
    | none =>
      simp only [evaluate, Option.map_none, Option.getD_none]
      rw [h a (by simp [inputs]), h b (by simp [inputs])]
    | some p =>
      simp only [evaluate, Option.map_some, Option.getD_some]
      rw [h a (by simp [inputs]), h b (by simp [inputs]), h p (by simp [inputs])]

def run (start : Nat) (w : Valuation) : List Definition → Valuation
  | [] => w
  | d :: rest => run (start + 1) (Function.update w start (evaluate d w)) rest

def Bounded (start : Nat) : List Definition → Prop
  | [] => True
  | d :: rest => (∀ i ∈ inputs d, i < start) ∧ Bounded (start + 1) rest

def Realizes (w : Valuation) (start : Nat) : List Definition → Prop
  | [] => True
  | d :: rest => w start = evaluate d w ∧ Realizes w (start + 1) rest

def compiled (start : Nat) : List Definition → CNF
  | [] => []
  | d :: rest => definitionClauses start d ++ compiled (start + 1) rest

lemma run_preserves_before (defs : List Definition) (start : Nat) (w : Valuation) :
    ∀ i, i < start → run start w defs i = w i := by
  induction defs generalizing start w with
  | nil => intro i hi; rfl
  | cons d rest ih =>
    intro i hi
    change run (start + 1) (Function.update w start (evaluate d w)) rest i = w i
    rw [ih (start + 1) _ i (by omega)]
    simp [Function.update, Nat.ne_of_lt hi]

lemma run_realizes (defs : List Definition) (start : Nat) (w : Valuation)
    (h : Bounded start defs) : Realizes (run start w defs) start defs := by
  induction defs generalizing start w with
  | nil => trivial
  | cons d rest ih =>
    obtain ⟨hhead, hrest⟩ := h
    constructor
    · have hprior : ∀ i ∈ inputs d, run start w (d :: rest) i = w i := by
        intro i hi
        exact run_preserves_before (d :: rest) start w i (hhead i hi)
      have hval : run start w (d :: rest) start = evaluate d w := by
        change run (start + 1) (Function.update w start (evaluate d w)) rest start = _
        rw [run_preserves_before rest (start + 1) _ start (by omega)]
        simp
      exact hval.trans (evaluate_congr d _ _ hprior).symm
    · exact ih (start + 1) (Function.update w start (evaluate d w)) hrest

lemma compiled_holds_of_realizes (defs : List Definition) (start : Nat)
    (w : Valuation) (h : Realizes w start defs) : CNFHolds w (compiled start defs) := by
  induction defs generalizing start with
  | nil => simp [compiled, CNFHolds]
  | cons d rest ih =>
    obtain ⟨hhead, hrest⟩ := h
    intro clause hc
    rcases List.mem_append.mp hc with hc | hc
    · exact definitionClauses_holds w start d hhead clause hc
    · exact ih (start + 1) hrest clause hc

lemma acyclic_definitions_extend (defs : List Definition) (start : Nat)
    (w : Valuation) (h : Bounded start defs) :
    ∃ z : Valuation, (∀ i, i < start → z i = w i) ∧
      Realizes z start defs ∧ CNFHolds z (compiled start defs) := by
  refine ⟨run start w defs, run_preserves_before defs start w, ?_, ?_⟩
  · exact run_realizes defs start w h
  · exact compiled_holds_of_realizes defs start _ (run_realizes defs start w h)

lemma boundaryClauses_holds (w : Valuation) (a b : Nat) (target : Bool)
    (h : (w a || w b) = target) :
    CNFHolds w (if target then [[(a, true), (b, true)]] else
      [[(a, false)], [(b, false)]]) := by
  cases ha : w a <;> cases hb : w b <;> cases target <;>
    simp_all [CNFHolds, clause_cons, clause_nil]

lemma guardedEquality_holds (w : Valuation) (guard a b : Nat)
    (h : w guard = true → w a = w b) :
    CNFHolds w [[(guard, false), (a, false), (b, true)],
      [(guard, false), (a, true), (b, false)]] := by
  cases hg : w guard <;> cases ha : w a <;> cases hb : w b <;>
    simp_all [CNFHolds, clause_cons, clause_nil]

-- The remaining clauses state semantic side conditions, rather than defining wires.
lemma mappedClause_holds_iff (w : Valuation) (sources : List Nat) (sign : Bool) :
    ClauseHolds w (sources.map (fun i => (i, sign))) ↔
      ∃ i ∈ sources, w i = sign := by
  constructor
  · rintro ⟨literal, hl, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    exact ⟨i, hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨(i, sign), List.mem_map.mpr ⟨i, hi, rfl⟩, hv⟩

lemma witnessClause_holds (w : Valuation) (sources : List Nat)
    (h : ∃ i ∈ sources, w i = true) :
    ClauseHolds w (sources.map (fun i => (i, true))) :=
  (mappedClause_holds_iff w sources true).mpr h

lemma unitClauses_holds (w : Valuation) (sources : List Nat) (sign : Bool)
    (h : ∀ i ∈ sources, w i = sign) :
    CNFHolds w (sources.map (fun i => [(i, sign)])) := by
  intro clause hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact ⟨(i, sign), by simp, h i hi⟩

lemma guardedConstant_holds (w : Valuation) (guard a : Nat) (value : Bool)
    (h : w guard = true → w a = value) :
    ClauseHolds w [(guard, false), (a, value)] := by
  cases hg : w guard with
  | false => exact ⟨(guard, false), by simp, hg⟩
  | true => exact ⟨(a, value), by simp, h hg⟩

lemma orderedBitClause_holds (w : Valuation) (a b : Nat) (pref : Option Nat)
    (h : (pref.map w).getD true = true → w a = true → w b = true) :
    ClauseHolds w (pref.toList.map (fun p => (p, false)) ++
      [(a, false), (b, true)]) := by
  cases pref with
  | none =>
    cases ha : w a <;> cases hb : w b <;>
      simp_all [clause_cons, clause_nil]
  | some p =>
    cases hp : w p <;> cases ha : w a <;> cases hb : w b <;>
      simp_all [clause_cons, clause_nil]

lemma capClause_holds (w : Valuation) (allFlags : Finset Nat)
    (chosen : List Nat) (budget : Nat) (hnodup : chosen.Nodup)
    (hsub : ∀ i ∈ chosen, i ∈ allFlags) (hsize : budget < chosen.length)
    (hbudget : (allFlags.filter (fun i => w i = true)).card ≤ budget) :
    ClauseHolds w (chosen.map (fun i => (i, false))) := by
  classical
  apply (mappedClause_holds_iff w chosen false).mpr
  by_contra hn
  have hall : ∀ i ∈ chosen, w i = true := by
    intro i hi
    cases hv : w i with
    | false => exact False.elim (hn ⟨i, hi, hv⟩)
    | true => rfl
  have hsubset : chosen.toFinset ⊆ allFlags.filter (fun i => w i = true) := by
    intro i hi
    have himem := List.mem_toFinset.mp hi
    exact Finset.mem_filter.mpr ⟨hsub i himem, hall i himem⟩
  have hcard := Finset.card_le_card hsubset
  have heq : chosen.toFinset.card = chosen.length := List.toFinset_card_of_nodup hnodup
  omega

lemma cnf_append_holds (w : Valuation) (first second : CNF)
    (hfirst : CNFHolds w first) (hsecond : CNFHolds w second) :
    CNFHolds w (first ++ second) := by
  intro clause hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hfirst clause hc
  · exact hsecond clause hc

-- This is the positive-even/negative-odd literal convention of the kernel checker.
def encodeLiteral (literal : Literal) : Nat :=
  2 * literal.1 + if literal.2 then 0 else 1

def encodeCNF (formula : CNF) : List (List Nat) :=
  formula.map (fun clause => clause.map encodeLiteral)

lemma encodeLiteral_holds (w : Valuation) (literal : Literal) :
    (w (encodeLiteral literal / 2) == (encodeLiteral literal % 2 == 0)) = true ↔
      w literal.1 = literal.2 := by
  rcases literal with ⟨i, sign⟩
  cases sign <;> simp [encodeLiteral, Nat.add_div, Nat.add_mod, Nat.mul_mod]

lemma encoded_cnf_holds (w : Valuation) (formula : CNF)
    (h : CNFHolds w formula) :
    ∀ clause ∈ encodeCNF formula, ∃ literal ∈ clause,
      (w (literal / 2) == (literal % 2 == 0)) = true := by
  intro clause hc
  obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hc
  obtain ⟨literal, hl, hv⟩ := h source hs
  exact ⟨encodeLiteral literal, List.mem_map.mpr ⟨literal, hl, rfl⟩,
    (encodeLiteral_holds w literal).mpr hv⟩

lemma acyclic_definitions_have_encoded_model (defs : List Definition) (start : Nat)
    (w : Valuation) (h : Bounded start defs) :
    ∃ z : Valuation, (∀ i, i < start → z i = w i) ∧
      ∀ clause ∈ encodeCNF (compiled start defs), ∃ literal ∈ clause,
        (z (literal / 2) == (literal % 2 == 0)) = true := by
  obtain ⟨z, hpreserve, _, hcnf⟩ := acyclic_definitions_extend defs start w h
  exact ⟨z, hpreserve, encoded_cnf_holds z _ hcnf⟩

end CnfTransport




namespace CnfTransport

-- Boundary, witness, unit, guarded equality, guarded constant, ordered bit, cap.
abbrev Requirement := Fin 7 × Nat × Nat × Nat × Bool × Option Nat × List Nat

def requirementHolds (flags : Finset Nat) (budget : Nat) (w : Valuation)
    (r : Requirement) : Prop :=
  match r with
  | (tag, a, b, guard, value, pref, sources) =>
    match tag.val with
    | 0 => (w a || w b) = value
    | 1 => ∃ i ∈ sources, w i = true
    | 2 => w a = value
    | 3 => w guard = true → w a = w b
    | 4 => w guard = true → w a = value
    | 5 => (pref.map w).getD true = true → w a = true → w b = true
    | 6 => sources.Nodup ∧ (∀ i ∈ sources, i ∈ flags) ∧
        budget < sources.length ∧ (flags.filter (fun i => w i = true)).card ≤ budget
    | _ => False

def requirementClauses (r : Requirement) : CNF :=
  match r with
  | (tag, a, b, guard, value, pref, sources) =>
    match tag.val with
    | 0 => if value then [[(a, true), (b, true)]] else [[(a, false)], [(b, false)]]
    | 1 => [sources.map (fun i => (i, true))]
    | 2 => [[(a, value)]]
    | 3 => [[(guard, false), (a, false), (b, true)],
        [(guard, false), (a, true), (b, false)]]
    | 4 => [[(guard, false), (a, value)]]
    | 5 => [pref.toList.map (fun p => (p, false)) ++ [(a, false), (b, true)]]
    | 6 => [sources.map (fun i => (i, false))]
    | _ => []

lemma requirementClauses_holds (flags : Finset Nat) (budget : Nat) (w : Valuation)
    (r : Requirement) (h : requirementHolds flags budget w r) :
    CNFHolds w (requirementClauses r) := by
  rcases r with ⟨tag, a, b, guard, value, pref, sources⟩
  fin_cases tag
  · exact boundaryClauses_holds w a b value h
  · intro clause hc
    have hc' : clause = sources.map (fun i => (i, true)) := List.mem_singleton.mp hc
    subst clause
    exact witnessClause_holds w sources h
  · intro clause hc
    have hc' : clause = [(a, value)] := List.mem_singleton.mp hc
    subst clause
    exact ⟨(a, value), by simp, h⟩
  · exact guardedEquality_holds w guard a b h
  · intro clause hc
    have hc' : clause = [(guard, false), (a, value)] := List.mem_singleton.mp hc
    subst clause
    exact guardedConstant_holds w guard a value h
  · intro clause hc
    have hc' : clause = pref.toList.map (fun p => (p, false)) ++
        [(a, false), (b, true)] := List.mem_singleton.mp hc
    subst clause
    exact orderedBitClause_holds w a b pref h
  · intro clause hc
    have hc' : clause = sources.map (fun i => (i, false)) := List.mem_singleton.mp hc
    subst clause
    exact capClause_holds w flags sources budget h.1 h.2.1 h.2.2.1 h.2.2.2

def definitionCatalog (start : Nat) : List Definition → List CNF
  | [] => []
  | d :: rest => definitionClauses start d :: definitionCatalog (start + 1) rest

lemma definitionCatalog_holds (defs : List Definition) (start : Nat) (w : Valuation)
    (h : Realizes w start defs) :
    ∀ formula ∈ definitionCatalog start defs, CNFHolds w formula := by
  induction defs generalizing start with
  | nil => simp [definitionCatalog]
  | cons d rest ih =>
    intro formula hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact definitionClauses_holds w start d h.1
    · exact ih (start + 1) h.2 formula hf

def specializeDefinition (value : Bool) (d : Definition) : Definition :=
  match d with
  | (tag, oldValue, a, b, pref, sources) =>
    (tag, if tag = 0 then value else oldValue, a, b, pref, sources)

lemma specialized_inputs (value : Bool) (d : Definition) :
    inputs (specializeDefinition value d) = inputs d := by
  rcases d with ⟨tag, oldValue, a, b, pref, sources⟩
  fin_cases tag <;> rfl

lemma specialized_clauses (value : Bool) (d : Definition) (out : Nat) :
    definitionClauses out (specializeDefinition value d) = definitionClauses out d := by
  rcases d with ⟨tag, oldValue, a, b, pref, sources⟩
  fin_cases tag <;> rfl

def specialize (start : Nat) (free : Valuation) : List Definition → List Definition
  | [] => []
  | d :: rest => specializeDefinition (free start) d :: specialize (start + 1) free rest

lemma specialized_bounded (defs : List Definition) (start : Nat) (free : Valuation)
    (h : Bounded start defs) : Bounded start (specialize start free defs) := by
  induction defs generalizing start with
  | nil => trivial
  | cons d rest ih =>
    exact ⟨by simpa [specialized_inputs] using h.1, ih (start + 1) h.2⟩

lemma specialized_catalog (defs : List Definition) (start : Nat) (free : Valuation) :
    definitionCatalog start (specialize start free defs) = definitionCatalog start defs := by
  induction defs generalizing start with
  | nil => rfl
  | cons d rest ih =>
    simp only [specialize, definitionCatalog, specialized_clauses, ih]

def candidateValue (defs : List Definition) (free : Valuation) : Valuation :=
  run 1 (fun _ => false) (specialize 1 free defs)

def fullCatalog (defs : List Definition) (requirements : List Requirement) : List CNF :=
  definitionCatalog 1 defs ++ requirements.map requirementClauses

lemma candidate_catalog_holds (defs : List Definition) (free : Valuation)
    (requirements : List Requirement) (flags : Finset Nat) (budget : Nat)
    (hbound : Bounded 1 defs)
    (hside : ∀ r ∈ requirements, requirementHolds flags budget (candidateValue defs free) r) :
    ∀ formula ∈ fullCatalog defs requirements, CNFHolds (candidateValue defs free) formula := by
  intro formula hf
  rcases List.mem_append.mp hf with hf | hf
  · have hr := run_realizes (specialize 1 free defs) 1 (fun _ => false)
      (specialized_bounded defs 1 free hbound)
    apply definitionCatalog_holds (specialize 1 free defs) 1 _ hr formula
    simpa [specialized_catalog] using hf
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact requirementClauses_holds flags budget _ r (hside r hr)

abbrev Reference := Nat × Nat

def referenceValid (catalog : List CNF) (ref : Reference) : Prop :=
  ref.1 < catalog.length ∧ ref.2 < (catalog[ref.1]?.getD []).length

def referenceClause (catalog : List CNF) (ref : Reference) : Clause :=
  ((catalog[ref.1]?.getD [])[ref.2]?).getD []

def selectedClauses (catalog : List CNF) (refs : List Reference) : CNF :=
  refs.map (referenceClause catalog)

lemma getD_mem_of_lt {α : Type} (xs : List α) (i : Nat) (default : α)
    (h : i < xs.length) : xs[i]?.getD default ∈ xs := by
  rw [List.getElem?_eq_getElem h]
  exact List.getElem_mem h

lemma referenceClause_holds (catalog : List CNF) (ref : Reference) (w : Valuation)
    (hvalid : referenceValid catalog ref)
    (hall : ∀ formula ∈ catalog, CNFHolds w formula) :
    ClauseHolds w (referenceClause catalog ref) := by
  exact hall (catalog[ref.1]?.getD []) (getD_mem_of_lt catalog ref.1 [] hvalid.1)
    (referenceClause catalog ref)
    (getD_mem_of_lt (catalog[ref.1]?.getD []) ref.2 [] hvalid.2)

lemma candidate_selected_holds (defs : List Definition) (free : Valuation)
    (requirements : List Requirement) (flags : Finset Nat) (budget : Nat)
    (refs : List Reference) (hbound : Bounded 1 defs)
    (hvalid : ∀ ref ∈ refs, referenceValid (fullCatalog defs requirements) ref)
    (hside : ∀ r ∈ requirements, requirementHolds flags budget (candidateValue defs free) r) :
    CNFHolds (candidateValue defs free) (selectedClauses (fullCatalog defs requirements) refs) := by
  intro clause hc
  obtain ⟨ref, hr, rfl⟩ := List.mem_map.mp hc
  exact referenceClause_holds _ ref _ (hvalid ref hr)
    (candidate_catalog_holds defs free requirements flags budget hbound hside)


def boundedCheck (start : Nat) : List Definition → Bool
  | [] => true
  | d :: rest => (inputs d).all (fun i => decide (i < start)) && boundedCheck (start + 1) rest

lemma boundedCheck_spec (defs : List Definition) (start : Nat) :
    boundedCheck start defs = true ↔ Bounded start defs := by
  induction defs generalizing start with
  | nil => simp [boundedCheck, Bounded]
  | cons d rest ih => simp [boundedCheck, Bounded, Bool.and_eq_true, List.all_eq_true, ih]

def referencesCheck (catalog : List CNF) (refs : List Reference) : Bool :=
  refs.all (fun ref => decide (ref.1 < catalog.length) &&
    decide (ref.2 < (catalog[ref.1]?.getD []).length))

lemma referencesCheck_spec (catalog : List CNF) (refs : List Reference) :
    referencesCheck catalog refs = true ↔ ∀ ref ∈ refs, referenceValid catalog ref := by
  simp [referencesCheck, referenceValid, List.all_eq_true, Bool.and_eq_true]

lemma encoded_selected_flatten (catalog : List CNF) (chunks : List (List Reference)) :
    encodeCNF (selectedClauses catalog chunks.flatten) =
      (chunks.map (fun refs => encodeCNF (selectedClauses catalog refs))).flatten := by
  simp [encodeCNF, selectedClauses, List.map_flatten, List.map_map]

end CnfTransport

end PEqualNP.Outside.L_meta_9033
