import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Tree.Basic
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


-- Exact retained finite CNF B-01; no circuit-to-CNF transport is asserted.
namespace CaseB01

set_option maxRecDepth 100000 in
def variableLookup : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 60, 64, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 87, 97, 102, 103, 104, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 125, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 231, 232, 233, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 297, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 317, 318, 319, 320, 321, 322, 323, 331, 332, 333, 334, 341, 342, 343, 344, 345, 346, 352, 353, 354, 441, 443, 445, 446, 447, 448, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 492, 493, 494, 495, 513, 514, 515, 516, 517, 518, 525, 526, 570, 571, 572, 574, 576, 577, 579, 580, 581, 583, 585, 587, 589, 590, 591, 592, 594, 597, 598, 600, 601, 603, 604, 609, 610, 611, 612, 613, 614, 615, 616, 617, 620, 622, 623, 624, 633, 634, 635, 644, 647, 652, 653, 655, 656, 657, 658, 659, 660, 661, 662, 663, 665, 666, 667, 671, 674, 675, 676, 677, 684, 697, 699, 700, 701, 703, 704, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 728, 730, 733, 734, 735, 736, 739, 741, 742, 743, 744, 746, 749, 751, 752, 753, 762, 764, 770, 772, 773, 774, 775, 776, 779, 781, 782, 784, 787, 788, 792, 795, 796, 805, 806, 807, 813, 816, 819, 824, 825, 826, 827, 828, 829, 830, 831, 835, 839, 848, 850, 859, 860, 862, 867, 868, 870, 873, 874, 875, 878, 881, 882, 885, 886, 889, 890, 891, 892, 899, 905, 908, 911, 912, 913, 916, 917, 918, 921, 924, 925, 928, 929, 932, 933, 934, 935, 936, 945, 948, 951, 954, 956, 959, 960, 961, 964, 965, 966, 967, 968, 971, 972, 975, 976, 977, 978, 988, 991, 994, 997, 999, 1000, 1001, 1004, 1009, 1010, 1020, 1021, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1125, 1126, 1175, 1176, 1187, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1226, 1230, 1234, 1235, 1236, 1243, 1265, 1278, 1279, 1301, 1302, 1303, 1304, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478]

set_option maxRecDepth 100000 in
def formulaWords : List Nat := [
  0x1000010578001582a8000a815a0004e0ab000298520a2140278360a90002685380012c294000781460003b0a10001d04f80013026c000961320004a0970002304b8001242404704412a000420930001384880009823c0008a1102181b08d000108458000802240003e10e000410850002003f01c106000140810000983f8000041f40007a0d6000280430000d01480001c0140d80003404003019000040038190000600900802e0000b0140140000a00b,0x10f23a0000c41d20003c0e90002d873800164394000e01bc3706d0d80b438c0006a1c20006b0df0003106e8000cc374000b61b6000590d90003506b80019835c000d21a0338230d5000310698000a034c0004e1a2000260cf000328640c6070334000c4196000210cb0001006480007c31c000c218a0005e0c50003005f02a1860001a0c10000c85f8001742e00f0bd0002d85d8001642e4000261720005a0b70002c85a8001602cc000ae166000070b1,0x100046c8991c0004688e8002244740011822c4502411b00046824800214464000502320007e1170003e08a8002204388603a2260008903b00042888800084444000fc21e0007c10d0004208580020442c001062080b0848002100b4000fc20e0007c1050004007f0202060007e1010003e07f8001f43f4000f81f60007b0f90003d07c8000203dc000061ea000790f00003b8798001c43cc000f10003b0750e81cc390370ef0001e8768001ac3ac000c5,0x1000548a8020038554000282a6000a7151000098a880029853c0014a29e0000800c29a00003002296000a4146000510a48002705240012c28e000a114027c4f09d07028a0003d143000470a08002144fc0007827e0007e13d0003e09d80026c4d09913025c1709c8002404dc0006a26e0008e1350001a09a8002144cc000662660007e1310003e0978002544a093124244148968000ac4ac0011c25200085127000150928001f048c0011e2420008e11f,0x131e0000800e31a00003004316000c4186000610c48002f062400187000608c017e2f85e83806c30a000b61830005a0c08000f05fc000762fa0003a17b0005d8ba1722e05b82e0582f2000351770001a0ba8002ac5cc000642e2000a716f000188b78002d45b4001682d6000b3169000578b48002c8588b004808859c001570a2590001562ca00028165000138b18000985840015c2b45601d0362be000ab15d000108ae80008056c0003e2b2000aa157,0x1000708e01be3786e83806e38a000db1c30006c8e08000f06fc0007637a0003a1bb0006e0298003686dc001b236a000d81b30006a0d980035c6b0d504808c6c4001a035e000281af000648d680031c6ac001a63486881d038352000d4039000108d3800326104d20003246940018e346000cf1a1000660d08003386681602a33e000c919d000638cd80032c6501001e33200014197000638ca80032264800190326000c7191000640c780031863c0018a,
  0x100010905800080824001fa40e00101205000800ff024406000142010007e8ff8003f8000fc1fb000028fc8003ec7d0001f23ee000f81f70007d4001ee3d87a8f41e60bc7c40006a3de000341ed000770f58000cc7ac000643d2000e71e7000788f28003c078c001de3c2000ed1dd000750ee8003b0758171db0000d0ec80039c75c001d23a0088ea80005074c001ce3a2000e61cf000728e7800024734001cc026000041cb000720e3000388724001c7,0x148e001202450008f12180047e9000023e4820011e23f0008f91e8004768e51e0004708f40023a02a000052390008e00580046c8d00023246e001132370008d40023045c8b1152280e48cc0021a4620010b22f0001e1168000ec8ac001fa452001122224408790e06044e000352250001a1118004088840006443e000fd21d0008610d80042c8640021442e001062170008490820e0948540020442600028213000139088003f483c0020a4108181e20d,0x14fea300028a5120013c87b51000143285000a194180050ca04002790d6a100026b0cea08002610caa000027e4fa0013f27b0009e42ba7c0009842aa7a0009e0002764ea0013927100098427a700009b9368004c2105360004d2995350004d099c0026106a998002644c6001308294c4001300004b497c0025d00096c002584ac0012a25900095c002524a09392624a0c09540006a4a600034251000921278000c89340023c4960012324900091121030,0x15a0b3c002cd592b38002cc5960016385159400164039000b1560ac6000b0163800588b0c002bb06ab08002be5780796080058007c0002857e0015b2bd000ae8002b856e0015aab356c0015a00f000ac80280056200157aab560001572ad000a9c3daac000aa954800554164002a10ceaa0002a6000a915180053ea6d5000053ca740029906aa700029a03a0014c00052ca5400293522a500029201a00001291000a400180051e00146800516a1d47000,0x1000c082d8005d219d800005b618d7f0005f8bec002f95e2be8002f85ee0017c2f5000be1798005f011c002f808a001748515ec001742f7000b7427af4000b6c26af2000bc1778005e0bb4002f05d600178039000bc01b8005d210d770005ba105760005b60fd750005ceb85740005ccb94002e65c60017302b000b741aae4000b6c19ae2000b816f8005c007c002db04eb78002dc000b616d8005acb6c0000e018b6400004004b5c002d5000b4d6a000,0x166a00199b2d66800199331000cc9978006641c4003210f6cc00031d0f2cb80032c65600196329000cb193800658c940032c0ba0019086b6540018f8696500018e86764c0018a86564800191053000c800031b62ec700031a6320018d02d000c541ab18000c581080062800188313000c3989800020c440000661e00186800616c0d86000614c240030a60e00185305000c28378006141b4002e90f2c20002dd0eec18002db0eac1000302602001812ff,
  0x107a001bf039000dec21b7c000de5bbb7a000de0188006f00ac0037604a001bb01f000dc9ba8006e4dc40036f000db5b4b6e000db1b58006c61edb50006d0d9c003686ca001b08696cc001af8676c8001b10006b808c0035a6b2001abb556b0001ab013000d58068006a802400354006001a98006a2001a7b4b6a4001a3b50000d39a680068a1eda6000694d240034a0be0019f867690001a2000684d040033d676cf80033c05e0019d023000ce19b800,0x10e6001da071000e7c3cbb2000ec1d78007601840039f0ceeb8003aa75a001d53a9000e9dd1ba8000e99d280074c12c003a6092001cf851748001cf3a5000e89d08007440f4003a2076001cf843740001ceb9b73c001ce39f000e70188007380b40039a04a001cd021000e59cc80072ce5400393000e440038f716e4800389720001c738d000dec3cb8c000e282d80070ce14003836fee1000382702001c104b000e08238006f6145c00006fcdf40037e,0x1000fea018007fcff2008007e8ffc003f07fa001fc3f67f6001fa3f9000fc1fb8007e4fd4003ec7e2001f78007da001f53e9000f99f28007c60d5f20007c4001f08007be001ee8007b6f5dee0007b4f64003c70f2f60003d67aa001e38677a8001e93d1000f3de5bd0000f39e680078e145e6000794f24003ca07a001e3843790001e23c7000f09e003005cf14003bc786001dc3c1000ef811800774ef4003ba772001db80076aec5db000768ecc003b4,0x189f148004500920022703b00112a268008911181044b0011122480088111c0044288a002214410010fe1ec400010f80880087801c0043a0720021b4390010d2198008321ee1900085d0b21542884d0c40006a85e0020a42d00100a158007e90a4003f084e0021142083d0720d42500015a118008290840040283e001fa41d000fc20d8008300020b4150010420740c82600201411000fd2078007e10340040880d01205800805024003f480e001f8405,0x16b0d563880056cace388005af1bc002d78da0016bc6b00052e3480052119c003d3000eac00387000d0c002fd000b44002a50009dc0045d00115400417000fac003bb000e5c00373000d6c00339000ae400297001194004430010dc003f3000f41d43846c0d018f2fa59ca893a00078ce79bd35e67cc71742c65409a8003b8728dc1ac336624b695b2944bc002324630011862fc620011800a8008bc02c0045c8b60022c023001158298008a914c00451,0x1932000eac970007564a8009252424748c915222434849052023f47c000d51abc91000a45494910009e52e48f0009852e48d000b395ac8b000a8949c8b0011321fc89000ba16cc89000b1d5a489000d61abc87000ad95ac87000b66428005b320c002d99020015a47f0005363f80087f1f4002928fa0011dc7d0007363e8008f51e23b4748e51c23746c8d51a2330004f296a3c8004c296a3b80059cace3a800544a463a8008990f63980040a7e239800,
  0x198930a604be9792ea5c4b69692ca584ae00099134cc7000f81f3cc5000f79f3cc3001066004c1000e61cecbf000648cfcbf000fa1f3cbd0009a934cbb000738edcb900076e5b8007cf2d4001db966000edcb100076e578009592aa544a694928a5049e93926a4c496928001ab35d9560016cae095600148a9a952000fc2039520020cbfa94e001ba37794a000fea0294a0022d4599460019f33b942000e71d593e000eac9d00080e4d80033326c001d5,0x10008110acf5000558b3cf50004288dcf50007e90acf3000e0a788003633c4002159de0010aced0008567580042b3a4004e69c938a704de9b936a6c4d69a934a684ce999328003786ff394002e75e13940044a89f38c002c059338c002d95e13840025c4df384001f841b37c004198153740043887736c0019235336c0045289f364002fa5e33640044c89f35c002e85e335c001fa41b354001a99a600106cd10008366780041b3340020d996002644c6,0x1000acd6951d0001f04ed1d0009e53f51b0009853f51900047096d1700042896d150003e096d13000e228880068d43c0009da1a0016950b0004b684800a0d412815009fd3f27d4f89ed3d2794f09dd3b2754e800113e28505000bc57c5050004488dd05000b9d7c5030004248d503000efde7501000dddc15010004088dd01000b657c4ff00097139cff000730efcff0007e10acfd001066094fb000b757c4f9000648d8cf900114a28cf7000be97ccf7,0x15f0c0ea4800744ec6a38005e0c0ea38004d2a1aa2800676d2aa18006aeda2a08003987c6a08003947c69f80015c38e9f8008330c29e80016c38e9d8001ac38e9c80073cec69b8005d0c0e9b80016438e9a8001c74cc000e3a6200071d2f0005e6968001c74ac00528a4d49291520a3d4728d518a2d45289510a1d432855080011422bd270002504ed2700113a2bd25000dfdc45250009a53f523000c5991d21000ad56951f000630dcd1f0010f22bd1d,0x1a0f39e64c938f6002b9570add5b2b5568acd592b1560abd572ad558aad552a9550a9c00218435ae200212435ade00209435ada00205435ad600200435ad2001fd435ace001f7435aca001f6435ac6001d63b5ac20010d233ac2000f21f3ac20005b0efabe0006b0efaba00201435ab6000590efab200077d570003beaa8001df54c00185aa200077d4f001532a5548a8d512a1540a7d4f29d538a6d4d299530a5d4b295000646cb2a580074cec6a4800,0x2002b9d4da5341e73cc995a002b9d4da0f39e64cad926002a6d29a0f39e64cad926002b9d4da0f39e64cad8f6002a6d29a0f39e64cad8f6002a6d29
]

set_option maxRecDepth 100000 in
def formula : List (List Nat) := decodeF (unpack 11 formulaWords)

set_option maxRecDepth 100000 in
def clauseIds : List Nat := List.range' 1 833

set_option maxRecDepth 100000 in
def proofWords : List Nat := [
  0x12800000d650868c28a0000686528034513d000034279381a209d80001a1049b0d0c4e00000d06a4cc68426c4c026a0000524c4682,0x20000d4b90d2c5b4ae85a00000d4b08d28580a985700001ecab0d24560a605580000d4a70d2052c0000d0f651068e28e4f0,0x16546a2368000068653243501ae3141ac00003531834f19f0000343b9831a70c780001a13cbd0d3461c0000d0825d86983025b82f8,0x2d588bcf888b80000d4f90d5477cd887680001ecda8d50734d107240001ecd30d4c6f80000d0f66606a436e6403640000d6,0x14a485649e8064787f647085a4a085249c7f246e84e49a7ee46c82a48a7ea46a7e246882e4f47e64dc7da46400085c862,0x12ce52a2aa4be2687764f072e4ee6e64ec6b64ea6724e85724e652e4e44b62640006245b46b04a683048c0000f68646ae,
  0x18ea6b65166b23b06b64ea0006aa8e26b451456e2ce5724e60005668e26b24d677243072a3f66e23c66b23b066e38856e,0x18d08cc6bc6b85642c80082f00062a25226b60005ae8ea6ba51e59e2ea5a24fe0005668ea6b851c5462b654a4fc000522,0x154202046a9348b36129d010235aba439b014e00811aad521cd7ca491e4a451dca409e05009804d4000b98f48e88e48e08dc8d88d4,0x29744cc0012492412292212192112092011f91f0d90d88ad05940385e403454ca4cd84000b6522cd8ca880408d56a9166c4,0x318c9a8dcc9d91949c4000991294d9cac47f03e8000809294d98ac116c9991749f000116528cd94a9d23ca91234a8c0208f,0x192c9286d04d28c04d08bc4ce0280000141f03f01f23f41f63fc1fa4046cc04a3cc6ee5644021f80526824c626e6ea3c8,
  0x5189f593c8001f3a5e9b495c2539599fd91c1fc91b9fb91b004472fcc9b90609180023995895495094894494093c938934930,0x197096c96896496095c6da58a7c245a0007ce98a6d85887be4580007ce9866d65847323f872e4ee00073a97e6d45807d2,0x31549ec00113d364dbcb40bec660bf4a00000bc5364db8b1d304b0d0048ecffc8e8ff48e41008399098c98898497c978974,0x3399391389381379369361359351349341339331328dc8b58001874de9c26e25a68724aa86e4de0008769b66e05a28a64c6,0x33fcdd8ba80041d5f09f26ea5d00204ec514f73742e70102757ca7b9b996e26e96a20592020491f80467f01c8f8fe48dd0148f41410d,0xaeb41324441124300826e079211fc91ba069208281374194114094013f93f13e13d93d13c93c13b93b13a93a0ddcbb8000994e6,
  0x27dce447e4000dfd494decc249fc534a3453c0009a548cde8c1c0401156aa3e6f26085a62ec5aa2ee000566a3a6f05f09f6,0x2d1c73cb4c5d89fc534e447e4d44744b545dca3453c9e05000056fa50a4ca48a44a40a3ca38a2ca28a24a18a106f8614712,0x22d94ecdfcc5c080151aca726fc6281c409c1e40a01e209a000164a6a6fa61ca225faa1e5f8a165f4a36604a326027123ee,0xa752b927344327000023853f38331b1f00f51f60f71f50f40001ca53f38231a02008c5729f9c098c80098f0c14f4e00c6008015,0x26a8c48d60b6c5ecb645e4034754d5c75cd50750020374728e0803c594ad45980047504615c7026b23b056e2ce8824b46b6,0x40018b5315295215195115095014f94f14e94e14d94d0e14c7008083398a827084b287c4b08784ae02035200c35062035661c,
  0x838fac08c530d556ce1ccac3b813c0614bab270c64aa5a620a5e622a5661ea62624a666262f01621c409c3101661e40a030e160,0xa3211a23611b23511800021a56138b32f1f20f6010334f22b09c519707702780c2eb57ce24cb43b813c06175aba710658806478,0x1ad672266a0321e838096b49c819a03415f59ce3ccccfbc8cc0010d5594e38cc802093ac671a66275a41c75650600076aac2718660,0x85714242124a41d2483f923741b2473f723627d144019e953f8a680cf42a3453c0086b86aade72666e0b1bb8480e6b69c919b02c7b21204b,0x2ca86102c83b813c0c231ae4ae0adcad8ad4ad0accac8ac4ac0abcab8ab4ab072867084a49883e4928064788464967f6470,0x4c216d1ac1899ca8000619731cb0d480892c21f92ca1e12b80c577104968002ff62672a674aa264eaaa652aa6650a9e64caae,
  0x41405b01585d01605c8148138be96f8bf80f8bf00406a0477317a5c072e05a06630017c05e18205c5c630605630406a6965ca,0x2d34134638bdc658bd4654bcc65011c64c040815d21aa5f07302cc5682ca5642c801c04800804616004c15c04a16404e168,0x4c31778c69768c61758c581c8c51788cb97c1cc06a01e86601e0040820459f1ae5d27320721a40761a207019e06e0a232209e,0x5781cd00411234c0e832c0d40e0811887360201983918a0080cc0406e0408d19a1945e073406819406c19206618e06408631008269807e,0x5af801166024a76c05b02f60204cc8739d3972e11852e93992e63960c20310bc0300c439b0000d739c01034c238c98041a6020d75f232e,0x411366e7cb605ec0604901294b5b275000766489d01529498aa14a8aa94b9390002489489cf9ac8092ca74cd54d68b585e8040238e273c,
  0x4aa1490a980c0bf244e8121ce7522cd8d214a6d20ca69204a640e0570152e80814c000c7248b1cacce84a98d5475cd587540305e40253d,0xba20040070030180020160010130de000bc54b00580000a88f11d94a0e69498048ea0040fe06c0151f0d91224a791fca600407f,0x10de27e1062660f427a1022620f01fa0ac27610025e0ee1f60aa28210826a0f828811227011066a3860002922381f0214,0x164e3740ba37000063a27226025c23865874610a0f66a428410c6623820e237e6663846583700b80fe26e0fc2420e023e,0x21584bc1dc4141683fc15c3ec1544e022042017c4081780409b2161f07480f82680fe26e0fa2660f20d66a20ce36a656378,0x26f4cc4704cbc700000ab74627a10227610028210828811263836263435e62c35a0580ba0400b22620f020e0b62020b01fa,
  0x40c47606405022168b33a73a410a3a20f93a50002a5d30290108961443d81503d014c0444b1f274a10c28610a27e1040e237e0f66a40f2,0x46d81f85d81585b81407282286c81f05c81505a8138599d387582506f82106b9ce077027804fbec3469c004e363a664750048,0x10cc0801b808860233a0b633660634c6143440dc0981d208e0f237a65e3801c20861da0960d60100f66a46623821ce08c,0x5c39411a194097e94016893f95293f13b93e9b78f119a8e180814a4e4c74ea4614b805f8b98e580780b00237f5d2334188082,0x165a3846647500f0808089e4044fa3e4e940e0ed7a244a75241a70a3e66823905f633059e2ea5462b64ea27e1e40a07a6508756506,0x9e036d1e13681de3661dc36026d31f1b606807b0189fd848d28378d11858d31810cd82d02207082186e82000c4c6ca46ec0225f,
  0x91206c11906911706710f0610fd05611506610d0600083640966e474428ea8121393401880900f008e1d00981da0960f66a86d6,0x1010288082541809a474e98eb0ea40e30f0119990a3aa11c3a6138088018bfc0c606022657560c62200ca0764c089e4c48a04c20900d62340da,0x2eb04481b043c1840606721a0c005033ba920d0024848e9d683408c00017a144820e78808e707fce687f40e05574a41609241222e0ce,0x2081a9023318482e91a00780470088840c452000c203a4eb818810c80ce78808e687f4440194e707fc0e07374240c07640874641874c,0x175e0118c818c74041ee0e1fb0718c9f00f5088c54fb07b844622d4c7480230d3ea1e80018490b3b0002c8c00aba75804837c73038472838004f4139e75e,0x86b3511e90ee06535032b1bc3251b91eb0ef0dd0400671b5008ce40467a022130580ba2100be62c35a0400b22040bc3ce1da39e,
  0x4ee0006e23c47b03ccd9c77817c72cda4784d2c740db0780d38738da8d50d30d4c1e812c3b01303a4eb80e34d3de1e41c2086,0x2748a3c54000c030680f67640203cb671de3291bb3691e132d1c236c1e03321c136a3543303520685343c2aa005f90f60d27624da6c2,0x217c72ca14528a04520d2c740a1c538d38738a285307b43c4d30d4ca20d1c1a4ec479c3b475c39474438873cebc02cd96a6,0x167a38e67438a0441c83a61c605200c3b41d23a81d067e3943b81e00cc1de3d41e63de1e43d21dc0d668c0ca68a692398,0x14547ac44e7b44527a844c7b04507ba4560000f20ce78e76875c1d00980a2878410098841c41a246311880f47661ce3b21cc05e38c,0x8343b207a3b3008afc0416a060b90105eabd1691f00f50e204e2b7167008c0d5c9399db90b9c98fd01462eac458ca3c5400430f0f218876a,
  0x2528a0c524a045200228f65a3845562c450e29c5cc3084d02720113db321c12ae16100863d721a59331a10044c6cc0d48ab0d240217b,0x5da1848d280c2d2374104afc5a8032e34ca2746be3b667e39463a36a5422ba4d628c010e1808bec0c37ed94774021bb64e3745522be50a,0x25400001aced8854ec8848ed4858ec0844eb883ce789b0dec7d4e347d8e3c7e0e287d0b1c5bcb045b007c5f800ae734078e,0x11e60ca68a0be3960f19986902c0484e0440376c0f22584919c04306d4c748c3469c0819b0cc76e29450868c50e29c51429851068e0f401051e,0x11da0960cc76e1ce08c0343782a5d40468e0834b0f47721e63d21dc0be3963da1e20ca68a0702c818174f7879004112143913d40f67701dc3d0,0x5db00588e5e02c46202cccd470c0235530e16000060477608a74c6326a005444fd9dd01c21a674c00668ba0614b98e58b805f808651766,
  0x15522be0b22bc0118a818c758d0d81730c214f0ac93409c80c63a5d429cc60d3cb90d2ca70d20998d081031d7720cc76e2ee1500d6,0x111e0179e800bd4cd0318cc9808ce97f8ce0a98488149a08108d680e8ab93189b98b8d894d8ad13289d0b885280c5ea194d140295b,0x4aa0498ab04e01019a64414026c1a0d50306c808fdd418a48441d2160ed030788083e404202002e35ec2ca7781462dc1522e614c2ae1262aa1242a2,0xa4512623f12424d12a008ad40478e9444b00431b7724a625a0d676c4a82604b026251e2a04ae25e0000c006048077a11e2a0124,0x86b3b622611923611b28f150004b3dcf0301df8144aa4748e047c0425547a77c25649225049c25c48e24e49625248624a47a242,0x148224647e24447a77c43a2183fe1f63f67744021f803278a1f10d00881d418a48041329a04e4a2853088c43c998d080e24744a220,
  0x4d38006321c05a0f04124310ed43a4eb80452977661a34e0000f278021c40a1fc4061fa04a3fc73640473840044022206077a,0x4578b68510c08568b58508bf85603c9e00be8558bd85503b9a703a8cf1838d21828d18368d080406a0221730816431016661a,0x5de0b204e8ab04b9748c402800382104b0001770ae9e184f0b184d0b084c8b29de01e32e1146480504b2ce0905f078415c304,0x4b39e994215c939804e8e082f373c5d00a208678a3da6f83d46fe3e47043e27003dc70a3e670e5040000a20866f67883205ec,0xa3d3be0002393c62233cf2243ca2213cc2223c821f3c626c019b3dbd9e21708c283cdce02703031878a9c3c14e261230757a2d27a244a56e,0x11b40000e036479070839a1be0263ac6ae63a6d23c26d83c06d46a80f47726de3c4000a8278e23c02800047624001423a,
  0x4a684e8061e486c0e106c8db8690e086b8da8688df86b03c9e00de86a8dd86a0144121bc6880a2093881b63901b861a34e38e,0x4960438a30450a49d589183887c9d280e5664ac1d44941c815c5081545049f45109ec50d1049689fc53510c9c0cd470c0f815,0xb7a32d1c231a1b000935d8c1a78049ce061e78ac4c86443660a40eca2a5fe24e0e6216760a2e6002520e823a75aa265fca125f2,0x12b32e8599844ccca1466d29c79460aa386f8a3e6f287a4b25682ca87c4b001c2f2020118a1a5f6a4261062e36263a36a64e374a46,0x176023a75a22e0ce0378f80b5d404372074d1039d1c4125a2fd28001ce6e2193800189f585418a4446cf2c006492e41522aa1242de1482a2120,0x2ed4e30868e2c44c1b8530238538f287e43e002c4708e4f187ecee840c1640846b40219d016b08099c5990e0804d020a1a12320d2216,
  0x67496e8043f257827c6c0340850424021ed6ae3ae2d078236479042c21401a2a66a83a60e24264302160760c85262a80042a4,0x2dd00309d9f25d232617432217231e16c31616800a2c800e4ae5662cc87a4b29e25c29fa5d89e65c69de5c09da5be9d65bc,0x4ac84a0ae9e181ed2e0dc624016975e8a046ee9fe5da3bc1d43c01d639a1be3c41d80263ac3c8714a0a5eaa025e09ea5c89ee,0x20280f01409a8714e018d1d450a600c6860a527030e2ba920d2fb198453263018705d594197e94022a93d81437aa3c540021b97047981302b612a,0x57c1e10343a25982800e1cd050e884906a008745498aa08d9e58043ab3c4b88e047c412c7c011c7bc0e1c941e206033769970bd0089ec044fe0280b,0x232c674300e8881113898064c2e80e82606ac32866c2fc6542f06442e40218d31e16c030c498b0b4028614043b33dcdccbc465c021d1,
  0x13d2a025e26ec3ca03c17c33c1863301846f63dc73e41034019a0a019874a41635c19c74e418a0a5ee8a24c49f25d235a,0x403137584a45418f344f89c0d109ccdd81384113f8ddc84041d3d4b9884c4180a821a065e67383fe2100b80581820563ce6f2,0x107413041220012166bc204906a03d1ec001ea5e608d9e58042ce8304205a0f048584280217f010c3a070ff1fb3ba00884c06022bec66003025,0x101085808c9c149c20ef6f0334380035c241e78c417400002614001c000e90bb810cf38f14e7c820e9482c0282974e418084202744408414204,0xbb6019c1c04e160316b01383819c3e9d9bf85b81429a9be805aa2026fb01c66d3937e0d739c02e3142cdb712497511c970026d301093808cdc0c9eb11496c026b3,0x3274ab5264aa925caa5254aa0d2c74016c277cc460018bfb4e1ce05b05df21aa8ee07801d2067a8ee0023d7a7a7008626ac85e4a20d6,
  0xb67029bbe5d95f8152aed2473152cc9006957a8a63e98a6d89866d697a6d296a57897257c96e57a96657696257495e57293e55c,0x8793c00a101b09f01a05ac5c045cf50cc79284abd28cd94d70764ce871516099408839113497c74c38d12c9780247798e58c94a,0x40c9b66a033c830420024bf95656e03269819a340469f1f4a540268d011a1d063cd4a92b5009a263f94b80498f504f1c7e43e14fce0c024bf146038,0x1031cf98f0b65473204e52da4e12d7028e3cc585a1788cb80499ebe0f0934cb31354b35344b2d33cb29334b2532cb2137cb54024b7,0x6939869d390627196ca6c9b7a6b967a289310049d736cb486b432c0e826064c2e8023af11201e2b212810e01c356194322172,0x114e03c08e3de136032a4a6f67063e414a03a1320306fc3d812e02c07820411a02241620211602008679c74a4169cc6e4,
  0x6a4991a9b98b2941e4a641b6a561b41d810804e01025f960a4d9558301df855011004a56e7c8202b40840252b15203e35c19c,0x5d79088309081d890b1da1098381e08b484f8af840f1e06f4576e42e0007483523483440745e07a05409106c892667ca9870a,0x1012158191ede190e1e090d9c28f9806bab14c98cef4864ee4860067c370e50401ae8c5527b3bb27801925c1d976004a30a273c7a241e73c77e,0xa62008d1c0466f14098403454c0233b09079e5262a80119f808d4c0d04e0b5c74021f83a61c61f68580bb74ea07401da16998d087703c0da8d501a407,0x107019234e18e08678a4222085d232209e69a0176b807e6de81d29038d28628c985d0d186202d37a0ec9800234335019e42821289e,0x27a0dd87980c08740903f4f108788083f8f189b0810418b1c5c8dec7b884841cb2c5cc028c359a2e87063e45902e26fc3d6,
  0x27fc3ec166b30318b88100b02934101d157019acc14d6e0a6bb1f35f83bf7d620b701cd7e0efcf5846946135f819b1c0c45e0a6c3033638188ac5cd860221f7a43d26f0,0x10d1db879b3c0474e830420e848180f4815494c2c0ec980066c7011c9ba320c44f262039b0dd3104a2813081cd76120f3c526bb41e20640e1fe,0x40478e100400023c3410204070192a8e6429906da41620234e18e76042297e6d408640675c41e73840273c7a2a0c79a9b65a4,0x142220812202611e0245d232201989ce32d854932202cc2d608b826c9b717c8cba709b88047a6bc06309b84f0063cf5d86984d8686,0x16ec3cc1060189365580481fa0fe0144041fc04e2fa40820ca9870a5be2fe9246c842420ea6e62a9ae59c5c230a91253e,0x2f2549cc302700802a80882b40842a407c29c07826c0640274f12e02e9cc6e412a02a9ca5b61260286f23d210a01a9586d0,
  0x4678d91e40389099da9c600446a85842886042c868e2c1e591078b280d153293154019704052a2b605ec0ac35077228091441dc82004797a667ca50,0x5ea1a697a8ca82708217c8cb9080839780c60043e2021f9030fe83d20503b260008a65d3104801f16f3c021e942620a08600e0a27a4350,0x48591788a90c88511688a03c9e011588983b9a71838d200471a8a44487ecee8198edc8c84688d846cedc85cc3469c0161b42c,0x636944235943a3a9ae96c0bd96b0bd0042daa54554a5c9c800153541d39d3252b52211c95ccf540e82f4280e422e46222c436,0x2a551f0d90a4c550a40a15198d791eccf524ccfd1fca5d1a4a18530238528234538f29244e811c4e7921ce740a5af8de512,0x20a6b10da3ad5f389009a86ac9c301cd3b1c4e79574e200269d0907e849a640519a1269103462849a540518b10c9c0edc85cdbc7881c695a485e24140727ac,
  0x6b29c72b19c6ab59c8aad9c3ab69c92b79c9ab899c98d0d8024d92129898684a863069e0735e84a5c6191ab834d6ac886cc6e034c0347d,0x2126ad02241bd446928614a08d069c840f2ee267150351c809c459e8e3a519b282ce23484c2007455c16dc10950483b6e6919bd06cdea0e9c5ad2720ace71e,0x6a499128197a27f977a7c9ba80cc9b364db9414bd8b205c534cb306a0320e047c4e0c7c8df87ad0e8958bdc658be465c13271,0xc9b2ac47328c37b1ee006e4482804cf2b2c5cc0903f48083f881041884841c8444100266559a2e89e25c40963e09b66e02ca778,0x2840180ef4f148752b0da12acad8b7c5fd38cb61394b6c0c47a1404bc40a6a12ae13a5822e058e2e46f23d26ec3cc952568,0x5a1aa61c2aa3990a831bba7b9ba27a9729e390f0138be82008010408101e9029d1906008b0ef085982805a0f041c484c01f85,
  0x150a0062a25227a6ac0728ae67aa1260289906da97e6d410a01a9cc6e49c26e27384021060184dc27873c4d80fe0144d8,0x3434bec1e741a3a6f0a5267812a02aa3e60c31a16a01e2ca0224b056a2cc87e4b25642c88784ae8f46bc0082f000c1168ce,0x120008218c32417632017031c18834400621a0b1010088f50387f804c3aea4834eaca0c00e455f03520840740703487ae618a4c6f8,0x98a0b6009f8c0cfde067ff0440798f3d905043c04226022c70329780959d5c939800f86634008f6016e611402ce78409241274e41874440a078204412,0x81b1fc04bb20fa570966380a2253f8a6805132edc85c086795e20847b6040688663b70003b03da001fcd598b300392b824fe6006452a20047b031816e,0x5ed8046420605701bbb80de1c0040ebc4f70f580e0f5c02adf89e4c40116caf919720b1011660a01a80cf00c65c08592f68694314057c97b28ac4c8,
  0x1153b8819dd44e9c6f44894027850170f82d39de9942004f0a02e2352e4e4013c4871e35489ee9019cf1e29d09031748c880465abdc65814001c0204f084,0x20d89b7b89f25d29e25c29b65a49a659803a97848e9c072ae64c2e807963011cb8d9cd4cdcb6ef88680750b013a09970bd20d40c5cea2174df073ac84d36c1cec23ee17,0x28900b51779444009a89cf73730433ce2f83c25493233a520b04b20a00d40c2493088d8370073c60b4f72240c801a7983a09803d3fc0e7ca0750b,0xbd301c12e831bba7f9bb1390034c61384102fa6b9906da6ec3caa9870a03a9581e0be5373160aa02201e94c2ea47404bc8e047c40351b79e,0x22abe36963a001ee081b08c1c9a203da903619839364465f22ec3f0797284b11c35896324c10b264839344189aaf78da12b4d012acadd4a0f24d5c75d5c8e5003043ac2,0x347cc1802affa3a60631a7b00157b87d00901301dee884902b185c1434bec024795802d60323ad491e47d75e524750124084921405786024810124280922407bea02495,
  0x16768f46bca506f89247428e651a
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma contradiction : ¬ FormulaSat formula :=
  check_sound formula clauseIds (LZPacked.decode 11 proofWords) (by decide +kernel)

set_option maxRecDepth 100000 in
def originalFormula : List (List Nat) :=
  formula.map (List.map (renameLiteral (fun index => variableLookup.getD index 0)))

lemma original_unsat : ¬ FormulaSat originalFormula :=
  unsat_map_literals formula (fun index => variableLookup.getD index 0) contradiction

end CaseB01

-- Exact retained finite CNF B-07; no circuit-to-CNF transport is asserted.
namespace CaseB07

set_option maxRecDepth 100000 in
def variableLookup : List Nat := [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 28, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 58, 61, 64, 67, 68, 69, 70, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 141, 142, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 186, 187, 188, 189, 190, 194, 195, 196, 197, 198, 211, 212, 213, 214, 215, 216, 217, 224, 225, 227, 228, 231, 232, 233, 237, 241, 245, 246, 255, 256, 257, 258, 259, 260, 266, 267, 268, 312, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 398, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 470, 471, 472, 473, 474, 475, 482, 483, 484, 486, 489, 490, 491, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 519, 520, 521, 522, 523, 524, 525, 526, 570, 571, 572, 574, 575, 576, 577, 581, 582, 583, 584, 585, 590, 591, 592, 594, 597, 598, 600, 601, 603, 604, 609, 610, 611, 612, 613, 615, 616, 617, 619, 620, 622, 623, 624, 627, 628, 631, 632, 633, 634, 635, 643, 644, 646, 647, 650, 652, 653, 655, 658, 659, 663, 666, 667, 676, 677, 678, 684, 687, 690, 695, 696, 697, 698, 699, 700, 701, 702, 703, 706, 709, 710, 714, 715, 716, 717, 718, 719, 721, 730, 731, 732, 733, 738, 739, 741, 742, 743, 744, 746, 749, 751, 752, 753, 754, 755, 756, 757, 761, 762, 764, 773, 774, 776, 781, 782, 784, 785, 786, 787, 788, 789, 790, 791, 792, 794, 795, 796, 798, 799, 800, 802, 803, 804, 805, 806, 813, 816, 819, 821, 822, 825, 826, 827, 828, 829, 830, 832, 839, 842, 843, 845, 846, 847, 848, 849, 856, 862, 863, 865, 868, 870, 873, 874, 875, 878, 879, 880, 881, 882, 885, 886, 889, 890, 891, 892, 899, 902, 905, 911, 912, 913, 914, 915, 916, 917, 918, 921, 924, 925, 929, 932, 933, 934, 935, 945, 948, 951, 954, 956, 957, 958, 959, 960, 964, 967, 968, 971, 972, 975, 976, 977, 978, 991, 994, 997, 999, 1000, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1029, 1030, 1031, 1032, 1033, 1034, 1086, 1088, 1090, 1091, 1092, 1093, 1095, 1096, 1097, 1106, 1107, 1108, 1115, 1116, 1117, 1118, 1119, 1120, 1129, 1130, 1131, 1132, 1179, 1187, 1192, 1193, 1259, 1273, 1277, 1278, 1279, 1292, 1298, 1300, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478]

set_option maxRecDepth 100000 in
def formulaWords : List Nat := [
  0x114028c0009e1420004b0a10002704d09807827c0009e07a0004709d0001204e80010026c0007c1320004a0921200b84b80011c2540003a12a000400930001f04880011823c0008611e00045088044234000801160003e0890002104101610e000400850001f0418000fc2040007c0fe0003d8790f80003d07d0001e03e8000141ec000020f20003c0030001d83280008c0e4258000941201d0000900ec0002c0420000800702a0000a01201000009009,0x10003706f8001ac37c000da1b00906e80005836c000d01b20006a0d203035c000201aa000680d30003386880001833c000cc194000640cd0002f06680016032c000c6188308600be0cc3240007618e000500c5000238618000e830c000801820003e0bf0002e85c0b61682c82a0bd0002905d8000c82ec000a0172000470b70001805b8001002d40007c166000570ac1542a05304c162000290af0002805680011c2ac000501520003e0a700028852800,0x1000478908002384680d11f0000808e80022846c001162320008a1170004488a80000844c0011021c000861110004008880021e0008510820c4108106821a0007a10b0003c0848000e841c0007220a000681030003f87e0fa1f03d82b1010001907f8000c43f4000de1f6000300fb0001787c8001a03dc000f21ea000780f30003b8788001cc3c4000ec1d43a01f0ef0001207680008c3ac000d01d2000720e21c00c073800074394000381c6000680e1,0x12c859c001622ca000b0163000018b08002bc5700015a2be000ac15f000574001562a8548a814e0b0150ac8000c855c000622aa000a3153000178a880027c53c0014b2925300014829a000a503d0005201980028851c001422800680b145000080a180027c5040013c27e0000700a27a0009d1380004d89d8002544e4001342644c09712c0b04dc0006426a00031133000480988000bc4bc0011425a000931242440c89480024049c0011824a0008a123,0x10e869400166346000b11a1000670cd19832c6502d19f000190ce80030c66c0017433200030199000598cb8002c46540019031c630c518809c64c00052322000c318f0005d0c68000a062c00162312000c21870005f0c3800304600bf04230a000ba183000120c18002cc604001622fe000bd1782ec0d0be8002e85ec0003a2f6000b3179000588bb8002e45d40016c2ea000b816e0505cc001662e2000b116f0005a8b401c2da000b316b000588b4800,0x10001c0ef8003b076c001d63b2000ea1d7000730eb8003a4740e7042080754001c43a6000241d30006d8e880036473c001ca3907181a03239a000e21cb0000e8e580036c72400038392000d91c7000708e2800378714001c037c0a0131c30006d8e08003646fc001ba3700700d1bd000080dd8003646e4001b436e000d91b50006c0d980000c010d880035c6b0001aa35e000cf1af0006b4001a834c690d11a00d86ac00076352000c31a70005d0d2800,
  0x140486c001f4432000f82170008490a8004148540021041c8302221300080908800090844001f441e000f820d0008210320406c82c002024120001d2090007d1038003e081400200406000fd2030007f8fe02a402000fa1ff0007c0fe8003f07d80f1fb0007d0fc8003e07dc001f23ea000f81f30007b8f88000107bc001ec3d4000f41ed000770f68003d6000f31e43c4780ef06c0d47a4001da3ce000eb1e5000710f18000e878c000723c2000d91df,0x14b60012c8004ac950002524ae0012a8004a09392624a4901b92980048c9440024249e0011824d0001d1268000e492c00228492001222470009092280048090c002384860011f23c474111208004608fc0004847e0002323d0008a11d80046c8d1190364720001d2370000e11a8004508cc0022e4620011622a03c8bc0002045a0011422b0008991480001089c002244440011022500088c0021e4388690c2160b88840006443e0010a21d0001890e800,0x105e0014e83b53c0014da975380014d299000a68118005260b54c00052ca540029602e0014982152800149000520a3c0028c0060014580051200143a835140013da88000a19428004ea1dd42000504a04002824fe0014127d0009d432a8000099c30a7e00097c2fa7c0009e93c8004f49dc002750a69e00025f0a29d8002740009c9388004d89a93426f000999368000709ac0025c4d20013226700098930265000081318004b89840025e0009612e800,0x15be0016eadb5bc0016e00d000b68018005b20016b8005aab456c00059ab58002d45a6001658775a4001682cf000b402b80058a18567000594001642c7000b0d60ac4000b0812800580064002be57a0015d800572acd5d000570adc002b856a0015c067000aac3bab6000a743aab4000ac958800564abc002b255a00159055000aac32ab0000a7430aae000a4c2faac000aa8002a854e00152aa154c001522a3000a901e80053a12551000540a7c002a0,0x1634c618b03263a0001d31b0000e18c800614c5c0031361ec50003126220018682d6200018701b000c300030960ec28003086160018330b0000398480061003c0000460e00183005000c14003035fec10003026020017b8776000017f2fd000bf97d8005fcbe4002fe0aa0017b8655f80017a8635f4001748615f00017b0005e4bd4002ea5ea001782ee5d80f81e2f3000ba1788005c4bbc002de5da00173ae55d000173023000b900c8005c0b8c002e0,0x1000d58278006a8d4c00351696d480035069e001a834d000d402180068a125a700067211da6000694d240034a68e001a5035000d141db48000ce41cb46000d0d9fb44000d09a280067cd1400342682001a1029000ce416b40000cf19d01c67e0019f01d0000819e800668cec00338000cd99a800664044000066620019780065aca597000658cac003230eeca80032864e00194325000ca02c80064218d9300062a185920006440018f321000c7190800,
  0x1714e4c00390032001c638f000e31c5800712001c3b81710001c3385000e19c18006de1d5c20006d61c5c100070016c0037e09a001be37b000de5b9b7a000de1bb8006f0dd400378086001bc03d000dbc24b76000db423b74000dc9b88006e40d40036f076dc00036c000da1b58006ccdac00010014da400006004d9c00365000d8c003616b6d90003576c4001b035f000d81ae8006c01b4003450ead78003390e6d700035a6b2001ad05b000d1430b58,0x10c2f30003ca792001e3bc3790001e33c5000f1820800782125e20007840dc003c2066001dfbbd780001df3c1000ef81580077c09c003bc03e001dc3bb000ee1db80076aecddb00076803c003b200a001d880075e001d6bab760001d3bae000eb034800754ea4003aa0ba001cc861750001d23a3000e85ceba2000e81cf8007400fc00399092e780039c736001ce031000e641db9a000e5dc8b98000e59cc800728e481502472e001cb02b000e39ca800,0x1000fea008007f8ffc003f87f6001fc8007ee001fabf17ec001fa3f3000fd0378007c61d5f90007e0174003f00b6001f73ed000fadf3bec000fa9f48007d4114003ea086001f18497d0001f33e5000f981b8007cc0d4003e3076f90003e17bef88003e0056001f0029000f780f8007bc074003dc7b6001ecbd77b4001ec013000f60088007ac024003d600e001ea8007a6f3dea0007a4f44003d20de001e906b000f043abd0000f39e680079c174003c1,0x189d132254488a60022345100110a278008811340005e896002194490011122380088910c0043a8820021f43d0010d416c3c0010e21b43b0000821c8008650dc004340010c2198008620021642a85109a1242f0001921680083d0ac0040c852001ff427000fea128008440021041f00106a0c41683a0020641b000ffa0c8007f505c0041282103a0a80081904c003fe822001fd40f0010120680081101a058007fd024003fa80e0020140080a001ff403,0x18ee0022b475000f74003b9000e3400337000b84002bf000a440045b000ff4003ef000f2c003a5000df400355000b24002a90009cc0046d00118c00445001084003ec790e89bd352640bd1632a64e0001f13c0730db9a23145d0b114e266000f69db38a6d4cd1852de578a392e0008e600238c6f8e40023806d0011b82d8008d91ac004698cf1a80046606a0023201100118a308008bc0c40045c0320022d45900115e2ac58001158058008a800c00450,0x1000d0e548005852a40034394e0006eca7001292514a093d2724d49892d2524949091d230000ce1af28c0028d52d2840025f4c927c00423809274004608bb26c002c4583264000d01af25c000d792a0006bc9300035e4880067f23c0022f91e0006bc8d00122a4448690920a4047e8f91ea3c4768e80022ac569120012fa5a90e0013aa5a90a001bd369906001a23339020006f8ce9020022c4578fe0019a3338fe001b4c7d0004f63d8006d31e400369,
  0x15bcbae668004508e6668001a039e668005d732c001cd996000a4ccb00039e658006953240023999200175cc70008e6638001cf31c0023998a000a4cc50008e6618001cf30c004c097d2f25d4b896d2d2594b095d2b2554a894c00160ac297e000670dd97a001983439760003c88c976001dd3bf972000db1c397200211c0a96e0022143f96a001a934396a0022043f9660019a343962000680dd962001a1caf000376578001bb2b4003439560006ecab,0x15e73b4001c43ab3b4003346a33ac002284833ac003519d2000eace9000bce7380048339c000ef9ce001a8ce5000906728006a338c002419c6001a8ce1000906708009bd3726d4d89ad352694d099d332654c898d312610007c0f9e6e800686d2a6e80067ed2a6d8003787366d80076af0a6c800666d2a6c8006cedca6b80060cc766b80044c8e66b800672d2a6a80036c7366a800847052698008d519e688008c117e6880068ad2a6780038873667800,0x116343c0008e1634340007c16342c003a6a12001ab5070002c68280059940c0012ba020027f4fc9f53e27b4f49e53c2774ec9d53a2734e49c5380003c278f3f40034a6a33f4003bf78d3ec003977413ec003436a13ec001c23ab3ec0008c13f3ec003917413e4001bc3ab3e4004658d13dc002dc5e73dc000ce1df3dc003306a33d4002264833d4002e25e73cc001b63ab3cc004238393c4003c878f3bc003526a33bc003997413b40031463f3b4002e8,0x1a7e001a535ba7e0021fc52a7a00160ad0a7600067101a72000b019fa6e000b319fa6a00211c2ea66000c319fa6200101221a5e000ba19fa5e000a3159a5e00090137a5e00068101a5a00080d2b0004069480020349c00159a4a00080d230014828f51ca354628b514a254428750ca1542283504a05400003786ff47c003516ad47c0039d74d474001282574740008c16346c0039174d4640007a16345c001122574540025f4f544c002754f5444000a0,0x1ac5582af55cab5562ab554aa5542a754ca95522a30006b6d82b48004f4a1eb38006a2d82b28004dca1eb1800686d82b080067ed82af80019c436ae8002c06aead8002cc6aeac80048c94eab8003b47a6ab80030c6aeaa80068ad82a98001a0436a880021b53c0010da9a00086d4b00056ea480021b51c00544a855029f53ca754e29b534a654c29752ca554a293524a44001ab35ba86000c919fa860023446fa82001d03aba82000ea1dda82001e13cf,0x800ad751690cdf98329645800ad74867fcdf98329645800a8b4867fcdf98329645800ad55a2b3564
]

set_option maxRecDepth 100000 in
def formula : List (List Nat) := decodeF (unpack 11 formulaWords)

set_option maxRecDepth 100000 in
def clauseIds : List Nat := List.range' 1 837

set_option maxRecDepth 100000 in
def proofWords : List Nat := [
  0x29d04cc000194a00d204e09784a400017c9f0d1c4c49a44b8040174d84d44de68c2584c22544ba2504b224c0004c44ca68a,0xab634e1592aa1560000652b034d1570000342f9561a60a500001a0b4a60d2c51ca48518000084a50d284f80000d0ee508692274,0x43b9951a98cb9860ca8000169881a90c500001a1dcc00d44614bd8608000194bf0d405b8b285a80001dcb48d3c57c0000d0ee,0xb6c1d50000473743581c8000034399ae1ab8de80001a11cd30d586e00000d07268c6aa36467035a00005a6806a834c644340000,0x149c81a48280a47a84e49a80647885649e84a4988024767fe47483e4947f64727fa5028424ea7f247000085885e6b23b2,0x297110c96d0cc94d1149d8000258988948a66b84b08684a800005a8786b64ae86e4aa8664a68624a40008708766b44a2852,
  0x2af4594a3c5149744a0f74a24ee4a20e34a1ccdca18b84a14afca10a44a0c001a36d46146ba4c48a24c289e4c08924ba88e,0x18ca8fe6c05208b24cc8b65040008ae8fe6be51e66a35866e50c0006668fe6bc4e47b644276e40a7163d266a3585be2ee,0x140876840676440401c32200831e61032660c3246146ba6d63a86d23a40223566666bc0164c88ae6be76e40a772510000,0x152e90a52890e52a4e82664bc2524b624e0009149109049008fc8f88f48f08ec8e86c45266f63c06fa4fa0006d29066c2,0x1010da8086e611125800373291289281279269261259251249241239230d94a88002934c893e6c85408c24d28c64ee0008ba9366c6,0x32e4da4acd10c96d1149d80010fd2d4da0ac8d4c70cd549f0000d0d2d4d9cac00410b6869626cc54a93a54280a47a806478,
  0x575a669b595da5b95a20592020491fa0391f0201173012f92f12e92e12d12c92c12b92b12a92a1298da8ad8eec8180011d77e,0x6662652642632622611b796900058ad29354db8b3d1ac9b51b49e000119d344db4b38040ff8be9a26d85965be2ee5c250a000,0x102094b514ef3712e90104a5a8a759b816e26996820a922a0992200458f04490d00c8f103c908141159bc9b89b49b09ac9a89a099c,0x33f13e93e13d93d13c93b93b13a93a1399391389380dd0bc8b8c5e0000d35e69e66e65de7924247964fe00078e9de6e45dc,0xd1f377311010045cea8e9bb1871d38ff1d79000001c8a8c9ba980a7897820e924a0d92400414706491d00c8f105c918140a39fc,0x2500ebc800d8c73cb5c5c8a245089d04cc00267a40a3ca38a34a30a2ca28a1ca18a14a08a006f06246ae39a6c639e0006a2,
  0x128ca5e6f46342000c82200cc21e0c60001a0a5a6f2628a1260ca0e60aa06606a22614a2661674e3fc6ae39a59a2e04f6,0x1a626fa63c44020e44821044620c000404a5e6f863a33c17a35c17e35a1780002e8a5e6f66382b011a2bc11e2ba118000,0x11cc3d61c60003a8a82704646040538ce539381322020054b029b9c01908100465994d4dfcc8108892c0010b94ccdf8c7c0802b30c,0x86615d08c0001a6a22a12a029f29e29d29c29b29a2992982972961c29960082aad6d50ce10cac08041324a867066503b81c83d8,0x6ab9c419a8d505f00c20b554e1cccc43019406147aa270c65aa4a62ca4e62ea4662aa52630a566322b011a2000c82bc11e220,0x10ca03091d5d38c3391aa0be01848ead9c599c0d505f00c247564e28cdc94849095849495448c00091955ce24cd87a0394040b53b4,
  0x2cc85682384301940c0f9ad4ad0accac8ac4ac0abcab8ab4ab0aacaa8aa4aa071c67e4f628051228400050eace71a674218,0xb6a35d30b38f3db2212df1773dd289000d94689c81021d91011da101814ad20458561671e682a9265ea9a662a96660a8e65ca9e,0x17ba5120002c672200201200002a00402643e02243c7b24407ac43800c3a20062e85b62ec5b82ea01808019c0826cc3a6,0x87f00e07d3922a71552a927a00008e0a139300a00190532a2a13180100483d00603c005808c861f4e481602f1202c01227b6442,0x12c800019a11c72804013804407a2a454a2a854029e05c03812a03613c04812c04613603c12603210201e13203a122030,0x22ec0cc29409828c09430c0e02dc0c03140e42e40c43200f82f00f4284e4c3040d82d40b820403c2fc0d42cc0b402049576,
  0x205021404420403c2cc0b422404c20c0400206b00019a14056472a0740ee69c18c07656e2c40ce2c05722c65642b40a8068,0x106217807a0aa2b40c22b053829a53429652c29004402a02c02411802e10c02c0ca69a11c7285622ba55e2b816a05c116,0x96007734e07515e2b71622b5161000395ca86401f06281c82c0d2238e503040d802075010728081d40c1c20007172c06816e05e176064172,0x8cd39801a03b14e09401c09602329f15002f14f0581f4501cb0471ca04980c80c0f22440600e0ef54072e07618e07418606e0ce,0x107a2a453829a52c29002c02454a2a813c04810c02c54072e14072c53429604402a11802e11c72813603c01035808854040d60c211,0x44a8b38498d085a8ca8570b784b8b484a0b28490b19c88d505f00499ed94740003e953a30c57073203e0922a21380445462a6,
  0x2d6471c16c718d6c738d807281b02ec6742cc6a42e819401c1dcd386942dc0614934e17233616434616c32e15e2e21302d6,0x26a4c14634b645cc004451fc1f41f00ee73436e68436667c36005013203812c2e41362d813468a38a2e81620c0160330168,0x14247463f26f63c06a638658e2d254e2aa4e22642200cc7de5007964fe74a4fc6fa4fa6aa4f85924f65524f44e64f265e,0x12d864e34a5f63106523505fe3185a22e265834e6043165a82de6546a66006a25a469e1ee0ac1a27202000c87da460792,0x8611580f905705f34c008d7d568ad9598b195c1cc8742c71cc9c4fdc8dcaec5900415b7364e85ea3086423440c40b41f80b80ae,0x10e816e3481767e646a0da4de7ea46c8e24e07e04628dc4dc3521740b41680ee73433a1661fe0b60ca69a3321601f60b0,
  0x17da4607de50000030e2e873a36605013268636e67c3600301e8182d41417a000d105d4e70898f80890f788880a1877c64662e8170,0x40811661cd28e7829060829410c8b0fac8bcf988a00d02805ec27c61029c5f02986042885e427459c24c5fc2845dc27002045,0x137e6a238469473c30814e302144010408080fc0937661ce7c2785e82805f02980ec6e4d10e705d0e74d246f00d46e8020412ee138,0x8b03591c71980b405b1c619b0b218739f1970af1670931950ae00813c11022d14670d68e8028c6082941246f80204b69e382086,0x2084e885ecb905e4b985e806011035410c084d28a54524a5c0043553a73630e73e1a60841a27200005d01ae04674238a0c0,0x13a051628644620c35a178001b2b4521c0f00742fe3a4051b0c08d9601ce8c534a68530a58524a60d2ca50d280b000c020310004cc,
  0x116c011778084848182e8041bada07500677f44020e35417c2180ca7b64428b24cc44821035c17e2200cc7ba5128b65047624026ca,0x24007fc3bc7d43a885c3fc7f43b87cc3a47c43a07bc39c024874f5c880f60878040748087373a200e74634e17230e73e346,0x24fca10d241d82e81ccd5c6a02ecd7472c1b4728d84738d68e8087c410043136a020e0be2120c01e60a85fa31234a16e432,0x4fe8340311c80f5808352e8842c18499c4e49fc4f04141783d41543581203781641801603e8e680036368e4fa27650628250c,0x174834a16e0709c8190d404b3ac146346b42f00418174a1e00563dc4001e472e3e24042027323f443420a7523f80ba3f67563fe758,0x400232a084f4a10d24a00d201d801c1902cc670e80005a53986bc3920e874a010ee80819dd3000b0ad68e800c5816a26023166063185fc,
  0x16a07503f07403ec7383e607c0a206009a1dc0a61cc0a41d209c1c20941a27207463f274a4fc0001d81d41c81c41e274e,0x23b41400ec0101246f8d3c7043ac13c11cd58d3470083c3e481c3d07d43a88343e08143cc2a2130511d80891df691800449e0040768a,0x175245e7d445a7cc4520881f806c1ee4241fc4141fa42820643874c1e274e1c609607200c09400a4121ea1ca0984221f4,0x28003c87e83c48083ecf8c8ac1203e88403f0fa48b81148b4005294520304e808374ff8778fc87600c1aa7f43b87dc3ac540cd41042a,0x200de32a80ee27c75827a500690041948070008cc329d58a494a1a514b80088aa60d2c0844d04275444c7c044a7bc4460541e003c1da,0x268cb3c5b49f44ec0679f506282033cda8613f019e5d421a48a083f0ab84500075aeac50c1fc00339754010378d904500903405be6067ab516286,
  0x54b8a69890cc14d0a61881a900020611836811c09459cb0c5a0b00598060110370124358120b145acc546840e3c164a3480b2,0x8088cdea90d80caa27ac38c003cfa8a9be68a0c43ac75a1162a61102a210e0aa30c29e10c28e10228a10003632c02e29061e332,0x16c239c3b61b443a2042aa1126b47403ca1c03b21b20129c80862d0c8800044be02549011319195141caa27a03946a82f8065513d81cc35c17e,0x5840c813e89d80703e1418a089e03e94309f89f1d6004aca6a02ec78c3786942dc7843741d47241ccd5cd7c730025513ce1c2,0x178242643420a79a42a0ba42879e4347a442e0d41c43be1b83661820c00b03621801f473400a31c1f20ae60e3280be68e,0x2cec6b8021bb01a3ac5926600a90da98e180435e034758b650401523b5527c3651d0028aac04336d14c741893eceb882cef8824ef081c0c2eb202,
  0x119407e19a73011602810201e11202601610d5938a03877ea89c307082500c61f20cd851f4a391e4a311dca2c061bb62e33461671e,0x43d806a4494b22b932aad9c596d0ba1460a203c00422a1319988d50b0848004426a74e6d554e1c0220ba1660ea0a608160078,0x4047a68cc43c8a442889c424022578fe6c0aba7187b043c6643568c84d419e0800203a401a2eaa2e61a8ea5140164c85ba2ec,0x2ea0d68e80d086d8cf86d46742cc4d41dc0226b4da2608824b493e6c84ce25a8766b44ca68a8724ac67a35e4c625623a0d8,0x21b47283c0e9947cddcd2c7095a4d00d847392ecae12d4d9d2c4d992bcab92acaad2a4aa529ca9d23ca68022732660ec6a0,0x10726aa0ea3921cc0a49b65b299e59a9ba5b49b25ac9aa6dc99258869237868e376aca67cac2678abe676aa66686be398,
  0x14de68c06009a35017663633846e2221ca0986323364d625e46a2201c609634a16e99a59299658a98e580986578076372,0x6b39c69418a082090789e03e8149eef1c845314af9474dd9344db04f8eb00a4e37844182901047383e68bc4d00ec17406433a,0x2eb46cc3044541a0025339bc6de3621802260ce1f47349ae5a800a31c25e0e8051b180944d7c8c3804a1f1eca340381f006507ac667a,0x325ca79254a7524ca71244a6d234a6008ce8406011075036073c3486d43084b41cc46c1ad204a44065435d230662a3423ac,0x111e02e97e57493253e5862d0a326ea9366c63a21a611a02a5802cc7203d68b84ce36e1869146c495a55897a572946548,0x86e11f06d4a436501b1964a12a300971e59958804b870f8964025bf8786b605808ca1e6121b408ea1a61014272604a2cea3661e,
  0x1712aac71cad66880383629806d497256a3845f677e5fca406f0a2a618a026042540f22700f62760f426e0f02620ea242,0x6a29d79120140649f09131ef1110139040e08640df863800f26350748358fa48b810c8b00479322447023048423448823648c,0x1032568a92c41c96a2e4b94a424844020e0125a8092e40ddfad4c70c958494890420024ad0125881bbe5aa93e1fb91b81c95295448c88c41802a0d6420c4,0x67297127197027096f1a58e107497a87c4100a4b90125e8193041498a06c4f49223846621e03623a2910a1f10e82271091ef0e70192845c94a0e4a9,0x10126c809374049ca9344786942dc92c47539cb8d3dcbd4124d5013ce8ee05307933404eea024d99fa5fe9ea5e89de6e2a3e6ee9d66e09d25ce,0x19ae5a808241e0132c8099d4190ce98d8ce18c8cd98f0cf98e0cf0fc95b3e4be4464a9112568292c40c96a2e4b9054e08393168e9bb1d08fc024992064d1,
  0x10841ac4021e03a61aa05641238a19677e6d238656a9706d49826849fc6e89da5d89f675c9e65e23a81b03ac75a9bc6de,0x17602424a024448e23649e24048a2340de4684862307ea46c4722247e046406e4520b820a7ce45e4362027d44584061e4,0x143c0324980926e2b932a9b9c016d0ba22a13180d2ab4c4df4024a7a6a6fe07265d2d37900931c2613e1e4df0d27180a644049de044f3a8868a3aa364aae,0x17086c239c36e186012439cf0d21c70cc1b50c253337e42f35942d25002ae862692fa2092d21d9ad21c92b01c90e2248ba727027b0,0x808fcc781d300480e87440c1d82e8854ea40240b4121ea39619e1ca0980347481908e9f9930048860d46e80291d3a21a639219c696384a86,0x61e1ad80db734ecc90b0c5a00237b056d8808f3e299ae07d1cd1cf8fba2592f07c82b9d08fc02f9a39ce0f98047be0c0134023eb1cc0a4,
  0x120aa5e6f84362024061e4402008d7b971f13991f5009ec434f6a022fb7844180641a23981ae3ac1b23b01b43b4710a7a64a87c4b2,0x1037e681b8e415c7a322b705606888acc2c56e7a03940a2b76a63863d81cc05161b5527c3d521b009ecc0458e7ac38c042c73a87626527543f6a8070a0b8,0x1a8270405820d3d32503972c1c4f6170310513dc4b25e01c0a40e05a070310381aad234f06b994f3870a9f99300cdce76c368062a701732808a8ceb86c00c556162af,0x98e3d321a3071943ce2153081903cc21300e07c3c020b13c07d00bb049f03f005d7a50020002eb92881024046f828c6f4a5c70a,0x20652343a20601147b4b1c22153a935a3a03503a821b1012090f60c94dc06192022934d2a585954c38ab6808ec800f313bc1c43621800d642e00a,0x113149858a5c045360229f01151808a9dd08fc03b05d1ce0f98d405d8180268d285b87282607182587302903a8e4804a5e1704143c0e980253b,
  0x5c004622f4c4df42f113a6a6fe09887d2d3790e904e09b134058a20a22901dad80b1641444a03b5f0125684b184058cb510ecc7eceacca5500e154bcdf00250f,0x2be461c2b5f7052de81b19404632025b50118c8196d4358e2d8473822c7d0d640808b440591a1655d0589f82b1f4a183f88e836014a8a02c79012a0839fc41623f4e4e043311ba6e,0x6a19c22b49a000e5ee750ec4f4c868f38855300da8f3084d2e4da4f00174df764aa6668035fc8198b46d7eb4ecc900f09f055fc88b0041d8221e5cd,0x5cb0f700b8a42b39c6a7c97c9cf8fb81f8fb00db9202ddd06009a9865781cc0a41e074c43a20642a7524121ea4d625ea7e64c,0x94637a04604f001c55948750289d50fe0768282769769d40fd005cc358ccf53ecbf41247d4e607c406e511dc0a64de68c0de430,0x86d1b50c211b06b00b82405c22014638c1c651228d88c2064002e312780fa27c0fc2801009ae5aa6e63be6f03ba2881026e86b0,
  0x26742cc194eac1fbc10129e8146cdda01998a90c4608e4afd310dbd37cd0d5a8e3814d49636aae7609fc6e89e65e22420dc36e18623e,0x2b249ecaa49e89cc9e40a5c7035388081e5019da9d78318d11938d29948d41960d39951a98046326942dc1d4724d7c73007c9fa88766,0x434b7e023eb012dbb213b45443b30096bc047a6272390f582a8c92454bf6bbc5f4bb45f006ab15c62f0056b281979d638b49538aa9388990f6073025aaa065d3,0x40f7f6bec6203e5fb015de80b914e486681cbef3dcbd93ccdcd39cb95334dad32cb2131cb08024730f2eb81b815790c09750c0004876265c35e84e8,0x28680255761032013920bce2154ed2eb2f117e00946c048d6066237984260330f8e605213c07d00985c781d309f1d607d1cd00e70a032290c6308,0x15f43be1b838e1980198682c0463781db09e02100943c04cf60f05fc0250303337cf92f903f1f600518e05dc1c3590b80cadec1c6500a6537a6,
  0x3304ed837878838879c38476c36802e093ae1ae39a1a206610429257c002abb420bca96601b502654335cb553f8dd0066a36e63be9f6,0xb6b4c72c221d1030992840494a854ea4d84738024cd016c38293b5019da82ee4f27cd90994d140f7330155ea170ff02ab05b49ea0373b1727880dc9c549da23717,0xaf117e0092a41d5a2064b50125c8e92f41f8fb014972023b909b7b86f2340760ba008fd5fa91b0d405d8730291f811901d51a3c0e981704140a48d99a,0x2de1474dd80668d9965900f370ca436548f29a0790d4155ca02441012268191840c8db35cb540a4716e63be0323a8291e5bc0ed81c90a0f05fcc206401a499,0x8090f41488a024490f238849205100838652e68904203696f60a31a038a881a5bca61db8353d2016ef9f65f413c0429da5d69146c49025229f25f2a40,0x1011ec838f74247c2063e9051f8828fd4147f20a4010d642e01202bd321a009025e710a01d136164050520682a31c2484a168eb03204a033b54c13b63421b602c6145e3121318d,
  0x101cf4cb32b143e2591b70c343c35b00e084160230d986086d0238d88600128b38028c725f95d1618b41838ca1600b300478a02857,0xb503a82f4274009d050d88080465e530edc027351119381f9d434e720273d29189a39e542cf32ee03847983881479f10a3be1b82941063c61be38a196,0x26e40277d42a75299658c98a57c0175c808cec1cef20277d4121ec2901080b1b3809cc52588e8399ab9ae8e5805cba8d44400e4d5402303696384,0x12fc0de4687ea46c7e04641e074c011a59d10d3018d1ce78690546860a347271a5818d3c2580e0236f0b820a43a20649a23c0ea39246e222076,0x17ce45e7d44580841ac05d689d40d81cc0d700f6a40a1f676c0f05fc0fc7d9344db0e847e00b16b3a61aa38a1961cc0a438656a5e2,0x26642c45d4e70d14ee007101336164011ab9970af008d4cca85700e1ea6782f41a38b35c17e0d1cfc7327100ace40075e18cee4126c522406e452,
  0x8bf0191c63993880f70e000e53aa06e7744e86423445ea30864e34a5f6310014a680a564052d20221b0da4de8e24e08dc4dc0b416834a170,0x13326843686243306806a86206a403c1d87eb4c7d1cd0675b6220fd031ee9bb0c5008f940593222b932a2a13180486a220d9032168190c4041820644935c,0x4e88698de8630db8618e78690dc8620da8610d98608d886000670ac206400538d7582aa1120c677203a36003632c67e36e61e,0x11db598d86553389680595a084ea8a74e6c2a27b7463f235c17e74a4fc03159820715f21e21b801d9dd9069e19089e3107820013ae600301194,0x14e27ee46e7aa4367123d001093836f85269de0fc1d00fb9ce0fa1cf0fa9cd0f91cc1399e09071b78eb1f191382400200d7aa021a5,0x48590b87f8fe877034e660407480e315130b7849d0dca8f69c98f6110083804296f6c884e3c7a8e2c7a51649980676771a50e8b65048e6,
  0x5dc8147120f88f290f1b851e63f323506d26f3871e73f52364712703801e23f023104872d0f88202438e8b4430067373fe1de3ea1d4456,0x14280b820a4362027323e04061e472e3de4021e005644a7c244c7c64667bc44603c21a45c21c46023e0e823c43a2040c6,0x85a0b403980d2488e11488511388483c3c6021eb010f78187cc1f78e022078b24cc03debc5b28200a66c0b7ee908ef4858f44864f009ccdbc79001803,0x2460908ef50e62746621e090888d982c2d4720630101301809b24041e2025fb0136a8497dde31df018db6934ef0068bf0de4686c239c7ea46c6b438c7e0462,0x144620c011129cd3bf11223711123511003b3bb0393553711d83471bb3e522a0024c4ee0015f26fc068f106e77478a42008241e470,0x1012bd84f1c42791372771360495bc1595e0225d8d64da6ae39a4f6280052a782b2cc044831b49e11cc9c4d8c73c0a53f5122844e82664bc252,
  0x107faf82fd8e989be8045d263c2ac1b48114e04e03a3ed3537f038ad4c48540045634b4de42746d32215815e0563161521520500a626a0a2268,0x4068520742d2541bd4338305a0b41930ad52f37b008e64c685524094900472207f6303a5e81fd6c27ebe0263337618a23a0d807315a3b11301989c3692a33f5b,0x5bf0f09a01aa00f0de1300b003f0f15a05403f858ab0294a92a80251674bb2b70afbfe58957a57956a5695625595525395303f15e23ef3,0x407c8e4641a871c3300249925a0e62460de2360d622e0d20bf17bb420300f8ac0c8ea079ef0123680d1059f8db80fe472d4da12ccac4d086d00786f,0x666965264961a63960a6295fa6195ea6b96992008c804992134c53961a02620ea24e0e238a19439219c2420dc24a0e037a18c,0x17864229aa5a29b65b099e59899658e9f25f09e65e29da5d49d25cc78c77c9d65d09ce5c89ca5c29c65be9c25ba9ea5e6,
  0x16f23be6a23847d645e9a26da8d24d86e43ae6943747cc4508cc4d6a3a6200681a22520e49b25ae0664189fa6009de6e4,0x17c645646022c09022a47c22e47a228a406f09fc6e808e6aca3e6266ee3bc9f65f869a3807d245c08a45aa826549ee5ee,0x16d477c4149826847804e6a8870a7323e09bc6dea7e64e72e3de9ba5b6014558042fc7900d167290d94f7888d23ca64028af6de3b4,0x284c868414f3485417485002a2f053daa7d13b28314128613f0390bc4553686440003e1f01a8583f86c74f82168c7052ad82ab4c055ae08aef79c7806d2970,0x13501767063ca6ba396015e5b611ce00af2dad0e30fde5a7a039406f2901b5580857c05876d947400693102b679d63c120b00f7ec07c9603e63404202782,0x2efc0523978200078406acf86b217002fade0002b563286f43186e4310ae92d3be1b63c21ba0ec1740e23c60e66ae
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma contradiction : ¬ FormulaSat formula :=
  check_sound formula clauseIds (LZPacked.decode 11 proofWords) (by decide +kernel)

set_option maxRecDepth 100000 in
def originalFormula : List (List Nat) :=
  formula.map (List.map (renameLiteral (fun index => variableLookup.getD index 0)))

lemma original_unsat : ¬ FormulaSat originalFormula :=
  unsat_map_literals formula (fun index => variableLookup.getD index 0) contradiction

end CaseB07

end R2CleanKernel

end PEqualNP.Outside.L_meta_9033
