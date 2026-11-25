import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

namespace StarContraction


def hit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def pair {n : ℕ} (a b : Fin n) (i : Fin n) : Bool :=
  decide (i = a ∨ i = b)

def rootOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def rectangle {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  rootOr A x && rootOr B x

def contract {n : ℕ} (c : Fin n) (B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  x c && rootOr B x

lemma hit_pair {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    hit G (pair a b) ↔ G.Adj a b := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [pair, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.irrefl huv).elim
    · exact huv
    · exact huv.symm
    · exact (G.irrefl huv).elim
  · intro h
    exact ⟨a, b, h, by simp [pair], by simp [pair]⟩

lemma contract_le {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A)
    (x : Fin n → Bool) : contract c B x = true → rectangle A B x = true := by
  simp only [contract, rectangle, Bool.and_eq_true, rootOr, decide_eq_true_eq]
  rintro ⟨hx, hb⟩
  exact ⟨⟨c, hc, hx⟩, hb⟩

lemma contract_agrees_at_center {n : ℕ} (A B : Finset (Fin n)) (c : Fin n)
    (hc : c ∈ A) (x : Fin n → Bool) (hx : x c = true) :
    contract c B x = rectangle A B x := by
  have ha : rootOr A x = true := by
    simp only [rootOr, decide_eq_true_eq]
    exact ⟨c, hc, hx⟩
  simp [contract, rectangle, hx, ha]

lemma extra_root_dirty_witness {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset (Fin n)) (c a u v : Fin n)
    (ha : a ∈ A) (hac : a ≠ c) (hu : u ∈ B) (hv : v ∈ B)
    (hcu : G.Adj c u) (hcv : G.Adj c v) (huv : u ≠ v) :
    ∃ x : Fin n → Bool, ¬ hit G x ∧ rectangle A B x = true ∧ contract c B x = false := by
  have hmissing : ¬ G.Adj a u ∨ ¬ G.Adj a v := by
    by_cases hau : G.Adj a u
    · right
      intro hav
      rcases hfour c u a v hcu hau.symm hav hcv.symm with h | h
      · exact hac h.symm
      · exact huv h
    · exact Or.inl hau
  obtain ⟨b, hb, hcb, hab⟩ : ∃ b ∈ B, G.Adj c b ∧ ¬ G.Adj a b := by
    rcases hmissing with h | h
    · exact ⟨u, hu, hcu, h⟩
    · exact ⟨v, hv, hcv, h⟩
  refine ⟨pair a b, (hit_pair G a b).not.mpr hab, ?_, ?_⟩
  · simp only [rectangle, Bool.and_eq_true, rootOr, decide_eq_true_eq]
    exact ⟨⟨a, ha, by simp [pair]⟩, ⟨b, hb, by simp [pair]⟩⟩
  · have hca : c ≠ a := Ne.symm hac
    have hcb' : c ≠ b := G.ne_of_adj hcb
    simp [contract, pair, hca, hcb']

def dirt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => ¬ (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧ f x = true

lemma dirt_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f g : (Fin n → Bool) → Bool) (h : ∀ x, f x = true → g x = true) :
    dirt G f ⊆ dirt G g := by
  intro x hx
  simp only [dirt, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨hx.1, h x hx.2⟩

lemma contract_dirt_strict {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset (Fin n)) (c a u v : Fin n)
    (hc : c ∈ A) (ha : a ∈ A) (hac : a ≠ c) (hu : u ∈ B) (hv : v ∈ B)
    (hcu : G.Adj c u) (hcv : G.Adj c v) (huv : u ≠ v) :
    (dirt G (contract c B)).card < (dirt G (rectangle A B)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨dirt_subset G _ _ (contract_le A B c hc), ?_⟩
  intro heq
  obtain ⟨x, hx, horig, hnew⟩ :=
    extra_root_dirty_witness G hfour A B c a u v ha hac hu hv hcu hcv huv
  have hm : x ∈ dirt G (rectangle A B) := by simpa only [dirt, Finset.mem_filter,
    Finset.mem_univ, true_and, hit] using And.intro hx horig
  rw [← heq] at hm
  simp [dirt, hnew] at hm

lemma rootOr_mono {n : ℕ} (A : Finset (Fin n)) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : rootOr A x = true → rootOr A y = true := by
  simp only [rootOr, decide_eq_true_eq]
  rintro ⟨a, ha, hxa⟩
  exact ⟨a, ha, hxy a hxa⟩

lemma contract_mono {n : ℕ} (c : Fin n) (B : Finset (Fin n)) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : contract c B x = true → contract c B y = true := by
  simp only [contract, Bool.and_eq_true]
  exact fun h => ⟨hxy c h.1, rootOr_mono B x y hxy h.2⟩

lemma star_contract_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A)
    (φ : (Fin n → Bool) → Bool → Bool)
    (hφinput : ∀ x y t, (∀ i, x i = true → y i = true) →
      φ x t = true → φ y t = true)
    (hφgate : ∀ x s t, (s = true → t = true) → φ x s = true → φ x t = true)
    (hcomp : ∀ x, φ x (rectangle A B x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hessential : ∀ a b, G.Adj a b → φ (pair a b) false = false → a = c ∨ b = c) :
    ∀ x, φ x (contract c B x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hy := hφgate x _ _ (contract_le A B c hc x) hx
    simpa only [hcomp] using hy
  · intro hx
    obtain ⟨a, b, hab, ha, hb⟩ := of_decide_eq_true hx
    have hpx : ∀ i, pair a b i = true → x i = true := by
      intro i hi
      simp only [pair, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    have hlocal : φ (pair a b) (contract c B (pair a b)) = true := by
      cases hz : φ (pair a b) false with
      | true => exact hφgate _ false _ (by simp) hz
      | false =>
        have hpc : pair a b c = true := by
          rcases hessential a b hab hz with rfl | rfl <;> simp [pair]
        rw [contract_agrees_at_center A B c hc _ hpc, hcomp]
        exact decide_eq_true ⟨a, b, hab, by simp [pair], by simp [pair]⟩
    exact hφgate x _ _ (contract_mono c B _ x hpx)
      (hφinput (pair a b) x _ hpx hlocal)


end StarContraction

namespace StarBypass


def starInputLe {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ v, x v = true → y v = true

def starSingleton {n : ℕ} (c : Fin n) : Fin n → Bool :=
  fun v => decide (v = c)

def starPair {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun v => decide (v = a ∨ v = b)

lemma star_bypass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : (Fin n → Bool) → Bool)
    (φ : (Fin n → Bool) → Bool → Bool) (c : Fin n)
    (hhmono : ∀ x y, starInputLe x y → h x = true → h y = true)
    (hφinput : ∀ x y t, starInputLe x y → φ x t = true → φ y t = true)
    (hφgate : ∀ x s t, (s = true → t = true) → φ x s = true → φ x t = true)
    (hcomp : ∀ x, φ x (h x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hcenter : h (starSingleton c) = true)
    (hessential : ∀ a b, G.Adj a b → φ (starPair a b) false = false →
      a = c ∨ b = c) :
    ∀ x, φ x (x c) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hbit : x c = true → h x = true := by
      intro hc
      apply hhmono (starSingleton c) x ?_ hcenter
      intro v hv
      have he : v = c := by simpa [starSingleton] using hv
      simpa [he] using hc
    have hv := hφgate x (x c) (h x) hbit hx
    simpa [hcomp] using hv
  · intro hx
    obtain ⟨a, b, hab, hxa, hxb⟩ := of_decide_eq_true hx
    have hpx : starInputLe (starPair a b) x := by
      intro v hv
      have he : v = a ∨ v = b := by simpa [starPair] using hv
      rcases he with rfl | rfl
      · exact hxa
      · exact hxb
    have hpair : φ (starPair a b) (h (starPair a b)) = true := by
      rw [hcomp]
      exact decide_eq_true ⟨a, b, hab, by simp [starPair], by simp [starPair]⟩
    have hlocal : φ (starPair a b) (starPair a b c) = true := by
      cases hc : starPair a b c with
      | false =>
        cases hf : φ (starPair a b) false with
        | true => rfl
        | false =>
          have he := hessential a b hab hf
          have ht : starPair a b c = true := by
            rcases he with rfl | rfl <;> simp [starPair]
          exact Bool.noConfusion (hc.symm.trans ht)
      | true =>
        exact hφgate (starPair a b) (h (starPair a b)) true (by simp) hpair
    exact hφgate x (starPair a b c) (x c) (hpx c)
      (hφinput (starPair a b) x (starPair a b c) hpx hlocal)

lemma star_essential_away {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : (Fin n → Bool) → Bool)
    (φ : (Fin n → Bool) → Bool → Bool) (c : Fin n)
    (hhmono : ∀ x y, starInputLe x y → h x = true → h y = true)
    (hφinput : ∀ x y t, starInputLe x y → φ x t = true → φ y t = true)
    (hφgate : ∀ x s t, (s = true → t = true) → φ x s = true → φ x t = true)
    (hcomp : ∀ x, φ x (h x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hcenter : h (starSingleton c) = true)
    (hnecessary : ∃ x, φ x (x c) ≠ φ x (h x)) :
    ∃ a b, G.Adj a b ∧ a ≠ c ∧ b ≠ c ∧
      φ (starPair a b) false = false := by
  classical
  by_contra hn
  have hessential : ∀ a b, G.Adj a b → φ (starPair a b) false = false →
      a = c ∨ b = c := by
    intro a b hab hzero
    by_contra hc
    have hac : a ≠ c := fun he => hc (Or.inl he)
    have hbc : b ≠ c := fun he => hc (Or.inr he)
    exact hn ⟨a, b, hab, hac, hbc, hzero⟩
  obtain ⟨x, hx⟩ := hnecessary
  apply hx
  rw [star_bypass G h φ c hhmono hφinput hφgate hcomp hcenter hessential x, hcomp]


end StarBypass

namespace StarObstruction


open PEqualNP.CircuitLowerBounds

def forestValue (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)

def starObstruction : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [0, 6]⟩,
    ⟨.or, [1, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [7, 9]⟩,
    ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩], 12⟩

def starInputs : Unit ⊕ (Fin 8 ⊕ (Fin 8 × Fin 8)) → List ℕ
  | .inl _ => []
  | .inr (.inl a) => [a.val]
  | .inr (.inr (a, b)) => [a.val, b.val]

def starReplacement (op : Bool) (p : Unit ⊕ (Fin 8 ⊕ (Fin 8 × Fin 8))) : Circuit :=
  { starObstruction with gates :=
    starObstruction.gates.set 2 ⟨if op then .and else .or, starInputs p⟩ }

def pairInput (a b : Fin 5) : Fin 5 → Bool := fun i => decide (i = a ∨ i = b)

lemma starObstruction_mono : PEqualNP.MetaComplexity.Monotone2 starObstruction := by
  simp [PEqualNP.MetaComplexity.Monotone2, starObstruction]

lemma starObstruction_correct :
    ∀ x : Fin 5 → Bool, starObstruction.eval (List.ofFn x) = forestValue x := by
  decide +kernel

lemma starObstruction_unsafe :
    (starObstruction.wires (List.ofFn (pairInput 0 3))).getD 7 false = true ∧
    forestValue (pairInput 0 3) = false := by
  decide +kernel

lemma starObstruction_essential :
    (starReplacement false (.inl ())).eval (List.ofFn (pairInput 0 1)) = false ∧
    (starReplacement false (.inl ())).eval (List.ofFn (pairInput 0 2)) = false ∧
    (starReplacement false (.inl ())).eval (List.ofFn (pairInput 3 4)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma starObstruction_no_single_replacement :
    ¬ ∃ (op : Bool) (p : Unit ⊕ (Fin 8 ⊕ (Fin 8 × Fin 8))),
      (∀ x : Fin 5 → Bool,
        (starReplacement op p).eval (List.ofFn x) = forestValue x) ∧
      (op = true → ∀ x : Fin 5 → Bool,
        ((starReplacement op p).wires (List.ofFn x)).getD 7 false = true →
          forestValue x = true) := by
  decide +kernel

def forestAdj (a b : Fin 5) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ ((a = 1 ∨ a = 2) ∧ b = 0) ∨
  (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)

def forestGraph : SimpleGraph (Fin 5) where
  Adj := forestAdj
  symm := by
    constructor
    unfold forestAdj
    decide +kernel
  loopless := by
    constructor
    unfold forestAdj
    decide +kernel

lemma forestGraph_triangleFree : ∀ a b c : Fin 5,
    forestGraph.Adj a b → forestGraph.Adj b c → ¬ forestGraph.Adj c a := by
  change ∀ a b c : Fin 5, forestAdj a b → forestAdj b c → ¬ forestAdj c a
  unfold forestAdj
  decide +kernel

set_option synthInstance.maxSize 10000 in
lemma forestGraph_squareFree : ∀ a b c d : Fin 5,
    forestGraph.Adj a b → forestGraph.Adj b c → forestGraph.Adj c d →
    forestGraph.Adj d a → a = c ∨ b = d := by
  change ∀ a b c d : Fin 5, forestAdj a b → forestAdj b c → forestAdj c d →
    forestAdj d a → a = c ∨ b = d
  unfold forestAdj
  decide +kernel

lemma forestValue_spec : ∀ x : Fin 5 → Bool, forestValue x = true ↔
    ∃ a b : Fin 5, forestGraph.Adj a b ∧ x a = true ∧ x b = true := by
  change ∀ x : Fin 5 → Bool, forestValue x = true ↔
    ∃ a b : Fin 5, forestAdj a b ∧ x a = true ∧ x b = true
  unfold forestAdj
  decide +kernel

lemma starObstruction_essential_star : ∀ a b : Fin 5,
    forestGraph.Adj a b →
    ((starReplacement false (.inl ())).eval (List.ofFn (pairInput a b)) = false ↔
      a = 0 ∨ b = 0) := by
  change ∀ a b : Fin 5, forestAdj a b →
    ((starReplacement false (.inl ())).eval (List.ofFn (pairInput a b)) = false ↔
      a = 0 ∨ b = 0)
  unfold forestAdj
  decide +kernel

lemma starObstruction_other_ands_safe : ∀ x : Fin 5 → Bool,
    ((starObstruction.wires (List.ofFn x)).getD 10 false = true → forestValue x = true) ∧
    ((starObstruction.wires (List.ofFn x)).getD 11 false = true → forestValue x = true) := by
  decide +kernel


end StarObstruction

end PEqualNP.Outside.L_meta_1904_aux
