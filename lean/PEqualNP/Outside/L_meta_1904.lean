import Mathlib.Combinatorics.SimpleGraph.VertexCover
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

lemma extra_support_dirty_witness {n : ℕ} (G : SimpleGraph (Fin n))
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
    extra_support_dirty_witness G hfour A B c a u v ha hac hu hv hcu hcv huv
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

lemma starObstruction_bad_input :
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

namespace StarCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open StarContraction

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def WireLE (v w : List Bool) : Prop :=
  ∀ i, v.getD i false = true → w.getD i false = true

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma append_bit_le {v w : List Bool} (hlen : v.length = w.length)
    (hle : WireLE v w) {a b : Bool} (hab : a = true → b = true) :
    WireLE (v ++ [a]) (w ++ [b]) := by
  intro i hi
  by_cases hlt : i < v.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
    have hlt' : i < w.length := hlen ▸ hlt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
    exact hle i hi
  · have hv : v.length ≤ i := by omega
    have hw : w.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hv] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hw]
    rw [← hlen]
    cases hidx : i - v.length with
    | zero => simpa [hidx] using hab (by simpa [hidx] using hi)
    | succ k => simp [hidx] at hi

lemma gate_eval_le (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hle : WireLE v w) :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro hv i hi
    exact hle i (hv i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

lemma run_le (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hlen : v.length = w.length) (hle : WireLE v w) :
    WireLE (run gs v) (run gs w) := by
  induction gs generalizing v w with
  | nil => exact hle
  | cons g gs ih =>
    apply ih (fun g hg => hmono g (List.mem_cons_of_mem _ hg))
    · simp [step, hlen]
    · exact append_bit_le hlen hle (gate_eval_le g (hmono g (by simp)) hle)

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) : WireLE (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
      (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · simp [List.getD_eq_getElem?_getD, hin] at hi

lemma patch_le (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
    (hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or)
    (hgate : h.op.eval (h.inputs.map fun i => (run pre x).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (run pre x).getD i false) = true) :
    WireLE (({gates := pre ++ h :: post, output := out} : Circuit).wires x)
      (({gates := pre ++ g :: post, output := out} : Circuit).wires x) := by
  change WireLE (run (pre ++ h :: post) x) (run (pre ++ g :: post) x)
  simp only [run, List.foldl_append, List.foldl_cons]
  apply run_le post hpost
  · simp [step]
  · exact append_bit_le rfl (fun _ hi => hi) hgate

def patchCircuit (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ g :: post, out⟩

def gatePrefix {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false)

def gateContext {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) (p : Bool) : Bool :=
  (run post (run pre (List.ofFn x) ++ [p])).getD out false

lemma run_old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma run_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    (run gs (List.ofFn x)).getD i false = x i := by
  rw [run_old_read gs _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma gateContext_orig {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x (gatePrefix pre g x) =
      (patchCircuit pre post g out).eval (List.ofFn x) := by
  simp only [gateContext,gatePrefix,patchCircuit,Circuit.eval,Circuit.wires,
    run,List.foldl_append,List.foldl_cons]
  rfl

lemma gateContext_zero {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x false =
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn x) := by
  exact gateContext_orig pre post ⟨.or,[]⟩ out x

lemma gateContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (p q : Bool)
    (hxy : ∀ i, x i = true → y i = true) (hpq : p = true → q = true) :
    gateContext pre post out x p = true → gateContext pre post out y q = true := by
  apply run_le post hpost (by simp [run_length]) _ out
  exact append_bit_le (by simp [run_length])
    (run_le pre hpre (by simp) (ofFn_le hxy)) hpq

lemma patch_mono (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    Monotone2 (patchCircuit pre post h out) := by
  intro q hq
  change q ∈ pre ++ h :: post at hq
  rcases List.mem_append.mp hq with hp | hpost
  · exact hc q (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp hpost with rfl | ht
    · exact hh
    · exact hc q (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

lemma patch_wire_value {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    ((patchCircuit pre post g out).wires (List.ofFn x)).getD (n + pre.length) false =
      gatePrefix pre g x := by
  change (run (pre ++ g :: post) (List.ofFn x)).getD (n + pre.length) false = _
  simp only [run,List.foldl_append,List.foldl_cons]
  change (run post (run pre (List.ofFn x) ++ [gatePrefix pre g x])).getD
    (n + pre.length) false = _
  have hlen : (run pre (List.ofFn x)).length = n + pre.length := by simp [run_length]
  rw [run_old_read post _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
  rfl

lemma prefix_rectangle {n : ℕ} (pre : List Gate) (p q : ℕ) (A B : Finset (Fin n))
    (hp : ∀ x, (run pre (List.ofFn x)).getD p false = rootOr A x)
    (hq : ∀ x, (run pre (List.ofFn x)).getD q false = rootOr B x)
    (x : Fin n → Bool) : gatePrefix pre ⟨.and, [p,q]⟩ x = rectangle A B x := by
  simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, hp, hq, rectangle]

lemma prefix_contract {n : ℕ} (pre : List Gate) (q : ℕ) (c : Fin n)
    (B : Finset (Fin n))
    (hq : ∀ x, (run pre (List.ofFn x)).getD q false = rootOr B x)
    (x : Fin n → Bool) : gatePrefix pre ⟨.and, [c.val,q]⟩ x = contract c B x := by
  simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, run_input, hq, contract]

lemma star_circuit_contract {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (p q out : ℕ) (A B : Finset (Fin n)) (c : Fin n)
    (hc : c ∈ A)
    (hmono : Monotone2 (patchCircuit pre post ⟨.and, [p,q]⟩ out))
    (hp : ∀ x, (run pre (List.ofFn x)).getD p false = rootOr A x)
    (hq : ∀ x, (run pre (List.ofFn x)).getD q false = rootOr B x)
    (hcorrect : ∀ x, (patchCircuit pre post ⟨.and, [p,q]⟩ out).eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hessential : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (pair a b)) = false →
      a = c ∨ b = c) :
    Monotone2 (patchCircuit pre post ⟨.and, [c.val,q]⟩ out) ∧
    (patchCircuit pre post ⟨.and, [c.val,q]⟩ out).size =
      (patchCircuit pre post ⟨.and, [p,q]⟩ out).size ∧
    (∀ x, (patchCircuit pre post ⟨.and, [c.val,q]⟩ out).eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    ∀ x : Fin n → Bool,
      WireLE ((patchCircuit pre post ⟨.and, [c.val,q]⟩ out).wires (List.ofFn x))
        ((patchCircuit pre post ⟨.and, [p,q]⟩ out).wires (List.ofFn x)) := by
  have hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hmono g (List.mem_append_left _ hg)).1
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hmono g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))).1
  refine ⟨patch_mono pre post _ _ out hmono (by simp), by simp [patchCircuit, Circuit.size], ?_, ?_⟩
  · have result := star_contract_replacement G A B c hc (gateContext pre post out)
      (fun x y t hxy => gateContext_mono pre post out hpre hpost x y t t hxy (fun h => h))
      (fun x s t hst => gateContext_mono pre post out hpre hpost x x s t (fun _ h => h) hst)
      (fun x => by rw [← prefix_rectangle pre p q A B hp hq x, gateContext_orig]; exact hcorrect x)
      (fun a b hab hz => hessential a b hab (by rwa [gateContext_zero] at hz))
    intro x
    rw [← gateContext_orig, prefix_contract pre q c B hq]
    exact result x
  · intro x
    apply patch_le pre post _ _ out _ hpost
    change gatePrefix pre ⟨.and, [c.val,q]⟩ x = true →
      gatePrefix pre ⟨.and, [p,q]⟩ x = true
    rw [prefix_contract pre q c B hq, prefix_rectangle pre p q A B hp hq]
    exact contract_le A B c hc x

lemma star_circuit_kills_dirty_event {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (pre post : List Gate) (p q out : ℕ) (A B : Finset (Fin n)) (c a u v : Fin n)
    (hp : ∀ x, (run pre (List.ofFn x)).getD p false = rootOr A x)
    (hq : ∀ x, (run pre (List.ofFn x)).getD q false = rootOr B x)
    (ha : a ∈ A) (hac : a ≠ c) (hu : u ∈ B) (hv : v ∈ B)
    (hcu : G.Adj c u) (hcv : G.Adj c v) (huv : u ≠ v) :
    ∃ x : Fin n → Bool, ¬ hit G x ∧
      ((patchCircuit pre post ⟨.and,[p,q]⟩ out).wires (List.ofFn x)).getD
        (n + pre.length) false = true ∧
      ((patchCircuit pre post ⟨.and,[c.val,q]⟩ out).wires (List.ofFn x)).getD
        (n + pre.length) false = false := by
  obtain ⟨x, hx, hold, hnew⟩ :=
    extra_support_dirty_witness G hfour A B c a u v ha hac hu hv hcu hcv huv
  refine ⟨x, hx, ?_, ?_⟩
  · rwa [patch_wire_value, prefix_rectangle pre p q A B hp hq]
  · rwa [patch_wire_value, prefix_contract pre q c B hq]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open StarContraction

lemma prefix_wire_mono {n : ℕ} (pre : List Gate) (p : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    (run pre (List.ofFn x)).getD p false = true →
      (run pre (List.ofFn y)).getD p false = true := by
  exact run_le pre hpre (by simp) (ofFn_le hxy) p

lemma prefix_singleton_true {n : ℕ} (pre : List Gate) (p : ℕ) (c : Fin n)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hsingle : (run pre (List.ofFn (StarBypass.starSingleton c))).getD p false = true)
    (x : Fin n → Bool) (hx : x c = true) :
    (run pre (List.ofFn x)).getD p false = true := by
  apply prefix_wire_mono pre p hpre (StarBypass.starSingleton c) x ?_ hsingle
  intro i hi
  have hieq : i = c := by simpa [StarBypass.starSingleton] using hi
  simpa [hieq] using hx

lemma star_circuit_contract_singletons {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (p q out : ℕ) (c : Fin n)
    (hmono : Monotone2 (patchCircuit pre post ⟨.and, [p, q]⟩ out))
    (hsingle : (run pre (List.ofFn (StarBypass.starSingleton c))).getD p false = true)
    (hcorrect : ∀ x, (patchCircuit pre post ⟨.and, [p, q]⟩ out).eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (hessential : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or, []⟩ out).eval (List.ofFn (pair a b)) = false →
      a = c ∨ b = c) :
    Monotone2 (patchCircuit pre post ⟨.and, [c.val, q]⟩ out) ∧
    (patchCircuit pre post ⟨.and, [c.val, q]⟩ out).size =
      (patchCircuit pre post ⟨.and, [p, q]⟩ out).size ∧
    (∀ x, (patchCircuit pre post ⟨.and, [c.val, q]⟩ out).eval (List.ofFn x) =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    ∀ x : Fin n → Bool,
      WireLE ((patchCircuit pre post ⟨.and, [c.val, q]⟩ out).wires (List.ofFn x))
        ((patchCircuit pre post ⟨.and, [p, q]⟩ out).wires (List.ofFn x)) := by
  have hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hmono g (List.mem_append_left _ hg)).1
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hmono g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))).1
  have hpc (x : Fin n → Bool) (hx : x c = true) :
      (run pre (List.ofFn x)).getD p false = true :=
    prefix_singleton_true pre p c hpre hsingle x hx
  have hgate_le (x : Fin n → Bool) :
      gatePrefix pre ⟨.and, [c.val, q]⟩ x = true →
      gatePrefix pre ⟨.and, [p, q]⟩ x = true := by
    simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, run_input, Bool.and_eq_true]
    rintro ⟨hc, hq⟩
    exact ⟨hpc x hc, hq⟩
  have hagree (x : Fin n → Bool) (hx : x c = true) :
      gatePrefix pre ⟨.and, [c.val, q]⟩ x = gatePrefix pre ⟨.and, [p, q]⟩ x := by
    simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, run_input, hpc x hx, hx]
  have hwires (x : Fin n → Bool) :=
    patch_le pre post ⟨.and, [p, q]⟩ ⟨.and, [c.val, q]⟩ out (List.ofFn x) hpost
      (hgate_le x)
  refine ⟨patch_mono pre post _ _ out hmono (by simp),
    by simp [patchCircuit, Circuit.size], ?_, hwires⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hy : (patchCircuit pre post ⟨.and, [p, q]⟩ out).eval (List.ofFn x) = true :=
      hwires x out hx
    simpa only [hcorrect] using hy
  · intro hx
    obtain ⟨a, b, hab, ha, hb⟩ := of_decide_eq_true hx
    have hpx : ∀ i, pair a b i = true → x i = true := by
      intro i hi
      simp only [pair, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    have hlocal : gateContext pre post out (pair a b)
        (gatePrefix pre ⟨.and, [c.val, q]⟩ (pair a b)) = true := by
      cases hz : gateContext pre post out (pair a b) false with
      | true =>
        exact gateContext_mono pre post out hpre hpost _ _ false _
          (fun _ h => h) (by simp) hz
      | false =>
        have hcpair : pair a b c = true := by
          rcases hessential a b hab (by rwa [gateContext_zero] at hz) with rfl | rfl <;>
            simp [pair]
        rw [hagree _ hcpair, gateContext_orig, hcorrect]
        exact decide_eq_true ⟨a, b, hab, by simp [pair], by simp [pair]⟩
    rw [← gateContext_orig]
    apply gateContext_mono pre post out hpre hpost (pair a b) x _ _ hpx _ hlocal
    exact gate_eval_le ⟨.and, [c.val, q]⟩ (by simp)
      (run_le pre hpre (by simp) (ofFn_le hpx))

lemma star_circuit_kills_dirty_singletons {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (pre post : List Gate) (p q out : ℕ) (c a u v : Fin n)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpa : (run pre (List.ofFn (StarBypass.starSingleton a))).getD p false = true)
    (hqu : (run pre (List.ofFn (StarBypass.starSingleton u))).getD q false = true)
    (hqv : (run pre (List.ofFn (StarBypass.starSingleton v))).getD q false = true)
    (hac : a ≠ c) (hcu : G.Adj c u) (hcv : G.Adj c v) (huv : u ≠ v) :
    ∃ x : Fin n → Bool, ¬ hit G x ∧
      ((patchCircuit pre post ⟨.and, [p, q]⟩ out).wires (List.ofFn x)).getD
        (n + pre.length) false = true ∧
      ((patchCircuit pre post ⟨.and, [c.val, q]⟩ out).wires (List.ofFn x)).getD
        (n + pre.length) false = false := by
  have hmissing : ¬ G.Adj a u ∨ ¬ G.Adj a v := by
    by_cases hau : G.Adj a u
    · right
      intro hav
      rcases hfour c u a v hcu hau.symm hav hcv.symm with h | h
      · exact hac h.symm
      · exact huv h
    · exact Or.inl hau
  obtain ⟨b, hcb, hab, hqb⟩ : ∃ b : Fin n, G.Adj c b ∧ ¬ G.Adj a b ∧
      (run pre (List.ofFn (StarBypass.starSingleton b))).getD q false = true := by
    rcases hmissing with h | h
    · exact ⟨u, hcu, h, hqu⟩
    · exact ⟨v, hcv, h, hqv⟩
  have hp := prefix_singleton_true pre p a hpre hpa (pair a b) (by simp [pair])
  have hq := prefix_singleton_true pre q b hpre hqb (pair a b) (by simp [pair])
  have hca : c ≠ a := Ne.symm hac
  have hcb' : c ≠ b := G.ne_of_adj hcb
  refine ⟨pair a b, (hit_pair G a b).not.mpr hab, ?_, ?_⟩
  · rw [patch_wire_value]
    simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
    exact ⟨hp, hq⟩
  · rw [patch_wire_value]
    simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, run_input]
    simp [pair, hca, hcb']


end StarCircuit

namespace StarObstruction

open PEqualNP.CircuitLowerBounds

def capIndex (i : ℕ) : Fin 8 := ⟨min i 7, by omega⟩

def capGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => (capIndex i).val⟩

def gateReplacement (g : Gate) : Circuit :=
  { starObstruction with gates := starObstruction.gates.set 2 g }

def replacementPrefix : List Gate := [⟨.or, [1, 3]⟩, ⟨.or, [5, 2]⟩]

def replacementSuffix : List Gate :=
  [⟨.or, [1, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [7, 9]⟩,
    ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩]

lemma capIndex_read (w : List Bool) (hw : w.length = 7) (i : ℕ) :
    w.getD (capIndex i).val false = w.getD i false := by
  by_cases hi : i ≤ 7
  · simp [capIndex, Nat.min_eq_left hi]
  · have hge : 7 ≤ i := by omega
    simp only [capIndex, Nat.min_eq_right hge]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma capGate_eval (g : Gate) (w : List Bool) (hw : w.length = 7) :
    (capGate g).op.eval ((capGate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [capGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact capIndex_read w hw i

lemma capGate_wires (g : Gate) (x : Fin 5 → Bool) :
    (gateReplacement (capGate g)).wires (List.ofFn x) =
      (gateReplacement g).wires (List.ofFn x) := by
  change StarCircuit.run replacementSuffix
      (StarCircuit.step (StarCircuit.run replacementPrefix (List.ofFn x)) (capGate g)) =
    StarCircuit.run replacementSuffix
      (StarCircuit.step (StarCircuit.run replacementPrefix (List.ofFn x)) g)
  have hlen : (StarCircuit.run replacementPrefix (List.ofFn x)).length = 7 := by
    simp [StarCircuit.run_length, replacementPrefix]
  simp only [StarCircuit.step, capGate_eval g _ hlen]

lemma capInputs_encoded (l : List ℕ) (hl : l.length ≤ 2) :
    ∃ p : Unit ⊕ (Fin 8 ⊕ (Fin 8 × Fin 8)),
      starInputs p = l.map (fun i => (capIndex i).val) := by
  cases l with
  | nil => exact ⟨.inl (), rfl⟩
  | cons a l =>
    cases l with
    | nil => exact ⟨.inr (.inl (capIndex a)), rfl⟩
    | cons b l =>
      cases l with
      | nil => exact ⟨.inr (.inr (capIndex a, capIndex b)), rfl⟩
      | cons c l => simp at hl

lemma capGate_encoded (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    ∃ (op : Bool) (p : Unit ⊕ (Fin 8 ⊕ (Fin 8 × Fin 8))),
      (if op then GateOp.and else GateOp.or) = g.op ∧
      gateReplacement (capGate g) = starReplacement op p := by
  obtain ⟨p, hp⟩ := capInputs_encoded g.inputs hlen
  have hex : ∃ op : Bool, (if op then GateOp.and else GateOp.or) = g.op := by
    rcases hop with hop | hop
    · exact ⟨true, hop.symm⟩
    · exact ⟨false, hop.symm⟩
  obtain ⟨op, hop⟩ := hex
  refine ⟨op, p, hop, ?_⟩
  simp only [gateReplacement, capGate, starReplacement, hp, hop]

lemma starObstruction_no_nat_replacement :
    ¬ ∃ g : Gate,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
      (∀ x : Fin 5 → Bool, (gateReplacement g).eval (List.ofFn x) = forestValue x) ∧
      (g.op = GateOp.and → ∀ x : Fin 5 → Bool,
        ((gateReplacement g).wires (List.ofFn x)).getD 7 false = true →
          forestValue x = true) := by
  rintro ⟨g, hop, hlen, hcorrect, hsafe⟩
  obtain ⟨op, p, hop, he⟩ := capGate_encoded g hop hlen
  have hw : ∀ x : Fin 5 → Bool,
      (starReplacement op p).wires (List.ofFn x) =
        (gateReplacement g).wires (List.ofFn x) := by
    intro x
    rw [← he]
    exact capGate_wires g x
  apply starObstruction_no_single_replacement
  refine ⟨op, p, ?_, ?_⟩
  · intro x
    change ((starReplacement op p).wires (List.ofFn x)).getD 12 false = forestValue x
    rw [hw]
    exact hcorrect x
  · intro h_op x hx
    apply hsafe (by simpa [h_op] using hop.symm) x
    rwa [hw] at hx

end StarObstruction

namespace DoubleStar

def orValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def rectangleValue {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orValue A x && orValue B x

def consumerValue {n : ℕ} (A B U V : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  (rectangleValue A B x || orValue U x) && orValue V x

def pairInput {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun v => decide (v = a ∨ v = b)

def safeConsumer {n : ℕ} (G : SimpleGraph (Fin n)) (A B U V : Finset (Fin n)) : Prop :=
  ∀ x, consumerValue A B U V x = true →
    ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Finset (Fin n) :=
  A.filter fun a => ∀ b ∈ B, G.Adj a b

lemma edge_on_pair {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n)
    (h : ∃ u v, G.Adj u v ∧ pairInput a b u = true ∧ pairInput a b v = true) :
    G.Adj a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [pairInput, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (G.irrefl huv).elim
  · exact huv
  · exact huv.symm
  · exact (G.irrefl huv).elim

lemma orValue_pair {n : ℕ} (A : Finset (Fin n)) (a b : Fin n) :
    orValue A (pairInput a b) = true ↔ a ∈ A ∨ b ∈ A := by
  simp only [orValue, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact Or.inl hu
    · exact Or.inr hu
  · rintro (ha | hb)
    · exact ⟨a, ha, Or.inl rfl⟩
    · exact ⟨b, hb, Or.inr rfl⟩

lemma safeConsumer_left_universal {n : ℕ} (G : SimpleGraph (Fin n))
    (A B U V : Finset (Fin n)) (hs : safeConsumer G A B U V)
    (a : Fin n) (haA : a ∈ A) (haV : a ∈ V) :
    ∀ b ∈ B, G.Adj a b := by
  intro b hbB
  apply edge_on_pair G a b
  apply hs
  simp only [consumerValue, rectangleValue, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨Or.inl ⟨(orValue_pair A a b).mpr (Or.inl haA),
    (orValue_pair B a b).mpr (Or.inr hbB)⟩,
    (orValue_pair V a b).mpr (Or.inl haV)⟩

lemma safeConsumer_right_universal {n : ℕ} (G : SimpleGraph (Fin n))
    (A B U V : Finset (Fin n)) (hs : safeConsumer G A B U V)
    (b : Fin n) (hbB : b ∈ B) (hbV : b ∈ V) :
    ∀ a ∈ A, G.Adj b a := by
  intro a haA
  apply edge_on_pair G b a
  apply hs
  simp only [consumerValue, rectangleValue, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨Or.inl ⟨(orValue_pair A b a).mpr (Or.inr haA),
    (orValue_pair B b a).mpr (Or.inl hbB)⟩,
    (orValue_pair V b a).mpr (Or.inl hbV)⟩

lemma safeConsumer_cross {n : ℕ} (G : SimpleGraph (Fin n))
    (A B U V : Finset (Fin n)) (hs : safeConsumer G A B U V) :
    ∀ u ∈ U, ∀ v ∈ V, G.Adj u v := by
  intro u hu v hv
  apply edge_on_pair G u v
  apply hs
  simp only [consumerValue, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨Or.inr ((orValue_pair U u v).mpr (Or.inl hu)),
    (orValue_pair V u v).mpr (Or.inr hv)⟩

lemma centers_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset (Fin n)) (b₁ b₂ : Fin n)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂) :
    (centers G A B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  obtain ⟨_, ha⟩ := Finset.mem_filter.mp ha
  obtain ⟨_, hc⟩ := Finset.mem_filter.mp hc
  exact (hfour a b₁ c b₂ (ha b₁ hb₁) (hc b₁ hb₁).symm
    (hc b₂ hb₂) (ha b₂ hb₂).symm).resolve_right hne

lemma safeConsumer_two_centers_no_junk {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (A B U V : Finset (Fin n)) (hs : safeConsumer G A B U V)
    (a b : Fin n) (haA : a ∈ A) (haV : a ∈ V) (hbB : b ∈ B) (hbV : b ∈ V) :
    U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hab := safeConsumer_left_universal G A B U V hs a haA haV b hbB
  have hua := safeConsumer_cross G A B U V hs u hu a haV
  have hbu := (safeConsumer_cross G A B U V hs u hu b hbV).symm
  exact htri u a b hua hab hbu

lemma rectangle_pair_disjoint {n : ℕ} (A B : Finset (Fin n))
    (hd : Disjoint A B) (a b : Fin n)
    (hr : rectangleValue A B (pairInput a b) = true) :
    (a ∈ A ∧ b ∈ B) ∨ (b ∈ A ∧ a ∈ B) := by
  have hh : orValue A (pairInput a b) = true ∧ orValue B (pairInput a b) = true := by
    simpa only [rectangleValue, Bool.and_eq_true] using hr
  obtain ⟨ha, hb⟩ := hh
  rcases (orValue_pair A a b).mp ha with ha | ha <;>
    rcases (orValue_pair B a b).mp hb with hb | hb
  · exact (Finset.disjoint_left.mp hd ha hb).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (Finset.disjoint_left.mp hd ha hb).elim

lemma consumer_rectangle_pair_covered {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B U V : Finset (Fin n))
    (hs : safeConsumer G A B U V) (hd : Disjoint A B) (a b : Fin n)
    (hr : rectangleValue A B (pairInput a b) = true)
    (hv : orValue V (pairInput a b) = true) :
    ∃ c ∈ centers G A B ∪ centers G B A, c = a ∨ c = b := by
  rcases rectangle_pair_disjoint A B hd a b hr with ⟨haA, hbB⟩ | ⟨hbA, haB⟩ <;>
    rcases (orValue_pair V a b).mp hv with haV | hbV
  · refine ⟨a, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haA, ?_⟩), Or.inl rfl⟩
    exact safeConsumer_left_universal G A B U V hs a haA haV
  · refine ⟨b, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbB, ?_⟩), Or.inr rfl⟩
    exact safeConsumer_right_universal G A B U V hs b hbB hbV
  · refine ⟨a, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haB, ?_⟩), Or.inl rfl⟩
    exact safeConsumer_right_universal G A B U V hs a haB haV
  · refine ⟨b, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbA, ?_⟩), Or.inr rfl⟩
    exact safeConsumer_left_universal G A B U V hs b hbA hbV

lemma consumer_lost_pair_covered {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B U V : Finset (Fin n))
    (hs : safeConsumer G A B U V) (hd : Disjoint A B) (a b : Fin n)
    (ht : consumerValue A B U V (pairInput a b) = true)
    (hz : (orValue U (pairInput a b) && orValue V (pairInput a b)) = false) :
    ∃ c ∈ centers G A B ∪ centers G B A, c = a ∨ c = b := by
  simp only [consumerValue, Bool.and_eq_true, Bool.or_eq_true] at ht
  obtain ⟨hr | hu, hv⟩ := ht
  · exact consumer_rectangle_pair_covered G A B U V hs hd a b hr hv
  · have ht' : (orValue U (pairInput a b) && orValue V (pairInput a b)) = true := by
      simp [hu, hv]
    rw [hz] at ht'
    exact Bool.noConfusion ht'

lemma centers_union_card_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : Finset (Fin n)) (ha : 2 ≤ A.card) (hb : 2 ≤ B.card) :
    (centers G A B ∪ centers G B A).card ≤ 2 := by
  obtain ⟨a₁, ha₁, a₂, ha₂, hneA⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨b₁, hb₁, b₂, hb₂, hneB⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hA := centers_card_le_one G hfour A B b₁ b₂ hb₁ hb₂ hneB
  have hB := centers_card_le_one G hfour B A a₁ a₂ ha₁ ha₂ hneA
  have hUnion := Finset.card_union_le (centers G A B) (centers G B A)
  omega

lemma safeConsumers_adjacent_centers_disjoint_junk {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (A B U₁ V₁ U₂ V₂ : Finset (Fin n))
    (hs₁ : safeConsumer G A B U₁ V₁) (hs₂ : safeConsumer G A B U₂ V₂)
    (a b : Fin n) (ha : a ∈ V₁) (hb : b ∈ V₂) (hab : G.Adj a b) :
    Disjoint U₁ U₂ := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  have hua := safeConsumer_cross G A B U₁ V₁ hs₁ u hu₁ a ha
  have hbu := (safeConsumer_cross G A B U₂ V₂ hs₂ u hu₂ b hb).symm
  exact htri u a b hua hab hbu

def doubleStarValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ c ∈ centers G A B, x c = true ∧ orValue B x = true) ∨
    ∃ c ∈ centers G B A, x c = true ∧ orValue A x = true)

lemma doubleStarValue_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (x : Fin n → Bool) (h : doubleStarValue G A B x = true) :
    ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  simp only [doubleStarValue, decide_eq_true_eq] at h
  rcases h with ⟨c, hc, hxc, hr⟩ | ⟨c, hc, hxc, hr⟩
  · obtain ⟨_, hc⟩ := Finset.mem_filter.mp hc
    obtain ⟨b, hb, hxb⟩ := of_decide_eq_true hr
    exact ⟨c, b, hc b hb, hxc, hxb⟩
  · obtain ⟨_, hc⟩ := Finset.mem_filter.mp hc
    obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hr
    exact ⟨c, a, hc a ha, hxc, hxa⟩

lemma doubleStarValue_le_rectangle {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (x : Fin n → Bool)
    (h : doubleStarValue G A B x = true) : rectangleValue A B x = true := by
  simp only [doubleStarValue, decide_eq_true_eq] at h
  simp only [rectangleValue, Bool.and_eq_true]
  rcases h with ⟨c, hc, hxc, hr⟩ | ⟨c, hc, hxc, hr⟩
  · refine ⟨?_, hr⟩
    exact decide_eq_true ⟨c, (Finset.mem_filter.mp hc).1, hxc⟩
  · refine ⟨hr, ?_⟩
    exact decide_eq_true ⟨c, (Finset.mem_filter.mp hc).1, hxc⟩

lemma consumer_lost_pair_doubleStar {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B U V : Finset (Fin n))
    (hs : safeConsumer G A B U V) (hd : Disjoint A B) (a b : Fin n)
    (ht : consumerValue A B U V (pairInput a b) = true)
    (hz : (orValue U (pairInput a b) && orValue V (pairInput a b)) = false) :
    doubleStarValue G A B (pairInput a b) = true := by
  have hc := consumer_lost_pair_covered G A B U V hs hd a b ht hz
  obtain ⟨c, hc, he⟩ := hc
  have hxc : pairInput a b c = true := by simpa [pairInput] using he
  simp only [consumerValue, Bool.and_eq_true, Bool.or_eq_true] at ht
  obtain ⟨hr | hu, hv⟩ := ht
  · have hh : orValue A (pairInput a b) = true ∧ orValue B (pairInput a b) = true := by
      simpa only [rectangleValue, Bool.and_eq_true] using hr
    simp only [doubleStarValue, decide_eq_true_eq]
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Or.inl ⟨c, hc, hxc, hh.2⟩
    · exact Or.inr ⟨c, hc, hxc, hh.1⟩
  · simp [hu, hv] at hz

end DoubleStar

namespace Gadget

variable {n k : ℕ}

def adj (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n)) :
    (Fin n ⊕ (Fin k ⊕ Fin k)) → (Fin n ⊕ (Fin k ⊕ Fin k)) → Prop
  | .inl a, .inl b => H.Adj a b
  | .inl a, .inr (.inl i) => a ∈ A i
  | .inr (.inl i), .inl a => a ∈ A i
  | .inr (.inl i), .inr (.inr j) => i = j
  | .inr (.inr j), .inr (.inl i) => i = j
  | _, _ => False

def graph (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n)) :
    SimpleGraph (Fin n ⊕ (Fin k ⊕ Fin k)) where
  Adj := adj H A
  symm := ⟨by
    intro a b h
    rcases a with a | a | a <;> rcases b with b | b | b <;> simp_all [adj]
    exact h.symm⟩
  loopless := ⟨by
    intro a
    rcases a with a | a | a <;> simp [adj]⟩

lemma triangleFree (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a)
    (hsep : ∀ i a b, a ∈ A i → b ∈ A i → ¬ H.Adj a b) :
    ∀ a b c, (graph H A).Adj a b → (graph H A).Adj b c →
      ¬ (graph H A).Adj c a := by
  intro a b c hab hbc hca
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    rcases c with c | c | c <;> simp_all [graph, adj]
  all_goals grind

lemma squareFree (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (hfour : ∀ a b c d, H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a →
      a = c ∨ b = d)
    (hcommon : ∀ i a b z, a ∈ A i → b ∈ A i → H.Adj a z → H.Adj b z → a = b)
    (hinter : ∀ i j a b, a ∈ A i → a ∈ A j → b ∈ A i → b ∈ A j →
      i = j ∨ a = b) :
    ∀ a b c d, (graph H A).Adj a b → (graph H A).Adj b c →
      (graph H A).Adj c d → (graph H A).Adj d a → a = c ∨ b = d := by
  intro a b c d hab hbc hcd hda
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    rcases c with c | c | c <;> rcases d with d | d | d <;>
    simp_all [graph, adj]
  all_goals grind [SimpleGraph.adj_comm]

def extend (C : Finset (Fin n)) : Finset (Fin n ⊕ (Fin k ⊕ Fin k)) :=
  C.disjSum (Finset.univ.disjSum ∅)

lemma extend_card (C : Finset (Fin n)) : (extend (k := k) C).card = C.card + k := by
  simp [extend]

lemma extend_cover (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (C : Finset (Fin n)) (hC : H.IsVertexCover (C : Set (Fin n))) :
    (graph H A).IsVertexCover (↑(extend (k := k) C) : Set (Fin n ⊕ (Fin k ⊕ Fin k))) := by
  intro a b hab
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp_all [graph, adj, extend]
  exact hC hab

lemma restrict_cover (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (C : Finset (Fin n ⊕ (Fin k ⊕ Fin k)))
    (hC : (graph H A).IsVertexCover (C : Set (Fin n ⊕ (Fin k ⊕ Fin k)))) :
    H.IsVertexCover (C.toLeft : Set (Fin n)) := by
  intro a b hab
  have h := @hC (.inl a) (.inl b) hab
  simpa using h

lemma cover_card_lower (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (C : Finset (Fin n ⊕ (Fin k ⊕ Fin k)))
    (hC : (graph H A).IsVertexCover (C : Set (Fin n ⊕ (Fin k ⊕ Fin k)))) :
    C.toLeft.card + k ≤ C.card := by
  have hpend : ∀ i : Fin k, i ∈ C.toRight.toLeft ∨ i ∈ C.toRight.toRight := by
    intro i
    have h := @hC (.inr (.inl i)) (.inr (.inr i)) rfl
    simpa using h
  have hu : Finset.univ ⊆ C.toRight.toLeft ∪ C.toRight.toRight := by
    intro i hi
    exact Finset.mem_union.mpr (hpend i)
  have hle : k ≤ C.toRight.card := by
    calc
      k = (Finset.univ : Finset (Fin k)).card := by simp
      _ ≤ (C.toRight.toLeft ∪ C.toRight.toRight).card := Finset.card_le_card hu
      _ ≤ C.toRight.toLeft.card + C.toRight.toRight.card := Finset.card_union_le _ _
      _ = C.toRight.card := Finset.card_toLeft_add_card_toRight
  have heq := Finset.card_toLeft_add_card_toRight (u := C)
  omega

lemma vertexCoverNum_eq (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n)) :
    (graph H A).vertexCoverNum = H.vertexCoverNum + k := by
  classical
  apply le_antisymm
  · obtain ⟨S, hS, hc⟩ := H.vertexCoverNum_exists
    let C := S.toFinset
    have hC : H.IsVertexCover (C : Set (Fin n)) := by simpa [C] using hc
    have he := (extend_cover H A C hC).vertexCoverNum_le
    have hcard : (C.card : ℕ∞) = H.vertexCoverNum := by
      rw [← hS]
      exact (Set.encard_eq_coe_toFinset_card S).symm
    simpa [extend_card, hcard] using he
  · obtain ⟨S, hS, hc⟩ := (graph H A).vertexCoverNum_exists
    let C := S.toFinset
    have hC : (graph H A).IsVertexCover (C : Set (Fin n ⊕ (Fin k ⊕ Fin k))) := by
      simpa [C] using hc
    have hr := (restrict_cover H A C hC).vertexCoverNum_le
    have hl := cover_card_lower H A C hC
    have hcard : (C.card : ℕ∞) = (graph H A).vertexCoverNum := by
      rw [← hS]
      exact (Set.encard_eq_coe_toFinset_card S).symm
    have hr' : H.vertexCoverNum ≤ (C.toLeft.card : ℕ∞) := by simpa using hr
    calc
      H.vertexCoverNum + k ≤ (C.toLeft.card : ℕ∞) + k := add_le_add hr' le_rfl
      _ = ((C.toLeft.card + k : ℕ) : ℕ∞) := by simp
      _ ≤ (C.card : ℕ∞) := by exact_mod_cast hl
      _ = (graph H A).vertexCoverNum := hcard

lemma sparse_girth (H : SimpleGraph (Fin n)) (A : Fin k → Finset (Fin n))
    (htri : ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a)
    (hfour : ∀ a b c d, H.Adj a b → H.Adj b c → H.Adj c d → H.Adj d a →
      a = c ∨ b = d)
    (hsep : ∀ i a, a ∈ A i → ∀ b, b ∈ A i → a ≠ b →
      ¬ H.Adj a b ∧ ¬ ∃ z, H.Adj a z ∧ H.Adj b z)
    (hinter : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (∀ a b c, (graph H A).Adj a b → (graph H A).Adj b c →
      ¬ (graph H A).Adj c a) ∧
    (∀ a b c d, (graph H A).Adj a b → (graph H A).Adj b c →
      (graph H A).Adj c d → (graph H A).Adj d a → a = c ∨ b = d) := by
  constructor
  · apply triangleFree H A htri
    intro i a b ha hb hab
    exact (hsep i a ha b hb (H.ne_of_adj hab)).1 hab
  · apply squareFree H A hfour
    · intro i a b z ha hb haz hbz
      by_contra hab
      exact (hsep i a ha b hb hab).2 ⟨z, haz, hbz⟩
    · intro i j a b hai haj hbi hbj
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr ((Finset.card_le_one.mp (hinter i j hij))
          a (Finset.mem_inter.mpr ⟨hai, haj⟩) b (Finset.mem_inter.mpr ⟨hbi, hbj⟩))

end Gadget

end PEqualNP.Outside.L_meta_1904_aux
