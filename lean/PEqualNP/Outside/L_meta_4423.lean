import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- Adapts the checked L-meta-3200 proof and its general suffix bound.
-- Earlier elimination and cofactor arguments are due to ylwang0701 and itsvari.
namespace PEqualNP.Outside.L_meta_4423


namespace Elimination

open PEqualNP.MetaComplexity
namespace Helpers
open PEqualNP.CircuitLowerBounds
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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
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

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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

noncomputable def charged (g : Gate) : Bool :=
  GateOp.rec true true false (fun _ => true) true g.op

noncomputable def cost (gs : List Gate) : ℕ := gs.countP charged



theorem step_account (op : GateOp) (m : ℕ) (ins : List ℕ)
    (M : ℕ → Stat) (u v : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hag : ∀ i j, M i = Sum.inr j → u i = v i) :
    let r := simplify op m (ins.map M)
    let original := cost [⟨op, ins⟩]
    cost r.1.toList ≤ original ∧
      (cost r.1.toList = original → ∀ j, r.2 = Sum.inr j →
        op.eval (ins.map u) = op.eval (ins.map v)) := by
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try have ha := hag a; cases hma : M a) <;>
    (try have hb := hag b; cases hmb : M b) <;>
    simp_all [simplify, simpAnd, simpOr, simpNot, cost, charged, GateOp.eval]

theorem weakCost (n : ℕ) (gs : List Gate) : ∀ (acc : List Stat × List Gate),
    (∀ g ∈ gs, Ok g) → cost (elim n gs acc).2 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil => intros; simp [elim,cost]
  | cons g gs ih =>
    intro acc hok
    have hg := hok g List.mem_cons_self
    have h := (step_account g.op (n + acc.2.length) g.inputs
        (fun i => acc.1.getD i (Sum.inl false)) (fun _ => false) (fun _ => false)
        hg.1 hg.2 (fun _ _ _ => rfl)).1
    change cost (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ≤ cost [g] at h
    have ht := ih (elimStep n acc g) (fun g' h' => hok g' (List.mem_cons_of_mem _ h'))
    show cost (elim n gs (elimStep n acc g)).2 ≤ _
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    rw [hcons]
    have hadd : cost (elimStep n acc g).2 = cost acc.2 +
        cost (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList :=
      List.countP_append
    rw [hadd] at ht
    omega

theorem strictCost (n : ℕ) (gs : List Gate) (out j : ℕ) :
    ∀ (acc : List Stat × List Gate) (u v : List Bool),
      (∀ g ∈ gs, Ok g) → u.length = acc.1.length → v.length = acc.1.length →
      (∀ i k, acc.1.getD i (Sum.inl false) = Sum.inr k → u.getD i false = v.getD i false) →
      (elim n gs acc).1.getD out (Sum.inl false) = Sum.inr j →
      (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false →
      cost (elim n gs acc).2 + 1 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil =>
    intro acc u v _ _ _ hag hj hdiff
    exact (hdiff (hag out j hj)).elim
  | cons g gs ih =>
    intro acc u v hok hu hv hag hj hdiff
    let M := fun i => acc.1.getD i (Sum.inl false)
    let r := simplify g.op (n + acc.2.length) (g.inputs.map M)
    have hg := hok g List.mem_cons_self
    have ha := step_account g.op (n + acc.2.length) g.inputs M
      (fun i => u.getD i false) (fun i => v.getD i false) hg.1 hg.2 hag
    change cost r.1.toList ≤ cost [g] ∧ _ at ha
    have hcost : cost (elimStep n acc g).2 = cost acc.2 + cost r.1.toList := by
      apply List.countP_append
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    have htail (g' : Gate) (h' : g' ∈ gs) := hok g' (List.mem_cons_of_mem _ h')
    change cost (elim n gs (elimStep n acc g)).2 + 1 ≤ _
    rw [hcons]
    by_cases heq : cost r.1.toList = cost [g]
    · let U := g.op.eval (g.inputs.map fun i => u.getD i false)
      let V := g.op.eval (g.inputs.map fun i => v.getD i false)
      have hnext := ih (elimStep n acc g) (u ++ [U]) (v ++ [V]) htail
        (by simp [elimStep,hu]) (by simp [elimStep,hv]) (by
          intro i k h
          change (acc.1 ++ [r.2]).getD i (Sum.inl false) = Sum.inr k at h
          by_cases hi : i = acc.1.length
          · subst i
            rw [getD_snoc_eq] at h
            rw [← hu, getD_snoc_eq, hu, ← hv, getD_snoc_eq]
            exact ha.2 heq k h
          · rw [getD_snoc_ne _ _ _ _ hi] at h
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag i k h) hj hdiff
      omega
    · have hweak := weakCost n gs (elimStep n acc g) htail
      omega

def pinStat {n : ℕ} (p : Fin (n+1)) : Fin (n+1) → Stat :=
  Fin.insertNth (α := fun _ => Stat) p (Sum.inl false) (fun j => Sum.inr j.val)

theorem pinStat_valid {n : ℕ} (p i : Fin (n+1)) : (pinStat p i).Valid n := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.Valid]
  · rename_i j
    simpa [pinStat, Stat.Valid] using j.isLt

theorem pinStat_val {n : ℕ} (p i : Fin (n+1)) (y : Fin n → Bool) :
    (pinStat p i).val (List.ofFn y) = Fin.insertNth (α := fun _ => Bool) p false y i := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.val]
  · rename_i j
    simp only [pinStat, Fin.insertNth_apply_succAbove, Stat.val]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]

theorem getMap {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : β) :
    (l.map f).getD i d = if h : i < l.length then f l[i] else d := by
  by_cases h : i < l.length
  · rw [dite_eq_left h,List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
  · rw [dite_eq_right h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

theorem pinValid {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).Valid n := by
  rw [getMap]; split
  · exact pinStat_valid _ _
  · trivial

theorem pinMap {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (y : Fin n → Bool) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).val (List.ofFn y) =
      (l.map (Fin.insertNth (α := fun _ => Bool) p false y)).getD k false := by
  rw [getMap,getMap]; split
  · exact pinStat_val _ _ _
  · rfl

theorem pinAgree {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (x : Fin (n+1) → Bool) (k j : ℕ)
    (h : (l.map (pinStat p)).getD k (Sum.inl false) = Sum.inr j) :
    (l.map (Function.update x p true)).getD k false = (l.map (Function.update x p false)).getD k false := by
  rw [getMap] at h
  rw [getMap,getMap]
  by_cases hk : k < l.length
  · simp only [dite_eq_left hk] at h ⊢
    have e : l[k] ≠ p := by
      intro e
      simp [e,pinStat] at h
    simp [Function.update_of_ne e]
  · simp [hk]


theorem restrict2958 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) := by
  dsimp only
  intro n p C l hfan
  intro hprobe hnc
  obtain ⟨x, hx⟩ := hprobe
  let M := l.map (pinStat p)
  let gs := C.gates
  let acc := elim n gs (M,[])
  have hok (g) (hg : g ∈ gs) : Ok g := hfan g hg
  have hval (y : Fin n → Bool) : (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn y)) = C.eval (l.map (p.insertNth false y)) := by
    let z := l.map (p.insertNth false y)
    have hi : Inv n (List.ofFn y) z (M,[]) := by
      refine ⟨by simp [M,z],?_⟩
      intro k
      exact ⟨pinValid p l k,pinMap p l y k⟩
    have he := ((inv_elim n (List.ofFn y) (by simp) gs z (M,[]) hok hi).2 C.output).2
    exact he
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨a,c,hac⟩ := hnc
    exact (hac (by rw [← hval a, ← hval c, ho]; rfl)).elim
  | inr j =>
    let u := l.map (Function.update x p true)
    let v := l.map (Function.update x p false)
    have hdiff : (wiresFrom gs u).getD C.output false ≠ (wiresFrom gs v).getD C.output false := by
      exact hx
    have hs := strictCost n gs C.output j (M,[]) u v hok
      (by simp [u,M]) (by simp [v,M]) (pinAgree p l x) ho hdiff
    refine ⟨⟨acc.2,j⟩, elim_ok n gs (M,[]) (by simp), ?_, ?_⟩
    · change cost acc.2 + 1 ≤ cost gs
      simpa only [show cost [] = 0 from rfl, Nat.zero_add] using hs
    · funext y
      have h := hval y
      rw [ho] at h
      exact h

end Helpers
end Elimination

theorem eliminateSensitive : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) :=
  PEqualNP.Outside.L_meta_4423.Elimination.Helpers.restrict2958


namespace Theta

/- Each sampled signal carries its phase. The four binary operations represent AND and OR on signed inputs, and inverting a signal changes only its phase. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

end Theta

namespace Theta

/- Trace the output backwards and keep the signals that still feed a gate. Each step uses one binary gate. Every surviving set separates every sampled pair, and its cardinality is at most one more than the remaining gate count. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

inductive Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | done {a} (hg : Good m a) (nonzero : a≠0) : Live m 0 {a}
  | step {k U a b d} (hd : d<4) (ha : a≠0) (hb : b≠0) (diff : a≠b)
      (fresh : combine d a b ∉ insert a (insert b U))
      (next : Live m k (insert (combine d a b) U)) :
      Live m (k+1) (insert a (insert b U))

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction h with
  | done hg hn => simpa using hn
  | @step k U a b d hd ha hb ne fresh tail ih =>
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction h with
  | done hg hn => simp
  | @step k U a b d hd ha hb ne fresh tail ih =>
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at ih
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction h with
  | done hg hn => exact ⟨_,Finset.mem_singleton_self _,hg i hi⟩
  | @step k U a b d hd ha hb ne fresh tail ih =>
    obtain ⟨x,hx,dist⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]
end Theta

namespace Theta

/- The search enumerates distinct operands, the four signed operations and the four choices of which operands are needed again. -/

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases h with
    | done hg hn => exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _))
    | step hd _ _ _ _ _ => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases h with
    | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self _)))
    | step hd _ _ ab fresh tail =>
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))
end Theta

namespace Theta

/- A restriction can force several live signals to zero. Projecting the rest of a trace saves at least one binary gate for each such signal. -/

structure Projection (m h : ℕ) where
  toFun : ℕ → ℕ
  atZero : toFun 0=0
  combineEq : ∀ d a b, d<4 → toFun (combine d a b)=combine d (toFun a) (toFun b)
  good : ∀ a, Good m a → Good h (toFun a)
  someRow : 0<h

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction live with
  | @done a hg hn =>
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | @step k U a b d hd ha hb ab fz tail ih =>
    obtain ⟨j,T,cost,ok,raw⟩ := ih
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩
end Theta

namespace Theta

/- A restricted bank keeps selected pairs of rows. Duplicate one retained pair in the other positions to preserve the two-column representation. -/
lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i<m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i<m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i<m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j<m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r<m) : Projection m m where
  toFun := slice m q r
  atZero := by simp [slice,half]
  combineEq := slice_hom m q r
  good := by
    intro a ga i hi
    rw [slice_lo _ _ _ hi,slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi
  someRow := by omega

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def cutSearch (m q fuel : ℕ) (v : List ℕ) : Bool :=
  let r := min (Nat.log2 q) (m-1)
  let xs := v.map (slice m q r)
  let gone := xs.count 0
  gone≤fuel && start m (fuel-gone) xs

theorem cut_complete {m k S} (hm : 0<m) (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup)
    (q fuel : ℕ) (lim : k≤fuel) : cutSearch m q fuel v=true := by
  let r := min (Nat.log2 q) (m-1)
  let p := projection m q r (show r<m by dsimp [r];omega)
  obtain ⟨l,T,cost,live,sub⟩ := projectLive p h
  let xs := v.map (slice m q r)
  have fixed : dead p.toFun S=xs.count 0 := by
    rw [←rep];dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [xs,List.count_eq_countP,List.countP_map,p,projection,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at cost
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs,p,projection,←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]
end Theta

namespace Theta

/- The certificate selects a restriction or enumerates a complete level of successors. Its hints can select any bank. Soundness follows from the projected trace and complete successor enumeration. -/
def oneOutput (m fuel : ℕ) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : List (List ℕ) :=
  if optionStep m fuel (fun _ => true) rest n cv a b z ka kb then [z::save ka a (save kb b rest)] else []
def oneGate (m fuel : ℕ) (v rest : List ℕ) (n cv a b z : ℕ) :=
  if z != 0 && !(v.contains z) then
    oneOutput m fuel rest n cv a b z false false ++ oneOutput m fuel rest n cv a b z true false ++
    oneOutput m fuel rest n cv a b z false true ++ oneOutput m fuel rest n cv a b z true true
  else []
def onePair (m fuel : ℕ) (v : List ℕ) (a b : ℕ) :=
  if a<b then
    let rest := without v a b
    let gate := oneGate m fuel v rest rest.length (cover m rest) a b
    gate (a &&& b) ++ gate (a ||| b) ++ gate (a ^^^ (a &&& b)) ++ gate (b ^^^ (a &&& b))
  else []
def successors (m fuel : ℕ) (v : List ℕ) :=
  v.flatMap (fun a => v.flatMap (fun b => onePair m fuel v a b))
lemma output_any (m fuel : ℕ) (go : List ℕ→Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) :
    (oneOutput m fuel rest n cv a b z ka kb).any go=optionStep m fuel go rest n cv a b z ka kb := by
  have E (t : Bool) (x : List ℕ) : ((if t then [x] else []) : List (List ℕ)).any go = (t && go x) := by cases t <;> simp
  unfold oneOutput
  rw [E]
  simp only [optionStep,Bool.and_true]
lemma gate_any (m fuel : ℕ) (go : List ℕ→Bool) (v rest : List ℕ) (n cv a b z : ℕ) :
    (oneGate m fuel v rest n cv a b z).any go=gateStep m fuel go v rest n cv a b z := by
  have E (t : Bool) (xs : List (List ℕ)) : (if t then xs else []).any go = (t && xs.any go) := by cases t <;> simp
  unfold oneGate gateStep
  rw [E]
  simp only [List.any_append,output_any,Bool.or_assoc,Bool.and_assoc]
lemma pair_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) (a b : ℕ) :
    (onePair m fuel v a b).any go=pairStep m fuel go v a b := by
  by_cases h : a<b <;> simp [onePair,pairStep,h,gate_any,Bool.or_assoc]
lemma successors_any (m fuel : ℕ) (go : List ℕ→Bool) (v : List ℕ) :
    (successors m fuel v).any go=anyGate m fuel go v := by simp [successors,anyGate,pair_any]
def feasible (m fuel : ℕ) (v : List ℕ) := ∃ k≤fuel,Live m k v.toFinset ∧ v.Nodup
theorem move {m fuel : ℕ} {v : List ℕ} (h : feasible m (fuel+1) v) :
    terminal m v=true ∨ ∃ w∈successors m fuel v,feasible m fuel w := by
  classical
  obtain ⟨k,lim,live,nd⟩ := h
  generalize e : v.toFinset=S at live
  cases live with
  | done hg hn => exact Or.inl (ends hg v (List.mem_toFinset.mp (e ▸ Finset.mem_singleton_self _)))
  | step hd ha hb ab fz tail =>
    let step := fun w => decide (feasible m fuel w)
    have hit := transition (go:=step) hd ab fz e nd (by omega : _≤fuel) tail (fun w rep nu => by
      apply decide_eq_true;exact ⟨_,by omega,rep ▸ tail,nu⟩)
    rw [←successors_any] at hit
    obtain ⟨w,hw,works⟩ := List.any_eq_true.mp hit
    exact Or.inr ⟨w,hw,of_decide_eq_true works⟩

def zeroPairs (m : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | x::xs, code, acc => zeroPairs m xs (code >>> 1)
      (if code % 2=1 then acc ^^^ (acc &&& (x ||| (x >>> m))) else acc)

end Theta

namespace Theta

/- Permutations of sampled row pairs preserve every gate operation and the condition that the output separates all pairs. -/
def flipSwap (i j a : ℕ) := if a.testBit i = a.testBit j then a else a ^^^ ((1 <<< i) ||| (1 <<< j))
lemma swapBit (i j k a : ℕ) : (flipSwap i j a).testBit k =
    a.testBit (if k=i then j else if k=j then i else k) := by
  by_cases h : a.testBit i=a.testBit j
  · by_cases x : k=i <;> by_cases y : k=j <;> simp [flipSwap,h,x,y] <;> grind
  · have n : i≠j := fun e => h (e ▸ rfl)
    by_cases x : k=i
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    by_cases y : k=j
    · subst k
      cases p : a.testBit i <;> cases q : a.testBit j <;>
        simp_all [flipSwap,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow]
    · simp [flipSwap,h,x,y,Nat.testBit_xor,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,Ne.symm x,Ne.symm y]
lemma flipSwap_twice (i j a : ℕ) : flipSwap i j (flipSwap i j a)=a := by
  apply Nat.eq_of_testBit_eq;intro k
  by_cases x : k=i <;> by_cases y : k=j <;> by_cases n : i=j <;> simp_all [swapBit]
lemma flipSwap_hom (i j d a b : ℕ) (hd : d<4) : flipSwap i j (combine d a b)=combine d (flipSwap i j a) (flipSwap i j b) := by
  apply Nat.eq_of_testBit_eq;intro k
  interval_cases d <;> simp [swapBit,combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]

def turn (m i j a : ℕ) := flipSwap i j (flipSwap (m+i) (m+j) a)
lemma turnGood {m i j a : ℕ} (hi : i<m) (hj : j<m) (g : Good m a) : Good m (turn m i j a) := by
  intro k hk
  have hm : m≠0 := by omega
  have ki : k≠m+i := by omega
  have kj : k≠m+j := by omega
  have ii : i≠m+i := by omega
  have ij : i≠m+j := by omega
  have ji : j≠m+i := by omega
  have jj : j≠m+j := by omega
  have ui : m+k≠i := by omega
  have uj : m+k≠j := by omega
  by_cases x : k=i
  · subst k;simp [turn,swapBit,ii,ij,ji,jj,ui,uj,hm];exact g _ hj
  by_cases y : k=j
  · subst k;simp [turn,swapBit,x,ii,ij,ji,jj,ui,uj,hm];exact g _ hi
  · simpa [turn,swapBit,x,y,ki,kj,ui,uj] using g k hk

theorem relabelLive {m k S} (f : ℕ→ℕ) (fz : f 0=0) (inj : Function.Injective f)
    (op : ∀ d a b,d<4 → f (combine d a b)=combine d (f a) (f b))
    (labels : ∀ a,Good m a → Good m (f a)) (live : Live m k S) : Live m k (S.image f) := by
  induction live with
  | done hg hn =>
    simp only [Finset.image_singleton]
    exact Live.done (labels _ hg) (fun h => hn (inj (h.trans fz.symm)))
  | @step k U a b d hd ha hb ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,op d a b hd] at ih
    apply Live.step hd (fun h => ha (inj (h.trans fz.symm))) (fun h => hb (inj (h.trans fz.symm))) (fun h => ne (inj h)) _ ih
    rw [←op d a b hd,←Finset.image_insert,←Finset.image_insert]
    exact fun h => fresh ((Finset.mem_image.mp h).elim (fun x hh => inj hh.2 ▸ hh.1))
def permute (m : ℕ) : List (ℕ×ℕ) → ℕ → ℕ
  | [],a => a
  | (i,j)::ss,a => permute m ss (turn m i j a)
theorem perm_live {m k S} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m) (h : Live m k S) :
    Live m k (S.image (permute m ss)) := by
  induction ss generalizing S with
  | nil => simpa [permute] using h
  | cons p ss ih =>
    obtain ⟨i,j⟩ := p
    obtain ⟨hi,hj⟩ := safe _ (List.mem_cons_self)
    have fi (a b : ℕ) : Function.Injective (flipSwap a b) := fun x y e =>
      (flipSwap_twice a b x).symm.trans ((congrArg (flipSwap a b) e).trans (flipSwap_twice a b y))
    have inj : Function.Injective (turn m i j) := (fi i j).comp (fi (m+i) (m+j))
    have names := relabelLive (turn m i j) (by simp [turn,flipSwap]) inj
      (fun d a b hd => by simp [turn,flipSwap_hom _ _ _ _ _ hd]) (fun _ => turnGood hi hj) h
    simpa [permute,Finset.image_image,Function.comp_def] using ih (fun p hp => safe _ (List.mem_cons_of_mem _ hp)) names
theorem perm_feasible {m fuel : ℕ} {v w : List ℕ} (ss : List (ℕ×ℕ)) (safe : ∀ p∈ss,p.1<m ∧ p.2<m)
    (eq : (v.map (permute m ss)).toFinset=w.toFinset) (nw : w.Nodup) (h : feasible m fuel v) : feasible m fuel w := by
  obtain ⟨k,lim,ok,_⟩ := h
  refine ⟨k,lim,?_,nw⟩
  have tr := perm_live ss safe ok
  have imageEq : (v.map (permute m ss)).toFinset = v.toFinset.image (permute m ss) := by ext x;simp
  rw [←eq,imageEq]
  exact tr
end Theta

namespace Theta
def Excluded (m k : ℕ) (v : List ℕ) := ¬feasible m k v
def Block (m k : ℕ) (vs : List (List ℕ)) (i n : ℕ) := ∀ v∈(vs.drop i).take n,Excluded m k v
lemma blocks_cover {m k width q : ℕ} {vs : List (List ℕ)} (pw : 0<width) (size : vs.length≤q*width)
    (all : ∀ j : Fin q,Block m k vs (j.val*width) width) : ∀ v∈vs,Excluded m k v := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  have split := Nat.div_add_mod' i width
  have within := Nat.mod_lt i pw
  have bound : i/width<q := (Nat.div_lt_iff_lt_mul pw).2 (by omega)
  apply all ⟨i/width,bound⟩ _
  apply List.mem_iff_getElem.mpr
  have ix : i % width<((vs.drop (i/width*width)).take width).length := by simp only [List.length_take,List.length_drop];omega
  refine ⟨i % width,ix,?_⟩
  simp only [List.getElem_take,List.getElem_drop]
  simp [split]
lemma join_exclusions {m k : ℕ} {v : List ℕ} (term : terminal m v=false)
    (no : ∀ w∈successors m k v,Excluded m k w) : Excluded m (k+1) v := by
  intro h
  rcases move h with e|⟨w,hw,hf⟩
  · exact Bool.noConfusion (term.symm.trans e)
  · exact no w hw hf
end Theta

namespace Theta

/- A stored bound proves that a smaller set of signals needs a stated number of gates. A receipt reconstructs all the restricted live signals from that set. Combining the bound with the zero signals lost by restriction excludes the proposed continuation. -/
structure FloorData where
  pairMask : ℕ
  lower : ℕ
  basis : List ℕ
deriving Inhabited
def Floor (m : ℕ) (s : FloorData) := ∀ k,Possible m k (0::s.basis) → s.lower≤k
theorem floorChecked {m : ℕ} {s : FloorData} (checked : start m (s.lower-1) (0::s.basis)=false) : Floor m s := by
  intro k poss
  by_contra small
  obtain ⟨j,S,le,live,sub⟩ := poss
  exact Bool.noConfusion (checked.symm.trans (start_complete live _ sub _ (by omega)))
lemma getMember {av : List ℕ} (zeroMem : 0∈av) (i : ℕ) : av.getD i 0∈av := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : av[i]? with
  | none => exact zeroMem
  | some t => exact List.mem_of_getElem? e

def instruction (av : List ℕ) (part : ℕ) :=
  let n := (part &&& 4095)-1
  combine (n % 4) (av.getD ((n >>> 2) &&& 15) 0) (av.getD ((n >>> 6) &&& 15) 0)
def replay : ℕ → ℕ → List ℕ → List ℕ
  | 0,_,av => av
  | k+1,code,av => if code=0 then av else replay k (code >>> 12) (av++[instruction av code])
def paidCount : ℕ → ℕ → ℕ
  | 0,_ => 0
  | k+1,code => if code=0 then 0 else paidCount k (code >>> 12)+1

theorem replay_back {m k : ℕ} (count code : ℕ) (av : List ℕ) (hasZero : 0∈av)
    (later : Possible m k (replay count code av)) : Possible m (k+paidCount count code) av := by
  induction count generalizing code av with
  | zero => simpa [replay,paidCount] using later
  | succ n ih =>
    by_cases stop : code=0
    · simpa [replay,paidCount,stop] using later
    rw [replay,ite_eq_right stop] at later
    have post := ih _ (av++[instruction av code]) (by simp [hasZero]) later
    let p := (code &&& 4095)-1
    have full := pullPaid (d:=p % 4) (Nat.mod_lt _ (by decide)) (getMember hasZero ((p >>> 2) &&& 15)) (getMember hasZero ((p >>> 6) &&& 15)) post
    obtain ⟨j,S,lim,live,sub⟩ := full
    refine ⟨j,S,?_,live,sub⟩
    rw [paidCount,ite_eq_right stop]
    have one (b : Bool) : b.toNat≤1 := by cases b <;> decide
    have bound := one (charge av (combine (p % 4) (av.getD ((p >>> 2) &&& 15) 0) (av.getD ((p >>> 6) &&& 15) 0)))
    omega

def contradictsFloor (m fuel : ℕ) (v : List ℕ) (s : FloorData) (code : ℕ) : Bool :=
  let r := min s.pairMask.log2 (m-1)
  let pv := v.map (slice m s.pairMask r)
  let av := replay 5 code (0::s.basis)
  fuel+paidCount 5 code<s.lower+pv.count 0 && pv.all (fun x => av.contains x)
lemma deadCount (f : ℕ→ℕ) {v : List ℕ} (nd : v.Nodup) :
    dead f v.toFinset=(v.map f).count 0 := by
  unfold dead
  have E : v.toFinset.filter (fun x => f x=0) = (v.filter (fun x => decide (f x=0))).toFinset := by ext x;simp
  rw [E,List.toFinset_card_of_nodup (nd.filter _)]
  simp only [List.count_eq_countP,List.countP_map]
  rw [List.countP_eq_length_filter]
  congr 2

theorem floor_consistent {m fuel : ℕ} (pos : 0<m) {v : List ℕ} (ok : feasible m fuel v) (s : FloorData)
    (known : Floor m s) (code : ℕ) : contradictsFloor m fuel v s code=false := by
  let r := min s.pairMask.log2 (m-1)
  let p := projection m s.pairMask r (show r<m by dsimp [r];omega)
  let pv := v.map p.toFun
  let av := replay 5 code (0::s.basis)
  obtain ⟨k,hk,live,nd⟩ := ok
  obtain ⟨l,T,lim,pr,inside⟩ := projectLive p live
  rw [deadCount _ nd] at lim
  apply Bool.eq_false_iff.mpr
  intro bad
  change (decide (fuel+paidCount 5 code < s.lower+pv.count 0) && pv.all (fun x => av.contains x))=true at bad
  simp only [Bool.and_eq_true] at bad
  obtain ⟨lo,mem⟩ := bad
  have low := of_decide_eq_true lo
  have final : Possible m l av := by
    refine ⟨l,T,le_rfl,pr,?_⟩
    intro x hx
    have active : x∈pv := by simpa [pv] using inside x hx
    exact List.contains_iff_mem.mp (List.all_eq_true.mp mem x active)
  have size := known _ (replay_back 5 code (0::s.basis) (by simp) final)
  change l+pv.count 0≤k at lim
  omega

def Memo := ℕ → FloorData × ℕ
def Certified (m : ℕ) (db : Memo) := ∀ i,Floor m (db i).1
inductive Advice where
  | plain
  | restrict (which : ℕ)
  | saved (index : ℕ)
  | fork (codes : ℕ) (nested : List Advice)
deriving Inhabited
def chooseAdvice (tag : ℕ) (gs : List Advice) : Advice :=
  if tag=1 then gs.headD .plain else if tag=0 then .plain else if tag<1024 then .restrict (tag-2) else .saved (tag-1024)
def memoRows (go : Advice → List ℕ → Bool) : List (List ℕ) → ℕ → List Advice → Bool
  | [],_,_ => false
  | v::vs,code,gs =>
    let tag := code &&& 4095
    go (chooseAdvice tag gs) v || memoRows go vs (code >>> 12) (if tag=1 then gs.tail else gs)
lemma memoRows_ok {go : Advice→List ℕ→Bool} {v : List ℕ} {vs : List (List ℕ)} (mem : v∈vs)
    (all : ∀ g,go g v=true) (code : ℕ) (gs : List Advice) : memoRows go vs code gs=true := by
  induction vs generalizing code gs with
  | nil => simp at mem
  | cons x xs ih =>
    rw [memoRows,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|next
    · exact Or.inl (all _)
    · exact Or.inr (ih next _ _)
def audited (m : ℕ) (db : Memo) : ℕ → Advice → List ℕ → Bool
  | 0,_,v => terminal m v
  | k+1,.plain,v => search m (k+1) v
  | k+1,.restrict which,v => cutSearch m (zeroPairs m v which (full m)) (k+1) v
  | k+1,.saved i,v => !(contradictsFloor m (k+1) v (db i).1 (db i).2)
  | k+1,.fork code gs,v => terminal m v || memoRows (audited m db k) (successors m k v) code gs
theorem audited_complete {m : ℕ} (hm : 0<m) (db : Memo) (safe : Certified m db)
    (fuel : ℕ) (v : List ℕ) (h : feasible m fuel v) (g : Advice) : audited m db fuel g v=true := by
  induction fuel generalizing v g with
  | zero =>
    obtain ⟨j,lim,live,nd⟩ := h
    exact complete m 0 live lim v rfl nd
  | succ k ih =>
    cases g with
    | plain =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact complete m (k+1) live lim v rfl nd
    | restrict which =>
      obtain ⟨j,lim,live,nd⟩ := h
      exact cut_complete hm live v rfl nd _ _ lim
    | saved i => simp [audited,floor_consistent hm h _ (safe i) _]
    | fork code gs =>
      rw [audited,Bool.or_eq_true]
      rcases move h with endNow|⟨w,hw,next⟩
      · exact Or.inl endNow
      · exact Or.inr (memoRows_ok hw (fun g => ih w next g) _ _)
lemma offAudit {m k v g} {db : Memo} (safe : Certified m db) (pos : 0<m) (e : audited m db k g v=false) : Excluded m k v := by
  intro h;exact Bool.noConfusion (e.symm.trans (audited_complete pos db safe k v h g))
lemma offMemoRows {m k : ℕ} {vs : List (List ℕ)} {i n code : ℕ} {gs : List Advice} {db : Memo}
    (safe : Certified m db) (pos : 0<m)
    (e : memoRows (audited m db k) ((vs.drop i).take n) code gs=false) : Block m k vs i n := by
  intro w hw h
  exact Bool.noConfusion (e.symm.trans (memoRows_ok hw (fun g => audited_complete pos db safe k w h g) code gs))
end Theta

namespace Theta

/- The 87 pairs below differ in one input bit. Every pair contains one positive and one negative assignment for the specified graph. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def graph (x : Fin 7 → Bool) := ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any (fun e => x e.1 && x e.2)
def posBits : ℕ := 0x1c74e5c7c3464c58a94a8d0e8c98b0e84889d1e366bc1c326395aad4f9162662a51a84571e1e3b69d1e3761c19a858ad264589d0233569d1f3160e94a870b92a4c8b90a22950f103220c0c883
def negBits : ℕ := 0x1870e1c383060c10a142850a0c1830604080d1a3468c183060952a54a9122442850a04070e1c3868d1a3460c182850a122448910203468d1a3060c142850a122448910202850a102020408081
def sample (bank : ℕ) (i : Fin 87) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 87, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (87+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 87, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 87, ∀ b∈inputs, b.testBit i.val≠b.testBit (87+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 87 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 87 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 87 out.2 := by
    intro i hi same
    let j : Fin 87 := ⟨i,hi⟩
    have diff : read i out=read (87+i) out := by simp [read,same]
    have p := ev i;have n := ev (87+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩
end Theta

namespace Theta

/- The matching upper bound groups the eight edges at vertices 1, 4, 5 and 6. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def eleven : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[7,5]⟩,⟨.and,[1,8]⟩,⟨.and,[0,4]⟩,⟨.and,[3,5]⟩,
    ⟨.or,[2,4]⟩,⟨.or,[12,3]⟩,⟨.and,[6,13]⟩,⟨.or,[9,10]⟩,⟨.or,[11,14]⟩,⟨.or,[15,16]⟩],17⟩
theorem upper_fan : FanInTwo eleven := by
  intro g hg
  simp only [eleven,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
theorem upper_cost : eleven.gates.countP counted=11 := by decide +kernel
theorem upper_match : circuitFun 7 eleven=graph := by
  funext x
  have all : ∀ a b c d e f g : Bool, circuitFun 7 eleven ![a,b,c,d,e,f,g] = graph ![a,b,c,d,e,f,g] := by decide +kernel
  have tab : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6] := by funext i;fin_cases i <;> rfl
  conv_lhs => rw [tab]
  conv_rhs => rw [tab]
  apply all
end Theta

namespace Theta

/- These are all 84 possibilities after the first live binary gate. The lists of transpositions below are graph automorphisms acting on the 87 pairs. -/
def s00 : List ℕ := [0x3c000003c70000000000007800008f8e000002004000,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s01 : List ℕ := [0x3fc1e3ffffc00003c079c1ffc7c7ffffaab2afa5f797,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s02 : List ℕ := [0x1e00000000003c079c18007c0000008922d81b387,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s03 : List ℕ := [0x3c003fc38c0000000000007c0077071a22080240410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s04 : List ℕ := [0x3c01e000000000000000007807c00400000004008200,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s05 : List ℕ := [0x3ffffc03c7000003c079c1fffffccfce4cdb3fc9fbc7,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s06 : List ℕ := [0x3c7000003c079c18000008b8e08922b817187,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s07 : List ℕ := [0x3fe1c000000000000000007f83c4040444910480840,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ffffc00000000000000007ffffc4440444914488a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s08 : List ℕ := [0x804400082008020811085,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s09 : List ℕ := [0x3c3fe003c703c0f3c7f9cff8ffc19f9e9f97ef9ff3bf,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s10 : List ℕ := [0x3e00000003c0f007800e00f80110109705c01e0038,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s11 : List ℕ := [0x3c01e003c7000003c079c1f003808f0c08120f00e302,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s12 : List ℕ := [0x8c0011092820080040010,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s13 : List ℕ := [0x3ffe03ffffc3c0f007800e7ffc47ffffb7a5e2bf54bd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s14 : List ℕ := [0x3e00000003c0f007800e003c4000001585609b10ad,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s15 : List ℕ := [0x3fc003ffffc00000000000770006ef6d202002204400,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s16 : List ℕ := [0x3e00000000000000000008fc400000040100080000,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s17 : List ℕ := [0x3ffffc000003c0f007800e7ffffd54d2d7cdf4df9afd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s18 : List ℕ := [0x3c0f007800e00000110929384e09710bd,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s19 : List ℕ := [0x3fc1fc00000000000000007703bc4440404814408a40,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s20 : List ℕ := [0x3c0000003c001c01000808780080207800380,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s21 : List ℕ := [0x3c01e3c3ff3c0703f879f1f90fcf8ffe799e6ff3f3ef,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s22 : List ℕ := [0x3c0383c070038003001080f0070710c40720068,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s23 : List ℕ := [0x3c01e00007000000007801e80740080e00902801f007,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s24 : List ℕ := [0x80100901104409200a8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s25 : List ℕ := [0x3e03c3f83fc7f3ff81fe19fccf97f2ff8fe7ff13fd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s26 : List ℕ := [0x3c3f83c0703f801f011008e8760680a07600340,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s27 : List ℕ := [0x3e00000003c0f007800e08f44010028681a00d1015,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s28 : List ℕ := [0x3c0003c07000000000000078200790e41000100,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s29 : List ℕ := [0x3fff83ffffff801f0552aaffff87ffffff223ea,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s30 : List ℕ := [0x3f8000003f801f011088805f0000006f202e8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s31 : List ℕ := [0x3c0003f8fc000000442220780806f1b8002002,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s32 : List ℕ := [0x3c3f800000000000011000787f0200002200000,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s33 : List ℕ := [0x3fc003fffffc0703f801f07fc88ffffffb2ec7f647f8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s34 : List ℕ := [0x3c0703f801f00008880000590e45d203e8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s35 : List ℕ := [0x3fc0003c07c000000000006ec000780f822080044410,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s36 : List ℕ := [0x11088c0440400804400240,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s37 : List ℕ := [0x3fffffc3f83c0703f801f07fffffc7f07d4f57fa8be8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s38 : List ℕ := [0x3c3f83c0703f801f000000383b0390643b201a8,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s39 : List ℕ := [0x3ffffc00000000000000006ef7704000044110088800,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s40 : List ℕ := [0x3c07800200100010408900781f000,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s41 : List ℕ := [0x3c01e003c73ff803ffffc1fa17d2afaf7ff22fffff87,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s42 : List ℕ := [0x3ff8003f860002101220217760007e0c00,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s43 : List ℕ := [0x3c01e003c70000000001c1d806c08e8a000228000387,0x3ff803fffe0022111221257ff007fffc00,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s44 : List ℕ := [0x3c00007800000100000001780009f1000,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s45 : List ℕ := [0x3e0000003ff8f3fffe0e2afd5331b7fff5e7fffcbd,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s46 : List ℕ := [0x3c3803f87e00220112212568700760ec00,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s47 : List ℕ := [0x3e0000000000f000000e08ec4110928005e00000bd,0x3ff803fffe0022111221257ff007fffc00,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s48 : List ℕ := [0x3c0003f800000000020120790007f20000,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s49 : List ℕ := [0x3c3f83fff03fffff033199fa7f57ffe47ffffe8,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s50 : List ℕ := [0x3f80007fe00221110200506f0000dfc00,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s51 : List ℕ := [0x3c3f80007000001f011088d86d0000e400003e8,0x3ff803fffe0022111221257ff007fffc00,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s52 : List ℕ := [0x3ff80000000000000220007ff001002000,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s53 : List ℕ := [0x3fc003ffffffffe00663337fb2d7ffffffffd02,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s54 : List ℕ := [0x3fffe002211100125000006ffdc00,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s55 : List ℕ := [0x3fc000007fc000000442225da08000ff8000102,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s56 : List ℕ := [0x2200022125222002244400,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s57 : List ℕ := [0x3fc003fffffff803fffe007fd117fffffff087fffc10,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s58 : List ℕ := [0x3ff803fffe0000111000005dd005dbb800,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s59 : List ℕ := [0x3fc003ffffc000000000005dc005deda800080000010,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40]
def s60 : List ℕ := [0x2211100000444004488800,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s61 : List ℕ := [0x3ffffc00003ff803fffe007ffffe65657ff917fffe40,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s62 : List ℕ := [0x3ff803fffe0000000221253bb003b77400,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s63 : List ℕ := [0x3ffffc00000000000000005deeec4440000910000240,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s64 : List ℕ := [0x4002008a08089229002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s65 : List ℕ := [0x3c01e3ffc73fffffc079c1fc27e7ff8e7fffff81f387,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s66 : List ℕ := [0x3fc003ffffc0000000420277000776dd0000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s67 : List ℕ := [0x3c01e003c7000003c079c1b805c0058600000681d285,0x3fc003ffffc000000442227fa087ffff9002102,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s68 : List ℕ := [0x3c0f000000000200110001785e0000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s69 : List ℕ := [0x3e03fc003ffffc07800e4cfe67fa9afffff99f31bf,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s70 : List ℕ := [0x3fc003c3f0c000000440226ea08687a19002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s71 : List ℕ := [0x3e00000000000007800e08dc4000928000009f10bd,0x3fc003ffffc000000442227fa087ffff9002102,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40]
def s72 : List ℕ := [0x3fc00000000000000440007fa08222080000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s73 : List ℕ := [0x3fc003fffffffffc0000007fe227fffffffffb246512,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s74 : List ℕ := [0x3ffffc00000000222000005ddf79002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s75 : List ℕ := [0x3fc00003ffc000000000003bc00005f7800002244410,0x3fc003ffffc000000442227fa087ffff9002102,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3ffffc00000000000000007ffffc4440444914488a40]
def s76 : List ℕ := [0x4422244000444910000000,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s77 : List ℕ := [0x3ffffffc003ffffc0000007ffffffe487ffffd48ab42,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s78 : List ℕ := [0x3fc003ffffc000000000003ba083bb6e9002102,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s79 : List ℕ := [0x3ffffc00000000000000003bddd80440000004488a40,0x3fc003ffffc000000442227fa087ffff9002102,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000000007fc007ffffa22082244410]
def s80 : List ℕ := [0x3fc00000000000000000007fc0044440000000000000,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s81 : List ℕ := [0x3fffffffffc000000000007fffffffffe669966cce50,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s82 : List ℕ := [0x3ffffc00000000000000003bbbfa22082244410,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def s83 : List ℕ := [0x3ffc0000000000000000003ff80000444914488a40,0x3fc003ffffc000000000007fc007ffffa22082244410,0x3ffffc00000000000000007ffffc4440444914488a40,0x3c01e003c7000003c079c1f807c08f8e08922f81f387,0x3e00000003c0f007800e08fc4110929785e09f10bd,0x3c3f83c0703f801f011088f87f0790e47f203e8,0x3ff803fffe0022111221257ff007fffc00,0x3fc003ffffc000000442227fa087ffff9002102]
def firstLayer : List (List ℕ) := [s00,s01,s02,s03,s04,s05,s06,s07,s08,s09,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50,s51,s52,s53,s54,s55,s56,s57,s58,s59,s60,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71,s72,s73,s74,s75,s76,s77,s78,s79,s80,s81,s82,s83]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem firstLayer_eq : successors 87 9 inputs=firstLayer := by decide +kernel
def perm0 : List (ℕ×ℕ) := []
def perm1 : List (ℕ×ℕ) := [(0,11),(1,10),(2,68),(3,67),(4,69),(5,6),(7,22),(8,21),(9,20),(12,15),(13,14),(16,72),(17,71),(18,73),(19,70),(23,26),(24,25),(27,48),(28,47),(29,81),(30,80),(31,82),(32,79),(33,53),(34,54),(35,52),(36,50),(37,51),(38,49),(39,85),(40,84),(41,86),(42,83),(43,56),(44,58),(45,57),(46,55),(59,61),(60,62),(63,65),(64,66),(74,76),(77,78)]
def perm2 : List (ℕ×ℕ) := [(0,28),(1,27),(2,69),(3,67),(4,68),(5,6),(7,35),(8,33),(9,34),(10,48),(11,47),(12,62),(13,59),(14,61),(15,60),(16,82),(17,80),(18,81),(19,79),(20,54),(21,53),(22,52),(23,66),(24,63),(25,65),(26,64),(29,73),(30,71),(31,72),(32,70),(36,51),(37,50),(38,49),(39,86),(40,84),(41,85),(42,83),(43,57),(44,58),(45,56),(46,55),(74,77),(76,78)]
def perm3 : List (ℕ×ℕ) := [(0,47),(1,48),(2,4),(7,52),(8,53),(9,54),(10,27),(11,28),(12,60),(13,61),(14,59),(15,62),(16,31),(17,30),(18,29),(19,32),(20,34),(21,33),(22,35),(23,64),(24,65),(25,63),(26,66),(36,37),(39,41),(43,45),(50,51),(56,57),(68,69),(70,79),(71,80),(72,82),(73,81),(74,78),(76,77),(85,86)]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe0 : ∀ p∈perm0,p.1<87 ∧ p.2<87 := by
  have good : perm0.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe1 : ∀ p∈perm1,p.1<87 ∧ p.2<87 := by
  have good : perm1.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe2 : ∀ p∈perm2,p.1<87 ∧ p.2<87 := by
  have good : perm2.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem safe3 : ∀ p∈perm3,p.1<87 ∧ p.2<87 := by
  have good : perm3.all (fun p => decide (p.1<87 ∧ p.2<87))=true := by decide +kernel
  intro p hp;exact of_decide_eq_true (List.all_eq_true.mp good p hp)
end Theta

namespace Theta

/- The orbit identities reduce the first layer to 28 representatives. -/
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym3 : feasible 87 9 s03 → feasible 87 9 s02 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym12 : feasible 87 9 s12 → feasible 87 9 s08 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym13 : feasible 87 9 s13 → feasible 87 9 s09 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym14 : feasible 87 9 s14 → feasible 87 9 s10 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym15 : feasible 87 9 s15 → feasible 87 9 s11 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym19 : feasible 87 9 s19 → feasible 87 9 s18 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym28 : feasible 87 9 s28 → feasible 87 9 s20 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym29 : feasible 87 9 s29 → feasible 87 9 s21 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym30 : feasible 87 9 s30 → feasible 87 9 s22 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym31 : feasible 87 9 s31 → feasible 87 9 s23 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym32 : feasible 87 9 s32 → feasible 87 9 s20 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym33 : feasible 87 9 s33 → feasible 87 9 s21 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym34 : feasible 87 9 s34 → feasible 87 9 s22 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym35 : feasible 87 9 s35 → feasible 87 9 s23 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym36 : feasible 87 9 s36 → feasible 87 9 s24 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym37 : feasible 87 9 s37 → feasible 87 9 s25 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym38 : feasible 87 9 s38 → feasible 87 9 s26 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym39 : feasible 87 9 s39 → feasible 87 9 s27 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym43 : feasible 87 9 s43 → feasible 87 9 s42 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym44 : feasible 87 9 s44 → feasible 87 9 s04 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym45 : feasible 87 9 s45 → feasible 87 9 s05 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym46 : feasible 87 9 s46 → feasible 87 9 s06 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym47 : feasible 87 9 s47 → feasible 87 9 s07 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym48 : feasible 87 9 s48 → feasible 87 9 s20 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym49 : feasible 87 9 s49 → feasible 87 9 s21 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym50 : feasible 87 9 s50 → feasible 87 9 s23 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym51 : feasible 87 9 s51 → feasible 87 9 s22 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym52 : feasible 87 9 s52 → feasible 87 9 s00 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym53 : feasible 87 9 s53 → feasible 87 9 s01 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym54 : feasible 87 9 s54 → feasible 87 9 s02 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym55 : feasible 87 9 s55 → feasible 87 9 s02 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym59 : feasible 87 9 s59 → feasible 87 9 s58 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym60 : feasible 87 9 s60 → feasible 87 9 s08 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym61 : feasible 87 9 s61 → feasible 87 9 s09 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym62 : feasible 87 9 s62 → feasible 87 9 s11 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym63 : feasible 87 9 s63 → feasible 87 9 s10 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym64 : feasible 87 9 s64 → feasible 87 9 s56 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym65 : feasible 87 9 s65 → feasible 87 9 s57 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym66 : feasible 87 9 s66 → feasible 87 9 s58 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym67 : feasible 87 9 s67 → feasible 87 9 s58 := perm_feasible perm1 safe1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym68 : feasible 87 9 s68 → feasible 87 9 s04 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym69 : feasible 87 9 s69 → feasible 87 9 s05 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym70 : feasible 87 9 s70 → feasible 87 9 s06 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym71 : feasible 87 9 s71 → feasible 87 9 s07 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym72 : feasible 87 9 s72 → feasible 87 9 s40 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym73 : feasible 87 9 s73 → feasible 87 9 s41 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym74 : feasible 87 9 s74 → feasible 87 9 s42 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym75 : feasible 87 9 s75 → feasible 87 9 s42 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym76 : feasible 87 9 s76 → feasible 87 9 s08 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym77 : feasible 87 9 s77 → feasible 87 9 s09 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym78 : feasible 87 9 s78 → feasible 87 9 s11 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym79 : feasible 87 9 s79 → feasible 87 9 s10 := perm_feasible perm2 safe2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym80 : feasible 87 9 s80 → feasible 87 9 s04 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym81 : feasible 87 9 s81 → feasible 87 9 s05 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym82 : feasible 87 9 s82 → feasible 87 9 s06 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem sym83 : feasible 87 9 s83 → feasible 87 9 s07 := perm_feasible perm3 safe3 (by decide +kernel) (by decide +kernel)
end Theta

namespace Theta

/- These 41 restricted instances are checked independently. The receipts below contain at most two binary operations for each retained symmetry representative. -/
def floorData0 : FloorData := ⟨0x7f83f7071f76dd07e0c78,8,[0x0,0x3c0000000380e007000c00f80110109705c01e0038,0x3803838060038003001080f0070710c40720068,0x3bb0003f060002101220217760007e0c00,0x3b8003bb6e80000007c27e7ff8e7fffff81f387,0x3fc3e3ffffc44917c0f9c3ffc7c7ffffaab2afa5f797,0x3ffffc47c7044917c0f9c3fffffccfce4cdb3fc9fbc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof0 : Floor 87 floorData0 := floorChecked (by decide +kernel)
def floorData1 : FloorData := ⟨0x6ef770780f86f1b80dfc17,8,[0x3c85e7c3ff3c8723f979f5f90fcf8ffe799e6ff3f3ef,0x3a0000000340d006800a08f44010028681a00d1015,0x0,0x3780006fe00221110200506f0000dfc00,0x3c000378dc000000552aaffff87ffffff223ea,0x3fc447fffffc8723f901f47fc88ffffffb2ec7f647f8,0x3fffffc3f83c8723f901f47fffffc7f07d4f57fa8be8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof1 : Floor 87 floorData1 := floorChecked (by decide +kernel)
def floorData2 : FloorData := ⟨0x5deeeddeda800ff80003ff,8,[0x3d09e913d7bff803ffffc1fa17d2afaf7ff22fffff87,0x360000000000f000000e08ec4110928005e00000bd,0x2c3680007000001f011088d86d0000e400003e8,0x0,0x2ec000007fc000000663337fb2d7ffffffffd02,0x3fc88bfffffff803fffe007fd117fffffff087fffc10,0x3ffffd1092bff803fffe007ffffe65657ff917fffe40]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof2 : Floor 87 floorData2 := floorChecked (by decide +kernel)
def floorData3 : FloorData := ⟨0x3bddd805f7800006ffdefd,8,[0x3e11f3ffc73fffffc079c1fc27e7ff8e7fffff81f387,0x2e00000000000007800e08dc4000928000009f10bd,0x2f800000378017011088805f0000006f202e8,0x37fee00663337fb2d7ffffffffd02,0x0,0x3fd113fffffffffc8010817fe227fffffffffb246512,0x3ffffffd043ffffc8010817ffffffe487ffffd48ab42]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof3 : Floor 87 floorData3 := floorChecked (by decide +kernel)
def floorData4 : FloorData := ⟨0x3ff800005ddf7ddbbbef,8,[0x1e00000000002c059c18007c0000008922d81b387,0x3ffe03ffffd3d0f117a20e7ffc47ffffb7a5e2bf54bd,0x2c0702e801f00008880000590e45d203e8,0x2ee802eddc0000111000005dd005dbb800,0x2eefbc0000007fe227fffffffffb246512,0x0,0x3fffffffffd110411222087fffffffffe669966cce50]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof4 : Floor 87 floorData4 := floorChecked (by decide +kernel)
def floorData5 : FloorData := ⟨0x7703beef6d687a1f60ef42,7,[0x3c7fe08bcf4bc2f3cff9dff8ffc19f9e9f97ef9ff3bf,0x0,0x343b0340503b001a011008e8760680a07600340,0x343803b07600220112212568700760ec00,0x37400343d0c0000004cfe67fa9afffff99f31bf,0x3ffe23ffffcbc2f04f885efffc47ffffb7a5e2bf54bd,0x3ffffc88494bc2f04f885efffffd54d2d7cdf4df9afd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof5 : Floor 87 floorData5 := floorChecked (by decide +kernel)
def floorData6 : FloorData := ⟨0x3d81800718000007e0c78,7,[0x0,0x2c00000000000007000c00d80000108000001e0038,0x380000003800300108080070000000720068,0x3f06007e37f7ffaf7fffffffff87,0x0,0x3fd3f3ffffffffffc0f9c3ffe7e7ffffffffffa5f797,0x3fffffffc73fffffc0f9c3ffffffffce7fffffc9fbc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof6 : Floor 87 floorData6 := floorChecked (by decide +kernel)
def floorData7 : FloorData := ⟨0x2ee80000000f780003ef,7,[0x16000000000000001c18006c00000000228000387,0x3ffe8bfffffff8f3fffe0e7ffd57fffffff5e7fffcbd,0x7000001f00008880000000e400003e8,0x0,0x7bc0000007ff337fffffffffffffd12,0x0,0x3ffffffffffff843fffe087ffffffffffff997fffe50]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof7 : Floor 87 floorData7 := floorChecked (by decide +kernel)
def floorData8 : FloorData := ⟨0x3bbbfbbb6ebb775bf,7,[0x1c7000001c038c18000008b8e08922b817187,0x1c07003800e00000110929384e09710bd,0x3fffffe3f83e278bfc45f07fffffc7f07d4f57fa8be8,0x1dd801dbba007ffffe65657ff917fffe40,0x3ffffffe203ffffe2445207ffffffe487ffffd48ab42,0x3fffffffffe2248a2445207fffffffffe669966cce50,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof8 : Floor 87 floorData8 := floorChecked (by decide +kernel)
def floorData9 : FloorData := ⟨0x7003e6061606810600c40,5,[0x0,0x0,0x3003030040030002001000e0060600800600040,0x3030003006000200122021606000600c00,0x330003034080000007cffe7ff9effffff9ff3bf,0x3fffe3ffffcfcbf7cff9dfffffc7ffffbfb7efbff7bf,0x3ffffccfcf4fcbf7cff9dffffffddfdedfdfffdffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof9 : Floor 87 floorData9 := floorChecked (by decide +kernel)
def floorData10 : FloorData := ⟨0x6f03070018661900c0c10,5,[0x0,0x380000000300c006000800f00010008601800c0010,0x0,0x3300006060002101020010660000c0c00,0x38000330c80000007d2feffffe7ffffff3f3ef,0x3fc7e7fffffccf37f9f9f7ffcfcffffffbbeeff7f7ff,0x3fffffc7ff3ccf37f9f9f7ffffffcffe7ddf7ffbfbef]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof10 : Floor 87 floorData10 := floorChecked (by decide +kernel)
def floorData11 : FloorData := ⟨0x660330680d00701800ec02,5,[0x3cffe7cbff7fc7f3fff9fff9ffcf9ffeff9feffff3ff,0x0,0x0,0x3800007600220110200500700000ec00,0x340000380c0000005dfeeffffaffffffff33ff,0x3ffe67ffffffc7f3ff89fefffccfffffffafe7ff57fd,0x3fffffcbf97fc7f3ff89feffffffd7f2ffcff7ff9bfd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof11 : Floor 87 floorData11 := floorChecked (by decide +kernel)
def floorData12 : FloorData := ⟨0x5e82d5050800dd0000078,5,[0x0,0x340000000000e000000c00e80110108005c0000038,0x2802800060000003001080d0050000c40000068,0x0,0x2a8000006e80000007e37f7ffaf7fffffffff87,0x3fcbebfffffff917ffffc3ffd7d7fffffff2afffff97,0x3ffffd57d7bff917ffffc3fffffeefef7ffb3fffffc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof12 : Floor 87 floorData12 := floorChecked (by decide +kernel)
def floorData13 : FloorData := ⟨0x4ce660580a8001b8000017,5,[0x3d8defd3ffbfff23fffff5fb1fdfafff7ffe6fffffef,0x320000000000d000000a08e44010028001a0000015,0x0,0x0,0x2c000000dc000000773bbffffd7fffffffffea,0x3fcccfffffffff23fffff47fd99ffffffffec7fffff8,0x3fffffd3fabfff23fffff47fffffe7f57fff57ffffe8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof13 : Floor 87 floorData13 := floorChecked (by decide +kernel)
def floorData14 : FloorData := ⟨0x2ad55000078000000ddc15,5,[0x3e95f7ffff3ffffff979f5fd2feffffe7ffffff3f3ef,0x2a00000000000006800a08d44000028000000d1015,0x0,0x6ee00773bbffffd7fffffffffea,0x0,0x3fd557fffffffffff911f57feaaffffffffffff667fa,0x3ffffffffc3ffffff911f57ffffffff87ffffffaabea]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof14 : Floor 87 floorData14 := floorChecked (by decide +kernel)
def floorData15 : FloorData := ⟨0x19ccc804d28000000002fd,5,[0x3f19fbffd7bfffffffffc1fe37f7ffaf7fffffffff87,0x2600000000000000000e08cc4000928000000000bd,0x268000000000170773bbffffd7fffffffffea,0x0,0x0,0x3fd99bfffffffffffffe817ff337fffffffffffffd12,0x3ffffffd96bffffffffe817fffffff6d7fffffffff42]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof15 : Floor 87 floorData15 := floorChecked (by decide +kernel)
def floorData16 : FloorData := ⟨0x38380000554d505a0868,5,[0x0,0x3fffe3ffffd7d9f7d7fbcfffffc7ffffbfb7efbff7bf,0x2806002800300008080000510c40520068,0x2aa0002d040000101000005540005a0800,0x2aa6a80000007fe7e7ffffffffffa5f797,0x0,0x3fffffffffd55957d2fbcbffffffffffeefbbfedffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof16 : Floor 87 floorData16 := floorChecked (by decide +kernel)
def floorData17 : FloorData := ⟨0x3b80000485a1d40ab42,5,[0x3fffe3ffffdbd2f3dffbdfffffc7ffffbfb7efbff7bf,0x0,0x240502a001a00000880000480a05400340,0x242802a05400000110000048500540a800,0x242d0c0000007ffe67fffffffffbbf75bf,0x0,0x3fffffffffdbd2f15faa5efffffffffff7edf6ffdefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof17 : Floor 87 floorData17 := floorChecked (by decide +kernel)
def floorData18 : FloorData := ⟨0x3770000004d13809b807,5,[0x1a00000000000005801800740000000902801b007,0x3ffe47ffffffd7f3ffa3fe7ffccfffffffafe7ff57fd,0x0,0x2680004dc00001110000004d00009b800,0x2689c0000007feaaffffffffffff667fa,0x0,0x3ffffffffffd9763fb23fc7fffffffffff6fd7fecff8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof18 : Floor 87 floorData18 := floorChecked (by decide +kernel)
def floorData19 : FloorData := ⟨0x1dd80000000004db9aed,5,[0xe000000000024049408005c00000000004819285,0x3fff13fffffffffd97b28f7ffe67fffffffffbbf75bf,0x26801700008880000000004d202e8,0x26dcc007ff337fffffffffffffd12,0x0,0x0,0x3ffffffffffffffd9232897fffffffffffffff6cef52]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof19 : Floor 87 floorData19 := floorChecked (by decide +kernel)
def floorData20 : FloorData := ⟨0x380f82b0a8057417,5,[0x7000000003801800000080e009028017007,0x1405002800a00000010028280a0051015,0x0,0x1580002ba007fffffe7f57fff57ffffe8,0x3ffffffff83ffffffd45f47ffffffff87ffffffaabea,0x3ffffffffffea7abfd45f47fffffffffff6fd7fecff8,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof20 : Floor 87 floorData20 := floorChecked (by decide +kernel)
def floorData21 : FloorData := ⟨0x19a9a8006e80001bf,5,[0x1450000000000c18000008a8a000228000187,0x7000000e7fffff75f7fffdf7fffefd,0x3ffffff3fabfff8bfffff07fffffe7f57fff57ffffe8,0x0,0x3ffffffeb2bfffffffff207fffffff6d7fffffffff42,0x3ffffffffffffc8bffff207ffffffffffff997fffe50,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof21 : Floor 87 floorData21 := floorChecked (by decide +kernel)
def floorData22 : FloorData := ⟨0x1b7800002b754bd,5,[0x3fffffffe73fffffe47de1ffffffffce7fffffc9fbc7,0x3800e00000000928000009710bd,0x3ffffffffc3ffffffc55f17ffffffff87ffffffaabea,0x15baa007fffffff6d7fffffffff42,0x0,0x3ffffffffffffffea455a17fffffffffffffff6cef52,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof22 : Floor 87 floorData22 := floorChecked (by decide +kernel)
def floorData23 : FloorData := ⟨0x600306001006010000c00,4,[0x0,0x0,0x0,0x30000006000200102001006000000c00,0x30000030080000007dffeffffefffffffff3ff,0x3fffe7ffffffcff7fff9ffffffcfffffffbfeffff7ff,0x3fffffcfff7fcff7fff9ffffffffdffeffdffffffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof23 : Floor 87 floorData23 := floorChecked (by decide +kernel)
def floorData24 : FloorData := ⟨0x5502acce48000a18000342,4,[0x3d7fe99bdffffaf3ffffdffaffd3bfbffff7efffffbf,0x0,0x243200005000001a011008c8640000a00000340,0x0,0x2640000050c0000006eff77fbbffffffffffdbf,0x3ffeabfffffffaf3fffe5efffd57fffffff5e7fffcbd,0x3ffffd98dbfffaf3fffe5effffff75f7fffdf7fffefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof24 : Floor 87 floorData24 := floorChecked (by decide +kernel)
def floorData25 : FloorData := ⟨0x330198056500000660ce40,4,[0x3e7ff3ffcf7fffffcff9dffcffe7ff9effffff9ff3bf,0x0,0x2b00000033001201100880560000006600240,0x33066006eff77fbbffffffffffdbf,0x0,0x3fff33fffffffffccf98dffffe67fffffffffbbf75bf,0x3ffffffd4d7ffffccf98dffffffffedafffffddfbbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof25 : Floor 87 floorData25 := floorChecked (by decide +kernel)
def floorData26 : FloorData := ⟨0x300180061000000600c40,4,[0x0,0x0,0x300000003000200100080060000000600040,0x3006007efff7ffbfffffffffffbf,0x0,0x3ffff3ffffffffffcff9dfffffe7ffffffffffbff7bf,0x3fffffffcf7fffffcff9dfffffffffdeffffffdffbff]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof26 : Floor 87 floorData26 := floorChecked (by decide +kernel)
def floorData27 : FloorData := ⟨0x2d01000018000000c0c10,4,[0x0,0x2800000000000006000800d00000008000000c0010,0x0,0x606007f3fffffff7fffffffffef,0x0,0x3fd7f7fffffffffff9f9f7ffefeffffffffffff7f7ff,0x3fffffffff3ffffff9f9f7fffffffffe7ffffffbfbef]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof27 : Floor 87 floorData27 := floorChecked (by decide +kernel)
def floorData28 : FloorData := ⟨0x1c8080050800000000078,4,[0x0,0x2400000000000000000c00c8000010800000000038,0x280000000000307f3fffffff7fffffffffef,0x0,0x0,0x3fdbfbffffffffffffffc3fff7f7ffffffffffffff97,0x3fffffffd7bfffffffffc3ffffffffef7fffffffffc7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof28 : Floor 87 floorData28 := floorChecked (by decide +kernel)
def floorData29 : FloorData := ⟨0x330000000501800a802,4,[0x3fffe7ffffffd7f3fffbffffffcfffffffbfeffff7ff,0x0,0x0,0x2800005400000110000000500000a800,0x280c0000007ffeefffffffffffff77ff,0x0,0x3fffffffffffd7f3ffabfeffffffffffffeff7ffdffd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof29 : Floor 87 floorData29 := floorChecked (by decide +kernel)
def floorData30 : FloorData := ⟨0x28280000000d50000068,4,[0x0,0x3fffebfffffff9f7ffffcfffffd7fffffff7efffffbf,0x6000000300008080000000c40000068,0x0,0x6a80000007ff7f7ffffffffffffff97,0x0,0x3ffffffffffff957ffffcbfffffffffffffbbfffffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof30 : Floor 87 floorData30 := floorChecked (by decide +kernel)
def floorData31 : FloorData := ⟨0x2a80000000a18000342,4,[0x3fffebfffffffaf3ffffdfffffd7fffffff7efffffbf,0x0,0x5000001a00000880000000a00000340,0x0,0x50c0000007fff77fffffffffffffdbf,0x0,0x3ffffffffffffaf3fffe5efffffffffffffdf7fffefd]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof31 : Floor 87 floorData31 := floorChecked (by decide +kernel)
def floorData32 : FloorData := ⟨0x26600000000138000007,4,[0x12000000000000000018006400000000028000007,0x3ffecffffffffff3fffffe7ffddfffffffffe7fffffd,0x0,0x0,0x9c0000007ffbbffffffffffffffffa,0x0,0x3fffffffffffff63fffffc7fffffffffffffd7fffff8]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof32 : Floor 87 floorData32 := floorChecked (by decide +kernel)
def floorData33 : FloorData := ⟨0x181800000000005a0868,4,[0x0,0x3ffff3ffffffffffd7fbcfffffe7ffffffffffbff7bf,0x2800300008080000000000520068,0x2d04007ff7f7ffffffffffffff97,0x0,0x0,0x3fffffffffffffffd2fbcbffffffffffffffffedffd7]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof33 : Floor 87 floorData33 := floorChecked (by decide +kernel)
def floorData34 : FloorData := ⟨0xcc800000000000002ed,4,[0x6000000000000001408004c00000000000000285,0x3fff9bfffffffffffffe8f7fff77fffffffffffffdbf,0x1707ffbbffffffffffffffffa,0x0,0x0,0x0,0x3ffffffffffffffffffe897fffffffffffffffffff52]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof34 : Floor 87 floorData34 := floorChecked (by decide +kernel)
def floorData35 : FloorData := ⟨0x33031b324c0360438,4,[0x0,0x1806003000c00000110109304c0160038,0x3fffffe7ff3e6f9ffcfdf3ffffffcffe7ddf7ffbfbef,0x1990001b02007ffffeefef7ffb3fffffc7,0x3fffffffe73fffffe4fde3ffffffffce7fffffc9fbc7,0x3fffffffffe66d9fe4fde3ffffffffffeefbbfedffd7,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof35 : Floor 87 floorData35 := floorChecked (by decide +kernel)
def floorData36 : FloorData := ⟨0x180a8000a8000017,4,[0x5000000000001800000080a000028000007,0x5000000a7ffffff7f7fffff7fffffd,0x0,0x0,0x3ffffffffabffffffffff47ffffffffd7fffffffffea,0x3fffffffffffffabfffff47fffffffffffffd7fffff8,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof36 : Floor 87 floorData36 := floorChecked (by decide +kernel)
def floorData37 : FloorData := ⟨0x31800000360438,4,[0x0,0x3000c0000000010800000160038,0x3fffffffff3ffffffcfdf3fffffffffe7ffffffbfbef,0x1b02007fffffffef7fffffffffc7,0x0,0x3fffffffffffffffe4fde3ffffffffffffffffedffd7,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof37 : Floor 87 floorData37 := floorChecked (by decide +kernel)
def floorData38 : FloorData := ⟨0x7800000055415,4,[0x3fffffffff3ffffffd7df5fffffffffe7ffffffbfbef,0x2800a0000000002800000051015,0x0,0x2aa007ffffffffd7fffffffffea,0x0,0x3ffffffffffffffffd55f57ffffffffffffffffeeffa,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof38 : Floor 87 floorData38 := floorChecked (by decide +kernel)
def floorData39 : FloorData := ⟨0x1996699331af,4,[0xc018c18000000000089229813187,0xc0300180067ffffffffff7edf6ffdefd,0x3fffffffffff37cbfe67f87fffffffffff6fd7fecff8,0x3ffffffffffffccbffff287ffffffffffff997fffe50,0x3fffffffffffffff3667287fffffffffffffff6cef52,0x0,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof39 : Floor 87 floorData39 := floorChecked (by decide +kernel)
def floorData40 : FloorData := ⟨0x6680001af,4,[0xc18000000000000228000187,0x300000067ffffffffffffdf7fffefd,0x3fffffffffffffcbfffff87fffffffffffffd7fffff8,0x0,0x3fffffffffffffffffff287fffffffffffffffffff52,0x0,0x0]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem floorProof40 : Floor 87 floorData40 := floorChecked (by decide +kernel)
def floorLibrary : List FloorData := [floorData0,floorData1,floorData2,floorData3,floorData4,floorData5,floorData6,floorData7,floorData8,floorData9,floorData10,floorData11,floorData12,floorData13,floorData14,floorData15,floorData16,floorData17,floorData18,floorData19,floorData20,floorData21,floorData22,floorData23,floorData24,floorData25,floorData26,floorData27,floorData28,floorData29,floorData30,floorData31,floorData32,floorData33,floorData34,floorData35,floorData36,floorData37,floorData38,floorData39,floorData40]
def emptyFloor : FloorData := ⟨0,0,[]⟩
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem storedFloor (i : ℕ) : Floor 87 (floorLibrary.getD i emptyFloor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : floorLibrary[i]? with
  | none => exact fun _ _ => Nat.zero_le _
  | some s =>
    have mem := List.mem_of_getElem? e
    simp only [floorLibrary,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact floorProof0
    · exact floorProof1
    · exact floorProof2
    · exact floorProof3
    · exact floorProof4
    · exact floorProof5
    · exact floorProof6
    · exact floorProof7
    · exact floorProof8
    · exact floorProof9
    · exact floorProof10
    · exact floorProof11
    · exact floorProof12
    · exact floorProof13
    · exact floorProof14
    · exact floorProof15
    · exact floorProof16
    · exact floorProof17
    · exact floorProof18
    · exact floorProof19
    · exact floorProof20
    · exact floorProof21
    · exact floorProof22
    · exact floorProof23
    · exact floorProof24
    · exact floorProof25
    · exact floorProof26
    · exact floorProof27
    · exact floorProof28
    · exact floorProof29
    · exact floorProof30
    · exact floorProof31
    · exact floorProof32
    · exact floorProof33
    · exact floorProof34
    · exact floorProof35
    · exact floorProof36
    · exact floorProof37
    · exact floorProof38
    · exact floorProof39
    · exact floorProof40
def receipt (i : ℕ) : ℕ×ℕ := (if i<78 then (if i<39 then (if i<19 then (if i<9 then (if i<4 then (if i<2 then (if i<1 then (0,0) else (8,0)) else (if i<3 then (16,0) else (40,0))) else (if i<6 then (if i<5 then (37,0) else (5,0)) else (if i<7 then (1,0) else (if i<8 then (2,0) else (7,454))))) else (if i<14 then (if i<11 then (if i<10 then (0,474) else (3,0)) else (if i<12 then (6,474) else (if i<13 then (4,454) else (7,0)))) else (if i<16 then (if i<15 then (6,0) else (4,0)) else (if i<17 then (30,0) else (if i<18 then (33,0) else (5,454)))))) else (if i<29 then (if i<24 then (if i<21 then (if i<20 then (5,474) else (17,0)) else (if i<22 then (9,0) else (if i<23 then (7,74) else (6,394)))) else (if i<26 then (if i<25 then (0,394) else (1,2146694)) else (if i<27 then (4,74) else (if i<28 then (0,458) else (1,390))))) else (if i<34 then (if i<31 then (if i<30 then (6,398) else (18,0)) else (if i<32 then (0,398) else (if i<33 then (10,0) else (4,78)))) else (if i<36 then (if i<35 then (7,78) else (11,0)) else (if i<37 then (23,0) else (if i<38 then (20,0) else (0,462))))))) else (if i<58 then (if i<48 then (if i<43 then (if i<41 then (if i<40 then (6,458) else (1,454)) else (if i<42 then (2,454) else (26,0))) else (if i<45 then (if i<44 then (3,458) else (35,0)) else (if i<46 then (3,394) else (if i<47 then (6,462) else (6,142))))) else (if i<53 then (if i<50 then (if i<49 then (38,0) else (3,142)) else (if i<51 then (3,398) else (if i<52 then (6,466) else (21,0)))) else (if i<55 then (if i<54 then (0,466) else (12,0)) else (if i<56 then (3,466) else (if i<57 then (31,0) else (0,146)))))) else (if i<68 then (if i<63 then (if i<60 then (if i<59 then (3,146) else (13,0)) else (if i<61 then (36,0) else (if i<62 then (3,210) else (4,2195910)))) else (if i<65 then (if i<64 then (1,2195910) else (2,2195910)) else (if i<66 then (7,2195910) else (if i<67 then (3,474) else (0,414))))) else (if i<73 then (if i<70 then (if i<69 then (6,414) else (8,146)) else (if i<71 then (29,0) else (if i<72 then (6,146) else (2,74)))) else (if i<75 then (if i<74 then (0,210) else (5,464)) else (if i<76 then (24,0) else (if i<77 then (4,458) else (7,458)))))))) else (if i<117 then (if i<97 then (if i<87 then (if i<82 then (if i<80 then (if i<79 then (7,134) else (4,134)) else (if i<81 then (7,142) else (14,0))) else (if i<84 then (if i<83 then (4,334) else (4,462)) else (if i<85 then (19,0) else (if i<86 then (4,150) else (7,150))))) else (if i<92 then (if i<89 then (if i<88 then (22,0) else (4,470)) else (if i<90 then (25,0) else (if i<91 then (1,458) else (8,144)))) else (if i<94 then (if i<93 then (0,2163146) else (4,2163146)) else (if i<95 then (2,2163146) else (if i<96 then (3,2163146) else (7,2163146)))))) else (if i<107 then (if i<102 then (if i<99 then (if i<98 then (6,2163146) else (2,458)) else (if i<100 then (1,146) else (if i<101 then (1,82) else (15,0)))) else (if i<104 then (if i<103 then (1,338) else (8,150)) else (if i<105 then (1,150) else (if i<106 then (1,406) else (1,474))))) else (if i<112 then (if i<109 then (if i<108 then (8,266) else (8,330)) else (if i<110 then (2,470) else (if i<111 then (39,0) else (27,0)))) else (if i<114 then (if i<113 then (6,202) else (4,2146382)) else (if i<115 then (2,78) else (if i<116 then (6,210) else (2,142))))))) else (if i<136 then (if i<126 then (if i<121 then (if i<119 then (if i<118 then (7,334) else (2,1978702)) else (if i<120 then (2,334) else (7,462))) else (if i<123 then (if i<122 then (32,0) else (4,198)) else (if i<124 then (7,198) else (if i<125 then (7,202) else (0,2146702))))) else (if i<131 then (if i<128 then (if i<127 then (4,214) else (7,214)) else (if i<129 then (8,203) else (if i<130 then (28,0) else (6,266)))) else (if i<133 then (if i<132 then (0,266) else (0,270)) else (if i<134 then (6,270) else (if i<135 then (0,1716370) else (1,1716370)))))) else (if i<146 then (if i<141 then (if i<138 then (if i<137 then (3,1716370) else (6,1716370)) else (if i<139 then (2,150) else (if i<140 then (3,1978578) else (34,0)))) else (if i<143 then (if i<142 then (7,470) else (1,1978706)) else (if i<144 then (3,270) else (if i<145 then (4,405654) else (1,405654))))) else (if i<151 then (if i<148 then (if i<147 then (2,405654) else (7,405654)) else (if i<149 then (4,330) else (if i<150 then (7,330) else (0,2179546)))) else (if i<153 then (if i<152 then (1,2179546) else (3,2179546)) else (if i<154 then (6,2179546) else (if i<155 then (4,94) else (7,94)))))))))
def database : Memo := fun i => (floorLibrary.getD (receipt i).1 emptyFloor,(receipt i).2)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem certifiedDB : Certified 87 database := fun i => storedFloor (receipt i).1
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc0 : Excluded 87 9 s00 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x0 : Block 87 8 (successors 87 8 s01) 0 10 := offMemoRows (code:=0x40f400001401402001001001402401) (gs:=[(.fork 0x40c40b09240b00040a40b40b40a40a40940808a408000407408408407407000406052406000022000405022405404404403403402402 []),(.fork 0x8440e08440d404409403402402401 []),(.fork 0x40241140240a41140a40241040240741040740240240640640200000040640240240240240540205240540f40040040f40040f40f40004a402 []),(.fork 0x4405240440240108a04a04a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x1 : Block 87 8 (successors 87 8 s01) 10 10 := offMemoRows (code:=0x40040040f400400400400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x2 : Block 87 8 (successors 87 8 s01) 20 10 := offMemoRows (code:=0x140f400400400400400400400001) (gs:=[(.fork 0x40e40e40e40e40e40e09240e40e40e40e40840c40840840840801200040c00041241202301205205240040040c00040440f40440f40f40140240140240140140f40140f40f400400 []),(.fork 0x40b40940b40b40b40b40d40d40d40d40d40d09240d40d40d40d01200040900041341302301209209240f40f40900040340040340040040140240140240140140040140040040f40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x3 : Block 87 8 (successors 87 8 s01) 30 10 := offMemoRows (code:=0x140500100140240540f40f40f40f) (gs:=[(.fork 0x41740a41740a416407416407000406032406415415414414402402401000022401 []),(.fork 0x415418414405402402 []),(.fork 0x41540240504a02a000 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x4 : Block 87 8 (successors 87 8 s01) 40 10 := offMemoRows (code:=0x140f400400400400001400402001) (gs:=[(.fork 0x40240a41140a40240741040741941940240600440640040f40040f40f40040f400000022402402402402402000401402052401 []),(.fork 0x40e40e40e40e40e40e41641a41641600003241a00040040041a01240240540240540540040005205240f41540f41540f40f40540f40540f []),(.fork 0x41741841741740d40d40d40d40d40d00005241800040f40f41440041440040040540040540040041801240240540240540540f40f092092 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x5 : Block 87 8 (successors 87 8 s01) 50 10 := offMemoRows (code:=0x40240600100100108b40f40f40f40f) (gs:=[(.fork 0x4a41c01240f09241b012400052401022025402022402022405047 []),(.fork 0x41500040504740e08a40d08a40f092400052402405052405 []),(.fork 0x2440f092404024400052401000401402052401048 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x6 : Block 87 8 (successors 87 8 s01) 60 10 := offMemoRows (code:=0x40040040040040200141c406001001) (gs:=[(.fork 0x41d41f41d40a41d40a42242141c42242240742240742105241f03203200000040503200040540542100042042041f00041e41e05241c41c41d41c032402402401006052401 []),(.fork 0x2600042041f41e406402402 []),(.fork 0x41140240240a41140a41040240240741040740200040200040240500040540201240040640040640201240f40040f40040240240240240241c401402000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x7 : Block 87 8 (successors 87 8 s01) 70 10 := offMemoRows (code:=0x40e40e00141c00141c40f40f40f40f) (gs:=[(.fork 0x42440603241c402423032423 []),(.fork 0x41541c40f052400032402405000405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x8 : Block 87 8 (successors 87 8 s01) 80 10 := offMemoRows (code:=0x40d40d40d40700141c00141c40e40e) (gs:=[(.fork 0x42642540205240241c []),(.fork 0x40f09240440005240140205240140605241c [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x9 : Block 87 8 (successors 87 8 s01) 90 10 := offMemoRows (code:=0x40040040040040d40040d40d40d407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x10 : Block 87 8 (successors 87 8 s01) 100 10 := offMemoRows (code:=0x40d40d40d40d40f40f40d40f40f40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x11 : Block 87 8 (successors 87 8 s01) 110 10 := offMemoRows (code:=0x40d40d40e40e40e40e40d40d40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x12 : Block 87 8 (successors 87 8 s01) 120 10 := offMemoRows (code:=0x40e40e40e40a40e40e40e40a40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x13 : Block 87 8 (successors 87 8 s01) 130 10 := offMemoRows (code:=0x40f40f40e40f40040040e400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b1x14 : Block 87 8 (successors 87 8 s01) 140 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40f40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc1 : Excluded 87 9 s01 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b1x0
  · exact b1x1
  · exact b1x2
  · exact b1x3
  · exact b1x4
  · exact b1x5
  · exact b1x6
  · exact b1x7
  · exact b1x8
  · exact b1x9
  · exact b1x10
  · exact b1x11
  · exact b1x12
  · exact b1x13
  · exact b1x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc2 : Excluded 87 9 s02 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc4 : Excluded 87 9 s04 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x0 : Block 87 8 (successors 87 8 s05) 0 10 := offMemoRows (code:=0x401400400400400400400400401400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x1 : Block 87 8 (successors 87 8 s05) 10 10 := offMemoRows (code:=0x400400400400400400400001400400) (gs:=[(.fork 0x40e40e08a40e40e40e40e40e40e40e40e40840840840c40840800600002300a04a04a40c00041241240040040c00040440f40440f40f40040040140240140240140140f40140f40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x2 : Block 87 8 (successors 87 8 s05) 20 10 := offMemoRows (code:=0x400400404001001405001001404405) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00404a00000040604a00340640641541541b04400741b41241b404404 []),(.fork 0x2242700740e04642841541b005405404404 []),(.fork 0x2e42a41540440540e0c242904a04a022012 []),(.fork 0x40440f00040f40440a40440a404407000407404047404406000406404044401404400404401401400404404404412022404404404012405400400405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x3 : Block 87 8 (successors 87 8 s05) 30 10 := offMemoRows (code:=0x401001001001001401400400001400) (gs:=[(.fork 0x40e40e00a40e40e40e40e40e40e40e40e412082412082400400412412404412022412404412022401412401412401401412401412401400400 []),(.fork 0x2241b42702242742742742742741b02200004241b04408204204205204204341b00440140100740041b40040041241b404405404405405401401400405400405400 []),(.fork 0x2242b04a42840140100540040440540140140040541b400 []),(.fork 0x3642a40140440540140e0c2429052400022400405012400042 []),(.fork 0x40400040140140440442c42c401404404026404048404000404026401401401400400401400412404405405401042415401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x4 : Block 87 8 (successors 87 8 s05) 40 10 := offMemoRows (code:=0x42840600100140440640c00100140c) (gs:=[(.fork 0x4442d41800000540040c404414022414 []),(.fork 0x4c42a41540c40108241240040440508a405 []),(.fork 0x40f04440f00642e00040a42e42e40a40a42804a00040704a40700004200040504a40542042042542542842e404404404404 []),(.fork 0x642e00740e420426425406404404 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x5 : Block 87 8 (successors 87 8 s05) 50 10 := offMemoRows (code:=0x1401400400400400001400404001) (gs:=[(.fork 0x40440f08a40f40440a40440a40440700040740408240440504a40540040640040640140040140042804404c428404404404404404428 []),(.fork 0x40e40e00a40e40e40e40e40e40e42800004704204b04a04700a41241240040040e40e428001404404404406404406406400400006000401420401420401401406401406406 [(.fork 0x42f022412423400 [])]),(.fork 0x44430401425400406400426400404406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x6 : Block 87 8 (successors 87 8 s05) 60 10 := offMemoRows (code:=0x40e40e40e40e001428001428401428) (gs:=[(.fork 0x1443142405200142800740040442304a423 [(.fork 0x42f022412423400 [])]),(.fork 0x1842a41504204e40642840105241240040440504a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x7 : Block 87 8 (successors 87 8 s05) 70 10 := offMemoRows (code:=0x42940700100140440740c428001428) (gs:=[(.fork 0x4443241f40000004640642840441e04641e []),(.fork 0x40840f40840f04243300040a43343340a40a00040604a406000405022405436436435408434434429433404404 []),(.fork 0x4243300740e436435434407404404 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x8 : Block 87 8 (successors 87 8 s05) 80 10 := offMemoRows (code:=0x1401400400400400001400404001) (gs:=[(.fork 0x40440f40840f40440a40440a404406000406404405022405400407400407404408401400401400408429429016404404404404404429 []),(.fork 0x40840840e40e08240e40e40e00004202302241241240040040e40e429042404407404407407400400408408401436401436401401407401407407 []),(.fork 0x44437401434400404407401400407435400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x9 : Block 87 8 (successors 87 8 s05) 90 10 := offMemoRows (code:=0x428429001428001429001429401429) (gs:=[(.fork 0x8443a43904204201340742908a40c007400404438022438 []),(.fork 0x5a42a41500042940105241240040440504a405 []),(.fork 0x2443d43c00040604a42805240140004240443b04a43b [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x10 : Block 87 8 (successors 87 8 s05) 100 10 := offMemoRows (code:=0x40a40a40c42940842940e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x11 : Block 87 8 (successors 87 8 s05) 110 10 := offMemoRows (code:=0x40e00140e00140e40a40e40e40e40e) (gs:=[(.fork 0x42c43e08342c42c43e08442c43e44044144043f44002343f05644008344042c44004342c40e40e40e40e42c44008442c43e43f04343f01543f01343f42c43f04342c40e40e40e40e42c43f00442c43e04704343e42c03402242c40e40e40e40e42c02c02242c40e40e40e40e40e40e40e40e40e40e40e40e40e40e40e40e []),(.fork 0x42c43e08442c40e08242c44004242c40e00442c43f00442c42c02200440e42c02c02242c40e40e40e40e40e08442c40e40e40e40e42c40e42c40e40e40e40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x12 : Block 87 8 (successors 87 8 s05) 120 10 := offMemoRows (code:=0x40e40e40e40e40040040040040e400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x13 : Block 87 8 (successors 87 8 s05) 130 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x14 : Block 87 8 (successors 87 8 s05) 140 10 := offMemoRows (code:=0x140140400140c40f00100140440f) (gs:=[(.fork 0x40c40b08640b00040a40b40b40a40a40940808a408000407408408407407000406046406000022000405022405402402403403404404 []),(.fork 0x8640b00740e08642940240940340f404404 []),(.fork 0x40440a40440a40440840440740840740440600040640400040440500040540440440440440f40040040f40040140140040c404 []),(.fork 0x8444208a42940100040340040f40040940040440f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b5x15 : Block 87 8 (successors 87 8 s05) 150 10 := offMemoRows (code:=0x40140c) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc5 : Excluded 87 9 s05 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=16) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b5x0
  · exact b5x1
  · exact b5x2
  · exact b5x3
  · exact b5x4
  · exact b5x5
  · exact b5x6
  · exact b5x7
  · exact b5x8
  · exact b5x9
  · exact b5x10
  · exact b5x11
  · exact b5x12
  · exact b5x13
  · exact b5x14
  · exact b5x15
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc6 : Excluded 87 9 s06 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x0 : Block 87 8 (successors 87 8 s07) 0 10 := offMemoRows (code:=0x40100140140f400400400400400401) (gs:=[(.fork 0x40344440340a44440a40340340340740340740300440340600040640100002440340340504640540140140344340340044340040140140140140040f40f400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x1 : Block 87 8 (successors 87 8 s07) 10 10 := offMemoRows (code:=0x40040040040140040040140f401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x2 : Block 87 8 (successors 87 8 s07) 20 10 := offMemoRows (code:=0x401001401405400400400400400400) (gs:=[(.fork 0x42742742740a42740a00008400040708440700000400040600040640340340140141b41b40140140f02704440f40040540540040041b41b400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x3 : Block 87 8 (successors 87 8 s07) 30 10 := offMemoRows (code:=0x1401400400400400401401401405) (gs:=[(.fork 0x42742742742700000040100000000000000040040040100041b401415401405405401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x4 : Block 87 8 (successors 87 8 s07) 40 10 := offMemoRows (code:=0x40140640300c001403401401401401) (gs:=[(.fork 0x418414401046401403 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x5 : Block 87 8 (successors 87 8 s07) 50 10 := offMemoRows (code:=0x400400400400401401401406401001) (gs:=[(.fork 0x42540a43040a42543c42540743c40740100042540500040540140142543040140142542640140140f42500040f400406406400400425426400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x6 : Block 87 8 (successors 87 8 s07) 60 10 := offMemoRows (code:=0x40e40e00e425001425401401401401) (gs:=[(.fork 0x424000405006425401423000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x7 : Block 87 8 (successors 87 8 s07) 70 10 := offMemoRows (code:=0x40100140140740342500142540e40e) (gs:=[(.fork 0x41f40f00641e401000401425 []),(.fork 0x43440a43340a43440643c40643440508640540140143443343443c40140143443540140140f43440340f400407407400400434435400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x8 : Block 87 8 (successors 87 8 s07) 80 10 := offMemoRows (code:=0x401401400400400400401401401407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x9 : Block 87 8 (successors 87 8 s07) 90 10 := offMemoRows (code:=0x42543443c42500e434001434401401) (gs:=[(.fork 0x439000405086445407434064403401438084401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x10 : Block 87 8 (successors 87 8 s07) 100 10 := offMemoRows (code:=0x40e40a40343440343440e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x11 : Block 87 8 (successors 87 8 s07) 110 10 := offMemoRows (code:=0x40040040040040e40e40e40a40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x12 : Block 87 8 (successors 87 8 s07) 120 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b7x13 : Block 87 8 (successors 87 8 s07) 130 10 := offMemoRows (code:=0x40140140140140e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc7 : Excluded 87 9 s07 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b7x0
  · exact b7x1
  · exact b7x2
  · exact b7x3
  · exact b7x4
  · exact b7x5
  · exact b7x6
  · exact b7x7
  · exact b7x8
  · exact b7x9
  · exact b7x10
  · exact b7x11
  · exact b7x12
  · exact b7x13
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc8 : Excluded 87 9 s08 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x0 : Block 87 8 (successors 87 8 s09) 0 10 := offMemoRows (code:=0x41540141a40f41500100100141540f) (gs:=[(.fork 0x41740a41740a416407416407000406026406414414402402415415401000022401 []),(.fork 0x41441840241541540f []),(.fork 0x41540a42a40a41641a41540741640741540642440641541541541540040f40040f41a00e40141502240140040540540041a415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x1 : Block 87 8 (successors 87 8 s09) 10 10 := offMemoRows (code:=0x400400400400143401415001001001) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00405200000040605200340640641b04400b41b41241b404404415415 []),(.fork 0x2440e04442441200b41b404415415401 []),(.fork 0x41542a41540700040741542441504441541541541541541540f41500040f40a41542a40a406415424406400405405400405400400405012415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x2 : Block 87 8 (successors 87 8 s09) 20 10 := offMemoRows (code:=0x405001405400400400405400400400) (gs:=[(.fork 0x1241440041540f40f400418400405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x3 : Block 87 8 (successors 87 8 s09) 30 10 := offMemoRows (code:=0x140040040540000140500140541a) (gs:=[(.fork 0x4a42400540041540140140041b400405405 []),(.fork 0x41a0924000a2415401401400012400405405 []),(.fork 0x40e40e40e40e40e40e41641641641a00002640040041a01240240540240540504a04a40f41540f41540f40f40540f40540f41a000400400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x4 : Block 87 8 (successors 87 8 s09) 40 10 := offMemoRows (code:=0x415406400400400400400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x5 : Block 87 8 (successors 87 8 s09) 50 10 := offMemoRows (code:=0x405424424405415001424406424001) (gs:=[(.fork 0x42440a42f40a42440704440742342342042041541540142405240140f42402440f []),(.fork 0x41540a42a40a42404441540704b40740540040540040040640040605442442442a41541541541541542440141505240140f41500040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x6 : Block 87 8 (successors 87 8 s09) 60 10 := offMemoRows (code:=0x40e40e40e40e400400400400001400) (gs:=[(.fork 0x40e40e40e40e42404440040042040542040540542400a0a242440e40e424424415406415406406400400424024405406405406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x7 : Block 87 8 (successors 87 8 s09) 70 10 := offMemoRows (code:=0x41540700142400142441a424001424) (gs:=[(.fork 0x40002644641e415026415424 []),(.fork 0x426425415052415424 []),(.fork 0x4044014150524010a2056406424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x8 : Block 87 8 (successors 87 8 s09) 80 10 := offMemoRows (code:=0x405448001405415001448407001001) (gs:=[(.fork 0x44740a44740a00040604640643941643843843643644844741541540100002240140f41602200041640f41640f []),(.fork 0x43843943640741541502641a []),(.fork 0x41540a42a40a41540642440641541640540040540040040740040741541541541541544840141500040140f41541640f []),(.fork 0x40541540740502a41a438400400407439400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x9 : Block 87 8 (successors 87 8 s09) 90 10 := offMemoRows (code:=0x40e40e424448001424400400400400) (gs:=[(.fork 0x44904604640642441543b044415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x10 : Block 87 8 (successors 87 8 s09) 100 10 := offMemoRows (code:=0x144800144841a44841644840e40e) (gs:=[(.fork 0x435434415022415448 []),(.fork 0x404401415052401448 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x11 : Block 87 8 (successors 87 8 s09) 110 10 := offMemoRows (code:=0x40e40540e40e40e40a40e40e40e40a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x12 : Block 87 8 (successors 87 8 s09) 120 10 := offMemoRows (code:=0x40e40e40040040040040540e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b9x13 : Block 87 8 (successors 87 8 s09) 130 10 := offMemoRows (code:=0x141a00141a40e40e40e40e40e40e) (gs:=[(.fork 0x4a44800040900b40f40341502241541a []),(.fork 0x40441a415401092401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc9 : Excluded 87 9 s09 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b9x0
  · exact b9x1
  · exact b9x2
  · exact b9x3
  · exact b9x4
  · exact b9x5
  · exact b9x6
  · exact b9x7
  · exact b9x8
  · exact b9x9
  · exact b9x10
  · exact b9x11
  · exact b9x12
  · exact b9x13
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x0 : Block 87 8 (successors 87 8 s10) 0 10 := offMemoRows (code:=0x40500140540f400400405400400400) (gs:=[(.fork 0x41741841440a41740a41440743840741444641440644640641802241441841440041840040540540540540f40040f400405405401414046401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x1 : Block 87 8 (successors 87 8 s10) 10 10 := offMemoRows (code:=0x40540540500140540540540f405405) (gs:=[(.fork 0x4200040f04440f40542742740a42740a0004070844070a20040a200000040600400340640641b41b41b40041b400405405405400405400405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x2 : Block 87 8 (successors 87 8 s10) 20 10 := offMemoRows (code:=0x400400400400400405400400405401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x3 : Block 87 8 (successors 87 8 s10) 30 10 := offMemoRows (code:=0x400400405405405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x4 : Block 87 8 (successors 87 8 s10) 40 10 := offMemoRows (code:=0x405406400400400400001400400400) (gs:=[(.fork 0x40e40e40e40e40e40e01240e40e40e40e412082412082412412404412022412404412022400400401412401412401401412401412401400400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x5 : Block 87 8 (successors 87 8 s10) 50 10 := offMemoRows (code:=0x405405405405405405405406405001) (gs:=[(.fork 0x42f42442340a42f40a42340704440742408240540540640040640042344642342440540540540540142300640140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x6 : Block 87 8 (successors 87 8 s10) 60 10 := offMemoRows (code:=0x44642340e40e40e40e400400400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x7 : Block 87 8 (successors 87 8 s10) 70 10 := offMemoRows (code:=0x405001405407001423001423414423) (gs:=[(.fork 0x426401006425405004405423 []),(.fork 0x4000124044010a240140500440544a406423 []),(.fork 0x43840a44740a43840604640643908240740040740000443843843843844743800443843940540540540540143808640140f43844b02a43840f44b40f400438439400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x8 : Block 87 8 (successors 87 8 s10) 80 10 := offMemoRows (code:=0x400400405405405405405405405407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x9 : Block 87 8 (successors 87 8 s10) 90 10 := offMemoRows (code:=0x40e40e40e40e423438001423400400) (gs:=[(.fork 0x44943840640700642340543b044405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x10 : Block 87 8 (successors 87 8 s10) 100 10 := offMemoRows (code:=0x40540a001438001438414438438414) (gs:=[(.fork 0x435434405084405438 []),(.fork 0x400012404401405022405407006438 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x11 : Block 87 8 (successors 87 8 s10) 110 10 := offMemoRows (code:=0x40540540e40540540540540a40540e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x12 : Block 87 8 (successors 87 8 s10) 120 10 := offMemoRows (code:=0x40e40e40040040e400400400405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b10x13 : Block 87 8 (successors 87 8 s10) 130 10 := offMemoRows (code:=0x1341400141440e40e40e40e40e40e) (gs:=[(.fork 0x5443840940104241340f403405044405414 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc10 : Excluded 87 9 s10 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b10x0
  · exact b10x1
  · exact b10x2
  · exact b10x3
  · exact b10x4
  · exact b10x5
  · exact b10x6
  · exact b10x7
  · exact b10x8
  · exact b10x9
  · exact b10x10
  · exact b10x11
  · exact b10x12
  · exact b10x13
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc11 : Excluded 87 9 s11 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x0 : Block 87 8 (successors 87 8 s16) 0 10 := offMemoRows (code:=0x405001405400405401405405405405) (gs:=[(.fork 0x41542a41540a42a40a41504741540700040741542441540642440640540540540540040540040541504740140140540540f41500040f401400400401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x1 : Block 87 8 (successors 87 8 s16) 10 10 := offMemoRows (code:=0x40540540500140540f405400405405) (gs:=[(.fork 0x41402741440a00040a41443841440743840741444641440644640641404741440000040040540540540540f40540f40540140140540540140f40f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x2 : Block 87 8 (successors 87 8 s16) 20 10 := offMemoRows (code:=0x40540540540540540140500140540f) (gs:=[(.fork 0x2b41404c41441445703341441545742a41540540540540501c45701c45741443443841445743403343442343443c42341543403341540540540540502b43408c43441442344642345742343042341542342441540540540540502b40500c02e42300c42300741441505341501b41504c415405405405405405405405405405001405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 []),(.fork 0x41403441400045701c45700043405443402a00000042302c02b42300f02b02b00041502c415405405 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x3 : Block 87 8 (successors 87 8 s16) 30 10 := offMemoRows (code:=0x401401405405405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x4 : Block 87 8 (successors 87 8 s16) 40 10 := offMemoRows (code:=0x40500140540641441508b415401401) (gs:=[(.fork 0x42340a43040a42343c42340743c40740540540140502c40640540640542344642343042342440140140540540540540f42344640f400423424400401406406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x5 : Block 87 8 (successors 87 8 s16) 50 10 := offMemoRows (code:=0x401401405405405405405405405406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x6 : Block 87 8 (successors 87 8 s16) 60 10 := offMemoRows (code:=0x457423430423415423424415401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x7 : Block 87 8 (successors 87 8 s16) 70 10 := offMemoRows (code:=0x405407405001405407414423446423) (gs:=[(.fork 0x43440a00040a43440643c40640540140740540740543443843402743443c43404740140140540540540540f43443840f400434000400401407407401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x8 : Block 87 8 (successors 87 8 s16) 80 10 := offMemoRows (code:=0x401401401401405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x9 : Block 87 8 (successors 87 8 s16) 90 10 := offMemoRows (code:=0x4b43442343443c42341543408b415) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x10 : Block 87 8 (successors 87 8 s16) 100 10 := offMemoRows (code:=0x40500140540a414434438414457434) (gs:=[(.fork 0x45702745740700040745743045740643040640540140a40540a40545702745742a40140140540540540540f45700040f40045742a40040140a40a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x11 : Block 87 8 (successors 87 8 s16) 110 10 := offMemoRows (code:=0x40140140540540540540540540540a) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x12 : Block 87 8 (successors 87 8 s16) 120 10 := offMemoRows (code:=0x41445704b41441545742a415401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b16x13 : Block 87 8 (successors 87 8 s16) 130 10 := offMemoRows (code:=0x401401401401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc16 : Excluded 87 9 s16 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b16x0
  · exact b16x1
  · exact b16x2
  · exact b16x3
  · exact b16x4
  · exact b16x5
  · exact b16x6
  · exact b16x7
  · exact b16x8
  · exact b16x9
  · exact b16x10
  · exact b16x11
  · exact b16x12
  · exact b16x13
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x0 : Block 87 8 (successors 87 8 s17) 0 10 := offMemoRows (code:=0x401405405405401405001401401401) (gs:=[(.fork 0x2b41404c41441445702b41441545742a41501c45701c45740540540540541443443841445743402b43442343443c42341543402b41502b43408c43440540540540541442344642345742343042341542342441500c02e42300c42300740540540540502b40541441504b41501b41504c415405405405405405405405405405001405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 []),(.fork 0x41403441400045701c45700043405443402a00000042302c02b42300f02b02b00041502c415405405 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x1 : Block 87 8 (successors 87 8 s17) 10 10 := offMemoRows (code:=0x40544c40500140541b405001405401) (gs:=[(.fork 0x4442400740040540541540140140041b400 []),(.fork 0x4444600740f40540541440140140f44c40f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x2 : Block 87 8 (successors 87 8 s17) 20 10 := offMemoRows (code:=0x100141b40000100141b400405405) (gs:=[(.fork 0x40f02240f42742702242700040a42742740a40a00040702240741b00404600000040604600340640641541541241b40440441b04400741b []),(.fork 0x2242b04600304445a41504740440000741b []),(.fork 0x42742742741b42740a42740a00040708440700040600040641b00840140040140041b00e40f02b00040f40040540540041b008 []),(.fork 0x1500c41b008405401400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x3 : Block 87 8 (successors 87 8 s17) 30 10 := offMemoRows (code:=0x44c41b00141b40100141b001001401) (gs:=[(.fork 0x2242742742742741b42702242700004241b02204204a04204341b04408204240140141241b40440540440540540040540040540041b00400b40041b400400401401 []),(.fork 0x2242b04442840140140440540040541b40000b400401401 []),(.fork 0x42742742742700000000000000000040100040140140540540040040100041540141b401 []),(.fork 0x4441c04502240500640f08600640004641b40102202b402022402 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x4 : Block 87 8 (successors 87 8 s17) 40 10 := offMemoRows (code:=0x100145a40600100145a001406406) (gs:=[(.fork 0x4600041e00641e00002600045100645100008600043b00643b00004600042000642042342342542342542300542542545a45a45a45a45a45a45a45a45a45a45a45a05245a000 []),(.fork 0x40f04440f00040a02440a00040708440700040004440042342342542505245a000 []),(.fork 0x42300742540605245a052 []),(.fork 0x45b45d04345b04445d04445d45d45f04345f45c45f46145c45b45f02345b44a45f02344a02445f02445f45d45e46045e45f45e04345e45c45e04345c45b45e08345b44a45e08344a08445e08445e45d45c04345c45b45c04345b04445c04445c44a45a05245b45d44a04344a45c44a04344a45b44a05244a45b45a05244a []),(.fork 0x40f04440f00040a02440a45a45e08445a00040708440700040004440040540640540640140640140645d45a04445a45f45a02445a45c45a04445a45b45a05245a44a45a05245a05245a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x5 : Block 87 8 (successors 87 8 s17) 50 10 := offMemoRows (code:=0x140140500145a001001405001001) (gs:=[(.fork 0x4200045d04445d00002200045f02445f00008200045e08445e00004200045c04445c44a44a44a05245b44a45b44a02b45b45b45b05245a45a406 []),(.fork 0x40540100740140505205205205245a05245a406 []),(.fork 0x4400002200008200004440540545a04445a04445a45a05240645a406406405405401423401423401401406401406406 []),(.fork 0x40540505240640540542340140140645a406 []),(.fork 0x4240502245a08440508200004240540545a02445b45a02a45a45a05240645a40640640545a401405405405405425405 []),(.fork 0x4200002400008445a08400004240140142540542540540540640540640540645a02445a45a05240645a406406401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x6 : Block 87 8 (successors 87 8 s17) 60 10 := offMemoRows (code:=0x145a41b45a00141b40100145a001) (gs:=[(.fork 0x40140142540540640545a406052406401401 []),(.fork 0x40104200002200008240104240140140140540140540545a04445a04444a45a02a45a45a05240645a40640640145a423401 []),(.fork 0x42404640000604604604640641b401042000420046420 []),(.fork 0x43002640a00602602602640645a405022000451026451 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x7 : Block 87 8 (successors 87 8 s17) 70 10 := offMemoRows (code:=0x100146240744c45a00145a42b45a) (gs:=[(.fork 0x44604640f00604604604640645a40104200041e04641e []),(.fork 0x44d44d04244d00040f44d44d40f40f00040a04240a08600000040608600340640600040002240043843843443446202446200444546200b462 []),(.fork 0x4244c08600308445a43808743440700b462 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x8 : Block 87 8 (successors 87 8 s17) 80 10 := offMemoRows (code:=0x405001462001001405001001462407) (gs:=[(.fork 0x44d44d44d40f44d40f05340a00040a00040600040600040004440040540740540740140740140744d46246200846200e00c462 []),(.fork 0x2540140500c46200c407 []),(.fork 0x44d44d44d44d00004208208a08208304208200004240540546244d46200446208446202244546200b40746240740740540504244d401438401438401401407401407407 []),(.fork 0x8446340540500b40740540504244c438401401407462407 []),(.fork 0x44d44d44d44d405000000000000000405000000000405405407407405462401405434405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x9 : Block 87 8 (successors 87 8 s17) 90 10 := offMemoRows (code:=0x145a41b46200141b401462001401) (gs:=[(.fork 0x8443c401434405407405462407007407401 []),(.fork 0x4446402502202241b000436022436 []),(.fork 0x43c08608608640608640700645a40508200043b08443b [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x10 : Block 87 8 (successors 87 8 s17) 100 10 := offMemoRows (code:=0x44c46244d46242b46200146245a462) (gs:=[(.fork 0x4446602500640a086006407026462042401405042053465042465 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x11 : Block 87 8 (successors 87 8 s17) 110 10 := offMemoRows (code:=0x140500100142b40a00100142b40a) (gs:=[(.fork 0x40f04240f42b08400040704240742b00402600000040602600340640642742702242700040042742740040042a42a45745746742b00b42b []),(.fork 0x2600302445a02241b42a01745740a00b42b []),(.fork 0x40f08440f05340700040700040600040642742742740042740040540a40540a40140a40140a42742b42b00842b00e00c42b []),(.fork 0x1740140500c42b00c40a []),(.fork 0x2242b00400004202202a02202342b02404202242742742742740540542b04242b42746742b00b40a42b40a40a40540502242740142a40142a40140140a40140a40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x12 : Block 87 8 (successors 87 8 s17) 120 10 := offMemoRows (code:=0x42741b40142b00140140500142b001) (gs:=[(.fork 0x2446840540500b40a40540502241b42a40140140a42b40a []),(.fork 0x40500000000000000040500042742742742740540540a40a40542b401405457405 []),(.fork 0x2443040145740540a40542b40a00740a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x13 : Block 87 8 (successors 87 8 s17) 130 10 := offMemoRows (code:=0x100144c40f44c42b00142b41b42b) (gs:=[(.fork 0x4446902504204242b000454042454 []),(.fork 0x40a04240a44d44d04244d00040744d44d40740744c00404600000040604600340640644c08400040002240041441441344c40340300744c []),(.fork 0x4246204600304445a41404740340f00744c [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b17x14 : Block 87 8 (successors 87 8 s17) 140 10 := offMemoRows (code:=0x40100144c00100140100100144c40f) (gs:=[(.fork 0x40a02440a44d44d44d44c44d40744d40700040600040644c00840140f40140f44c00e40002b00040040f40540540f44c008 []),(.fork 0x2500c44c00840540140f []),(.fork 0x2244c04244d44d44d44d44c44d04244d04204a04204344c04402204244c00400002240140141344c40340540340540540f40540f40540f00b40f44c40f40f401401 []),(.fork 0x4246204446a40140140340540f40544c40f00b40f401401 []),(.fork 0x44d44d44d44d00000000000040100040140140540540f40f40100041440144c401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc17 : Excluded 87 9 s17 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b17x0
  · exact b17x1
  · exact b17x2
  · exact b17x3
  · exact b17x4
  · exact b17x5
  · exact b17x6
  · exact b17x7
  · exact b17x8
  · exact b17x9
  · exact b17x10
  · exact b17x11
  · exact b17x12
  · exact b17x13
  · exact b17x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x0 : Block 87 8 (successors 87 8 s18) 0 10 := offMemoRows (code:=0x405001405400405001405405405405) (gs:=[(.fork 0x40104200040f02240f40501200040a02240a405082000407022407405052401052052000000406052003406406401042000400012400401405405405405401405405405 []),(.fork 0x40542a41540a42a40a41540700040741542441540642440640540540540540040540040541504441502240540540f41504440f400415012400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x1 : Block 87 8 (successors 87 8 s18) 10 10 := offMemoRows (code:=0x405405405001405406405400405405) (gs:=[(.fork 0x42340700040740540542344642342442305240540540540540f42344640f40a42300040a400423424400406423052406405406406405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x2 : Block 87 8 (successors 87 8 s18) 20 10 := offMemoRows (code:=0x405405405001405001405407405406) (gs:=[(.fork 0x46b4140a241441442a04341441542a42a41546b42a02442a40540540540541442344642342a42304342341542342441546b42300442340540540540541441508341546b41504441540540540540540540540540540540540540541443843841442a43802642a42343808342341543804641546b438022438405405405405 []),(.fork 0x41443843841442a43802442a42343808742341543804441546b43805243840540540540540540540f43843840f40a43802440a406438000406400438000400407438022407405407407405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x3 : Block 87 8 (successors 87 8 s18) 30 10 := offMemoRows (code:=0x40500140500140540a405407405407) (gs:=[(.fork 0x46c41408441441443843841442343808342341543808341546c43808443840540540540542a43808442a41442344642341542342441546c42300442340540540540542a42302342341441508341546c4150c241540540540540540540540540540540540540541442a08641441542a42a41546c42a02242a405405405405 []),(.fork 0x42a43808442a42a40702640742a42302742342a40600040641442a08441441542a42a41546c42a0c242a40540540540540540540f42a00040f40042a42a40040a42a02240a40540a40a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x4 : Block 87 8 (successors 87 8 s18) 40 10 := offMemoRows (code:=0x40500140540f40540a40540a405405) (gs:=[(.fork 0x41440a00040a40543841440743840741444641440644640641408441440004640040540540540540f40540f40541404240540540f41402240f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x5 : Block 87 8 (successors 87 8 s18) 50 10 := offMemoRows (code:=0x40500140540540540540540f405405) (gs:=[(.fork 0x40140140140140140141445702b41441545742a41540140140140141443443841445743403343442343443c42341543402b41540140140140141442344642345742343042341542342441540140140140141441504b415401401401401401401405405405405405405405405405405405405405405405405405405405405405405405405405401405001 [(.fork 0x1541403341441445703341441545742a41500d45701b45741443443841445743403343442343443c42341543403341501543405343441442344642345742343042341542342441500d42302b42341441503341500d41502b415 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x6 : Block 87 8 (successors 87 8 s18) 60 10 := offMemoRows (code:=0x405405405405405405405405405401) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x7 : Block 87 8 (successors 87 8 s18) 70 10 := offMemoRows (code:=0x1405414415001415401415001401) (gs:=[(.fork 0x3442a40140440540e0c2429046042400022400405012400401 []),(.fork 0x4500040540e08440d08440f086400046402405046405415 []),(.fork 0x423000423000405405405405052405406406423405423446423424405405401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x8 : Block 87 8 (successors 87 8 s18) 80 10 := offMemoRows (code:=0x424415401423001401405405405405) (gs:=[(.fork 0x40142540543000643c006052406052406405052406401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x9 : Block 87 8 (successors 87 8 s18) 90 10 := offMemoRows (code:=0x41442344642342a42304b423415423) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x10 : Block 87 8 (successors 87 8 s18) 100 10 := offMemoRows (code:=0x401438001401405405405405001405) (gs:=[(.fork 0x43800043800040543840540508240540740540740540743440543843843804a43808c43802a44543840540544b44b401401 []),(.fork 0x401434405437086407052407405022407401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x11 : Block 87 8 (successors 87 8 s18) 110 10 := offMemoRows (code:=0x142a42343810b423415438001415) (gs:=[(.fork 0x2540e08440704643640500040502a415 []),(.fork 0x3440a08640702646540502640504a04a42a405000 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x12 : Block 87 8 (successors 87 8 s18) 120 10 := offMemoRows (code:=0x40540500140541443843841442a438) (gs:=[(.fork 0x42a04a42a00042a02c42a00040540540542a01240540a40540a40540a45740542a04a42a42a46742a405405459459401401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x13 : Block 87 8 (successors 87 8 s18) 130 10 := offMemoRows (code:=0x41542a42a41540142a001401405405) (gs:=[(.fork 0x40145740546d02640a0c240a40502240a401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b18x14 : Block 87 8 (successors 87 8 s18) 140 10 := offMemoRows (code:=0x40141400140141442a001414) (gs:=[(.fork 0x2540d04440a08645440500040504a414 []),(.fork 0x5443840140340544208640d0a204240f04240f40502240f401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc18 : Excluded 87 9 s18 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b18x0
  · exact b18x1
  · exact b18x2
  · exact b18x3
  · exact b18x4
  · exact b18x5
  · exact b18x6
  · exact b18x7
  · exact b18x8
  · exact b18x9
  · exact b18x10
  · exact b18x11
  · exact b18x12
  · exact b18x13
  · exact b18x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc20 : Excluded 87 9 s20 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x0 : Block 87 8 (successors 87 8 s21) 0 10 := offMemoRows (code:=0x42040142140f42000100100142040f) (gs:=[(.fork 0x41d41f41d40a41d40a41c42242242142240742240741f02a42105202600000040502600040540541f00041e41e04a41c41c41d41c02a40240242100042042040100a046401 []),(.fork 0x4442441e41f40242042040f []),(.fork 0x46f42042040a46f40a42042242040742240742042442001242042000042042046f42042442042040040640040640142000a401405420424405400406406400421420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x1 : Block 87 8 (successors 87 8 s21) 10 10 := offMemoRows (code:=0x400400400400001401420001001001) (gs:=[(.fork 0x40f04440f00a42e00040a42e42e40a40a42805200040705240700004200040505240542542542842e404404404404420420 []),(.fork 0x2440e425426404420420401 []),(.fork 0x42005242040700040742042042046f40442002642042040042040642040040040640f42000040f40a42046f40a40542042440540040640640004a420 []),(.fork 0x42504a42040100a04a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x2 : Block 87 8 (successors 87 8 s21) 20 10 := offMemoRows (code:=0x406001406400400400406400400400) (gs:=[(.fork 0x42f42442442f424044424001406406424024424052424424420405420405405406406404424400423400423400400405400405400 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x3 : Block 87 8 (successors 87 8 s21) 30 10 := offMemoRows (code:=0x40640640640640640e406406406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x4 : Block 87 8 (successors 87 8 s21) 40 10 := offMemoRows (code:=0x400406001406406406406406406406) (gs:=[(.fork 0x4044044044044040004040a244a44a404052404052406406404404404400400404400000044404420026404420404400400404400406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x5 : Block 87 8 (successors 87 8 s21) 50 10 := offMemoRows (code:=0x400400001400400400400400400406) (gs:=[(.fork 0x40e40e40e40e01240e40e40e40e42800005304241241205305204b01240e40e428001400400404404404406404406406012000401420401420401401406401406406400400 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x6 : Block 87 8 (successors 87 8 s21) 60 10 := offMemoRows (code:=0x420001424405424001420405400400) (gs:=[(.fork 0x42440a47040a42440704440742342341541542042040142405240140f42402440f []),(.fork 0x42040a46f40a42404442040700040740640040640042042040040640040647142442042042042440142005240140f42002440f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x7 : Block 87 8 (successors 87 8 s21) 70 10 := offMemoRows (code:=0x421424001424400400400400001400) (gs:=[(.fork 0x40e40e40e40e4240440a242440e40e400400424424415406415406406424024405406405406406420405420405405400400424012 []),(.fork 0x44640f052414420026420424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x8 : Block 87 8 (successors 87 8 s21) 80 10 := offMemoRows (code:=0x47240700100142040708b424001424) (gs:=[(.fork 0x5240001241b052052052406401042000420052420424 []),(.fork 0x47340a47340a00040504640544904243b43b43643647204242042040100005240140f42242240f []),(.fork 0x43b449436407420420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x9 : Block 87 8 (successors 87 8 s21) 90 10 := offMemoRows (code:=0x400400406406406406001406420001) (gs:=[(.fork 0x42040a46f40a42040542440542005640640040640040040640040642042042042042047240142000040140f42040f42042242002a40f []),(.fork 0x47344944904a43843844900040640605205242242247205242247247200042040742040740740640640440447347303204640043b40043b400400407400407400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x10 : Block 87 8 (successors 87 8 s21) 100 10 := offMemoRows (code:=0x40e40e40e40e424472001424400400) (gs:=[(.fork 0x43940604404640500040704242400e421420438044420 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x11 : Block 87 8 (successors 87 8 s21) 110 10 := offMemoRows (code:=0x40e40a001472001472421472422472) (gs:=[(.fork 0x43c052406434420052420052472 []),(.fork 0x400012425404406401420052401472 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x12 : Block 87 8 (successors 87 8 s21) 120 10 := offMemoRows (code:=0x40e40040040040e40e40e40a40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x13 : Block 87 8 (successors 87 8 s21) 130 10 := offMemoRows (code:=0x40e40e40e40e40e40e40e40e400400) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b21x14 : Block 87 8 (successors 87 8 s21) 140 10 := offMemoRows (code:=0x142100142140e40e40e40e) (gs:=[(.fork 0x4a47240909240640f000403420044420421 []),(.fork 0x425421400012420401000401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc21 : Excluded 87 9 s21 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b21x0
  · exact b21x1
  · exact b21x2
  · exact b21x3
  · exact b21x4
  · exact b21x5
  · exact b21x6
  · exact b21x7
  · exact b21x8
  · exact b21x9
  · exact b21x10
  · exact b21x11
  · exact b21x12
  · exact b21x13
  · exact b21x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc22 : Excluded 87 9 s22 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc23 : Excluded 87 9 s23 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc24 : Excluded 87 9 s24 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x0 : Block 87 8 (successors 87 8 s25) 0 10 := offMemoRows (code:=0x42340f424400423001424001423400) (gs:=[(.fork 0x42440a42f40a42440704440742042041541542342340142404640140f42402440f []),(.fork 0x42f42442340a42f40a42340705340742342340640040640042342340540040540042401640142300a40140f42344640f424423 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x1 : Block 87 8 (successors 87 8 s25) 10 10 := offMemoRows (code:=0x100142340144640f423001446001) (gs:=[(.fork 0x44640a02440a44640745040744640002640041e41e414414423423401446046401 []),(.fork 0x42340a03340a45044642340745040742342340640f40640f42342340540640540644601640142300a401400423424400446423 []),(.fork 0x40f04440f00040a02440a00040708440700040004440042542505245a000423423 []),(.fork 0x42545a052423423401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x2 : Block 87 8 (successors 87 8 s25) 20 10 := offMemoRows (code:=0x406406406406405406001401423001) (gs:=[(.fork 0x42340700040742342342342340540640540640f42344640f40a42300040a400423424400405406406405052423 []),(.fork 0x44600a42400a00a42544a052423401052 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x3 : Block 87 8 (successors 87 8 s25) 30 10 := offMemoRows (code:=0x406406406001406406405406406406) (gs:=[(.fork 0x42442f42f42442404442404a406406424424420405420405405404424400423400423400400405400405400424001406406424024 [(.fork 0x42f412022400423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x4 : Block 87 8 (successors 87 8 s25) 40 10 := offMemoRows (code:=0x406406406001406406406406406406) (gs:=[(.fork 0x44602444645045044644602644604a40640644644641e40541e40540540344640f42340f42340f40f40540f40540f446001406406 [(.fork 0x45041302240f423 [])])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x5 : Block 87 8 (successors 87 8 s25) 50 10 := offMemoRows (code:=0x424405406406406406406406406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x6 : Block 87 8 (successors 87 8 s25) 60 10 := offMemoRows (code:=0x1001001405446405446405424405) (gs:=[(.fork 0x4400002200008200004445a04445a04440540545a45a05240645a406406401423401423401401406401406406405405 []),(.fork 0x40540505240642340140140645a406405405 []),(.fork 0x423000423000423446423424405405401401405405405405406406423405052405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x7 : Block 87 8 (successors 87 8 s25) 70 10 := offMemoRows (code:=0x1424001424446424001424001405) (gs:=[(.fork 0x446012424012405406052423401401406052406405052 []),(.fork 0x41c406026402423026423424 []),(.fork 0xc431046428001013400404423044423424 [(.fork 0x42f022412423400 [])]),(.fork 0x405012425401423000401424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x8 : Block 87 8 (successors 87 8 s25) 80 10 := offMemoRows (code:=0x406406423001474407001001423407) (gs:=[(.fork 0x40a02440a00008243b43b46345046304a43843843843842342340100008640140f45000a00045040f45040f400000046400 []),(.fork 0x43b463438438407423423026446 []),(.fork 0x42340a00040a42300040640740640742344642342442342340540640540642342342342342347440142300040140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x9 : Block 87 8 (successors 87 8 s25) 90 10 := offMemoRows (code:=0x424474001424405474001405406406) (gs:=[(.fork 0x40543840642340740502a446406407463406 []),(.fork 0x464436423044423424 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x10 : Block 87 8 (successors 87 8 s25) 100 10 := offMemoRows (code:=0x1474446474450446431474001474) (gs:=[(.fork 0x466474423465026423 []),(.fork 0x43c434423084423474 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x11 : Block 87 8 (successors 87 8 s25) 110 10 := offMemoRows (code:=0x42300143140a00100142340a001474) (gs:=[(.fork 0x40501242540142300a401474 []),(.fork 0x40702640700002245145146802a46842f42a42a42a42a42342340100002640140f00002640f40042f00a00042f40042f400 []),(.fork 0x45146842a42a40a423423046424 []),(.fork 0x42340700040742300040640a40640a42344642342442342342342340540640540642342342343140142300040140f42344640f400423424400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x12 : Block 87 8 (successors 87 8 s25) 120 10 := offMemoRows (code:=0x144642443142f424405431001405) (gs:=[(.fork 0x40542a40640a40646840642340a40504a424 []),(.fork 0x469454423024423446 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b25x13 : Block 87 8 (successors 87 8 s25) 130 10 := offMemoRows (code:=0x1446001446001431001431446431) (gs:=[(.fork 0x430457423024423431 []),(.fork 0x40501242540142300a401431 []),(.fork 0xc47404646a00101340f403423044423446 [(.fork 0x45002241342340f [])]),(.fork 0x405012425401423000401446 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc25 : Excluded 87 9 s25 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=14) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b25x0
  · exact b25x1
  · exact b25x2
  · exact b25x3
  · exact b25x4
  · exact b25x5
  · exact b25x6
  · exact b25x7
  · exact b25x8
  · exact b25x9
  · exact b25x10
  · exact b25x11
  · exact b25x12
  · exact b25x13
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc26 : Excluded 87 9 s26 := offAudit (g:=(.saved 6)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x0 : Block 87 8 (successors 87 8 s27) 0 10 := offMemoRows (code:=0x400405405405001405400406406406) (gs:=[(.fork 0x41540a42a40a42400041540704440740540540040640040600042442442a40540541542441540042440041502440540540141504640140f41500040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x1 : Block 87 8 (successors 87 8 s27) 10 10 := offMemoRows (code:=0x40540540f40540540500140540f405) (gs:=[(.fork 0x41440a02440a44643841440743840741404441440000040040540540f40640f406000446446000405405414446414406446406405405401414046401 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x2 : Block 87 8 (successors 87 8 s27) 20 10 := offMemoRows (code:=0x406405406405401405405405001405) (gs:=[(.fork 0x4400040f04440f00040a02440a45a06200040708440700004400040004440040540540540640540645a02445b45a02a45a45a05245a00040645a45a406405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x3 : Block 87 8 (successors 87 8 s27) 30 10 := offMemoRows (code:=0x406406406406406406406405406406) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x4 : Block 87 8 (successors 87 8 s27) 40 10 := offMemoRows (code:=0x406406406406406406001406406406) (gs:=[(.fork 0x2642a02a42a02a42a00042a42a40640642a0c242442442a42a42a40a40a42a40a40640645b45b42a45100c42a45142a40a40a42a40a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x5 : Block 87 8 (successors 87 8 s27) 50 10 := offMemoRows (code:=0x405405406001406406406406406406) (gs:=[(.fork 0x45b00045b00044a44a45b44a02a44a44a45b44a02a44a00044a00040640644a44a45b44a02a44a44a45b44a000406406 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x6 : Block 87 8 (successors 87 8 s27) 60 10 := offMemoRows (code:=0x405405001405405405405405405405) (gs:=[(.fork 0x4240502245a08440508200004245a02440545a45b45a02a45a45a05240645a406406401405405405405425405405405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x7 : Block 87 8 (successors 87 8 s27) 70 10 := offMemoRows (code:=0x23415001415414415001415405405) (gs:=[(.fork 0x41c40f046400026402405000405415 []),(.fork 0x1c42a042428048406401046412400404405044405415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x8 : Block 87 8 (successors 87 8 s27) 80 10 := offMemoRows (code:=0x1406405405405407405001405407) (gs:=[(.fork 0x43840a02440a40508240740640740643840646340600443843843843802443802240540543846340540540143808640140f43844b00043840f44b40f400438046400 []),(.fork 0x43808a43806243843843800040640643806244644643843843840740743840740640645b45b00002443843b02443843b438407407438407 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x9 : Block 87 8 (successors 87 8 s27) 90 10 := offMemoRows (code:=0x1415405405405405406406406406) (gs:=[(.fork 0x464436405044405407022415 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x10 : Block 87 8 (successors 87 8 s27) 100 10 := offMemoRows (code:=0x41443843841442a43800142a415438) (gs:=[(.fork 0x46640602640a04640702642a405465026405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x11 : Block 87 8 (successors 87 8 s27) 110 10 := offMemoRows (code:=0x40540a40500140540a001438001438) (gs:=[(.fork 0x43c072406434405084405062438 []),(.fork 0x40506242545b40640140500a405407006438 []),(.fork 0x42a04442a40702640740502240a40640a40642a46842a40646840600442a42a02242a42a40540540540540142a02640140f42a02640f40042a45900042a400459400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x12 : Block 87 8 (successors 87 8 s27) 120 10 := offMemoRows (code:=0x41542a42a415405405405405405405) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x13 : Block 87 8 (successors 87 8 s27) 130 10 := offMemoRows (code:=0x141400142a00142a41442a001414) (gs:=[(.fork 0x46945440502440540a022414 []),(.fork 0x4300c202840645740502440542a []),(.fork 0x4050c242545b40640140500a40540a00642a []),(.fork 0x1c43804246a04840640104641340f403405044405414 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b27x14 : Block 87 8 (successors 87 8 s27) 140 10 := offMemoRows (code:=0x23414) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc27 : Excluded 87 9 s27 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b27x0
  · exact b27x1
  · exact b27x2
  · exact b27x3
  · exact b27x4
  · exact b27x5
  · exact b27x6
  · exact b27x7
  · exact b27x8
  · exact b27x9
  · exact b27x10
  · exact b27x11
  · exact b27x12
  · exact b27x13
  · exact b27x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc40 : Excluded 87 9 s40 := offAudit (g:=(.saved 0)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x0 : Block 87 8 (successors 87 8 s41) 0 10 := offMemoRows (code:=0x43640140d40f40d40d40d40d40d40f) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x1 : Block 87 8 (successors 87 8 s41) 10 10 := offMemoRows (code:=0x400400400400001401436001001001) (gs:=[(.fork 0x40840f40840f04243300040a43343340a40a000406052406000405022405435408434434429433404404436436 []),(.fork 0x8440e434435404436436401 []),(.fork 0x43641043643643648143643640040740040740f43641040f40a43648140a40643600040640543605240540040740740004a436 []),(.fork 0x43404a43640104204a [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x2 : Block 87 8 (successors 87 8 s41) 20 10 := offMemoRows (code:=0x407001407400400400407400400400) (gs:=[(.fork 0x44744744744700004243904240d40d40740744544540d40d02302240d40d43640543640540540740704240d400438400438400400405400405400 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x3 : Block 87 8 (successors 87 8 s41) 30 10 := offMemoRows (code:=0x40740e407407407407407407407407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x4 : Block 87 8 (successors 87 8 s41) 40 10 := offMemoRows (code:=0x407407407407407407407407407407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x5 : Block 87 8 (successors 87 8 s41) 50 10 := offMemoRows (code:=0x40040040040040d400400407400407) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x6 : Block 87 8 (successors 87 8 s41) 60 10 := offMemoRows (code:=0x1001436405400400400400001400) (gs:=[(.fork 0x40840840e40e40e40e08240e00004241241202302240e40e429042400400404407404407407408408401436401436401401407401407407400400 []),(.fork 0x48240a48240a00040604a40648341643843844848241541543643640100002240140f41602200041640f41640f []),(.fork 0x43848341540543643604640d [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x7 : Block 87 8 (successors 87 8 s41) 70 10 := offMemoRows (code:=0x40d40d400400400400436001001405) (gs:=[(.fork 0x41504243640504a046 []),(.fork 0x43640a48140a43640600040643641040740040740043648143643640040740040743643643604640143605240140f43641040f [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x8 : Block 87 8 (successors 87 8 s41) 80 10 := offMemoRows (code:=0x100143640600100100108b40d40d) (gs:=[(.fork 0x4a46402241b022000436022436027 []),(.fork 0x41502402740e08a407052436405000405 []),(.fork 0x40d08a024400092434401436000401027 []),(.fork 0x48540a48540a00040504a40548404243b43b47204242042043643640100005240140f42242240f []),(.fork 0x43b484420406436436 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x9 : Block 87 8 (successors 87 8 s41) 90 10 := offMemoRows (code:=0x1464400400400400436001464406) (gs:=[(.fork 0x43640a48140a43640500040543600043600043643640040640040643643643646440143600040140f43641040f400407407400 []),(.fork 0x42446443642304a423 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x10 : Block 87 8 (successors 87 8 s41) 100 10 := offMemoRows (code:=0x40d40d40d40d40e40e40e40e001464) (gs:=[(.fork 0x41540702246443640504a405 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x11 : Block 87 8 (successors 87 8 s41) 110 10 := offMemoRows (code:=0x40e40a40e40e40e40a001464001464) (gs:=[(.fork 0x43c425436052436464 []),(.fork 0x400042434401436052401464 [])]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x12 : Block 87 8 (successors 87 8 s41) 120 10 := offMemoRows (code:=0x40e40e40e40e40040040040040e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x13 : Block 87 8 (successors 87 8 s41) 130 10 := offMemoRows (code:=0x40d40d40e40e40e40e40e40e40e40e) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem b41x14 : Block 87 8 (successors 87 8 s41) 140 10 := offMemoRows (code:=0x40d40d) (gs:=[]) certifiedDB (by decide) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc41 : Excluded 87 9 s41 := by
  apply join_exclusions (by decide +kernel)
  apply blocks_cover (width:=10) (q:=15) (by decide) (by decide +kernel)
  intro j;fin_cases j
  · exact b41x0
  · exact b41x1
  · exact b41x2
  · exact b41x3
  · exact b41x4
  · exact b41x5
  · exact b41x6
  · exact b41x7
  · exact b41x8
  · exact b41x9
  · exact b41x10
  · exact b41x11
  · exact b41x12
  · exact b41x13
  · exact b41x14
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc42 : Excluded 87 9 s42 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc56 : Excluded 87 9 s56 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc57 : Excluded 87 9 s57 := offAudit (g:=(.saved 13)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem exc58 : Excluded 87 9 s58 := offAudit (g:=(.saved 7)) certifiedDB (by decide) (by decide +kernel)
end Theta

namespace Theta
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem theta_excluded : Excluded 87 10 inputs := by
  apply join_exclusions (by decide +kernel)
  intro v mem
  rw [firstLayer_eq] at mem
  simp only [firstLayer,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact exc0
  · exact exc1
  · exact exc2
  · exact fun h => exc2 (sym3 h)
  · exact exc4
  · exact exc5
  · exact exc6
  · exact exc7
  · exact exc8
  · exact exc9
  · exact exc10
  · exact exc11
  · exact fun h => exc8 (sym12 h)
  · exact fun h => exc9 (sym13 h)
  · exact fun h => exc10 (sym14 h)
  · exact fun h => exc11 (sym15 h)
  · exact exc16
  · exact exc17
  · exact exc18
  · exact fun h => exc18 (sym19 h)
  · exact exc20
  · exact exc21
  · exact exc22
  · exact exc23
  · exact exc24
  · exact exc25
  · exact exc26
  · exact exc27
  · exact fun h => exc20 (sym28 h)
  · exact fun h => exc21 (sym29 h)
  · exact fun h => exc22 (sym30 h)
  · exact fun h => exc23 (sym31 h)
  · exact fun h => exc20 (sym32 h)
  · exact fun h => exc21 (sym33 h)
  · exact fun h => exc22 (sym34 h)
  · exact fun h => exc23 (sym35 h)
  · exact fun h => exc24 (sym36 h)
  · exact fun h => exc25 (sym37 h)
  · exact fun h => exc26 (sym38 h)
  · exact fun h => exc27 (sym39 h)
  · exact exc40
  · exact exc41
  · exact exc42
  · exact fun h => exc42 (sym43 h)
  · exact fun h => exc4 (sym44 h)
  · exact fun h => exc5 (sym45 h)
  · exact fun h => exc6 (sym46 h)
  · exact fun h => exc7 (sym47 h)
  · exact fun h => exc20 (sym48 h)
  · exact fun h => exc21 (sym49 h)
  · exact fun h => exc23 (sym50 h)
  · exact fun h => exc22 (sym51 h)
  · exact fun h => exc0 (sym52 h)
  · exact fun h => exc1 (sym53 h)
  · exact fun h => exc2 (sym54 h)
  · exact fun h => exc2 (sym55 h)
  · exact exc56
  · exact exc57
  · exact exc58
  · exact fun h => exc58 (sym59 h)
  · exact fun h => exc8 (sym60 h)
  · exact fun h => exc9 (sym61 h)
  · exact fun h => exc11 (sym62 h)
  · exact fun h => exc10 (sym63 h)
  · exact fun h => exc56 (sym64 h)
  · exact fun h => exc57 (sym65 h)
  · exact fun h => exc58 (sym66 h)
  · exact fun h => exc58 (sym67 h)
  · exact fun h => exc4 (sym68 h)
  · exact fun h => exc5 (sym69 h)
  · exact fun h => exc6 (sym70 h)
  · exact fun h => exc7 (sym71 h)
  · exact fun h => exc40 (sym72 h)
  · exact fun h => exc41 (sym73 h)
  · exact fun h => exc42 (sym74 h)
  · exact fun h => exc42 (sym75 h)
  · exact fun h => exc8 (sym76 h)
  · exact fun h => exc9 (sym77 h)
  · exact fun h => exc11 (sym78 h)
  · exact fun h => exc10 (sym79 h)
  · exact fun h => exc4 (sym80 h)
  · exact fun h => exc5 (sym81 h)
  · exact fun h => exc6 (sym82 h)
  · exact fun h => exc7 (sym83 h)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem resolved : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro C fan eq
  have same : (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op)=counted := by
    funext g;rcases g with ⟨op,ins⟩;cases op <;> rfl
  rw [same]
  by_contra small
  obtain ⟨k,lim,live⟩ := trace C fan eq
  exact theta_excluded ⟨k,by omega,live,by decide +kernel⟩
end Theta

theorem thetaBound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  exact PEqualNP.Outside.L_meta_4423.Theta.resolved


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem suffixNonNotBound
    (eliminate : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11))
    (theta : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → 13 ≤ (x1.gates.drop 1).countP (fun g => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op) := by
  intro C fan first computes
  let charged := fun g : Gate => GateOp.rec
    (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  let edge := fun x : Fin 9 → Bool =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  have eqEdge : circuitFun 9 C = edge := computes.trans (by decide +kernel)
  obtain ⟨gates,out⟩ := C
  cases gates with
  | nil =>
    have h := first (fun _ => true)
    change false = true at h
    contradiction
  | cons g gs =>
    let tail : Circuit := ⟨gs,out⟩
    let ports : List (Fin 9) := List.ofFn id ++ [2]
    let f := fun x : Fin 9 → Bool => tail.eval (ports.map x)
    let step := fun (w : List Bool) (a : Gate) =>
      w ++ [a.op.eval (a.inputs.map fun k => w.getD k false)]
    have stable (rest : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
        (rest.foldl step w).getD k false = w.getD k false := by
      induction rest generalizing w with
      | nil => rfl
      | cons a rest ih =>
        rw [List.foldl_cons, ih (step w a) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ h
    have agrees (x : Fin 9 → Bool) (h : x 0 = false ∨ x 2 = true) : f x = edge x := by
      let w := List.ofFn x
      have hw : w.length = 9 := by simp [w]
      have a := first x
      change (gs.foldl step (step w g)).getD 9 false = _ at a
      rw [stable _ _ _ (by simp [step, hw])] at a
      have last : (step w g).getD 9 false = g.op.eval (g.inputs.map fun j => w.getD j false) := calc
        _ = (step w g).getD w.length false := congrArg (fun j => (step w g).getD j false) hw.symm
        _ = _ := by simp [step]
      rw [last] at a
      have orEq : (x 0 || x 2) = x 2 := by rcases h with h|h <;> simp [h]
      have start : ports.map x = step w g := by
        simp only [ports, step, List.map_append, List.map_singleton, List.map_ofFn, a, orEq]
        rfl
      change (gs.foldl step (ports.map x)).getD out false = edge x
      rw [start]
      exact congrFun eqEdge x
    let i0 : Fin 9 := 0
    let i4 : Fin 8 := 3
    let f8 := fun x : Fin 8 → Bool => edge (i0.insertNth false x)
    have restrict0 (x : Fin 8 → Bool) : f (i0.insertNth false x) = f8 x :=
      agrees _ (.inl (Fin.insertNth_apply_same ..))
    have tailFan : FanInTwo tail := fun t ht => fan t (List.mem_cons_of_mem g ht)
    have dep0 : ∃ x, f (Function.update x i0 true) ≠ f (Function.update x i0 false) := by
      refine ⟨fun q => decide (q = 2 ∨ q = 4), ?_⟩
      rw [agrees _ (.inr (by decide)), agrees _ (.inr (by decide))]
      decide
    have nc8 : ∃ y z, f (i0.insertNth false y) ≠ f (i0.insertNth false z) := by
      refine ⟨fun _ => true, fun _ => false, ?_⟩
      rw [restrict0, restrict0]
      decide
    obtain ⟨D, fanD, c1, eqD⟩ := eliminate 8 i0 tail ports tailFan dep0 nc8
    have Dval (x : Fin 8 → Bool) : D.eval ((List.ofFn (id : Fin 8 → Fin 8)).map x) = f8 x := by
      rw [List.map_ofFn]
      exact (congrFun eqD x).trans (restrict0 x)
    have dep4 : ∃ x : Fin 8 → Bool,
        f8 (Function.update x i4 true) ≠ f8 (Function.update x i4 false) := by
      exact ⟨fun q => decide (q = 2), by decide⟩
    have nc7 : ∃ y z, f8 (i4.insertNth false y) ≠ f8 (i4.insertNth false z) := by
      exact ⟨fun _ => true, fun _ => false, by decide⟩
    obtain ⟨T, fanT, c2, eqT⟩ := eliminate 7 i4 D (List.ofFn id) fanD
      (by simpa only [Dval] using dep4) (by simpa only [Dval] using nc7)
    have small := theta T fanT (eqT.trans (by
      funext y
      dsimp only
      rw [Dval]
      exact (by decide +kernel : ∀ z : Fin 7 → Bool, f8 (i4.insertNth false z) =
        ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] :
          List (Fin 7 × Fin 7)).any fun e => z e.1 && z e.2) y))
    change D.gates.countP charged + 1 ≤ gs.countP charged at c1
    change T.gates.countP charged + 1 ≤ D.gates.countP charged at c2
    change 11 ≤ T.gates.countP charged at small
    change 13 ≤ gs.countP charged
    omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem fromSuffix :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (5 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan nots first computes
  have bound := suffixNonNotBound eliminateSensitive thetaBound C fan first computes
  obtain ⟨i,j,order,position,ni,nj⟩ := nots
  let charged := fun g : Gate => GateOp.rec
    (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  obtain ⟨gates,out⟩ := C
  cases gates with
  | nil => exact Fin.elim0 i
  | cons g gs =>
    change 13 ≤ gs.countP charged at bound
    have positive : 0 < i.val := by omega
    have ilt : i.val < gs.length + 1 := i.isLt
    have jlt : j.val < gs.length + 1 := j.isLt
    have lt : i.val < j.val := order
    let u : Fin gs.length := ⟨i.val-1, by omega⟩
    let v : Fin gs.length := ⟨j.val-1, by omega⟩
    have shift (a : Fin (g :: gs).length) (z : Fin gs.length) (hz : a.val = z.val + 1) :
        (g :: gs).get a = gs.get z := by simp [List.get_eq_getElem, hz]
    have hu : gs[u.val].op = .not := by
      change (gs.get u).op = .not
      rwa [← shift i u (by dsimp [u]; omega)]
    have hv : gs[v.val].op = .not := by
      change (gs.get v).op = .not
      rwa [← shift j v (by dsimp [v]; omega)]
    have neq : u.val ≠ v.val := by dsimp [u,v]; omega
    let gate : Gate := ⟨.and, []⟩
    let updated := gs.set u.val gate
    have index : v.val < updated.length := by simp [updated]
    have preserve : updated[v.val].op = .not := by
      rw [show updated[v.val] = gs[v.val] from List.getElem_set_ne neq index]
      exact hv
    have count1 : updated.countP charged = gs.countP charged + 1 := by
      simp [updated, gate, List.countP_set u.isLt, charged, hu]
    have count2 : (updated.set v.val gate).countP charged = updated.countP charged + 1 := by
      simp [gate, List.countP_set index, charged, preserve]
    have count := List.countP_le_length (p := charged) (l := updated.set v.val gate)
    simp only [List.length_set] at count
    have len : updated.length = gs.length := List.length_set
    change 16 ≤ gs.length + 1
    omega

end PEqualNP.Outside.L_meta_4423

theorem PEqualNP.Outside.L_meta_4423 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (15 : ℕ) →       (∃ (x4 : Fin x1.gates.length) (x5 : Fin x1.gates.length), x4 < x5 ∧ ↑x4 = (5 : ℕ) ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool),             have x6 : List Bool := x1.wires (List.ofFn x5);             x6.getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ))) ∧ x6.getD x1.output Bool.false = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x7 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x7 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) x7)) →           have x6 : List (BitVec (512 : ℕ)) := List.map (fun (x6 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x6 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x6)) (List.range (7 : ℕ));           have x7 : Bool → Bool → BitVec (512 : ℕ) → BitVec (512 : ℕ) → BitVec (512 : ℕ) := fun (x7 x8 : Bool) (x9 x10 : BitVec (512 : ℕ)) =>             have x11 : BitVec (512 : ℕ) := (if x7 = Bool.true then x9 else ~~~x9) &&& if x8 = Bool.true then x10 else ~~~x10;             if x11.getLsbD (0 : ℕ) = Bool.true then ~~~x11 else x11;           ∃ (x8 : List (BitVec (512 : ℕ))),             x8.length ≤ (10 : ℕ) ∧               (∀ (x9 : Fin x8.length),                   have x10 : List (BitVec (512 : ℕ)) := x6 ++ List.take (↑x9) x8;                   ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool) (x14 : Bool), x8.get x9 = x7 x13 x14 x11 x12) ∧                 BitVec.ofNat (512 : ℕ) ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∈ x6 ++ x8 := by
  intro C fan small nots h
  exfalso
  have graphEq : ∀ x : Fin 9 → Bool,
      ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 n)) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5) := by decide +kernel
  have lower := PEqualNP.Outside.L_meta_4423.fromSuffix C fan nots
    (fun x => (h x).1) (funext fun x => (h x).2.trans (graphEq x))
  omega
