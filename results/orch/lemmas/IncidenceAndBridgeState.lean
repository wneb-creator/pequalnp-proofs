import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.AndBridge

open PEqualNP.CircuitLowerBounds

abbrev Rec (n : ℕ) := Finset (Fin n) × Finset ℕ × Finset (Fin n) × Finset ℕ
abbrev Form (n : ℕ) := Option (Finset (Fin n) × Finset ℕ)

def zeroF {n : ℕ} : Form n := some (∅, ∅)

def orF {n : ℕ} : List (Form n) → Form n
  | [] => some (∅, ∅)
  | f :: fs =>
    match f, orF fs with
    | none, _ => none
    | some _, none => none
    | some (a, b), some (c, d) => some (a ∪ c, b ∪ d)

structure St (n : ℕ) where
  fs : List (Form n)
  rs : List (Rec n)

def getF {n : ℕ} (s : St n) (i : ℕ) : Form n := s.fs.getD i zeroF

def andStep {n : ℕ} (s : St n) (fa fb : Form n) : St n :=
  match fa, fb with
  | none, f => ⟨s.fs ++ [f], s.rs⟩
  | some p, none => ⟨s.fs ++ [some p], s.rs⟩
  | some (va, ga), some (vb, gb) => ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [(va, ga, vb, gb)]⟩

def step {n : ℕ} (s : St n) (g : Gate) : St n :=
  match g.op, g.inputs with
  | GateOp.or, ins => ⟨s.fs ++ [orF (ins.map (getF s))], s.rs⟩
  | GateOp.and, [] => ⟨s.fs ++ [none], s.rs⟩
  | GateOp.and, [a] => ⟨s.fs ++ [getF s a], s.rs⟩
  | GateOp.and, a :: b :: _ => andStep s (getF s a) (getF s b)
  | _, _ => ⟨s.fs ++ [zeroF], s.rs⟩

def sv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (V : Finset (Fin n)) (G : Finset ℕ) : Bool :=
  decide (∃ v ∈ V, v ∈ U) || decide (∃ j ∈ G, vs.getD j false = true)

def rvStep {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (r : Rec n) : List Bool :=
  vs ++ [sv U vs r.1 r.2.1 && sv U vs r.2.2.1 r.2.2.2]

def rvals {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : List Bool := rs.foldl (rvStep U) []

def fv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : Form n → Bool
  | none => true
  | some p => sv U vs p.1 p.2

theorem fv_orF {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (fs : List (Form n)) :
    fv U vs (orF fs) = fs.any (fv U vs) := by
  induction fs with
  | nil => simp [orF, fv, sv]
  | cons f fs ih =>
    rcases f with _ | ⟨a, b⟩
    · simp [orF, fv]
    · rcases h : orF fs with _ | ⟨c, d⟩
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp [fv]
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp only [fv, sv, Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        ac_rfl

theorem rv_pre {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ (vs : List Bool) (j : ℕ), j < vs.length → (rs.foldl (rvStep U) vs).getD j false = vs.getD j false := by
  induction rs with
  | nil => intro vs j _; rfl
  | cons r rs ih =>
    intro vs j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [rvStep]; omega)]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem rv_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ vs : List Bool, (rs.foldl (rvStep U) vs).length = vs.length + rs.length := by
  induction rs with
  | nil => intro vs; simp
  | cons r rs ih => intro vs; simp only [List.foldl_cons, ih]; simp [rvStep]; omega

theorem rvals_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : (rvals U rs).length = rs.length := by
  simp [rvals, rv_len]

theorem rvals_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) :
    rvals U (rs ++ [r]) = rvStep U (rvals U rs) r := by
  simp [rvals, List.foldl_append]

theorem sv_congr {n : ℕ} (U : Finset (Fin n)) (vs vs' : List Bool) (V : Finset (Fin n)) (G : Finset ℕ)
    (h : ∀ j ∈ G, vs.getD j false = vs'.getD j false) : sv U vs V G = sv U vs' V G := by
  unfold sv
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj).symm ▸ hv⟩

def RefsLt {n : ℕ} (m : ℕ) (f : Form n) : Prop := ∀ p, f = some p → ∀ j ∈ p.2, j < m

def GoodRecs {n : ℕ} (rs : List (Rec n)) : Prop :=
  ∀ k (hk : k < rs.length), (∀ j ∈ rs[k].2.1, j < k) ∧ (∀ j ∈ rs[k].2.2.2, j < k)

theorem fv_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) (f : Form n)
    (hf : RefsLt rs.length f) : fv U (rvals U (rs ++ [r])) f = fv U (rvals U rs) f := by
  rcases f with _ | p
  · rfl
  · simp only [fv]
    apply sv_congr
    intro j hj
    have hjl := hf p rfl j hj
    rw [rvals_snoc]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rvals_len U]; exact hjl)]

theorem refs_orF {n : ℕ} (m : ℕ) (fs : List (Form n)) (h : ∀ f ∈ fs, RefsLt m f) : RefsLt m (orF fs) := by
  induction fs with
  | nil => intro p hp j hj; simp [orF] at hp; subst hp; simp at hj
  | cons f fs ih =>
    have ih' := ih (fun f' hf' => h f' (by simp [hf']))
    have hf := h f (by simp)
    intro p hp j hj
    rcases f with _ | ⟨a, b⟩
    · simp [orF] at hp
    · rcases hq : orF fs with _ | ⟨c, d⟩
      · simp [orF, hq] at hp
      · simp only [orF, hq, Option.some.injEq] at hp
        subst hp
        rcases Finset.mem_union.1 hj with hj | hj
        · exact hf _ rfl j hj
        · exact ih' _ hq j hj

theorem refs_getF {n : ℕ} (m : ℕ) (s : St n) (h : ∀ f ∈ s.fs, RefsLt m f) (i : ℕ) : RefsLt m (getF s i) := by
  unfold getF
  by_cases hi : i < s.fs.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp j hj
    simp [zeroF] at hp; subst hp; simp at hj

def Fw (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def Inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) : Prop :=
  s.fs.length = W.length ∧ (∀ f ∈ s.fs, RefsLt s.rs.length f) ∧ GoodRecs s.rs ∧
    ∀ i, W.getD i false = fv U (rvals U s.rs) (getF s i)

theorem getF_push {n : ℕ} (fs : List (Form n)) (rs : List (Rec n)) (f : Form n) (i : ℕ) :
    getF ⟨fs ++ [f], rs⟩ i = if i < fs.length then fs.getD i zeroF else if i = fs.length then f else zeroF := by
  unfold getF
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem fv_zero {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : fv U vs zeroF = false := by
  simp [fv, zeroF, sv]

theorem inv_push {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (f : Form n) (x : Bool)
    (hI : Inv U W s) (hf : RefsLt s.rs.length f) (hx : x = fv U (rvals U s.rs) f) :
    Inv U (W ++ [x]) ⟨s.fs ++ [f], s.rs⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, hg, ?_⟩
  · intro f' hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hr f' h
    · simp at h; subst h; exact hf
  · intro i
    rw [getF_push]
    split_ifs with h1 h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      exact this
    · subst h2; rw [hl]; simp [List.getD_eq_getElem?_getD, hx]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

theorem inv_rec {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (r : Rec n) (x : Bool)
    (hI : Inv U W s) (h1 : ∀ j ∈ r.2.1, j < s.rs.length) (h2 : ∀ j ∈ r.2.2.2, j < s.rs.length)
    (hx : x = (sv U (rvals U s.rs) r.1 r.2.1 && sv U (rvals U s.rs) r.2.2.1 r.2.2.2)) :
    Inv U (W ++ [x]) ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [r]⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · intro f' hf'
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases List.mem_append.1 hf' with h | h
    · intro p hp j hj; have := hr f' h p hp j hj; omega
    · simp at h; subst h; intro p hp j hj; simp at hp; subst hp; simp at hj; omega
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < s.rs.length
    · rw [List.getElem_append_left hk']; exact hg k hk'
    · have : k = s.rs.length := by omega
      subst this
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨h1, h2⟩
  · intro i
    rw [getF_push]
    split_ifs with hi1 hi2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      rw [this, fv_snoc U s.rs r]
      have := hr _ (List.getElem_mem (by omega : i < s.fs.length))
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact this
    · subst hi2
      rw [hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      have hlen : (rvals U s.rs).length = s.rs.length := rvals_len U s.rs
      simp only [fv, sv, rvals_snoc, rvStep, Finset.mem_singleton, exists_eq_left]
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp [hx, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem step_inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (g : Gate)
    (hI : Inv U W s) (hg : Ok g) : Inv U (Fw W g) (step s g) := by
  have hv := hI.2.2.2
  have hR : ∀ i, RefsLt s.rs.length (getF s i) := refs_getF s.rs.length s hI.2.1
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
      simp [GateOp.eval, fv]
    · apply inv_push U W s (getF s a) _ hI (hR a)
      have := hv a
      simp only [List.getD_eq_getElem?_getD] at this
      simp [Fw, GateOp.eval, this]
    · show Inv U (Fw W ⟨GateOp.and, [a, b]⟩) (andStep s (getF s a) (getF s b))
      have ea := hv a
      have eb := hv b
      rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
      · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
        rw [hfa] at ea; rw [hfb] at eb
        simp [Fw, GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (vb, gb)) _ hI (hfb ▸ hR b)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (va, ga)) _ hI (hfa ▸ hR a)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · have ha := hR a; rw [hfa] at ha
        have hb := hR b; rw [hfb] at hb
        apply inv_rec U W s (va, ga, vb, gb) _ hI (ha _ rfl) (hb _ rfl)
        rw [hfa] at ea; rw [hfb] at eb
        simp only [fv, List.getD_eq_getElem?_getD] at ea eb
        simp [Fw, GateOp.eval, ea, eb]
    · simp at hlen
  · apply inv_push U W s (orF (ins.map (getF s))) _ hI
      (refs_orF _ _ (fun f hf => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
        exact hR i))
    rw [fv_orF]
    simp only [GateOp.eval, List.any_map]
    congr 1
    funext i
    have := hv i
    simp only [List.getD_eq_getElem?_getD] at this
    simp [Function.comp, this]

theorem fold_inv {n : ℕ} (U : Finset (Fin n)) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ (W : List Bool) (s : St n), Inv U W s → Inv U (gs.foldl Fw W) (gs.foldl step s) := by
  induction gs with
  | nil => intro W s h; exact h
  | cons g gs ih =>
    intro W s h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (step_inv U W s g h (hgs g (by simp)))

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  unfold isAnd
  split <;> simp_all

theorem step_rs {n : ℕ} (s : St n) (g : Gate) :
    (step s g).rs.length ≤ s.rs.length + (if isAnd g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step, isAnd] <;> try simp
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [step]
  · simp
  · simp
  · unfold andStep
    split <;> simp

theorem fold_rs {n : ℕ} (gs : List Gate) :
    ∀ s : St n, (gs.foldl step s).rs.length ≤ s.rs.length + gs.countP isAnd := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    simp only [List.foldl_cons, List.countP_cons]
    have h1 := ih (step s g)
    have h2 := step_rs s g
    split_ifs at h2 ⊢ <;> omega

theorem rvals_split {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k : ℕ) :
    rvals U rs = (rs.drop k).foldl (rvStep U) (rvals U (rs.take k)) := by
  unfold rvals
  rw [← List.foldl_append, List.take_append_drop]

theorem rvals_take {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k j : ℕ) (hj : j < k) (hk : k ≤ rs.length) :
    (rvals U rs).getD j false = (rvals U (rs.take k)).getD j false := by
  rw [rvals_split U rs k, rv_pre]
  rw [rvals_len, List.length_take]; omega

theorem rec_val {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (k : ℕ) (hk : k < rs.length) :
    (rvals U rs).getD k false = (sv U (rvals U rs) rs[k].1 rs[k].2.1 && sv U (rvals U rs) rs[k].2.2.1 rs[k].2.2.2) := by
  rw [rvals_take U rs (k + 1) k (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hk, rvals_snoc]
  have hl : (rvals U (rs.take k)).length = k := by rw [rvals_len, List.length_take]; omega
  simp only [rvStep]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  obtain ⟨h1, h2⟩ := hg k hk
  congr 1
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h1 j hj) (by omega)).symm
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h2 j hj) (by omega)).symm

def toACC {n : ℕ} (rs : List (Rec n)) (V : Finset (Fin n)) (G : Finset ℕ) : PEqualNP.AndCount.AndCountCircuit n where
  size := rs.length
  leftVars i := rs[i].1
  leftGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.1)
  rightVars i := rs[i].2.2.1
  rightGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.2.2)
  outVars := V
  outGates := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ G)

theorem side_eq {n : ℕ} (U : Finset (Fin n)) (m : ℕ) (B : Finset (Fin n)) (G : Finset ℕ) (i : Fin m)
    (val : Fin m → Bool) (vs : List Bool) (hG : ∀ j ∈ G, j < i.val)
    (hval : ∀ j : Fin m, j < i → val j = vs.getD j false) :
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B (Finset.univ.filter (fun j : Fin m => j.val ∈ G)) i val
      = sv U vs B G := by
  unfold PEqualNP.AndCount.AndCountCircuit.sideTrue sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hji, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val, hj, by rw [← hval j hji]; exact hv⟩
  · rintro ⟨j, hj, hv⟩
    have hji := hG j hj
    refine ⟨⟨j, by omega⟩, by simp [hj], hji, ?_⟩
    rw [hval ⟨j, by omega⟩ hji]
    exact hv

theorem fuel {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    ∀ d (i : Fin rs.length), i.val < d →
      (toACC rs V G).gateValFuel U d i = (rvals U rs).getD i false := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    rw [rec_val U rs hg i i.isLt]
    obtain ⟨h1, h2⟩ := hg i i.isLt
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel]
    have hv : ∀ j : Fin rs.length, j < i → (toACC rs V G).gateValFuel U d j = (rvals U rs).getD j false :=
      fun j hj => ih j (by omega)
    congr 1
    · exact side_eq U rs.length _ _ i _ _ h1 hv
    · exact side_eq U rs.length _ _ i _ _ h2 hv

theorem eval_eq {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < rs.length) : (toACC rs V G).eval U = sv U (rvals U rs) V G := by
  unfold PEqualNP.AndCount.AndCountCircuit.eval sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j.val ∈ G := (Finset.mem_filter.1 hj).2
    refine ⟨j.val, hj', ?_⟩
    exact (fuel U rs hg V G rs.length j j.isLt).symm.trans hv
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j, hG j hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
    exact (fuel U rs hg V G rs.length ⟨j, hG j hj⟩ (hG j hj)).trans hv

theorem wf {n : ℕ} (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    (toACC rs V G).WellFormed := by
  intro i
  obtain ⟨h1, h2⟩ := hg i i.isLt
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact h1 j (Finset.mem_filter.1 hj).2
  · exact h2 j (Finset.mem_filter.1 hj).2


def NoTop {n : ℕ} (s : St n) : Prop := ∀ f ∈ s.fs, f ≠ none

lemma getF_some {n : ℕ} (s : St n) (hn : NoTop s) (i : ℕ) :
    ∃ p, getF s i = some p := by
  by_cases hi : i < s.fs.length
  · have hh := hn (s.fs[i]) (List.getElem_mem hi)
    rw [getF, List.getD_eq_getElem _ _ hi]
    cases he : s.fs[i] with
    | none => exact (hh he).elim
    | some p => exact ⟨p, rfl⟩
  · exact ⟨(∅, ∅), by rw [getF, List.getD_eq_default _ _ (by omega)]; rfl⟩

lemma step_shape {n : ℕ} (s : St n) (hn : NoTop s) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    ∃ p, (step s g).fs = s.fs ++ [some p] ∧
      (step s g).rs.length = s.rs.length + (if isAnd g = true then 1 else 0) ∧
      (g.op = GateOp.and → p = (∅, {s.rs.length})) := by
  obtain ⟨a, b, hins⟩ := List.length_eq_two.mp hlen
  obtain ⟨pa, ha⟩ := getF_some s hn a
  obtain ⟨pb, hb⟩ := getF_some s hn b
  rcases g with ⟨op, ins⟩
  simp only at hins hop
  subst ins
  rcases hop with rfl | rfl
  · exact ⟨(∅, {s.rs.length}), by simp [step, ha, hb, andStep, isAnd]⟩
  · rcases pa with ⟨va, ga⟩
    rcases pb with ⟨vb, gb⟩
    exact ⟨(va ∪ vb, ga ∪ gb), by simp [step, ha, hb, orF, isAnd]⟩

lemma step_noTop {n : ℕ} (s : St n) (hn : NoTop s) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    NoTop (step s g) := by
  obtain ⟨p, hp, _, _⟩ := step_shape s hn g hop hlen
  intro f hf
  rw [hp] at hf
  rcases List.mem_append.mp hf with hf | hf
  · exact hn f hf
  · simp only [List.mem_singleton] at hf
    subst f
    simp

lemma fold_noTop {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : St n) (hn : NoTop s) : NoTop (gs.foldl step s) := by
  induction gs generalizing s with
  | nil => exact hn
  | cons g gs ih =>
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    exact step_noTop s hn g (hgs g (List.mem_cons_self ..)).1
      (hgs g (List.mem_cons_self ..)).2

lemma fold_count {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : St n) (hn : NoTop s) :
    (gs.foldl step s).rs.length = s.rs.length + gs.countP isAnd := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    rw [List.foldl_cons, ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _
      (step_noTop s hn g hg.1 hg.2)]
    obtain ⟨_, _, he, _⟩ := step_shape s hn g hg.1 hg.2
    rw [he, List.countP_cons]
    split_ifs <;> omega

lemma fold_fs_length {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : St n) (hn : NoTop s) :
    (gs.foldl step s).fs.length = s.fs.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    rw [List.foldl_cons, ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _
      (step_noTop s hn g hg.1 hg.2)]
    obtain ⟨_, he, _, _⟩ := step_shape s hn g hg.1 hg.2
    simp [he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma fold_fs_preserve {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : St n) (hn : NoTop s) (i : ℕ) (hi : i < s.fs.length) :
    getF (gs.foldl step s) i = getF s i := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (List.mem_cons_self ..)
    obtain ⟨p, he, _, _⟩ := step_shape s hn g hg.1 hg.2
    rw [List.foldl_cons, ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _
      (step_noTop s hn g hg.1 hg.2) (by simp [he]; omega)]
    unfold getF
    rw [he]
    exact List.getD_append _ _ _ _ hi

def initial (n : ℕ) : St n := ⟨List.ofFn (fun i : Fin n => some ({i}, ∅)), []⟩

def build {n : ℕ} (gs : List Gate) : St n := gs.foldl step (initial n)

lemma initial_noTop (n : ℕ) : NoTop (initial n) := by
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  simp

lemma initial_inv {n : ℕ} (U : Finset (Fin n)) :
    Inv U (List.ofFn fun x : Fin n => decide (x ∈ U)) (initial n) := by
  refine ⟨by simp [initial], ?_, ?_, ?_⟩
  · intro f hf p hp j hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    simp only [Option.some.injEq] at hp
    subst hp
    simp at hj
  · intro k hk; simp [initial] at hk
  · intro i
    by_cases hi : i < n
    · simp only [getF, initial]
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      simp [fv, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [getF, initial]
      rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

lemma and_marker {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (k : ℕ) (hk : k < gs.length) (ha : gs[k].op = GateOp.and) :
    getF (build (n := n) gs) (n + k) = some (∅, {(gs.take k).countP isAnd}) := by
  let s : St n := build (gs.take k)
  have hpre : ∀ g ∈ gs.take k,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => hgs g (List.mem_of_mem_take hg)
  have hpost : ∀ g ∈ gs.drop (k + 1),
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => hgs g (List.mem_of_mem_drop hg)
  have hn : NoTop s := fold_noTop _ hpre _ (initial_noTop n)
  have hlen : s.fs.length = n + k := by
    simpa [s, build, initial, Nat.min_eq_left (Nat.le_of_lt hk)] using
      fold_fs_length (gs.take k) hpre (initial n) (initial_noTop n)
  have hcnt : s.rs.length = (gs.take k).countP isAnd := by
    simpa [s, build, initial] using fold_count (gs.take k) hpre (initial n) (initial_noTop n)
  have hg := hgs gs[k] (List.getElem_mem hk)
  obtain ⟨p, hfs, hrs, hp⟩ := step_shape s hn gs[k] hg.1 hg.2
  have hp' := hp ha
  have hdecomp : gs = (gs.take k ++ [gs[k]]) ++ gs.drop (k + 1) := by
    rw [← List.take_succ_eq_append_getElem hk, List.take_append_drop]
  have hbuild : build (n := n) gs = (gs.drop (k + 1)).foldl step (step s gs[k]) := by
    conv_lhs => rw [build, hdecomp]
    rw [List.foldl_append, List.foldl_append]
    rfl
  rw [hbuild, fold_fs_preserve _ hpost _ (step_noTop s hn gs[k] hg.1 hg.2)
    (n + k) (by simp [hfs, hlen])]
  unfold getF
  rw [hfs, ← hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  simp [hp', hcnt]

end PEqualNP.Outside.L_meta_2583_aux.AndBridge
