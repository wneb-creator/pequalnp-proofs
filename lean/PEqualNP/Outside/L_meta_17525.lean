import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_17525_aux.Convert

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

end PEqualNP.Outside.L_meta_17525_aux.Convert

namespace PEqualNP.Outside.L_meta_17525_aux

theorem Convert : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin (42 : ℕ))), (PEqualNP.MetaComplexity.circuitFun (42 : ℕ) x1 fun (x4 : Fin (42 : ℕ)) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin (42 : ℕ))), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun (42 : ℕ) x1 fun (x6 : Fin (42 : ℕ)) => Decidable.decide (x6 ∈ x5) := by
  intro C hmono hex
  obtain ⟨U0, hU0⟩ := hex
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_17525_aux.Convert.Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : PEqualNP.Outside.L_meta_17525_aux.Convert.St 42 := ⟨List.ofFn (fun i : Fin 42 => some ({i}, ∅)), []⟩
  let s := C.gates.foldl PEqualNP.Outside.L_meta_17525_aux.Convert.step s0
  have hinit : ∀ U : Finset (Fin 42), PEqualNP.Outside.L_meta_17525_aux.Convert.Inv U (List.ofFn fun x : Fin 42 => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < 42
      · simp only [PEqualNP.Outside.L_meta_17525_aux.Convert.getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [PEqualNP.Outside.L_meta_17525_aux.Convert.fv, PEqualNP.Outside.L_meta_17525_aux.Convert.sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [PEqualNP.Outside.L_meta_17525_aux.Convert.getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), PEqualNP.Outside.L_meta_17525_aux.Convert.fv_zero]
  have hinv : ∀ U : Finset (Fin 42), PEqualNP.Outside.L_meta_17525_aux.Convert.Inv U (C.gates.foldl PEqualNP.Outside.L_meta_17525_aux.Convert.Fw (List.ofFn fun x : Fin 42 => decide (x ∈ U))) s :=
    fun U => PEqualNP.Outside.L_meta_17525_aux.Convert.fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin 42), PEqualNP.MetaComplexity.circuitFun 42 C (fun x => decide (x ∈ U))
      = PEqualNP.Outside.L_meta_17525_aux.Convert.fv U (PEqualNP.Outside.L_meta_17525_aux.Convert.rvals U s.rs) (PEqualNP.Outside.L_meta_17525_aux.Convert.getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : PEqualNP.Outside.L_meta_17525_aux.Convert.getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [PEqualNP.Outside.L_meta_17525_aux.Convert.fv] at this
  · have hG : ∀ j ∈ G, j < s.rs.length := PEqualNP.Outside.L_meta_17525_aux.Convert.refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨PEqualNP.Outside.L_meta_17525_aux.Convert.toACC s.rs V G, PEqualNP.Outside.L_meta_17525_aux.Convert.wf s.rs hgood V G, ?_, ?_⟩
    · have h1 := PEqualNP.Outside.L_meta_17525_aux.Convert.fold_rs C.gates s0
      have h2 : C.gates.countP PEqualNP.Outside.L_meta_17525_aux.Convert.isAnd = Nat.card {x5 : Fin C.gates.length // (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        conv_lhs => rw [← List.ofFn_get C.gates]
        rw [List.countP_ofFn]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_17525_aux.Convert.isAnd_iff]
      change s.rs.length ≤ s0.rs.length + _ at h1
      have h0 : s0.rs.length = 0 := rfl
      show s.rs.length ≤ _
      omega
    · intro U
      rw [PEqualNP.Outside.L_meta_17525_aux.Convert.eval_eq U s.rs hgood V G hG, hfun U, hfo]
      rfl

end PEqualNP.Outside.L_meta_17525_aux

namespace PEqualNP.Outside.L_meta_17525_aux.Plane

namespace Pin

open PEqualNP.AndCount

private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private def signal {n k : ℕ} (U A : Finset (Fin n)) (P : Finset (Fin k))
    (val : Fin k → Bool) : Prop :=
  (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true

private theorem gate_spec {n : ℕ} (C : AndCountCircuit n) (hw : C.WellFormed)
    (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔ signal U (C.leftVars i) (C.leftGates i) (C.gateVal U) ∧
      signal U (C.rightVars i) (C.rightGates i) (C.gateVal U) := by
  rw [gateVal_eq, Bool.and_eq_true]
  simp only [signal, AndCountCircuit.sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases hr with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
    · rcases hr with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩

private def expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) : Finset (Fin n) :=
  A ∪ if i ∈ P then B else ∅

private def expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) :
    Finset (Fin m) :=
  Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)

private theorem mem_expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) (v : Fin n) :
    v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
  by_cases h : i ∈ P <;> simp [expandVars, h]

private theorem mem_expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1)))
    (k : Fin m) :
    k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
  simp [expandRefs]

private theorem signal_expand {n m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin n))
    (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool)
    (before : ∀ j ∈ F, j < i) (expand : val i = true ↔ signal U B F val)
    (agree : ∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) :
    signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨k, hk, ht⟩)
    · rcases (mem_expandVars i B A P v).mp hv with hvA | ⟨hi, hvB⟩
      · exact Or.inl ⟨v, hvA, hu⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inl ⟨v, hvB, hu⟩)⟩
    · rw [agree k hk] at ht
      rcases (mem_expandRefs i F P k).mp hk with hP | ⟨hi, hF⟩
      · exact Or.inr ⟨_, hP, ht⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inr ⟨_, hF, ht⟩)⟩
  · rintro (⟨v, hv, hu⟩ | ⟨j, hj, ht⟩)
    · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inl hv), hu⟩
    · by_cases hji : j = i
      · subst j
        rcases expand.mp ht with ⟨v, hv, hu⟩ | ⟨l, hl, ht'⟩
        · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
          have hk := (mem_expandRefs i F P k).mpr (Or.inr ⟨hj, hl⟩)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hk := (mem_expandRefs i F P k).mpr (Or.inl hj)
        exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩

private def Removal {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) : Prop :=
  ∃ C' : AndCountCircuit n, ∃ f : Fin C'.size → Fin C.size,
    C'.WellFormed ∧ C'.size + 1 = C.size ∧ StrictMono f ∧
    (∀ j, j ≠ i ↔ ∃ k, f k = j) ∧
    (∀ k, C.leftVars (f k) ⊆ C'.leftVars k ∧ C.rightVars (f k) ⊆ C'.rightVars k) ∧
    ∀ U ∈ D, C'.eval U = C.eval U ∧ ∀ j, C'.gateVal U j = C.gateVal U (f j)

private theorem eliminate {n m : ℕ}
    (lv rv : Fin (m + 1) → Finset (Fin n)) (lg rg : Fin (m + 1) → Finset (Fin (m + 1)))
    (ov : Finset (Fin n)) (og : Finset (Fin (m + 1))) (i : Fin (m + 1))
    (D : Set (Finset (Fin n))) (B : Finset (Fin n)) (F : Finset (Fin (m + 1)))
    (hw : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) (before : ∀ j ∈ F, j < i)
    (same : ∀ U ∈ D, (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U i = true ↔
      signal U B F ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U)) :
    Removal (AndCountCircuit.mk (m + 1) lv lg rv rg ov og) D i := by
  let C : AndCountCircuit n := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
  let C' : AndCountCircuit n :=
    ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
      fun j => expandRefs i F (lg (i.succAbove j)),
      fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
      fun j => expandRefs i F (rg (i.succAbove j)),
      expandVars i B ov og, expandRefs i F og⟩
  have lt_ref (j k : Fin m) (P : Finset (Fin (m + 1)))
      (old : ∀ l ∈ P, l < i.succAbove j) (hk : k ∈ expandRefs i F P) : k < j := by
    apply Fin.succAbove_lt_succAbove_iff.mp
    rcases (mem_expandRefs i F P k).mp hk with hp | ⟨hi, hf⟩
    · exact old _ hp
    · exact (before _ hf).trans (old i hi)
  have hw' : C'.WellFormed := by
    intro j
    exact ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
      fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
  refine ⟨C', i.succAbove, hw', rfl, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    exact Fin.succAbove_lt_succAbove_iff.mpr hjk
  · intro j
    exact ⟨Fin.exists_succAbove_eq, by rintro ⟨k, rfl⟩; exact Fin.succAbove_ne i k⟩
  · intro k
    exact ⟨fun _ h => (mem_expandVars i B _ _ _).mpr (Or.inl h),
      fun _ h => (mem_expandVars i B _ _ _).mpr (Or.inl h)⟩
  intro U hU
  have values (j : Fin m) : C'.gateVal U j = C.gateVal U (i.succAbove j) := by
    induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
    | h j ih =>
      rw [Bool.eq_iff_iff, gate_spec C' hw', gate_spec C hw]
      exact and_congr
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
  refine ⟨?_, values⟩
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)

private def Expandable {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) : Prop :=
  ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
    ∀ U ∈ D, C.gateVal U i = true ↔ signal U B F (C.gateVal U)

private theorem remove_one {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) (hw : C.WellFormed) (g : Expandable C D i) : Removal C D i := by
  obtain ⟨B, F, before, same⟩ := g
  rcases C with ⟨s, lv, lg, rv, rg, ov, og⟩
  cases s with
  | zero => exact Fin.elim0 i
  | succ m => exact eliminate lv rv lg rg ov og i D B F hw before same

variable {n : ℕ}

def pinReads (C : AndCountCircuit n) (T : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i)

theorem mem_pinReads (C : AndCountCircuit n) (T : Finset (Fin n)) (i : Fin C.size) :
    i ∈ pinReads C T ↔ ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by
  simp [pinReads]

theorem pinReads_card (C : AndCountCircuit n) (T : Finset (Fin n)) :
    (pinReads C T).card =
      {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard := by
  have eq : (↑(pinReads C T) : Set (Fin C.size)) =
      {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i} := by
    ext i
    exact mem_pinReads C T i
  rw [← eq, Set.ncard_coe_finset]

private theorem pin_expandable (C : AndCountCircuit n) (wf : C.WellFormed)
    (T : Finset (Fin n)) (i : Fin C.size) (hi : i ∈ pinReads C T) :
    Expandable C {U : Finset (Fin n) | T ⊆ U} i := by
  rcases (mem_pinReads C T i).mp hi with ⟨v, hv, vL | vR⟩
  · refine ⟨C.rightVars i, C.rightGates i, (wf i).2, ?_⟩
    intro U hU
    exact (gate_spec C wf U i).trans
      ⟨fun h => h.2, fun h => ⟨Or.inl ⟨v, vL, hU hv⟩, h⟩⟩
  · refine ⟨C.leftVars i, C.leftGates i, (wf i).1, ?_⟩
    intro U hU
    exact (gate_spec C wf U i).trans
      ⟨fun h => h.1, fun h => ⟨h, Or.inl ⟨v, vR, hU hv⟩⟩⟩

private theorem pin_remove (T : Finset (Fin n)) (s : ℕ) :
    ∀ (C : AndCountCircuit n), C.size = s → C.WellFormed →
      ∃ D : AndCountCircuit n, D.WellFormed ∧ pinReads D T = ∅ ∧
        D.size + (pinReads C T).card ≤ C.size ∧
        ∀ U : Finset (Fin n), T ⊆ U → D.eval U = C.eval U := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs wf
    by_cases e : pinReads C T = ∅
    · exact ⟨C, wf, e, by simp [e], fun _ _ => rfl⟩
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr e
      obtain ⟨C', f, wf', size, mono, ran, bare, sem⟩ :=
        remove_one C {U : Finset (Fin n) | T ⊆ U} i wf (pin_expandable C wf T i hi)
      have hsub : (pinReads C T).erase i ⊆ (pinReads C' T).image f := by
        intro j hj
        obtain ⟨jne, jmem⟩ := Finset.mem_erase.mp hj
        obtain ⟨k, rfl⟩ := (ran j).mp jne
        obtain ⟨v, hv, hraw⟩ := (mem_pinReads C T (f k)).mp jmem
        exact Finset.mem_image.mpr
          ⟨k, (mem_pinReads C' T k).mpr
            ⟨v, hv, hraw.imp (fun h => (bare k).1 h) (fun h => (bare k).2 h)⟩, rfl⟩
      have hcard : ((pinReads C T).erase i).card ≤ (pinReads C' T).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      have cs := Finset.card_erase_add_one hi
      obtain ⟨D, wd, empty, bound, val⟩ := ih C'.size (by omega) C' rfl wf'
      exact ⟨D, wd, empty, by omega, fun U hU => (val U hU).trans (sem U hU).1⟩

private def relabel (C : AndCountCircuit n)
    (f : Finset (Fin n) → Finset (Fin n)) : AndCountCircuit n :=
  ⟨C.size, fun i => f (C.leftVars i), C.leftGates, fun i => f (C.rightVars i),
    C.rightGates, f C.outVars, C.outGates⟩

private abbrev hit (U B : Finset (Fin n)) : Prop := ∃ v ∈ B, v ∈ U

private theorem eval_relabel (C : AndCountCircuit n) (f : Finset (Fin n) → Finset (Fin n))
    (U V : Finset (Fin n))
    (l : ∀ i, hit U (f (C.leftVars i)) ↔ hit V (C.leftVars i))
    (r : ∀ i, hit U (f (C.rightVars i)) ↔ hit V (C.rightVars i))
    (o : hit U (f C.outVars) ↔ hit V C.outVars) :
    (relabel C f).eval U = C.eval V := by
  have fuel (d : ℕ) (i : Fin C.size) :
      (relabel C f).gateValFuel U d i = C.gateValFuel V d i := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      change
        (AndCountCircuit.sideTrue U (f (C.leftVars i)) (C.leftGates i) i
          ((relabel C f).gateValFuel U d) &&
        AndCountCircuit.sideTrue U (f (C.rightVars i)) (C.rightGates i) i
          ((relabel C f).gateValFuel U d)) = _
      rw [show (relabel C f).gateValFuel U d = C.gateValFuel V d from funext ih]
      have side (B : Finset (Fin n)) (S : Finset (Fin C.size))
          (h : hit U (f B) ↔ hit V B) :
          AndCountCircuit.sideTrue U (f B) S i (C.gateValFuel V d) =
          AndCountCircuit.sideTrue V B S i (C.gateValFuel V d) := by
        unfold AndCountCircuit.sideTrue
        exact decide_eq_decide.mpr (or_congr h Iff.rfl)
      rw [side _ _ (l i), side _ _ (r i)] <;> rfl
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  change (hit U (f C.outVars) ∨
      ∃ j ∈ C.outGates, (relabel C f).gateValFuel U C.size j = true) ↔
    (hit V C.outVars ∨ ∃ j ∈ C.outGates, C.gateValFuel V C.size j = true)
  exact or_congr o (by simp only [fuel])

private theorem hit_mask_union (T F U B : Finset (Fin n))
    (none : ¬ hit T B) : hit U (B \ F) ↔ hit (T ∪ (U \ F)) B := by
  constructor
  · rintro ⟨v, hv, vu⟩
    obtain ⟨vb, vf⟩ := Finset.mem_sdiff.mp hv
    exact ⟨v, vb, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨vu, vf⟩)⟩
  · rintro ⟨v, vb, h⟩
    rcases Finset.mem_union.mp h with vt | vuf
    · exact (none ⟨v, vb, vt⟩).elim
    · obtain ⟨vu, vf⟩ := Finset.mem_sdiff.mp vuf
      exact ⟨v, Finset.mem_sdiff.mpr ⟨vb, vf⟩, vu⟩

theorem pin_exists (C : AndCountCircuit n) (wf : C.WellFormed)
    (T F : Finset (Fin n)) (hT : C.eval T = false) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.size + {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ C.size ∧
      ∀ U, D.eval U = C.eval (T ∪ (U \ F)) := by
  obtain ⟨E, ew, empty, bound, sem⟩ := pin_remove T C.size C rfl wf
  have l (i : Fin E.size) : ¬ hit T (E.leftVars i) := by
    rintro ⟨v, vl, vt⟩
    have hh := (mem_pinReads E T i).mpr ⟨v, vt, Or.inl vl⟩
    simp only [empty, Finset.notMem_empty] at hh
  have r (i : Fin E.size) : ¬ hit T (E.rightVars i) := by
    rintro ⟨v, vr, vt⟩
    have hh := (mem_pinReads E T i).mpr ⟨v, vt, Or.inr vr⟩
    simp only [empty, Finset.notMem_empty] at hh
  have o : ¬ hit T E.outVars := by
    intro h
    have et := (sem T (fun _ ht => ht)).trans hT
    have tt : E.eval T = true := by
      unfold AndCountCircuit.eval
      exact decide_eq_true (Or.inl h)
    rw [et] at tt
    contradiction
  refine ⟨relabel E (fun B => B \ F), ew, ?_, ?_⟩
  · rw [← pinReads_card]
    exact bound
  · intro U
    exact (eval_relabel E (fun B => B \ F) U (T ∪ (U \ F))
      (fun i => hit_mask_union T F U _ (l i))
      (fun i => hit_mask_union T F U _ (r i))
      (hit_mask_union T F U _ o)).trans
        (sem _ (fun _ ht => Finset.mem_union_left _ ht))

end Pin

namespace Pin

open PEqualNP.AndCount

variable {n m : ℕ}

def activeGraph (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := a ∈ A ∧ b ∈ A ∧ G.Adj a b
  symm := ⟨fun a b h => ⟨h.2.1, h.1, G.symm.symm a b h.2.2⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.2.2⟩

theorem activeGraph_adj (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a b : Fin n) :
    (activeGraph G A).Adj a b ↔ a ∈ A ∧ b ∈ A ∧ G.Adj a b := Iff.rfl

theorem activeGraph_univ (G : SimpleGraph (Fin n)) : activeGraph G Finset.univ = G := by
  ext a b
  simp [activeGraph_adj]

def closedPin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∈ T ∨ ∃ t ∈ T, G.Adj t v)

theorem mem_closedPin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (v : Fin n) :
    v ∈ closedPin G T ↔ v ∈ T ∨ ∃ t ∈ T, G.Adj t v := by
  simp [closedPin]

theorem mem_closedPin_singleton (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) : w ∈ closedPin G {v} ↔ w = v ∨ G.Adj v w := by
  simp [mem_closedPin]

abbrev HasEdge (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Prop :=
  ∃ a ∈ U, ∃ b ∈ U, G.Adj a b

abbrev Independent (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b

theorem singleton_independent (G : SimpleGraph (Fin n)) (v : Fin n) :
    Independent G {v} := by
  intro a ha b hb
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  subst a
  subst b
  exact G.loopless.irrefl v

theorem edges_on_cofactor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T U : Finset (Fin n)) (ind : Independent G T) :
    HasEdge (activeGraph G A) (T ∪ (U \ closedPin G T)) ↔
      HasEdge (activeGraph G (A \ closedPin G T)) U := by
  constructor
  · rintro ⟨a, ha, b, hb, hadj⟩
    obtain ⟨aa, bb, ab⟩ := (activeGraph_adj G A a b).mp hadj
    have aout : a ∉ T := by
      intro atT
      rcases Finset.mem_union.mp hb with bt | bf
      · exact ind a atT b bt ab
      · exact (Finset.mem_sdiff.mp bf).2
          ((mem_closedPin G T b).mpr (Or.inr ⟨a, atT, ab⟩))
    have bout : b ∉ T := by
      intro bt
      rcases Finset.mem_union.mp ha with atT | af
      · exact ind a atT b bt ab
      · exact (Finset.mem_sdiff.mp af).2
          ((mem_closedPin G T a).mpr (Or.inr ⟨b, bt, G.symm.symm a b ab⟩))
    have af := Finset.mem_sdiff.mp ((Finset.mem_union.mp ha).resolve_left aout)
    have bf := Finset.mem_sdiff.mp ((Finset.mem_union.mp hb).resolve_left bout)
    exact ⟨a, af.1, b, bf.1, (activeGraph_adj G _ a b).mpr
      ⟨Finset.mem_sdiff.mpr ⟨aa, af.2⟩, Finset.mem_sdiff.mpr ⟨bb, bf.2⟩, ab⟩⟩
  · rintro ⟨a, ha, b, hb, hadj⟩
    obtain ⟨aa, bb, ab⟩ := (activeGraph_adj G _ a b).mp hadj
    obtain ⟨aA, af⟩ := Finset.mem_sdiff.mp aa
    obtain ⟨bA, bf⟩ := Finset.mem_sdiff.mp bb
    exact ⟨a, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨ha, af⟩),
      b, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨hb, bf⟩),
      (activeGraph_adj G A a b).mpr ⟨aA, bA, ab⟩⟩

theorem pin_active (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes (activeGraph G A))
    (ind : Independent G T) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.Computes (activeGraph G (A \ closedPin G T)) ∧
      D.size + (pinReads C T).card ≤ C.size := by
  have hT : C.eval T = false := by
    apply Bool.eq_false_of_ne_true
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := (comp T).mp h
    exact ind a ha b hb ((activeGraph_adj G A a b).mp hab).2.2
  obtain ⟨D, wd, bound, sem⟩ := pin_exists C wf T (closedPin G T) hT
  refine ⟨D, wd, ?_, ?_⟩
  · intro U
    rw [sem U]
    exact (comp _).trans (edges_on_cofactor G A T U ind)
  · simpa only [pinReads_card C T] using bound

theorem pin_graph (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes G) (ind : Independent G T) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.Computes (activeGraph G (Finset.univ \ closedPin G T)) ∧
      D.size + (pinReads C T).card ≤ C.size :=
  pin_active C G Finset.univ T wf (by simpa only [activeGraph_univ] using comp) ind

private def relabelAcross (C : AndCountCircuit n)
    (f : Finset (Fin n) → Finset (Fin m)) : AndCountCircuit m :=
  ⟨C.size, fun i => f (C.leftVars i), C.leftGates, fun i => f (C.rightVars i),
    C.rightGates, f C.outVars, C.outGates⟩

private abbrev bareHit {s : ℕ} (U B : Finset (Fin s)) : Prop := ∃ v ∈ B, v ∈ U

private theorem eval_across (C : AndCountCircuit n) (f : Finset (Fin n) → Finset (Fin m))
    (U : Finset (Fin m)) (V : Finset (Fin n))
    (l : ∀ i, bareHit U (f (C.leftVars i)) ↔ bareHit V (C.leftVars i))
    (r : ∀ i, bareHit U (f (C.rightVars i)) ↔ bareHit V (C.rightVars i))
    (o : bareHit U (f C.outVars) ↔ bareHit V C.outVars) :
    (relabelAcross C f).eval U = C.eval V := by
  have fuel (d : ℕ) (i : Fin C.size) :
      (relabelAcross C f).gateValFuel U d i = C.gateValFuel V d i := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      change
        (AndCountCircuit.sideTrue U (f (C.leftVars i)) (C.leftGates i) i
          ((relabelAcross C f).gateValFuel U d) &&
        AndCountCircuit.sideTrue U (f (C.rightVars i)) (C.rightGates i) i
          ((relabelAcross C f).gateValFuel U d)) = _
      rw [show (relabelAcross C f).gateValFuel U d = C.gateValFuel V d from funext ih]
      have side (B : Finset (Fin n)) (S : Finset (Fin C.size))
          (h : bareHit U (f B) ↔ bareHit V B) :
          AndCountCircuit.sideTrue U (f B) S i (C.gateValFuel V d) =
          AndCountCircuit.sideTrue V B S i (C.gateValFuel V d) := by
        unfold AndCountCircuit.sideTrue
        exact decide_eq_decide.mpr (or_congr h Iff.rfl)
      rw [side _ _ (l i), side _ _ (r i)]
      rfl
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  change (bareHit U (f C.outVars) ∨
      ∃ j ∈ C.outGates, (relabelAcross C f).gateValFuel U C.size j = true) ↔
    (bareHit V C.outVars ∨ ∃ j ∈ C.outGates, C.gateValFuel V C.size j = true)
  exact or_congr o (by simp only [fuel])

def transport (C : AndCountCircuit n) (e : Fin n ≃ Fin m) : AndCountCircuit m :=
  relabelAcross C (fun B => B.map e.toEmbedding)

theorem transport_size (C : AndCountCircuit n) (e : Fin n ≃ Fin m) :
    (transport C e).size = C.size := rfl

theorem transport_wf (C : AndCountCircuit n) (e : Fin n ≃ Fin m) (wf : C.WellFormed) :
    (transport C e).WellFormed := wf

private theorem hit_transport (e : Fin n ≃ Fin m) (U : Finset (Fin m)) (B : Finset (Fin n)) :
    bareHit U (B.map e.toEmbedding) ↔ bareHit (U.map e.symm.toEmbedding) B := by
  constructor
  · rintro ⟨v, vb, vu⟩
    exact ⟨e.symm v, Finset.mem_map_equiv.mp vb,
      Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using vu)⟩
  · rintro ⟨v, vb, vu⟩
    exact ⟨e v, Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_apply_apply] using vb),
      by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using vu⟩

theorem transport_eval (C : AndCountCircuit n) (e : Fin n ≃ Fin m) (U : Finset (Fin m)) :
    (transport C e).eval U = C.eval (U.map e.symm.toEmbedding) :=
  eval_across C (fun B => B.map e.toEmbedding) U _ (fun _ => hit_transport e U _)
    (fun _ => hit_transport e U _) (hit_transport e U _)

theorem transport_computes (C : AndCountCircuit n)
    (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (e : Fin n ≃ Fin m)
    (adj : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b) (comp : C.Computes G) :
    (transport C e).Computes H := by
  intro U
  rw [transport_eval, comp (U.map e.symm.toEmbedding)]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨e a, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using ha,
      e b, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hb, (adj a b).mpr hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    have ha' : e.symm a ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨a, ha, rfl⟩
    have hb' : e.symm b ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨b, hb, rfl⟩
    exact ⟨e.symm a, ha', e.symm b, hb', (adj _ _).mp
      (by simpa only [Equiv.apply_symm_apply] using hab)⟩

abbrev Lower (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ (C : AndCountCircuit n), C.WellFormed → C.Computes G → k ≤ C.size

theorem lower_transport (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (e : Fin n ≃ Fin m)
    (adj : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b) {k : ℕ} (low : Lower G k) :
    Lower H k := by
  have inv (a b : Fin m) : G.Adj (e.symm a) (e.symm b) ↔ H.Adj a b := by
    simpa only [Equiv.apply_symm_apply] using (adj (e.symm a) (e.symm b)).symm
  intro C wf comp
  exact low (transport C e.symm) (transport_wf C _ wf) (transport_computes C H G e.symm inv comp)

theorem outVars_empty (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (comp : C.Computes G) : C.outVars = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  have tr : C.eval {v} = true := by
    unfold AndCountCircuit.eval
    exact decide_eq_true (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (comp _).mp tr
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  exact G.loopless.irrefl v (by simpa only [ea, eb] using hab)

private theorem miss_insert {v : Fin n} {U B : Finset (Fin n)} (nov : v ∉ B) :
    bareHit (insert v U) B ↔ bareHit U B := by
  constructor
  · rintro ⟨w, wb, hu⟩
    rcases Finset.mem_insert.mp hu with eq | wu
    · subst w
      exact (nov wb).elim
    · exact ⟨w, wb, wu⟩
  · rintro ⟨w, wb, wu⟩
    exact ⟨w, wb, Finset.mem_insert_of_mem wu⟩

theorem useful_read_pos (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (comp : C.Computes G) (v : Fin n) (hn : ∃ w, G.Adj v w) :
    0 < (pinReads C {v}).card := by
  apply Finset.card_pos.mpr
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h0
  have notread (i : Fin C.size) : ¬ (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) := by
    intro h
    have hi := (mem_pinReads C {v} i).mpr ⟨v, Finset.mem_singleton_self v, h⟩
    simp only [h0, Finset.notMem_empty] at hi
  obtain ⟨w, adj⟩ := hn
  have o := outVars_empty C G comp
  have same : C.eval (insert v {w}) = C.eval {w} := by
    have h := eval_across C id (insert v {w}) {w}
      (fun i => miss_insert (fun hv => notread i (Or.inl hv)))
      (fun i => miss_insert (fun hv => notread i (Or.inr hv)))
      (by
        simp only [id, o]
        constructor
        · rintro ⟨x, hx, _⟩
          exact (Finset.notMem_empty x hx).elim
        · rintro ⟨x, hx, _⟩
          exact (Finset.notMem_empty x hx).elim)
    exact h
  have yes : C.eval (insert v {w}) = true :=
    (comp _).mpr ⟨v, Finset.mem_insert_self v _, w,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self w), adj⟩
  have no : C.eval {w} ≠ true := by
    intro hw
    obtain ⟨a, ha, b, hb, ab⟩ := (comp _).mp hw
    have ea := Finset.mem_singleton.mp ha
    have eb := Finset.mem_singleton.mp hb
    exact G.loopless.irrefl w (by simpa only [ea, eb] using ab)
  exact no (same.symm.trans yes)

inductive Chain (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ → Finset (Fin n) → Prop
  | nil (A) : Chain G 0 A
  | cons {k A} (v : Fin n) (hv : v ∈ A) (hn : ∃ w ∈ A, G.Adj v w)
      (tail : Chain G k (A \ closedPin G {v})) : Chain G (k + 1) A

theorem chain_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k : ℕ} {A : Finset (Fin n)} (h : Chain G k A) : Lower (activeGraph G A) k := by
  induction h with
  | nil A =>
    intro C _ _
    exact Nat.zero_le C.size
  | cons v hv hn tail ih =>
    intro C wf comp
    obtain ⟨D, wd, dc, bound⟩ :=
      pin_active C G _ {v} wf comp (singleton_independent G v)
    have pos := useful_read_pos C _ comp v (by
      obtain ⟨w, hw, adj⟩ := hn
      exact ⟨w, hv, hw, adj⟩)
    have lower := ih D wd dc
    omega

end Pin

namespace Slot

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

variable {n : ℕ}

abbrev Side (C : AndCountCircuit n) := Fin C.size × Bool

def raw (C : AndCountCircuit n) (s : Side C) : Finset (Fin n) :=
  if s.2 then C.rightVars s.1 else C.leftVars s.1

def prev (C : AndCountCircuit n) (s : Side C) : Finset (Fin C.size) :=
  if s.2 then C.rightGates s.1 else C.leftGates s.1

def other (C : AndCountCircuit n) (s : Side C) : Side C := (s.1, !s.2)

def hits (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Side C) : Prop :=
  ∃ v ∈ raw C s, v ∈ U

def sval (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Side C) : Bool :=
  sideTrue U (raw C s) (prev C s) s.1 (C.gateVal U)

lemma ne_other (C : AndCountCircuit n) (s : Side C) : other C s ≠ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [other]

lemma hit_insert (C : AndCountCircuit n) (U : Finset (Fin n)) (v : Fin n) (s : Side C) :
    hits C (insert v U) s ↔ hits C U s ∨ v ∈ raw C s := by
  simp only [hits, Finset.mem_insert]
  constructor
  · rintro ⟨a, ha, eq | hm⟩
    · exact Or.inr (eq ▸ ha)
    · exact Or.inl ⟨a, ha, hm⟩
  · rintro (⟨a, ha, hm⟩ | hv)
    · exact ⟨a, ha, Or.inr hm⟩
    · exact ⟨v, hv, Or.inl rfl⟩

lemma hit_singleton (C : AndCountCircuit n) (v : Fin n) (s : Side C) :
    hits C {v} s ↔ v ∈ raw C s := by
  simp only [hits, Finset.mem_singleton, exists_eq_right]

lemma sval_congr (C : AndCountCircuit n) (U V : Finset (Fin n)) (s : Side C)
    (hh : hits C U s ↔ hits C V s)
    (hp : ∀ j : Fin C.size, j < s.1 → C.gateVal U j = C.gateVal V j) :
    sval C U s = sval C V s := by
  unfold sval
  rw [sideTrue_congr U (raw C s) (prev C s) s.1 _ _ hp]
  simp only [sideTrue, decide_eq_decide]
  exact or_congr hh Iff.rfl

lemma gate_eq_sval (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sval C U (i,false) && sval C U (i,true)) := by
  rw [gateVal_eq C U i]
  rfl

lemma gate_congr (C : AndCountCircuit n) (U V : Finset (Fin n)) (i : Fin C.size)
    (hL : hits C U (i,false) ↔ hits C V (i,false))
    (hR : hits C U (i,true) ↔ hits C V (i,true))
    (hp : ∀ j : Fin C.size, j < i → C.gateVal U j = C.gateVal V j) :
    C.gateVal U i = C.gateVal V i := by
  rw [gate_eq_sval C U i, gate_eq_sval C V i,
    sval_congr C U V (i,false) hL hp, sval_congr C U V (i,true) hR hp]

lemma eval_congr (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hout : C.outVars = ∅) (hv : ∀ i : Fin C.size, C.gateVal U i = C.gateVal V i) :
    C.eval U = C.eval V := by
  simp only [AndCountCircuit.eval, hout, Finset.notMem_empty, false_and, exists_false,
    false_or, hv]

lemma eval_eq_of_hits (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hout : C.outVars = ∅)
    (hh : ∀ s : Side C, hits C U s ↔ hits C V s) : C.eval U = C.eval V := by
  apply eval_congr C U V hout
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    exact gate_congr C U V i (hh (i,false)) (hh (i,true)) ih

lemma same_before_if (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t)) :
    ∀ i : Fin C.size, i < s.1 → C.gateVal U i = C.gateVal V i := by
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    intro hi
    have ne (b : Bool) : (i,b) ≠ s := fun e =>
      (ne_of_lt hi) (congrArg Prod.fst e)
    exact gate_congr C U V i (hH (i,false) (ne false)) (hH (i,true) (ne true))
      (fun j hj => ih j hj (hj.trans hi))

lemma pivot_gate (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hout : C.outVars = ∅)
    (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t))
    (hne : C.eval U ≠ C.eval V) : C.gateVal U s.1 ≠ C.gateVal V s.1 := by
  intro hEq
  apply hne
  apply eval_congr C U V hout
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    by_cases hi : i = s.1
    · simpa only [hi] using hEq
    · have ne (b : Bool) : (i,b) ≠ s := fun e => hi (congrArg Prod.fst e)
      exact gate_congr C U V i (hH (i,false) (ne false)) (hH (i,true) (ne true)) ih

lemma pivot_other (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hout : C.outVars = ∅)
    (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t))
    (hne : C.eval U ≠ C.eval V) : sval C U (other C s) = true := by
  have gates := pivot_gate C U V s hout hH hne
  have hop := sval_congr C U V (other C s) (hH _ (ne_other C s))
    (same_before_if C U V s hH)
  have f (h : sval C U (other C s) = false) : False := by
    have hv : sval C V (other C s) = false := hop.symm.trans h
    apply gates
    rcases s with ⟨i,b⟩
    cases b <;>
      simp only [other, Bool.not_false, Bool.not_true] at h hv <;>
      simp [gate_eq_sval, h, hv]
  cases h : sval C U (other C s)
  · exact (f h).elim
  · rfl

def positions (C : AndCountCircuit n) (v : Fin n) : Finset (Side C) :=
  Finset.univ.filter (fun s => v ∈ raw C s)

lemma mem_positions (C : AndCountCircuit n) (v : Fin n) (s : Side C) :
    s ∈ positions C v ↔ v ∈ raw C s := by simp [positions]

def readers (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)

lemma mem_readers (C : AndCountCircuit n) (v : Fin n) (i : Fin C.size) :
    i ∈ readers C v ↔ v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by simp [readers]

lemma positions_image (C : AndCountCircuit n) (v : Fin n) :
    (positions C v).image Prod.fst = readers C v := by
  ext i
  simp only [Finset.mem_image, mem_positions, mem_readers]
  constructor
  · rintro ⟨⟨j,b⟩, hj, rfl⟩
    cases b
    · exact Or.inl (by simpa [raw] using hj)
    · exact Or.inr (by simpa [raw] using hj)
  · rintro (hl | hr)
    · exact ⟨(i,false), by simpa [raw] using hl, rfl⟩
    · exact ⟨(i,true), by simpa [raw] using hr, rfl⟩

lemma positions_card (C : AndCountCircuit n) (v : Fin n)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (positions C v).card = (readers C v).card := by
  rw [← positions_image]
  symm
  apply Finset.card_image_of_injOn
  rintro ⟨i,b⟩ hb ⟨j,c⟩ hc (e : i = j)
  subst j
  rw [Finset.mem_coe, mem_positions] at hb hc
  cases b <;> cases c <;> simp only [raw, Bool.false_eq_true, ite_false, ite_true] at hb hc
  · rfl
  · exact (Finset.disjoint_left.mp (hd i) hb hc).elim
  · exact (Finset.disjoint_left.mp (hd i) hc hb).elim
  · rfl

lemma readers_ncard (C : AndCountCircuit n) (v : Fin n) :
    {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard =
      (readers C v).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  exact (mem_readers C v i).symm

lemma hit_unchanged_if_not (C : AndCountCircuit n) (U : Finset (Fin n))
    (v : Fin n) (s : Side C) (hn : v ∉ raw C s) :
    hits C U s ↔ hits C (insert v U) s := by simp [hit_insert, hn]

lemma hit_unchanged_if_already (C : AndCountCircuit n) (U : Finset (Fin n))
    (v : Fin n) (s : Side C) (hh : hits C U s) :
    hits C U s ↔ hits C (insert v U) s := by simp [hit_insert, hh]

lemma separation (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (U : Finset (Fin n)) (v w : Fin n) (hw : w ∈ U)
    (hind : ∀ a ∈ U, ∀ b ∈ U, ¬ G.Adj a b) (ha : G.Adj v w) :
    ∃ s : Side C, v ∈ raw C s ∧ ¬ hits C U s := by
  classical
  by_contra! bad
  have he := eval_eq_of_hits C U (insert v U) ho (fun s => by
    by_cases hs : v ∈ raw C s
    · exact hit_unchanged_if_already C U v s (bad s hs)
    · exact hit_unchanged_if_not C U v s hs)
  have hz : C.eval U = false := Bool.eq_false_iff.mpr (fun hy => by
    obtain ⟨a, ham, b, hbm, hab⟩ := (hc U).mp hy
    exact hind a ham b hbm hab)
  have hy : C.eval (insert v U) = true :=
    (hc _).mpr ⟨v, by simp, w, Finset.mem_insert_of_mem hw, ha⟩
  simpa [hz, hy] using he

lemma some_position (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) {v w : Fin n} (h : G.Adj v w) :
    (positions C v).Nonempty := by
  obtain ⟨s, hm, _⟩ := separation G C hc ho {w} v w (by simp) (by simp) h
  exact ⟨s, (mem_positions C v s).mpr hm⟩

lemma unique_position_neighbor (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    {v w : Fin n} (h : G.Adj v w) (s : Side C) (just : positions C v = {s}) :
    w ∈ raw C (other C s) := by
  have hz : C.eval {w} = false := Bool.eq_false_iff.mpr (fun hy => by
    obtain ⟨a, ham, b, hbm, hab⟩ := (hc {w}).mp hy
    simp only [Finset.mem_singleton] at ham hbm
    subst a
    subst b
    exact G.loopless.irrefl w hab)
  have hy : C.eval (insert v {w}) = true :=
    (hc _).mpr ⟨v, by simp, w, by simp, h⟩
  have hH (t : Side C) (ht : t ≠ s) : hits C {w} t ↔ hits C (insert v {w}) t := by
    apply hit_unchanged_if_not
    intro hmem
    have hh := (mem_positions C v t).mpr hmem
    rw [just, Finset.mem_singleton] at hh
    exact ht hh
  have hp := pivot_other C {w} (insert v {w}) s ho hH (by simp [hz,hy])
  change sideTrue {w} (raw C (other C s)) (prev C (other C s))
    (other C s).1 (C.gateVal {w}) = true at hp
  simp only [sideTrue, decide_eq_true_eq, hs, Bool.false_eq_true, and_false,
    exists_false, or_false, Finset.mem_singleton, exists_eq_right] at hp
  exact hp

lemma uniform_singletons (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    (color : Fin n → Bool)
    (cross : ∀ {v w}, G.Adj v w → color v ≠ color w)
    {v w : Fin n} (col : color v = color w)
    (nbv : ∃ u, G.Adj v u) (nbw : ∃ u, G.Adj w u)
    (diff : ∃ u, (G.Adj v u ∧ ¬ G.Adj w u) ∨ (G.Adj w u ∧ ¬ G.Adj v u))
    (s t : Side C) (hv : positions C v = {s}) (hw : positions C w = {t}) :
    s.1 ≠ t.1 := by
  intro hgate
  have ne : s ≠ t := by
    intro hst
    obtain ⟨u, hd | hd⟩ := diff
    · have hz : C.eval {w,u} = false := Bool.eq_false_iff.mpr (fun hy => by
        obtain ⟨a, ha, b, hb, hab⟩ := (hc _).mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.loopless.irrefl _ hab
        · exact hd.2 hab
        · exact hd.2 hab.symm
        · exact G.loopless.irrefl _ hab)
      have hy : C.eval {v,u} = true := (hc _).mpr ⟨v, by simp, u, by simp, hd.1⟩
      have hh (r : Side C) : v ∈ raw C r ↔ w ∈ raw C r := by
        rw [← mem_positions, ← mem_positions, hv, hw, hst]
      have eq := eval_eq_of_hits C {v,u} {w,u} ho (fun r => by
        rw [hit_insert, hit_insert, hh])
      simpa [hz,hy] using eq
    · have hz : C.eval {v,u} = false := Bool.eq_false_iff.mpr (fun hy => by
        obtain ⟨a, ha, b, hb, hab⟩ := (hc _).mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.loopless.irrefl _ hab
        · exact hd.2 hab
        · exact hd.2 hab.symm
        · exact G.loopless.irrefl _ hab)
      have hy : C.eval {w,u} = true := (hc _).mpr ⟨w, by simp, u, by simp, hd.1⟩
      have hh (r : Side C) : v ∈ raw C r ↔ w ∈ raw C r := by
        rw [← mem_positions, ← mem_positions, hv, hw, hst]
      have eq := eval_eq_of_hits C {v,u} {w,u} ho (fun r => by
        rw [hit_insert, hit_insert, hh])
      simpa [hz,hy] using eq
  have et : t = other C s := by
    rcases s with ⟨i,b⟩
    rcases t with ⟨j,d⟩
    change i = j at hgate
    subst j
    cases b <;> cases d <;> first | rfl | exact (ne rfl).elim
  have es : s = other C t := by
    rw [et]
    rcases s with ⟨i,b⟩
    cases b <;> rfl
  obtain ⟨a, ha⟩ := nbv
  obtain ⟨b, hb⟩ := nbw
  have aT : a ∈ raw C t := by rw [et]; exact unique_position_neighbor G C hc ho hs ha s hv
  have bS : b ∈ raw C s := by rw [es]; exact unique_position_neighbor G C hc ho hs hb t hw
  have sameAB : color a = color b := by
    calc
      color a = !(color v) := Bool.eq_not_of_ne (cross ha).symm
      _ = !(color w) := congrArg Bool.not col
      _ = color b := (Bool.eq_not_of_ne (cross hb).symm).symm
  have hind : ∀ x ∈ ({a,b} : Finset (Fin n)), ∀ y ∈ ({a,b} : Finset (Fin n)), ¬ G.Adj x y := by
    intro x hx y hy h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hxC : color x = color a := hx.elim (fun e => congrArg color e)
      (fun e => (congrArg color e).trans sameAB.symm)
    have hyC : color y = color a := hy.elim (fun e => congrArg color e)
      (fun e => (congrArg color e).trans sameAB.symm)
    exact cross h (hxC.trans hyC.symm)
  obtain ⟨r, hr, hnone⟩ := separation G C hc ho {a,b} v a (by simp) hind ha
  have eq : r = s := by
    have h := (mem_positions C v r).mpr hr
    simpa only [hv, Finset.mem_singleton] using h
  rw [eq] at hnone
  exact hnone ⟨b, bS, by simp⟩

lemma uniform_one_count (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (color : Fin n → Bool)
    (cross : ∀ {v w}, G.Adj v w → color v ≠ color w)
    (T : Finset (Fin n)) (b : Bool) (col : ∀ v ∈ T, color v = b)
    (nb : ∀ v ∈ T, ∃ w, G.Adj v w)
    (diff : ∀ v ∈ T, ∀ w ∈ T, v ≠ w →
      ∃ u, (G.Adj v u ∧ ¬G.Adj w u) ∨ (G.Adj w u ∧ ¬G.Adj v u))
    (one : ∀ v ∈ T, (readers C v).card = 1) :
    T.card ≤ C.size := by
  classical
  have pick (v : {v // v ∈ T}) : ∃ s, positions C v.1 = {s} := by
    apply Finset.card_eq_one.mp
    rw [positions_card C v.1 hd]
    exact one v.1 v.2
  let index (v : {v // v ∈ T}) : Fin C.size := (Classical.choose (pick v)).1
  have inj : Function.Injective index := by
    intro v w hix
    apply Subtype.ext
    by_contra h
    exact uniform_singletons G C hc ho hs color cross
      ((col v.1 v.2).trans (col w.1 w.2).symm) (nb v.1 v.2) (nb w.1 w.2)
      (diff v.1 v.2 w.1 w.2 h) _ _ (Classical.choose_spec (pick v))
      (Classical.choose_spec (pick w)) hix
  simpa using (Fintype.card_le_of_injective index inj)

end Slot

namespace Slot

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ}

structure Environment (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) where
  active : Finset (Fin n)
  color : Fin n → Bool
  computes : C.Computes G
  out : C.outVars = ∅
  clean : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false
  disjoint : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)
  used : ∀ s : Side C, raw C s ⊆ active
  cross : ∀ {v w}, G.Adj v w → color v ≠ color w
  someNeighbor : ∀ v ∈ active, ∃ t, G.Adj v t
  avoidTwo : ∀ v ∈ active, ∀ a b : Fin n, a ≠ v → b ≠ v →
    color a = color v → color b = color v →
    ∃ t, G.Adj v t ∧ ¬ G.Adj a t ∧ ¬ G.Adj b t
  uniqueCommon : ∀ {a b c d}, a ≠ b → c ≠ d →
    G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → False
  twice : ∀ v ∈ active, (positions C v).card ≤ 2

variable {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
variable (K : Environment G C)

def pure (v : Fin n) (s : Side C) : Prop :=
  ∀ w ∈ raw C s, K.color w = K.color v

def partPrivate (v : Fin n) (s : Side C) : Prop :=
  ∀ w ∈ raw C s, K.color w = K.color v → w = v

def universal (C : AndCountCircuit n) (v : Fin n) : Prop :=
  ∃ s : Side C, raw C s = {v}

abbrev Active := {v : Fin n // v ∈ K.active}

lemma independent_monoColor (J : Finset (Fin n)) (b : Bool)
    (same : ∀ v ∈ J, K.color v = b) :
    ∀ v ∈ J, ∀ w ∈ J, ¬ G.Adj v w := by
  intro v hv w hw ha
  exact K.cross ha ((same v hv).trans (same w hw).symm)

lemma independent_bipart (B T : Finset (Fin n)) (b : Bool)
    (sameB : ∀ v ∈ B, K.color v = b)
    (sameT : ∀ v ∈ T, K.color v ≠ b)
    (notAdj : ∀ v ∈ B, ∀ w ∈ T, ¬ G.Adj v w) :
    ∀ v ∈ B ∪ T, ∀ w ∈ B ∪ T, ¬ G.Adj v w := by
  intro v hv w hw hadj
  rcases Finset.mem_union.mp hv with hv | hv <;> rcases Finset.mem_union.mp hw with hw | hw
  · exact K.cross hadj ((sameB v hv).trans (sameB w hw).symm)
  · exact notAdj v hv w hw hadj
  · exact notAdj w hw v hv hadj.symm
  · exact K.cross hadj ((Bool.eq_not_of_ne (sameT v hv)).trans (Bool.eq_not_of_ne (sameT w hw)).symm)

lemma pure_exists (v : Fin n) (ha : v ∈ K.active) :
    ∃ s : Side C, v ∈ raw C s ∧ pure K v s := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun w => K.color w ≠ K.color v)
  obtain ⟨t, ht⟩ := K.someNeighbor v ha
  have tT : t ∈ T := by simpa [T] using (K.cross ht).symm
  have opp (w : Fin n) (hw : w ∈ T) : K.color w ≠ K.color v := by simpa [T] using hw
  have hind : ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b := by
    simpa only [Finset.empty_union] using
      (independent_bipart K ∅ T (K.color v) (by simp) opp (by simp))
  obtain ⟨s, hv, noHits⟩ := separation G C K.computes K.out T v t tT hind ht
  refine ⟨s, hv, ?_⟩
  intro w hw
  by_contra hn
  exact noHits ⟨w, hw, by simp [T, hn]⟩

lemma card_le_two_cover {α : Type*} [DecidableEq α] (F : Finset α)
    (hne : F.Nonempty) (hc : F.card ≤ 2) :
    ∃ a ∈ F, ∃ b ∈ F, F ⊆ {a,b} := by
  have hp := Finset.card_pos.mpr hne
  have cases : F.card = 1 ∨ F.card = 2 := by omega
  rcases cases with h | h
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, by simp, a, by simp, by simp⟩
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, by simp, b, by simp, by simp⟩

lemma partPrivate_exists (v : Fin n) (ha : v ∈ K.active) :
    ∃ s : Side C, v ∈ raw C s ∧ partPrivate K v s := by
  classical
  by_contra hn
  have alt (s : Side C) (hs : s ∈ positions C v) :
      ∃ w ∈ raw C s, K.color w = K.color v ∧ w ≠ v := by
    by_contra! h
    exact hn ⟨s, (mem_positions C v s).mp hs, h⟩
  obtain ⟨w, hw⟩ := K.someNeighbor v ha
  obtain ⟨a, ha', b, hb', cov⟩ := card_le_two_cover (positions C v)
    (some_position G C K.computes K.out hw) (K.twice v ha)
  obtain ⟨x, hx, xc, xn⟩ := alt a ha'
  obtain ⟨y, hy, yc, yn⟩ := alt b hb'
  obtain ⟨t, ht, ntX, ntY⟩ := K.avoidTwo v ha x y xn yn xc yc
  let I : Finset (Fin n) := {x,y} ∪ {t}
  have sameP : ∀ v' ∈ ({x,y} : Finset (Fin n)), K.color v' = K.color v := by
    intro v' hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl <;> assumption
  have sameT : ∀ v' ∈ ({t} : Finset (Fin n)), K.color v' ≠ K.color v := by
    intro v' hv'
    have e : v' = t := by simpa using hv'
    subst v'
    exact (K.cross ht).symm
  have crossF : ∀ v' ∈ ({x,y} : Finset (Fin n)), ∀ w' ∈ ({t} : Finset (Fin n)),
      ¬ G.Adj v' w' := by
    intro v' hv' w' hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv' hw'
    rcases hv' with rfl | rfl <;> subst w' <;> assumption
  obtain ⟨s, hvs, none⟩ := separation G C K.computes K.out I v t (by simp [I])
    (independent_bipart K {x,y} {t} _ sameP sameT crossF) ht
  have hs := cov ((mem_positions C v s).mpr hvs)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact none ⟨x, hx, by simp [I]⟩
  · exact none ⟨y, hy, by simp [I]⟩

noncomputable def pureSlot (v : Active K) : Side C :=
  Classical.choose (pure_exists K v.1 v.2)

noncomputable def privSlot (v : Active K) : Side C :=
  Classical.choose (partPrivate_exists K v.1 v.2)

lemma pureSlot_spec (v : Active K) :
    v.1 ∈ raw C (pureSlot K v) ∧ pure K v.1 (pureSlot K v) :=
  Classical.choose_spec (pure_exists K v.1 v.2)

lemma privSlot_spec (v : Active K) :
    v.1 ∈ raw C (privSlot K v) ∧ partPrivate K v.1 (privSlot K v) :=
  Classical.choose_spec (partPrivate_exists K v.1 v.2)

lemma coincident_universal (v : Active K) (h : pureSlot K v = privSlot K v) :
    universal C v.1 := by
  refine ⟨pureSlot K v, Finset.eq_singleton_iff_unique_mem.mpr ⟨(pureSlot_spec K v).1, ?_⟩⟩
  intro w hw
  apply (privSlot_spec K v).2 w (h ▸ hw)
  exact (pureSlot_spec K v).2 w hw

lemma slots_two_exact (v : Active K) (hu : ¬ universal C v.1) :
    positions C v.1 = {pureSlot K v, privSlot K v} := by
  have ne : pureSlot K v ≠ privSlot K v := fun e => hu (coincident_universal K v e)
  have incl : {pureSlot K v, privSlot K v} ⊆ positions C v.1 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact (mem_positions C v.1 _).mpr (pureSlot_spec K v).1
    · exact (mem_positions C v.1 _).mpr (privSlot_spec K v).1
  apply (Finset.eq_of_subset_of_card_le incl _).symm
  rw [Finset.card_insert_of_notMem (by simpa using ne), Finset.card_singleton]
  exact K.twice v.1 v.2

lemma pure_choiceAlt (v : Active K) (hu : ¬ universal C v.1) :
    ∃ a ∈ raw C (pureSlot K v), a ≠ v.1 := by
  by_contra! bad
  apply hu
  exact ⟨_, Finset.eq_singleton_iff_unique_mem.mpr ⟨(pureSlot_spec K v).1, bad⟩⟩

lemma mixed_choiceAlt (v : Active K) (hu : ¬ universal C v.1) :
    ∃ a ∈ raw C (privSlot K v), K.color a ≠ K.color v.1 := by
  by_contra! bad
  apply hu
  refine ⟨_, Finset.eq_singleton_iff_unique_mem.mpr ⟨(privSlot_spec K v).1, ?_⟩⟩
  intro w hw
  exact (privSlot_spec K v).2 w hw (bad w hw)

lemma only_pure_slot (v : Active K) (hu : ¬ universal C v.1)
    (s : Side C) (hm : v.1 ∈ raw C s) (hp : pure K v.1 s) : s = pureSlot K v := by
  have hs := (mem_positions C v.1 s).mpr hm
  rw [slots_two_exact K v hu, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | e
  · exact h
  · obtain ⟨a, ha, hn⟩ := mixed_choiceAlt K v hu
    exact (hn (hp a (e.symm ▸ ha))).elim

lemma pure_mixed_incident (v : Active K) (a b : Fin n)
    (aMake : a ∈ raw C (privSlot K v)) (aOpp : K.color a ≠ K.color v.1)
    (bMake : b ∈ raw C (pureSlot K v)) (bNe : b ≠ v.1)
    (hu : ¬ universal C v.1) : G.Adj a b := by
  by_contra bad
  have bSame := (pureSlot_spec K v).2 b bMake
  obtain ⟨t, ht, noB, _⟩ := K.avoidTwo v.1 v.2 b b bNe bNe bSame bSame
  let I : Finset (Fin n) := {b} ∪ {a,t}
  have sameB : ∀ w ∈ ({b} : Finset (Fin n)), K.color w = K.color v.1 := by
    intro w hw
    simpa [(Finset.mem_singleton.mp hw)] using bSame
  have sameT : ∀ w ∈ ({a,t} : Finset (Fin n)), K.color w ≠ K.color v.1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact aOpp
    · exact (K.cross ht).symm
  have notAdj : ∀ w ∈ ({b} : Finset (Fin n)), ∀ u ∈ ({a,t} : Finset (Fin n)), ¬ G.Adj w u := by
    intro w hw u hu'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hu'
    subst w
    rcases hu' with rfl | rfl
    · exact fun h => bad h.symm
    · exact noB
  obtain ⟨s, hm, hnone⟩ := separation G C K.computes K.out I v.1 t (by simp [I])
    (independent_bipart K {b} {a,t} _ sameB sameT notAdj) ht
  have hs := (mem_positions C v.1 s).mpr hm
  rw [slots_two_exact K v hu, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h
  · apply hnone
    exact ⟨b,h.symm ▸ bMake,by simp [I]⟩
  · apply hnone
    exact ⟨a,h.symm ▸ aMake,by simp [I]⟩

lemma mixed_inj_same (v w : Active K) (same : K.color v.1 = K.color w.1)
    (e : privSlot K v = privSlot K w) : v = w := by
  apply Subtype.ext
  have hv := (privSlot_spec K v).2 w.1 (e.symm ▸ (privSlot_spec K w).1) same.symm
  exact hv.symm

lemma pos_no_three (v : Active K) (s t u : Side C)
    (sv : v.1 ∈ raw C s) (tv : v.1 ∈ raw C t) (uv : v.1 ∈ raw C u)
    (hST : s ≠ t) (hSU : s ≠ u) (hTU : t ≠ u) : False := by
  have hIncl : ({s,t,u} : Finset (Side C)) ⊆ positions C v.1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    apply (mem_positions C v.1 q).mpr
    rcases hq with rfl | rfl | rfl <;> assumption
  have big := Finset.card_le_card hIncl
  have small := K.twice v.1 v.2
  rw [Finset.card_insert_of_notMem (by simp [hST,hSU]),
    Finset.card_insert_of_notMem (by simp [hTU]), Finset.card_singleton] at big
  omega

lemma pure_pair_card (v w : Active K) (different : v ≠ w)
    (vn : ¬ universal C v.1) (wn : ¬ universal C w.1)
    (e : pureSlot K v = pureSlot K w) :
    (raw C (pureSlot K v)).card ≤ 3 := by
  classical
  have vne : v.1 ≠ w.1 := fun h => different (Subtype.ext h)
  have wRaw : w.1 ∈ raw C (pureSlot K v) := e.symm ▸ (pureSlot_spec K w).1
  have col : K.color v.1 = K.color w.1 := ((pureSlot_spec K v).2 w.1 wRaw).symm
  have mDiff : privSlot K v ≠ privSlot K w := fun h => different (mixed_inj_same K v w col h)
  obtain ⟨a, aRaw, aOpp⟩ := mixed_choiceAlt K v vn
  obtain ⟨b, bRaw, bOpp⟩ := mixed_choiceAlt K w wn
  have abNe : a ≠ b := by
    intro eq
    subst b
    let q : Active K := ⟨a, K.used _ aRaw⟩
    have pNeV : pureSlot K q ≠ privSlot K v := by
      intro eq
      have hv : v.1 ∈ raw C (pureSlot K q) := eq.symm ▸ (privSlot_spec K v).1
      exact aOpp ((pureSlot_spec K q).2 v.1 hv).symm
    have pNeW : pureSlot K q ≠ privSlot K w := by
      intro eq
      have hw : w.1 ∈ raw C (pureSlot K q) := eq.symm ▸ (privSlot_spec K w).1
      exact bOpp ((pureSlot_spec K q).2 w.1 hw).symm
    exact pos_no_three K q _ _ _ aRaw bRaw (pureSlot_spec K q).1
      mDiff pNeV.symm pNeW.symm
  have common (z : Fin n) (hz : z ∈ raw C (pureSlot K v)) (zv : z ≠ v.1) (zw : z ≠ w.1) :
      G.Adj a z ∧ G.Adj b z :=
    ⟨pure_mixed_incident K v a z aRaw aOpp hz zv vn,
      pure_mixed_incident K w b z bRaw bOpp (e ▸ hz) zw wn⟩
  let extra := (raw C (pureSlot K v)).filter (fun z => z ≠ v.1 ∧ z ≠ w.1)
  have cap : extra.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz z' hz'
    obtain ⟨hzR, hzV, hzW⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz'R, hz'V, hz'W⟩ := Finset.mem_filter.mp hz'
    obtain ⟨az,bz⟩ := common z hzR hzV hzW
    obtain ⟨az',bz'⟩ := common z' hz'R hz'V hz'W
    by_contra nd
    exact K.uniqueCommon abNe nd az bz az' bz'
  have subset : raw C (pureSlot K v) ⊆ insert v.1 (insert w.1 extra) := by
    intro z hz
    by_cases ev : z = v.1
    · simp [ev]
    by_cases ew : z = w.1
    · simp [ew]
    simp [extra, hz, ev, ew]
  have h0 := Finset.card_le_card subset
  have h1 := Finset.card_insert_le v.1 (insert w.1 extra)
  have h2 := Finset.card_insert_le w.1 extra
  omega

lemma some_extra_unless_double (v w : Active K)
    (vn : ¬ universal C v.1) (wn : ¬ universal C w.1) (vne : v.1 ≠ w.1)
    (same : K.color v.1 = K.color w.1)
    (notdouble : ¬ (pureSlot K v = pureSlot K w ∧ raw C (pureSlot K v) = {v.1,w.1})) :
    ∃ b ∈ raw C (pureSlot K v), b ≠ v.1 ∧ b ≠ w.1 := by
  by_contra! bad
  obtain ⟨b,hb,nb⟩ := pure_choiceAlt K v vn
  have eb := bad b hb nb
  have bw : w.1 ∈ raw C (pureSlot K v) := eb ▸ hb
  have e : pureSlot K v = pureSlot K w := by
    apply only_pure_slot K w wn _ bw
    intro u hu
    exact ((pureSlot_spec K v).2 u hu).trans same
  apply notdouble
  refine ⟨e, ?_⟩
  ext u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hu
    by_cases eu : u = v.1
    · exact Or.inl eu
    · exact Or.inr (bad u hu eu)
  · rintro (rfl | rfl)
    · exact (pureSlot_spec K v).1
    · exact bw

lemma critical_if_pure_hit (v : Active K) (vn : ¬ universal C v.1)
    (I : Finset (Fin n)) (hI : hits C I (pureSlot K v)) (s : Side C)
    (ne : s ≠ privSlot K v) :
    hits C I s ↔ hits C (insert v.1 I) s := by
  by_cases hvs : v.1 ∈ raw C s
  · have mem := (mem_positions C v.1 s).mpr hvs
    rw [slots_two_exact K v vn, Finset.mem_insert, Finset.mem_singleton] at mem
    rcases mem with e | e
    · exact hit_unchanged_if_already C I v.1 s (e.symm ▸ hI)
    · exact (ne e).elim
  · exact hit_unchanged_if_not C I v.1 s hvs

lemma gate_insert_mono (C : AndCountCircuit n) (I : Finset (Fin n)) (v : Fin n) :
    ∀ i : Fin C.size, C.gateVal I i = true → C.gateVal (insert v I) i = true := by
  have fuel : ∀ (d : ℕ) (j : Fin C.size),
      C.gateValFuel I d j = true → C.gateValFuel (insert v I) d j = true := by
    intro d
    induction d with
    | zero => simp [gateValFuel]
    | succ e ih =>
      intro j hj
      simp only [gateValFuel, Bool.and_eq_true, sideTrue, decide_eq_true_eq] at hj ⊢
      constructor
      · rcases hj.1 with ⟨u,hu,ui⟩ | ⟨q,hq,lt,h⟩
        · exact Or.inl ⟨u,hu,Finset.mem_insert_of_mem ui⟩
        · exact Or.inr ⟨q,hq,lt,ih q h⟩
      · rcases hj.2 with ⟨u,hu,ui⟩ | ⟨q,hq,lt,h⟩
        · exact Or.inl ⟨u,hu,Finset.mem_insert_of_mem ui⟩
        · exact Or.inr ⟨q,hq,lt,ih q h⟩
  exact fuel C.size

lemma sides_eq_of_gate_eq {C : AndCountCircuit n} {s t : Side C}
    (same : s.1 = t.1) (different : s ≠ t) : t = other C s := by
  rcases s with ⟨i,b⟩
  rcases t with ⟨j,c⟩
  change i = j at same
  subst j
  cases b <;> cases c <;> first | rfl | exact (different rfl).elim

lemma mixed_double_gate (v w : Active K)
    (vn : ¬ universal C v.1) (wn : ¬ universal C w.1) (vne : v.1 ≠ w.1)
    (same : K.color v.1 = K.color w.1) (g : (privSlot K v).1 = (privSlot K w).1) :
    pureSlot K v = pureSlot K w ∧ raw C (pureSlot K v) = {v.1,w.1} := by
  classical
  by_contra h
  have hs : ¬ (pureSlot K w = pureSlot K v ∧ raw C (pureSlot K w) = {w.1,v.1}) := by
    intro a
    have h2 : ({w.1,v.1} : Finset (Fin n)) = {v.1,w.1} := by ext z; simp [or_comm]
    exact h ⟨a.1.symm,a.1.symm ▸ a.2.trans h2⟩
  obtain ⟨b,hb,bv,bw⟩ := some_extra_unless_double K v w vn wn vne same h
  obtain ⟨c,hc,cw,cv⟩ := some_extra_unless_double K w v wn vn vne.symm same.symm hs
  have bc := (pureSlot_spec K v).2 b hb
  have cc := (pureSlot_spec K w).2 c hc
  obtain ⟨t,ht,bt,ct⟩ := K.avoidTwo v.1 v.2 b c bv cv bc (cc.trans same.symm)
  obtain ⟨u,hu,bu,cu⟩ := K.avoidTwo w.1 w.2 b c bw cw (bc.trans same) cc
  let I : Finset (Fin n) := {b,c} ∪ {t,u}
  have bp : ∀ z ∈ ({b,c} : Finset (Fin n)), K.color z = K.color v.1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact bc
    · exact cc.trans same.symm
  have tp : ∀ z ∈ ({t,u} : Finset (Fin n)), K.color z ≠ K.color v.1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (K.cross ht).symm
    · simpa only [same] using (K.cross hu).symm
  have np : ∀ z ∈ ({b,c} : Finset (Fin n)), ∀ a ∈ ({t,u} : Finset (Fin n)), ¬G.Adj z a := by
    intro z hz a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ha
    rcases hz with rfl | rfl <;> rcases ha with rfl | rfl <;> assumption
  have ind := independent_bipart K {b,c} {t,u} _ bp tp np
  have eval0 : C.eval I = false := Bool.eq_false_iff.mpr (fun z => by
    obtain ⟨i,hi,j,hj,edge⟩ := (K.computes _).mp z
    exact ind i hi j hj edge)
  have eval1 : C.eval (insert v.1 I) = true :=
    (K.computes _).mpr ⟨v.1,by simp,t,by simp [I],ht⟩
  have eval2 : C.eval (insert w.1 I) = true :=
    (K.computes _).mpr ⟨w.1,by simp,u,by simp [I],hu⟩
  have hpV : hits C I (pureSlot K v) := ⟨b,hb,by simp [I]⟩
  have hpW : hits C I (pureSlot K w) := ⟨c,hc,by simp [I]⟩
  have eqV := critical_if_pure_hit K v vn I hpV
  have eqW := critical_if_pure_hit K w wn I hpW
  have otherV := pivot_other C I (insert v.1 I) (privSlot K v) K.out eqV (by simp [eval0,eval1])
  have otherW := pivot_other C I (insert w.1 I) (privSlot K w) K.out eqW (by simp [eval0,eval2])
  have neq : privSlot K v ≠ privSlot K w := by
    intro e
    exact vne (congrArg Subtype.val (mixed_inj_same K v w same e))
  have oppW := sides_eq_of_gate_eq g neq
  have oppV := sides_eq_of_gate_eq g.symm neq.symm
  have vtrue : sval C I (privSlot K v) = true := by rw [oppV]; exact otherW
  have wtrue : sval C I (privSlot K w) = true := by rw [oppW]; exact otherV
  have gtrue : C.gateVal I (privSlot K v).1 = true := by
    rw [oppW] at wtrue
    have temp : ∀ s : Side C, sval C I s = true → sval C I (other C s) = true →
        C.gateVal I s.1 = true := by
      rintro ⟨i,d⟩ s1 s2
      cases d <;> simp [other,gate_eq_sval] at s1 s2 ⊢ <;> simp [s1,s2]
    exact temp _ vtrue wtrue
  have gc := pivot_gate C I (insert v.1 I) (privSlot K v) K.out eqV (by simp [eval0,eval1])
  exact gc (gtrue.trans (gate_insert_mono C I v.1 _ gtrue).symm)

end Slot

namespace Slot

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open scoped BigOperators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
variable (K : Environment G C)

noncomputable def colorPool (b : Bool) : Finset (Active K) :=
  Finset.univ.filter (fun v => K.color v.1 = b)

noncomputable def nonUni (b : Bool) : Finset (Active K) := by
  classical
  exact (colorPool K b).filter (fun v => ¬ universal C v.1)

noncomputable def uniColor (b : Bool) : Finset (Active K) := by
  classical
  exact (colorPool K b).filter (fun v => universal C v.1)

noncomputable def univPool : Finset (Active K) := by
  classical
  exact Finset.univ.filter (fun v => universal C v.1)

lemma nonUni_spec (b : Bool) (v : Active K) :
    v ∈ nonUni K b ↔ K.color v.1 = b ∧ ¬ universal C v.1 := by
  classical
  simp [nonUni, colorPool]

lemma univPool_spec (v : Active K) :
    v ∈ univPool K ↔ universal C v.1 := by
  classical
  simp [univPool]

noncomputable def singleSlot (v : Active K) : Side C := by
  classical
  exact if h : universal C v.1 then Classical.choose h else pureSlot K v

lemma singleSpec (v : Active K) (h : universal C v.1) :
    raw C (singleSlot K v) = {v.1} := by
  unfold singleSlot
  rw [dif_pos h]
  exact Classical.choose_spec h

noncomputable def singlePool : Finset (Side C) :=
  (univPool K).image (singleSlot K)

noncomputable def purePool (b : Bool) : Finset (Side C) :=
  (nonUni K b).image (pureSlot K)

noncomputable def mixedPool (b : Bool) : Finset (Side C) :=
  (nonUni K b).image (privSlot K)

noncomputable def mixedAll : Finset (Side C) := mixedPool K false ∪ mixedPool K true

noncomputable def doubles (b : Bool) : Finset (Side C) :=
  (purePool K b).filter (fun p => (raw C p).card = 2)

noncomputable def fiber (b : Bool) (s : Side C) : Finset (Active K) :=
  (nonUni K b).filter (fun v => pureSlot K v = s)

lemma nonUni_count (b : Bool) :
    (nonUni K b).card + (uniColor K b).card =
      (colorPool K b).card := by
  classical
  have eq : nonUni K b ∪ uniColor K b = colorPool K b := by
    ext v
    by_cases h : universal C v.1 <;> simp [nonUni,uniColor,h]
  have ds : Disjoint (nonUni K b) (uniColor K b) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
  rw [← eq,Finset.card_union_of_disjoint ds]

lemma uni_and_two_colors :
    (univPool K).card + (nonUni K false).card + (nonUni K true).card =
      (colorPool K false).card + (colorPool K true).card := by
  classical
  let a := uniColor K false
  let b := uniColor K true
  have d : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro v av bv
    simp [a, b, uniColor, colorPool] at av bv
    rw [av.1] at bv
    simp at bv
  have same : a ∪ b = univPool K := by
    ext v
    simp only [a, b, uniColor, colorPool, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, univPool_spec]
    cases h : K.color v.1 <;> simp [h]
  have ua : (univPool K).card = a.card + b.card := by rw [← same, Finset.card_union_of_disjoint d]
  have aC := nonUni_count K false
  have bC := nonUni_count K true
  change (nonUni K false).card + a.card = _ at aC
  change (nonUni K true).card + b.card = _ at bC
  omega

lemma singles_size : (singlePool K).card = (univPool K).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw h
  have ev := singleSpec K v ((univPool_spec K v).mp hv)
  have ew := singleSpec K w ((univPool_spec K w).mp hw)
  apply Subtype.ext
  rw [h, ew] at ev
  simpa using ev.symm

lemma mixed_size (b : Bool) : (mixedPool K b).card = (nonUni K b).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw h
  exact mixed_inj_same K v w (((nonUni_spec K b v).mp hv).1.trans
    ((nonUni_spec K b w).mp hw).1.symm) h

lemma pure_inhabited (b : Bool) (s : Side C) (hs : s ∈ purePool K b) :
    (fiber K b s).Nonempty := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hs
  exact ⟨v,by simp [fiber,hv]⟩

lemma fiber_embed (b : Bool) (s : Side C) :
    (fiber K b s).card ≤ (raw C s).card := by
  let f : Active K → Fin n := Subtype.val
  have inj : Function.Injective f := fun a b eq => Subtype.ext eq
  rw [← Finset.card_image_of_injective (fiber K b s) inj]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  have e := (Finset.mem_filter.mp hx).2
  exact e ▸ (pureSlot_spec K x).1

lemma fiber_card (b : Bool) (s : Side C) :
    (fiber K b s).card ≤ 3 := by
  classical
  by_contra! big
  have nonempty : (fiber K b s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := nonempty
  have diff : ((fiber K b s).erase v).Nonempty := by
    have := Finset.card_erase_add_one hv
    exact Finset.card_pos.mp (by omega)
  obtain ⟨w,hw'⟩ := diff
  obtain ⟨wnv,hw⟩ := Finset.mem_erase.mp hw'
  obtain ⟨vNon,vSlot⟩ := Finset.mem_filter.mp hv
  obtain ⟨wNon,wSlot⟩ := Finset.mem_filter.mp hw
  have vNU := ((nonUni_spec K b v).mp vNon).2
  have wNU := ((nonUni_spec K b w).mp wNon).2
  have h := pure_pair_card K v w wnv.symm vNU wNU (vSlot.trans wSlot.symm)
  rw [vSlot] at h
  exact (not_le_of_gt big) ((fiber_embed K b s).trans h)

lemma fibers_sum (b : Bool) :
    ∑ s ∈ purePool K b, (fiber K b s).card = (nonUni K b).card := by
  rw [show (∑ s ∈ purePool K b, (fiber K b s).card) =
      ((nonUni K b).filter (fun v => pureSlot K v ∈ purePool K b)).card by
    exact Finset.sum_card_fiberwise_eq_card_filter _ _ _]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact Finset.mem_image.mpr ⟨v,hv,rfl⟩

lemma pure_deficiency (b : Bool) :
    (nonUni K b).card + (doubles K b).card ≤ 3 * (purePool K b).card := by
  classical
  have ac (s : Side C) : (fiber K b s).card + (if (raw C s).card = 2 then 1 else 0) ≤ 3 := by
    split_ifs with h
    · have lim := fiber_embed K b s
      omega
    · have lim := fiber_card K b s
      omega
  have add : ∑ s ∈ purePool K b, (if (raw C s).card = 2 then (1:ℕ) else 0) =
      (doubles K b).card := by simp [doubles, Finset.sum_filter]
  rw [← fibers_sum K b, ← add, ← Finset.sum_add_distrib]
  apply (Finset.sum_le_sum (fun s _ => ac s)).trans
  simp [Nat.mul_comm]

lemma singleton_disjoint_p (b : Bool) : Disjoint (singlePool K) (purePool K b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hU hP
  obtain ⟨u,hu,eu⟩ := Finset.mem_image.mp hU
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hP
  have hu' := (univPool_spec K u).mp hu
  have hv' := ((nonUni_spec K b v).mp hv).2
  have a := singleSpec K u hu'
  have vert := (pureSlot_spec K v).1
  rw [eu] at a
  rw [ev,a,Finset.mem_singleton] at vert
  exact hv' ⟨s,by simpa only [vert] using a⟩

lemma singleton_disjoint_m (b : Bool) : Disjoint (singlePool K) (mixedPool K b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hU hM
  obtain ⟨u,hu,eu⟩ := Finset.mem_image.mp hU
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hM
  have a := singleSpec K u ((univPool_spec K u).mp hu)
  have hv' := ((nonUni_spec K b v).mp hv).2
  have vert := (privSlot_spec K v).1
  rw [eu] at a
  rw [ev,a,Finset.mem_singleton] at vert
  exact hv' ⟨s,by simpa only [vert] using a⟩

lemma pure_different : Disjoint (purePool K false) (purePool K true) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s hF hT
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hF
  obtain ⟨w,hw,ew⟩ := Finset.mem_image.mp hT
  have cf := ((nonUni_spec K false v).mp hv).1
  have ct := ((nonUni_spec K true w).mp hw).1
  have a : w.1 ∈ raw C (pureSlot K v) := ev.symm ▸ ew ▸ (pureSlot_spec K w).1
  have e := (pureSlot_spec K v).2 w.1 a
  simpa [cf,ct] using e

lemma pure_disjoint_mixed (b d : Bool) : Disjoint (purePool K b) (mixedPool K d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro s p m
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp p
  obtain ⟨w,hw,ew⟩ := Finset.mem_image.mp m
  obtain ⟨a,ha,na⟩ := mixed_choiceAlt K w ((nonUni_spec K d w).mp hw).2
  have vRaw : w.1 ∈ raw C (pureSlot K v) := ev.symm ▸ ew ▸ (privSlot_spec K w).1
  have aRaw : a ∈ raw C (pureSlot K v) := ev.symm ▸ ew ▸ ha
  exact na (((pureSlot_spec K v).2 a aRaw).trans ((pureSlot_spec K v).2 w.1 vRaw).symm)

noncomputable def fullPool : Finset (Side C) :=
  ((singlePool K ∪ purePool K false) ∪ purePool K true) ∪ mixedAll K

lemma fullPool_size :
    (fullPool K).card = (univPool K).card + (purePool K false).card +
      (purePool K true).card + (mixedAll K).card := by
  have du := singleton_disjoint_p K false
  have d2 : Disjoint (singlePool K ∪ purePool K false) (purePool K true) :=
    Finset.disjoint_union_left.mpr ⟨singleton_disjoint_p K true,pure_different K⟩
  have dt (b : Bool) :
      Disjoint ((singlePool K ∪ purePool K false) ∪ purePool K true) (mixedPool K b) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨singleton_disjoint_m K b,pure_disjoint_mixed K false b⟩,
       pure_disjoint_mixed K true b⟩
  unfold fullPool mixedAll
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨dt false,dt true⟩),
    Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint du, singles_size K]

lemma mixed_le_all (b : Bool) : (nonUni K b).card ≤ (mixedAll K).card := by
  rw [← mixed_size K b]
  apply Finset.card_le_card
  cases b
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

def bothSides (S : Finset (Side C)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => (i,false) ∈ S ∧ (i,true) ∈ S)

def haveSide (S : Finset (Side C)) (b : Bool) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => (i,b) ∈ S)

lemma count_bothSides (S : Finset (Side C)) :
    S.card ≤ C.size + (bothSides S).card := by
  let l := haveSide S false
  let r := haveSide S true
  have inter : l ∩ r = bothSides S := by
    ext i
    simp [l,r,haveSide,bothSides]
  let X : Finset (Side C) := S.filter (fun s => s.2 = false)
  let Y : Finset (Side C) := S.filter (fun s => s.2 = true)
  have xy : X ∪ Y = S := by
    ext s
    rcases s with ⟨i,b⟩
    cases b <;> simp [X,Y]
  have dis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro s sx sy
    have x := (Finset.mem_filter.mp sx).2
    have y := (Finset.mem_filter.mp sy).2
    simp [X,Y] at sx sy
    simp [x] at y
  have xImage : X.image Prod.fst = l := by
    ext i
    simp only [Finset.mem_image, X, Finset.mem_filter, l, haveSide, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j,b⟩,⟨h,e⟩,rfl⟩
      change b = false at e
      subst b
      exact h
    · intro h
      exact ⟨(i,false), ⟨h,rfl⟩,rfl⟩
  have yImage : Y.image Prod.fst = r := by
    ext i
    simp only [Finset.mem_image, Y, Finset.mem_filter, r, haveSide, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j,b⟩,⟨h,e⟩,rfl⟩
      change b = true at e
      subst b
      exact h
    · intro h
      exact ⟨(i,true), ⟨h,rfl⟩,rfl⟩
  have xSize : l.card = X.card := by
    rw [← xImage]
    apply Finset.card_image_of_injOn
    rintro ⟨i,b⟩ h ⟨j,d⟩ h' (e:i=j)
    have e1 := (Finset.mem_filter.mp h).2
    have e2 := (Finset.mem_filter.mp h').2
    simp at e1 e2
    simp [e,e1,e2]
  have ySize : r.card = Y.card := by
    rw [← yImage]
    apply Finset.card_image_of_injOn
    rintro ⟨i,b⟩ h ⟨j,d⟩ h' (e:i=j)
    have e1 := (Finset.mem_filter.mp h).2
    have e2 := (Finset.mem_filter.mp h').2
    simp at e1 e2
    simp [e,e1,e2]
  have eq := Finset.card_union_add_card_inter l r
  have ub : (l∪r).card ≤ C.size := by simpa using Finset.card_le_univ (l∪r)
  have xyc : S.card = l.card + r.card := by
    rw [← xy, Finset.card_union_of_disjoint dis, ← xSize, ← ySize]
  rw [inter] at eq
  omega

lemma double_image_exists (b : Bool) (i : Fin C.size)
    (hi : i ∈ bothSides (mixedPool K b)) :
    ∃ v ∈ nonUni K b, privSlot K v = (i,false) ∧ pureSlot K v ∈ doubles K b := by
  obtain ⟨hl,hr⟩ : (i,false) ∈ mixedPool K b ∧ (i,true) ∈ mixedPool K b := by
    simpa [bothSides] using hi
  obtain ⟨v,hv,lv⟩ := Finset.mem_image.mp hl
  obtain ⟨w,hw,rw'⟩ := Finset.mem_image.mp hr
  have vdn : v.1 ≠ w.1 := by
    intro nd
    have e : v=w := Subtype.ext nd
    subst w
    have nn := lv.symm.trans rw'
    simp at nn
  obtain ⟨vc,vn⟩ := (nonUni_spec K b v).mp hv
  obtain ⟨wc,wn⟩ := (nonUni_spec K b w).mp hw
  have heq : (privSlot K v).1 = (privSlot K w).1 := by rw [lv,rw']
  obtain ⟨_, pair⟩ := mixed_double_gate K v w vn wn vdn (vc.trans wc.symm) heq
  have pureMem : pureSlot K v ∈ purePool K b := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  refine ⟨v,hv,lv,?_⟩
  simp [doubles,pureMem,pair,vdn]

noncomputable def doubleOwner (b : Bool) (i : Fin C.size) : Side C := by
  classical
  exact if h : i ∈ bothSides (mixedPool K b)
    then pureSlot K (Classical.choose (double_image_exists K b i h))
    else (i,false)

lemma doubleOwner_spec (b : Bool) (i : Fin C.size) (hi : i ∈ bothSides (mixedPool K b)) :
    ∃ v ∈ nonUni K b, privSlot K v = (i,false) ∧ pureSlot K v = doubleOwner K b i ∧
      doubleOwner K b i ∈ doubles K b := by
  have hh := Classical.choose_spec (double_image_exists K b i hi)
  unfold doubleOwner
  rw [dif_pos hi]
  exact ⟨_,hh.1,hh.2.1,rfl,hh.2.2⟩

lemma doubles_ge (b : Bool) :
    (bothSides (mixedPool K b)).card ≤ (doubles K b).card := by
  classical
  have sub (i : Fin C.size) (hi : i ∈ bothSides (mixedPool K b)) :
      doubleOwner K b i ∈ doubles K b := by
    obtain ⟨v,hv,he1,he2,he3⟩ := doubleOwner_spec K b i hi
    exact he3
  apply Finset.card_le_card_of_injOn (doubleOwner K b) sub
  intro i hi j hj e
  obtain ⟨v,hv,ve,vo,_⟩ := doubleOwner_spec K b i hi
  obtain ⟨x,hx,xe,xo,_⟩ := doubleOwner_spec K b j hj
  obtain ⟨_,hr⟩ : True ∧ (i,true) ∈ mixedPool K b := by
    refine ⟨trivial,?_⟩
    exact (show (i,false) ∈ mixedPool K b ∧ (i,true) ∈ mixedPool K b from by
      simpa [bothSides] using hi).2
  obtain ⟨w,hw,we⟩ := Finset.mem_image.mp hr
  have vw : v.1 ≠ w.1 := by
    intro eq
    have vwe : v=w := Subtype.ext eq
    subst w
    have nn := ve.symm.trans we
    simp at nn
  obtain ⟨vc,vn⟩ := (nonUni_spec K b v).mp hv
  obtain ⟨wc,wn⟩ := (nonUni_spec K b w).mp hw
  have eqg : (privSlot K v).1 = (privSlot K w).1 := by rw [ve,we]
  obtain ⟨_, pair⟩ := mixed_double_gate K v w vn wn vw (vc.trans wc.symm) eqg
  have ep : pureSlot K x = pureSlot K v := xo.trans (e.symm.trans vo.symm)
  have xRaw := (pureSlot_spec K x).1
  rw [ep,pair,Finset.mem_insert,Finset.mem_singleton] at xRaw
  rcases xRaw with eq | eq
  · have vx : x=v := Subtype.ext eq
    subst x
    exact congrArg Prod.fst (ve.symm.trans xe)
  · have wx : x=w := Subtype.ext eq
    subst x
    exact congrArg Prod.fst (we.symm.trans xe)

lemma mixed_double_lower (b : Bool) :
    (nonUni K b).card ≤ C.size + (doubles K b).card := by
  have hm := count_bothSides (mixedPool K b)
  have ds := doubles_ge K b
  rw [mixed_size K b] at hm
  omega

end Slot

namespace Slot

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open scoped BigOperators

variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
variable (K : Environment G C)

lemma fiber_subset (b : Bool) (s : Side C) :
    (fiber K b s).image Subtype.val ⊆ raw C s := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have e := (Finset.mem_filter.mp hw).2
  exact e ▸ (pureSlot_spec K w).1

lemma largeFiber_raw (b : Bool) (s : Side C) (big : 2 ≤ (fiber K b s).card) :
    (raw C s).card ≤ 3 := by
  classical
  have nonempty : (fiber K b s).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := nonempty
  have diff : ((fiber K b s).erase v).Nonempty := by
    have eq := Finset.card_erase_add_one hv
    exact Finset.card_pos.mp (by omega)
  obtain ⟨w,hw'⟩ := diff
  obtain ⟨wnv,hw⟩ := Finset.mem_erase.mp hw'
  obtain ⟨vNon,vSlot⟩ := Finset.mem_filter.mp hv
  obtain ⟨wNon,wSlot⟩ := Finset.mem_filter.mp hw
  have vNU := ((nonUni_spec K b v).mp vNon).2
  have wNU := ((nonUni_spec K b w).mp wNon).2
  have h := pure_pair_card K v w wnv.symm vNU wNU (vSlot.trans wSlot.symm)
  simpa only [vSlot] using h

lemma tightFiber (b : Bool) (s : Side C) (hs : s ∈ purePool K b)
    (tight : (nonUni K b).card + (doubles K b).card = 3 * (purePool K b).card) :
    (raw C s).card ≤ 3 ∧ ∀ v ∈ raw C s, ¬universal C v := by
  classical
  let w (x : Side C) : ℕ := (fiber K b x).card + if (raw C x).card = 2 then 1 else 0
  have pointwise (x) : w x ≤ 3 := by
    unfold w
    split_ifs with h
    · have lim := fiber_embed K b x
      omega
    · have lim := fiber_card K b x
      omega
  have sumw : ∑ x ∈ purePool K b, w x = 3 * (purePool K b).card := by
    dsimp only [w]
    rw [Finset.sum_add_distrib, fibers_sum K b]
    have add : ∑ x ∈ purePool K b, (if (raw C x).card = 2 then (1:ℕ) else 0) =
        (doubles K b).card := by simp [doubles, Finset.sum_filter]
    rw [add]
    exact tight
  have point : w s = 3 := by
    by_contra h
    have smaller : w s < 3 := lt_of_le_of_ne (pointwise s) h
    have strict := Finset.sum_lt_sum (s := purePool K b)
      (f := w) (g := fun _ => (3:ℕ)) (fun x _ => pointwise x) ⟨s,hs,smaller⟩
    rw [sumw] at strict
    simp [Nat.mul_comm] at strict
  have equal : (fiber K b s).card = (raw C s).card := by
    dsimp only [w] at point
    split_ifs at point with e
    · omega
    · have z := largeFiber_raw K b s (by omega)
      have lo := fiber_embed K b s
      omega
  have cov : (fiber K b s).image Subtype.val = raw C s := by
    apply Finset.eq_of_subset_of_card_le (fiber_subset K b s)
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact equal.ge
  refine ⟨?_,?_⟩
  · have lo := fiber_card K b s
    omega
  · intro v hv
    rw [← cov] at hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact ((nonUni_spec K b x).mp ((Finset.mem_filter.mp hx).1)).2

lemma tightMixed (s : Side C) (hs : s ∈ mixedAll K)
    (size0 : (mixedAll K).card = (nonUni K false).card)
    (size1 : (mixedAll K).card = (nonUni K true).card) :
    (raw C s).card ≤ 3 ∧ ∀ v ∈ raw C s, ¬universal C v := by
  classical
  have h0 : mixedPool K false = mixedAll K := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
    change (mixedAll K).card ≤ (mixedPool K false).card
    rw [size0,mixed_size K false]
  have h1 : mixedPool K true = mixedAll K := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
    change (mixedAll K).card ≤ (mixedPool K true).card
    rw [size1,mixed_size K true]
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp (h0.symm ▸ hs)
  obtain ⟨w,hw,ew⟩ := Finset.mem_image.mp (h1.symm ▸ hs)
  obtain ⟨vc,vn⟩ := (nonUni_spec K false v).mp hv
  obtain ⟨wc,wn⟩ := (nonUni_spec K true w).mp hw
  have hprivV : partPrivate K v.1 s := ev ▸ (privSlot_spec K v).2
  have hprivW : partPrivate K w.1 s := ew ▸ (privSlot_spec K w).2
  have sub : raw C s ⊆ {v.1,w.1} := by
    intro u hu
    cases h : K.color u
    · have e := hprivV u hu (h.trans vc.symm)
      simp [e]
    · have e := hprivW u hu (h.trans wc.symm)
      simp [e]
  refine ⟨(Finset.card_le_card sub).trans (Finset.card_le_two.trans (by decide)),
    ?_⟩
  intro u hu
  have mem := sub hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with e | e
  · exact e.symm ▸ vn
  · exact e.symm ▸ wn

lemma tightSlots [DecidableRel G.Adj] (minFour : ∀ v ∈ K.active, 4 ≤
      (Finset.univ.filter (fun w : Fin n => G.Adj v w)).card)
    (univPositive : 0 < (univPool K).card)
    (all : fullPool K = Finset.univ)
    (t0 : (nonUni K false).card + (doubles K false).card = 3 * (purePool K false).card)
    (t1 : (nonUni K true).card + (doubles K true).card = 3 * (purePool K true).card)
    (m0 : (mixedAll K).card = (nonUni K false).card)
    (m1 : (mixedAll K).card = (nonUni K true).card) : False := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_pos.mp univPositive
  have vU := (univPool_spec K v).mp hv
  have full (s : Side C) : s ∈ fullPool K := by rw [all]; exact Finset.mem_univ _
  have caseSlot (s : Side C) :
      (∃ u : Active K, u ∈ univPool K ∧ s = singleSlot K u ∧ raw C s = {u.1}) ∨
      ((raw C s).card ≤ 3 ∧ ∀ w ∈ raw C s, ¬ universal C w) := by
    have mem := full s
    simp only [fullPool, Finset.mem_union] at mem
    rcases mem with ((h | h) | h) | h
    · obtain ⟨u,hu,e⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨u,hu,e.symm,e ▸ singleSpec K u ((univPool_spec K u).mp hu)⟩
    · exact Or.inr (tightFiber K false s h t0)
    · exact Or.inr (tightFiber K true s h t1)
    · exact Or.inr (tightMixed K s h m0 m1)
  have only : positions C v.1 = {singleSlot K v} := by
    ext s
    rw [mem_positions, Finset.mem_singleton]
    constructor
    · intro h
      rcases caseSlot s with ⟨u,hu,eq,sing⟩ | small
      · have e : v.1 = u.1 := by simpa only [sing,Finset.mem_singleton] using h
        have e' : v=u := Subtype.ext e
        exact eq.trans (congrArg (singleSlot K) e').symm
      · exact (small.2 v.1 h vU).elim
    · intro h
      rw [h, singleSpec K v vU]
      exact Finset.mem_singleton_self _
  let s := other C (singleSlot K v)
  have nbSub : (Finset.univ.filter (fun w : Fin n => G.Adj v.1 w)) ⊆ raw C s := by
    intro w hw
    have aw := (Finset.mem_filter.mp hw).2
    exact unique_position_neighbor G C K.computes K.out K.clean aw _ only
  have low := (minFour v.1 v.2).trans (Finset.card_le_card nbSub)
  rcases caseSlot s with ⟨u,_,_,e⟩ | h
  · rw [e,Finset.card_singleton] at low
    omega
  · omega

def minPure (budget d : ℕ) : ℕ :=
  (max d (2*d-budget) + 2)/3

private theorem sizes21 : ∀ d e : Fin 22,
    42-d.val-e.val + minPure 18 d.val + minPure 18 e.val + max d.val e.val ≤ 36 →
    d.val = 18 ∧ e.val = 18 := by decide +kernel

private theorem sizes15 : ∀ d e : Fin 16,
    30-d.val-e.val + minPure 13 d.val + minPure 13 e.val + max d.val e.val ≤ 26 →
    (d.val = 14 ∧ e.val = 14) ∨ (d.val = 12 ∧ e.val = 12) := by decide +kernel

private theorem sizes10 : ∀ d e : Fin 11,
    ¬ 20-d.val-e.val + minPure 8 d.val + minPure 8 e.val + max d.val e.val ≤ 16 := by
  decide +kernel

theorem packing [DecidableRel G.Adj] (part budget : ℕ)
    (mode : (part = 21 ∧ budget = 18) ∨ (part = 15 ∧ budget = 13) ∨
      (part = 10 ∧ budget = 8))
    (c0 : (colorPool K false).card = part)
    (c1 : (colorPool K true).card = part)
    (minFour : part ≠ 10 → ∀ v ∈ K.active, 4 ≤
      (Finset.univ.filter (fun w : Fin n => G.Adj v w)).card)
    (lim : C.size ≤ budget) : False := by
  classical
  let d := (nonUni K false).card
  let e := (nonUni K true).card
  let p := (purePool K false).card
  let q := (purePool K true).card
  let m := (mixedAll K).card
  let s := (univPool K).card
  let j := (doubles K false).card
  let k := (doubles K true).card
  have dLe : d ≤ part := by
    have z := nonUni_count K false
    rw [c0] at z
    omega
  have eLe : e ≤ part := by
    have z := nonUni_count K true
    rw [c1] at z
    omega
  have total : s+d+e=part+part := by
    have h := uni_and_two_colors K
    rw [c0,c1] at h
    exact h
  have dM : d ≤ m := mixed_le_all K false
  have eM : e ≤ m := mixed_le_all K true
  have maxM : max d e ≤ m := max_le dM eM
  have def0 : d+j ≤ 3*p := pure_deficiency K false
  have def1 : e+k ≤ 3*q := pure_deficiency K true
  have low0 : d ≤ C.size+j := mixed_double_lower K false
  have low1 : e ≤ C.size+k := mixed_double_lower K true
  have sumAll : (fullPool K).card = s+p+q+m := fullPool_size K
  have slots : s+p+q+m ≤ C.size*2 := by
    rw [← sumAll]
    simpa using Finset.card_le_univ (fullPool K)
  have mP : minPure budget d ≤ p := by
    have a : max d (2*d-budget) ≤ 3*p := max_le (by omega) (by omega)
    unfold minPure
    omega
  have mQ : minPure budget e ≤ q := by
    have a : max e (2*e-budget) ≤ 3*q := max_le (by omega) (by omega)
    unfold minPure
    omega
  have finite : 2*part-d-e + minPure budget d + minPure budget e + max d e ≤ 2*budget := by omega
  have done (ss : 0 < s) (sat : s+p+q+m = 2*budget)
      (defP : d+j = 3*p) (defQ : e+k = 3*q)
      (mP : m = d) (mQ : m = e) (n10 : part ≠ 10) : False := by
    have all : fullPool K = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [sumAll,sat]
      simp
      omega
    exact tightSlots K (minFour n10) ss all defP defQ mP mQ
  rcases mode with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have h := sizes21 ⟨d,by omega⟩ ⟨e,by omega⟩ finite
    change d=18 ∧ e=18 at h
    have pBound : 6 ≤ p := by omega
    have qBound : 6 ≤ q := by omega
    exact done (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)
  · have h := sizes15 ⟨d,by omega⟩ ⟨e,by omega⟩ finite
    change (d=14 ∧ e=14) ∨ (d=12 ∧ e=12) at h
    rcases h with h | h
    · have pBound : 5 ≤ p := by omega
      have qBound : 5 ≤ q := by omega
      exact done (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)
    · have pBound : 4 ≤ p := by omega
      have qBound : 4 ≤ q := by omega
      exact done (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)
  · exact sizes10 ⟨d,by omega⟩ ⟨e,by omega⟩ finite

lemma cardinal_color_pool (b : Bool) :
    (colorPool K b).card = (K.active.filter (fun v => K.color v = b)).card := by
  classical
  rw [← Finset.card_image_of_injective _ (Subtype.val_injective :
    Function.Injective (Subtype.val : Active K → Fin n))]
  congr 1
  ext v
  simp only [Finset.mem_image, colorPool, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.2,hu⟩
  · rintro ⟨ha,hc⟩
    exact ⟨⟨v,ha⟩,hc,rfl⟩

lemma avoid_two_from_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v a b : Fin n)
    (minThree : 3 ≤ (Finset.univ.filter (fun t : Fin n => G.Adj v t)).card)
    (av : a ≠ v) (bv : b ≠ v)
    (uniq : ∀ {u w c d : Fin n}, u ≠ w → c ≠ d →
      G.Adj u c → G.Adj w c → G.Adj u d → G.Adj w d → False) :
    ∃ t, G.Adj v t ∧ ¬G.Adj a t ∧ ¬G.Adj b t := by
  classical
  let N := Finset.univ.filter (fun t : Fin n => G.Adj v t)
  let A (u : Fin n) := N.filter (fun t => G.Adj u t)
  have card_le (u : Fin n) (un : u ≠ v) : (A u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨nc,uc⟩ := Finset.mem_filter.mp hc
    obtain ⟨nd,ud⟩ := Finset.mem_filter.mp hd
    by_contra h
    exact uniq un.symm h (Finset.mem_filter.mp nc).2 uc (Finset.mem_filter.mp nd).2 ud
  by_contra h
  have sub : N ⊆ A a ∪ A b := by
    intro t ht
    have hv := (Finset.mem_filter.mp ht).2
    by_cases ha : G.Adj a t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,ha⟩)
    · by_cases hb : G.Adj b t
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,hb⟩)
      · exact (h ⟨t,hv,ha,hb⟩).elim
  have le := Finset.card_le_card sub
  have ub := Finset.card_union_le (A a) (A b)
  have qa := card_le a av
  have qb := card_le b bv
  change 3 ≤ N.card at minThree
  omega

end Slot

namespace ActiveNorm.Credited563

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

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

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    cases h : (stripCircuit C).gateVal {v} i
    · rfl
    · exfalso
      rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at h
      have hL := h.1
      have hR := h.2
      unfold sideTrue at hL hR
      rw [decide_eq_true_eq] at hL hR
      have hvL : v ∈ (stripCircuit C).leftVars i := by
        rcases hL with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      have hvR : v ∈ (stripCircuit C).rightVars i := by
        rcases hR with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      rw [mem_strip_leftVars] at hvL
      rw [mem_strip_rightVars] at hvR
      apply hvL.2
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvL.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvR.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

end ActiveNorm.Credited563

theorem ActiveNorm.normalizeSingleton : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
      C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
      (∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) ∧
      (∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i)) ∧
      (C.WellFormed → C'.WellFormed) := by
  intro n C
  refine ⟨PEqualNP.Outside.L_meta_17525_aux.Plane.ActiveNorm.Credited563.stripCircuit C, le_refl C.size,
    fun U => PEqualNP.Outside.L_meta_17525_aux.Plane.ActiveNorm.Credited563.strip_eval_eq C U,
    fun i v => PEqualNP.Outside.L_meta_17525_aux.Plane.ActiveNorm.Credited563.strip_singleton_false C v C.size i i.isLt,
    fun i => PEqualNP.Outside.L_meta_17525_aux.Plane.ActiveNorm.Credited563.strip_disjoint C i,
    fun hWF => hWF⟩

namespace ActiveNorm

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17525_aux.Plane.Pin

variable {n : Nat}

def mask (C : AndCountCircuit n) (A : Finset (Fin n)) : AndCountCircuit n :=
  ⟨C.size, fun i => C.leftVars i ∩ A, C.leftGates, fun i => C.rightVars i ∩ A,
    C.rightGates, C.outVars ∩ A, C.outGates⟩

@[simp] theorem mask_size (C : AndCountCircuit n) (A : Finset (Fin n)) :
    (mask C A).size = C.size := rfl

theorem mask_wf (C : AndCountCircuit n) (A : Finset (Fin n)) (wf : C.WellFormed) :
    (mask C A).WellFormed := wf

private abbrev Hits (U B : Finset (Fin n)) : Prop := ∃ v ∈ B, v ∈ U

private theorem hits_mask (U B A : Finset (Fin n)) :
    Hits U (B ∩ A) ↔ Hits (U ∩ A) B := by
  constructor
  · rintro ⟨v, hv, hu⟩
    obtain ⟨hB,hA⟩ := Finset.mem_inter.mp hv
    exact ⟨v,hB,Finset.mem_inter.mpr ⟨hu,hA⟩⟩
  · rintro ⟨v,hB,hv⟩
    obtain ⟨hu,hA⟩ := Finset.mem_inter.mp hv
    exact ⟨v,Finset.mem_inter.mpr ⟨hB,hA⟩,hu⟩

private theorem side_mask (U B A : Finset (Fin n)) {m : Nat}
    (F : Finset (Fin m)) (i : Fin m) (values : Fin m → Bool) :
    sideTrue U (B ∩ A) F i values = sideTrue (U ∩ A) B F i values := by
  unfold sideTrue
  exact decide_eq_decide.mpr (or_congr (hits_mask U B A) Iff.rfl)

theorem fuel_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) :
    ∀ (d : Nat) (i : Fin C.size),
      (mask C A).gateValFuel U d i = C.gateValFuel (U ∩ A) d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
      intro i
      change
        (sideTrue U (C.leftVars i ∩ A) (C.leftGates i) i
          ((mask C A).gateValFuel U d) &&
         sideTrue U (C.rightVars i ∩ A) (C.rightGates i) i
          ((mask C A).gateValFuel U d)) =
        (sideTrue (U ∩ A) (C.leftVars i) (C.leftGates i) i
          (C.gateValFuel (U ∩ A) d) &&
         sideTrue (U ∩ A) (C.rightVars i) (C.rightGates i) i
          (C.gateValFuel (U ∩ A) d))
      rw [show (mask C A).gateValFuel U d = C.gateValFuel (U ∩ A) d from funext ih]
      simp only [side_mask]

theorem gate_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) (i : Fin C.size) :
    (mask C A).gateVal U i = C.gateVal (U ∩ A) i :=
  fuel_mask C A U C.size i

theorem eval_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) :
    (mask C A).eval U = C.eval (U ∩ A) := by
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  change (Hits U (C.outVars ∩ A) ∨
      ∃ j ∈ C.outGates, (mask C A).gateVal U j = true) ↔
    (Hits (U ∩ A) C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal (U ∩ A) j = true)
  exact or_congr (hits_mask U C.outVars A) (by simp only [gate_mask])

theorem computes_mask (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (comp : C.Computes (activeGraph G A)) :
    (mask C A).Computes (activeGraph G A) := by
  intro U
  rw [eval_mask, comp]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ⟨a,(Finset.mem_inter.mp ha).1,b,(Finset.mem_inter.mp hb).1,hab⟩
  · rintro ⟨a,ha,b,hb,hab⟩
    have hab' := (activeGraph_adj G A a b).mp hab
    exact ⟨a,Finset.mem_inter.mpr ⟨ha,hab'.1⟩,
      b,Finset.mem_inter.mpr ⟨hb,hab'.2.1⟩,hab⟩

private theorem empty_fuel (C : AndCountCircuit n) :
    ∀ (d : Nat) (i : Fin C.size), C.gateValFuel ∅ d i = false := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
      intro i
      simp only [gateValFuel]
      rw [show C.gateValFuel ∅ d = (fun _ => false) from funext ih]
      simp [sideTrue]

theorem single_mask (C : AndCountCircuit n) (A : Finset (Fin n))
    (clean : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false) :
    ∀ i : Fin (mask C A).size, ∀ v : Fin n, (mask C A).gateVal {v} i = false := by
  intro i v
  let j : Fin C.size := i
  refine (gate_mask C A {v} j).trans ?_
  by_cases hv : v ∈ A
  · have h : ({v} : Finset (Fin n)) ∩ A = {v} := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro e
        subst w
        exact ⟨rfl,hv⟩
    rw [h]
    exact clean j v
  · have h : ({v} : Finset (Fin n)) ∩ A = ∅ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨e,hw⟩
      exact hv (e ▸ hw)
    rw [h]
    exact empty_fuel C C.size j

theorem disjoint_mask (C : AndCountCircuit n) (A : Finset (Fin n))
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    ∀ i, Disjoint ((mask C A).leftVars i) ((mask C A).rightVars i) := by
  intro i
  apply Finset.disjoint_left.mpr
  intro v hv hrv
  exact (Finset.disjoint_left.mp (hd i)) (Finset.mem_inter.mp hv).1
    (Finset.mem_inter.mp hrv).1

theorem mask_used (C : AndCountCircuit n) (A : Finset (Fin n)) :
    ∀ s : Slot.Side (mask C A), Slot.raw (mask C A) s ⊆ A := by
  intro s v hv
  rcases s with ⟨i,b⟩
  cases b
  · change v ∈ C.leftVars i ∩ A at hv
    exact (Finset.mem_inter.mp hv).2
  · change v ∈ C.rightVars i ∩ A at hv
    exact (Finset.mem_inter.mp hv).2

theorem out_of_computes (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (comp : C.Computes G) :
    C.outVars = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  have tr : C.eval {v} = true := by
    unfold AndCountCircuit.eval
    exact decide_eq_true (Or.inl ⟨v,hv,Finset.mem_singleton_self v⟩)
  obtain ⟨a,ha,b,hb,adj⟩ := (comp {v}).mp tr
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  exact G.loopless.irrefl v (by simpa only [ea, eb] using adj)

structure Result (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) where
  circuit : AndCountCircuit n
  size_le : circuit.size ≤ C.size
  wf : circuit.WellFormed
  comp : circuit.Computes (activeGraph G A)
  out : circuit.outVars = ∅
  clean : ∀ i : Fin circuit.size, ∀ v : Fin n, circuit.gateVal {v} i = false
  disjoint : ∀ i, Disjoint (circuit.leftVars i) (circuit.rightVars i)
  used : ∀ s : Slot.Side circuit, Slot.raw circuit s ⊆ A

theorem normalizeActive (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes (activeGraph G A)) :
    Nonempty (Result C G A) := by
  obtain ⟨D,dsize,deval,dclean,ddisj,dwf⟩ := normalizeSingleton n C
  have dcomp : D.Computes (activeGraph G A) := by
    intro U
    rw [deval U]
    exact comp U
  have d'comp := computes_mask D G A dcomp
  exact ⟨⟨mask D A, dsize, mask_wf D A (dwf wf), d'comp,
    out_of_computes _ _ d'comp, single_mask D A dclean,
    disjoint_mask D A ddisj, mask_used D A⟩⟩

theorem pinReads_eq_readers (C : AndCountCircuit n) (v : Fin n) :
    pinReads C {v} = Slot.readers C v := by
  ext i
  simp [mem_pinReads, Slot.mem_readers]

theorem positions_eq_pinReads_card (C : AndCountCircuit n) (v : Fin n)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (Slot.positions C v).card = (pinReads C {v}).card := by
  rw [Slot.positions_card C v hd, pinReads_eq_readers]

def Result.toEnvironment {C : AndCountCircuit n}
    {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (R : Result C G A)
    (color : Fin n → Bool)
    (cross : ∀ {v w}, (activeGraph G A).Adj v w → color v ≠ color w)
    (someNeighbor : ∀ v ∈ A, ∃ w, (activeGraph G A).Adj v w)
    (avoidTwo : ∀ v ∈ A, ∀ a b : Fin n, a ≠ v → b ≠ v →
      color a = color v → color b = color v →
      ∃ t, (activeGraph G A).Adj v t ∧ ¬ (activeGraph G A).Adj a t ∧
        ¬ (activeGraph G A).Adj b t)
    (unique : ∀ {a b c d}, a ≠ b → c ≠ d →
      (activeGraph G A).Adj a c → (activeGraph G A).Adj b c →
      (activeGraph G A).Adj a d → (activeGraph G A).Adj b d → False)
    (readTwo : ∀ v ∈ A, (pinReads R.circuit {v}).card ≤ 2) :
    Slot.Environment (activeGraph G A) R.circuit where
  active := A
  color := color
  computes := R.comp
  out := R.out
  clean := R.clean
  disjoint := R.disjoint
  used := R.used
  cross := cross
  someNeighbor := someNeighbor
  avoidTwo := avoidTwo
  uniqueCommon := unique
  twice := fun v hv => by
    rw [positions_eq_pinReads_card _ _ R.disjoint]
    exact readTwo v hv

theorem avoidTwo_of_three (H : SimpleGraph (Fin n))
    (unique : ∀ {a b c d}, a ≠ b → c ≠ d → H.Adj a c → H.Adj b c →
      H.Adj a d → H.Adj b d → False)
    (v a b : Fin n) (hav : a ≠ v) (hbv : b ≠ v)
    (T : Finset (Fin n)) (ht : 3 ≤ T.card) (neighbors : ∀ w ∈ T, H.Adj v w) :
    ∃ w, H.Adj v w ∧ ¬H.Adj a w ∧ ¬H.Adj b w := by
  classical
  let M (u : Fin n) := T.filter (H.Adj u)
  have small (u : Fin n) (hu : u ≠ v) : (M u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have hc' : c ∈ T ∧ H.Adj u c := Finset.mem_filter.mp hc
    have hd' : d ∈ T ∧ H.Adj u d := Finset.mem_filter.mp hd
    by_contra hcd
    exact unique hu hcd hc'.2 (neighbors c hc'.1) hd'.2 (neighbors d hd'.1)
  have few : ((M a) ∪ (M b)).card < T.card := by
    have hsum := Finset.card_union_le (M a) (M b)
    have ha := small a hav
    have hb := small b hbv
    omega
  obtain ⟨w,hw,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card few
  refine ⟨w,neighbors w hw,?_,?_⟩
  · intro ha
    exact hout (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,ha⟩))
  · intro hb
    exact hout (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw,hb⟩))

def Result.toEnvironmentOfThree {C : AndCountCircuit n}
    {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (R : Result C G A)
    (color : Fin n → Bool)
    (cross : ∀ {v w}, (activeGraph G A).Adj v w → color v ≠ color w)
    (unique : ∀ {a b c d}, a ≠ b → c ≠ d →
      (activeGraph G A).Adj a c → (activeGraph G A).Adj b c →
      (activeGraph G A).Adj a d → (activeGraph G A).Adj b d → False)
    (three : ∀ v ∈ A, ∃ T : Finset (Fin n), 3 ≤ T.card ∧
      ∀ w ∈ T, (activeGraph G A).Adj v w)
    (readTwo : ∀ v ∈ A, (pinReads R.circuit {v}).card ≤ 2) :
    Slot.Environment (activeGraph G A) R.circuit := by
  refine R.toEnvironment color cross ?_ ?_ unique readTwo
  · intro v hv
    obtain ⟨T,ht,neighbors⟩ := three v hv
    have hN : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w,hw⟩ := hN
    exact ⟨w,neighbors w hw⟩
  · intro v hv a b hav hbv ca cb
    obtain ⟨T,ht,neighbors⟩ := three v hv
    exact avoidTwo_of_three _ unique v a b hav hbv T ht neighbors

end ActiveNorm

namespace Numeric

abbrev NMask := Nat

def vertices : List Nat := List.range 42

def point (v : Nat) : Bool := decide (v < 21)

def nbrTable : Array NMask := #[2474238803968, 550433193984, 1100866387968, 2201732775936, 5421137920, 10842275840, 21684551680, 43369103360, 86738206720, 173476413440, 346952826880, 693905653760, 1387811307520, 2775622615040, 1153200816128, 2306401632256, 214758850560, 429517701120, 859035402240, 1718070804480, 3436141608960, 81939, 163878, 327756, 655512, 1311024, 524897, 1049794, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 1247744, 398337, 796674, 1593348, 1089545]

def nbr (v : Nat) : NMask := nbrTable[v]?.getD 0

def bit (v : Nat) : Nat := 1 <<< v

def present (mask : NMask) (v : Nat) : Bool := mask.testBit v

def pin (mask : NMask) (v : Nat) : NMask :=
  mask - (mask &&& (bit v ||| nbr v))

def useful (mask : NMask) (v : Nat) : Bool :=
  present mask v && (mask &&& nbr v != 0)

def allMask : NMask := 4398046511103

def h1 : NMask := pin allMask 0

def h2 : NMask := pin h1 22

def firstPin (reverse : Bool) (mask : NMask) : Option Nat :=
  (if reverse then vertices.reverse else vertices).find? (useful mask)

def usefulChain (reverse : Bool) : Nat → NMask → Bool
  | 0, _ => true
  | k+1, mask =>
    match firstPin reverse mask with
    | none => false
    | some v => usefulChain reverse k (pin mask v)

def collect (mask : NMask) (onPoints : Bool) : List Nat → List NMask → Bool
  | [], acc => decide (acc.length ≥ 6)
  | v :: vs, acc =>
    if acc.length ≥ 6 then true else
    if present mask v && (point v == onPoints) then
      let s := mask &&& nbr v
      if s == 0 || acc.contains s then collect mask onPoints vs acc else
      if usefulChain false 4 (pin mask v) || usefulChain true 4 (pin mask v) then
        collect mask onPoints vs (s :: acc)
      else collect mask onPoints vs acc
    else collect mask onPoints vs acc

def h5OK (mask : NMask) : Bool :=
  collect mask true vertices [] || collect mask false vertices []

def checkZ (z : NMask) : Bool :=
  vertices.all fun v => !(present z v) || h5OK (pin z v)

def checkFirst (p : Nat) : Bool :=
  if !(present h2 p) then true else
  let w := pin h2 p
  vertices.all fun v => !(present w v) || (point p == point v) || checkZ (pin w v)

def edge (u v : Nat) : Bool :=
  let pq := if point u then (u,v) else (v,u)
  (point u != point v) && [0,5,7,17,20].contains ((pq.2 + 21 - pq.1) % 21)

def tableOK : Bool :=
  vertices.all fun u => vertices.all fun v => present (nbr u) v == edge u v

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem tableOK_true : tableOK = true := by decide +kernel

end Numeric

namespace Reflection

open Numeric
abbrev V := Fin 42

def rel (u v : V) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)

def plane : SimpleGraph V := SimpleGraph.fromRel rel

instance planeDec : DecidableRel plane.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (rel u v ∨ rel v u))
  unfold rel
  infer_instance

theorem edge_reflect (u v : V) : edge u.val v.val = decide (plane.Adj u v) := by
  by_cases hu : u.val < 21
  · by_cases hv : v.val < 21
    · have hu' : ¬21 ≤ u.val := by omega
      have hv' : ¬21 ≤ v.val := by omega
      simp [edge, point, plane, rel, hu, hv, hu', hv']
    · have hv' : 21 ≤ v.val := by omega
      have hne : u ≠ v := by intro h; subst v; contradiction
      simp [edge, point, plane, rel, hu, hv, hv', hne]
  · have hu' : 21 ≤ u.val := by omega
    by_cases hv : v.val < 21
    · have hne : u ≠ v := by intro h; subst v; contradiction
      simp [edge, point, plane, rel, hu, hu', hv, hne]
    · simp [edge, point, plane, rel, hu, hv]

theorem nbr_reflect (u v : V) : (nbr u.val).testBit v.val = true ↔ plane.Adj u v := by
  have hu : u.val ∈ vertices := List.mem_range.mpr u.isLt
  have hv : v.val ∈ vertices := List.mem_range.mpr v.isLt
  have h := List.all_eq_true.mp (List.all_eq_true.mp tableOK_true u.val hu) v.val hv
  have hb : present (nbr u.val) v.val = edge u.val v.val := beq_iff_eq.mp h
  change present (nbr u.val) v.val = true ↔ plane.Adj u v
  rw [hb, edge_reflect]
  simp

def Low (x : Nat) : Prop := ∀ i, 42 ≤ i → x.testBit i = false

def active (x : Nat) : Finset V := Finset.univ.filter fun v => x.testBit v.val = true

@[simp] theorem mem_active (x : Nat) (v : V) :
    v ∈ active x ↔ x.testBit v.val = true := by simp [active]

@[simp] theorem active_zero : active 0 = ∅ := by
  ext v
  simp

theorem active_injective {x y : Nat} (hx : Low x) (hy : Low y)
    (h : active x = active y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 42
  · have hb : x.testBit i = true ↔ y.testBit i = true := by
      let v : V := ⟨i,hi⟩
      change (x.testBit v.val = true ↔ y.testBit v.val = true)
      simp only [← mem_active, h]
    exact Bool.eq_iff_iff.mpr hb
  · simp [hx i (by omega), hy i (by omega)]

theorem low_and_left {x y : Nat} (hx : Low x) : Low (x &&& y) := by
  intro i hi
  simp [hx i hi]

private theorem land_add_ldiff (x y : Nat) : (x &&& y) + Nat.ldiff x y = x := by
  induction x using Nat.binaryRec generalizing y with
  | zero =>
      simp [Nat.ldiff]
  | bit b x ih =>
      cases y using Nat.bitCasesOn with
      | bit c y =>
          have h := ih y
          rw [Nat.land_bit, Nat.ldiff_bit]
          cases b <;> cases c <;> simp [Nat.bit_val] <;> omega

theorem sub_land_eq_ldiff (x y : Nat) : x - (x &&& y) = Nat.ldiff x y := by
  have h := congrArg (fun n : Nat => n - (x &&& y)) (land_add_ldiff x y)
  simpa using h.symm

private theorem bit_reflect (u v : V) : (bit u.val).testBit v.val = true ↔ u = v := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow, Fin.ext_iff]

def strip (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => w ≠ v ∧ ¬plane.Adj v w

@[simp] theorem mem_strip (S : Finset V) (v w : V) :
    w ∈ strip S v ↔ w ∈ S ∧ w ≠ v ∧ ¬plane.Adj v w := by simp [strip]

theorem pin_reflect (x : Nat) (v : V) :
    active (pin x v.val) = strip (active x) v := by
  unfold pin
  rw [sub_land_eq_ldiff]
  ext w
  have hb : (bit v.val).testBit w.val = decide (w = v) := by
    apply Bool.eq_iff_iff.mpr
    rw [bit_reflect, decide_eq_true_eq]
    exact ⟨Eq.symm, Eq.symm⟩
  have hn : (nbr v.val).testBit w.val = decide (plane.Adj v w) := by
    apply Bool.eq_iff_iff.mpr
    simp [nbr_reflect]
  rw [mem_active, mem_strip, mem_active, Nat.testBit_ldiff, Nat.testBit_or, hb, hn]
  by_cases he : w = v <;> by_cases ha : plane.Adj v w <;> simp [he,ha]

theorem low_pin {x : Nat} (hx : Low x) (v : Nat) : Low (pin x v) := by
  intro i hi
  unfold pin
  rw [sub_land_eq_ldiff]
  simp [Nat.testBit_ldiff, hx i hi]

theorem allMask_bits (i : Nat) : allMask.testBit i = decide (i < 42) := by
  have hh : allMask = 2^42 - 1 := by rfl
  rw [hh, Nat.testBit_two_pow_sub_one]

theorem allMask_low : Low allMask := by
  intro i hi
  rw [allMask_bits]
  exact decide_eq_false (by omega)

theorem active_allMask : active allMask = Finset.univ := by
  ext v
  simp [allMask_bits, v.isLt]

theorem h2_active : active h2 = strip (strip Finset.univ (0 : V)) (22 : V) := by
  calc
    active h2 = strip (active h1) (22 : V) := pin_reflect h1 (22 : V)
    _ = strip (strip (active allMask) (0 : V)) (22 : V) :=
      congrArg (fun S => strip S (22 : V)) (pin_reflect allMask (0 : V))
    _ = _ := by rw [active_allMask]

theorem h2_low : Low h2 := low_pin (low_pin allMask_low 0) 22

def neighborhood (S : Finset V) (v : V) : Finset V :=
  S.filter (plane.Adj v)

@[simp] theorem mem_neighborhood (S : Finset V) (v w : V) :
    w ∈ neighborhood S v ↔ w ∈ S ∧ plane.Adj v w := by simp [neighborhood]

theorem signature_reflect (x : Nat) (v : V) :
    active (x &&& nbr v.val) = neighborhood (active x) v := by
  ext w
  simp [Nat.testBit_and, nbr_reflect]

theorem useful_reflect {x : Nat} (hx : Low x) (v : V) (h : useful x v.val = true) :
    v ∈ active x ∧ (neighborhood (active x) v).Nonempty := by
  have hh : x.testBit v.val = true ∧ (x &&& nbr v.val) ≠ 0 := by
    simpa [useful, present] using h
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hh.2
  have hib : i < 42 := by
    by_contra hge
    have hfalse := low_and_left (y := nbr v.val) hx i (by omega)
    have htrue : (x &&& nbr v.val).testBit i = true := hi
    rw [hfalse] at htrue
    contradiction
  refine ⟨(mem_active x v).mpr hh.1, ?_⟩
  rw [← signature_reflect]
  exact ⟨⟨i,hib⟩, (mem_active _ _).mpr hi⟩

def Chain : Nat → Finset V → Prop
  | 0, _ => True
  | k + 1, S =>
    ∃ v ∈ S, (neighborhood S v).Nonempty ∧ Chain k (strip S v)

private theorem firstPin_sound (rev : Bool) (x v : Nat)
    (h : firstPin rev x = some v) : v < 42 ∧ useful x v = true := by
  unfold firstPin at h
  have hmem := List.mem_of_find?_eq_some h
  have hu : useful x v = true := List.find?_some h
  have hv : v ∈ vertices := by
    cases rev <;> simpa using hmem
  exact ⟨List.mem_range.mp hv, hu⟩

theorem usefulChain_sound (rev : Bool) :
    ∀ (k x : Nat), Low x → usefulChain rev k x = true → Chain k (active x) := by
  intro k
  induction k with
  | zero => intro x hx h; exact True.intro
  | succ k ih =>
      intro x hx h
      cases hv : firstPin rev x with
      | none => simp [usefulChain, hv] at h
      | some v =>
          obtain ⟨hvlt, hu⟩ := firstPin_sound rev x v hv
          let q : V := ⟨v,hvlt⟩
          obtain ⟨hq, hn⟩ := useful_reflect hx q hu
          have ht : usefulChain rev k (pin x v) = true := by
            simpa [usefulChain, hv] using h
          refine ⟨q, hq, hn, ?_⟩
          rw [← pin_reflect]
          exact ih (pin x v) (low_pin hx v) ht

def SignReal (x : Nat) (b : Bool) (s : Nat) : Prop :=
  ∃ v : V, present x v.val = true ∧ point v.val = b ∧
    s = (x &&& nbr v.val) ∧ s ≠ 0 ∧
    (usefulChain false 4 (pin x v.val) = true ∨ usefulChain true 4 (pin x v.val) = true)

private theorem finish_collect {x : Nat} {b : Bool} {acc : List Nat}
    (hn : acc.Nodup) (hs : ∀ s ∈ acc, SignReal x b s) (hsize : 6 ≤ acc.length) :
    ∃ T : Finset Nat, 6 ≤ T.card ∧ ∀ s ∈ T, SignReal x b s := by
  refine ⟨acc.toFinset, ?_, ?_⟩
  · rwa [List.toFinset_card_of_nodup hn]
  · intro s hs'
    exact hs s (List.mem_toFinset.mp hs')

private theorem collect_sound (x : Nat) (b : Bool) :
    ∀ vs acc : List Nat, (∀ v ∈ vs, v < 42) → acc.Nodup →
      (∀ s ∈ acc, SignReal x b s) →
      collect x b vs acc = true →
      ∃ T : Finset Nat, 6 ≤ T.card ∧ ∀ s ∈ T, SignReal x b s := by
  intro vs
  induction vs with
  | nil =>
      intro acc _ hn hs h
      exact finish_collect hn hs (by simpa [collect] using h)
  | cons v vs ih =>
      intro acc hsmall hn hs h
      have hvl : v < 42 := hsmall v (by simp)
      have hvs : ∀ w ∈ vs, w < 42 := fun w hw => hsmall w (by simp [hw])
      by_cases hlen : acc.length ≥ 6
      · exact finish_collect hn hs hlen
      · by_cases hlabel : (present x v && (point v == b)) = true
        · let s := x &&& nbr v
          by_cases hskip : ((s == 0) || acc.contains s) = true
          · apply ih acc hvs hn hs
            have hk : x &&& nbr v = 0 ∨ x &&& nbr v ∈ acc := by
              simpa [s, List.contains_eq_mem] using hskip
            simpa [collect, hlen, hlabel, hk] using h
          · have hk : ¬(x &&& nbr v = 0 ∨ x &&& nbr v ∈ acc) := by
              intro hh
              apply hskip
              simpa [s, List.contains_eq_mem] using hh
            by_cases hchain : (usefulChain false 4 (pin x v) ||
                usefulChain true 4 (pin x v)) = true
            · have h0 : s ≠ 0 := by
                intro e
                exact hskip (by simp [e])
              have hnew : s ∉ acc := by
                intro hm
                exact hskip (by simp [List.contains_eq_mem, hm])
              have hreal : SignReal x b s := by
                have hp := Bool.and_eq_true_iff.mp hlabel
                exact ⟨⟨v,hvl⟩, hp.1, beq_iff_eq.mp hp.2, rfl, h0,
                  Bool.or_eq_true_iff.mp hchain⟩
              apply ih (s :: acc) hvs (List.nodup_cons.mpr ⟨hnew, hn⟩)
              · intro w hw
                rcases List.mem_cons.mp hw with he | hw
                · simpa [he] using hreal
                · exact hs w hw
              · simpa [collect, hlen, hlabel, hk, hchain, s] using h
            · apply ih acc hvs hn hs
              simpa [collect, hlen, hlabel, hk, hchain, s] using h
        · apply ih acc hvs hn hs
          simpa [collect, hlen, hlabel] using h

def Six (S : Finset V) : Prop :=
  ∃ b : Bool, ∃ T : Finset V, 6 ≤ T.card ∧
    (∀ v ∈ T, v ∈ S ∧ point v.val = b ∧ (neighborhood S v).Nonempty ∧
      Chain 4 (strip S v)) ∧
    Set.InjOn (neighborhood S) (T : Set V)

private theorem signatures_to_six {x : Nat} (hx : Low x) (b : Bool)
    (W : Finset Nat) (hc : 6 ≤ W.card) (hW : ∀ s ∈ W, SignReal x b s) :
    Six (active x) := by
  classical
  let pick : Nat → V := fun s => if h : s ∈ W then (hW s h).choose else 0
  have hspec {s : Nat} (h : s ∈ W) :
      present x (pick s).val = true ∧ point (pick s).val = b ∧
      s = (x &&& nbr (pick s).val) ∧ s ≠ 0 ∧
      (usefulChain false 4 (pin x (pick s).val) = true ∨
        usefulChain true 4 (pin x (pick s).val) = true) := by
    simpa [pick, h] using (hW s h).choose_spec
  have hi : Set.InjOn pick (W : Set Nat) := by
    intro s hs t ht he
    have h₁ := (hspec hs).2.2.1
    have h₂ := (hspec ht).2.2.1
    rw [he] at h₁
    exact h₁.trans h₂.symm
  refine ⟨b, W.image pick, ?_, ?_, ?_⟩
  · rwa [(Finset.card_image_iff.mpr hi)]
  · intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp,hb,he,hn,hchain⟩ := hspec hs
    have hv' : useful x (pick s).val = true := by
      have hn' : (x &&& nbr (pick s).val) ≠ 0 := by rwa [← he]
      simp [useful, hp, hn']
    have hg := useful_reflect hx (pick s) hv'
    refine ⟨hg.1, hb, hg.2, ?_⟩
    rw [← pin_reflect]
    rcases hchain with h | h
    · exact usefulChain_sound false 4 _ (low_pin hx _) h
    · exact usefulChain_sound true 4 _ (low_pin hx _) h
  · intro v hv w hw hsame
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (show v ∈ W.image pick from hv)
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (show w ∈ W.image pick from hw)
    have hs' := (hspec hs).2.2.1
    have ht' := (hspec ht).2.2.1
    have hsame' : active s = active t := calc
      active s = neighborhood (active x) (pick s) := (congrArg active hs').trans (signature_reflect x (pick s))
      _ = neighborhood (active x) (pick t) := hsame
      _ = active t := (signature_reflect x (pick t)).symm.trans (congrArg active ht').symm
    have hsl : Low s := by rw [hs']; exact low_and_left hx
    have htl : Low t := by rw [ht']; exact low_and_left hx
    exact congrArg pick (active_injective hsl htl hsame')

theorem h5OK_sound (x : Nat) (hx : Low x) (h : h5OK x = true) :
    Six (active x) := by
  have hv : ∀ v ∈ vertices, v < 42 := fun v h => List.mem_range.mp h
  change (collect x true vertices [] || collect x false vertices []) = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨T,hc,hh⟩ := collect_sound x true vertices [] hv (by simp) (by simp) h
    exact signatures_to_six hx true T hc hh
  · obtain ⟨T,hc,hh⟩ := collect_sound x false vertices [] hv (by simp) (by simp) h
    exact signatures_to_six hx false T hc hh

theorem sample_sound (p : V) (hc : checkFirst p.val = true)
    (hp : p ∈ active h2) (w : V) (hw : w ∈ strip (active h2) p)
    (hcol : point p.val ≠ point w.val) :
    ∀ u ∈ strip (strip (active h2) p) w,
      Six (strip (strip (strip (active h2) p) w) u) := by
  intro u hu
  let x := pin h2 p.val
  let y := pin x w.val
  have hpx : present h2 p.val = true := (mem_active _ _).mp hp
  have hx : active x = strip (active h2) p := pin_reflect _ _
  have hy : active y = strip (strip (active h2) p) w := by
    change active (pin x w.val) = _
    rw [pin_reflect, hx]
  have hwx : present x w.val = true := by
    apply (mem_active _ _).mp
    rw [hx]
    exact hw
  have huy : present y u.val = true := by
    apply (mem_active _ _).mp
    rw [hy]
    exact hu
  have hscan : vertices.all (fun v => !(present x v) || (point p.val == point v) ||
      checkZ (pin x v)) = true := by
    simpa [checkFirst, hpx, x] using hc
  have hz : checkZ y = true := by
    have hh := List.all_eq_true.mp hscan w.val (List.mem_range.mpr w.isLt)
    simpa [hwx, hcol, y] using hh
  have hc5 : h5OK (pin y u.val) = true := by
    change vertices.all (fun v => !(present y v) || h5OK (pin y v)) = true at hz
    have hz' := List.all_eq_true.mp hz u.val (List.mem_range.mpr u.isLt)
    simpa [huy] using hz'
  have hs := h5OK_sound _ (low_pin (low_pin (low_pin h2_low _) _) _) hc5
  rwa [pin_reflect, hy] at hs

end Reflection

namespace Reflection

open Numeric

def part (S : Finset V) (b : Bool) : Finset V := S.filter fun v => point v.val = b

@[simp] theorem mem_part (S : Finset V) (b : Bool) (v : V) :
    v ∈ part S b ↔ v ∈ S ∧ point v.val = b := by simp [part]

theorem adj_opposite {u v : V} (h : plane.Adj u v) : point u.val ≠ point v.val := by
  obtain ⟨_, h⟩ := (SimpleGraph.fromRel_adj rel u v).mp h
  rcases h with h | h
  · have hu := h.1
    have hvge := h.2.1
    have hv : ¬v.val < 21 := by omega
    simp [point, hu, hv]
  · have hv := h.1
    have huge := h.2.1
    have hu : ¬u.val < 21 := by omega
    simp [point, hu, hv]

private theorem bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
  cases a <;> cases b <;> decide

theorem strip_same_part (S : Finset V) (v : V) :
    part (strip S v) (point v.val) = (part S (point v.val)).erase v := by
  ext w
  simp only [mem_part, mem_strip, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hw,hne,_⟩,hc⟩
    exact ⟨hne,hw,hc⟩
  · rintro ⟨hne,hw,hc⟩
    exact ⟨⟨hw,hne,fun h => (adj_opposite h) hc.symm⟩,hc⟩

theorem strip_other_part (S : Finset V) (v : V) :
    part (strip S v) (!(point v.val)) =
      part S (!(point v.val)) \ neighborhood S v := by
  ext w
  simp only [mem_part, mem_strip, Finset.mem_sdiff, mem_neighborhood]
  constructor
  · rintro ⟨⟨hw,_,hno⟩,hc⟩
    exact ⟨⟨hw,hc⟩, fun h => hno h.2⟩
  · rintro ⟨⟨hw,hc⟩,hno⟩
    refine ⟨⟨hw,?_,fun ha => hno ⟨hw,ha⟩⟩,hc⟩
    intro e
    subst w
    exact (bool_ne_iff_eq_not _ _).mpr hc rfl

theorem strip_part_sizes (S : Finset V) (v : V) (hv : v ∈ S) :
    (part (strip S v) (point v.val)).card =
      (part S (point v.val)).card - 1 ∧
    (part (strip S v) (!(point v.val))).card =
      (part S (!(point v.val))).card - (neighborhood S v).card := by
  constructor
  · rw [strip_same_part]
    exact Finset.card_erase_of_mem ((mem_part _ _ _).mpr ⟨hv,rfl⟩)
  · rw [strip_other_part]
    apply Finset.card_sdiff_of_subset
    intro w hw
    have h := (mem_neighborhood _ _ _).mp hw
    exact (mem_part _ _ _).mpr
      ⟨h.1,(bool_ne_iff_eq_not _ _).mp (adj_opposite h.2).symm⟩

theorem neighborhood_strip_opposite (S : Finset V) (v w : V)
    (hopp : point v.val ≠ point w.val) (hw : w ∈ strip S v) :
    neighborhood (strip S v) w = neighborhood S w := by
  ext z
  simp only [mem_neighborhood, mem_strip]
  constructor
  · rintro ⟨⟨hz,_,_⟩,ha⟩
    exact ⟨hz,ha⟩
  · rintro ⟨hz,ha⟩
    refine ⟨⟨hz,?_,?_⟩,ha⟩
    · intro h
      subst z
      have hnone := ((mem_strip _ _ _).mp hw).2.2
      exact hnone (SimpleGraph.Adj.symm ha)
    · intro hbad
      have hvz := (bool_ne_iff_eq_not _ _).mp (adj_opposite hbad)
      have hwz := (bool_ne_iff_eq_not _ _).mp (adj_opposite ha)
      exact hopp (hvz.trans hwz.symm)

def UniqueCommon : Prop :=
  ∀ a b x y : V, a ≠ b → plane.Adj a x → plane.Adj b x →
    plane.Adj a y → plane.Adj b y → x = y

theorem neighborhood_strip_same_drop (uniq : UniqueCommon)
    (S : Finset V) (v w : V) (hSame : point v.val = point w.val)
    (hw : w ∈ strip S v) :
    (neighborhood S w).card ≤ (neighborhood (strip S v) w).card + 1 := by
  have hneigh : neighborhood (strip S v) w =
      neighborhood S w \ neighborhood S v := by
    ext z
    simp only [mem_neighborhood, mem_strip, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hz,_,hno⟩,ha⟩
      exact ⟨⟨hz,ha⟩,fun hb => hno hb.2⟩
    · rintro ⟨⟨hz,ha⟩,hno⟩
      refine ⟨⟨hz,?_,fun hza => hno ⟨hz,hza⟩⟩,ha⟩
      intro e
      subst z
      exact (adj_opposite ha) hSame.symm
  have hsmall : ((neighborhood S w) ∩ neighborhood S v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haw,hav⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbw,hbv⟩ := Finset.mem_inter.mp hb
    exact uniq w v a b ((mem_strip _ _ _).mp hw).2.1
      ((mem_neighborhood _ _ _).mp haw).2 ((mem_neighborhood _ _ _).mp hav).2
      ((mem_neighborhood _ _ _).mp hbw).2 ((mem_neighborhood _ _ _).mp hbv).2
  rw [hneigh]
  have hcount := Finset.card_sdiff_add_card_inter (neighborhood S w) (neighborhood S v)
  omega

theorem distinct_neighborhoods (uniq : UniqueCommon) (S T : Finset V)
    (hdeg : ∀ v ∈ T, 2 ≤ (neighborhood S v).card) :
    Set.InjOn (neighborhood S) (T : Set V) := by
  intro a ha b hb h
  by_contra hn
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < (neighborhood S a).card from by
    have hh := hdeg a ha
    omega)
  have hxb : x ∈ neighborhood S b := h ▸ hx
  have hyb : y ∈ neighborhood S b := h ▸ hy
  exact hxy (uniq a b x y hn ((mem_neighborhood _ _ _).mp hx).2
    ((mem_neighborhood _ _ _).mp hxb).2 ((mem_neighborhood _ _ _).mp hy).2
    ((mem_neighborhood _ _ _).mp hyb).2)

def BaseH2 (S : Finset V) : Prop :=
  (∀ b : Bool, (part S b).card = 15) ∧ ∀ v ∈ S, (neighborhood S v).card = 4

theorem h3_layout {S : Finset V} (base : BaseH2 S)
    (v : V) (hv : v ∈ S) :
    (part (strip S v) (point v.val)).card = 14 ∧
    (part (strip S v) (!(point v.val))).card = 11 ∧
    ∀ w ∈ strip S v, point v.val ≠ point w.val →
      (neighborhood (strip S v) w).card = 4 := by
  obtain ⟨h1,h2⟩ := strip_part_sizes S v hv
  refine ⟨by simpa [base.1] using h1, by simpa [base.1, base.2 v hv] using h2, ?_⟩
  intro w hw hp
  rw [neighborhood_strip_opposite S v w hp hw]
  exact base.2 _ ((mem_strip _ _ _).mp hw).1

theorem h4_layout {S : Finset V} (base : BaseH2 S) (uniq : UniqueCommon)
    (v : V) (hv : v ∈ S) (w : V) (hw : w ∈ strip S v)
    (hp : point v.val ≠ point w.val) :
    let Z := strip (strip S v) w
    (∀ b : Bool, (part Z b).card = 10) ∧
    ∀ u ∈ Z, 3 ≤ (neighborhood Z u).card := by
  dsimp only
  obtain ⟨h3a,h3b,h3d⟩ := h3_layout base v hv
  obtain ⟨h4a,h4b⟩ := strip_part_sizes (strip S v) w hw
  have htp : point w.val = !(point v.val) := (bool_ne_iff_eq_not _ _).mp hp.symm
  have htp' : (!(point w.val)) = point v.val := by simp [htp]
  have h4a' : (part (strip (strip S v) w) (point w.val)).card = 10 := by
    rw [h4a, htp, h3b]
  have h4b' : (part (strip (strip S v) w) (!(point w.val))).card = 10 := by
    rw [h4b, htp', h3a, h3d w hw hp]
  refine ⟨?_, ?_⟩
  · intro b
    by_cases he : b = point w.val
    · simpa only [he] using h4a'
    · have he' := (bool_ne_iff_eq_not _ _).mp he
      simpa only [he'] using h4b'
  · intro u hu
    have hu3 := ((mem_strip _ _ _).mp hu).1
    have hu2 := ((mem_strip _ _ _).mp hu3).1
    by_cases same : point v.val = point u.val
    · have hOpp : point w.val ≠ point u.val := fun h => hp (same.trans h.symm)
      rw [neighborhood_strip_opposite _ w u hOpp hu]
      have hdrop := neighborhood_strip_same_drop uniq S v u same hu3
      have hd := base.2 u hu2
      omega
    · have hSame : point w.val = point u.val := by
        have ht := (bool_ne_iff_eq_not _ _).mp (Ne.symm same)
        exact htp.trans ht.symm
      have hdrop := neighborhood_strip_same_drop uniq _ w u hSame hu
      have hd := h3d u hu3 same
      omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem base_h2_finite :
    (∀ b : Bool, (part (active h2) b).card = 15) ∧
    ∀ v : V, v ∈ active h2 → (neighborhood (active h2) v).card = 4 := by
  decide +kernel

theorem base_h2 : BaseH2 (active h2) := base_h2_finite

end Reflection

namespace Reflection

open Numeric

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
private theorem common_masks : ∀ a b : V, a ≠ b →
    let m := (nbr a.val) &&& (nbr b.val)
    m = 0 ∨ m.isPowerOfTwo := by
  decide +kernel

theorem plane_unique : UniqueCommon := by
  intro a b x y hab hax hbx hay hby
  let m := (nbr a.val) &&& (nbr b.val)
  have hx : m.testBit x.val = true := by
    simp [m, (nbr_reflect a x).mpr hax, (nbr_reflect b x).mpr hbx]
  have hy : m.testBit y.val = true := by
    simp [m, (nbr_reflect a y).mpr hay, (nbr_reflect b y).mpr hby]
  rcases common_masks a b hab with hm | ⟨k,hk⟩
  · change m = 0 at hm
    simp [hm] at hx
  · change m = 2^k at hk
    have h1 : k = x.val := by simpa [hk, Nat.testBit_two_pow] using hx
    have h2 : k = y.val := by simpa [hk, Nat.testBit_two_pow] using hy
    exact Fin.ext (h1.symm.trans h2)

theorem base_h1 :
    (part (active h1) true).card = 20 ∧
    (part (active h1) false).card = 16 ∧
    ∀ v ∈ part (active h1) false, (neighborhood (active h1) v).card = 5 := by
  decide +kernel

end Reflection

namespace Reflection

open Numeric

def AdjEquiv (e : V ≃ V) : Prop :=
  ∀ a b, plane.Adj (e a) (e b) ↔ plane.Adj a b

private theorem adj_inv (e : V ≃ V) (he : AdjEquiv e) (a b : V) :
    plane.Adj a b ↔ plane.Adj (e.symm a) (e.symm b) := by
  simpa only [Equiv.apply_symm_apply] using he (e.symm a) (e.symm b)

theorem strip_image (e : V ≃ V) (he : AdjEquiv e) (S : Finset V) (v : V) :
    strip (S.image e) (e v) = (strip S v).image e := by
  classical
  ext w
  obtain ⟨a,rfl⟩ := e.surjective w
  have mem_img (B : Finset V) : e a ∈ B.image e ↔ a ∈ B := by
    constructor
    · rintro h
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp h
      exact e.injective eq ▸ hx
    · intro h
      exact Finset.mem_image.mpr ⟨a,h,rfl⟩
  simp [mem_img, he v a, e.injective.eq_iff]

theorem neighborhood_image (e : V ≃ V) (he : AdjEquiv e) (S : Finset V) (v : V) :
    neighborhood (S.image e) (e v) = (neighborhood S v).image e := by
  classical
  ext w
  obtain ⟨a,rfl⟩ := e.surjective w
  have mem_img (B : Finset V) : e a ∈ B.image e ↔ a ∈ B := by
    constructor
    · rintro h
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp h
      exact e.injective eq ▸ hx
    · intro h
      exact Finset.mem_image.mpr ⟨a,h,rfl⟩
  simp [mem_img, he v a]

theorem chain_image (e : V ≃ V) (he : AdjEquiv e) :
    ∀ k S, Chain k S → Chain k (S.image e) := by
  intro k
  induction k with
  | zero => intro S h; exact True.intro
  | succ k ih =>
      intro S h
      obtain ⟨v,hv, ⟨w,hw⟩, tail⟩ := h
      refine ⟨e v, Finset.mem_image.mpr ⟨v,hv,rfl⟩, ?_, ?_⟩
      · rw [neighborhood_image e he]
        exact ⟨e w, Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩
      · rw [strip_image e he]
        exact ih (strip S v) tail

theorem Six_image (e : V ≃ V) (he : AdjEquiv e) (φ : Bool → Bool)
    (hc : ∀ a : V, point (e a).val = φ (point a.val))
    {S : Finset V} (h : Six S) : Six (S.image e) := by
  classical
  obtain ⟨b,T,hsz,hs,hi⟩ := h
  refine ⟨φ b,T.image e, ?_, ?_, ?_⟩
  · simpa only [Finset.card_image_of_injective _ e.injective] using hsz
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hxS,hb,⟨w,hw⟩,hchain⟩ := hs x hx
    refine ⟨Finset.mem_image.mpr ⟨x,hxS,rfl⟩, (hc x).trans (congrArg φ hb), ?_, ?_⟩
    · rw [neighborhood_image e he]
      exact ⟨e w, Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩
    · rw [strip_image e he]
      exact chain_image e he _ _ hchain
  · intro a ha b' hb heq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (show a ∈ T.image e from ha)
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (show b' ∈ T.image e from hb)
    simp only [neighborhood_image e he] at heq
    have heraw : neighborhood S x = neighborhood S y := by
      ext w
      have im (B : Finset V) : e w ∈ B.image e ↔ w ∈ B := by
        constructor
        · intro hh
          obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp hh
          exact e.injective eq ▸ hz
        · exact fun hh => Finset.mem_image.mpr ⟨w,hh,rfl⟩
      simpa only [im] using
        (show e w ∈ (neighborhood S x).image e ↔ e w ∈ (neighborhood S y).image e by rw [heq])
    exact congrArg e (hi hx hy heraw)

theorem h5_all_of_orbit (p0 : V) (hc : checkFirst p0.val = true)
    (hp0 : p0 ∈ active h2)
    (orbit : ∀ p ∈ active h2, ∃ e : V ≃ V, AdjEquiv e ∧
      (active h2).image e = active h2 ∧ e p0 = p ∧
      ∃ b : Bool → Bool, Function.Injective b ∧
        ∀ v : V, point (e v).val = b (point v.val)) :
    ∀ p ∈ active h2, ∀ w ∈ strip (active h2) p,
      point p.val ≠ point w.val →
      ∀ u ∈ strip (strip (active h2) p) w,
        Six (strip (strip (strip (active h2) p) w) u) := by
  intro p hp w hw hcol u hu
  obtain ⟨e,he,hact,hp',φ,hφ,hcolor⟩ := orbit p hp
  let w0 := e.symm w
  let u0 := e.symm u
  have ew : e w0 = w := e.apply_symm_apply w
  have eu : e u0 = u := e.apply_symm_apply u
  have pre (S : Finset V) (x : V) : e x ∈ S.image e ↔ x ∈ S := by
    constructor
    · rintro h
      obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp h
      exact e.injective eq ▸ hz
    · exact fun h => Finset.mem_image.mpr ⟨x,h,rfl⟩
  have hm1 : (strip (active h2) p0).image e = strip (active h2) p := by
    rw [← strip_image e he, hact, hp']
  have hm2 : (strip (strip (active h2) p0) w0).image e =
      strip (strip (active h2) p) w := by
    rw [← strip_image e he, hm1, ew]
  have hw0 : w0 ∈ strip (active h2) p0 := (pre _ _).mp (by rwa [ew,hm1])
  have hu0 : u0 ∈ strip (strip (active h2) p0) w0 := (pre _ _).mp (by rwa [eu,hm2])
  have hc0 : point p0.val ≠ point w0.val := by
    intro eq
    exact hcol (by
      rw [← hp', ← ew, hcolor p0, hcolor w0, eq])
  have h := sample_sound p0 hc hp0 w0 hw0 hc0 u0 hu0
  have h' := Six_image e he φ hcolor h
  rwa [← strip_image e he, hm2, eu] at h'

end Reflection

namespace Reflection
open PEqualNP.Outside.L_meta_17525_aux.Plane.Pin
instance activeDec (S : Finset V) : DecidableRel (activeGraph plane S).Adj := fun a b =>
  inferInstanceAs (Decidable (a ∈ S ∧ b ∈ S ∧ plane.Adj a b))
end Reflection

namespace Reflection

open PEqualNP.AndCount
open PEqualNP.Outside.L_meta_17525_aux.Plane.Pin
open Numeric

theorem strip_eq_closed (S : Finset V) (v : V) :
    strip S v = S \ closedPin plane {v} := by
  ext w
  simp [mem_closedPin_singleton, not_or]

theorem pin_active_reflect (x : Nat) (v : V) :
    active (pin x v.val) = active x \ closedPin plane {v} := by
  rw [pin_reflect, strip_eq_closed]

theorem h1_closed : active h1 = Finset.univ \ closedPin plane {(0 : V)} := by
  change active (pin allMask ((0 : V).val)) = _
  rw [pin_active_reflect _ (0 : V), active_allMask]

theorem strip_twice_closed (S : Finset V) (v w : V) :
    strip (strip S v) w = S \ closedPin plane ({v,w} : Finset V) := by
  ext x
  simp only [mem_strip, Finset.mem_sdiff, mem_closedPin, Finset.mem_insert,
    Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, not_or]
  tauto

theorem h2_closed :
    active h2 = Finset.univ \ closedPin plane ({(0 : V),(22 : V)} : Finset V) := by
  rw [h2_active, strip_twice_closed]

theorem neighborhood_graph (S : Finset V) (v : V) (hv : v ∈ S) :
    (Finset.univ.filter fun w => (activeGraph plane S).Adj v w) = neighborhood S v := by
  classical
  ext w
  simp [activeGraph_adj, hv, neighborhood]

theorem chain_to_pin : ∀ (k : Nat) (S : Finset V),
    Reflection.Chain k S → PEqualNP.Outside.L_meta_17525_aux.Plane.Pin.Chain plane k S := by
  intro k
  induction k with
  | zero => intro S h; exact .nil S
  | succ k ih =>
      intro S h
      obtain ⟨v, hv, ⟨w, hw⟩, tail⟩ := h
      obtain ⟨hwS, hAdj⟩ := (mem_neighborhood _ _ _).mp hw
      refine .cons v hv ⟨w, hwS, hAdj⟩ ?_
      rw [← strip_eq_closed]
      exact ih _ tail

theorem chain_floor {k : Nat} {S : Finset V} (h : Reflection.Chain k S) :
    Lower (activeGraph plane S) k :=
  chain_lower plane (chain_to_pin k S h)

def SlotNorm (C : AndCountCircuit 42) : Prop :=
  (∀ (i : Fin C.size) (v : V), C.gateVal {v} i = false) ∧
  ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)

theorem six_floor_normalized
    (Good : AndCountCircuit 42 → Prop)
    (normalize : ∀ C : AndCountCircuit 42, C.WellFormed →
      ∃ D : AndCountCircuit 42, D.WellFormed ∧ D.size ≤ C.size ∧ Good D ∧
        ∀ U, D.eval U = C.eval U)
    (pack : ∀ (C : AndCountCircuit 42) (S T : Finset V) (b : Bool),
      C.WellFormed → C.Computes (activeGraph plane S) → Good C →
      (∀ v ∈ T, v ∈ S ∧ point v.val = b ∧
        (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1) →
      Set.InjOn (neighborhood S) (T : Set V) → T.card ≤ C.size)
    {S : Finset V} (h : Six S) :
    Lower (activeGraph plane S) 6 := by
  intro C0 wf0 comp0
  by_contra! small0
  obtain ⟨C,wf,hsize,hGood,heval⟩ := normalize C0 wf0
  have comp : C.Computes (activeGraph plane S) := by
    intro U
    rw [heval U]
    exact comp0 U
  have small : C.size < 6 := by omega
  obtain ⟨b,T,hc,hshape,hinj⟩ := h
  have good : ∀ v ∈ T, v ∈ S ∧ point v.val = b ∧
      (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1 := by
    intro v hv
    obtain ⟨hvS, hcolor, hn, hchain⟩ := hshape v hv
    obtain ⟨D, wfD, compD, bound⟩ :=
      pin_active C plane S {v} wf comp (singleton_independent plane v)
    have hfloor : 4 ≤ D.size := chain_floor hchain D wfD (by
      simpa only [strip_eq_closed] using compD)
    obtain ⟨w, hw⟩ := hn
    obtain ⟨hwS, hAdj⟩ := (mem_neighborhood _ _ _).mp hw
    have hpos := useful_read_pos C _ comp v ⟨w, hvS, hwS, hAdj⟩
    exact ⟨hvS, hcolor, ⟨w,hw⟩, by omega⟩
  exact (Nat.not_le_of_gt small) (hc.trans (pack C S T b wf comp hGood good hinj))

theorem six_floor
    (pack : ∀ (C : AndCountCircuit 42) (S T : Finset V) (b : Bool),
      C.WellFormed → C.Computes (activeGraph plane S) →
      (∀ v ∈ T, v ∈ S ∧ point v.val = b ∧
        (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1) →
      Set.InjOn (neighborhood S) (T : Set V) → T.card ≤ C.size)
    {S : Finset V} (h : Six S) : Lower (activeGraph plane S) 6 :=
  six_floor_normalized (fun _ => True)
    (fun C wf => ⟨C,wf,le_rfl,True.intro,fun _ => rfl⟩)
    (fun C S T b wf comp _ => pack C S T b wf comp) h

end Reflection

namespace Reflection

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17525_aux.Plane.Pin
open Numeric

namespace Stage

open PEqualNP.Outside.L_meta_17525_aux.Plane.Slot

def Norm (S : Finset V) (C : AndCountCircuit 42) : Prop :=
  C.outVars = ∅ ∧
  (∀ (i : Fin C.size) (v : V), C.gateVal {v} i = false) ∧
  (∀ i, Disjoint (C.leftVars i) (C.rightVars i)) ∧
  ∀ i, C.leftVars i ⊆ S ∧ C.rightVars i ⊆ S

def Normalize : Prop :=
  ∀ (S : Finset V) (C : AndCountCircuit 42), C.WellFormed →
    C.Computes (activeGraph plane S) →
    ∃ D : AndCountCircuit 42, D.WellFormed ∧ D.size ≤ C.size ∧
      D.Computes (activeGraph plane S) ∧ Norm S D

lemma pinReads_singleton (C : AndCountCircuit 42) (v : V) :
    pinReads C {v} = readers C v := by
  ext i
  simp [mem_pinReads, mem_readers]

private lemma adj_cross (S : Finset V) {a b : V} (h : (activeGraph plane S).Adj a b) :
    point a.val ≠ point b.val :=
  adj_opposite ((activeGraph_adj plane S a b).mp h).2.2

private lemma neigh_adj (S : Finset V) (v w : V) (hv : v ∈ S) :
    w ∈ neighborhood S v ↔ (activeGraph plane S).Adj v w := by
  simp [mem_neighborhood,activeGraph_adj,hv]

private lemma neigh_nonempty (S : Finset V) (v : V) (hv : v ∈ S)
    (h : (neighborhood S v).Nonempty) : ∃ w, (activeGraph plane S).Adj v w := by
  obtain ⟨w,hw⟩ := h
  exact ⟨w,(neigh_adj S v w hv).mp hw⟩

lemma one_reader_pack (C : AndCountCircuit 42) (S T : Finset V) (b : Bool)
    (comp : C.Computes (activeGraph plane S)) (norm : Norm S C)
    (data : ∀ v ∈ T, v ∈ S ∧ point v.val = b ∧
      (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1)
    (distinct : Set.InjOn (neighborhood S) (T : Set V)) :
    T.card ≤ C.size := by
  classical
  refine uniform_one_count (activeGraph plane S) C comp norm.1 norm.2.1 norm.2.2.1
    (fun v => point v.val) (adj_cross S) T b ?_ ?_ ?_ ?_
  · intro v hv
    exact (data v hv).2.1
  · intro v hv
    exact neigh_nonempty S v (data v hv).1 (data v hv).2.2.1
  · intro v hv w hw ne
    by_contra hn
    apply ne
    apply distinct hv hw
    ext u
    rw [neigh_adj S v u (data v hv).1, neigh_adj S w u (data w hw).1]
    constructor
    · intro he
      by_contra h
      exact hn ⟨u,Or.inl ⟨he,h⟩⟩
    · intro he
      by_contra h
      exact hn ⟨u,Or.inr ⟨he,h⟩⟩
  · intro v hv
    rw [← pinReads_singleton C v]
    exact (data v hv).2.2.2

private lemma no_four (S : Finset V) (uniq : UniqueCommon) {a b c d : V}
    (ab : a ≠ b) (cd : c ≠ d)
    (ac : (activeGraph plane S).Adj a c) (bc : (activeGraph plane S).Adj b c)
    (ad : (activeGraph plane S).Adj a d) (bd : (activeGraph plane S).Adj b d) : False :=
  cd (uniq a b c d ab ac.2.2 bc.2.2 ad.2.2 bd.2.2)

lemma pack_inside (C : AndCountCircuit 42) (S : Finset V) (partSize budget : ℕ)
    (mode : (partSize = 21 ∧ budget = 18) ∨ (partSize = 15 ∧ budget = 13) ∨
      (partSize = 10 ∧ budget = 8))
    (comp : C.Computes (activeGraph plane S)) (norm : Norm S C)
    (uniq : UniqueCommon)
    (sizes : ∀ b, (part S b).card = partSize)
    (deg : ∀ v ∈ S, 3 ≤ (neighborhood S v).card)
    (minFour : partSize ≠ 10 → ∀ v ∈ S, 4 ≤ (neighborhood S v).card)
    (lim : C.size ≤ budget) (two : ∀ v ∈ S, (pinReads C {v}).card ≤ 2) : False := by
  letI : DecidableRel (activeGraph plane S).Adj := fun a b =>
    inferInstanceAs (Decidable (a ∈ S ∧ b ∈ S ∧ plane.Adj a b))
  let K : Environment (activeGraph plane S) C := {
    active := S
    color := fun v => point v.val
    computes := comp
    out := norm.1
    clean := norm.2.1
    disjoint := norm.2.2.1
    used := by
      rintro ⟨i,b⟩
      cases b
      · simpa [raw] using (norm.2.2.2 i).1
      · simpa [raw] using (norm.2.2.2 i).2
    cross := adj_cross S
    someNeighbor := by
      intro v hv
      exact neigh_nonempty S v hv (Finset.card_pos.mp (by have h := deg v hv; omega))
    avoidTwo := by
      intro v hv a b av bv _ _
      apply avoid_two_from_degree (activeGraph plane S) v a b _ av bv (no_four S uniq)
      rw [neighborhood_graph S v hv]
      exact deg v hv
    uniqueCommon := no_four S uniq
    twice := by
      intro v hv
      rw [positions_card C v norm.2.2.1, ← pinReads_singleton C v]
      exact two v hv }
  have colcard (b : Bool) : (colorPool K b).card = partSize := by
    rw [cardinal_color_pool K b]
    exact sizes b
  refine packing K partSize budget mode (colcard false) (colcard true) ?_ lim
  intro hn v hv
  change v ∈ S at hv
  rw [neighborhood_graph S v hv]
  exact minFour hn v hv

theorem floor_six (normalize : Normalize) {S : Finset V} (cert : Six S) :
    Lower (activeGraph plane S) 6 := by
  intro C0 wf0 comp0
  by_contra! small0
  obtain ⟨C,wf,sz,comp,norm⟩ := normalize S C0 wf0 comp0
  obtain ⟨b,T,hc,hshape,hinj⟩ := cert
  have data : ∀ v ∈ T, v ∈ S ∧ point v.val = b ∧
      (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1 := by
    intro v hv
    obtain ⟨hvS,col,hn,hchain⟩ := hshape v hv
    obtain ⟨D,wD,cD,bd⟩ := pin_active C plane S {v} wf comp (singleton_independent plane v)
    have floor : 4 ≤ D.size := chain_floor hchain D wD (by simpa only [strip_eq_closed] using cD)
    have pos := useful_read_pos C _ comp v (neigh_nonempty S v hvS hn)
    exact ⟨hvS,col,hn,by omega⟩
  have too := one_reader_pack C S T b comp norm data hinj
  omega

def AllFive : Prop :=
  ∀ p ∈ active h2, ∀ w ∈ strip (active h2) p,
    point p.val ≠ point w.val →
    ∀ u ∈ strip (strip (active h2) p) w,
      Six (strip (strip (strip (active h2) p) w) u)

theorem floor_four (normalize : Normalize) (uniq : UniqueCommon) (five : AllFive)
    (p : V) (hp : p ∈ active h2) (w : V) (hw : w ∈ strip (active h2) p)
    (opp : point p.val ≠ point w.val) :
    Lower (activeGraph plane (strip (strip (active h2) p) w)) 9 := by
  let S := strip (strip (active h2) p) w
  obtain ⟨szpart,deg⟩ := h4_layout base_h2 uniq p hp w hw opp
  intro C0 wf0 c0
  by_contra! small0
  obtain ⟨C,wf,sz,c,norm⟩ := normalize S C0 wf0 c0
  have two : ∀ u ∈ S, (pinReads C {u}).card ≤ 2 := by
    intro u hu
    obtain ⟨D,wD,cD,bd⟩ := pin_active C plane S {u} wf c (singleton_independent plane u)
    have low := floor_six normalize (five p hp w hw opp u hu) D wD
      (by change D.Computes (activeGraph plane (strip S u))
          rwa [strip_eq_closed])
    omega
  exact pack_inside C S _ _ (Or.inr (Or.inr ⟨rfl,rfl⟩)) c norm uniq szpart deg (by simp)
    (by omega) two

theorem floor_three (normalize : Normalize) (uniq : UniqueCommon) (five : AllFive)
    (p : V) (hp : p ∈ active h2) :
    Lower (activeGraph plane (strip (active h2) p)) 11 := by
  let S := strip (active h2) p
  let b := !(point p.val)
  let T := part S b
  obtain ⟨_, ht, deg⟩ := h3_layout base_h2 p hp
  intro C0 wf0 c0
  by_contra! small0
  obtain ⟨C,wf,sz,c,norm⟩ := normalize S C0 wf0 c0
  have opp (w : V) (hw : w ∈ T) : point p.val ≠ point w.val := by
    have eq := ((mem_part S b w).mp hw).2
    dsimp [b] at eq
    rw [eq]
    cases point p.val <;> decide
  have degT (w : V) (hw : w ∈ T) : (neighborhood S w).card = 4 :=
    deg w ((mem_part S b w).mp hw).1 (opp w hw)
  have data : ∀ w ∈ T, w ∈ S ∧ point w.val = b ∧
      (neighborhood S w).Nonempty ∧ (pinReads C {w}).card = 1 := by
    intro w hw
    obtain ⟨hwS,col⟩ := (mem_part S b w).mp hw
    have hn := Finset.card_pos.mp (by rw [degT w hw]; decide)
    obtain ⟨D,wD,cD,bd⟩ := pin_active C plane S {w} wf c (singleton_independent plane w)
    have low := floor_four normalize uniq five p hp w hwS (opp w hw) D wD
      (by change D.Computes (activeGraph plane (strip S w))
          rwa [strip_eq_closed])
    have pos := useful_read_pos C _ c w (neigh_nonempty S w hwS hn)
    exact ⟨hwS,col,hn,by omega⟩
  have distinct := distinct_neighborhoods uniq S T (fun w hw => by rw [degT w hw]; decide)
  have cnt := one_reader_pack C S T b c norm data distinct
  change T.card = 11 at ht
  omega

theorem floor_two (normalize : Normalize) (uniq : UniqueCommon) (five : AllFive) :
    Lower (activeGraph plane (active h2)) 14 := by
  let S := active h2
  intro C0 wf0 c0
  by_contra! small0
  obtain ⟨C,wf,sz,c,norm⟩ := normalize S C0 wf0 c0
  have two : ∀ v ∈ S, (pinReads C {v}).card ≤ 2 := by
    intro v hv
    obtain ⟨D,wD,cD,bd⟩ := pin_active C plane S {v} wf c (singleton_independent plane v)
    have low := floor_three normalize uniq five v hv D wD
      (by simpa only [strip_eq_closed] using cD)
    omega
  have deg : ∀ v ∈ S, 4 ≤ (neighborhood S v).card := fun v hv => (base_h2.2 v hv).ge
  exact pack_inside C S _ _ (Or.inr (Or.inl ⟨rfl,rfl⟩)) c norm uniq base_h2.1
    (fun v hv => (by decide : 3 ≤ 4).trans (deg v hv)) (fun _ => deg) (by omega) two

def TwoOrbit : Prop :=
  ∀ w ∈ part (active h1) false, ∃ e : V ≃ V, AdjEquiv e ∧
    (active h2).image e = strip (active h1) w

lemma floor_image (S T : Finset V) (e : V ≃ V) (adj : AdjEquiv e)
    (img : S.image e = T) {k : ℕ} (h : Lower (activeGraph plane S) k) :
    Lower (activeGraph plane T) k := by
  apply lower_transport (activeGraph plane S) (activeGraph plane T) e _ h
  have same (v : V) : e v ∈ T ↔ v ∈ S := by
    rw [← img,Finset.mem_image]
    constructor
    · rintro ⟨u,hu,equ⟩
      exact (e.injective equ) ▸ hu
    · intro hu
      exact ⟨v,hu,rfl⟩
  intro a b
  simp only [activeGraph_adj,same]
  exact and_congr_right (fun _ => and_congr_right (fun _ => adj a b))

theorem floor_one (normalize : Normalize) (uniq : UniqueCommon) (five : AllFive)
    (twoOrbit : TwoOrbit)
    (lineCard : (part (active h1) false).card = 16)
    (lineDeg : ∀ v ∈ part (active h1) false, (neighborhood (active h1) v).card = 5) :
    Lower (activeGraph plane (active h1)) 16 := by
  let S := active h1
  let T := part S false
  intro C0 wf0 c0
  by_contra! small0
  obtain ⟨C,wf,sz,c,norm⟩ := normalize S C0 wf0 c0
  have data : ∀ v ∈ T, v ∈ S ∧ point v.val = false ∧
      (neighborhood S v).Nonempty ∧ (pinReads C {v}).card = 1 := by
    intro v hv
    obtain ⟨hvS,col⟩ := (mem_part S false v).mp hv
    obtain ⟨e,adj,img⟩ := twoOrbit v hv
    have hn : (neighborhood S v).Nonempty := Finset.card_pos.mp (by rw [lineDeg v hv]; decide)
    obtain ⟨D,wD,cD,bd⟩ := pin_active C plane S {v} wf c (singleton_independent plane v)
    have low := floor_image _ _ e adj img (floor_two normalize uniq five) D wD
      (by simpa only [strip_eq_closed] using cD)
    have pos := useful_read_pos C _ c v (neigh_nonempty S v hvS hn)
    exact ⟨hvS,col,hn,by omega⟩
  have distinct := distinct_neighborhoods uniq S T (fun v hv => by rw [lineDeg v hv]; decide)
  have cnt := one_reader_pack C S T false c norm data distinct
  change T.card = 16 at lineCard
  omega

def SingleFloors : Prop :=
  ∀ v : V, Lower (activeGraph plane (Finset.univ \ closedPin plane {v})) 16

def PairFloors : Prop :=
  ∀ p l : V, p.val < 21 → 21 ≤ l.val → ¬ plane.Adj p l →
    Lower (activeGraph plane (Finset.univ \ closedPin plane ({p,l} : Finset V))) 14

private lemma pair_independent (p l : V) (non : ¬ plane.Adj p l) :
    Independent plane ({p,l} : Finset V) := by
  intro a ha b hb edge
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact plane.loopless.irrefl _ edge
  · exact non edge
  · exact non edge.symm
  · exact plane.loopless.irrefl _ edge

lemma root_single (low : SingleFloors) (C : AndCountCircuit 42)
    (wf : C.WellFormed) (c : C.Computes plane) (v : V) :
    {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard + 16 ≤ C.size := by
  obtain ⟨D,wD,cD,bd⟩ := pin_graph C plane {v} wf c (singleton_independent plane v)
  have lb := low v D wD cD
  rw [pinReads_singleton C v, ← readers_ncard C v] at bd
  omega

lemma root_pair (low : PairFloors) (C : AndCountCircuit 42)
    (wf : C.WellFormed) (c : C.Computes plane) (p l : V)
    (hp : p.val < 21) (hl : 21 ≤ l.val) (non : ¬ plane.Adj p l) :
    {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard + 14 ≤ C.size := by
  obtain ⟨D,wD,cD,bd⟩ := pin_graph C plane ({p,l} : Finset V) wf c (pair_independent p l non)
  have lb := low p l hp hl non D wD cD
  rw [pinReads_card C ({p,l} : Finset V)] at bd
  have eq :
      {i : Fin C.size | ∃ v ∈ ({p,l} : Finset V), v ∈ C.leftVars i ∨ v ∈ C.rightVars i} =
      {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i} := by
    ext i
    simp only [Set.mem_setOf_eq,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨v, rfl | rfl, hd⟩
      · rcases hd with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hd)
    · rintro (h | h | h)
      · exact ⟨p,Or.inl rfl,Or.inl h⟩
      · exact ⟨p,Or.inl rfl,Or.inr h⟩
      · exact ⟨l,Or.inr rfl,h⟩
  rw [eq] at bd
  omega

private theorem root_cards : ∀ b : Bool, (part Finset.univ b).card = 21 := by
  decide +kernel

private theorem root_neigh : ∀ v : V, (neighborhood Finset.univ v).card = 5 := by
  decide +kernel

lemma root_atLeast (one : SingleFloors) (uniq : UniqueCommon) (C : AndCountCircuit 42)
    (wf : C.WellFormed) (c : C.Computes plane) (out : C.outVars = ∅)
    (clean : ∀ (i : Fin C.size) (v : V), C.gateVal {v} i = false)
    (dis : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) : 19 ≤ C.size := by
  by_contra! sm
  have comp : C.Computes (activeGraph plane Finset.univ) := by
    rw [activeGraph_univ]
    exact c
  have norm : Norm Finset.univ C := ⟨out,clean,dis,fun _ =>
    ⟨Finset.subset_univ _,Finset.subset_univ _⟩⟩
  have two (v : V) (_ : v ∈ (Finset.univ : Finset V)) : (pinReads C {v}).card ≤ 2 := by
    have b := root_single one C wf c v
    rw [readers_ncard C v, ← pinReads_singleton C v] at b
    omega
  have deg (v : V) (_ : v ∈ (Finset.univ : Finset V)) :
      3 ≤ (neighborhood Finset.univ v).card := by rw [root_neigh]; decide
  have min4 (_ : (21:ℕ) ≠ 10) (v : V) (_ : v ∈ (Finset.univ : Finset V)) :
      4 ≤ (neighborhood Finset.univ v).card := by rw [root_neigh]; decide
  exact pack_inside C Finset.univ _ _ (Or.inl ⟨rfl,rfl⟩) comp norm uniq root_cards deg min4
    (by omega) two

end Stage
end Reflection

namespace Reflection

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17525_aux.Plane.Pin
open Numeric

namespace Stage

def SingleOrbit : Prop :=
  ∀ v : V, ∃ e : V ≃ V, AdjEquiv e ∧ e (0 : V) = v

def PairOrbit : Prop :=
  ∀ p l : V, p.val < 21 → 21 ≤ l.val → ¬ plane.Adj p l →
    ∃ e : V ≃ V, AdjEquiv e ∧ e (0 : V) = p ∧ e (22 : V) = l

private lemma image_univ_equiv (e : V ≃ V) :
    (Finset.univ : Finset V).image e = Finset.univ := by
  ext v
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    exact Finset.mem_image.mpr ⟨e.symm v,Finset.mem_univ _,e.apply_symm_apply v⟩

private lemma h1_strip : active h1 = strip Finset.univ (0 : V) := by
  rw [strip_eq_closed,h1_closed]

lemma single_mask_image (e : V ≃ V) (adj : AdjEquiv e) (v : V) (ev : e (0 : V) = v) :
    (active h1).image e = Finset.univ \ closedPin plane {v} := by
  calc
    (active h1).image e = (strip Finset.univ (0 : V)).image e := by rw [h1_strip]
    _ = strip (Finset.univ.image e) (e (0 : V)) := (strip_image e adj _ _).symm
    _ = Finset.univ \ closedPin plane {v} := by
      rw [image_univ_equiv,ev,strip_eq_closed]

lemma pair_mask_image (e : V ≃ V) (adj : AdjEquiv e) (p l : V)
    (ep : e (0 : V) = p) (el : e (22 : V) = l) :
    (active h2).image e = Finset.univ \ closedPin plane ({p,l} : Finset V) := by
  calc
    (active h2).image e = (strip (strip Finset.univ (0 : V)) (22 : V)).image e := by
      rw [h2_active]
    _ = strip (strip (Finset.univ.image e) (e (0 : V))) (e (22 : V)) := by
      rw [strip_image e adj Finset.univ (0 : V),
        strip_image e adj (strip Finset.univ (0 : V)) (22 : V)]
    _ = Finset.univ \ closedPin plane ({p,l} : Finset V) := by
      rw [image_univ_equiv,ep,el,strip_twice_closed]

lemma two_orbit (orb : PairOrbit) : TwoOrbit := by
  intro w hw
  obtain ⟨hwS,hcolor⟩ := (mem_part _ _ _).mp hw
  have val : 21 ≤ w.val := by
    by_contra! nh
    simp [point,nh] at hcolor
  have no : ¬ plane.Adj (0 : V) w := by
    rw [h1_strip] at hwS
    exact ((mem_strip _ _ _).mp hwS).2.2
  obtain ⟨e,adj,e0,ew⟩ := orb (0 : V) w (by decide) val no
  refine ⟨e,adj,?_⟩
  rw [pair_mask_image e adj _ _ e0 ew, h1_strip,strip_twice_closed]

lemma single_floors (orb : SingleOrbit) (base : Lower (activeGraph plane (active h1)) 16) :
    SingleFloors := by
  intro v
  obtain ⟨e,adj,ev⟩ := orb v
  exact floor_image _ _ e adj (single_mask_image e adj v ev) base

lemma pair_floors (orb : PairOrbit) (base : Lower (activeGraph plane (active h2)) 14) :
    PairFloors := by
  intro p l hp hl no
  obtain ⟨e,adj,ep,el⟩ := orb p l hp hl no
  exact floor_image _ _ e adj (pair_mask_image e adj p l ep el) base

lemma normalize_exact : Normalize := by
  intro S C wf co
  obtain ⟨r⟩ := PEqualNP.Outside.L_meta_17525_aux.Plane.ActiveNorm.normalizeActive C plane S wf co
  refine ⟨r.circuit,r.wf,r.size_le,r.comp,r.out,r.clean,r.disjoint,?_⟩
  intro i
  exact ⟨by simpa [PEqualNP.Outside.L_meta_17525_aux.Plane.Slot.raw] using r.used (i,false),
    by simpa [PEqualNP.Outside.L_meta_17525_aux.Plane.Slot.raw] using r.used (i,true)⟩

theorem from_certified_orbits (single : SingleOrbit) (pair : PairOrbit) (five : AllFive)
    (C : AndCountCircuit 42) (wf : C.WellFormed) (comp : C.Computes plane)
    (out : C.outVars = ∅) (clean : ∀ (i : Fin C.size) (v : V), C.gateVal {v} i = false)
    (dis : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (_size : C.size ≤ 20) :
    19 ≤ C.size ∧
    (∀ v : V, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard + 16 ≤ C.size) ∧
    ∀ p l : V, p.val < 21 → 21 ≤ l.val → ¬ plane.Adj p l →
      {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard + 14 ≤ C.size := by
  have lo1 := floor_one normalize_exact plane_unique five (two_orbit pair) base_h1.2.1 base_h1.2.2
  have lo2 := floor_two normalize_exact plane_unique five
  have all1 := single_floors single lo1
  have all2 := pair_floors pair lo2
  exact ⟨root_atLeast all1 plane_unique C wf comp out clean dis,
    root_single all1 C wf comp, root_pair all2 C wf comp⟩

end Stage
end Reflection

namespace Numeric

def autoA : Array Nat := #[0,6,1,17,19,20,15,4,14,13,11,16,8,18,9,10,5,7,2,3,12,26,27,22,24,40,41,32,21,34,39,37,36,25,35,30,31,33,28,23,29,38]
def autoB : Array Nat := #[0,11,10,1,2,3,20,17,18,13,9,12,19,4,8,14,7,5,6,15,16,28,31,27,22,23,41,37,38,39,30,29,40,24,25,34,35,33,26,32,36,21]

def a (x : Nat) : Nat := autoA[x]?.getD 0
def b (x : Nat) : Nat := autoB[x]?.getD 0

def h2auto (x : Nat) : Nat := b (b (a (b (a x))))

def dualSwap (x : Nat) : Nat :=
  if point x then 21 + ((22-x) % 21) else (43-x) % 21

def translate (t x : Nat) : Nat :=
  if point x then (x+t) % 21 else 21 + (x+t) % 21

def adjOK (f : Nat → Nat) : Bool :=
  vertices.all fun u => vertices.all fun v => edge u v == edge (f u) (f v)

def permOK (f : Nat → Nat) : Bool :=
  (vertices.all fun u => decide (f u < 42)) &&
    decide ((vertices.map f).Nodup) && adjOK f

def activeOK (m : NMask) (f : Nat → Nat) : Bool :=
  vertices.all fun u => present m u == present m (f u)

def iterMap (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k+1, x => iterMap f k (f x)

def onSideOrbit (u : Nat) : Bool :=
  !(present h2 u) || (List.range 15).any
    (fun j => iterMap h2auto j 3 == u || dualSwap (iterMap h2auto j 3) == u)

def words : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => (words k).flatMap fun w => [false :: w, true :: w]

def mapWord (w : List Bool) (u : Nat) : Nat :=
  w.foldl (fun x k => if k then b x else a x) u

def nonincidentOrbit (u : Nat) : Bool :=
  point u || edge 0 u ||
    (List.range 6).any (fun k => (words k).any (fun w => mapWord w 22 == u))

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem a_ok : permOK a = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem b_ok : permOK b = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem dualSwap_ok : permOK dualSwap = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem h2_actions : (activeOK h2 h2auto && activeOK h2 dualSwap) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem every_h2_vertex : vertices.all onSideOrbit = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem every_nonincident_line : vertices.all nonincidentOrbit = true := by decide +kernel

theorem ab_fix : a 0 = 0 ∧ b 0 = 0 := by decide +kernel
theorem dual_pair : dualSwap 0 = 22 ∧ dualSwap 22 = 0 := by decide +kernel

end Numeric
namespace Reflection

open Numeric

private theorem perm_pieces (f : Nat → Nat) (hf : permOK f = true) :
    (∀ u ∈ vertices, f u < 42) ∧ (vertices.map f).Nodup ∧ adjOK f = true := by
  unfold permOK at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
  simpa only [and_assoc] using hf

private def permFn (f : Nat → Nat) (hf : permOK f = true) (u : V) : V :=
  ⟨f u.val, (perm_pieces f hf).1 u.val (List.mem_range.mpr u.isLt)⟩

private theorem permFn_inj (f : Nat → Nat) (hf : permOK f = true) :
    Function.Injective (permFn f hf) := by
  intro u v huv
  have hs : f u.val = f v.val := congrArg Fin.val huv
  have hN := (perm_pieces f hf).2.1
  have hu : u.val < (vertices.map f).length := by simpa [vertices] using u.isLt
  have hv : v.val < (vertices.map f).length := by simpa [vertices] using v.isLt
  apply Fin.ext
  apply (List.Nodup.getElem_inj_iff hN (hi := hu) (hj := hv)).mp
  simpa [vertices] using hs

noncomputable def graphPerm (f : Nat → Nat) (hf : permOK f = true) : V ≃ V := by
  classical
  exact Equiv.ofBijective (permFn f hf)
    (Finite.injective_iff_bijective.mp (permFn_inj f hf))

@[simp] theorem graphPerm_val (f : Nat → Nat) (hf : permOK f = true) (u : V) :
    (graphPerm f hf u).val = f u.val := rfl

theorem graphPerm_adj (f : Nat → Nat) (hf : permOK f = true) :
    AdjEquiv (graphPerm f hf) := by
  intro u v
  have hu : u.val ∈ vertices := List.mem_range.mpr u.isLt
  have hv : v.val ∈ vertices := List.mem_range.mpr v.isLt
  have ha := (perm_pieces f hf).2.2
  have hb := List.all_eq_true.mp (List.all_eq_true.mp ha u.val hu) v.val hv
  have hh : edge u.val v.val = edge (f u.val) (f v.val) := beq_iff_eq.mp hb
  have hh' : edge u.val v.val =
      edge (graphPerm f hf u).val (graphPerm f hf v).val := hh
  simp only [edge_reflect] at hh'
  simpa only [decide_eq_true_eq] using (Bool.eq_iff_iff.mp hh').symm

theorem active_image_of_OK (m : NMask) (f : Nat → Nat) (hf : permOK f = true)
    (hm : activeOK m f = true) :
    (active m).image (graphPerm f hf) = active m := by
  ext w
  let e := graphPerm f hf
  let u := e.symm w
  have hu : u.val ∈ vertices := List.mem_range.mpr u.isLt
  have hm' := List.all_eq_true.mp hm u.val hu
  have hbit : present m u.val = present m w.val := by
    have hm'' : present m u.val = present m (e u).val := beq_iff_eq.mp hm'
    simpa [u] using hm''
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
    have huv : v = u := by
      apply e.injective
      exact he.trans (e.apply_symm_apply w).symm
    have hb : present m v.val = true := (mem_active m v).mp hv
    rw [huv] at hb
    exact (mem_active m w).mpr (hbit.symm.trans hb)
  · intro h
    refine Finset.mem_image.mpr ⟨u, ?_, e.apply_symm_apply w⟩
    exact (mem_active m u).mpr (hbit.trans ((mem_active m w).mp h))

theorem adjEquiv_trans {e f : V ≃ V} (he : AdjEquiv e) (hf : AdjEquiv f) :
    AdjEquiv (e.trans f) := fun u v => (hf (e u) (e v)).trans (he u v)

theorem adjEquiv_symm {e : V ≃ V} (he : AdjEquiv e) : AdjEquiv e.symm := by
  intro u v
  simpa only [Equiv.apply_symm_apply] using (he (e.symm u) (e.symm v)).symm

end Reflection
namespace Numeric

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem tr_ok : ∀ t : Fin 21, permOK (translate t.val) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem tr_color : ∀ (t : Fin 21) (v : Fin 42), point (translate t.val v.val) = point v.val := by
  decide +kernel

theorem to_zero (p : Fin 42) : point p.val = true → ∃ t : Fin 21, translate t.val p.val = 0 := by
  have h : ∀ q : Fin 42, point q.val = true →
      ∃ t : Fin 21, translate t.val q.val = 0 := by decide +kernel
  exact h p

theorem transitive_single (v : Fin 42) :
    ∃ t : Fin 21, translate t.val 0 = v.val ∨ translate t.val 22 = v.val := by
  have h : ∀ u : Fin 42, ∃ t : Fin 21, translate t.val 0 = u.val ∨
      translate t.val 22 = u.val := by decide +kernel
  exact h v

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem h2perm_ok : permOK h2auto = true := by decide +kernel

theorem h2perm_color : ∀ v : Fin 42, point (h2auto v.val) = point v.val := by decide +kernel

theorem dual_color : ∀ v : Fin 42, point (dualSwap v.val) = !point v.val := by decide +kernel

end Numeric

namespace Reflection

open Numeric

noncomputable def orbitA : V ≃ V := graphPerm a a_ok
noncomputable def orbitB : V ≃ V := graphPerm b b_ok
noncomputable def orbitD : V ≃ V := graphPerm dualSwap dualSwap_ok
noncomputable def orbitG : V ≃ V := graphPerm h2auto h2perm_ok
noncomputable def orbitT (t : Fin 21) : V ≃ V := graphPerm (translate t.val) (tr_ok t)

noncomputable def wordEquiv : List Bool → V ≃ V
  | [] => Equiv.refl _
  | k :: ks => (if k then orbitB else orbitA).trans (wordEquiv ks)

theorem word_adjacency : ∀ w, AdjEquiv (wordEquiv w)
  | [] => fun _ _ => Iff.rfl
  | true :: ws => adjEquiv_trans (graphPerm_adj b b_ok) (word_adjacency ws)
  | false :: ws => adjEquiv_trans (graphPerm_adj a a_ok) (word_adjacency ws)

theorem word_at_zero : ∀ w, wordEquiv w (0 : V) = 0
  | [] => rfl
  | true :: ws => by
    have hb : orbitB (0 : V) = 0 := Fin.ext ab_fix.2
    simpa [wordEquiv, hb] using word_at_zero ws
  | false :: ws => by
    have ha : orbitA (0 : V) = 0 := Fin.ext ab_fix.1
    simpa [wordEquiv, ha] using word_at_zero ws

theorem word_val : ∀ (w : List Bool) (v : V),
    (wordEquiv w v).val = mapWord w v.val
  | [], _ => rfl
  | true :: ws, v => word_val ws (orbitB v)
  | false :: ws, v => word_val ws (orbitA v)

theorem singleEquiv (v : V) : ∃ e : V ≃ V, AdjEquiv e ∧ e 0 = v := by
  obtain ⟨t, ht | ht⟩ := transitive_single v
  · exact ⟨orbitT t, graphPerm_adj _ _, Fin.ext ht⟩
  · refine ⟨orbitD.trans (orbitT t), adjEquiv_trans (graphPerm_adj _ _) (graphPerm_adj _ _), ?_⟩
    have hd : orbitD (0 : V) = 22 := Fin.ext dual_pair.1
    change orbitT t (orbitD 0) = v
    rw [hd]
    exact Fin.ext ht

theorem pairEquiv (p l : V) (hp : point p.val = true) (hl : point l.val = false)
    (hne : ¬plane.Adj p l) :
    ∃ e : V ≃ V, AdjEquiv e ∧ e 0 = p ∧ e 22 = l := by
  obtain ⟨t, ht⟩ := to_zero p hp
  let tr := orbitT t
  have hadj : AdjEquiv tr := graphPerm_adj _ _
  have htp : tr p = 0 := Fin.ext ht
  let w := tr l
  have hwc : point w.val = false := (tr_color t l).trans hl
  have hwe : edge 0 w.val = false := by
    rw [show 0 = (0 : V).val by rfl, edge_reflect]
    apply decide_eq_false
    intro hh
    exact hne ((hadj p l).mp (htp.symm ▸ hh))
  have hwmem : w.val ∈ vertices := List.mem_range.mpr w.isLt
  have hob := List.all_eq_true.mp every_nonincident_line w.val hwmem
  have hbool : (List.range 6).any (fun k => (words k).any (fun xs => mapWord xs 22 == w.val)) = true := by
    simpa [nonincidentOrbit,hwc,hwe] using hob
  obtain ⟨k,_,hk⟩ := List.any_eq_true.mp hbool
  obtain ⟨xs,_,hxs⟩ := List.any_eq_true.mp hk
  have hx : wordEquiv xs (22 : V) = w := by
    apply Fin.ext
    rw [word_val]
    exact beq_iff_eq.mp hxs
  refine ⟨(wordEquiv xs).trans tr.symm,
    adjEquiv_trans (word_adjacency xs) (adjEquiv_symm hadj), ?_, ?_⟩
  · change tr.symm (wordEquiv xs 0) = p
    rw [word_at_zero, ← htp, Equiv.symm_apply_apply]
  · change tr.symm (wordEquiv xs 22) = l
    rw [hx]
    exact tr.symm_apply_apply l

noncomputable def iterateEquiv (e : V ≃ V) : Nat → V ≃ V
  | 0 => Equiv.refl _
  | k+1 => e.trans (iterateEquiv e k)

theorem iterAdj (e : V ≃ V) (he : AdjEquiv e) : ∀ k, AdjEquiv (iterateEquiv e k)
  | 0 => fun _ _ => Iff.rfl
  | k+1 => adjEquiv_trans he (iterAdj e he k)

theorem iter_val : ∀ (k : Nat) (v : V), (iterateEquiv orbitG k v).val = iterMap h2auto k v.val
  | 0, _ => rfl
  | k+1, v => iter_val k (orbitG v)

theorem iter_color : ∀ (k : Nat) (v : V), point (iterateEquiv orbitG k v).val = point v.val
  | 0, _ => rfl
  | k+1, v => (iter_color k (orbitG v)).trans (h2perm_color v)

theorem iter_image (e : V ≃ V) (T : Finset V) (h : T.image e = T) :
    ∀ k, T.image (iterateEquiv e k) = T
  | 0 => by simp [iterateEquiv]
  | k+1 => by
    change T.image ((iterateEquiv e k : V → V) ∘ (e : V → V)) = T
    rw [← Finset.image_image, h, iter_image e T h k]

theorem h2Equiv (v : V) (hv : v ∈ active h2) : ∃ (e : V ≃ V) (φ : Bool → Bool),
    AdjEquiv e ∧ (active h2).image e = active h2 ∧
    Function.Injective φ ∧ (∀ u, point (e u).val = φ (point u.val)) ∧ e 3 = v := by
  have hV : v.val ∈ vertices := List.mem_range.mpr v.isLt
  have hact : present h2 v.val = true := (mem_active h2 v).mp hv
  have hor := List.all_eq_true.mp every_h2_vertex v.val hV
  have hex : (List.range 15).any (fun j =>
      iterMap h2auto j 3 == v.val || dualSwap (iterMap h2auto j 3) == v.val) = true := by
    simpa [onSideOrbit,hact] using hor
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp hex
  let e := iterateEquiv orbitG j
  have he := iterAdj orbitG (graphPerm_adj h2auto h2perm_ok) j
  have hA := Bool.and_eq_true_iff.mp h2_actions
  have hei : (active h2).image e = active h2 :=
    iter_image orbitG (active h2) (active_image_of_OK h2 h2auto h2perm_ok hA.1) j
  have hd : AdjEquiv orbitD := graphPerm_adj _ _
  have hdi : (active h2).image orbitD = active h2 := active_image_of_OK h2 dualSwap dualSwap_ok hA.2
  rcases Bool.or_eq_true_iff.mp hj with J | J
  · refine ⟨e, id, he, hei, (fun _ _ h => h), iter_color j, ?_⟩
    apply Fin.ext
    rw [iter_val]
    exact beq_iff_eq.mp J
  · refine ⟨e.trans orbitD, Bool.not, adjEquiv_trans he hd, ?_, ?_, ?_, ?_⟩
    · change (active h2).image ((orbitD : V → V) ∘ (e : V → V)) = active h2
      rw [← Finset.image_image, hei, hdi]
    · intro a b h
      cases a <;> cases b <;> simp_all
    · intro u
      change point (dualSwap (e u).val) = !(point u.val)
      rw [dual_color, iter_color]
    · apply Fin.ext
      change dualSwap (e (3 : V)).val = v.val
      rw [iter_val]
      exact beq_iff_eq.mp J

end Reflection

namespace Reflection

open Numeric

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checkedSample : checkFirst 3 = true := by decide +kernel

theorem allFive : Stage.AllFive := by
  apply h5_all_of_orbit (3 : V) checkedSample (by decide +kernel)
  intro v hv
  obtain ⟨e, φ, ha, hi, hφ, hc, he⟩ := h2Equiv v hv
  exact ⟨e,ha,hi,he,φ,hφ,hc⟩

theorem pairAll : Stage.PairOrbit := by
  intro p l hp hl hn
  apply pairEquiv p l (by simp [point,hp]) (by simp [point, not_lt_of_ge hl]) hn

end Reflection

end PEqualNP.Outside.L_meta_17525_aux.Plane

namespace PEqualNP.Outside.L_meta_17525_aux

theorem Plane :
have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size ≤ (20 : ℕ) → (19 : ℕ) ≤ x2.size ∧ (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard + (16 : ℕ) ≤ x2.size) ∧ ∀ (x9 x10 : Fin (42 : ℕ)), ↑x9 < (21 : ℕ) → (21 : ℕ) ≤ ↑x10 → ¬x1.Adj x9 x10 → {x14 : Fin x2.size | x9 ∈ x2.leftVars x14 ∨ x9 ∈ x2.rightVars x14 ∨ x10 ∈ x2.leftVars x14 ∨ x10 ∈ x2.rightVars x14}.ncard + (14 : ℕ) ≤ x2.size
 := by
  exact PEqualNP.Outside.L_meta_17525_aux.Plane.Reflection.Stage.from_certified_orbits
    PEqualNP.Outside.L_meta_17525_aux.Plane.Reflection.singleEquiv
    PEqualNP.Outside.L_meta_17525_aux.Plane.Reflection.pairAll
    PEqualNP.Outside.L_meta_17525_aux.Plane.Reflection.allFive

end PEqualNP.Outside.L_meta_17525_aux

namespace PEqualNP.Outside.L_meta_17525_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

abbrev rel (a b : Fin 42) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ [0, 5, 7, 17, 20]

def plane : SimpleGraph (Fin 42) := SimpleGraph.fromRel rel

def edges : List (Nat × Nat) :=
  (List.range 21).flatMap (fun j => [(j, 21 + (j + 20) % 21), (j, 21 + j),
    (j, 21 + (j + 5) % 21), (j, 21 + (j + 7) % 21), (j, 21 + (j + 17) % 21)])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem edges_eq : ∀ a b : Fin 42,
    (a ≠ b ∧ (rel a b ∨ rel b a)) ↔ (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges := by
  decide +kernel

theorem bound (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 42, (a.val,b.val) ∈ edges ∧ x a = true ∧ x b = true)
    (hu : {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard ≤ 18) : False := by
  classical
  have hzero : circuitFun 42 C (fun i => decide (i ∈ (∅ : Finset (Fin 42)))) = false := by
    change C.eval (List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42))))) = false
    cases h : C.eval (List.ofFn (fun i : Fin 42 => decide (i ∈ (∅ : Finset (Fin 42))))) with
    | false => rfl
    | true =>
      obtain ⟨a,b,he,ha,hb⟩ := (hc _).mp h
      simp at ha
  obtain ⟨D,hw,hs,he⟩ := Convert C hm ⟨∅,hzero⟩
  obtain ⟨S,hSD,hSE,hsing,hdis,hSW⟩ := Plane.ActiveNorm.normalizeSingleton 42 D
  have hcomp : S.Computes plane := by
    intro U
    rw [hSE, he]
    change C.eval (List.ofFn (fun i : Fin 42 => decide (i ∈ U))) = true ↔ _
    rw [hc]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, (edges_eq a b).mpr (Or.inl hab)⟩
    · rintro ⟨a,ha,b,hb,hab⟩
      rcases (edges_eq a b).mp hab with h | h
      · exact ⟨a,b,h,decide_eq_true ha,decide_eq_true hb⟩
      · exact ⟨b,a,h,decide_eq_true hb,decide_eq_true ha⟩
  have h0 := Plane.Pin.outVars_empty S plane hcomp
  have hsize : D.size ≤ {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard := hs
  have h19 := (Plane S (hSW hw) hcomp h0 hsing hdis (by omega)).1
  omega

end PEqualNP.Outside.L_meta_17525_aux

theorem PEqualNP.Outside.L_meta_17525 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (11 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (12 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hm hc hlo hup
  exact False.elim (PEqualNP.Outside.L_meta_17525_aux.bound C hm hc (by omega))
