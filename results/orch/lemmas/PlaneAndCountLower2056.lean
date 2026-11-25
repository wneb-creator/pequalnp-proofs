import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression

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

end PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression

theorem PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.compress (n : ℕ) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x3 : Finset (Fin (n : ℕ))), (PEqualNP.MetaComplexity.circuitFun (n : ℕ) x1 fun (x4 : Fin (n : ℕ)) => Decidable.decide (x4 ∈ x3)) = Bool.false) → ∃ (x4 : PEqualNP.AndCount.AndCountCircuit (n : ℕ)), x4.WellFormed ∧ x4.size ≤ Nat.card { x5 : Fin x1.gates.length // (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and } ∧ ∀ (x5 : Finset (Fin (n : ℕ))), x4.eval x5 = PEqualNP.MetaComplexity.circuitFun (n : ℕ) x1 fun (x6 : Fin (n : ℕ)) => Decidable.decide (x6 ∈ x5) := by
  intro C hmono hex
  obtain ⟨U0, hU0⟩ := hex
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.St n := ⟨List.ofFn (fun i : Fin n => some ({i}, ∅)), []⟩
  let s := C.gates.foldl PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.step s0
  have hinit : ∀ U : Finset (Fin n), PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.Inv U (List.ofFn fun x : Fin n => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < n
      · simp only [PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fv, PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fv_zero]
  have hinv : ∀ U : Finset (Fin n), PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.Inv U (C.gates.foldl PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.Fw (List.ofFn fun x : Fin n => decide (x ∈ U))) s :=
    fun U => PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin n), PEqualNP.MetaComplexity.circuitFun n C (fun x => decide (x ∈ U))
      = PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fv U (PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.rvals U s.rs) (PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fv] at this
  · have hG : ∀ j ∈ G, j < s.rs.length := PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.toACC s.rs V G, PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.wf s.rs hgood V G, ?_, ?_⟩
    · have h1 := PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.fold_rs C.gates s0
      have h2 : C.gates.countP PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.isAnd = Nat.card {x5 : Fin C.gates.length // (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        conv_lhs => rw [← List.ofFn_get C.gates]
        rw [List.countP_ofFn]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.isAnd_iff]
      change s.rs.length ≤ s0.rs.length + _ at h1
      have h0 : s0.rs.length = 0 := rfl
      show s.rs.length ≤ _
      omega
    · intro U
      rw [PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Compression.eval_eq U s.rs hgood V G hG, hfun U, hfo]
      rfl

namespace PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Selectors

/- The selector construction through complement_clause is copied from the checked
L_meta_958 auxiliary proof. The final cardinal bound is packaged here for research. -/

open PEqualNP.AndCount AndCountCircuit

variable {n : Nat}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩


def MaximalFalseSet (C : AndCountCircuit n) (I : Finset (Fin n)) : Prop :=
  C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

theorem maximal_false_count_le (C : AndCountCircuit n) :
    Nat.card {I : Finset (Fin n) // MaximalFalseSet C I} ≤ 2 ^ C.size := by
  classical
  let pick (I : {I : Finset (Fin n) // MaximalFalseSet C I}) := left C I.1
  have hpick : Function.Injective pick := by
    intro I J hij
    apply Subtype.ext
    apply Finset.ext
    intro u
    rw [complement_clause C I.1 I.2.1 I.2.2 u,
      complement_clause C J.1 J.2.1 J.2.2 u]
    change left C I.1 = left C J.1 at hij
    rw [hij]
  simpa using Fintype.card_le_of_injective pick hpick

end PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse.Selectors

namespace PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def MaximalFalseSet (n : Nat) (C : Circuit) (I : Finset (Fin n)) : Prop :=
  circuitFun n C (fun u => decide (u ∈ I)) = false ∧
    ∀ u, u ∉ I → circuitFun n C (fun v => decide (v ∈ insert u I)) = true

theorem maximal_false_count_le (n : Nat) (C : Circuit) (hC : Monotone2 C)
    (hfalse : ∃ I : Finset (Fin n), circuitFun n C (fun u => decide (u ∈ I)) = false) :
    Nat.card {I : Finset (Fin n) // MaximalFalseSet n C I} ≤
      2 ^ Nat.card {i : Fin C.gates.length // (C.gates.get i).op = GateOp.and} := by
  classical
  obtain ⟨D, hD, hsize, heval⟩ := Compression.compress n C hC hfalse
  have hp (I : Finset (Fin n)) : MaximalFalseSet n C I ↔ Selectors.MaximalFalseSet D I := by
    simp only [MaximalFalseSet, Selectors.MaximalFalseSet, heval]
  calc
    Nat.card {I : Finset (Fin n) // MaximalFalseSet n C I} =
        Nat.card {I : Finset (Fin n) // Selectors.MaximalFalseSet D I} :=
      Nat.card_congr (Equiv.subtypeEquivRight hp)
    _ ≤ 2 ^ D.size := Selectors.maximal_false_count_le D
    _ ≤ 2 ^ Nat.card {i : Fin C.gates.length // (C.gates.get i).op = GateOp.and} := by
      gcongr

end PEqualNP.Outside.L_meta_2056_aux.OrdinaryFalse


namespace PEqualNP.Outside.L_meta_2056_aux.MaskRows

def decode {n : ℕ} (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => m.testBit i.val

theorem mem_decode {n : ℕ} (m : ℕ) (i : Fin n) :
    i ∈ decode m ↔ m.testBit i.val = true := by simp [decode]

def maskEval {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) : Bool :=
  E.any fun e => m.testBit e.1.val && m.testBit e.2.val

def maskGood {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) : Bool :=
  !maskEval E m && (List.range n).all (fun i => m.testBit i || maskEval E (m ||| 2 ^ i))

def setEval {n : ℕ} (E : List (Fin n × Fin n)) (U : Finset (Fin n)) : Bool :=
  E.any fun e => decide (e.1 ∈ U) && decide (e.2 ∈ U)

theorem setEval_decode {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ) :
    setEval E (decode m) = maskEval E m := by
  simp [setEval, maskEval, mem_decode]

theorem decode_insert {n : ℕ} (m : ℕ) (i : Fin n) :
    decode (m ||| 2 ^ i.val) = insert i (decode m) := by
  ext j
  simp only [mem_decode, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
    decide_eq_true_eq, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (Fin.ext h.symm)
  · rintro (rfl | h)
    · exact Or.inr rfl
    · exact Or.inl h

theorem decode_injective_bounded {n : ℕ} {m k : ℕ}
    (hm : m < 2 ^ n) (hk : k < 2 ^ n)
    (he : (decode m : Finset (Fin n)) = decode k) : m = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hiff : m.testBit i = true ↔ k.testBit i = true := by
      simpa only [mem_decode] using
        (show (⟨i, hi⟩ : Fin n) ∈ decode m ↔ (⟨i, hi⟩ : Fin n) ∈ decode k by rw [he])
    cases hmi : m.testBit i <;> cases hki : k.testBit i <;> simp_all
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk hp)]

def MaximalFalseSet {n : ℕ} (f : Finset (Fin n) → Bool) (U : Finset (Fin n)) : Prop :=
  f U = false ∧ ∀ i, i ∉ U → f (insert i U) = true

theorem good_maximal {n : ℕ} (E : List (Fin n × Fin n)) (m : ℕ)
    (h : maskGood E m = true) : MaximalFalseSet (setEval E) (decode m) := by
  rw [maskGood, Bool.and_eq_true] at h
  have hm : maskEval E m = false := by
    cases he : maskEval E m
    · rfl
    · simp [he] at h
  refine ⟨by simpa only [setEval_decode] using hm, ?_⟩
  intro i hi
  have hbit : m.testBit i.val = false := by
    cases hb : m.testBit i.val
    · rfl
    · exact False.elim (hi ((mem_decode m i).2 hb))
  have hv := List.all_eq_true.mp h.2 i.val (List.mem_range.mpr i.isLt)
  rw [hbit, Bool.false_or] at hv
  rw [← decode_insert m i, setEval_decode]
  exact hv

theorem distinct_good_rows_lower_bound {n : ℕ} (E : List (Fin n × Fin n)) (M : List ℕ)
    (hn : M.Nodup) (hb : M.all (fun m => decide (m < 2 ^ n)) = true)
    (hg : M.all (maskGood E) = true)
    (f : Finset (Fin n) → Bool) (hf : ∀ U, f U = setEval E U) :
    M.length ≤ Nat.card {U : Finset (Fin n) // MaximalFalseSet f U} := by
  classical
  let embed (i : Fin M.length) : {U : Finset (Fin n) // MaximalFalseSet f U} :=
    ⟨decode (M.get i), by
      have hgood := good_maximal E (M.get i)
        (List.all_eq_true.mp hg (M.get i) (List.get_mem M i))
      simpa only [MaximalFalseSet, hf] using hgood⟩
  have hinj : Function.Injective embed := by
    intro i j he
    apply hn.injective_get
    have hi : M.get i < 2 ^ n := of_decide_eq_true
      (List.all_eq_true.mp hb (M.get i) (List.get_mem M i))
    have hj : M.get j < 2 ^ n := of_decide_eq_true
      (List.all_eq_true.mp hb (M.get j) (List.get_mem M j))
    exact decode_injective_bounded hi hj (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective embed hinj

end PEqualNP.Outside.L_meta_2056_aux.MaskRows


namespace PEqualNP.Outside.L_meta_2056_aux.PlaneFalse

def edges : List (Fin 26 × Fin 26) := [
  (0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
  (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
  (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
  (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
  (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
  (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
  (12, 14), (12, 15), (12, 17), (12, 23)
]

def maskEval (m : Nat) : Bool :=
  edges.any fun e => m.testBit e.1.val && m.testBit e.2.val

def maskGood (m : Nat) : Bool :=
  !maskEval m && (List.range 26).all (fun i => m.testBit i || maskEval (m ||| 2 ^ i))

def block0 : List Nat := [
  8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480,
  70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599,
  141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204,
  213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked0 : block0.all maskGood = true := by decide +kernel

def block1 : List Nat := [
  304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423,
  401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346,
  551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770,
  623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked1 : block1.all maskGood = true := by decide +kernel

def block2 : List Nat := [
  696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102,
  864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681,
  1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376,
  1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked2 : block2.all maskGood = true := by decide +kernel

def block3 : List Nat := [
  1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803,
  1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834,
  1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272,
  2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked3 : block3.all maskGood = true := by decide +kernel

def block4 : List Nat := [
  2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100,
  2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252,
  2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604,
  2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked4 : block4.all maskGood = true := by decide +kernel

def block5 : List Nat := [
  3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256,
  3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728,
  4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718,
  4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked5 : block5.all maskGood = true := by decide +kernel

def block6 : List Nat := [
  4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696,
  4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602,
  4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374,
  5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked6 : block6.all maskGood = true := by decide +kernel

def block7 : List Nat := [
  5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148,
  6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732,
  6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716,
  7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked7 : block7.all maskGood = true := by decide +kernel

def block8 : List Nat := [
  8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716,
  8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943,
  8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834,
  8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked8 : block8.all maskGood = true := by decide +kernel

def block9 : List Nat := [
  9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547,
  9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387,
  9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570,
  10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked9 : block9.all maskGood = true := by decide +kernel

def block10 : List Nat := [
  10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173,
  11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222,
  12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146,
  13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked10 : block10.all maskGood = true := by decide +kernel

def block11 : List Nat := [
  14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668,
  15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536,
  16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944,
  16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked11 : block11.all maskGood = true := by decide +kernel

def block12 : List Nat := [
  17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195,
  17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042,
  17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857,
  17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked12 : block12.all maskGood = true := by decide +kernel

def block13 : List Nat := [
  18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432,
  18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696,
  19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272,
  19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked13 : block13.all maskGood = true := by decide +kernel

def block14 : List Nat := [
  20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850,
  21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474,
  22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747,
  25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked14 : block14.all maskGood = true := by decide +kernel

def block15 : List Nat := [
  25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571,
  27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922,
  29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258,
  31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked15 : block15.all maskGood = true := by decide +kernel

def block16 : List Nat := [
  33595744
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem checked16 : block16.all maskGood = true := by decide +kernel

def masks : List Nat :=
  block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16

theorem masks_length : masks.length = 513 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem masks_nodup : masks.Nodup := by decide +kernel

theorem masks_good : masks.all maskGood = true := by
  simp only [masks, List.all_append, checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16]
  rfl

set_option maxRecDepth 10000 in
theorem masks_bound : masks.all (fun m => decide (m < 2 ^ 26)) = true := by decide +kernel

end PEqualNP.Outside.L_meta_2056_aux.PlaneFalse


namespace PEqualNP.Outside.L_meta_2056_aux.PlaneAndCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem edges_spec : ∀ p q : Fin 26,
    (p, q) ∈ PlaneFalse.edges ↔ p.val < 13 ∧ 13 ≤ q.val ∧
      (p.val + (q.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List Nat) := by
  decide +kernel

theorem ten_ands (C : Circuit) (hC : Monotone2 C)
    (hfun : ∀ U : Finset (Fin 26),
      circuitFun 26 C (fun u => decide (u ∈ U)) = MaskRows.setEval PlaneFalse.edges U) :
    10 ≤ Nat.card {i : Fin C.gates.length // (C.gates.get i).op = GateOp.and} := by
  classical
  have hg : PlaneFalse.masks.all (MaskRows.maskGood PlaneFalse.edges) = true :=
    PlaneFalse.masks_good
  have hl := MaskRows.distinct_good_rows_lower_bound PlaneFalse.edges PlaneFalse.masks
    PlaneFalse.masks_nodup PlaneFalse.masks_bound hg
    (fun U => circuitFun 26 C (fun u => decide (u ∈ U))) hfun
  have hlo : 513 ≤ Nat.card {U : Finset (Fin 26) // OrdinaryFalse.MaximalFalseSet 26 C U} := by
    simpa only [PlaneFalse.masks_length, MaskRows.MaximalFalseSet,
      OrdinaryFalse.MaximalFalseSet] using hl
  have hfalse : ∃ U : Finset (Fin 26),
      circuitFun 26 C (fun u => decide (u ∈ U)) = false := by
    refine ⟨∅, ?_⟩
    rw [hfun]
    rfl
  have hu := OrdinaryFalse.maximal_false_count_le 26 C hC hfalse
  have hpow := hlo.trans hu
  by_contra hn
  have ha : Nat.card {i : Fin C.gates.length // (C.gates.get i).op = GateOp.and} ≤ 9 := by omega
  have hp : 2 ^ Nat.card {i : Fin C.gates.length // (C.gates.get i).op = GateOp.and} ≤ 512 := by
    calc
      _ ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) ha
      _ = 512 := by decide
  omega

end PEqualNP.Outside.L_meta_2056_aux.PlaneAndCount
