import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.PairClean

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split <;> rename_i hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split <;> rename_i h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

lemma gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

lemma cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            rcases hitA with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            rcases hitB with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

lemma edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

lemma edge_finset_gate_bound (n k N : ℕ) (G J : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel J.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, J.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    J.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : J.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : J.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : J.Adj u v := J.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      J.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

lemma total_from_model (n k N r L : ℕ) (G J : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel J.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, J.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, J.Adj u v → u ∈ T ∨ v ∈ T) ∧
      J.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : J.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G J S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r J S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

lemma pairCleanSubgraphBound (n : ℕ) (G J : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel J.Adj]
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate) (out : ℕ)
    (ops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (single : ∀ u : Fin n, (Circuit.mk gs out).eval (List.ofFn (singletonBits u)) = false)
    (hits : ∀ u v : Fin n, J.Adj u v →
      (Circuit.mk gs out).eval (List.ofFn (pairBits u v)) = true)
    (clean : ∀ (i : Fin gs.length) (x : Fin n → Bool),
      (x = (fun _ => false) ∨ (∃ u : Fin n, x = singletonBits u) ∨
        (∃ u v : Fin n, x = pairBits u v)) →
      (gs.get i).op = GateOp.and →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD (n + i.val) false = true → edgeTrue G x) :
    ∃ T : Finset (Fin n), (∀ u v, J.Adj u v → u ∈ T ∨ v ∈ T) ∧
      J.edgeFinset.card + T.card ≤ gs.length + 1 := by
  have hs : supports (n := n) gs (clampWire (n + gs.length) out) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh := (mem_support gs (clampWire (n + gs.length) out) u).mp hu
    rw [root_read, single u] at hh
    exact Bool.false_ne_true hh
  have hh : ∀ u v, J.Adj u v →
      posRead gs (clampWire (n + gs.length) out) (pairBits u v) = true := by
    intro u v huv
    rw [root_read]
    exact hits u v huv
  apply total_from_model n (n + 1) (n + 1 + gs.length)
    (clampWire (n + gs.length) out) gs.length G J
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    hs hh (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi, ha, Bool.false_eq_true, ite_false,
      Bool.or_eq_true] using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi, ha, ite_true, Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)

end PEqualNP.Outside.L_meta_2732_aux.PairClean


namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (cut replacement i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then replacement else i - 1

def gate (cut replacement : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire cut replacement)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def erased (n : ℕ) (pre post : List Gate) (out replacement : ℕ) : Circuit :=
  ⟨pre ++ post.map (gate (n + pre.length) replacement), wire (n + pre.length) replacement out⟩

lemma run_append (pre post : List Gate) (w : List Bool) :
    run (pre ++ post) w = run post (run pre w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma append_get (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (by omega)]
  · subst i
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), ite_eq_right (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma initial (w : List Bool) (replacement i : ℕ) :
    w.getD (wire w.length replacement i) false =
      (w ++ [w.getD replacement false]).getD i false := by
  by_cases hi : i < w.length
  · rw [wire, ite_eq_left hi, List.getD_append _ _ _ _ hi]
  · by_cases he : i = w.length
    · subst i
      simp [wire]
    · have hi' : w.length + 1 ≤ i := by omega
      simp only [wire, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

lemma wire_at (cut replacement i m : ℕ) (hc : cut ≤ m) (hr : replacement ≠ m) :
    wire cut replacement i = m ↔ i = m + 1 := by
  by_cases hi : i < cut
  · simp only [wire, ite_eq_left hi]
    omega
  · by_cases he : i = cut
    · simp only [wire, ite_eq_right hi, ite_eq_left he]
      omega
    · simp only [wire, ite_eq_right hi, ite_eq_right he]
      omega

lemma fold (cut replacement : ℕ) (gs : List Gate) :
    ∀ old new : List Bool, cut < old.length → old.length = new.length + 1 →
      (replacement < cut ∨ new.length + gs.length ≤ replacement) →
      (∀ i, new.getD (wire cut replacement i) false = old.getD i false) →
      ∀ i, (run (gs.map (gate cut replacement)) new).getD (wire cut replacement i) false =
        (run gs old).getD i false := by
  induction gs with
  | nil => intro old new hc hl hr hv; exact hv
  | cons g gs ih =>
    intro old new hc hl hr hv
    let b := g.op.eval (g.inputs.map fun i => old.getD i false)
    have hb : (gate cut replacement g).op.eval
        ((gate cut replacement g).inputs.map fun i => new.getD i false) = b := by
      simp only [gate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hv i
    have hr' : replacement ≠ new.length := by
      rcases hr with hr | hr
      · omega
      · simp only [List.length_cons] at hr
        omega
    have hc' : cut ≤ new.length := by omega
    have step : ∀ i, (new ++ [b]).getD (wire cut replacement i) false =
        (old ++ [b]).getD i false := by
      intro i
      rw [append_get, append_get, hl]
      simp only [wire_at cut replacement i new.length hc' hr', hv i]
    have hr'' : replacement < cut ∨ (new ++ [b]).length + gs.length ≤ replacement := by
      rcases hr with hr | hr
      · exact Or.inl hr
      · right
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega
    have h := ih (old ++ [b]) (new ++ [b]) (by simp; omega) (by simp [hl]) hr'' step
    simpa only [run, List.map_cons, List.foldl_cons, hb] using h

lemma eval (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ)
    (safe : replacement < n + pre.length ∨ n + pre.length + post.length ≤ replacement)
    (x : List Bool) (hx : x.length = n)
    (aliases : g.op.eval (g.inputs.map fun i => (run pre x).getD i false) =
      (run pre x).getD replacement false) :
    (erased n pre post out replacement).eval x = (Circuit.mk (pre ++ g :: post) out).eval x := by
  let w := run pre x
  have hw : w.length = n + pre.length := by simp [w, run_length, hx]
  change (run (pre ++ post.map (gate (n + pre.length) replacement)) x).getD
      (wire (n + pre.length) replacement out) false = (run (pre ++ g :: post) x).getD out false
  rw [run_append, run_append]
  change (run (post.map (gate (n + pre.length) replacement)) w).getD
      (wire (n + pre.length) replacement out) false =
    (run post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD out false
  rw [aliases]
  apply fold (n + pre.length) replacement post (w ++ [w.getD replacement false]) w
  · simp [hw]
  · simp
  · simpa only [hw] using safe
  · intro i
    simpa only [hw] using initial w replacement i

lemma size (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ) :
    (erased n pre post out replacement).size + 1 = (Circuit.mk (pre ++ g :: post) out).size := by
  simp [erased, Circuit.size]
  omega

lemma monotone (n : ℕ) (pre post : List Gate) (g : Gate) (out replacement : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out)) :
    Monotone2 (erased n pre post out replacement) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h a (List.mem_append_left _ ha)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have h' := h b (List.mem_append_right _ (List.mem_cons_of_mem g hb))
    exact ⟨h'.1, by simpa [gate] using h'.2⟩

lemma delete_zero (n : ℕ) (pre post : List Gate) (out : ℕ) (x : List Bool) (hx : x.length = n) :
    (erased n pre post out (n + pre.length + post.length)).eval x =
      (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: post) out).eval x := by
  apply eval n pre post ⟨GateOp.or, []⟩ out (n + pre.length + post.length) (Or.inr le_rfl) x hx
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  symm
  apply List.getD_eq_default
  rw [run_length, hx]
  omega

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def normalizedRef (cut limit i : ℕ) : ℕ := if i < cut then i else limit

lemma normalized_safe (cut limit i : ℕ) :
    normalizedRef cut limit i < cut ∨ limit ≤ normalizedRef cut limit i := by
  by_cases hi : i < cut <;> simp [normalizedRef, hi]

lemma normalized_get (cut limit i : ℕ) (hl : cut ≤ limit) (w : List Bool)
    (hw : w.length = cut) : w.getD (normalizedRef cut limit i) false = w.getD i false := by
  by_cases hi : i < cut
  · simp [normalizedRef, hi]
  · rw [normalizedRef, ite_eq_right hi,
      List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma alias_invalid (cut limit z : ℕ) (g : Gate) (hl : cut ≤ limit)
    (ho : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hz : z ∈ g.inputs) (hcut : cut ≤ z) :
    ∃ replacement, (replacement < cut ∨ limit ≤ replacement) ∧
      ∀ w : List Bool, w.length = cut →
        g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD replacement false := by
  rcases g with ⟨op, ins⟩
  rcases ho with rfl | rfl
  · refine ⟨limit, Or.inr le_rfl, ?_⟩
    intro w hw
    rw [List.getD_eq_default _ _ (by omega)]
    change (ins.map fun i => w.getD i false).all id = false
    apply List.all_eq_false.mpr
    refine ⟨w.getD z false, List.mem_map_of_mem hz, ?_⟩
    have hzero : w.getD z false = false := List.getD_eq_default _ _ (by omega)
    rw [hzero]
    decide
  · cases ins with
    | nil => simp at hz
    | cons a ins =>
      cases ins with
      | nil =>
        refine ⟨normalizedRef cut limit a, normalized_safe cut limit a, ?_⟩
        intro w hw
        rw [normalized_get cut limit a hl w hw]
        simp [GateOp.eval]
      | cons b ins =>
        have ht : ins = [] := by
          have ht : ins.length = 0 := by
            simp only [List.length_cons] at hlen
            omega
          simpa using ht
        subst ins
        have hz' : z = a ∨ z = b := by simpa using hz
        rcases hz' with hz' | hz'
        · refine ⟨normalizedRef cut limit b, normalized_safe cut limit b, ?_⟩
          intro w hw
          rw [normalized_get cut limit b hl w hw]
          have ha : w.getD a false = false := List.getD_eq_default _ _ (by omega)
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
          change (w.getD a false || (w.getD b false || false)) = w.getD b false
          rw [ha]
          simp
        · refine ⟨normalizedRef cut limit a, normalized_safe cut limit a, ?_⟩
          intro w hw
          rw [normalized_get cut limit a hl w hw]
          have hb : w.getD b false = false := List.getD_eq_default _ _ (by omega)
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
          change (w.getD a false || (w.getD b false || false)) = w.getD a false
          rw [hb]
          simp

lemma delete_invalid_input (n : ℕ) (pre post : List Gate) (g : Gate) (out z : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (hz : z ∈ g.inputs) (hcut : n + pre.length ≤ z) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = (Circuit.mk (pre ++ g :: post) out).size ∧
      ∀ x : List Bool, x.length = n → D.eval x = (Circuit.mk (pre ++ g :: post) out).eval x := by
  have hg := h g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  obtain ⟨replacement, safe, halias⟩ := alias_invalid (n + pre.length)
    (n + pre.length + post.length) z g (by omega) hop hg.2 hz hcut
  refine ⟨erased n pre post out replacement, monotone n pre post g out replacement h,
    size n pre post g out replacement, ?_⟩
  intro x hx
  apply eval n pre post g out replacement safe x hx
  exact halias (run pre x) (by simp [run_length, hx])

lemma delete_zero_consumer (n : ℕ) (pre between after : List Gate) (dead consumer : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out))
    (uses : n + pre.length ∈ consumer.inputs) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 2 = (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out).size ∧
      ∀ x : List Bool, x.length = n →
        D.eval x = (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: (between ++ consumer :: after)) out).eval x := by
  let post := between ++ consumer :: after
  let cut := n + pre.length
  let limit := n + pre.length + post.length
  let E := erased n pre post out limit
  let pre' := pre ++ between.map (gate cut limit)
  let consumer' := gate cut limit consumer
  let after' := after.map (gate cut limit)
  have he : E = Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out) := by
    simp [E, erased, pre', consumer', after', post, cut, List.map_append, List.append_assoc]
  have hE : Monotone2 E := monotone n pre post dead out limit h
  have hE' : Monotone2 (Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out)) := by
    rw [← he]
    exact hE
  have huses : limit ∈ consumer'.inputs := by
    change limit ∈ consumer.inputs.map (wire cut limit)
    have hw : wire cut limit cut = limit := by simp [wire]
    have hm := List.mem_map_of_mem (f := wire cut limit) uses
    change wire cut limit cut ∈ consumer.inputs.map (wire cut limit) at hm
    simpa only [hw] using hm
  have hinvalid : n + pre'.length ≤ limit := by
    simp [pre', limit, post]
    omega
  obtain ⟨D, hD, hs, hv⟩ := delete_invalid_input n pre' after' consumer'
    (wire cut limit out) limit hE' huses hinvalid
  have hsE : E.size + 1 = (Circuit.mk (pre ++ dead :: post) out).size :=
    size n pre post dead out limit
  rw [← he] at hs
  refine ⟨D, hD, ?_, ?_⟩
  · change D.size + 2 = (Circuit.mk (pre ++ dead :: post) out).size
    omega
  intro x hx
  have hv' : D.eval x = E.eval x := by simpa only [← he] using hv x hx
  exact hv'.trans (delete_zero n pre post out x hx)

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gate_true_mono (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ → Bool) (hab : ∀ i, a i = true → b i = true)
    (ha : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
  rcases ho with ho | ho
  · rw [ho] at ha ⊢
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hab i (List.all_eq_true.mp ha _ (List.mem_map_of_mem hi))
  · rw [ho] at ha ⊢
    obtain ⟨v, hv, hvt⟩ := List.any_eq_true.mp ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact List.any_eq_true.mpr ⟨b i, List.mem_map_of_mem hi, hab i hvt⟩

lemma run_true_mono (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hl : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    let av := g.op.eval (g.inputs.map fun i => a.getD i false)
    let bv := g.op.eval (g.inputs.map fun i => b.getD i false)
    have hv : av = true → bv = true := gate_true_mono g (ops g List.mem_cons_self) _ _ hab
    have next : ∀ i, (a ++ [av]).getD i false = true →
        (b ++ [bv]).getD i false = true := by
      intro i
      rw [append_get, append_get, hl]
      by_cases hi : i = b.length
      · simpa only [hi, ite_true] using hv
      · simpa only [hi, ite_false] using hab i
    exact ih (fun g hg => ops g (List.mem_cons_of_mem _ hg))
      (a ++ [av]) (b ++ [bv]) (by simp [hl]) next

lemma zero_forcing (pre post : List Gate) (g : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out)) (x : List Bool) :
    ∀ i, (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD i false = true →
      (run (pre ++ g :: post) x).getD i false = true := by
  rw [run_append, run_append]
  let w := run pre x
  change ∀ i, (run post (w ++ [false])).getD i false = true →
    (run post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true
  apply run_true_mono post
  · intro a ha
    have hop := (h a (List.mem_append_right _ (List.mem_cons_of_mem g ha))).1
    simpa using hop
  · simp
  · intro i
    rw [append_get, append_get]
    by_cases hi : i = w.length
    · simp only [hi, ite_true, Bool.false_eq_true, false_implies]
    · simp only [hi, ite_false]
      exact id

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma erased_gate_index (n : ℕ) (pre post : List Gate) (dead : Gate) (out replacement : ℕ)
    (i : Fin (erased n pre post out replacement).gates.length) :
    ∃ j : Fin (pre ++ dead :: post).length, j.val ≠ pre.length ∧
      ((pre ++ dead :: post).get j).op =
        ((erased n pre post out replacement).gates.get i).op ∧
      wire (n + pre.length) replacement (n + j.val) = n + i.val := by
  have hi : i.val < pre.length + post.length := by
    simpa only [erased, List.length_append, List.length_map] using i.isLt
  by_cases hp : i.val < pre.length
  · let j : Fin (pre ++ dead :: post).length := ⟨i.val, by simp; omega⟩
    refine ⟨j, by dsimp [j]; omega, ?_, ?_⟩
    · have oldbound : i.val < (pre ++ dead :: post).length := j.isLt
      have newbound : i.val < (pre ++ post.map (gate (n + pre.length) replacement)).length := i.isLt
      change ((pre ++ dead :: post)[i.val]).op =
        ((pre ++ post.map (gate (n + pre.length) replacement))[i.val]).op
      rw [List.getElem_append_left hp, List.getElem_append_left hp]
    · simp only [j, wire, ite_eq_left (show n + i.val < n + pre.length by omega)]
  · have hp' : pre.length ≤ i.val := by omega
    let j : Fin (pre ++ dead :: post).length := ⟨i.val + 1, by simp; omega⟩
    refine ⟨j, by dsimp [j]; omega, ?_, ?_⟩
    · have oldbound : i.val + 1 < (pre ++ dead :: post).length := j.isLt
      have newbound : i.val < (pre ++ post.map (gate (n + pre.length) replacement)).length := i.isLt
      change ((pre ++ dead :: post)[i.val + 1]).op =
        ((pre ++ post.map (gate (n + pre.length) replacement))[i.val]).op
      rw [List.getElem_append_right (show pre.length ≤ i.val + 1 by omega),
        List.getElem_append_right hp']
      have he : i.val + 1 - pre.length = (i.val - pre.length) + 1 := by omega
      simp only [he, List.getElem_cons_succ, List.getElem_map, gate]
    · simp only [j, wire, ite_eq_right (show ¬ n + (i.val + 1) < n + pre.length by omega),
        ite_eq_right (show n + (i.val + 1) ≠ n + pre.length by omega)]
      omega

lemma erase_preserves_and_false (n : ℕ) (pre post : List Gate) (dead : Gate)
    (out replacement : ℕ)
    (safe : replacement < n + pre.length ∨ n + pre.length + post.length ≤ replacement)
    (x : List Bool) (hx : x.length = n)
    (aliases : dead.op.eval (dead.inputs.map fun i => (run pre x).getD i false) =
      (run pre x).getD replacement false)
    (clean : ∀ j : Fin (pre ++ dead :: post).length, j.val ≠ pre.length →
      ((pre ++ dead :: post).get j).op = GateOp.and →
      (run (pre ++ dead :: post) x).getD (n + j.val) false = false) :
    ∀ i : Fin (erased n pre post out replacement).gates.length,
      ((erased n pre post out replacement).gates.get i).op = GateOp.and →
      (run (erased n pre post out replacement).gates x).getD (n + i.val) false = false := by
  intro i hi
  obtain ⟨j, hj, hop, hw⟩ := erased_gate_index n pre post dead out replacement i
  have he := eval n pre post dead (n + j.val) replacement safe x hx aliases
  change (run (erased n pre post out replacement).gates x).getD
    (wire (n + pre.length) replacement (n + j.val)) false =
      (run (pre ++ dead :: post) x).getD (n + j.val) false at he
  rw [hw] at he
  exact he.trans (clean j hj (hop.trans hi))

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma zero_forcing_preserves_clean (pre post : List Gate) (g : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out)) (x : List Bool)
    (clean : ∀ j : Fin (pre ++ g :: post).length, j.val ≠ pre.length →
      ((pre ++ g :: post).get j).op = GateOp.and →
      (run (pre ++ g :: post) x).getD (x.length + j.val) false = false) :
    ∀ i : Fin (pre ++ ⟨GateOp.or, []⟩ :: post).length,
      ((pre ++ ⟨GateOp.or, []⟩ :: post).get i).op = GateOp.and →
      (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD (x.length + i.val) false = false := by
  intro i hop
  let j : Fin (pre ++ g :: post).length := ⟨i.val, by simpa using i.isLt⟩
  have oldbound : i.val < (pre ++ g :: post).length := j.isLt
  have hij : j.val ≠ pre.length ∧ ((pre ++ g :: post).get j).op = GateOp.and := by
    by_cases hp : i.val < pre.length
    · refine ⟨by dsimp [j]; omega, ?_⟩
      change ((pre ++ g :: post)[i.val]).op = GateOp.and
      change ((pre ++ ⟨GateOp.or, []⟩ :: post)[i.val]).op = GateOp.and at hop
      rw [List.getElem_append_left hp] at hop ⊢
      exact hop
    · have hp' : pre.length ≤ i.val := by omega
      have hneq : i.val ≠ pre.length := by
        intro he
        have hop' := hop
        simp only [List.get_eq_getElem, he, List.getElem_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem_cons_zero] at hop'
        cases hop'
      refine ⟨hneq, ?_⟩
      change ((pre ++ g :: post)[i.val]).op = GateOp.and
      change ((pre ++ ⟨GateOp.or, []⟩ :: post)[i.val]).op = GateOp.and at hop
      rw [List.getElem_append_right hp', List.getElem_cons] at hop ⊢
      rw [dite_eq_right (show i.val - pre.length ≠ 0 by omega)] at hop ⊢
      exact hop
  have hfalse := clean j hij.1 hij.2
  cases he : (run (pre ++ ⟨GateOp.or, []⟩ :: post) x).getD (x.length + i.val) false with
  | false => rfl
  | true =>
    have ht := zero_forcing pre post g out h x (x.length + i.val) he
    have hf : (run (pre ++ g :: post) x).getD (x.length + i.val) false = false := hfalse
    rw [hf] at ht
    cases ht

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def AndFalse (gs : List Gate) (x : List Bool) : Prop :=
  ∀ i : Fin gs.length, (gs.get i).op = GateOp.and →
    (run gs x).getD (x.length + i.val) false = false

lemma delete_invalid_input_clean (n : ℕ) (pre post : List Gate) (g : Gate) (out z : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (hz : z ∈ g.inputs) (hcut : n + pre.length ≤ z) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = (Circuit.mk (pre ++ g :: post) out).size ∧
      ∀ x : List Bool, x.length = n →
        D.eval x = (Circuit.mk (pre ++ g :: post) out).eval x ∧
        (AndFalse (pre ++ g :: post) x → AndFalse D.gates x) := by
  have hg := h g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  obtain ⟨replacement, safe, halias⟩ := alias_invalid (n + pre.length)
    (n + pre.length + post.length) z g (by omega) hop hg.2 hz hcut
  refine ⟨erased n pre post out replacement, monotone n pre post g out replacement h,
    size n pre post g out replacement, ?_⟩
  intro x hx
  have ha := halias (run pre x) (by simp [run_length, hx])
  refine ⟨eval n pre post g out replacement safe x hx ha, ?_⟩
  intro clean
  have hc := erase_preserves_and_false n pre post g out replacement safe x hx ha
    (fun j _ hop => by simpa only [hx] using clean j hop)
  simpa only [AndFalse, hx] using hc

lemma prune_zero_consumer (n : ℕ) (pre between after : List Gate) (dead consumer : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out))
    (uses : n + pre.length ∈ consumer.inputs) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 2 = (Circuit.mk (pre ++ dead :: (between ++ consumer :: after)) out).size ∧
      ∀ x : List Bool, x.length = n →
        D.eval x = (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: (between ++ consumer :: after)) out).eval x ∧
        ((∀ j : Fin (pre ++ dead :: (between ++ consumer :: after)).length,
          j.val ≠ pre.length →
          ((pre ++ dead :: (between ++ consumer :: after)).get j).op = GateOp.and →
          (run (pre ++ dead :: (between ++ consumer :: after)) x).getD (n + j.val) false = false) →
          AndFalse D.gates x) := by
  let post := between ++ consumer :: after
  let cut := n + pre.length
  let limit := n + pre.length + post.length
  let E := erased n pre post out limit
  let pre' := pre ++ between.map (gate cut limit)
  let consumer' := gate cut limit consumer
  let after' := after.map (gate cut limit)
  have he : E = Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out) := by
    simp [E, erased, pre', consumer', after', post, cut, List.map_append, List.append_assoc]
  have hE : Monotone2 E := monotone n pre post dead out limit h
  have hE' : Monotone2 (Circuit.mk (pre' ++ consumer' :: after') (wire cut limit out)) := by
    rw [← he]
    exact hE
  have huses : limit ∈ consumer'.inputs := by
    change limit ∈ consumer.inputs.map (wire cut limit)
    have hw : wire cut limit cut = limit := by simp [wire]
    have hm := List.mem_map_of_mem (f := wire cut limit) uses
    change wire cut limit cut ∈ consumer.inputs.map (wire cut limit) at hm
    simpa only [hw] using hm
  have hinvalid : n + pre'.length ≤ limit := by
    simp [pre', limit, post]
    omega
  obtain ⟨D, hD, hs, hv⟩ := delete_invalid_input_clean n pre' after' consumer'
    (wire cut limit out) limit hE' huses hinvalid
  have hsE : E.size + 1 = (Circuit.mk (pre ++ dead :: post) out).size :=
    size n pre post dead out limit
  rw [← he] at hs
  refine ⟨D, hD, ?_, ?_⟩
  · change D.size + 2 = (Circuit.mk (pre ++ dead :: post) out).size
    omega
  · intro x hx
    obtain ⟨hval, hclean⟩ := hv x hx
    have hv' : D.eval x = E.eval x := by simpa only [← he] using hval
    refine ⟨hv'.trans (delete_zero n pre post out x hx), ?_⟩
    intro oldclean
    have forcedclean := zero_forcing_preserves_clean pre post dead out h x
      (fun j hj hop => by simpa only [hx] using oldclean j hj hop)
    have ha : GateOp.or.eval (([] : List ℕ).map fun i => (run pre x).getD i false) =
        (run pre x).getD limit false := by
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      apply List.getD_eq_default
      simp only [run_length, hx]
      dsimp [limit]
      omega
    have hEC := erase_preserves_and_false n pre post ⟨GateOp.or, []⟩ out limit
      (Or.inr le_rfl) x hx ha (fun j _ hop => by simpa only [hx] using forcedclean j hop)
    have hEC' : AndFalse E.gates x := by simpa only [AndFalse, hx] using hEC
    apply hclean
    simpa only [he] using hEC'

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma prune_zero (n : ℕ) (pre post : List Gate) (dead : Gate) (out : ℕ)
    (h : Monotone2 (Circuit.mk (pre ++ dead :: post) out)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = (Circuit.mk (pre ++ dead :: post) out).size ∧
      ∀ x : List Bool, x.length = n →
        D.eval x = (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: post) out).eval x ∧
        ((∀ j : Fin (pre ++ dead :: post).length, j.val ≠ pre.length →
          ((pre ++ dead :: post).get j).op = GateOp.and →
          (run (pre ++ dead :: post) x).getD (n + j.val) false = false) → AndFalse D.gates x) := by
  let limit := n + pre.length + post.length
  refine ⟨erased n pre post out limit, monotone n pre post dead out limit h,
    size n pre post dead out limit, ?_⟩
  intro x hx
  refine ⟨delete_zero n pre post out x hx, ?_⟩
  intro oldclean
  have forcedclean := zero_forcing_preserves_clean pre post dead out h x
    (fun j hj hop => by simpa only [hx] using oldclean j hj hop)
  have ha : GateOp.or.eval (([] : List ℕ).map fun i => (run pre x).getD i false) =
      (run pre x).getD limit false := by
    simp only [GateOp.eval, List.map_nil, List.any_nil]
    symm
    apply List.getD_eq_default
    simp only [run_length, hx]
    dsimp [limit]
    omega
  have hc := erase_preserves_and_false n pre post ⟨GateOp.or, []⟩ out limit
    (Or.inr le_rfl) x hx ha (fun j _ hop => by simpa only [hx] using forcedclean j hop)
  simpa only [AndFalse, hx] using hc

end PEqualNP.Outside.L_meta_2732_aux.EraseWire

namespace PEqualNP.Outside.L_meta_2732_aux.EraseWire

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PairClean

lemma zeroed_accounting (n : ℕ) (G J : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel J.Adj]
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (pre post : List Gate) (dead : Gate) (out : ℕ)
    (ops : Monotone2 (Circuit.mk (pre ++ dead :: post) out))
    (single : ∀ u : Fin n, (Circuit.mk (pre ++ dead :: post) out).eval
      (List.ofFn (singletonBits u)) = false)
    (hits : ∀ u v : Fin n, J.Adj u v →
      (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: post) out).eval
        (List.ofFn (pairBits u v)) = true)
    (clean : ∀ (i : Fin (pre ++ dead :: post).length)
      (x : Fin n → Bool), i.val ≠ pre.length →
      (x = (fun _ => false) ∨ (∃ u : Fin n, x = singletonBits u) ∨
        (∃ u v : Fin n, x = pairBits u v)) →
      ((pre ++ dead :: post).get i).op = GateOp.and →
      (run (pre ++ dead :: post) (List.ofFn x)).getD
        (n + i.val) false = true → edgeTrue G x) :
    ∃ T : Finset (Fin n), (∀ u v, J.Adj u v → u ∈ T ∨ v ∈ T) ∧
      J.edgeFinset.card + T.card ≤
        (Circuit.mk (pre ++ dead :: post) out).size := by
  obtain ⟨D, hD, hsize, hprops⟩ := prune_zero n pre post dead out ops
  have dops : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    simpa using hD g hg
  have dsingle : ∀ u : Fin n, D.eval (List.ofFn (singletonBits u)) = false := by
    intro u
    let x := List.ofFn (singletonBits u)
    have hx : x.length = n := by simp [x]
    have he := (hprops x hx).1
    cases hd : D.eval x with
    | false => rfl
    | true =>
      have hf : (Circuit.mk (pre ++ ⟨GateOp.or, []⟩ :: post) out).eval x = true :=
        he.symm.trans hd
      have ht := zero_forcing pre post dead out ops x out hf
      have hs : (run (pre ++ dead :: post) x).getD out false = false := single u
      rw [hs] at ht
      cases ht
  have dhits : ∀ u v : Fin n, J.Adj u v → D.eval (List.ofFn (pairBits u v)) = true := by
    intro u v huv
    exact ((hprops (List.ofFn (pairBits u v)) (by simp)).1).trans (hits u v huv)
  have dclean : ∀ (i : Fin D.gates.length) (x : Fin n → Bool),
      (x = (fun _ => false) ∨ (∃ u : Fin n, x = singletonBits u) ∨
        (∃ u v : Fin n, x = pairBits u v)) →
      (D.gates.get i).op = GateOp.and →
      (Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (n + i.val) false = true → edgeTrue G x := by
    intro i x hx hop htrue
    by_contra hG
    have hc := (hprops (List.ofFn x) (by simp)).2
    have hd : AndFalse D.gates (List.ofFn x) := by
      apply hc
      intro j hj hjop
      cases he : (run (pre ++ dead :: post) (List.ofFn x)).getD
          (n + j.val) false with
      | false => rfl
      | true => exact (hG (clean j x hj hx hjop he)).elim
    have hf : (run D.gates (List.ofFn x)).getD (n + i.val) false = false := by
      simpa only [List.length_ofFn] using hd i hop
    change (run D.gates (List.ofFn x)).getD (n + i.val) false = true at htrue
    rw [hf] at htrue
    cases htrue
  obtain ⟨T, hT, hbound⟩ := pairCleanSubgraphBound n G J hc4 D.gates D.output dops dsingle dhits dclean
  refine ⟨T, hT, ?_⟩
  change D.gates.length + 1 = _ at hsize
  omega

end PEqualNP.Outside.L_meta_2732_aux.EraseWire
