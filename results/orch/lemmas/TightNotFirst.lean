import KernelFirstEngine

namespace PEqualNP.Outside.L_meta_10760_first

def LTR (m T q u : ℕ) (S : Set ℕ) : Prop :=
  ∃ k ≤ q, ∃ t ≤ u, k + u ≤ q + t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0

lemma LTR.mono {m T q u : ℕ} {S : Set ℕ} (h : LTR m T q u S)
    {q' u' : ℕ} {S' : Set ℕ} (hq : q ≤ q') (hu : u ≤ u') (hbu : q + u' ≤ q' + u) (hs : S ⊆ S') :
    LTR m T q' u' S' := by
  obtain ⟨k, hk, t, ht, hbal, S0, hS, hl⟩ := h
  exact ⟨k, hk.trans hq, t, ht.trans hu, by omega, S0, hS.trans hs, hl⟩

lemma LTR.done {m T : ℕ} {S : Set ℕ} (h : T ∈ S) : LTR m T 0 0 S :=
  ⟨0, by omega, 0, by omega, by omega, {T}, by simpa using h, .stop⟩

lemma LTR.un {m T q u a : ℕ} {S : Set ℕ} (ha : a ∈ S)
    (h : LTR m T q u (insert (a ^^^ m) S)) : LTR m T (q + 1) (u + 1) S := by
  obtain ⟨k, hk, t, ht, hbal, S1, hs, hl⟩ := h
  by_cases hg : a ^^^ m ∈ S1
  · refine ⟨k + 1, by omega, t + 1, by omega, by omega, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
    intro x hx
    simp at hx
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ha
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, t, by omega, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma LTR.bi {m T q u a b : ℕ} {d : Bool} {S : Set ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (h : LTR m T q u (insert (op d a b) S)) : LTR m T (q + 1) u S := by
  obtain ⟨k, hk, t, ht, hbal, S1, hs, hl⟩ := h
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab; rw [op_self] at hs
      exact ⟨k, by omega, t, ht, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
    refine ⟨k + 1, by omega, t, ht, by omega, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, t, ht, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩


lemma LTR.exact_counts {m T q u : ℕ} {S : Set ℕ}
    (hmin : ∀ k < q, ¬ Sol Z0 m T k S) (h : LTR m T q u S) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T q u S0 := by
  obtain ⟨k, hk, t, ht, hbal, S0, hS, hl⟩ := h
  have hkeq : k = q := by
    by_contra hne
    exact hmin k (by omega) (hl.sol.mono le_rfl hS)
  have hteq : t = u := by omega
  subst k
  subst t
  exact ⟨S0, hS, hl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

def ncount : List Gate → ℕ
  | [] => 0
  | g :: gs => (if isNot g then 1 else 0) + ncount gs

lemma ex_ltr {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → LTR m T gs.length (ncount gs) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact LTR.done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → LTR m T (g :: gs).length (ncount (g :: gs)) S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) (by simp only [ncount]; omega) (by simp only [List.length_cons, ncount]; split_ifs <;> omega) subset_rfl
    have go : LTR m T gs.length (ncount gs) (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => simpa [ncount, isNot] using LTR.bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => simpa [ncount, isNot] using LTR.bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: _ => simpa [ncount, isNot, Nat.add_comm] using LTR.un (rd i) go

lemma ncount_zero (gs : List Gate) (h : ∀ g ∈ gs, g.op ≠ GateOp.not) : ncount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g List.mem_cons_self
    have ht := ih fun x hx => h x (List.mem_cons_of_mem g hx)
    obtain ⟨o, l⟩ := g
    cases o <;> simp_all [ncount, isNot]

lemma ncount_one (gs : List Gate)
    (h : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) : ncount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have ht : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j := by
      intro i j hi hj
      have he := h i.succ j.succ hi hj
      exact Fin.succ_inj.mp he
    by_cases hg : g.op = GateOp.not
    · have hz : ncount gs = 0 := ncount_zero gs (by
        intro x hx hxnot
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
        have he := h ⟨0, by simp⟩ i.succ hg hxnot
        have hv := congrArg Fin.val he
        simp at hv)
      simp [ncount, isNot, hg, hz]
    · have hi := ih ht
      obtain ⟨o, l⟩ := g
      cases o <;> simp_all [ncount, isNot]


lemma ncount_pos_of_mem {gs : List Gate} {g : Gate} (hg : g ∈ gs)
    (hn : g.op = GateOp.not) : 0 < ncount gs := by
  induction gs with
  | nil => simp at hg
  | cons a gs ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [ncount, isNot, hn]
    · have := ih hg
      simp only [ncount]
      omega

lemma ncount_zero_iff (gs : List Gate) : ncount gs = 0 ↔ ∀ g ∈ gs, g.op ≠ GateOp.not := by
  constructor
  · intro hz g hg hn
    have := ncount_pos_of_mem hg hn
    omega
  · exact ncount_zero gs

lemma zero_not_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hn : ncount gs = 0) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hmem
  have hnot := (ncount_zero_iff gs).mp hn g hmem
  obtain ⟨hop, hlen⟩ := hg g hmem
  exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun h => False.elim (hnot h))), hlen⟩


lemma monotone_or_one (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ncount gs = 1 := by
  have hle := ncount_one gs hu
  by_cases hz : ncount gs = 0
  · exact Or.inl (zero_not_monotone gs hg hz)
  · exact Or.inr (by omega)

end circuit
section circuitMore
variable (m : ℕ)
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuitMore
def f (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 2 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 6 0) ||| (rawP.getD 2 0 &&& rawP.getD 6 0) ||| (rawP.getD 3 0 &&& rawP.getD 6 0) ||| (rawP.getD 5 0 &&& rawP.getD 6 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 7 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 7 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 7 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
lemma bridge_ltr (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = f y) :
    LTR (mz 0) (tz 0) D.size (ncount D.gates) (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 7 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_ltr (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩

end PEqualNP.Outside.L_meta_10760_first
