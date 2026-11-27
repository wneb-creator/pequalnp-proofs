import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_25806_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def brun (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma brun_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    brun (gs ++ [g]) x = brun gs x ++ [g.op ((brun gs x).getD g.left false) ((brun gs x).getD g.right false)] := by
  simp [brun, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma brun_length (gs : List BinaryGate) (x : List Bool) : (brun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [brun]
  | append_singleton gs g ih => rw [brun_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma brun_init (gs hs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (brun (gs ++ hs) x).getD i false = (brun gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, brun_snoc, getD_lt _ _ _ (by
      rw [brun_length, List.length_append]; omega), ih]

abbrev Ref := Bool ⊕ ((Bool → Bool) × ℕ)

def val (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr r => r.1 (w.getD r.2 false)

def idx : Ref → ℕ
  | .inl _ => 0
  | .inr r => r.2

def fn : Ref → Bool → Bool
  | .inl b => fun _ => b
  | .inr r => r.1

def Valid (N : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr r => r.2 < N

def lift (f : Bool → Bool) : Ref → Ref
  | .inl b => .inl (f b)
  | .inr r => .inr (f ∘ r.1, r.2)

lemma val_fn (w : List Bool) (r : Ref) : val w r = fn r (w.getD (idx r) false) := by
  cases r <;> rfl

lemma val_lift (w : List Bool) (f : Bool → Bool) (r : Ref) : val w (lift f r) = f (val w r) := by
  cases r <;> rfl

lemma valid_lift (N : ℕ) (f : Bool → Bool) (r : Ref) (h : Valid N r) : Valid N (lift f r) := by
  cases r <;> exact h

lemma valid_mono {N M : ℕ} (h : N ≤ M) (r : Ref) (hr : Valid N r) : Valid M r := by
  cases r with
  | inl b => trivial
  | inr r => exact lt_of_lt_of_le hr h

lemma val_ext (gs hs : List BinaryGate) (x : List Bool) (r : Ref)
    (hr : Valid (x.length + gs.length) r) :
    val (brun (gs ++ hs) x) r = val (brun gs x) r := by
  cases r with
  | inl b => rfl
  | inr r => simp only [val]; rw [brun_init _ _ _ _ hr]

lemma idx_valid (N : ℕ) (r : Ref) (hN : 0 < N) (hr : Valid N r) : idx r < N := by
  cases r with
  | inl b => exact hN
  | inr r => exact hr

def Back (N : ℕ) (gs : List BinaryGate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].left < N + j ∧ gs[j].right < N + j

lemma back_append (N : ℕ) (gs hs : List BinaryGate) (hg : Back N gs)
    (hh : ∀ g ∈ hs, g.left < N + gs.length ∧ g.right < N + gs.length) : Back N (gs ++ hs) := by
  intro j hj
  by_cases h : j < gs.length
  · rw [List.getElem_append_left h]
    exact hg j h
  · have hj' : j - gs.length < hs.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega)]
    have hm : hs[j - gs.length] ∈ hs := List.getElem_mem hj'
    obtain ⟨hl,hr⟩ := hh _ hm
    exact ⟨by omega,by omega⟩

lemma emit (N : ℕ) (hs : List BinaryGate) (g : Gate) (refs : ℕ → Ref)
    (hg : g.inputs.length ≤ 2) (hv : ∀ i, Valid (N + hs.length) (refs i)) :
    ∃ (r : Ref) (es : List BinaryGate), es.length ≤ (if g.inputs.length == 2 then 1 else 0) ∧
      Valid (N + hs.length + es.length) r ∧
      (0 < N → ∀ g ∈ es, g.left < N + hs.length ∧ g.right < N + hs.length) ∧
      ∀ x : List Bool, x.length = N →
        val (brun (hs ++ es) x) r = g.op.eval (g.inputs.map fun i => val (brun hs x) (refs i)) := by
  rcases g with ⟨op, is⟩
  rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c, is⟩⟩⟩
  · refine ⟨.inl (op.eval []), [], by simp, by trivial, by simp, ?_⟩
    intro x hx
    rfl
  · refine ⟨lift (fun v => op.eval [v]) (refs a), [], by simp, ?_, by simp, ?_⟩
    · simpa using valid_lift _ _ _ (hv a)
    · intro x hx
      simp only [List.append_nil, val_lift, List.map_cons, List.map_nil]
  · let gate : BinaryGate := ⟨fun u v => op.eval [fn (refs a) u, fn (refs b) v], idx (refs a), idx (refs b)⟩
    refine ⟨.inr (id, N + hs.length), [gate], by simp, by simp [Valid], ?_, ?_⟩
    · intro hN g hg
      have heq : g = gate := by simpa using hg
      subst g
      exact ⟨idx_valid _ _ (by omega) (hv a), idx_valid _ _ (by omega) (hv b)⟩
    intro x hx
    have he : N + hs.length = (brun hs x).length := by rw [brun_length, hx]
    change (brun (hs ++ [gate]) x).getD (N + hs.length) false = _
    rw [brun_snoc, he, getD_at]
    simp only [gate, List.map_cons, List.map_nil, val_fn]
  · simp at hg

lemma getD_ne (l : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  by_cases h : i < l.length
  · exact getD_lt _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma normalize_run (N : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (hs : List BinaryGate) (refs : ℕ → Ref),
      hs.length ≤ gs.countP (fun g => g.inputs.length == 2) ∧
      (∀ i, Valid (N + hs.length) (refs i)) ∧
      (0 < N → Back N hs) ∧
      ∀ x : List Bool, x.length = N → ∀ i,
        val (brun hs x) (refs i) = (run gs x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (fun i => if i < N then .inr (id,i) else .inl false), by simp, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · simpa [Valid] using hi
      · trivial
    · intro hN j hj
      simp at hj
    · intro x hx i
      by_cases hi : i < N
      · simp [hi, val, brun, run]
      · simp only [hi, ↓reduceIte, val, run, List.foldl_nil]
        exact (List.getD_eq_default _ _ (by omega)).symm
  | append_singleton gs g ih =>
    have hgs' : ∀ a ∈ gs, a.inputs.length ≤ 2 := by
      intro a ha
      exact hgs a (by simp [ha])
    have hg : g.inputs.length ≤ 2 := hgs g (by simp)
    obtain ⟨hs, refs, hc, hv, hb, heval⟩ := ih hgs'
    obtain ⟨r, es, he, hr, heb, hem⟩ := emit N hs g refs hg hv
    refine ⟨hs ++ es, (fun i => if i = N + gs.length then r else refs i), ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.countP_append, List.countP_singleton]
      omega
    · intro i
      dsimp only
      split_ifs
      · simpa [List.length_append, Nat.add_assoc] using hr
      · exact valid_mono (by simp) _ (hv i)
    · intro hN
      exact back_append N hs es (hb hN) (heb hN)
    · intro x hx i
      by_cases hi : i = N + gs.length
      · simp only [hi, ↓reduceIte]
        rw [hem x hx, run_snoc]
        have hlen : N + gs.length = (run gs x).length := by rw [run_length,hx]
        rw [hlen, getD_at]
        congr 1
        exact List.map_congr_left fun j _ => heval x hx j
      · simp only [hi, ↓reduceIte]
        rw [val_ext hs es x (refs i) (by rw [hx]; exact hv i), heval x hx i, run_snoc]
        exact (getD_ne _ _ _ (by rw [run_length,hx]; exact hi)).symm

lemma normalize (N : ℕ) (C : Circuit) (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (B : BinaryCircuit) (out : Bool → Bool),
      B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      ∀ x : List Bool, x.length = N → C.eval x = out (B.eval x) := by
  obtain ⟨hs, refs, hc, hv, hb, heval⟩ := normalize_run N C.gates hC
  refine ⟨⟨hs,idx (refs C.output)⟩, fn (refs C.output), hc, ?_⟩
  intro x hx
  change (run C.gates x).getD C.output false = fn (refs C.output) ((brun hs x).getD (idx (refs C.output)) false)
  rw [← heval x hx C.output, val_fn]

lemma normalize_back (N : ℕ) (hN : 0 < N) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (B : BinaryCircuit) (out : Bool → Bool),
      B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      Back N B.gates ∧ B.output < N + B.gates.length ∧
      ∀ x : List Bool, x.length = N → C.eval x = out (B.eval x) := by
  obtain ⟨hs, refs, hc, hv, hb, heval⟩ := normalize_run N C.gates hC
  refine ⟨⟨hs,idx (refs C.output)⟩, fn (refs C.output), hc, hb hN,
    idx_valid _ _ (by omega) (hv C.output), ?_⟩
  intro x hx
  change (run C.gates x).getD C.output false = fn (refs C.output) ((brun hs x).getD (idx (refs C.output)) false)
  rw [← heval x hx C.output, val_fn]

def down (k i : ℕ) : ℕ := if i < k then i else i - 1

def remap (k : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨g.op, down k g.left, down k g.right⟩

lemma getD_erase_down (l : List Bool) (k i : ℕ) (hi : i ≠ k) :
    (l.eraseIdx k).getD (down k i) false = l.getD i false := by
  simp only [down]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt h]
  · have hki : k ≤ i - 1 := by omega
    have hii : i - 1 + 1 = i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hki, hii]

lemma back_prefix (N : ℕ) (gs hs : List BinaryGate) (hb : Back N (gs ++ hs)) : Back N gs := by
  intro j hj
  have h := hb j (by simp; omega)
  simpa only [List.getElem_append_left hj] using h

lemma remap_eq_of_back (N : ℕ) (gs : List BinaryGate) (hb : Back N gs) :
    gs.map (remap (N + gs.length)) = gs := by
  calc
    gs.map (remap (N + gs.length)) = gs.map id := by
      apply List.map_congr_left
      intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨hl,hr⟩ := hb j hj
      simp only [remap, down, ite_eq_left (by omega : gs[j].left < N + gs.length),
        ite_eq_left (by omega : gs[j].right < N + gs.length), id_eq]
    _ = gs := List.map_id gs

lemma brun_erase (N : ℕ) (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length)
    (hb : Back N gs) (hd : ∀ g ∈ gs, g.left ≠ N + j ∧ g.right ≠ N + j)
    (x : List Bool) (hx : x.length = N) :
    brun ((gs.eraseIdx j).map (remap (N + j))) x = (brun gs x).eraseIdx (N + j) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    have hb' : Back N gs := back_prefix N gs [g] hb
    have hd' : ∀ a ∈ gs, a.left ≠ N + j ∧ a.right ≠ N + j := by
      intro a ha
      exact hd a (by simp [ha])
    have hdg := hd g (by simp)
    by_cases hj' : j < gs.length
    · rw [List.eraseIdx_append_of_lt_length hj', List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [brun_snoc, ih hj' hb' hd', brun_snoc,
        List.eraseIdx_append_of_lt_length (by rw [brun_length,hx]; omega)]
      congr 1
      simp only [remap, getD_erase_down _ _ _ hdg.1, getD_erase_down _ _ _ hdg.2]
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.eraseIdx_append_of_length_le (by omega)]
      simp only [Nat.sub_self, List.eraseIdx_zero, List.tail_cons, List.append_nil]
      rw [remap_eq_of_back N gs hb', brun_snoc]
      have hl : N + gs.length = (brun gs x).length := by rw [brun_length,hx]
      rw [hl, List.eraseIdx_append_of_length_le (by omega)]
      simp

lemma back_erase (N : ℕ) (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length)
    (hb : Back N gs) (hd : ∀ g ∈ gs, g.left ≠ N + j ∧ g.right ≠ N + j) :
    Back N ((gs.eraseIdx j).map (remap (N + j))) := by
  intro i hi
  have hi' : i < (gs.eraseIdx j).length := by simpa using hi
  rw [List.getElem_map]
  by_cases hij : i < j
  · rw [List.getElem_eraseIdx_of_lt hi' hij]
    have hi0 : i < gs.length := by have := List.length_eraseIdx_le gs j; omega
    obtain ⟨hl,hr⟩ := hb i hi0
    simp only [remap, down]
    constructor <;> split_ifs <;> omega
  · rw [List.getElem_eraseIdx_of_ge hi' (by omega)]
    have hi0 : i + 1 < gs.length := by rw [List.length_eraseIdx_of_lt hj] at hi'; omega
    obtain ⟨hl,hr⟩ := hb (i+1) hi0
    obtain ⟨hdl,hdr⟩ := hd gs[i+1] (List.getElem_mem hi0)
    simp only [remap, down]
    constructor <;> split_ifs <;> omega

def eraseCircuit (N : ℕ) (C : BinaryCircuit) (j : ℕ) : BinaryCircuit :=
  ⟨(C.gates.eraseIdx j).map (remap (N+j)), down (N+j) C.output⟩

lemma eraseCircuit_spec (N : ℕ) (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length)
    (hb : Back N C.gates) (hd : ∀ g ∈ C.gates, g.left ≠ N + j ∧ g.right ≠ N + j)
    (ho : C.output < N + C.gates.length) (hne : C.output ≠ N+j) :
    (eraseCircuit N C j).size + 1 = C.size ∧
    Back N (eraseCircuit N C j).gates ∧
    (eraseCircuit N C j).output < N + (eraseCircuit N C j).gates.length ∧
    ∀ x : List Bool, x.length = N → (eraseCircuit N C j).eval x = C.eval x := by
  refine ⟨?_, back_erase N C.gates j hj hb hd, ?_, ?_⟩
  · simp only [eraseCircuit, BinaryCircuit.size, List.length_map, List.length_eraseIdx_of_lt hj]
    omega
  · simp only [eraseCircuit, List.length_map, List.length_eraseIdx_of_lt hj, down]
    split_ifs <;> omega
  · intro x hx
    change (brun ((C.gates.eraseIdx j).map (remap (N+j))) x).getD (down (N+j) C.output) false =
      (brun C.gates x).getD C.output false
    rw [brun_erase N C.gates j hj hb hd x hx, getD_erase_down _ _ _ hne]

def Live (N : ℕ) (C : BinaryCircuit) : Prop :=
  ∀ i (hi : i < C.gates.length), N+i ≠ C.output →
    ∃ (j : ℕ) (hj : j < C.gates.length), i < j ∧ (C.gates[j].left = N+i ∨ C.gates[j].right = N+i)

lemma prune (N : ℕ) (C : BinaryCircuit) (hb : Back N C.gates)
    (ho : C.output < N + C.gates.length) :
    ∃ D : BinaryCircuit, D.size ≤ C.size ∧ Back N D.gates ∧
      D.output < N + D.gates.length ∧
      (∀ x : List Bool, x.length = N → D.eval x = C.eval x) ∧ Live N D := by
  classical
  have hex : ∃ k, ∃ D : BinaryCircuit, Back N D.gates ∧
      D.output < N + D.gates.length ∧ D.size ≤ k ∧
      ∀ x : List Bool, x.length = N → D.eval x = C.eval x :=
    ⟨C.size,C,hb,ho,le_rfl,fun x hx => rfl⟩
  obtain ⟨D,hback,hout,hsize,hval⟩ := Nat.find_spec hex
  have hmin : Nat.find hex ≤ C.size :=
    Nat.find_min' hex ⟨C,hb,ho,le_rfl,fun x hx => rfl⟩
  refine ⟨D,hsize.trans hmin,hback,hout,hval,?_⟩
  intro i hi hio
  by_contra hn
  have hd : ∀ g ∈ D.gates, g.left ≠ N+i ∧ g.right ≠ N+i := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨hl,hr⟩ := hback j hj
    constructor
    · intro he
      exact hn ⟨j,hj,by omega,Or.inl he⟩
    · intro he
      exact hn ⟨j,hj,by omega,Or.inr he⟩
  obtain ⟨hes,heb,heo,hev⟩ := eraseCircuit_spec N D i hi hback hd hout hio.symm
  have hlower : Nat.find hex ≤ (eraseCircuit N D i).size :=
    Nat.find_min' hex ⟨eraseCircuit N D i,heb,heo,le_rfl,
      fun x hx => (hev x hx).trans (hval x hx)⟩
  omega

def Edge (N : ℕ) (C : BinaryCircuit) (a b : ℕ) : Prop :=
  ∃ (j : ℕ) (hj : j < C.gates.length), b = N+j ∧ (C.gates[j].left = a ∨ C.gates[j].right = a)

lemma live_reaches (N : ℕ) (C : BinaryCircuit) (hl : Live N C) :
    ∀ i, i < C.gates.length → Relation.ReflTransGen (Edge N C) (N+i) C.output := by
  have aux : ∀ k i, C.gates.length-i = k → i < C.gates.length →
      Relation.ReflTransGen (Edge N C) (N+i) C.output := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hki hi
      by_cases hio : N+i = C.output
      · rw [hio]
      · obtain ⟨j,hj,hij,hr⟩ := hl i hi hio
        have tail := ih (C.gates.length-j) (by omega) j rfl hj
        exact (Relation.ReflTransGen.single ⟨j,hj,rfl,hr⟩).trans tail
  intro i hi
  exact aux (C.gates.length-i) i rfl hi

lemma live_output_last (N : ℕ) (C : BinaryCircuit) (hl : Live N C)
    (hn : 0 < C.gates.length) : C.output = N + (C.gates.length - 1) := by
  by_contra ho
  obtain ⟨j,hj,hij,hr⟩ := hl (C.gates.length-1) (by omega) (fun h => ho h.symm)
  omega

lemma normalize_live (N : ℕ) (hN : 0 < N) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (B : BinaryCircuit) (out : Bool → Bool),
      B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      Back N B.gates ∧ B.output < N + B.gates.length ∧ Live N B ∧
      (∀ i, i < B.gates.length → Relation.ReflTransGen (Edge N B) (N+i) B.output) ∧
      ∀ x : List Bool, x.length = N → C.eval x = out (B.eval x) := by
  obtain ⟨B,out,hsize,hback,hout,heval⟩ := normalize_back N hN C hC
  obtain ⟨D,hds,hdb,hdo,hdv,hdl⟩ := prune N B hback hout
  refine ⟨D,out,hds.trans hsize,hdb,hdo,hdl,live_reaches N D hdl,?_⟩
  intro x hx
  rw [heval x hx,hdv x hx]

end PEqualNP.Outside.L_meta_25806_aux.Normalize


namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

abbrev gatesOf (C : Circuit) : Finset ℕ := Finset.range C.size
abbrev readsOf (C : Circuit) (w : ℕ) : ℕ := readsIn C (Finset.range C.size) w
def isBinOp (_op : GateOp) : Prop := True

lemma readsIn_empty (C : Circuit) (w : ℕ) : readsIn C ∅ w = 0 := by
  simp [readsIn]

lemma readsIn_insert (C : Circuit) (G : Finset ℕ) (j w : ℕ) (hj : j ∉ G) :
    readsIn C (insert j G) w = (gateAt C j).inputs.count w + readsIn C G w := by
  unfold readsIn
  exact Finset.sum_insert hj

lemma readsIn_union (C : Circuit) (G1 G2 : Finset ℕ) (w : ℕ) (h : Disjoint G1 G2) :
    readsIn C (G1 ∪ G2) w = readsIn C G1 w + readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_union h

lemma readsIn_mono (C : Circuit) {G1 G2 : Finset ℕ} (h : G1 ⊆ G2) (w : ℕ) :
    readsIn C G1 w ≤ readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset h

lemma readsIn_eq_zero_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    readsIn C G w = 0 ↔ ∀ j ∈ G, w ∉ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj hw
    have hp : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hz := h j hj
    omega
  · intro h j hj
    exact List.count_eq_zero.mpr (h j hj)

lemma readsIn_pos_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    0 < readsIn C G w ↔ ∃ j ∈ G, w ∈ (gateAt C j).inputs := by
  constructor
  · intro hp
    by_contra h
    have hz : readsIn C G w = 0 := (readsIn_eq_zero_iff C G w).2 (fun j hj hw => h ⟨j, hj, hw⟩)
    omega
  · rintro ⟨j, hj, hw⟩
    have hc : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn
    omega

lemma readsIn_ge_of_mem (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ G) (hw : w ∈ (gateAt C j).inputs) : 1 ≤ readsIn C G w :=
  (readsIn_pos_iff C G w).2 ⟨j, hj, hw⟩

lemma readsIn_eq_one_unique (C : Circuit) (G : Finset ℕ) (w : ℕ) (h : readsIn C G w = 1) :
    ∃ j ∈ G, w ∈ (gateAt C j).inputs ∧ (gateAt C j).inputs.count w = 1 ∧
      ∀ j' ∈ G, w ∈ (gateAt C j').inputs → j' = j := by
  obtain ⟨j, hj, hw⟩ := (readsIn_pos_iff C G w).1 (by omega)
  have hcpos : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have hcle : (gateAt C j).inputs.count w ≤ 1 := by
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn at h
    omega
  refine ⟨j, hj, hw, by omega, ?_⟩
  intro j' hj' hw'
  by_contra hne
  have hc' : 0 < (gateAt C j').inputs.count w := List.count_pos_iff.mpr hw'
  have hsub : ({j, j'} : Finset ℕ) ⊆ G := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun i => (gateAt C i).inputs.count w) hsub
  rw [Finset.sum_pair (Ne.symm hne)] at hle
  unfold readsIn at h
  omega

lemma readsIn_disjoint_zero (C : Circuit) {G1 G2 : Finset ℕ} {w : ℕ}
    (h1 : G1 ⊆ gatesOf C) (h2 : G2 ⊆ gatesOf C) (hdisj : Disjoint G1 G2)
    (hr : readsOf C w = 1) (h1r : readsIn C G1 w = 1) : readsIn C G2 w = 0 := by
  have hsub : G1 ∪ G2 ⊆ gatesOf C := Finset.union_subset h1 h2
  have hle := readsIn_mono C hsub w
  rw [readsIn_union C G1 G2 w hdisj] at hle
  change readsIn C (gatesOf C) w = 1 at hr
  omega

lemma readsIn_zero_of_count_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ gatesOf C) (hG : G ⊆ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (hc : (gateAt C j).inputs.count w = 1) : readsIn C G w = 0 := by
  refine readsIn_disjoint_zero C (G1 := {j}) (G2 := G)
    (Finset.singleton_subset_iff.2 hj) hG (Finset.disjoint_singleton_left.2 hn) hr ?_
  simpa [readsIn] using hc

lemma count_zero_of_readsIn_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hG : G ⊆ gatesOf C) (hj : j ∈ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (h1 : readsIn C G w = 1) : (gateAt C j).inputs.count w = 0 := by
  have hz := readsIn_disjoint_zero C (G1 := G) (G2 := {j})
    hG (Finset.singleton_subset_iff.2 hj) (Finset.disjoint_singleton_right.2 hn) hr h1
  simpa [readsIn] using hz

lemma readsIn_ge_bound_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    {G : Finset ℕ} (hG : G ⊆ gatesOf C) {r : ℕ} (hbound : ∀ j ∈ G, n + j ≤ r) :
    readsIn C G r = 0 := by
  rw [readsIn_eq_zero_iff]
  intro j hj hr
  have hjlt : j < C.gates.length := Finset.mem_range.1 (hG hj)
  have hlt := hback j hjlt r hr
  have hle := hbound j hj
  omega

lemma reads_output_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) : readsOf C C.output = 0 := by
  refine readsIn_ge_bound_zero n C hback (Finset.Subset.refl _) ?_
  intro j hj
  have hjlt : j < C.size := Finset.mem_range.1 hj
  omega

lemma ne_output_of_reads_pos (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {w : ℕ} (hw : 0 < readsOf C w) : C.output ≠ w := by
  rintro rfl
  have hz := reads_output_zero n C hback hout
  omega

lemma gateAt_mem_gates (C : Circuit) {j : ℕ} (hj : j < C.size) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  have hlen : j < C.gates.length := hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

lemma list_len2_eq (l : List ℕ) (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at h ⊢

lemma list_len1_eq (l : List ℕ) (h : l.length = 1) :
    l = [l.getD 0 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h ⊢

lemma count_pair_eq_one_left {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count a = 1 := by
  simp [h]

lemma count_pair_eq_one_right {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count b = 1 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

lemma count_pair_eq_two {a : ℕ} : ([a, a] : List ℕ).count a = 2 := by
  simp

lemma count_pair_eq_zero {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) :
    ([a, b] : List ℕ).count x = 0 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

inductive BTree
  | priv (w : ℕ) : BTree
  | mark (w : ℕ) : BTree
  | node (j : ℕ) (l r : BTree) : BTree

def BTree.root (n : ℕ) : BTree → ℕ
  | BTree.priv w => w
  | BTree.mark w => w
  | BTree.node j _ _ => n + j

def BTree.marks : BTree → ℕ
  | BTree.priv _ => 0
  | BTree.mark _ => 1
  | BTree.node _ l r => l.marks + r.marks

def BTree.privs : BTree → Finset ℕ
  | BTree.priv w => {w}
  | BTree.mark _ => ∅
  | BTree.node _ l r => l.privs ∪ r.privs

def BTree.gates : BTree → Finset ℕ
  | BTree.priv _ => ∅
  | BTree.mark _ => ∅
  | BTree.node j l r => insert j (l.gates ∪ r.gates)

def BTree.wires (n : ℕ) (t : BTree) : Finset ℕ :=
  t.privs ∪ t.gates.image (fun k => n + k)

def BTree.nonMark : BTree → Prop
  | BTree.mark _ => False
  | _ => True

def GoodTree (n : ℕ) (C : Circuit) : BTree → Prop
  | BTree.priv w => w < n ∧ readsOf C w = 1
  | BTree.mark _ => True
  | BTree.node j l r =>
      j < C.size ∧ isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs = [l.root n, r.root n] ∧
      GoodTree n C l ∧ GoodTree n C r ∧
      (l.nonMark → readsOf C (l.root n) = 1) ∧
      (r.nonMark → readsOf C (r.root n) = 1)

lemma BTree.wires_node (n j : ℕ) (l r : BTree) :
    (BTree.node j l r).wires n = insert (n + j) (l.wires n ∪ r.wires n) := by
  ext w
  simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_insert, Finset.image_union,
    Finset.mem_union, Finset.mem_insert]
  tauto

lemma BTree.root_mem_wires (n : ℕ) {t : BTree} (ht : t.nonMark) : t.root n ∈ t.wires n := by
  cases t with
  | priv w => simp [BTree.wires, BTree.privs, BTree.root]
  | mark w => exact False.elim ht
  | node j l r =>
    rw [BTree.wires_node, BTree.root]
    exact Finset.mem_insert_self _ _

lemma BTree.nonMark_of_marks_zero {t : BTree} (h : t.marks = 0) : t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.marks] at h
  | node _ _ _ => trivial

lemma BTree.nonMark_of_wires_nonempty (n : ℕ) {t : BTree} {w : ℕ} (hw : w ∈ t.wires n) :
    t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.wires, BTree.privs, BTree.gates] at hw
  | node _ _ _ => trivial

lemma good_gates_sub {n : ℕ} {C : Circuit} {t : BTree} (ht : GoodTree n C t) :
    t.gates ⊆ gatesOf C := by
  induction t with
  | priv _ => simp [BTree.gates]
  | mark _ => simp [BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, _, hgl, hgr, _, _⟩
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · exact Finset.mem_range.2 hj
    · exact ihl hgl hkl
    · exact ihr hgr hkr

lemma good_wires_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ w ∈ t.wires n, w ≤ t.root n := by
  induction t with
  | priv w =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu ⊢
    omega
  | mark _ =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
    have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
    have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
    intro w hw
    rw [BTree.wires_node] at hw
    rw [BTree.root]
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihl hgl w hwl) hl_lt)
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihr hgr w hwr) hr_lt)

lemma good_gates_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ k ∈ t.gates, n + k ≤ t.root n := by
  intro k hk
  refine good_wires_le hback ht (n + k) ?_
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)

lemma good_readsIn_top_zero {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : readsIn C t.gates (t.root n) = 0 :=
  readsIn_ge_bound_zero n C hback (good_gates_sub ht) (good_gates_le hback ht)

lemma good_node_not_mem_sub {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {j : ℕ} {l r : BTree}
    (ht : GoodTree n C (BTree.node j l r)) : j ∉ l.gates ∧ j ∉ r.gates := by
  rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
  have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
  have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
  constructor
  · intro hjl
    have := good_gates_le hback hgl j hjl
    omega
  · intro hjr
    have := good_gates_le hback hgr j hjr
    omega

lemma good_internal_reads {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree} (ht : GoodTree n C t) :
    (∀ w ∈ t.wires n, w ≠ t.root n → readsIn C t.gates w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) ∧
    (∀ j l r, t = BTree.node j l r → Disjoint (l.wires n) (r.wires n)) := by
  induction t with
  | priv w =>
    refine ⟨fun u hu hne => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu hne
    exact absurd hu hne
  | mark _ =>
    refine ⟨fun u hu => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    obtain ⟨ihl_int, _⟩ := ihl hgl
    obtain ⟨ihr_int, _⟩ := ihr hgr
    have hnot : j ∉ l.gates ∧ j ∉ r.gates :=
      good_node_not_mem_sub hback ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
    have hl_sub : l.gates ⊆ gatesOf C := good_gates_sub hgl
    have hr_sub : r.gates ⊆ gatesOf C := good_gates_sub hgr
    have hdisj_wires : Disjoint (l.wires n) (r.wires n) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      have hnon : (l.wires n ∩ r.wires n).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
      let w := (l.wires n ∩ r.wires n).max' hnon
      have hw_mem : w ∈ l.wires n ∩ r.wires n := Finset.max'_mem _ hnon
      have hwl : w ∈ l.wires n := (Finset.mem_inter.1 hw_mem).1
      have hwr : w ∈ r.wires n := (Finset.mem_inter.1 hw_mem).2
      have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      by_cases h1 : w = l.root n
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hcnt : (gateAt C j).inputs.count w = 2 := by
            rw [hinp, ← h1, ← h2]
            exact count_pair_eq_two
          have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hjG
          change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count w = 1 at hrw
          omega
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hrr : readsIn C r.gates w = 1 := (ihr_int w hwr h2).1
          have hdisj_j : Disjoint r.gates {j} := by simp [hnot.2]
          have hsub_rj : r.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hr_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_rj w
          rw [readsIn_union C r.gates {j} w hdisj_j] at hle
          have hjr : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h1]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h2 ▸ hr1 hrnm
          have hrl : readsIn C l.gates w = 1 := (ihl_int w hwl h1).1
          have hdisj_j : Disjoint l.gates {j} := by simp [hnot.1]
          have hsub_lj : l.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hl_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_lj w
          rw [readsIn_union C l.gates {j} w hdisj_j] at hle
          have hjl : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h2]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
        · have hrl := ihl_int w hwl h1
          have hrr := ihr_int w hwr h2
          obtain ⟨p, hpG, hpw, _, hpuniq⟩ := readsIn_eq_one_unique C (gatesOf C) w hrl.2.1
          obtain ⟨pl, hpl, hplw⟩ := (readsIn_pos_iff C l.gates w).1 (by omega)
          obtain ⟨pr, hpr, hprw⟩ := (readsIn_pos_iff C r.gates w).1 (by omega)
          have hpl_eq : pl = p := hpuniq pl (hl_sub hpl) hplw
          have hpr_eq : pr = p := hpuniq pr (hr_sub hpr) hprw
          subst hpl_eq
          have hpr' : pl ∈ r.gates := by rwa [← hpr_eq]
          have hmem_inter : n + pl ∈ l.wires n ∩ r.wires n := Finset.mem_inter.2
            ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpl, rfl⟩),
             Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpr', rfl⟩)⟩
          have hle_max : n + pl ≤ w := Finset.le_max' _ _ hmem_inter
          have hlt := hback pl (Finset.mem_range.1 (hl_sub hpl)) w hplw
          omega
    have hdisj_gates : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_wires
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hj_not_u : j ∉ l.gates ∪ r.gates := by
      simp [hnot.1, hnot.2]
    refine ⟨?_, fun j' l' r' heq => by cases heq; exact hdisj_wires⟩
    intro w hw hne
    rw [BTree.wires_node] at hw
    rw [BTree.root] at hne
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact absurd rfl hne
    · have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1l : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 2 := by
          rw [hinp, ← heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (l.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (l.root n) = 1 at hr1l
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = l.root n
      · subst hwr_eq
        have hrw : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_left hlr_ne
        have hrl0 : readsIn C l.gates (l.root n) = 0 := good_readsIn_top_zero hback hgl
        have hrr0 : readsIn C r.gates (l.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hr_sub hnot.2 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihl_int w hwl hwr_eq
        have hrr0 : readsIn C r.gates w = 0 :=
          readsIn_disjoint_zero C hl_sub hr_sub hdisj_gates hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hl_sub hjG hnot.1 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩
    · have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1r : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 2 := by
          rw [hinp, heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (r.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (r.root n) = 1 at hr1r
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = r.root n
      · subst hwr_eq
        have hrw : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_right hlr_ne
        have hrr0 : readsIn C r.gates (r.root n) = 0 := good_readsIn_top_zero hback hgr
        have hrl0 : readsIn C l.gates (r.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hl_sub hnot.1 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihr_int w hwr hwr_eq
        have hrl0 : readsIn C l.gates w = 0 :=
          readsIn_disjoint_zero C hr_sub hl_sub hdisj_gates.symm hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hr_sub hjG hnot.2 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩

lemma good_markFree_inputs {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) :
    ∀ j ∈ t.gates, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ t.wires n := by
  induction t with
  | priv _ =>
    intro j hj
    simp [BTree.gates] at hj
  | mark _ =>
    simp [BTree.marks] at hm
  | node j l r ihl ihr =>
    rcases ht with ⟨_, hop, hinp, hgl, hgr, _, _⟩
    simp only [BTree.marks] at hm
    have hml : l.marks = 0 := by omega
    have hmr : r.marks = 0 := by omega
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · refine ⟨hop, by rw [hinp]; rfl, fun w hw => ?_⟩
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [BTree.wires_node]
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hml)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmr)))
    · obtain ⟨ho, hl2, hwin⟩ := ihl hgl hml k hkl
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · obtain ⟨ho, hl2, hwin⟩ := ihr hgr hmr k hkr
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hwin w hw))

def IsTree (n : ℕ) (C : Circuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := readsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

lemma good_markFree_isTree {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) : IsTree n C t.privs ∅ := by
  refine ⟨t.gates, t.root n, good_gates_sub ht,
    BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hm),
    good_readsIn_top_zero hback ht, fun _ hb => absurd hb (Finset.notMem_empty _), ?_,
    (good_internal_reads hback hout ht).1⟩
  intro j hj
  obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs ht hm j hj
  exact ⟨ho, hl, fun w hw => Or.inl (hwin w hw)⟩

def IsTopStretch (n : ℕ) (C : Circuit) (t : BTree) (reg priv : Finset ℕ) (b : ℕ) : Prop :=
  reg ⊆ t.gates ∧ priv ⊆ t.privs ∧ b ≤ t.root n ∧
  ((reg = ∅ ∧ priv = ∅ ∧ b = t.root n) ∨
   (let wires := priv ∪ reg.image (fun k => n + k)
    t.root n ∈ wires ∧ b ∉ wires ∧ b < t.root n ∧ readsIn C reg b = 1 ∧
    (∀ j ∈ reg, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ t.root n → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w)))

lemma isTree_of_topStretch {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) {reg priv : Finset ℕ} {b : ℕ}
    (hs : IsTopStretch n C t reg priv b) (hnp : priv.Nonempty) : IsTree n C priv {b} := by
  rcases hs with ⟨hreg, _, _, ⟨_, hpe, _⟩ | ⟨hrm, hbn, hblt, hbr, hgj, hwint⟩⟩
  · rw [hpe] at hnp
    exact absurd hnp Finset.not_nonempty_empty
  · refine ⟨reg, t.root n, hreg.trans (good_gates_sub ht), hrm,
      readsIn_ge_bound_zero n C hback (hreg.trans (good_gates_sub ht))
        (fun k hk => good_gates_le hback ht k (hreg hk)),
      fun b' hb' => by
        rw [Finset.mem_singleton.1 hb']
        exact ⟨hbn, hblt, hbr⟩,
      fun j hj => by
        obtain ⟨ho, hl, hwin⟩ := hgj j hj
        exact ⟨ho, hl, fun w hw => (hwin w hw).imp id (fun h => Finset.mem_singleton.2 h)⟩,
      hwint⟩

lemma extend_stretch_aux {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {j : ℕ} {mf mk : BTree}
    (hj : j < C.size) (hop : isBinOp (gateAt C j).op)
    (hinp : (gateAt C j).inputs = [mf.root n, mk.root n] ∨
      (gateAt C j).inputs = [mk.root n, mf.root n])
    (hgf : GoodTree n C mf) (hgk : GoodTree n C mk)
    (hmf : mf.marks = 0)
    (hrf1 : readsOf C (mf.root n) = 1)
    (hrk1 : mk.nonMark → readsOf C (mk.root n) = 1)
    (hdisj_w : Disjoint (mf.wires n) (mk.wires n))
    (hdisj_g : Disjoint mf.gates mk.gates)
    (hj_mf : j ∉ mf.gates) (hj_mk : j ∉ mk.gates)
    {reg_k priv_k : Finset ℕ} {b : ℕ}
    (hsk : IsTopStretch n C mk reg_k priv_k b) :
    let reg := insert j (mf.gates ∪ reg_k)
    let priv := mf.privs ∪ priv_k
    let wires := priv ∪ reg.image (fun k => n + k)
    (n + j) ∈ wires ∧ b ∉ wires ∧ b < n + j ∧ readsIn C reg b = 1 ∧
    (∀ k ∈ reg, isBinOp (gateAt C k).op ∧ (gateAt C k).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ n + j → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) := by
  intro reg priv wires
  have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
  have hmf_sub : mf.gates ⊆ gatesOf C := good_gates_sub hgf
  have hmk_sub : mk.gates ⊆ gatesOf C := good_gates_sub hgk
  have hmf_int := (good_internal_reads hback hout hgf).1
  have hmf_lt : mf.root n < n + j := hback j hj (mf.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmk_lt : mk.root n < n + j := hback j hj (mk.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmf_ne_mk : mf.root n ≠ mk.root n := by
    intro heq
    have hcnt : (gateAt C j).inputs.count (mf.root n) = 2 := by
      rcases hinp with h | h <;> rw [h, heq] <;> exact count_pair_eq_two
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (mf.root n))) hjG
    change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (mf.root n) = 1 at hrf1
    omega
  have hcnt_mf : (gateAt C j).inputs.count (mf.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_left hmf_ne_mk
    · exact count_pair_eq_one_right hmf_ne_mk.symm
  have hcnt_mk : (gateAt C j).inputs.count (mk.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_right hmf_ne_mk
    · exact count_pair_eq_one_left hmf_ne_mk.symm
  rcases hsk with ⟨hreg_k, hpriv_k, hb_le, hcase⟩
  have hdisj_rk : Disjoint mf.gates reg_k := Disjoint.mono_right hreg_k hdisj_g
  have hj_not_u : j ∉ mf.gates ∪ reg_k := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hj_mf, fun h => hj_mk (hreg_k h)⟩
  have hwires_eq : wires = insert (n + j) (mf.wires n ∪ (priv_k ∪ reg_k.image (fun k => n + k))) := by
    ext w
    simp only [wires, priv, reg, BTree.wires, Finset.image_insert, Finset.image_union,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h1 | h2) | (h3 | h4 | h5))
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h3
      · exact Or.inr (Or.inl (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inr h5))
    · rintro (h1 | (h2 | h3) | (h4 | h5))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inr (Or.inr h5))
  have hwk_sub : priv_k ∪ reg_k.image (fun k => n + k) ⊆ mk.wires n := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hp | ⟨k, hk, rfl⟩
    · exact Finset.mem_union_left _ (hpriv_k hp)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hreg_k hk, rfl⟩)
  have hmf_reads_sub : ∀ w ∈ mf.wires n, readsIn C reg_k w = 0 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · subst hwr
      exact readsIn_zero_of_count_one C hjG (hreg_k.trans hmk_sub) (fun h => hj_mk (hreg_k h)) hrf1 hcnt_mf
    · have hi := hmf_int w hw hwr
      exact readsIn_disjoint_zero C hmf_sub (hreg_k.trans hmk_sub) hdisj_rk hi.2.1 hi.1
  have hmf_all_reads1 : ∀ w ∈ mf.wires n, readsOf C w = 1 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · exact hwr ▸ hrf1
    · exact (hmf_int w hw hwr).2.1
  have hb_not_mf : b ∉ mf.wires n := by
    intro hbm
    have hrb1 : readsOf C b = 1 := hmf_all_reads1 b hbm
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, _, hbr1, _, _⟩
    · subst hbeq
      have hne_root : mk.root n ≠ mf.root n := hmf_ne_mk.symm
      have hi := hmf_int (mk.root n) hbm hne_root
      have h0 := count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
      omega
    · have h0 := hmf_reads_sub b hbm
      omega
  have hmf_reads_b : readsIn C mf.gates b = 0 := by
    rw [readsIn_eq_zero_iff]
    intro k hk hbk
    have hwin := (good_markFree_inputs hgf hmf k hk).2.2 b hbk
    exact hb_not_mf hwin
  have hroot_mem : n + j ∈ wires := by
    rw [hwires_eq]
    exact Finset.mem_insert_self _ _
  have hb_lt : b < n + j := Nat.lt_of_le_of_lt hb_le hmk_lt
  have hb_not_w : b ∉ wires := by
    rw [hwires_eq]
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨by omega, hb_not_mf, ?_⟩
    rcases hcase with ⟨hre, hpe, _⟩ | ⟨_, hbn, _, _, _, _⟩
    · simp [hre, hpe]
    · simpa [Finset.mem_union, not_or] using hbn
  have hb_reads : readsIn C reg b = 1 := by
    rw [readsIn_insert C _ j b hj_not_u, readsIn_union C mf.gates reg_k b hdisj_rk, hmf_reads_b]
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, hblt_k, hbr1, _, _⟩
    · subst hbeq
      rw [hre, readsIn_empty, hcnt_mk]
    · have hcj0 : (gateAt C j).inputs.count b = 0 := by
        have hbn1 : b ≠ mf.root n := fun heq =>
          hb_not_mf (heq ▸ BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf))
        have hbn2 : b ≠ mk.root n := by omega
        rcases hinp with h | h <;> rw [h]
        · exact count_pair_eq_zero hbn1 hbn2
        · exact count_pair_eq_zero hbn2 hbn1
      rw [hcj0, hbr1]
  refine ⟨hroot_mem, hb_not_w, hb_lt, hb_reads, ?_, ?_⟩
  · intro k hk
    simp only [reg, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkm | hkk
    · refine ⟨hop, by rcases hinp with h | h <;> rw [h] <;> rfl, fun w hw => ?_⟩
      have hwf : w = mf.root n ∨ w = mk.root n := by
        rcases hinp with h | h <;> rw [h] at hw <;> simp at hw <;> tauto
      rcases hwf with rfl | rfl
      · left
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf)))
      · rcases hcase with ⟨_, _, hbeq⟩ | ⟨hrm, _, _, _, _, _⟩
        · exact Or.inr hbeq.symm
        · left
          rw [hwires_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hrm)
    · obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs hgf hmf k hkm
      refine ⟨ho, hl, fun w hw => Or.inl ?_⟩
      rw [hwires_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · rcases hcase with ⟨hre, _, _⟩ | ⟨_, _, _, _, hgj, _⟩
      · rw [hre] at hkk
        exact absurd hkk (Finset.notMem_empty _)
      · obtain ⟨ho, hl, hwin⟩ := hgj k hkk
        refine ⟨ho, hl, fun w hw => (hwin w hw).imp (fun h => ?_) id⟩
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
  · intro w hw hne
    rw [hwires_eq] at hw
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwm | hwk
    · exact absurd rfl hne
    · rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk,
        hmf_reads_sub w hwm]
      by_cases hwr : w = mf.root n
      · subst hwr
        rw [hcnt_mf, good_readsIn_top_zero hback hgf]
        exact ⟨by omega, hrf1, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := hmf_int w hwm hwr
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
        rw [hcj0, hi.1]
        exact ⟨by omega, hi.2.1, hi.2.2⟩
    · rcases hcase with ⟨hre, hpe, _⟩ | ⟨hrm, _, _, _, _, hwint⟩
      · simp [hre, hpe] at hwk
      · have hw_in_mk : w ∈ mk.wires n := hwk_sub (Finset.mem_union.2 hwk)
        have hmknm : mk.nonMark := BTree.nonMark_of_wires_nonempty n hw_in_mk
        rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk]
        by_cases hwr : w = mk.root n
        · subst hwr
          have hrk := hrk1 hmknm
          have hrl0 : readsIn C mf.gates (mk.root n) = 0 :=
            readsIn_zero_of_count_one C hjG hmf_sub hj_mf hrk hcnt_mk
          have hrr0 : readsIn C reg_k (mk.root n) = 0 :=
            readsIn_ge_bound_zero n C hback (hreg_k.trans hmk_sub)
              (fun k hk => good_gates_le hback hgk k (hreg_k hk))
          rw [hcnt_mk, hrl0, hrr0]
          exact ⟨by omega, hrk, ne_output_of_reads_pos n C hback hout (by omega)⟩
        · have hi := hwint w (Finset.mem_union.2 hwk) hwr
          have hrl0 : readsIn C mf.gates w = 0 :=
            readsIn_disjoint_zero C (hreg_k.trans hmk_sub) hmf_sub hdisj_rk.symm hi.2.1 hi.1
          have hcj0 : (gateAt C j).inputs.count w = 0 :=
            count_zero_of_readsIn_one C (hreg_k.trans hmk_sub) hjG (fun h => hj_mk (hreg_k h)) hi.2.1 hi.1
          rw [hcj0, hrl0, hi.1]
          exact ⟨by omega, hi.2.1, hi.2.2⟩

lemma decomp_marked {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ (reg_top priv_top : Finset ℕ) (b_top : ℕ) (rest : List (Finset ℕ)),
      IsTopStretch n C t reg_top priv_top b_top ∧
      rest.length + 2 ≤ 2 * t.marks ∧
      (∀ S ∈ rest, S.Nonempty ∧ S ⊆ t.privs ∧ Disjoint S priv_top ∧ ∃ b, IsTree n C S {b}) ∧
      rest.Pairwise Disjoint ∧
      priv_top ∪ rest.toFinset.biUnion (fun S => S) = t.privs := by
  induction t with
  | priv _ =>
    simp [BTree.marks] at hm
  | mark w =>
    refine ⟨∅, ∅, w, [], ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _,
      Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [BTree.marks], fun _ h => by simp at h, List.Pairwise.nil,
      by simp [BTree.privs]⟩
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hgt_node : GoodTree n C (BTree.node j l r) := ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hdisj_w : Disjoint (l.wires n) (r.wires n) :=
      (good_internal_reads hback hout hgt_node).2 j l r rfl
    have hdisj_g : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_w
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hdisj_p : Disjoint l.privs r.privs :=
      Disjoint.mono (Finset.subset_union_left) (Finset.subset_union_left) hdisj_w
    have hnot := good_node_not_mem_sub hback hgt_node
    simp only [BTree.marks] at hm
    by_cases hml : l.marks = 0
    · have hmr : 1 ≤ r.marks := by omega
      obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr
      have hrf1 : readsOf C (l.root n) = 1 := hl1 (BTree.nonMark_of_marks_zero hml)
      have hext := extend_stretch_aux hback hout hj hop (Or.inl hinp) hgl hgr hml hrf1 hr1
        hdisj_w hdisj_g hnot.1 hnot.2 hsr
      refine ⟨insert j (l.gates ∪ reg_r), l.privs ∪ priv_r, b_r, rest_r, ?_, ?_, ?_, hpw_r, ?_⟩
      · refine ⟨Finset.insert_subset_insert j (Finset.union_subset_union_right hsr.1),
          Finset.union_subset_union_right hsr.2.1, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
      · simp only [BTree.marks]
        omega
      · intro S hS
        obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_r S hS
        refine ⟨hnp, hsub.trans Finset.subset_union_right, ?_, htr⟩
        rw [Finset.disjoint_union_right]
        exact ⟨Disjoint.mono_left hsub hdisj_p.symm, hdp⟩
      · simp only [BTree.privs]
        rw [Finset.union_assoc, hcov_r]
    · by_cases hmr : r.marks = 0
      · have hml1 : 1 ≤ l.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        have hrf1 : readsOf C (r.root n) = 1 := hr1 (BTree.nonMark_of_marks_zero hmr)
        have hext := extend_stretch_aux hback hout hj hop (Or.inr hinp) hgr hgl hmr hrf1 hl1
          hdisj_w.symm hdisj_g.symm hnot.2 hnot.1 hsl
        refine ⟨insert j (r.gates ∪ reg_l), r.privs ∪ priv_l, b_l, rest_l, ?_, ?_, ?_, hpw_l, ?_⟩
        · refine ⟨?_, ?_, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
          · intro k hk
            simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk ⊢
            rcases hk with rfl | h1 | h2
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h1)
            · exact Or.inr (Or.inl (hsl.1 h2))
          · intro w hw
            simp only [BTree.privs, Finset.mem_union] at hw ⊢
            rcases hw with h1 | h2
            · exact Or.inr h1
            · exact Or.inl (hsl.2.1 h2)
        · simp only [BTree.marks]
          omega
        · intro S hS
          obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_l S hS
          refine ⟨hnp, hsub.trans Finset.subset_union_left, ?_, htr⟩
          rw [Finset.disjoint_union_right]
          exact ⟨Disjoint.mono_left hsub hdisj_p, hdp⟩
        · simp only [BTree.privs]
          rw [Finset.union_assoc, hcov_l, Finset.union_comm]
      · have hml1 : 1 ≤ l.marks := by omega
        have hmr1 : 1 ≤ r.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr1
        let Ll : List (Finset ℕ) := if priv_l.Nonempty then priv_l :: rest_l else rest_l
        let Lr : List (Finset ℕ) := if priv_r.Nonempty then priv_r :: rest_r else rest_r
        have hLl_len : Ll.length ≤ rest_l.length + 1 := by
          dsimp only [Ll]
          split_ifs <;> simp
        have hLr_len : Lr.length ≤ rest_r.length + 1 := by
          dsimp only [Lr]
          split_ifs <;> simp
        have hLl_prop : ∀ S ∈ Ll, S.Nonempty ∧ S ⊆ l.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Ll] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsl.2.1, b_l, isTree_of_topStretch hback hgl hsl hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_l S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_l S hS
            exact ⟨a, b, c⟩
        have hLr_prop : ∀ S ∈ Lr, S.Nonempty ∧ S ⊆ r.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Lr] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsr.2.1, b_r, isTree_of_topStretch hback hgr hsr hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_r S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_r S hS
            exact ⟨a, b, c⟩
        have hLl_pw : Ll.Pairwise Disjoint := by
          dsimp only [Ll]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_l S hS).2.2.1.symm, hpw_l⟩
          · exact hpw_l
        have hLr_pw : Lr.Pairwise Disjoint := by
          dsimp only [Lr]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_r S hS).2.2.1.symm, hpw_r⟩
          · exact hpw_r
        have hLl_cov : Ll.toFinset.biUnion (fun S => S) = l.privs := by
          dsimp only [Ll]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_l]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_l
            exact hcov_l
        have hLr_cov : Lr.toFinset.biUnion (fun S => S) = r.privs := by
          dsimp only [Lr]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_r]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_r
            exact hcov_r
        refine ⟨∅, ∅, n + j, Ll ++ Lr,
          ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, BTree.marks]
          omega
        · intro S hS
          rcases List.mem_append.1 hS with h1 | h2
          · obtain ⟨a, b, c⟩ := hLl_prop S h1
            exact ⟨a, b.trans Finset.subset_union_left, Finset.disjoint_empty_right S, c⟩
          · obtain ⟨a, b, c⟩ := hLr_prop S h2
            exact ⟨a, b.trans Finset.subset_union_right, Finset.disjoint_empty_right S, c⟩
        · rw [List.pairwise_append]
          refine ⟨hLl_pw, hLr_pw, fun S1 h1 S2 h2 => ?_⟩
          exact Disjoint.mono (hLl_prop S1 h1).2.1 (hLr_prop S2 h2).2.1 hdisj_p
        · rw [Finset.empty_union, List.toFinset_append, Finset.union_biUnion, hLl_cov, hLr_cov]
          rfl

lemma marked_tree_chains {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ L : List (Finset ℕ),
      L.length + 1 ≤ 2 * t.marks ∧
      (∀ S ∈ L, S.Nonempty ∧ S ⊆ t.privs ∧ ∃ b, IsTree n C S {b}) ∧
      L.Pairwise Disjoint ∧
      L.toFinset.biUnion (fun S => S) = t.privs := by
  obtain ⟨reg, priv, b, rest, hs, hlen, hrest, hpw, hcov⟩ := decomp_marked hback hout ht hm
  by_cases hnp : priv.Nonempty
  · refine ⟨priv :: rest, by simp; omega, ?_, ?_, ?_⟩
    · intro S hS
      rcases List.mem_cons.1 hS with rfl | hSr
      · exact ⟨hnp, hs.2.1, b, isTree_of_topStretch hback ht hs hnp⟩
      · obtain ⟨a, b', _, c⟩ := hrest S hSr
        exact ⟨a, b', c⟩
    · exact List.pairwise_cons.2 ⟨fun S hS => (hrest S hS).2.2.1.symm, hpw⟩
    · rw [List.toFinset_cons, Finset.biUnion_insert, hcov]
  · refine ⟨rest, by omega, fun S hS => ?_, hpw, ?_⟩
    · obtain ⟨a, b', _, c⟩ := hrest S hS
      exact ⟨a, b', c⟩
    · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov
      exact hcov

def isInternalChild (n : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  readsOf C u = 1 ∧ ¬ (n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not)

open Classical in
noncomputable def buildTree (n : ℕ) (C : Circuit) (r : ℕ) : BTree :=
  if h : n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not then
    let j := r - n
    let u0 := (gateAt C j).inputs.getD 0 0
    let u1 := (gateAt C j).inputs.getD 1 0
    let child : ℕ → BTree := fun u =>
      if hu : u < r ∧ isInternalChild n C u then
        if u < n then BTree.priv u else buildTree n C u
      else BTree.mark u
    BTree.node j (child u0) (child u1)
  else if r < n ∧ readsOf C r = 1 then
    BTree.priv r
  else
    BTree.mark r
termination_by r

lemma buildTree_root (n : ℕ) (C : Circuit) (r : ℕ) : (buildTree n C r).root n = r := by
  rw [buildTree]
  split_ifs with h1 h2
  · simp [BTree.root]
    omega
  · rfl
  · rfl

lemma buildTree_good (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C) : ∀ r : ℕ, GoodTree n C (buildTree n C r) := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    rw [buildTree]
    split_ifs with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      classical
      have hchild_prop : ∀ u : ℕ, u < r →
          let ch := if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u
          ch.root n = u ∧ GoodTree n C ch ∧ (ch.nonMark → readsOf C u = 1) := by
        intro u hult
        dsimp only
        split_ifs with hu hun
        · refine ⟨rfl, ⟨hun, hu.2.1⟩, fun _ => hu.2.1⟩
        · refine ⟨buildTree_root n C u, ih u hult, fun _ => hu.2.1⟩
        · refine ⟨rfl, trivial, fun h => False.elim h⟩
      have hc0 := hchild_prop _ hu0_lt
      have hc1 := hchild_prop _ hu1_lt
      refine ⟨hj, hbin.1, ?_, hc0.2.1, hc1.2.1, ?_, ?_⟩
      · rw [hc0.1, hc1.1]
        exact hinp
      · rw [hc0.1]
        exact hc0.2.2
      · rw [hc1.1]
        exact hc1.2.2
    · exact h2
    · trivial

open Classical in
noncomputable def parentGate (C : Circuit) (w : ℕ) : ℕ :=
  if h : ∃ j ∈ gatesOf C, w ∈ (gateAt C j).inputs then Classical.choose h else 0

lemma parentGate_spec (C : Circuit) {w : ℕ} (h : readsOf C w = 1) :
    parentGate C w ∈ gatesOf C ∧ w ∈ (gateAt C (parentGate C w)).inputs ∧
    ∀ j ∈ gatesOf C, w ∈ (gateAt C j).inputs → j = parentGate C w := by
  obtain ⟨j, hj, hw, _, huniq⟩ := readsIn_eq_one_unique C (gatesOf C) w h
  have hex : ∃ j' ∈ gatesOf C, w ∈ (gateAt C j').inputs := ⟨j, hj, hw⟩
  have hdef : parentGate C w = Classical.choose hex := by
    unfold parentGate
    exact dif_pos hex
  rw [hdef]
  have hch := Classical.choose_spec hex
  have heq : Classical.choose hex = j := huniq _ hch.1 hch.2
  rw [heq]
  exact ⟨hj, hw, huniq⟩

open Classical in
noncomputable def owner (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if h : w < n + C.size ∧ readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not ∧
      w < n + parentGate C w then
    owner n C (n + parentGate C w)
  else w
termination_by n + C.size - w

open Classical in
lemma owner_step (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {w : ℕ}
    (hw1 : readsOf C w = 1) (hnot : (gateAt C (parentGate C w)).op ≠ GateOp.not) :
    owner n C w = owner n C (n + parentGate C w) := by
  obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hw1
  have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
  have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
  have hcond : w < n + C.size ∧ readsOf C w = 1 ∧
      (gateAt C (parentGate C w)).op ≠ GateOp.not ∧ w < n + parentGate C w :=
    ⟨by omega, hw1, hnot, hwlt⟩
  rw [owner]
  exact dif_pos hcond

lemma owner_fixed (n : ℕ) (C : Circuit) {w : ℕ}
    (h : ¬ (readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not)) :
    owner n C w = w := by
  rw [owner]
  split_ifs with h1
  · exact absurd ⟨h1.2.1, h1.2.2.1⟩ h
  · rfl

lemma owner_of_good_child (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {j u : ℕ}
    (hj : j < C.size) (hop : (gateAt C j).op ≠ GateOp.not)
    (hu : u ∈ (gateAt C j).inputs) (hr1 : readsOf C u = 1) :
    owner n C u = owner n C (n + j) := by
  obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
  have hpeq : j = parentGate C u := huniq j (Finset.mem_range.2 hj) hu
  rw [owner_step n C hback hr1 (by rwa [← hpeq]), ← hpeq]

open Classical in
lemma owner_eq_of_mem_wires (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ), ∀ w ∈ (buildTree n C r).wires n, owner n C w = owner n C r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro w hw
    rw [buildTree] at hw
    split_ifs at hw with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      have hchild : ∀ (u : ℕ), u ∈ (gateAt C (r - n)).inputs →
          w ∈ (if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u : BTree).wires n → owner n C w = owner n C r := by
        intro u hu hwu
        split_ifs at hwu with huc hun
        · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
            Finset.union_empty, Finset.mem_singleton] at hwu
          subst hwu
          rw [owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · rw [ih u huc.1 w hwu, owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · simp [BTree.wires, BTree.privs, BTree.gates] at hwu
      rw [BTree.wires_node] at hw
      simp only [Finset.mem_insert, Finset.mem_union] at hw
      rcases hw with rfl | hwl | hwr
      · rw [hnj]
      · exact hchild _ (by rw [hinp]; simp) hwl
      · exact hchild _ (by rw [hinp]; simp) hwr
    · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
        Finset.mem_singleton] at hw
      rw [hw]
    · simp [BTree.wires, BTree.privs, BTree.gates] at hw

open Classical in
lemma mem_wires_buildTree_owner (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (w : ℕ),
      ((w < n ∧ readsOf C w = 1) ∨
        (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not)) →
      w ∈ (buildTree n C (owner n C w)).wires n := by
  intro w
  induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
  | ind d ih =>
    intro hw
    by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
    · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
      have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
      have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
      have hown : owner n C w = owner n C (n + parentGate C w) :=
        owner_step n C hback hstep.1 hstep.2
      have hnp_in : n + parentGate C w ∈ (buildTree n C (owner n C (n + parentGate C w))).wires n :=
        ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      rw [hown]
      have hrec : ∀ (r : ℕ), n + parentGate C w ∈ (buildTree n C r).wires n →
          w ∈ (buildTree n C r).wires n := by
        intro r
        induction r using Nat.strong_induction_on with
        | ind r ihr =>
          intro hrw
          rw [buildTree] at hrw ⊢
          split_ifs at hrw ⊢ with h1 h2
          · have hj : r - n < C.size := h1.2.1
            have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
            have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
              rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
              · exact ⟨trivial, hl⟩
              · exact absurd hn h1.2.2
            have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
            have hnj : n + (r - n) = r := by omega
            rw [BTree.wires_node] at hrw ⊢
            simp only [Finset.mem_insert, Finset.mem_union] at hrw ⊢
            rcases hrw with hreq | hwl | hwr
            · have hpeq : r - n = parentGate C w := by omega
              have hwin_r : w ∈ (gateAt C (r - n)).inputs := by rwa [hpeq]
              rw [hinp] at hwin_r
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin_r
              have hint_w : isInternalChild n C w := by
                refine ⟨hstep.1, ?_⟩
                rintro ⟨hle, _, hnot⟩
                rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
                · omega
                · exact hne hnot
              have hw_in_child : ∀ u : ℕ, w = u →
                  w ∈ (if hu : u < r ∧ isInternalChild n C u then
                    if u < n then BTree.priv u else buildTree n C u
                  else BTree.mark u : BTree).wires n := by
                intro u hu
                subst hu
                have hcond : w < r ∧ isInternalChild n C w := ⟨by omega, hint_w⟩
                rw [dif_pos hcond]
                by_cases hwn : w < n
                · rw [if_pos hwn]
                  simp [BTree.wires, BTree.privs]
                · rw [if_neg hwn, buildTree]
                  have hwb : n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not := by
                    rcases hw with ⟨hlt, _⟩ | hgood
                    · omega
                    · exact hgood
                  rw [dif_pos hwb, BTree.wires_node]
                  have : n + (w - n) = w := by omega
                  rw [this]
                  exact Finset.mem_insert_self _ _
              rcases hwin_r with h0 | h1'
              · exact Or.inr (Or.inl (hw_in_child _ h0))
              · exact Or.inr (Or.inr (hw_in_child _ h1'))
            · refine Or.inr (Or.inl ?_)
              split_ifs at hwl ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwl
                omega
              · exact ihr _ huc.1 hwl
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwl
            · refine Or.inr (Or.inr ?_)
              split_ifs at hwr ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwr
                omega
              · exact ihr _ huc.1 hwr
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwr
          · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
              Finset.mem_singleton] at hrw
            omega
          · simp [BTree.wires, BTree.privs, BTree.gates] at hrw
      exact hrec _ hnp_in
    · rw [owner_fixed n C hstep, buildTree]
      rcases hw with ⟨hlt, hr1⟩ | hbin
      · have hnotb : ¬ (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not) := by omega
        rw [dif_neg hnotb, if_pos ⟨hlt, hr1⟩]
        simp [BTree.wires, BTree.privs, BTree.gates]
      · rw [dif_pos hbin, BTree.wires_node]
        have : n + (w - n) = w := by omega
        rw [this]
        exact Finset.mem_insert_self _ _

lemma mem_privs_iff_lt (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ w, w ∈ t.privs ↔ w ∈ t.wires n ∧ w < n := by
  induction t with
  | priv u =>
    intro w
    simp only [BTree.privs, BTree.wires, BTree.gates, Finset.image_empty, Finset.union_empty,
      Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, ht.1⟩
    · exact fun h => h.1
  | mark _ =>
    intro w
    simp [BTree.privs, BTree.wires, BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro w
    rw [BTree.wires_node]
    simp only [BTree.privs, Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · have := (ihl hgl w).1 h
        exact ⟨Or.inr (Or.inl this.1), this.2⟩
      · have := (ihr hgr w).1 h
        exact ⟨Or.inr (Or.inr this.1), this.2⟩
    · rintro ⟨rfl | h | h, hlt⟩
      · omega
      · exact Or.inl ((ihl hgl w).2 ⟨h, hlt⟩)
      · exact Or.inr ((ihr hgr w).2 ⟨h, hlt⟩)

lemma mem_gates_iff_ge (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ k, k ∈ t.gates ↔ n + k ∈ t.wires n := by
  induction t with
  | priv u =>
    intro k
    have hu : u < n := ht.1
    simp only [BTree.gates, BTree.wires, BTree.privs, Finset.image_empty, Finset.union_empty,
      Finset.notMem_empty, Finset.mem_singleton, false_iff]
    omega
  | mark _ =>
    intro k
    simp [BTree.gates, BTree.wires, BTree.privs]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro k
    rw [BTree.wires_node]
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
    rw [ihl hgl k, ihr hgr k]
    constructor
    · rintro (rfl | h | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (heq | h | h)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

open Classical in
lemma buildTree_marks_eq_sum (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ),
      ((r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)) →
      (buildTree n C r).marks =
        ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hgt := buildTree_good n C hshape hback r
    have hdisj_from_good := (good_internal_reads hback hout hgt).2
    have hnot_from_good : ∀ j l r', buildTree n C r = BTree.node j l r' → j ∉ l.gates ∧ j ∉ r'.gates := by
      intro j l r' heq
      rw [heq] at hgt
      exact good_node_not_mem_sub hback hgt
    rw [buildTree] at hgt hdisj_from_good hnot_from_good ⊢
    split_ifs at hgt hdisj_from_good hnot_from_good ⊢ with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      set ch : ℕ → BTree := fun u =>
        if hu : u < r ∧ isInternalChild n C u then
          if u < n then BTree.priv u else buildTree n C u
        else BTree.mark u
      have hnot := good_node_not_mem_sub hback hgt
      have hdisjw := hdisj_from_good (r - n) _ _ rfl
      have hdisjg : Disjoint (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates := by
        rw [Finset.disjoint_left]
        intro k hkl hkr
        exact Finset.disjoint_left.1 hdisjw
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
      have hj_not_u : r - n ∉ (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates ∪
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates :=
        Finset.notMem_union.2 hnot
      simp only [BTree.marks, BTree.gates]
      rw [Finset.sum_insert hj_not_u, Finset.sum_union hdisjg]
      have hch_eq : ∀ u : ℕ, u < r →
          (ch u).marks =
            (if ¬ isInternalChild n C u then 1 else 0) +
            ∑ j ∈ (ch u).gates,
              @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
                (gateAt C j).inputs := by
        intro u hult
        dsimp only [ch]
        by_cases huc : u < r ∧ isInternalChild n C u
        · rw [dif_pos huc, if_neg (not_not.2 huc.2), zero_add]
          by_cases hun : u < n
          · rw [if_pos hun]
            simp [BTree.marks, BTree.gates]
          · rw [if_neg hun]
            have hvalid : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op ≠ GateOp.not :=
              ⟨by omega, by omega, fun hnot => huc.2.2 ⟨by omega, by omega, hnot⟩⟩
            exact ih u hult (Or.inr hvalid)
        · rw [dif_neg huc]
          have hni : ¬ isInternalChild n C u := fun hi => huc ⟨hult, hi⟩
          rw [if_pos hni]
          simp [BTree.marks, BTree.gates]
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      rw [hch_eq _ hu0_lt, hch_eq _ hu1_lt]
      have hcnt_pair :
          @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
            (gateAt C (r - n)).inputs =
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 0 0) then 1 else 0) +
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 1 0) then 1 else 0) := by
        conv_lhs => rw [hinp]
        simp only [List.countP_cons, List.countP_nil]
        have hdec : ∀ (P : Prop),
            (if (@decide P (Classical.propDecidable P)) = true then 1 else 0) =
            if P then 1 else 0 := by
          intro P
          by_cases hP : P
          · rw [@decide_eq_true P (Classical.propDecidable P) hP, if_pos rfl, if_pos hP]
          · rw [@decide_eq_false P (Classical.propDecidable P) hP, if_neg Bool.false_ne_true, if_neg hP]
        rw [hdec, hdec, Nat.zero_add, Nat.add_comm]
        congr 1
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
      rw [hcnt_pair]
      omega
    · simp [BTree.marks, BTree.gates]
    · rcases hr with h | h
      · exact absurd h h2
      · exact absurd h h1

lemma list_countP_le_sum_count (l : List ℕ) (S : Finset ℕ) :
    @List.countP ℕ (fun u => @decide (u ∈ S) (Classical.propDecidable _)) l =
      ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    simp only [List.countP_cons, List.count_cons, Finset.sum_add_distrib, ih]
    have h1 : (∑ w ∈ S, if a == w then 1 else 0) = if a ∈ S then 1 else 0 := by
      by_cases ha : a ∈ S
      · rw [if_pos ha, Finset.sum_eq_single a]
        · simp
        · intro w _ hwa
          simp [beq_eq_false_iff_ne.2 (Ne.symm hwa)]
        · intro h
          exact absurd ha h
      · rw [if_neg ha, Finset.sum_eq_zero]
        intro w hw
        have hne : a ≠ w := fun h => ha (h ▸ hw)
        simp [beq_eq_false_iff_ne.2 hne]
    rw [h1]
    by_cases ha : a ∈ S <;> simp [ha] <;> omega

lemma list_flatMap_collect {α : Type*} [DecidableEq α] (L : List α) (f : α → List (Finset ℕ))
    (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ S ∈ f a, S ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise Disjoint)
    (hf_cov : ∀ a ∈ L, (f a).toFinset.biUnion (fun S => S) = g a) :
    (L.flatMap f).Pairwise Disjoint ∧
    (L.flatMap f).toFinset.biUnion (fun S => S) = L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ S ∈ f a, S ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw : (f a).Pairwise Disjoint := hf_pw a (List.mem_cons_self ..)
    have hfa_cov : (f a).toFinset.biUnion (fun S => S) = g a := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun S1 h1 S2 h2 => ?_⟩
      obtain ⟨b, hb, hS2⟩ := List.mem_flatMap.1 h2
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub S1 h1) (hf_sub b (List.mem_cons_of_mem a hb) S2 hS2)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov, hrec.2.1,
        List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

lemma forest_extract (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C)
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (n + j)) :
    let gates := Finset.range C.size
    let gate := gateAt C
    let reads := readsIn C gates
    let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
      (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (R : Finset ℕ) (tree : ℕ → BTree),
      R.card ≤ sharedGates.card + neg.card + 1 ∧
      (∀ r ∈ R, GoodTree n C (tree r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (tree r).privs (tree s).privs) ∧
      R.biUnion (fun r => (tree r).privs) = once ∧
      (∑ r ∈ R, (tree r).marks) ≤ markedReads + neg.card := by
  classical
  intro gates gate reads neg shared sharedGates markedReads once
  let validRoot : ℕ → Prop := fun r =>
    (r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)
  let Rout : Finset ℕ := if (gateAt C (C.size - 1)).op ≠ GateOp.not then {C.output} else ∅
  let Rsh : Finset ℕ :=
    (sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not)).image (fun k => n + k)
  let Rneg : Finset ℕ :=
    (neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0))).image
      (fun j => (gateAt C j).inputs.getD 0 0)
  let Roots : Finset ℕ := Rout ∪ Rsh ∪ Rneg
  have hRout_card : Rout.card ≤ 1 := by
    dsimp only [Rout]
    split_ifs <;> simp
  have hRsh_card : Rsh.card ≤ sharedGates.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRneg_card : Rneg.card ≤ neg.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRoots_le3 : Roots.card ≤ Rout.card + Rsh.card + Rneg.card :=
    (Finset.card_union_le (Rout ∪ Rsh) Rneg).trans
      (Nat.add_le_add_right (Finset.card_union_le Rout Rsh) _)
  have hRoots_card : Roots.card ≤ sharedGates.card + neg.card + 1 := by
    omega
  have hRoots_valid : ∀ r ∈ Roots, validRoot r := by
    intro r hr
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        exact Or.inr ⟨by omega, by omega, by rwa [show C.output - n = C.size - 1 by omega]⟩
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates, gates, Finset.mem_range] at hk
      exact Or.inr ⟨by omega, by omega, by simpa using hk.2⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      have hlt : (gateAt C j).inputs.getD 0 0 < n + j := hback j hj.1.1 _ hmem0
      by_cases hlt_n : (gateAt C j).inputs.getD 0 0 < n
      · exact Or.inl ⟨hlt_n, hj.2.1⟩
      · exact Or.inr ⟨by omega, by omega, fun hnot => hj.2.2 ⟨by omega, by omega, hnot⟩⟩
  have hRoots_fixed : ∀ r ∈ Roots, owner n C r = r := by
    intro r hr
    refine owner_fixed n C ?_
    rintro ⟨hr1, hnot⟩
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        have hz := reads_output_zero n C hback hout
        omega
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates] at hk
      have h2r : 2 ≤ readsOf C (n + k) := hk.1.2
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
      have hpeq : j = parentGate C ((gateAt C j).inputs.getD 0 0) :=
        huniq j (Finset.mem_range.2 hj.1.1) hmem0
      rw [← hpeq] at hnot
      exact hnot hj.1.2
  have howner_mem : ∀ w : ℕ, validRoot w → owner n C w ∈ Roots := by
    intro w
    induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
    | ind d ih =>
      intro hw
      by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
      · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
        have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
        have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
        rw [owner_step n C hback hstep.1 hstep.2]
        exact ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      · rw [owner_fixed n C hstep]
        by_cases hr1 : readsOf C w = 1
        · have hpnot : (gateAt C (parentGate C w)).op = GateOp.not := by
            by_contra hne
            exact hstep ⟨hr1, hne⟩
          obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hr1
          have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
          have hgs := hshape (gateAt C (parentGate C w)) (gateAt_mem_gates C hplt)
          have hlen1 : (gateAt C (parentGate C w)).inputs.length = 1 := by
            rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
            · rcases ho with ho | ho <;> rw [hpnot] at ho <;> cases ho
            · exact hl
          have hweq : (gateAt C (parentGate C w)).inputs.getD 0 0 = w := by
            rw [list_len1_eq _ hlen1] at hpw
            simp only [List.mem_singleton] at hpw
            exact hpw.symm
          have hint : isInternalChild n C w := by
            refine ⟨hr1, ?_⟩
            rintro ⟨hle, _, hnot⟩
            rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
            · omega
            · exact hne hnot
          refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨parentGate C w, ?_, hweq⟩)
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.2 ⟨hpG, hpnot⟩, by rwa [hweq]⟩
        · rcases hw with ⟨_, hr1'⟩ | ⟨hle, hlt, hne⟩
          · exact absurd hr1' hr1
          · by_cases hlast : w - n = C.size - 1
            · have hwout : w = C.output := by omega
              subst hwout
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              dsimp only [Rout]
              have hop : (gateAt C (C.size - 1)).op ≠ GateOp.not := by
                rwa [← hlast]
              simp [hop]
            · have hpos := hused (w - n) hlt (by omega)
              have hge2 : 2 ≤ readsOf C (n + (w - n)) := by
                have heq : n + (w - n) = w := by omega
                rw [heq] at hpos ⊢
                change 0 < readsOf C w at hpos
                omega
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_image.2 ⟨w - n, ?_, by omega⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hge2⟩, hne⟩
  have hpriv_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).privs (buildTree n C r2).privs := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 w (Finset.mem_union_left _ hw1)
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 w (Finset.mem_union_left _ hw2)
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hgates_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).gates (buildTree n C r2).gates := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk1, rfl⟩))
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk2, rfl⟩))
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hpriv_cov : Roots.biUnion (fun r => (buildTree n C r).privs) = once := by
    ext w
    simp only [Finset.mem_biUnion, once, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, hwp⟩
      have hgt := buildTree_good n C hshape hback r
      have hlt := ((mem_privs_iff_lt n C hgt w).1 hwp).2
      have hwr : readsOf C w = 1 := by
        by_cases hweq : w = r
        · subst hweq
          rcases hRoots_valid w hr with ⟨_, hr1⟩ | ⟨hle, _, _⟩
          · exact hr1
          · omega
        · have hroot : (buildTree n C r).root n = r := buildTree_root n C r
          exact ((good_internal_reads hback hout hgt).1 w (Finset.mem_union_left _ hwp)
            (by rwa [hroot])).2.1
      exact ⟨hlt, hwr⟩
    · rintro ⟨hlt, hr1⟩
      have hmemR : owner n C w ∈ Roots := howner_mem w (Or.inl ⟨hlt, hr1⟩)
      refine ⟨owner n C w, hmemR, ?_⟩
      have hw := mem_wires_buildTree_owner n C hback hshape w (Or.inl ⟨hlt, hr1⟩)
      exact (mem_privs_iff_lt n C (buildTree_good n C hshape hback _) w).2 ⟨hw, hlt⟩
  have hsum_marks : ∑ r ∈ Roots, (buildTree n C r).marks ≤ markedReads + neg.card := by
    have h1 : ∑ r ∈ Roots, (buildTree n C r).marks =
        ∑ r ∈ Roots, ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_congr rfl (fun r hr => buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hr))
    rw [h1, ← Finset.sum_biUnion (fun r1 hr1 r2 hr2 hne => hgates_disj r1 hr1 r2 hr2 hne)]
    have hsub_g : Roots.biUnion (fun r => (buildTree n C r).gates) ⊆ gates := by
      intro j hj
      obtain ⟨r, _, hjr⟩ := Finset.mem_biUnion.1 hj
      exact good_gates_sub (buildTree_good n C hshape hback r) hjr
    have hle1 :
        ∑ j ∈ Roots.biUnion (fun r => (buildTree n C r).gates),
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_le_sum_of_subset hsub_g
    let negOnly : Finset ℕ := (neg.filter (fun k => readsOf C (n + k) = 1)).image (fun k => n + k)
    have hterm_le : ∀ j ∈ gates,
        @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
          (gateAt C j).inputs ≤
        @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
          (gateAt C j).inputs +
        @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
          (gateAt C j).inputs := by
      intro j hj
      have hjlt : j < C.size := Finset.mem_range.1 hj
      have hgen : ∀ (l : List ℕ), (∀ u ∈ l, u < n + j) →
          (∀ u ∈ l, 1 ≤ readsOf C u) →
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _)) l ≤
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _)) l +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _)) l := by
        intro l
        induction l with
        | nil => intros; simp
        | cons u ls ih =>
          intro hlt_l hpos_l
          simp only [List.countP_cons]
          have ih' := ih (fun v hv => hlt_l v (List.mem_cons_of_mem u hv))
            (fun v hv => hpos_l v (List.mem_cons_of_mem u hv))
          have hult : u < n + j := hlt_l u (List.mem_cons_self ..)
          have hupos : 1 ≤ readsOf C u := hpos_l u (List.mem_cons_self ..)
          by_cases hni : ¬ isInternalChild n C u
          · have hor : u ∈ shared ∨ u ∈ negOnly := by
              by_cases hr2 : 2 ≤ readsOf C u
              · left
                exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr2⟩
              · right
                have hr1 : readsOf C u = 1 := by omega
                have hnotg : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not := by
                  by_contra h
                  exact hni ⟨hr1, h⟩
                refine Finset.mem_image.2 ⟨u - n, ?_, by omega⟩
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hnotg.2.1, hnotg.2.2⟩, ?_⟩
                have : n + (u - n) = u := by omega
                rwa [this]
            have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = true :=
              @decide_eq_true _ (Classical.propDecidable _) hni
            rw [hd1, if_pos rfl]
            rcases hor with hsh | hno
            · have hd2 : (@decide (u ∈ shared) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hsh
              rw [hd2, if_pos rfl]
              split_ifs <;> omega
            · have hd3 : (@decide (u ∈ negOnly) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hno
              rw [hd3, if_pos rfl]
              split_ifs <;> omega
          · have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = false :=
              @decide_eq_false _ (Classical.propDecidable _) hni
            rw [hd1]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split_ifs <;> omega
      exact hgen (gateAt C j).inputs (fun u hu => hback j hjlt u hu)
        (fun u hu => readsIn_ge_of_mem C hj hu)
    have hle2 :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          (@List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs) :=
      Finset.sum_le_sum hterm_le
    rw [Finset.sum_add_distrib] at hle2
    have hsum_sh :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs = markedReads := by
      simp_rw [list_countP_le_sum_count _ shared]
      rw [Finset.sum_comm]
      rfl
    have hsum_no :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs ≤ neg.card := by
      simp_rw [list_countP_le_sum_count _ negOnly]
      rw [Finset.sum_comm]
      calc ∑ w ∈ negOnly, readsOf C w
          = ∑ _w ∈ negOnly, 1 := by
            refine Finset.sum_congr rfl (fun w hw => ?_)
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
            exact (Finset.mem_filter.1 hk).2
        _ = negOnly.card := by simp
        _ ≤ neg.card := (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    omega
  exact ⟨Roots, buildTree n C, hRoots_card,
    fun r _ => buildTree_good n C hshape hback r, hpriv_disj, hpriv_cov, hsum_marks⟩


def binarySkeleton (C : PEqualNP.MetaComplexity.BinaryCircuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨GateOp.and, [g.left, g.right]⟩), C.output⟩

lemma binarySkeleton_size (C : PEqualNP.MetaComplexity.BinaryCircuit) :
    (binarySkeleton C).size = C.size := by
  simp [binarySkeleton, Circuit.size, PEqualNP.MetaComplexity.BinaryCircuit.size]

lemma binarySkeleton_shape (C : PEqualNP.MetaComplexity.BinaryCircuit) :
    ∀ g ∈ (binarySkeleton C).gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) := by
  intro g hg
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hg
  exact Or.inl ⟨Or.inl rfl, rfl⟩

lemma binarySkeleton_gate (C : PEqualNP.MetaComplexity.BinaryCircuit) (j : ℕ)
    (hj : j < C.gates.length) :
    gateAt (binarySkeleton C) j =
      ⟨GateOp.and, [(C.gates[j]).left, (C.gates[j]).right]⟩ := by
  simp [gateAt, binarySkeleton, List.getD_eq_getElem, hj]

lemma binarySkeleton_back (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ∀ (j : ℕ) (hj : j < C.gates.length),
      (C.gates[j]).left < n + j ∧ (C.gates[j]).right < n + j) :
    ReadsBack n (binarySkeleton C) := by
  intro j hj w hw
  have hj' : j < C.gates.length := by simpa [binarySkeleton, Circuit.size] using hj
  rw [binarySkeleton_gate C j hj'] at hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hback j hj').1
  · exact (hback j hj').2

lemma binarySkeleton_forest (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ReadsBack n (binarySkeleton C))
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size →
      0 < readsOf (binarySkeleton C) (n + j)) :
    let reads := readsOf (binarySkeleton C)
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := (Finset.range C.size).filter (fun j => 2 ≤ reads (n + j))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (R : Finset ℕ) (tree : ℕ → BTree),
      R.card ≤ sharedGates.card + 1 ∧
      (∀ r ∈ R, GoodTree n (binarySkeleton C) (tree r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (tree r).privs (tree s).privs) ∧
      R.biUnion (fun r => (tree r).privs) = once ∧
      (∑ r ∈ R, (tree r).marks) ≤ markedReads := by
  classical
  have negEmpty : (Finset.range (binarySkeleton C).size).filter
      (fun k => (gateAt (binarySkeleton C) k).op = GateOp.not) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj
    have hj' : j < C.gates.length := by
      have hj'' := Finset.mem_range.mp hj
      simpa [binarySkeleton, Circuit.size] using hj''
    rw [binarySkeleton_gate C j hj']
    exact GateOp.noConfusion
  have result := forest_extract n (binarySkeleton C) (binarySkeleton_shape C) hback
    (by simpa only [binarySkeleton_size] using hsz)
    (by rw [binarySkeleton_size]; exact hout)
    (by simpa only [readsOf, binarySkeleton_size] using hused)
  dsimp only at result ⊢
  rw [negEmpty] at result
  simpa only [readsOf, binarySkeleton_size, Finset.card_empty, Nat.add_zero] using result

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def BTree.privateMultiset : BTree → Multiset ℕ
  | .priv w => {w}
  | .mark _ => 0
  | .node _ l r => l.privateMultiset + r.privateMultiset

def BTree.cutDecompose (n : ℕ) : BTree → BTree × List BTree
  | .priv w => (.priv w, [])
  | .mark w => (.mark w, [])
  | .node j l r =>
    if l.marks = 0 then
      (.node j l (r.cutDecompose n).1, (r.cutDecompose n).2)
    else if r.marks = 0 then
      (.node j (l.cutDecompose n).1 r, (l.cutDecompose n).2)
    else
      (.mark (n + j), (l.cutDecompose n).1 :: (l.cutDecompose n).2 ++
        (r.cutDecompose n).1 :: (r.cutDecompose n).2)

def BTree.cutPieces (n : ℕ) (t : BTree) : List BTree :=
  (t.cutDecompose n).1 :: (t.cutDecompose n).2

lemma BTree.cutDecompose_root (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.root n = t.root n := by
  cases t with
  | priv w => rfl
  | mark w => rfl
  | node j l r =>
    simp only [cutDecompose]
    split_ifs <;> rfl

lemma BTree.cutDecompose_nonMark (n : ℕ) (t : BTree)
    (h : (t.cutDecompose n).1.nonMark) : t.nonMark := by
  cases t with
  | priv w => trivial
  | mark w => exact h
  | node j l r => trivial

lemma BTree.cutDecompose_pure (n : ℕ) (t : BTree) (h : t.marks = 0) :
    t.cutDecompose n = (t, []) := by
  induction t with
  | priv w => rfl
  | mark w => simp [marks] at h
  | node j l r ihl ihr =>
    have hl : l.marks = 0 := by simp only [marks] at h; omega
    have hr : r.marks = 0 := by simp only [marks] at h; omega
    simp [cutDecompose, hl, ihr hr]

lemma BTree.cutDecompose_top_marks (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.marks ≤ 1 := by
  induction t with
  | priv w => simp [cutDecompose, marks]
  | mark w => simp [cutDecompose, marks]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl, marks] using ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr, marks] using ihl
      · simp [cutDecompose, hl, hr, marks]

lemma BTree.cutDecompose_rest_marks (n : ℕ) (t : BTree) :
    ∀ p ∈ (t.cutDecompose n).2, p.marks ≤ 1 := by
  induction t with
  | priv w => simp [cutDecompose]
  | mark w => simp [cutDecompose]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl] using ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr] using ihl
      · intro p hp
        simp only [cutDecompose, if_neg hl, if_neg hr, List.mem_cons, List.mem_append] at hp
        rcases hp with (rfl | hp) | (rfl | hp)
        · exact cutDecompose_top_marks n l
        · exact ihl p hp
        · exact cutDecompose_top_marks n r
        · exact ihr p hp

lemma BTree.cutDecompose_length (n : ℕ) (t : BTree) (h : 0 < t.marks) :
    (t.cutDecompose n).2.length + 2 ≤ 2 * t.marks := by
  induction t with
  | priv w => simp [marks] at h
  | mark w => simp [cutDecompose, marks]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · have hr : 0 < r.marks := by simp only [marks] at h; omega
      simpa [cutDecompose, hl, marks] using ihr hr
    · by_cases hr : r.marks = 0
      · have hl' : 0 < l.marks := by omega
        simpa [cutDecompose, hl, hr, marks] using ihl hl'
      · have hl' := ihl (by omega : 0 < l.marks)
        have hr' := ihr (by omega : 0 < r.marks)
        simp only [cutDecompose, if_neg hl, if_neg hr, List.length_cons,
          List.length_append, marks]
        omega

lemma BTree.cutDecompose_leaves (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.privateMultiset +
      ((t.cutDecompose n).2.map privateMultiset).sum = t.privateMultiset := by
  induction t with
  | priv w => simp [cutDecompose, privateMultiset]
  | mark w => simp [cutDecompose, privateMultiset]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl, privateMultiset, add_assoc] using
        congrArg (fun z => l.privateMultiset + z) ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr, privateMultiset, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z => z + r.privateMultiset) ihl
      · simp only [cutDecompose, if_neg hl, if_neg hr, privateMultiset, List.map_cons,
          List.map_append, List.sum_cons, List.sum_append, zero_add]
        rw [← add_assoc, ihl, add_assoc, ihr]

lemma BTree.mem_privateMultiset (t : BTree) (w : ℕ) :
    w ∈ t.privateMultiset ↔ w ∈ t.privs := by
  induction t with
  | priv a => simp [privateMultiset, privs]
  | mark a => simp [privateMultiset, privs]
  | node j l r ihl ihr => simp [privateMultiset, privs, ihl, ihr]

lemma BTree.cutDecompose_top_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) : GoodTree n C (t.cutDecompose n).1 := by
  induction t with
  | priv w => exact ht
  | mark w => trivial
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hrl, hrr⟩
    by_cases hl : l.marks = 0
    · simp only [cutDecompose, if_pos hl]
      refine ⟨hj, hop, ?_, hgl, ihr hgr, hrl, ?_⟩
      · simpa only [cutDecompose_root] using hinp
      · intro h
        rw [cutDecompose_root]
        exact hrr (cutDecompose_nonMark n r h)
    · by_cases hr : r.marks = 0
      · simp only [cutDecompose, if_neg hl, if_pos hr]
        refine ⟨hj, hop, ?_, ihl hgl, hgr, ?_, hrr⟩
        · simpa only [cutDecompose_root] using hinp
        · intro h
          rw [cutDecompose_root]
          exact hrl (cutDecompose_nonMark n l h)
      · simp [cutDecompose, hl, hr, GoodTree]

lemma BTree.cutDecompose_rest_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) : ∀ p ∈ (t.cutDecompose n).2, GoodTree n C p := by
  induction t with
  | priv w => simp [cutDecompose]
  | mark w => simp [cutDecompose]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hrl, hrr⟩
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl] using ihr hgr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr] using ihl hgl
      · intro p hp
        simp only [cutDecompose, if_neg hl, if_neg hr, List.mem_cons, List.mem_append] at hp
        rcases hp with (rfl | hp) | (rfl | hp)
        · exact cutDecompose_top_good hgl
        · exact ihl hgl p hp
        · exact cutDecompose_top_good hgr
        · exact ihr hgr p hp

lemma BTree.privateMultiset_nodup {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) : t.privateMultiset.Nodup := by
  induction t with
  | priv w => simp [privateMultiset]
  | mark w => simp [privateMultiset]
  | node j l r ihl ihr =>
    have hd := (good_internal_reads hback hout ht).2 j l r rfl
    have hgl := ht.2.2.2.1
    have hgr := ht.2.2.2.2.1
    rw [privateMultiset, Multiset.nodup_add]
    refine ⟨ihl hgl, ihr hgr, ?_⟩
    rw [Multiset.disjoint_left]
    intro w hw1 hw2
    exact Finset.disjoint_left.1 hd
      (Finset.mem_union_left _ ((mem_privateMultiset l w).1 hw1))
      (Finset.mem_union_left _ ((mem_privateMultiset r w).1 hw2))

lemma btree_multiset_sum_nodup_pairwise (L : List (Multiset ℕ)) (h : L.sum.Nodup) :
    L.Pairwise Disjoint := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons s L ih =>
    rw [List.sum_cons, Multiset.nodup_add] at h
    refine List.pairwise_cons.2 ⟨?_, ih h.2.1⟩
    intro r hr
    exact Disjoint.mono_right (List.le_sum_of_mem hr) h.2.2

lemma BTree.cutPieces_leaves (n : ℕ) (t : BTree) :
    ((t.cutPieces n).map privateMultiset).sum = t.privateMultiset := by
  simpa [cutPieces] using cutDecompose_leaves n t

lemma BTree.cutPieces_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) :
    ∀ p ∈ t.cutPieces n, GoodTree n C p ∧ p.marks ≤ 1 := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨cutDecompose_top_good ht, cutDecompose_top_marks n t⟩
  · exact ⟨cutDecompose_rest_good ht p hp, cutDecompose_rest_marks n t p hp⟩

lemma BTree.cutPieces_length_pos (n : ℕ) (t : BTree) (h : 0 < t.marks) :
    (t.cutPieces n).length + 1 ≤ 2 * t.marks := by
  simpa [cutPieces, Nat.add_assoc] using cutDecompose_length n t h

lemma BTree.cutPieces_length_zero (n : ℕ) (t : BTree) (h : t.marks = 0) :
    (t.cutPieces n).length = 1 := by
  simp [cutPieces, cutDecompose_pure n t h]

lemma BTree.cutPieces_length (n : ℕ) (t : BTree) :
    (t.cutPieces n).length ≤ 2 * t.marks + 1 := by
  by_cases h : t.marks = 0
  · simp [cutPieces_length_zero n t h, h]
  · have := cutPieces_length_pos n t (by omega)
    omega

lemma BTree.cutPieces_disjoint {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) :
    (t.cutPieces n).Pairwise (fun p q => Disjoint p.privs q.privs) := by
  have hs : (((t.cutPieces n).map privateMultiset).sum).Nodup := by
    rw [cutPieces_leaves]
    exact privateMultiset_nodup hback hout ht
  have hp := btree_multiset_sum_nodup_pairwise _ hs
  rw [List.pairwise_map] at hp
  refine hp.imp (fun {p q} hd => ?_)
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  exact Multiset.disjoint_left.1 hd
    ((mem_privateMultiset p w).2 hw1) ((mem_privateMultiset q w).2 hw2)

lemma btree_mem_multiset_list_sum (L : List (Multiset ℕ)) (w : ℕ) :
    w ∈ L.sum ↔ ∃ s ∈ L, w ∈ s := by
  induction L with
  | nil => simp
  | cons s L ih => simp [ih]

lemma BTree.cutPieces_cover (n : ℕ) (t : BTree) :
    (@List.toFinset BTree (Classical.decEq _) (t.cutPieces n)).biUnion BTree.privs = t.privs := by
  classical
  ext w
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  rw [← mem_privateMultiset t w, ← cutPieces_leaves n t,
    btree_mem_multiset_list_sum]
  constructor
  · rintro ⟨p, hp, hw⟩
    exact ⟨p.privateMultiset, List.mem_map.2 ⟨p, hp, rfl⟩,
      (mem_privateMultiset p w).2 hw⟩
  · rintro ⟨s, hs, hws⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    exact ⟨p, hp, (mem_privateMultiset p w).1 hws⟩

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def paintBad (bad : Finset ℕ) : BTree → BTree
  | .priv w => if w ∈ bad then .mark w else .priv w
  | .mark w => .mark w
  | .node j l r => .node j (paintBad bad l) (paintBad bad r)

lemma paintBad_root (bad : Finset ℕ) (n : ℕ) (t : BTree) :
    (paintBad bad t).root n = t.root n := by
  cases t <;> simp only [paintBad, BTree.root]
  split_ifs <;> rfl

lemma paintBad_nonMark (bad : Finset ℕ) (t : BTree) :
    (paintBad bad t).nonMark → t.nonMark := by
  cases t <;> simp only [paintBad, BTree.nonMark]
  · intro _; trivial
  · exact False.elim
  · intro _; trivial

lemma paintBad_privs (bad : Finset ℕ) (t : BTree) :
    (paintBad bad t).privs = t.privs \ bad := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad <;> ext x <;> simp [paintBad, BTree.privs, hw] <;> aesop
  | mark w => simp [paintBad, BTree.privs]
  | node j l r ihl ihr =>
    ext w
    simp only [paintBad, BTree.privs, ihl, ihr, Finset.mem_union, Finset.mem_sdiff]
    tauto

lemma paintBad_good {n : ℕ} {C : Circuit} (bad : Finset ℕ) {t : BTree}
    (ht : GoodTree n C t) : GoodTree n C (paintBad bad t) := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad
    · simp [paintBad, hw, GoodTree]
    · simpa [paintBad, hw] using ht
  | mark w => trivial
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl, hr⟩
    refine ⟨hj, hop, ?_, ihl hgl, ihr hgr, ?_, ?_⟩
    · simpa only [paintBad_root] using hinp
    · simpa only [paintBad_root] using fun h => hl (paintBad_nonMark bad l h)
    · simpa only [paintBad_root] using fun h => hr (paintBad_nonMark bad r h)

lemma paintBad_marks {n : ℕ} {C : Circuit} (bad : Finset ℕ)
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) :
    (paintBad bad t).marks = t.marks + (t.privs ∩ bad).card := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad <;> simp [paintBad, BTree.marks, BTree.privs, hw]
  | mark w => simp [paintBad, BTree.marks, BTree.privs]
  | node j l r ihl ihr =>
    have disj := (good_internal_reads hback hout ht).2 j l r rfl
    have dp : Disjoint l.privs r.privs :=
      Disjoint.mono Finset.subset_union_left Finset.subset_union_left disj
    have di : Disjoint (l.privs ∩ bad) (r.privs ∩ bad) :=
      Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left dp
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl, hr⟩
    simp only [paintBad, BTree.marks, BTree.privs, ihl hgl, ihr hgr,
      Finset.union_inter_distrib_right, Finset.card_union_of_disjoint di]
    omega

lemma paintBad_marks_forest {n : ℕ} {C : Circuit} (bad R : Finset ℕ)
    (tree : ℕ → BTree) (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    (good : ∀ r ∈ R, GoodTree n C (tree r))
    (disj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (tree r).privs (tree s).privs) :
    (∑ r ∈ R, (paintBad bad (tree r)).marks) ≤
      (∑ r ∈ R, (tree r).marks) + bad.card := by
  have count : (∑ r ∈ R, ((tree r).privs ∩ bad).card) ≤ bad.card := by
    have dj : (R : Set ℕ).Pairwise (fun r s =>
        Disjoint ((tree r).privs ∩ bad) ((tree s).privs ∩ bad)) := by
      intro r hr s hs hne
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (disj r hr s hs hne)
    rw [← Finset.card_biUnion dj]
    exact Finset.card_le_card (by
      intro w hw
      obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_inter.mp hr).2)
  calc
    (∑ r ∈ R, (paintBad bad (tree r)).marks) =
        ∑ r ∈ R, ((tree r).marks + ((tree r).privs ∩ bad).card) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact paintBad_marks bad hback hout (good r hr)
    _ = (∑ r ∈ R, (tree r).marks) + ∑ r ∈ R, ((tree r).privs ∩ bad).card :=
      Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left count _

lemma concrete_tree_bad_partition {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) (bad : Finset ℕ) {t : BTree}
    (ht : GoodTree n C t) :
    ∃ L : List BTree,
      L.length ≤ 2 * (t.marks + (t.privs ∩ bad).card) + 1 ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty ∧
        p.privs ⊆ t.privs \ bad) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs = t.privs \ bad := by
  classical
  let u := paintBad bad t
  let L := (u.cutPieces n).filter (fun p => decide p.privs.Nonempty)
  have hu : GoodTree n C u := paintBad_good bad ht
  have hcov : (@List.toFinset BTree (Classical.decEq _) (u.cutPieces n)).biUnion BTree.privs =
      t.privs \ bad := by
    rw [BTree.cutPieces_cover, paintBad_privs]
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · have hlen := BTree.cutPieces_length n u
    have hfilter : L.length ≤ (u.cutPieces n).length := List.length_filter_le _ _
    have hm : u.marks = t.marks + (t.privs ∩ bad).card := paintBad_marks bad hback hout ht
    omega
  · intro p hp
    have hpf := List.mem_filter.1 hp
    have hg := BTree.cutPieces_good hu p hpf.1
    refine ⟨hg.1, hg.2, of_decide_eq_true hpf.2, ?_⟩
    intro w hw
    rw [← hcov]
    exact Finset.mem_biUnion.2 ⟨p, List.mem_toFinset.2 hpf.1, hw⟩
  · exact (BTree.cutPieces_disjoint hback hout hu).filter _
  · ext w
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · rintro ⟨p, hp, hw⟩
      rw [← hcov]
      exact Finset.mem_biUnion.2 ⟨p, List.mem_toFinset.2 (List.mem_filter.1 hp).1, hw⟩
    · intro hw
      rw [← hcov] at hw
      obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.1 hw
      refine ⟨p, List.mem_filter.2 ⟨List.mem_toFinset.1 hp, ?_⟩, hwp⟩
      exact decide_eq_true ⟨w, hwp⟩

lemma concrete_flatmap_collect {α : Type*} [DecidableEq α] (L : List α)
    (f : α → List BTree) (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ p ∈ f a, p.privs ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise (fun p q => Disjoint p.privs q.privs))
    (hf_cov : ∀ a ∈ L,
      (@List.toFinset BTree (Classical.decEq _) (f a)).biUnion BTree.privs = g a) :
    (L.flatMap f).Pairwise (fun p q => Disjoint p.privs q.privs) ∧
    (@List.toFinset BTree (Classical.decEq _) (L.flatMap f)).biUnion BTree.privs =
      L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  classical
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ p ∈ f a, p.privs ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw := hf_pw a (List.mem_cons_self ..)
    have hfa_cov := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun p hp q hq => ?_⟩
      obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub p hp) (hf_sub b (List.mem_cons_of_mem a hb) q hqb)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov,
        hrec.2.1, List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

lemma concrete_forest_inter_sum_le (R : Finset ℕ) (f : ℕ → Finset ℕ) (bad : Finset ℕ)
    (hd : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (f a) (f b)) :
    (∑ a ∈ R, (f a ∩ bad).card) ≤ bad.card := by
  have hdisj : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (f a ∩ bad) (f b ∩ bad) := by
    intro a ha b hb hab
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hd a ha b hb hab)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (by
    intro x hx
    obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxa).2)

lemma concrete_forest_bad_partition {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) (bad R : Finset ℕ) (trees : ℕ → BTree)
    (hgood : ∀ r ∈ R, GoodTree n C (trees r))
    (hdisj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (trees r).privs (trees s).privs) :
    ∃ L : List BTree,
      L.length ≤ 2 * ((∑ r ∈ R, (trees r).marks) + bad.card) + R.card ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs =
        (R.biUnion fun r => (trees r).privs) \ bad := by
  classical
  have hex (r : ℕ) : ∃ L : List BTree, r ∈ R →
      L.length ≤ 2 * ((trees r).marks + ((trees r).privs ∩ bad).card) + 1 ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty ∧
        p.privs ⊆ (trees r).privs \ bad) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      L.toFinset.biUnion BTree.privs = (trees r).privs \ bad := by
    by_cases hr : r ∈ R
    · obtain ⟨L, hL⟩ := concrete_tree_bad_partition hback hout bad (hgood r hr)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨[], fun h => False.elim (hr h)⟩
  choose parts hparts using hex
  have hc := concrete_flatmap_collect R.toList parts (fun r => (trees r).privs \ bad)
    R.nodup_toList
    (fun a ha b hb hab => Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
      (hdisj a (Finset.mem_toList.mp ha) b (Finset.mem_toList.mp hb) hab))
    (fun a ha p hp => ((hparts a (Finset.mem_toList.mp ha)).2.1 p hp).2.2.2)
    (fun a ha => (hparts a (Finset.mem_toList.mp ha)).2.2.1)
    (fun a ha => (hparts a (Finset.mem_toList.mp ha)).2.2.2)
  refine ⟨R.toList.flatMap parts, ?_, ?_, hc.1, ?_⟩
  · rw [hc.2.2, Finset.toList_toFinset]
    have hsum := Finset.sum_le_sum (fun r hr => (hparts r hr).1)
    have hbad := concrete_forest_inter_sum_le R (fun r => (trees r).privs) bad hdisj
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul, mul_one] at hsum
    omega
  · intro p hp
    obtain ⟨r, hr, hpr⟩ := List.mem_flatMap.mp hp
    obtain ⟨hg, hm, hne, _⟩ := (hparts r (Finset.mem_toList.mp hr)).2.1 p hpr
    exact ⟨hg, hm, hne⟩
  · rw [hc.2.1, Finset.toList_toFinset]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    aesop

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def BTree.Subtree (t u : BTree) : Prop :=
  t = u ∨ match t with
    | .node _ l r => l.Subtree u ∨ r.Subtree u
    | _ => False

lemma BTree.Subtree.refl (t : BTree) : t.Subtree t := by
  cases t <;> exact Or.inl rfl

lemma BTree.Subtree.left (j : ℕ) (l r : BTree) :
    (BTree.node j l r).Subtree l := Or.inr (Or.inl (BTree.Subtree.refl l))

lemma BTree.Subtree.right (j : ℕ) (l r : BTree) :
    (BTree.node j l r).Subtree r := Or.inr (Or.inr (BTree.Subtree.refl r))

lemma BTree.Subtree.trans {t u v : BTree} (htu : t.Subtree u) (huv : u.Subtree v) :
    t.Subtree v := by
  induction t with
  | priv w =>
    rcases htu with h | h
    · simpa only [h] using huv
    · exact False.elim h
  | mark w =>
    rcases htu with h | h
    · simpa only [h] using huv
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases htu with h | h | h
    · simpa only [h] using huv
    · exact Or.inr (Or.inl (ihl h))
    · exact Or.inr (Or.inr (ihr h))

lemma BTree.Subtree.good {n : ℕ} {C : Circuit} {t u : BTree}
    (h : t.Subtree u) (ht : GoodTree n C t) : GoodTree n C u := by
  induction t with
  | priv w =>
    rcases h with h | h
    · simpa only [← h] using ht
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · simpa only [← h] using ht
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · simpa only [← h] using ht
    · exact ihl h ht.2.2.2.1
    · exact ihr h ht.2.2.2.2.1

lemma BTree.Subtree.marks_le {t u : BTree} (h : t.Subtree u) :
    u.marks ≤ t.marks := by
  induction t with
  | priv w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · subst u; exact le_rfl
    · exact (ihl h).trans (Nat.le_add_right _ _)
    · exact (ihr h).trans (Nat.le_add_left _ _)

lemma BTree.Subtree.privs_subset {t u : BTree} (h : t.Subtree u) :
    u.privs ⊆ t.privs := by
  induction t with
  | priv w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · subst u; exact le_rfl
    · exact (ihl h).trans Finset.subset_union_left
    · exact (ihr h).trans Finset.subset_union_right

def BTree.bankCount (P : ℕ → Prop) [DecidablePred P] (t : BTree) : ℕ :=
  (t.privs.filter P).card

lemma BTree.bankCount_node_le (P : ℕ → Prop) [DecidablePred P]
    (j : ℕ) (l r : BTree) :
    (BTree.node j l r).bankCount P ≤ l.bankCount P + r.bankCount P := by
  unfold bankCount
  rw [BTree.privs, Finset.filter_union]
  exact Finset.card_union_le _ _

lemma BTree.small_violating_subtree (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (t : BTree)
    (hlarge : 2 < t.bankCount P ∨ 2 < t.bankCount Q) :
    ∃ u : BTree, t.Subtree u ∧
      (2 < u.bankCount P ∨ 2 < u.bankCount Q) ∧
      u.bankCount P ≤ 4 ∧ u.bankCount Q ≤ 4 := by
  induction t with
  | priv w =>
    have hp : (BTree.priv w).bankCount P ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp [BTree.privs])
    have hq : (BTree.priv w).bankCount Q ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp [BTree.privs])
    omega
  | mark w =>
    simp [BTree.bankCount, BTree.privs] at hlarge
  | node j l r ihl ihr =>
    by_cases hl : 2 < l.bankCount P ∨ 2 < l.bankCount Q
    · obtain ⟨u, hu, hlarge, hp, hq⟩ := ihl hl
      exact ⟨u, (BTree.Subtree.left j l r).trans hu, hlarge, hp, hq⟩
    by_cases hr : 2 < r.bankCount P ∨ 2 < r.bankCount Q
    · obtain ⟨u, hu, hlarge, hp, hq⟩ := ihr hr
      exact ⟨u, (BTree.Subtree.right j l r).trans hu, hlarge, hp, hq⟩
    refine ⟨BTree.node j l r, BTree.Subtree.refl _, hlarge, ?_, ?_⟩
    · have h := BTree.bankCount_node_le P j l r
      omega
    · have h := BTree.bankCount_node_le Q j l r
      omega

lemma BTree.good_small_violating_subtree {n : ℕ} {C : Circuit}
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (t : BTree) (ht : GoodTree n C t)
    (hmarks : t.marks ≤ 1)
    (hlarge : 2 < t.bankCount P ∨ 2 < t.bankCount Q) :
    ∃ u : BTree, GoodTree n C u ∧ u.marks ≤ 1 ∧ u.privs ⊆ t.privs ∧
      (2 < u.bankCount P ∨ 2 < u.bankCount Q) ∧
      u.bankCount P ≤ 4 ∧ u.bankCount Q ≤ 4 := by
  obtain ⟨u, hu, hlarge, hp, hq⟩ := small_violating_subtree P Q t hlarge
  exact ⟨u, hu.good ht, hu.marks_le.trans hmarks, hu.privs_subset, hlarge, hp, hq⟩

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

lemma one_mark_good_isTree {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) (hm : t.marks ≤ 1)
    (hnp : t.privs.Nonempty) :
    ∃ E : Finset ℕ, E.card ≤ 1 ∧ IsTree n C t.privs E := by
  by_cases hzero : t.marks = 0
  · exact ⟨∅, by simp, good_markFree_isTree hback hout ht hzero⟩
  obtain ⟨reg, priv, b, rest, hs, hlen, hrest, hpw, hcov⟩ :=
    decomp_marked hback hout ht (by omega)
  cases rest with
  | nil =>
    simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.union_empty] at hcov
    subst priv
    exact ⟨{b}, by simp, isTree_of_topStretch hback ht hs hnp⟩
  | cons s rest =>
    simp only [List.length_cons] at hlen
    omega

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset


lemma binary_concrete_bad_partition (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ReadsBack n (binarySkeleton C))
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size →
      0 < readsOf (binarySkeleton C) (n + j))
    (bad : Finset ℕ) :
    let reads := readsOf (binarySkeleton C)
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := (Finset.range C.size).filter (fun j => 2 ≤ reads (n + j))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ L : List BTree,
      L.length ≤ 2 * (markedReads + bad.card) + sharedGates.card + 1 ∧
      (∀ p ∈ L, GoodTree n (binarySkeleton C) p ∧ p.marks ≤ 1 ∧
        p.privs.Nonempty ∧ p.privs ⊆ once \ bad ∧
        ∃ E : Finset ℕ, E.card ≤ 1 ∧ IsTree n (binarySkeleton C) p.privs E) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs = once \ bad := by
  classical
  intro reads shared sharedGates markedReads once
  obtain ⟨R, trees, hR, hgood, hdisj, hcov, hmarks⟩ :=
    binarySkeleton_forest n C hback hsz hout hused
  have hout' : (binarySkeleton C).output + 1 = n + (binarySkeleton C).size := by
    rw [binarySkeleton_size]
    exact hout
  obtain ⟨L, hL, hpieces, hpw, hcover⟩ :=
    concrete_forest_bad_partition hback hout' bad R trees hgood hdisj
  rw [hcov] at hcover
  have hsubset : ∀ p ∈ L, p.privs ⊆ once \ bad := by
    intro p hp w hw
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp, hw⟩
  refine ⟨L, ?_, ?_, hpw, hcover⟩
  · change R.card ≤ sharedGates.card + 1 at hR
    change (∑ r ∈ R, (trees r).marks) ≤ markedReads at hmarks
    omega
  · intro p hp
    obtain ⟨hg, hm, hn⟩ := hpieces p hp
    exact ⟨hg, hm, hn, hsubset p hp, one_mark_good_isTree hback hout' hg hm hn⟩

end PEqualNP.Outside.L_meta_25806_aux


namespace PEqualNP.Outside.L_meta_25806_aux.Table

def errors {n m : ℕ} (F A : Fin n → Fin m → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin m)).filter
    (fun z => A z.1 z.2 ≠ F z.1 z.2)).card

def rowErrors {n m : ℕ} (F A : Fin n → Fin m → Bool) (r : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun c => A r c ≠ F r c)).card

def colErrors {n m : ℕ} (F A : Fin n → Fin m → Bool) (c : Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun r => A r c ≠ F r c)).card

lemma sum_rowErrors {n m : ℕ} (F A : Fin n → Fin m → Bool) :
    ∑ r, rowErrors F A r = errors F A := by
  simp only [rowErrors, errors, Finset.card_filter]
  rw [Fintype.sum_prod_type]

lemma sum_colErrors {n m : ℕ} (F A : Fin n → Fin m → Bool) :
    ∑ c, colErrors F A c = errors F A := by
  simp only [colErrors, errors, Finset.card_filter]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

def badRows {n : ℕ} (F A : Fin n → Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun r => n < 16 * rowErrors F A r)

def badCols {n : ℕ} (F A : Fin n → Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun c => n < 16 * colErrors F A c)

lemma bad_rows_budget {n : ℕ} (F A : Fin n → Fin n → Bool) :
    n * (badRows F A).card ≤ 16 * errors F A := by
  have local_bound : ∑ r ∈ badRows F A, n ≤
      ∑ r ∈ badRows F A, 16 * rowErrors F A r := by
    apply Finset.sum_le_sum
    intro r hr
    exact Nat.le_of_lt (Finset.mem_filter.mp hr).2
  have total_bound : (∑ r ∈ badRows F A, rowErrors F A r) ≤
      ∑ r, rowErrors F A r :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [sum_rowErrors] at total_bound
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at local_bound
  nlinarith

lemma bad_cols_budget {n : ℕ} (F A : Fin n → Fin n → Bool) :
    n * (badCols F A).card ≤ 16 * errors F A := by
  have local_bound : ∑ c ∈ badCols F A, n ≤
      ∑ c ∈ badCols F A, 16 * colErrors F A c := by
    apply Finset.sum_le_sum
    intro c hc
    exact Nat.le_of_lt (Finset.mem_filter.mp hc).2
  have total_bound : (∑ c ∈ badCols F A, colErrors F A c) ≤
      ∑ c, colErrors F A c :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [sum_colErrors] at total_bound
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at local_bound
  nlinarith

lemma bad_names_budget {n : ℕ} (F A : Fin n → Fin n → Bool) :
    n * ((badRows F A).card + (badCols F A).card) ≤ 32 * errors F A := by
  have hr := bad_rows_budget F A
  have hc := bad_cols_budget F A
  nlinarith

lemma good_row_error {n : ℕ} (F A : Fin n → Fin n → Bool) (r : Fin n)
    (h : r ∉ badRows F A) : 16 * rowErrors F A r ≤ n := by
  simp only [badRows, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
  exact h

lemma good_col_error {n : ℕ} (F A : Fin n → Fin n → Bool) (c : Fin n)
    (h : c ∉ badCols F A) : 16 * colErrors F A c ≤ n := by
  simp only [badCols, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
  exact h

def badNames {n : ℕ} (F A : Fin n → Fin n → Bool) : Finset ℕ :=
  (badRows F A).image Fin.val ∪ (badCols F A).image (fun c => n + c.val)

lemma banks_disjoint {n m : ℕ} (R : Finset (Fin n)) (K : Finset (Fin m)) :
    Disjoint (R.image Fin.val) (K.image (fun c => n + c.val)) := by
  apply Finset.disjoint_left.mpr
  intro w hw hk
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hw
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hk
  have hlt := r.isLt
  omega

lemma badNames_card {n : ℕ} (F A : Fin n → Fin n → Bool) :
    (badNames F A).card = (badRows F A).card + (badCols F A).card := by
  rw [badNames, Finset.card_union_of_disjoint (banks_disjoint _ _)]
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

lemma badNames_budget {n : ℕ} (F A : Fin n → Fin n → Bool) :
    n * (badNames F A).card ≤ 32 * errors F A := by
  rw [badNames_card]
  exact bad_names_budget F A

lemma row_good_of_not_badName {n : ℕ} (F A : Fin n → Fin n → Bool) (r : Fin n)
    (h : r.val ∉ badNames F A) : 16 * rowErrors F A r ≤ n := by
  apply good_row_error F A r
  intro hr
  exact h (Finset.mem_union_left _ (Finset.mem_image_of_mem Fin.val hr))

lemma col_good_of_not_badName {n : ℕ} (F A : Fin n → Fin n → Bool) (c : Fin n)
    (h : n + c.val ∉ badNames F A) : 16 * colErrors F A c ≤ n := by
  apply good_col_error F A c
  intro hc
  exact h (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun c => n + c.val) hc))

lemma partition_count_arithmetic (excess sharedNames sharedGates marks pieces good pairs bad used : ℕ)
    (sharing : sharedNames + sharedGates ≤ excess)
    (marked : marks ≤ bad + excess + sharedNames + sharedGates)
    (piece_bound : pieces ≤ 2 * marks + sharedGates + 1)
    (leaves : good ≤ 2 * pieces + pairs)
    (cover : used ≤ good + sharedNames + bad) :
    used ≤ 10 * excess + 5 * bad + 2 + pairs := by
  omega

end PEqualNP.Outside.L_meta_25806_aux.Table


namespace PEqualNP.Outside.L_meta_25806_aux.Selection

lemma choose_disjoint_pairs {ι α : Type*} [DecidableEq α]
    (S : ι → Finset α) (hs : ∀ i, (S i).card = 2)
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ a b : ι → α, Function.Injective a ∧ Function.Injective b ∧
      (∀ i j, a i ≠ b j) ∧ ∀ i, a i ∈ S i ∧ b i ∈ S i ∧ a i ≠ b i := by
  classical
  have ex : ∀ i, ∃ a b, a ≠ b ∧ S i = {a, b} := fun i =>
    Finset.card_eq_two.mp (hs i)
  choose a b hab hS using ex
  have ha (i : ι) : a i ∈ S i := by rw [hS]; simp
  have hb (i : ι) : b i ∈ S i := by rw [hS]; simp
  have cross (i j : ι) (hij : i ≠ j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j) : False :=
    Finset.disjoint_left.mp (hd i j hij) hxi hxj
  refine ⟨a, b, ?_, ?_, ?_, fun i => ⟨ha i, hb i, hab i⟩⟩
  · intro i j he
    by_contra hij
    exact cross i j hij (a i) (ha i) (he ▸ ha j)
  · intro i j he
    by_contra hij
    exact cross i j hij (b i) (hb i) (he ▸ hb j)
  · intro i j he
    by_cases hij : i = j
    · subst j
      exact hab i he
    · exact cross i j hij (a i) (ha i) (he ▸ hb j)

lemma two_bank_piece_count {ι : Type*} [Fintype ι]
    (r c : ι → ℕ) (hr : ∀ i, r i ≤ 2) (hc : ∀ i, c i ≤ 2) :
    (∑ i, (r i + c i)) ≤ 2 * Fintype.card ι +
      Fintype.card {i // r i = 2} + Fintype.card {i // c i = 2} := by
  classical
  have each (i : ι) : r i + c i ≤ 2 +
      (if r i = 2 then 1 else 0) + (if c i = 2 then 1 else 0) := by
    have hri := hr i
    have hci := hc i
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => each i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  simp only [Fintype.card_subtype, Finset.card_filter]
  simpa only [Nat.mul_comm (Fintype.card ι) 2, Finset.sum_add_distrib] using hsum

def rows {n : ℕ} (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => u.val ∈ S)

def cols {n : ℕ} (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => n + v.val ∈ S)

lemma rows_disjoint {n : ℕ} {S T : Finset ℕ} (h : Disjoint S T) :
    Disjoint (rows (n := n) S) (rows T) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2

lemma cols_disjoint {n : ℕ} {S T : Finset ℕ} (h : Disjoint S T) :
    Disjoint (cols (n := n) S) (cols T) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2

lemma raw_parts {n : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range (n + n)) :
    S.card = (rows (n := n) S).card + (cols (n := n) S).card := by
  have split : S = S.filter (fun w => w < n) ∪ S.filter (fun w => n ≤ w) := by
    ext w
    by_cases hw : w ∈ S
    · simp only [Finset.mem_union, Finset.mem_filter, hw, true_and, true_iff]
      omega
    · simp [hw]
  have disj : Disjoint (S.filter (fun w => w < n)) (S.filter (fun w => n ≤ w)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hv
    have h1 := (Finset.mem_filter.mp hw).2
    have h2 := (Finset.mem_filter.mp hv).2
    omega
  have row_eq : (rows (n := n) S).image Fin.val = S.filter (fun w => w < n) := by
    ext w
    simp only [Finset.mem_image, rows, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.isLt⟩
    · rintro ⟨hw, hn⟩
      exact ⟨⟨w, hn⟩, hw, rfl⟩
  have col_eq : (cols (n := n) S).image (fun v => n + v.val) =
      S.filter (fun w => n ≤ w) := by
    ext w
    simp only [Finset.mem_image, cols, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, by omega⟩
    · rintro ⟨hw, hn⟩
      have hwlt := Finset.mem_range.mp (hS hw)
      let v : Fin n := ⟨w - n, by omega⟩
      have hv : n + v.val = w := by dsimp [v]; omega
      exact ⟨v, by simpa only [hv] using hw, hv⟩
  calc
    S.card = (S.filter (fun w => w < n)).card + (S.filter (fun w => n ≤ w)).card := by
      conv_lhs => rw [split]
      exact Finset.card_union_of_disjoint disj
    _ = _ := by
      rw [← row_eq, ← col_eq, Finset.card_image_of_injective _ Fin.val_injective,
        Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

end PEqualNP.Outside.L_meta_25806_aux.Selection


namespace PEqualNP.Outside.L_meta_25806

open Finset

lemma incidence_budget {α : Type*} [DecidableEq α]
    (W I B : Finset α) (r : α) (R : α → α → Prop) [DecidableRel R]
    (hI : I ⊆ W) (hr : r ∈ W)
    (hlive : ∀ a ∈ W, a ≠ r → ∃ b ∈ W, R a b)
    (hin : ∀ b ∈ W, (W.filter (fun a => R a b)).card ≤
      (if b ∈ I then 0 else 1) + (if b ∈ B then 1 else 0)) :
    I.card + ∑ a ∈ W, ((W.filter (R a)).card - 1) ≤ B.card + 1 := by
  have lower : (W.erase r).card + ∑ a ∈ W, ((W.filter (R a)).card - 1) ≤
      ∑ a ∈ W, (W.filter (R a)).card := by
    have herase : (W.erase r).card = ∑ a ∈ W, (if a = r then 0 else 1 : ℕ) := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add,
        Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext a
      simp only [Finset.mem_erase, Finset.mem_filter]
      tauto
    rw [herase, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    by_cases he : a = r
    · simp [he]
    · obtain ⟨b, hb, hab⟩ := hlive a ha he
      have hp : 0 < (W.filter (R a)).card :=
        Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩⟩
      simp only [he, ite_false]
      omega
  have swap : (∑ a ∈ W, (W.filter (R a)).card) =
      ∑ b ∈ W, (W.filter (fun a => R a b)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have upper : (∑ b ∈ W, (W.filter (fun a => R a b)).card) ≤
      (W \ I).card + B.card := by
    calc
      _ ≤ ∑ b ∈ W, ((if b ∈ I then 0 else 1) + (if b ∈ B then 1 else 0)) :=
        Finset.sum_le_sum hin
      _ = (W \ I).card + (W ∩ B).card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]
        congr 1; congr 1; ext a; simp
      _ ≤ _ := Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
  have hsplit := Finset.card_sdiff_add_card_eq_card hI
  have hroot := Finset.card_erase_add_one hr
  rw [swap] at lower
  omega

lemma shared_count_le_excess {α : Type*} [DecidableEq α]
    (W : Finset α) (d : α → ℕ) :
    (W.filter fun a => 2 ≤ d a).card ≤ ∑ a ∈ W, (d a - 1) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a ha
  split_ifs <;> omega

lemma normalized_budget (N s : ℕ) (v : ℕ → ℕ) (hs : 0 < s)
    (hlive : ∀ j < s, v (N+j) = 0 ↔ j+1 = s)
    (htotal : ∑ i ∈ Finset.range (N+s), v i = 2*s) :
    ((Finset.range N).filter (fun i => 1 ≤ v i)).card +
      ∑ i ∈ Finset.range (N+s), (v i - 1) = s+1 := by
  have split (t : Finset ℕ) :
      (∑ i ∈ t, v i) = (t.filter (fun i => 1 ≤ v i)).card +
        ∑ i ∈ t, (v i - 1) := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> omega
  have gates : ((Finset.range (N+s)).filter (fun i => 1 ≤ v i)).card =
      ((Finset.range N).filter (fun i => 1 ≤ v i)).card + (s-1) := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
    congr 1
    have hh : (∑ i ∈ Finset.range s, (if 1 ≤ v (N+i) then 1 else 0 : ℕ)) =
        ∑ i ∈ Finset.range s, (if i = s-1 then 0 else 1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hz := hlive i (Finset.mem_range.mp hi)
      split_ifs <;> omega
    rw [hh]
    simp [Finset.sum_ite, Finset.filter_ne', show s-1 ∈ Finset.range s by simp; omega]
  have h := split (Finset.range (N+s))
  rw [htotal, gates] at h
  omega

lemma binary_fanout_total (N s : ℕ) (left right : ℕ → ℕ)
    (hleft : ∀ j < s, left j < N+j)
    (hright : ∀ j < s, right j < N+j) :
    (∑ w ∈ Finset.range (N+s), ∑ j ∈ Finset.range s,
      ((if w = left j then 1 else 0) + (if w = right j then 1 else 0) : ℕ)) = 2*s := by
  rw [Finset.sum_comm]
  have step (j : ℕ) (hj : j ∈ Finset.range s) :
      (∑ w ∈ Finset.range (N+s),
        ((if w = left j then 1 else 0) + (if w = right j then 1 else 0) : ℕ)) = 2 := by
    have hjlt := Finset.mem_range.mp hj
    have h1 : left j < N+s := (hleft j hjlt).trans_le (by omega)
    have h2 : right j < N+s := (hright j hjlt).trans_le (by omega)
    simp [Finset.sum_add_distrib, h1, h2]
  calc
    _ = ∑ _j ∈ Finset.range s, 2 := Finset.sum_congr rfl step
    _ = _ := by simp [Nat.mul_comm]

lemma marked_reads_budget {α : Type*} [DecidableEq α]
    (W M : Finset α) (d : α → ℕ) (hM : M ⊆ W)
    (hpos : ∀ a ∈ M, 1 ≤ d a) :
    (∑ a ∈ M, d a) ≤ (∑ a ∈ W, (d a - 1)) + M.card := by
  have he : (∑ a ∈ M, d a) = (∑ a ∈ M, (d a - 1)) + M.card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have := hpos a ha
    omega
  rw [he]
  exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset hM) _

lemma charging_arithmetic (n b q d bad pairs e : ℕ)
    (support : 2*n^2 ≤ n*q + 2*n + 8*e)
    (budget : q+d ≤ b+1)
    (partition : q ≤ 10*d+5*bad+2+pairs)
    (bad_budget : n*bad ≤ 32*e)
    (pair_budget : n*pairs ≤ 6*n+20*e) :
    11*n^2 ≤ (5*b+20)*n+134*e := by
  have hp := Nat.mul_le_mul_left n partition
  have hb := Nat.mul_le_mul_left n budget
  nlinarith

end PEqualNP.Outside.L_meta_25806


namespace PEqualNP.Outside.L_meta_25806_aux.BinarySupport

open PEqualNP.MetaComplexity

def run (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op ((run gs x).getD g.left false) ((run gs x).getD g.right false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List BinaryGate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma run_input (gs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega), ih]

lemma run_congr (N : ℕ) (gs : List BinaryGate) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N)
    (agree : ∀ g ∈ gs, ∀ i, (i = g.left ∨ i = g.right) → i < N →
      x.getD i false = y.getD i false) :
    ∀ i, N ≤ i → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [run, List.foldl_nil]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    have ih' := ih (fun a ha => agree a (List.mem_append_left _ ha))
    have operands (i : ℕ) (hi : i = g.left ∨ i = g.right) :
        (run gs x).getD i false = (run gs y).getD i false := by
      by_cases hN : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
        exact agree g (by simp) i hi hN
      · exact ih' i (by omega)
    intro i hi
    rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy]
    split_ifs
    · rw [operands g.left (Or.inl rfl), operands g.right (Or.inr rfl)]
    · exact ih' i hi

def gateAt (C : BinaryCircuit) (j : ℕ) : BinaryGate :=
  C.gates.getD j ⟨fun _ _ => false, 0, 0⟩

def reads (C : BinaryCircuit) (w : ℕ) : ℕ :=
  ∑ j ∈ Finset.range C.size,
    ((if w = (gateAt C j).left then 1 else 0) +
      (if w = (gateAt C j).right then 1 else 0))

lemma reads_positive (C : BinaryCircuit) (g : BinaryGate) (hg : g ∈ C.gates)
    (w : ℕ) (hw : w = g.left ∨ w = g.right) : 0 < reads C w := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
  have gat : gateAt C j = g := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, he]
  have hterm : 1 ≤ (if w = (gateAt C j).left then 1 else 0) +
      (if w = (gateAt C j).right then 1 else 0) := by
    rw [gat]
    rcases hw with h | h <;> simp [h]
  have hsingle := Finset.single_le_sum
    (f := fun k => (if w = (gateAt C k).left then 1 else 0) +
      (if w = (gateAt C k).right then 1 else 0))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  exact lt_of_lt_of_le (by omega) hsingle

lemma eval_congr (N : ℕ) (C : BinaryCircuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (ho : N ≤ C.output)
    (agree : ∀ i < N, 0 < reads C i → x.getD i false = y.getD i false) :
    C.eval x = C.eval y := by
  apply run_congr N C.gates x y hx hy ?_ C.output ho
  intro g hg i hi hN
  exact agree i hN (reads_positive C g hg i hi)

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n+m := by
  simp [PEqualNP.Represents.oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n+v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i-n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n+v.val
      · simp [hv]
      · have hv' : ¬ i-n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

lemma unused_rows {n m : ℕ} (C : BinaryCircuit) (ho : n+m ≤ C.output)
    (u v : Fin n) (hu : reads C u.val = 0) (hv : reads C v.val = 0) (z : Fin m) :
    C.eval (PEqualNP.Represents.oneEach u z) =
      C.eval (PEqualNP.Represents.oneEach v z) := by
  apply eval_congr (n+m) C _ _ (oneEach_length _ _) (oneEach_length _ _) ho
  intro i hi hp
  have h1 : i ≠ u.val := by intro h; rw [h, hu] at hp; omega
  have h2 : i ≠ v.val := by intro h; rw [h, hv] at hp; omega
  rw [oneEach_getD, oneEach_getD]
  simp [h1, h2]

lemma unused_columns {n m : ℕ} (C : BinaryCircuit) (ho : n+m ≤ C.output)
    (u v : Fin m) (hu : reads C (n+u.val) = 0) (hv : reads C (n+v.val) = 0) (z : Fin n) :
    C.eval (PEqualNP.Represents.oneEach z u) =
      C.eval (PEqualNP.Represents.oneEach z v) := by
  apply eval_congr (n+m) C _ _ (oneEach_length _ _) (oneEach_length _ _) ho
  intro i hi hp
  have h1 : i ≠ n+u.val := by intro h; rw [h, hu] at hp; omega
  have h2 : i ≠ n+v.val := by intro h; rw [h, hv] at hp; omega
  rw [oneEach_getD, oneEach_getD]
  simp [h1, h2]

end PEqualNP.Outside.L_meta_25806_aux.BinarySupport

namespace PEqualNP.Outside.L_meta_25806_aux.BinarySupport

open PEqualNP.MetaComplexity

lemma reads_total (N : ℕ) (C : BinaryCircuit)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j) :
    (∑ w ∈ Finset.range (N+C.size), reads C w) = 2*C.size := by
  exact PEqualNP.Outside.L_meta_25806.binary_fanout_total N C.size
    (fun j => (gateAt C j).left) (fun j => (gateAt C j).right)
    (fun j hj => (back j hj).1) (fun j hj => (back j hj).2)

lemma reads_last (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j) :
    reads C (N+(C.size-1)) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have hb := back j hjlt
  have hl : N+(C.size-1) ≠ (gateAt C j).left := by omega
  have hr : N+(C.size-1) ≠ (gateAt C j).right := by omega
  simp [hl, hr]

lemma reads_gate_zero_iff (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j)
    (live : ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j)) :
    ∀ j < C.size, reads C (N+j) = 0 ↔ j+1 = C.size := by
  intro j hj
  constructor
  · intro hz
    by_contra h
    have hp := live j hj (by omega)
    omega
  · intro h
    have hjlast : j = C.size-1 := by omega
    rw [hjlast]
    exact reads_last N C hs back

lemma reads_budget (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j)
    (live : ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j)) :
    ((Finset.range N).filter (fun w => 1 ≤ reads C w)).card +
      ∑ w ∈ Finset.range (N+C.size), (reads C w - 1) = C.size+1 := by
  exact PEqualNP.Outside.L_meta_25806.normalized_budget N C.size (reads C) hs
    (reads_gate_zero_iff N C hs back live) (reads_total N C back)

end PEqualNP.Outside.L_meta_25806_aux.BinarySupport

namespace PEqualNP.Outside.L_meta_25806

lemma raw_name_partition (N : ℕ) (d : ℕ → ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    ((Finset.range N).filter (fun w => 1 ≤ d w)).card =
      ((Finset.range N).filter (fun w => d w = 1 ∧ ¬bad w)).card +
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range N).filter (fun w => d w = 1 ∧ bad w)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hb : bad w <;> by_cases h0 : d w = 0 <;> by_cases h1 : d w = 1 <;>
    simp_all <;> split_ifs <;> omega

lemma shared_name_gate_budget (N s : ℕ) (d : ℕ → ℕ) :
    ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card ≤
      ∑ w ∈ Finset.range (N+s), (d w - 1) := by
  have h := shared_count_le_excess (Finset.range (N+s)) d
  simpa only [Finset.card_filter, Finset.sum_range_add] using h

lemma used_le_good_shared_bad (N : ℕ) (d : ℕ → ℕ) (bad : Finset ℕ) :
    ((Finset.range N).filter (fun w => 1 ≤ d w)).card ≤
      ((Finset.range N).filter (fun w => d w = 1 ∧ w ∉ bad)).card +
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card + bad.card := by
  have h := raw_name_partition N d (fun w => w ∈ bad)
  have hc : ((Finset.range N).filter (fun w => d w = 1 ∧ w ∈ bad)).card ≤ bad.card := by
    apply Finset.card_le_card
    intro w hw
    exact (Finset.mem_filter.mp hw).2.2
  omega

lemma shared_marked_reads_budget (N s bad : ℕ) (d : ℕ → ℕ) :
    (∑ w ∈ (Finset.range (N+s)).filter (fun w => 2 ≤ d w), d w) + bad ≤
      (∑ w ∈ Finset.range (N+s), (d w - 1)) +
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card + bad := by
  have h := marked_reads_budget (Finset.range (N+s))
    ((Finset.range (N+s)).filter (fun w => 2 ≤ d w)) d
    (Finset.filter_subset _ _) (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega)
  have split : ((Finset.range (N+s)).filter (fun w => 2 ≤ d w)).card =
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card := by
    simp only [Finset.card_filter, Finset.sum_range_add]
  rw [split] at h
  omega

lemma bad_error_budget {α : Type*} [DecidableEq α]
    (s bad : Finset α) (err : α → ℕ) (n : ℕ) (hb : bad ⊆ s)
    (hcost : ∀ a ∈ bad, n ≤ 16*err a) :
    n*bad.card ≤ 16 * ∑ a ∈ s, err a := by
  calc
    n*bad.card = ∑ _a ∈ bad, n := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ bad, 16*err a := Finset.sum_le_sum hcost
    _ = 16 * ∑ a ∈ bad, err a := by rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left 16 (Finset.sum_le_sum_of_subset hb)

end PEqualNP.Outside.L_meta_25806

namespace PEqualNP.Outside.L_meta_25806_aux.BinarySupport

open PEqualNP.MetaComplexity

lemma normalize_back_reads (N : ℕ) (C : BinaryCircuit)
    (back : PEqualNP.Outside.L_meta_25806_aux.Normalize.Back N C.gates) :
    ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j := by
  intro j hj
  simpa only [gateAt, List.getD_eq_getElem _ _ hj] using back j hj

lemma normalize_live_reads (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (live : PEqualNP.Outside.L_meta_25806_aux.Normalize.Live N C) :
    ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j) := by
  intro j hj hjlast
  have hout := PEqualNP.Outside.L_meta_25806_aux.Normalize.live_output_last N C live hs
  have hne : N+j ≠ C.output := by rw [hout]; change j+1 < C.gates.length at hjlast; omega
  obtain ⟨k, hk, hjk, he⟩ := live j hj hne
  apply reads_positive C C.gates[k] (List.getElem_mem hk) (N+j)
  simpa only [eq_comm] using he

lemma normalized_reads_budget (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : PEqualNP.Outside.L_meta_25806_aux.Normalize.Back N C.gates)
    (live : PEqualNP.Outside.L_meta_25806_aux.Normalize.Live N C) :
    ((Finset.range N).filter (fun w => 1 ≤ reads C w)).card +
      ∑ w ∈ Finset.range (N+C.size), (reads C w - 1) = C.size+1 := by
  exact reads_budget N C hs (normalize_back_reads N C back)
    (normalize_live_reads N C hs live)

end PEqualNP.Outside.L_meta_25806_aux.BinarySupport

namespace PEqualNP.Outside.L_meta_25806_aux.Patterns



open scoped BigOperators

lemma h5_orthogonal_pair_aggregate {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (v : ι → α → ℤ) (m : ι → ℤ)
    (hgram : ∀ i j, (∑ x, v i x * v j x) =
      if i = j then 2 * (Fintype.card α : ℤ) else 0)
    (hmass : ∀ i, (∑ x, v i x) = 4 * m i - (Fintype.card α : ℤ)) :
    (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) ≤
      8 * (∑ i, m i) + 2 * (Fintype.card α : ℤ) := by
  classical
  have hnorm : (∑ x, (∑ i, v i x) ^ 2) =
      2 * (Fintype.card α : ℤ) * (Fintype.card ι : ℤ) := by
    calc
      (∑ x, (∑ i, v i x) ^ 2) = ∑ i, ∑ j, ∑ x, v i x * v j x := by
        simp only [pow_two, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = 2 * (Fintype.card α : ℤ) * (Fintype.card ι : ℤ) := by
        simp [hgram]
        ring
  have htotal : (∑ x, ∑ i, v i x) =
      4 * (∑ i, m i) - (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) := by
    rw [Finset.sum_comm]
    simp [hmass, Finset.sum_sub_distrib, Finset.mul_sum]
  have hsq : 0 ≤ ∑ x, ((∑ i, v i x) + 2) ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hexpand : (∑ x, ((∑ i, v i x) + 2) ^ 2) =
      (∑ x, (∑ i, v i x) ^ 2) + 4 * (∑ x, ∑ i, v i x) +
        4 * (Fintype.card α : ℤ) := by
    calc
      (∑ x, ((∑ i, v i x) + 2) ^ 2) =
          ∑ x, ((∑ i, v i x) ^ 2 + 4 * (∑ i, v i x) + 4) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
        ring
  rw [hexpand, hnorm, htotal] at hsq
  nlinarith

lemma h5_disjoint_pair_aggregate {ι α ρ : Type*} [Fintype ι] [Fintype α] [DecidableEq ρ]
    (h : ρ → α → ℤ) (a b : ι → ρ) (m : ι → ℤ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hgram : ∀ r s, (∑ x, h r x * h s x) =
      if r = s then (Fintype.card α : ℤ) else 0)
    (hmass : ∀ i, (∑ x, (h (a i) x - h (b i) x)) =
      4 * m i - (Fintype.card α : ℤ)) :
    (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) ≤
      8 * (∑ i, m i) + 2 * (Fintype.card α : ℤ) := by
  classical
  apply h5_orthogonal_pair_aggregate (fun i x => h (a i) x - h (b i) x) m
  · intro i j
    have heq : (∑ x, (h (a i) x - h (b i) x) * (h (a j) x - h (b j) x)) =
        (∑ x, h (a i) x * h (a j) x) - (∑ x, h (a i) x * h (b j) x) -
        (∑ x, h (b i) x * h (a j) x) + (∑ x, h (b i) x * h (b j) x) := by
      calc
        _ = ∑ x, (h (a i) x * h (a j) x - h (a i) x * h (b j) x -
            h (b i) x * h (a j) x + h (b i) x * h (b j) x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [heq, hgram, hgram, hgram, hgram]
    by_cases hij : i = j
    · subst j
      simp [hab, Ne.symm (hab i i)]
      ring
    · simp [hij, ha.ne hij, hb.ne hij, hab, Ne.symm (hab j i)]
  · exact hmass

def h5_sign (b : Bool) : ℤ := if b then 1 else -1

lemma h5_sign_inner {α : Type*} [Fintype α] (f g : α → Bool) :
    (∑ x, h5_sign (f x) * h5_sign (g x)) = (Fintype.card α : ℤ) -
      2 * (((Finset.univ : Finset α).filter (fun x => f x ≠ g x)).card : ℤ) := by
  classical
  calc
    _ = ∑ x, (1 - 2 * (if f x ≠ g x then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases f x <;> cases g x <;> norm_num [h5_sign]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma h5_sign_mass {α : Type*} [Fintype α] (f g : α → Bool) :
    (∑ x, (h5_sign (f x) - h5_sign (g x))) =
      4 * (((Finset.univ : Finset α).filter (fun x => f x = true ∧ g x = false)).card : ℤ) -
      2 * (((Finset.univ : Finset α).filter (fun x => f x ≠ g x)).card : ℤ) := by
  classical
  calc
    _ = ∑ x, (4 * (if f x = true ∧ g x = false then (1 : ℤ) else 0) -
        2 * (if f x ≠ g x then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases f x <;> cases g x <;> norm_num [h5_sign]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]

lemma h5_bool_disjoint_pair_bound {ι α ρ : Type*} [Fintype ι] [Fintype α]
    (F : ρ → α → Bool) (a b : ι → ρ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hpair : ∀ r s, r ≠ s →
      2 * ((Finset.univ : Finset α).filter (fun x => F r x ≠ F s x)).card =
        Fintype.card α) :
    Fintype.card ι * Fintype.card α ≤
      8 * (∑ i, ((Finset.univ : Finset α).filter
        (fun x => F (a i) x = true ∧ F (b i) x = false)).card) + 2 * Fintype.card α := by
  classical
  have hgram : ∀ r s, (∑ x, h5_sign (F r x) * h5_sign (F s x)) =
      if r = s then (Fintype.card α : ℤ) else 0 := by
    intro r s
    rw [h5_sign_inner]
    by_cases hrs : r = s
    · subst s
      simp
    · simp only [hrs, ite_false]
      have hc : (2 : ℤ) * (((Finset.univ : Finset α).filter
          (fun x => F r x ≠ F s x)).card : ℤ) = (Fintype.card α : ℤ) := by
        exact_mod_cast hpair r s hrs
      linarith
  have hmass : ∀ i, (∑ x, (h5_sign (F (a i) x) - h5_sign (F (b i) x))) =
      4 * (((Finset.univ : Finset α).filter
        (fun x => F (a i) x = true ∧ F (b i) x = false)).card : ℤ) -
        (Fintype.card α : ℤ) := by
    intro i
    rw [h5_sign_mass]
    have hc : (2 : ℤ) * (((Finset.univ : Finset α).filter
        (fun x => F (a i) x ≠ F (b i) x)).card : ℤ) = (Fintype.card α : ℤ) := by
      exact_mod_cast hpair (a i) (b i) (hab i i)
    rw [hc]
  have hbound := h5_disjoint_pair_aggregate (fun r x => h5_sign (F r x)) a b
    (fun i => (((Finset.univ : Finset α).filter
      (fun x => F (a i) x = true ∧ F (b i) x = false)).card : ℤ)) ha hb hab hgram hmass
  exact_mod_cast hbound


open Finset

namespace HadamardPatterns

lemma xor_false (a b : Bool) : Bool.xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

lemma xor_true (a b : Bool) : Bool.xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

lemma filter_count_split {α : Type*} (s : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (s.filter (fun x => P x ∧ Q x)).card +
      (s.filter (fun x => P x ∧ ¬ Q x)).card = (s.filter P).card := by
  simpa only [Finset.filter_filter] using
    (Finset.card_filter_add_card_filter_not (s := s.filter P) (p := Q))

lemma filter_count_congr {α : Type*} (s : Finset α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x ∈ s, P x ↔ Q x) :
    (s.filter P).card = (s.filter Q).card := by
  congr 1
  apply Finset.filter_congr
  exact h

lemma triple_patterns {α : Type*} (s : Finset α) (f g h : α → Bool)
    (hfg : 2 * (s.filter (fun x => f x ≠ g x)).card = s.card)
    (hfh : 2 * (s.filter (fun x => f x ≠ h x)).card = s.card)
    (hgh : 2 * (s.filter (fun x => g x ≠ h x)).card = s.card)
    (p q : Bool) :
    4 * (s.filter (fun x => Bool.xor (f x) (g x) = p ∧
      Bool.xor (f x) (h x) = q)).card = s.card := by
  classical
  let a := (s.filter (fun x => f x = g x ∧ f x = h x)).card
  let b := (s.filter (fun x => f x = g x ∧ f x ≠ h x)).card
  let c := (s.filter (fun x => f x ≠ g x ∧ f x = h x)).card
  let d := (s.filter (fun x => f x ≠ g x ∧ f x ≠ h x)).card
  have hab : a + b = (s.filter (fun x => f x = g x)).card :=
    filter_count_split s (fun x => f x = g x) (fun x => f x = h x)
  have hcd : c + d = (s.filter (fun x => f x ≠ g x)).card :=
    filter_count_split s (fun x => f x ≠ g x) (fun x => f x = h x)
  have hall : a + b + (c + d) = s.card := by
    rw [hab, hcd]
    exact Finset.card_filter_add_card_filter_not (fun x => f x = g x)
  have hbd : b + d = (s.filter (fun x => f x ≠ h x)).card := by
    have hs := filter_count_split s (fun x => f x ≠ h x) (fun x => f x = g x)
    simpa only [and_comm] using hs
  have hbc : b + c = (s.filter (fun x => g x ≠ h x)).card := by
    have hs := filter_count_split s (fun x => g x ≠ h x) (fun x => f x = g x)
    have hb : (s.filter (fun x => g x ≠ h x ∧ f x = g x)).card = b := by
      apply filter_count_congr
      intro x hx
      cases f x <;> cases g x <;> cases h x <;> decide
    have hc : (s.filter (fun x => g x ≠ h x ∧ f x ≠ g x)).card = c := by
      apply filter_count_congr
      intro x hx
      cases f x <;> cases g x <;> cases h x <;> decide
    rwa [hb, hc] at hs
  have ha : 4*a = s.card := by omega
  have hb : 4*b = s.card := by omega
  have hc : 4*c = s.card := by omega
  have hd : 4*d = s.card := by omega
  cases p <;> cases q
  · simpa [a, xor_false] using ha
  · simpa [b, xor_false, xor_true] using hb
  · simpa [c, xor_false, xor_true] using hc
  · simpa [d, xor_true] using hd

lemma card_union_four_le {α : Type*} [DecidableEq α]
    (a b c d : Finset α) :
    (a ∪ b ∪ c ∪ d).card ≤ a.card + b.card + c.card + d.card := by
  have h1 := Finset.card_union_le a b
  have h2 := Finset.card_union_le (a ∪ b) c
  have h3 := Finset.card_union_le (a ∪ b ∪ c) d
  omega

lemma triple_missing_error_bound {α : Type*} (s t : Finset α)
    (f g h f' g' h' : α → Bool)
    (hfg : 2 * (s.filter (fun x => f x ≠ g x)).card = s.card)
    (hfh : 2 * (s.filter (fun x => f x ≠ h x)).card = s.card)
    (hgh : 2 * (s.filter (fun x => g x ≠ h x)).card = s.card)
    (p q : Bool)
    (hmissing : ∀ x ∈ s, x ∉ t →
      ¬ (Bool.xor (f' x) (g' x) = p ∧ Bool.xor (f' x) (h' x) = q)) :
    s.card ≤ 4 * ((s.filter (fun x => f x ≠ f' x)).card +
      (s.filter (fun x => g x ≠ g' x)).card +
      (s.filter (fun x => h x ≠ h' x)).card + t.card) := by
  classical
  have hcount := triple_patterns s f g h hfg hfh hgh p q
  have hsub : s.filter (fun x => Bool.xor (f x) (g x) = p ∧
      Bool.xor (f x) (h x) = q) ⊆
      s.filter (fun x => f x ≠ f' x) ∪ s.filter (fun x => g x ≠ g' x) ∪
        s.filter (fun x => h x ≠ h' x) ∪ t := by
    intro x hx
    have hxs := (Finset.mem_filter.mp hx).1
    have hpat := (Finset.mem_filter.mp hx).2
    by_cases ht : x ∈ t
    · simp [ht]
    by_cases hf : f x = f' x
    · by_cases hg : g x = g' x
      · by_cases hh : h x = h' x
        · exact False.elim ((hmissing x hxs ht) (by simpa [hf, hg, hh] using hpat))
        · simp [hxs, hh]
      · simp [hxs, hg]
    · simp [hxs, hf]
  have hcard := Finset.card_le_card hsub
  have hu := card_union_four_le (s.filter (fun x => f x ≠ f' x))
    (s.filter (fun x => g x ≠ g' x)) (s.filter (fun x => h x ≠ h' x)) t
  omega

lemma triple_good_pattern_exists {α : Type*} (s t : Finset α)
    (f g h f' g' h' : α → Bool)
    (hfg : 2 * (s.filter (fun x => f x ≠ g x)).card = s.card)
    (hfh : 2 * (s.filter (fun x => f x ≠ h x)).card = s.card)
    (hgh : 2 * (s.filter (fun x => g x ≠ h x)).card = s.card)
    (herr : 4 * ((s.filter (fun x => f x ≠ f' x)).card +
      (s.filter (fun x => g x ≠ g' x)).card +
      (s.filter (fun x => h x ≠ h' x)).card + t.card) < s.card)
    (p q : Bool) :
    ∃ x ∈ s, x ∉ t ∧ Bool.xor (f' x) (g' x) = p ∧
      Bool.xor (f' x) (h' x) = q := by
  classical
  by_contra hn
  have hm : ∀ x ∈ s, x ∉ t →
      ¬ (Bool.xor (f' x) (g' x) = p ∧ Bool.xor (f' x) (h' x) = q) := by
    intro x hx ht hp
    exact hn ⟨x, hx, ht, hp⟩
  have he := triple_missing_error_bound s t f g h f' g' h' hfg hfh hgh p q hm
  omega

end HadamardPatterns


namespace HadamardTransform

lemma xor_ne_common (a b c d : Bool) :
    (Bool.xor (Bool.xor a c) d ≠ Bool.xor (Bool.xor b c) d) ↔ a ≠ b := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma xor_ne_different (a b c d e : Bool) (hde : d ≠ e) :
    (Bool.xor (Bool.xor a c) d ≠ Bool.xor (Bool.xor b c) e) ↔ a = b := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

lemma half_pair_twist {α ρ : Type*} (s : Finset α)
    (F : ρ → α → Bool) (R : ρ → Bool) (H : α → Bool)
    (hpair : ∀ r t, r ≠ t →
      2 * (s.filter (fun x => F r x ≠ F t x)).card = s.card) :
    ∀ r t, r ≠ t →
      2 * (s.filter (fun x =>
        Bool.xor (Bool.xor (F r x) (H x)) (R r) ≠
        Bool.xor (Bool.xor (F t x) (H x)) (R t))).card = s.card := by
  classical
  intro r t hrt
  by_cases hm : R r = R t
  · simpa only [hm, xor_ne_common] using hpair r t hrt
  · simp only [xor_ne_different _ _ _ _ _ hm]
    have ht := Finset.card_filter_add_card_filter_not (s := s) (fun x => F r x = F t x)
    have hp := hpair r t hrt
    simp only [ne_eq] at *
    omega

lemma twist_errors {α : Type*} (s : Finset α) (f g H : α → Bool) (R : Bool) :
    (s.filter (fun x => Bool.xor (Bool.xor (f x) (H x)) R ≠
      Bool.xor (Bool.xor (g x) (H x)) R)).card =
        (s.filter (fun x => f x ≠ g x)).card := by
  simp only [xor_ne_common]

lemma twist_pattern (a b H p q : Bool) :
    (Bool.xor (Bool.xor a H) (!p) = true ∧
      Bool.xor (Bool.xor b H) q = false) ↔
    (Bool.xor a H = p ∧ Bool.xor b H = q) := by
  cases a <;> cases b <;> cases H <;> cases p <;> cases q <;> decide

end HadamardTransform

namespace HadamardPatterns

lemma arbitrary_disjoint_pair_bound {ι α ρ : Type*} [Fintype ι] [Fintype α]
    (F : ρ → α → Bool) (a b : ι → ρ) (H : α → Bool) (p q : ι → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hpair : ∀ r s, r ≠ s →
      2 * ((Finset.univ : Finset α).filter (fun x => F r x ≠ F s x)).card =
        Fintype.card α) :
    Fintype.card ι * Fintype.card α ≤
      8 * (∑ i, ((Finset.univ : Finset α).filter
        (fun x => Bool.xor (F (a i) x) (H x) = p i ∧
          Bool.xor (F (b i) x) (H x) = q i)).card) + 2 * Fintype.card α := by
  classical
  let sel : Sum ι ι → ρ := Sum.elim a b
  have hsel : Function.Injective sel := by
    intro r s hrs
    cases r with
    | inl i =>
      cases s with
      | inl j =>
        change a i = a j at hrs
        exact congrArg Sum.inl (ha hrs)
      | inr j =>
        change a i = b j at hrs
        exact False.elim (hab i j hrs)
    | inr i =>
      cases s with
      | inl j =>
        change b i = a j at hrs
        exact False.elim (hab j i hrs.symm)
      | inr j =>
        change b i = b j at hrs
        exact congrArg Sum.inr (hb hrs)
  let R : Sum ι ι → Bool := Sum.elim (fun i => !p i) q
  let FT : Sum ι ι → α → Bool :=
    fun r x => Bool.xor (Bool.xor (F (sel r) x) (H x)) (R r)
  have hhalf : ∀ r s : Sum ι ι, r ≠ s →
      2 * ((Finset.univ : Finset α).filter (fun x => FT r x ≠ FT s x)).card =
        Fintype.card α := by
    simpa only [Finset.card_univ] using
      HadamardTransform.half_pair_twist (Finset.univ : Finset α)
        (fun r => F (sel r)) R H (fun r s hrs => by
          simpa only [Finset.card_univ] using hpair (sel r) (sel s) (hsel.ne hrs))
  have hs := h5_bool_disjoint_pair_bound FT Sum.inl Sum.inr
    (by intro i j hij; exact Sum.inl.inj hij)
    (by intro i j hij; exact Sum.inr.inj hij)
    (by intro i j hij; cases hij) hhalf
  simpa only [FT, R, sel, Sum.elim_inl, Sum.elim_inr,
    HadamardTransform.twist_pattern] using hs

end HadamardPatterns

lemma h5_disjoint_pair_sum_le {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (a b : ι → ρ) (e : ρ → ℕ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) :
    (∑ i, (e (a i) + e (b i))) ≤ ∑ r, e r := by
  classical
  have hdisj : Disjoint (Finset.univ.image a) (Finset.univ.image b) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
    obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hs
    exact hab i j (hir.trans hjr.symm)
  have hae : (∑ i, e (a i)) = ∑ r ∈ Finset.univ.image a, e r := by
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact ha hij
  have hbe : (∑ i, e (b i)) = ∑ r ∈ Finset.univ.image b, e r := by
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact hb hij
  calc
    (∑ i, (e (a i) + e (b i))) = (∑ i, e (a i)) + ∑ i, e (b i) :=
      Finset.sum_add_distrib
    _ = (∑ r ∈ Finset.univ.image a, e r) + ∑ r ∈ Finset.univ.image b, e r := by
      rw [hae, hbe]
    _ = ∑ r ∈ Finset.univ.image a ∪ Finset.univ.image b, e r :=
      (Finset.sum_union hdisj).symm
    _ ≤ ∑ r, e r := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun r hr hs => Nat.zero_le _)

namespace HadamardPatterns

lemma pair_missing_error_bound {α : Type*} (s t : Finset α)
    (f g f' g' H : α → Bool) (p q : Bool)
    (hmissing : ∀ x ∈ s, x ∉ t →
      ¬ (Bool.xor (f' x) (H x) = p ∧ Bool.xor (g' x) (H x) = q)) :
    (s.filter (fun x => Bool.xor (f x) (H x) = p ∧
      Bool.xor (g x) (H x) = q)).card ≤
      (s.filter (fun x => f x ≠ f' x)).card +
      (s.filter (fun x => g x ≠ g' x)).card + t.card := by
  classical
  have hsub : s.filter (fun x => Bool.xor (f x) (H x) = p ∧
      Bool.xor (g x) (H x) = q) ⊆
      s.filter (fun x => f x ≠ f' x) ∪ s.filter (fun x => g x ≠ g' x) ∪ t := by
    intro x hx
    have hxs := (Finset.mem_filter.mp hx).1
    have hpat := (Finset.mem_filter.mp hx).2
    by_cases ht : x ∈ t
    · simp [ht]
    by_cases hf : f x = f' x
    · by_cases hg : g x = g' x
      · exact False.elim ((hmissing x hxs ht) (by simpa [hf, hg] using hpat))
      · simp [hxs, hg]
    · simp [hxs, hf]
  have hcard := Finset.card_le_card hsub
  have hu := Finset.card_union_le (s.filter (fun x => f x ≠ f' x))
    (s.filter (fun x => g x ≠ g' x))
  have ht := Finset.card_union_le
    (s.filter (fun x => f x ≠ f' x) ∪ s.filter (fun x => g x ≠ g' x)) t
  omega

lemma robust_disjoint_pair_bound {ι α ρ : Type*}
    [Fintype ι] [Fintype α] [Fintype ρ]
    (F G : ρ → α → Bool) (a b : ι → ρ) (H : α → Bool) (p q : ι → Bool)
    (t : ι → Finset α)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hpair : ∀ r s, r ≠ s →
      2 * ((Finset.univ : Finset α).filter (fun x => F r x ≠ F s x)).card =
        Fintype.card α)
    (ht : ∀ i, (t i).card ≤ 2)
    (hmissing : ∀ i x, x ∉ t i →
      ¬ (Bool.xor (G (a i) x) (H x) = p i ∧
          Bool.xor (G (b i) x) (H x) = q i)) :
    Fintype.card ι * Fintype.card α ≤
      8 * (∑ r, ((Finset.univ : Finset α).filter (fun x => F r x ≠ G r x)).card) +
        16 * Fintype.card ι + 2 * Fintype.card α := by
  classical
  let err : ρ → ℕ := fun r =>
    ((Finset.univ : Finset α).filter (fun x => F r x ≠ G r x)).card
  let count : ι → ℕ := fun i => ((Finset.univ : Finset α).filter
    (fun x => Bool.xor (F (a i) x) (H x) = p i ∧
      Bool.xor (F (b i) x) (H x) = q i)).card
  have hc : ∀ i, count i ≤ err (a i) + err (b i) + 2 := by
    intro i
    have he := pair_missing_error_bound (Finset.univ : Finset α) (t i)
      (F (a i)) (F (b i)) (G (a i)) (G (b i)) H (p i) (q i)
      (fun x _ hx => hmissing i x hx)
    dsimp [count, err]
    exact le_trans he (Nat.add_le_add_left (ht i) _)
  have hsum : (∑ i, count i) ≤ (∑ r, err r) + 2 * Fintype.card ι := by
    calc
      (∑ i, count i) ≤ ∑ i, (err (a i) + err (b i) + 2) :=
        Finset.sum_le_sum (fun i _ => hc i)
      _ = (∑ i, (err (a i) + err (b i))) + 2 * Fintype.card ι := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ ≤ (∑ r, err r) + 2 * Fintype.card ι :=
        Nat.add_le_add_right (h5_disjoint_pair_sum_le a b err ha hb hab) _
  have hbound := arbitrary_disjoint_pair_bound F a b H p q ha hb hab hpair
  change Fintype.card ι * Fintype.card α ≤ 8 * (∑ i, count i) + 2 * Fintype.card α at hbound
  change Fintype.card ι * Fintype.card α ≤
    8 * (∑ r, err r) + 16 * Fintype.card ι + 2 * Fintype.card α
  omega

lemma pair_bound_simplify (n k e : ℕ) (hn : 80 ≤ n)
    (h : k * n ≤ 8 * e + 16 * k + 2 * n) :
    k * n ≤ 3 * n + 10 * e := by
  have hnk : 80 * k ≤ k * n := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right k hn
  omega

end HadamardPatterns

namespace HadamardPatterns

lemma good_triple_budget (n e₁ e₂ e₃ k : ℕ) (hn : 128 ≤ n)
    (h₁ : 16 * e₁ ≤ n) (h₂ : 16 * e₂ ≤ n) (h₃ : 16 * e₃ ≤ n)
    (hk : k ≤ 5) : 4 * (e₁ + e₂ + e₃ + k) < n := by
  omega

lemma sum_row_errors {ρ α : Type*} [Fintype ρ] [Fintype α]
    (F G : ρ → α → Bool) :
    (∑ r, ((Finset.univ : Finset α).filter (fun x => F r x ≠ G r x)).card) =
      ((Finset.univ : Finset (ρ × α)).filter (fun z => F z.1 z.2 ≠ G z.1 z.2)).card := by
  classical
  simp only [Finset.card_filter]
  simpa using (Finset.sum_product (Finset.univ : Finset ρ) (Finset.univ : Finset α)
    (fun z => if F z.1 z.2 ≠ G z.1 z.2 then (1 : ℕ) else 0)).symm

lemma sum_col_errors {ρ α : Type*} [Fintype ρ] [Fintype α]
    (F G : ρ → α → Bool) :
    (∑ x, ((Finset.univ : Finset ρ).filter (fun r => F r x ≠ G r x)).card) =
      ((Finset.univ : Finset (ρ × α)).filter (fun z => F z.1 z.2 ≠ G z.1 z.2)).card := by
  classical
  rw [← sum_row_errors F G]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

end HadamardPatterns

namespace HadamardPatterns

lemma finite_pair_error_charge {n : ℕ} {ι : Type*} [Fintype ι]
    (F G : Fin n → Fin n → Bool) (a b : ι → Fin n)
    (H : Fin n → Bool) (p q : ι → Bool) (t : ι → Finset (Fin n))
    (hn : 80 ≤ n)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (hpair : ∀ r s, r ≠ s →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F s x)).card = n)
    (ht : ∀ i, (t i).card ≤ 2)
    (hmissing : ∀ i x, x ∉ t i →
      ¬ (Bool.xor (G (a i) x) (H x) = p i ∧
          Bool.xor (G (b i) x) (H x) = q i)) :
    n * Fintype.card ι ≤ 3 * n +
      10 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun z => G z.1 z.2 ≠ F z.1 z.2)).card := by
  classical
  have hs := robust_disjoint_pair_bound F G a b H p q t ha hb hab
    (by simpa only [Fintype.card_fin] using hpair) ht hmissing
  simp only [Fintype.card_fin] at hs
  rw [sum_row_errors F G] at hs
  have he := pair_bound_simplify n (Fintype.card ι)
    (((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => F z.1 z.2 ≠ G z.1 z.2)).card) hn hs
  simpa only [Nat.mul_comm n, ne_comm] using he

end HadamardPatterns



lemma h5_extract_disjoint_pairs {ι ρ : Type*} [DecidableEq ρ]
    (s : ι → Finset ρ)
    (hcard : ∀ i, (s i).card = 2)
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ a b : ι → ρ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i j, a i ≠ b j) ∧ (∀ i, s i = {a i, b i}) := by
  classical
  have hex : ∀ i, ∃ x y, x ≠ y ∧ s i = {x, y} :=
    fun i => Finset.card_eq_two.mp (hcard i)
  let a : ι → ρ := fun i => Classical.choose (hex i)
  let b : ι → ρ := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hp : ∀ i, a i ≠ b i ∧ s i = {a i, b i} :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hamem : ∀ i, a i ∈ s i := by
    intro i
    rw [(hp i).2]
    simp
  have hbmem : ∀ i, b i ∈ s i := by
    intro i
    rw [(hp i).2]
    simp
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (hamem i) (by
      simpa only [hij] using hamem j)
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (hbmem i) (by
      simpa only [hij] using hbmem j)
  have hab : ∀ i j, a i ≠ b j := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      exact (hp i).1 hij
    · exact Finset.disjoint_left.mp (hdisj heq) (hamem i) (by
        simpa only [hij] using hbmem j)
  exact ⟨a, b, ha, hb, hab, fun i => (hp i).2⟩


open scoped BigOperators

namespace HadamardPieces

lemma piece_count_bound {ι : Type*} [Fintype ι] (a b : ι → ℕ)
    (ha : ∀ i, a i ≤ 2) (hb : ∀ i, b i ≤ 2) :
    (∑ i, (a i + b i)) ≤ 2 * Fintype.card ι +
      ((Finset.univ : Finset ι).filter (fun i => a i = 2)).card +
      ((Finset.univ : Finset ι).filter (fun i => b i = 2)).card := by
  classical
  have hpoint : ∀ i, a i + b i ≤ 2 + (if a i = 2 then 1 else 0) +
      (if b i = 2 then 1 else 0) := by
    intro i
    have ha' := ha i
    have hb' := hb i
    by_cases h₁ : a i = 2 <;> by_cases h₂ : b i = 2 <;> simp [h₁, h₂] <;> omega
  calc
    (∑ i, (a i + b i)) ≤ ∑ i, (2 + (if a i = 2 then 1 else 0) +
      (if b i = 2 then 1 else 0)) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, Nat.mul_comm]

lemma leaves_error_charge (n k g t₁ t₂ e : ℕ)
    (hleaf : g ≤ 2*k+t₁+t₂)
    (h₁ : n*t₁ ≤ 3*n+10*e) (h₂ : n*t₂ ≤ 3*n+10*e) :
    n*g ≤ 2*n*k+6*n+20*e := by
  have hmul := Nat.mul_le_mul_left n hleaf
  nlinarith

end HadamardPieces

namespace HadamardPatterns

lemma double_family_error_charge {n : ℕ} {ι : Type*} [Fintype ι]
    (F G : Fin n → Fin n → Bool) (s : ι → Finset (Fin n)) (H : Fin n → Bool)
    (hn : 80 ≤ n)
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hpair : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hmissing : ∀ i, (s i).card = 2 → ∀ a b : Fin n,
      s i = {a, b} → a ≠ b → ∃ (p q : Bool) (t : Finset (Fin n)),
        t.card ≤ 2 ∧ ∀ x, x ∉ t →
          ¬ (Bool.xor (G a x) (H x) = p ∧ Bool.xor (G b x) (H x) = q)) :
    n * ((Finset.univ : Finset ι).filter (fun i => (s i).card = 2)).card ≤
      3 * n + 10 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun z => G z.1 z.2 ≠ F z.1 z.2)).card := by
  classical
  let doubles : Finset ι := Finset.univ.filter (fun i => (s i).card = 2)
  have hcard : ∀ i : doubles, (s i.val).card = 2 := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  have hd : Pairwise (fun i j : doubles => Disjoint (s i.val) (s j.val)) := by
    intro i j hij
    apply hdisj
    intro hval
    exact hij (Subtype.ext hval)
  obtain ⟨a, b, ha, hb, hab, hs⟩ :=
    h5_extract_disjoint_pairs (fun i : doubles => s i.val) hcard hd
  have hex : ∀ i : doubles, ∃ (p q : Bool) (t : Finset (Fin n)),
      t.card ≤ 2 ∧ ∀ x, x ∉ t →
        ¬ (Bool.xor (G (a i) x) (H x) = p ∧ Bool.xor (G (b i) x) (H x) = q) := by
    intro i
    exact hmissing i.val (hcard i) (a i) (b i) (hs i) (hab i i)
  choose p q t ht hm using hex
  have hbound := finite_pair_error_charge F G a b H p q t hn ha hb hab hpair ht hm
  simpa only [Fintype.card_coe] using hbound

end HadamardPatterns

namespace HadamardPatterns

lemma transpose_error_count {ρ α : Type*} [Fintype ρ] [Fintype α]
    (F G : ρ → α → Bool) :
    ((Finset.univ : Finset (α × ρ)).filter (fun z => G z.2 z.1 ≠ F z.2 z.1)).card =
      ((Finset.univ : Finset (ρ × α)).filter (fun z => G z.1 z.2 ≠ F z.1 z.2)).card := by
  classical
  rw [← sum_row_errors (fun x r => G r x) (fun x r => F r x)]
  exact sum_col_errors G F

lemma two_bank_leaf_charge {n : ℕ} {ι : Type*} [Fintype ι]
    (F G : Fin n → Fin n → Bool) (left right : ι → Finset (Fin n))
    (Hleft Hright : Fin n → Bool) (hn : 80 ≤ n)
    (hdisjleft : Pairwise (fun i j => Disjoint (left i) (left j)))
    (hdisjright : Pairwise (fun i j => Disjoint (right i) (right j)))
    (hsizeleft : ∀ i, (left i).card ≤ 2) (hsizeright : ∀ i, (right i).card ≤ 2)
    (hrows : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hcols : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x r ≠ F x u)).card = n)
    (hmissingleft : ∀ i, (left i).card = 2 → ∀ a b : Fin n,
      left i = {a,b} → a ≠ b → ∃ (p q : Bool) (t : Finset (Fin n)),
        t.card ≤ 2 ∧ ∀ x, x ∉ t →
          ¬ (Bool.xor (G a x) (Hleft x) = p ∧ Bool.xor (G b x) (Hleft x) = q))
    (hmissingright : ∀ i, (right i).card = 2 → ∀ a b : Fin n,
      right i = {a,b} → a ≠ b → ∃ (p q : Bool) (t : Finset (Fin n)),
        t.card ≤ 2 ∧ ∀ x, x ∉ t →
          ¬ (Bool.xor (G x a) (Hright x) = p ∧ Bool.xor (G x b) (Hright x) = q)) :
    n * (∑ i, ((left i).card + (right i).card)) ≤
      2 * n * Fintype.card ι + 6 * n +
        20 * ((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun z => G z.1 z.2 ≠ F z.1 z.2)).card := by
  classical
  have hleft := double_family_error_charge F G left Hleft hn hdisjleft hrows hmissingleft
  have hright := double_family_error_charge (fun x r => F r x) (fun x r => G r x)
    right Hright hn hdisjright hcols hmissingright
  rw [transpose_error_count F G] at hright
  have hcount := HadamardPieces.piece_count_bound (fun i => (left i).card)
    (fun i => (right i).card) hsizeleft hsizeright
  exact HadamardPieces.leaves_error_charge n (Fintype.card ι)
    (∑ i, ((left i).card + (right i).card))
    ((Finset.univ.filter (fun i => (left i).card = 2)).card)
    ((Finset.univ.filter (fun i => (right i).card = 2)).card)
    (((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => G z.1 z.2 ≠ F z.1 z.2)).card) hcount hleft hright

end HadamardPatterns

end PEqualNP.Outside.L_meta_25806_aux.Patterns


open scoped BigOperators

namespace PEqualNP.Outside.L_meta_25806_aux

def agreeSign (a b : Bool) : ℤ := if a = b then 1 else -1

lemma agreeSign_mul (a b c : Bool) :
    agreeSign a c * agreeSign b c = agreeSign a b := by
  cases a <;> cases b <;> cases c <;> decide

lemma agreeSign_sum {α : Type*} [Fintype α] (f g : α → Bool) :
    (∑ x, agreeSign (f x) (g x)) = (Fintype.card α : ℤ) -
      2 * (((Finset.univ : Finset α).filter (fun x => f x ≠ g x)).card : ℤ) := by
  classical
  calc
    _ = ∑ x, (1 - 2 * (if f x ≠ g x then (1 : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      cases f x <;> cases g x <;> norm_num [agreeSign]
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma integer_quadratic (s : ℤ) : 3 * s ≤ s ^ 2 + 2 := by
  by_cases hs : s ≤ 1
  · have hp := mul_nonneg_of_nonpos_of_nonpos (show s - 1 ≤ 0 by omega)
      (show s - 2 ≤ 0 by omega)
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ s - 1 by omega) (show 0 ≤ s - 2 by omega)
    nlinarith

lemma common_baseline_error {ι α : Type*} [Fintype ι] [Fintype α]
    (F : ι → α → Bool) (H : α → Bool)
    (hpair : ∀ i j, i ≠ j →
      2 * ((Finset.univ : Finset α).filter (fun x => F i x ≠ F j x)).card =
        Fintype.card α) :
    Fintype.card ι * Fintype.card α ≤ Fintype.card α +
      3 * (∑ i, ((Finset.univ : Finset α).filter (fun x => F i x ≠ H x)).card) := by
  classical
  let v : ι → α → ℤ := fun i x => agreeSign (F i x) (H x)
  let E : ι → ℤ := fun i =>
    (((Finset.univ : Finset α).filter (fun x => F i x ≠ H x)).card : ℤ)
  have hgram : ∀ i j, (∑ x, v i x * v j x) =
      if i = j then (Fintype.card α : ℤ) else 0 := by
    intro i j
    simp only [v, agreeSign_mul]
    rw [agreeSign_sum]
    by_cases hij : i = j
    · subst j
      simp
    · simp only [hij, ite_false]
      have hc : (2 : ℤ) * (((Finset.univ : Finset α).filter
          (fun x => F i x ≠ F j x)).card : ℤ) = (Fintype.card α : ℤ) := by
        exact_mod_cast hpair i j hij
      linarith
  have hnorm : (∑ x, (∑ i, v i x) ^ 2) =
      (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) := by
    calc
      _ = ∑ i, ∑ j, ∑ x, v i x * v j x := by
        simp only [pow_two, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = _ := by simp [hgram]
  have hmass : (∑ x, ∑ i, v i x) =
      (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) - 2 * ∑ i, E i := by
    rw [Finset.sum_comm]
    simp only [v, agreeSign_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, E]
  have hbound : 3 * (∑ x, ∑ i, v i x) ≤
      (∑ x, (∑ i, v i x) ^ 2) + 2 * (Fintype.card α : ℤ) := by
    have hp := Finset.sum_le_sum (s := (Finset.univ : Finset α))
      (fun x hx => integer_quadratic (∑ i, v i x))
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hp
  rw [hnorm, hmass] at hbound
  have hfinal : (Fintype.card ι : ℤ) * (Fintype.card α : ℤ) ≤
      (Fintype.card α : ℤ) + 3 * ∑ i, E i := by nlinarith
  dsimp [E] at hfinal
  exact_mod_cast hfinal

end PEqualNP.Outside.L_meta_25806_aux


namespace PEqualNP.Outside.L_meta_25806_aux

lemma unused_rows_error {ι α : Type*} [Fintype ι] [Fintype α]
    (F A : ι → α → Bool) (U : Finset ι)
    (hpair : ∀ i j, i ≠ j →
      2 * ((Finset.univ : Finset α).filter (fun x => F i x ≠ F j x)).card =
        Fintype.card α)
    (hconst : ∀ i ∈ U, ∀ j ∈ U, ∀ x, A i x = A j x) :
    U.card * Fintype.card α ≤ Fintype.card α +
      3 * (∑ i, ((Finset.univ : Finset α).filter (fun x => F i x ≠ A i x)).card) := by
  classical
  by_cases hU : U.Nonempty
  · obtain ⟨u, hu⟩ := hU
    have hp : ∀ i j : U, i ≠ j →
        2 * ((Finset.univ : Finset α).filter
          (fun x => F i.val x ≠ F j.val x)).card = Fintype.card α := by
      intro i j hij
      apply hpair
      intro heq
      exact hij (Subtype.ext heq)
    have hc := common_baseline_error (fun i : U => F i.val) (A u) hp
    have heq : (∑ i : U, ((Finset.univ : Finset α).filter
        (fun x => F i.val x ≠ A u x)).card) =
        ∑ i ∈ U, ((Finset.univ : Finset α).filter
          (fun x => F i x ≠ A i x)).card := by
      rw [Finset.sum_coe_sort U (fun i : ι =>
        ((Finset.univ : Finset α).filter (fun x => F i x ≠ A u x)).card)]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Finset.filter_congr
      intro x hx
      rw [hconst i hi u hu x]
    rw [heq] at hc
    have hs : (∑ i ∈ U, ((Finset.univ : Finset α).filter
        (fun x => F i x ≠ A i x)).card) ≤
        ∑ i, ((Finset.univ : Finset α).filter
          (fun x => F i x ≠ A i x)).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      exact Nat.zero_le _
    simpa only [Fintype.card_coe] using (hc.trans (by omega))
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simp [he]

lemma row_errors_eq_column_errors {α β : Type*} [Fintype α] [Fintype β]
    (F A : α → β → Bool) :
    (∑ i, ((Finset.univ : Finset β).filter (fun j => F i j ≠ A i j)).card) =
      ∑ j, ((Finset.univ : Finset α).filter (fun i => F i j ≠ A i j)).card := by
  classical
  calc
    _ = ∑ i, ∑ j, (if F i j ≠ A i j then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.sum_boole (fun j => F i j ≠ A i j) Finset.univ).symm
    _ = ∑ j, ∑ i, (if F i j ≠ A i j then (1 : ℕ) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_boole (fun i => F i j ≠ A i j) Finset.univ

lemma table_support_error (n b : ℕ) (F A : Fin n → Fin n → Bool)
    (R C : Finset (Fin n))
    (hused : R.card + C.card ≤ b + 1)
    (hrows : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F i x ≠ F j x)).card = n)
    (hcols : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x i ≠ F x j)).card = n)
    (hR : ∀ i, i ∉ R → ∀ j, j ∉ R → ∀ x, A i x = A j x)
    (hC : ∀ i, i ∉ C → ∀ j, j ∉ C → ∀ x, A x i = A x j) :
    2 * n ^ 2 ≤ b * n + 3 * n +
      6 * (∑ i, ((Finset.univ : Finset (Fin n)).filter
        (fun x => F i x ≠ A i x)).card) := by
  classical
  have hr := unused_rows_error F A Rᶜ
    (by simpa using hrows) (by simpa only [Finset.mem_compl] using hR)
  have hc := unused_rows_error (fun i x => F x i) (fun i x => A x i) Cᶜ
    (by simpa using hcols) (by simpa only [Finset.mem_compl] using hC)
  rw [← row_errors_eq_column_errors F A] at hc
  simp only [Fintype.card_fin] at hr hc
  have hrc : Rᶜ.card + R.card = n := by simp
  have hcc : Cᶜ.card + C.card = n := by simp
  nlinarith [Nat.mul_le_mul_right n hused]

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux
lemma table_support_count (n : ℕ) (F A : Fin n → Fin n → Bool)
    (R C : Finset (Fin n))
    (hrows : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F i x ≠ F j x)).card = n)
    (hcols : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x i ≠ F x j)).card = n)
    (hR : ∀ i, i ∉ R → ∀ j, j ∉ R → ∀ x, A i x = A j x)
    (hC : ∀ i, i ∉ C → ∀ j, j ∉ C → ∀ x, A x i = A x j) :
    2 * n ^ 2 ≤ n * (R.card + C.card) + 2 * n +
      6 * (∑ i, ((Finset.univ : Finset (Fin n)).filter
        (fun x => F i x ≠ A i x)).card) := by
  classical
  have hr := unused_rows_error F A Rᶜ
    (by simpa using hrows) (by simpa only [Finset.mem_compl] using hR)
  have hc := unused_rows_error (fun i x => F x i) (fun i x => A x i) Cᶜ
    (by simpa using hcols) (by simpa only [Finset.mem_compl] using hC)
  rw [← row_errors_eq_column_errors F A] at hc
  simp only [Fintype.card_fin] at hr hc
  have hrc : Rᶜ.card + R.card = n := by simp
  have hcc : Cᶜ.card + C.card = n := by simp
  nlinarith

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux.PairSelection

def rowLeaves (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ S)

def colLeaves (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => n+i.val ∈ S)

lemma rowLeaves_card (n : ℕ) (S : Finset ℕ) :
    (rowLeaves n S).card = (S.filter (fun w => w < n)).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
  · intro i hi j hj he
    exact Fin.ext he
  · intro w hw
    have h := Finset.mem_filter.mp hw
    refine ⟨⟨w, h.2⟩, ?_, rfl⟩
    simp [rowLeaves, h.1]

lemma colLeaves_card (n : ℕ) (S : Finset ℕ) (hs : S ⊆ Finset.range (2*n)) :
    (colLeaves n S).card = (S.filter (fun w => n ≤ w)).card := by
  apply Finset.card_bij (fun i _ => n+i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, by omega⟩
  · intro i hi j hj he
    apply Fin.ext
    omega
  · intro w hw
    have h := Finset.mem_filter.mp hw
    have hi := Finset.mem_range.mp (hs h.1)
    refine ⟨⟨w-n, by omega⟩, ?_, by simp; omega⟩
    simp only [colLeaves, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Nat.add_sub_of_le h.2] using h.1

lemma leaf_bank_card (n : ℕ) (S : Finset ℕ) (hs : S ⊆ Finset.range (2*n)) :
    S.card = (rowLeaves n S).card + (colLeaves n S).card := by
  rw [rowLeaves_card, colLeaves_card n S hs]
  have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun w => w < n)
  simpa only [not_lt] using h.symm


end PEqualNP.Outside.L_meta_25806_aux.PairSelection

namespace PEqualNP.Outside.L_meta_25806_aux.BinarySupport

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25806_aux.PairSelection

lemma raw_reads_support (n : ℕ) (F : Fin n → Fin n → Bool) (C : BinaryCircuit)
    (out : Bool → Bool) (ho : 2*n ≤ C.output)
    (hrows : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F i x ≠ F j x)).card = n)
    (hcols : ∀ i j : Fin n, i ≠ j →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x i ≠ F x j)).card = n) :
    2*n^2 ≤ n*((Finset.range (2*n)).filter (fun w => 1 ≤ reads C w)).card + 2*n +
      6*((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
        out (C.eval (PEqualNP.Represents.oneEach z.1 z.2)) ≠ F z.1 z.2)).card := by
  classical
  let S := (Finset.range (2*n)).filter (fun w => 1 ≤ reads C w)
  let R := rowLeaves n S
  let T := colLeaves n S
  let A := fun i j : Fin n => out (C.eval (PEqualNP.Represents.oneEach i j))
  have hR (i : Fin n) : i ∈ R ↔ 1 ≤ reads C i.val := by
    simp only [R, rowLeaves, Finset.mem_filter, Finset.mem_univ, true_and, S,
      Finset.mem_range]
    have hi := i.isLt
    omega
  have hT (i : Fin n) : i ∈ T ↔ 1 ≤ reads C (n+i.val) := by
    simp only [T, colLeaves, Finset.mem_filter, Finset.mem_univ, true_and, S,
      Finset.mem_range]
    have hi := i.isLt
    omega
  have hrconst : ∀ i, i ∉ R → ∀ j, j ∉ R → ∀ x, A i x = A j x := by
    intro i hi j hj x
    have zi : reads C i.val = 0 := by rw [hR] at hi; omega
    have zj : reads C j.val = 0 := by rw [hR] at hj; omega
    exact congrArg out (unused_rows C (by omega) i j zi zj x)
  have hcconst : ∀ i, i ∉ T → ∀ j, j ∉ T → ∀ x, A x i = A x j := by
    intro i hi j hj x
    have zi : reads C (n+i.val) = 0 := by rw [hT] at hi; omega
    have zj : reads C (n+j.val) = 0 := by rw [hT] at hj; omega
    exact congrArg out (unused_columns C (by omega) i j zi zj x)
  have hc := leaf_bank_card n S (Finset.filter_subset _ _)
  have hb := PEqualNP.Outside.L_meta_25806_aux.table_support_count n F A R T
    hrows hcols hrconst hcconst
  change S.card = R.card+T.card at hc
  rw [← hc] at hb
  have he : (∑ i, ((Finset.univ : Finset (Fin n)).filter (fun x => F i x ≠ A i x)).card) =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => A z.1 z.2 ≠ F z.1 z.2)).card := by
    simp only [Finset.card_filter]
    simpa [ne_comm] using (Finset.sum_product (Finset.univ : Finset (Fin n))
      (Finset.univ : Finset (Fin n)) (fun z => if F z.1 z.2 ≠ A z.1 z.2 then (1 : ℕ) else 0)).symm
  rw [he] at hb
  exact hb

end PEqualNP.Outside.L_meta_25806_aux.BinarySupport

namespace PEqualNP.Outside.L_meta_25806_aux

namespace UnaryAudit

open PEqualNP.CircuitLowerBounds

lemma length_step (w : List Bool) (g : Gate) :
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
  simp

lemma property_step {α : Type} (P : (α → Bool) → Prop)
    (hc : ∀ b, P (fun _ => b))
    (hu : ∀ (f : α → Bool) (k : Bool → Bool), P f → P (fun a => k (f a)))
    (w : α → List Bool) (N : ℕ) (hl : ∀ a, (w a).length = N)
    (hw : ∀ i, P (fun a => (w a).getD i false))
    (g : Gate) (hg : g.inputs.length ≤ 1) :
    ∀ i, P (fun a => (w a ++ [g.op.eval (g.inputs.map fun j => (w a).getD j false)]).getD i false) := by
  intro i
  by_cases hi : i < N
  · convert hw i using 1
    ext a
    exact List.getD_append _ _ _ _ (by simpa [hl a] using hi)
  · by_cases he : i = N
    · subst i
      have heq : (fun a => (w a ++ [g.op.eval (g.inputs.map fun j => (w a).getD j false)]).getD N false) =
          (fun a => g.op.eval (g.inputs.map fun j => (w a).getD j false)) := by
        funext a
        rw [← hl a]
        simp
      rw [heq]
      cases hs : g.inputs with
      | nil => simpa only [hs, List.map_nil] using hc (g.op.eval [])
      | cons j js =>
        have hjs : js = [] := by simpa [hs] using hg
        subst js
        simpa only [hs, List.map_cons, List.map_nil] using
          hu (fun a => (w a).getD j false) (fun b => g.op.eval [b]) (hw j)
    · convert hc false using 1
      ext a
      exact List.getD_eq_default _ _ (by simp [hl a]; omega)

lemma property_fold {α : Type} (P : (α → Bool) → Prop)
    (hc : ∀ b, P (fun _ => b))
    (hu : ∀ (f : α → Bool) (k : Bool → Bool), P f → P (fun a => k (f a)))
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 1)
    (w : α → List Bool) (N : ℕ) (hl : ∀ a, (w a).length = N)
    (hw : ∀ i, P (fun a => (w a).getD i false)) :
    ∀ i, P (fun a => (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) (w a)).getD i false) := by
  induction gs generalizing w N with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun h hh => hg h (List.mem_cons_of_mem _ hh))
      (fun a => w a ++ [g.op.eval (g.inputs.map fun j => (w a).getD j false)]) (N + 1)
    · intro a
      simp [hl a]
    · exact property_step P hc hu w N hl hw g (hg g List.mem_cons_self)


def OneBank {n : ℕ} (h : Fin n × Fin n → Bool) : Prop :=
  (∃ f : Fin n → Bool, ∀ z, h z = f z.1) ∨
  (∃ f : Fin n → Bool, ∀ z, h z = f z.2)

lemma oneBank_const {n : ℕ} (b : Bool) : OneBank (n := n) (fun _ => b) :=
  Or.inl ⟨fun _ => b, fun _ => rfl⟩

lemma oneBank_unary {n : ℕ} (f : Fin n × Fin n → Bool) (k : Bool → Bool)
    (hf : OneBank f) : OneBank (fun a => k (f a)) := by
  rcases hf with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨fun a => k (f a), fun z => congrArg k (hf z)⟩
  · exact Or.inr ⟨fun a => k (f a), fun z => congrArg k (hf z)⟩

lemma oneBank_inputs {n : ℕ} (i : ℕ) :
    OneBank (fun z : Fin n × Fin n => (PEqualNP.Represents.oneEach z.1 z.2).getD i false) := by
  by_cases hi : i < n
  · left
    refine ⟨fun u => (List.ofFn fun a : Fin n => decide (a = u)).getD i false, ?_⟩
    intro z
    exact List.getD_append _ _ _ _ (by simpa using hi)
  · right
    refine ⟨fun v => (List.ofFn fun a : Fin n => decide (a = v)).getD (i - n) false, ?_⟩
    intro z
    dsimp only
    unfold PEqualNP.Represents.oneEach
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

lemma unary_of_zero_binary (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hz : C.gates.countP (fun g => g.inputs.length == 2) = 0) :
    ∀ g ∈ C.gates, g.inputs.length ≤ 1 := by
  intro g hg
  have hf := hfan g hg
  have hz' := List.countP_eq_zero.mp hz g hg
  simp only [beq_iff_eq] at hz'
  omega

lemma zero_binary_oneBank {n : ℕ} (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hz : C.gates.countP (fun g => g.inputs.length == 2) = 0) :
    OneBank (fun z : Fin n × Fin n => C.eval (PEqualNP.Represents.oneEach z.1 z.2)) := by
  exact property_fold OneBank oneBank_const oneBank_unary C.gates
    (unary_of_zero_binary C hfan hz)
    (fun z : Fin n × Fin n => PEqualNP.Represents.oneEach z.1 z.2) (n + n)
    (by intro z; simp [PEqualNP.Represents.oneEach]) oneBank_inputs C.output


lemma pair_errors {α : Type} (s : Finset α) (f g h : α → Bool) :
    (s.filter (fun x => f x ≠ g x)).card ≤
      (s.filter (fun x => f x ≠ h x)).card + (s.filter (fun x => g x ≠ h x)).card := by
  classical
  apply le_trans (Finset.card_le_card (show s.filter (fun x => f x ≠ g x) ⊆
    s.filter (fun x => f x ≠ h x) ∪ s.filter (fun x => g x ≠ h x) from ?_))
    (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union] at hx ⊢
  by_cases hf : f x = h x
  · right
    exact ⟨hx.1, fun hg => hx.2 (hf.trans hg.symm)⟩
  · exact Or.inl ⟨hx.1, hf⟩

lemma common_row_error_bound {n m : ℕ} (hn : 1 < n)
    (F : Fin n → Fin m → Bool) (g : Fin m → Bool)
    (hp : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m) :
    n * m ≤ 4 * ∑ u : Fin n,
      ((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ g x)).card := by
  classical
  let E := fun u : Fin n => ((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ g x)).card
  have ht (u v : Fin n) (huv : u ≠ v) : m ≤ 2 * (E u + E v) := by
    rw [← hp u v huv]
    exact Nat.mul_le_mul_left 2 (pair_errors Finset.univ (F u) (F v) g)
  have hrow (u : Fin n) :
      (n - 1) * m + 2 * E u ≤
        2 * ((n - 1) * E u + ∑ v : Fin n, E v) := by
    have hs := Finset.sum_le_sum (s := Finset.univ.erase u)
      (fun v hv => ht u v (Ne.symm (Finset.ne_of_mem_erase hv)))
    have he : (∑ v ∈ Finset.univ.erase u, E v) + E u = ∑ v : Fin n, E v :=
      Finset.sum_erase_add _ _ (Finset.mem_univ u)
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib] at hs
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hrow u)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hs
  change n * m ≤ 4 * ∑ u : Fin n, E u
  have hn' : 0 < n - 1 := by omega
  have hns : n = (n - 1) + 1 := by omega
  have hmul := congrArg (fun t : ℕ => t * ∑ u : Fin n, E u) hns
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  have hs' : (n - 1) * (n * m) ≤ (n - 1) * (4 * ∑ u : Fin n, E u) := by
    nlinarith only [hs, hmul]
  by_contra h
  have hh : 4 * (∑ u : Fin n, E u) < n * m := by omega
  have hlt := Nat.mul_lt_mul_of_pos_left hh hn'
  omega


lemma sum_row_errors {n m : ℕ} (F G : Fin n → Fin m → Bool) :
    (∑ u, ((Finset.univ : Finset (Fin m)).filter (fun v => F u v ≠ G u v)).card) =
      ((Finset.univ : Finset (Fin n × Fin m)).filter (fun z => F z.1 z.2 ≠ G z.1 z.2)).card := by
  classical
  simp only [Finset.card_filter]
  simpa using (Finset.sum_product (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin m))
    (fun z => if F z.1 z.2 ≠ G z.1 z.2 then (1 : ℕ) else 0)).symm

lemma sum_col_errors {n m : ℕ} (F G : Fin n → Fin m → Bool) :
    (∑ v, ((Finset.univ : Finset (Fin n)).filter (fun u => F u v ≠ G u v)).card) =
      ((Finset.univ : Finset (Fin n × Fin m)).filter (fun z => F z.1 z.2 ≠ G z.1 z.2)).card := by
  classical
  rw [← sum_row_errors F G]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma oneBank_error_bound {n : ℕ} (hn : 1 < n)
    (F : Fin n → Fin n → Bool) (G : Fin n × Fin n → Bool)
    (hr : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F u x ≠ F v x)).card = n)
    (hc : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x u ≠ F x v)).card = n)
    (hG : OneBank G) :
    n ^ 2 ≤ 4 * ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => G z ≠ F z.1 z.2)).card := by
  rcases hG with ⟨g, hg⟩ | ⟨g, hg⟩
  · have he := sum_col_errors F (fun u _ => g u)
    have hb := common_row_error_bound hn (fun u v => F v u) g hc
    rw [he] at hb
    simpa only [pow_two, hg, ne_comm] using hb
  · have he := sum_row_errors F (fun _ v => g v)
    have hb := common_row_error_bound hn F g hr
    rw [he] at hb
    simpa only [pow_two, hg, ne_comm] using hb

lemma zero_binary_target {n : ℕ} (F : Fin n → Fin n → Bool) (C : Circuit)
    (hn : 128 ≤ n)
    (hr : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F u x ≠ F v x)).card = n)
    (hc : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x u ≠ F x v)).card = n)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hz : C.gates.countP (fun g => g.inputs.length == 2) = 0) :
    11 * n ^ 2 ≤ (5 * C.gates.countP (fun g => g.inputs.length == 2) + 20) * n +
      134 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun z => C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ F z.1 z.2)).card := by
  have h := oneBank_error_bound (by omega : 1 < n) F
    (fun z => C.eval (PEqualNP.Represents.oneEach z.1 z.2)) hr hc (zero_binary_oneBank C hfan hz)
  nlinarith

end UnaryAudit
namespace UnaryAudit

lemma unary_input_target {n : ℕ} (F : Fin n → Fin n → Bool)
    (out : Bool → Bool) (i b : ℕ) (hn : 128 ≤ n)
    (hr : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F u x ≠ F v x)).card = n)
    (hc : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x u ≠ F x v)).card = n) :
    11 * n ^ 2 ≤ (5 * b + 20) * n +
      134 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun z => out ((PEqualNP.Represents.oneEach z.1 z.2).getD i false) ≠ F z.1 z.2)).card := by
  have h := oneBank_error_bound (by omega : 1 < n) F
    (fun z => out ((PEqualNP.Represents.oneEach z.1 z.2).getD i false)) hr hc
    (oneBank_unary _ out (oneBank_inputs i))
  nlinarith

lemma empty_binary_target {n : ℕ} (F : Fin n → Fin n → Bool)
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (out : Bool → Bool)
    (b : ℕ) (hz : C.size = 0) (hn : 128 ≤ n)
    (hr : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F u x ≠ F v x)).card = n)
    (hc : ∀ u v : Fin n, u ≠ v →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x u ≠ F x v)).card = n) :
    11 * n ^ 2 ≤ (5 * b + 20) * n +
      134 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun z => out (C.eval (PEqualNP.Represents.oneEach z.1 z.2)) ≠ F z.1 z.2)).card := by
  have hg : C.gates = [] := List.length_eq_zero_iff.mp hz
  simpa only [PEqualNP.MetaComplexity.BinaryCircuit.eval,
    PEqualNP.MetaComplexity.BinaryCircuit.wires, hg, List.foldl_nil] using
      unary_input_target F out C.output b hn hr hc

end UnaryAudit
end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux.Assembly

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25806_aux

lemma reads_eq (C : BinaryCircuit) (w : ℕ) :
    readsOf (binarySkeleton C) w = BinarySupport.reads C w := by
  unfold readsOf PEqualNP.MetaComplexity.NestedCover.readsIn BinarySupport.reads
  rw [binarySkeleton_size]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < C.gates.length := Finset.mem_range.mp hj
  rw [binarySkeleton_gate C j hj']
  simp only [BinarySupport.gateAt, List.getD_eq_getElem _ _ hj', List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

lemma list_disjoint (L : List (Finset ℕ)) (hL : L.Pairwise Disjoint)
    (S T : Finset ℕ) (hS : S ∈ L) (hT : T ∈ L) (hst : S ≠ T) : Disjoint S T := by
  obtain ⟨i,hi,hei⟩ := List.getElem_of_mem hS
  obtain ⟨j,hj,hej⟩ := List.getElem_of_mem hT
  have hij : i ≠ j := by
    intro h
    subst j
    exact hst (hei.symm.trans hej)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · simpa only [hei,hej] using hL.rel_getElem_of_lt hi hj h
  · exact (by simpa only [hei,hej] using hL.rel_getElem_of_lt hj hi h : Disjoint T S).symm

def PieceSemantic {n : ℕ} (A : Fin n → Fin n → Bool)
    (Hr Hc : Fin n → Bool) (S : Finset ℕ) : Prop :=
  (Selection.rows (n := n) S).card ≤ 2 ∧ (Selection.cols (n := n) S).card ≤ 2 ∧
  (∀ a b : Fin n, Selection.rows S = {a,b} → a ≠ b →
    ∃ (p q : Bool) (t : Finset (Fin n)), t.card ≤ 2 ∧ ∀ x, x ∉ t →
      ¬ (Bool.xor (A a x) (Hr x) = p ∧ Bool.xor (A b x) (Hr x) = q)) ∧
  (∀ a b : Fin n, Selection.cols S = {a,b} → a ≠ b →
    ∃ (p q : Bool) (t : Finset (Fin n)), t.card ≤ 2 ∧ ∀ x, x ∉ t →
      ¬ (Bool.xor (A x a) (Hc x) = p ∧ Bool.xor (A x b) (Hc x) = q))

lemma forest_leaf_charge {n : ℕ} (F A : Fin n → Fin n → Bool)
    (Hr Hc : Fin n → Bool) (hn : 80 ≤ n)
    (hrows : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hcols : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x r ≠ F x u)).card = n)
    (L : List (Finset ℕ)) (hd : L.Pairwise Disjoint)
    (hbound : ∀ S ∈ L, S ⊆ Finset.range (n+n))
    (hsem : ∀ S ∈ L, PieceSemantic A Hr Hc S) :
    n * (L.toFinset.biUnion (fun S => S)).card ≤
      2*n*L.length + 6*n + 20*Table.errors F A := by
  classical
  let I := L.toFinset
  have disj : Pairwise (fun i j : I => Disjoint i.val j.val) := by
    intro i j hij
    exact list_disjoint L hd i.val j.val (List.mem_toFinset.mp i.property)
      (List.mem_toFinset.mp j.property) (fun h => hij (Subtype.ext h))
  have sem (i : I) : PieceSemantic A Hr Hc i.val :=
    hsem i.val (List.mem_toFinset.mp i.property)
  have leaf := Patterns.HadamardPatterns.two_bank_leaf_charge F A
    (fun i : I => Selection.rows i.val) (fun i : I => Selection.cols i.val) Hr Hc hn
    (fun i j hij => Selection.rows_disjoint (disj hij))
    (fun i j hij => Selection.cols_disjoint (disj hij))
    (fun i => (sem i).1) (fun i => (sem i).2.1) hrows hcols
    (fun i _ => (sem i).2.2.1) (fun i _ => (sem i).2.2.2)
  have hsum : (L.toFinset.biUnion (fun S => S)).card ≤
      ∑ i : I, ((Selection.rows (n:=n) i.val).card + (Selection.cols (n:=n) i.val).card) := by
    calc
      _ ≤ ∑ S ∈ L.toFinset, S.card := Finset.card_biUnion_le
      _ = _ := by
        rw [Finset.sum_coe_sort I (fun S : Finset ℕ => (Selection.rows (n:=n) S).card + (Selection.cols (n:=n) S).card)]
        apply Finset.sum_congr rfl
        intro S hS
        exact Selection.raw_parts S (hbound S (List.mem_toFinset.mp hS))
  have hmul := Nat.mul_le_mul_left n hsum
  have hcount : Fintype.card I ≤ L.length := by
    simpa only [Fintype.card_coe] using L.toFinset_card_le
  have hcountmul := Nat.mul_le_mul_left (2*n) hcount
  change n * _ ≤ 2*n*Fintype.card I + 6*n + 20*Table.errors F A at leaf
  omega

lemma weighted_arithmetic (n b q d sn sg marked pieces good bad e : ℕ)
    (support : 2*n^2 ≤ n*q + 2*n + 8*e)
    (budget : q+d ≤ b+1)
    (sharing : sn+sg ≤ d)
    (marks : marked ≤ d+sn+sg)
    (piece_bound : pieces ≤ 2*(marked+bad)+sg+1)
    (cover : q ≤ good+sn+bad)
    (leaves : n*good ≤ 2*n*pieces+6*n+20*e)
    (bad_budget : n*bad ≤ 32*e) :
    11*n^2 ≤ (5*b+20)*n+134*e := by
  have hbudget := Nat.mul_le_mul_left n budget
  have hsharing := Nat.mul_le_mul_left n sharing
  have hmarks := Nat.mul_le_mul_left n marks
  have hpieces := Nat.mul_le_mul_left n piece_bound
  have hcover := Nat.mul_le_mul_left n cover
  nlinarith

def TreeSemantic {n : ℕ} (F A : Fin n → Fin n → Bool)
    (B : BinaryCircuit) (Hr Hc : Fin n → Bool) : Prop :=
  ∀ t : BTree, GoodTree (n+n) (binarySkeleton B) t → t.marks ≤ 1 → t.privs.Nonempty →
    t.privs ⊆ ((Finset.range (n+n)).filter (fun w => BinarySupport.reads B w = 1)) \ Table.badNames F A →
    PieceSemantic A Hr Hc t.privs

lemma conditional_normalized {n : ℕ} (F A : Fin n → Fin n → Bool)
    (B : BinaryCircuit) (Hr Hc : Fin n → Bool) (hn : 128 ≤ n)
    (hrows : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hcols : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x r ≠ F x u)).card = n)
    (back : Normalize.Back (n+n) B.gates) (live : Normalize.Live (n+n) B)
    (hs : 0 < B.size)
    (support : 2*n^2 ≤ n*((Finset.range (n+n)).filter
      (fun w => 1 ≤ BinarySupport.reads B w)).card + 2*n + 8*Table.errors F A)
    (semantic : TreeSemantic F A B Hr Hc) :
    11*n^2 ≤ (5*B.size+20)*n+134*Table.errors F A := by
  classical
  let N := n+n
  let r := BinarySupport.reads B
  let bad := Table.badNames F A
  let once := (Finset.range N).filter (fun w => r w = 1)
  let sharedNames := (Finset.range N).filter (fun w => 2 ≤ r w)
  let sharedGates := (Finset.range B.size).filter (fun j => 2 ≤ r (N+j))
  let marked := ∑ w ∈ (Finset.range (N+B.size)).filter (fun w => 2 ≤ r w), r w
  let excess := ∑ w ∈ Finset.range (N+B.size), (r w-1)
  have hout : B.output + 1 = N + B.size := by
    have h := Normalize.live_output_last N B live hs
    change B.output = N + (B.size-1) at h
    omega
  have hparts := binary_concrete_bad_partition N B (binarySkeleton_back N B back) hs hout
    (fun j hj hjlast => by
      rw [reads_eq]
      exact BinarySupport.normalize_live_reads N B hs live j hj hjlast) bad
  have heqreads : readsOf (binarySkeleton B) = r := funext (reads_eq B)
  rw [heqreads] at hparts
  dsimp only at hparts
  obtain ⟨T,hT,hpieces,hdisjoint,hcover⟩ := hparts
  let L := T.map BTree.privs
  have hL : L.length ≤ 2*(marked+bad.card)+sharedGates.card+1 := by
    simpa only [L,List.length_map] using hT
  have hcoverL : L.toFinset.biUnion (fun S => S) = once \ bad := by
    have hm : L.toFinset.biUnion (fun S => S) = T.toFinset.biUnion BTree.privs := by
      ext w
      simp only [Finset.mem_biUnion,List.mem_toFinset]
      constructor
      · rintro ⟨S,hS,hw⟩
        obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hS
        exact ⟨t,ht,hw⟩
      · rintro ⟨t,ht,hw⟩
        exact ⟨t.privs,List.mem_map.mpr ⟨t,ht,rfl⟩,hw⟩
    exact hm.trans hcover
  have hdisjointL : L.Pairwise Disjoint := by
    simpa only [L,List.pairwise_map] using hdisjoint
  have bounds (S : Finset ℕ) (hS : S ∈ L) : S ⊆ Finset.range (n+n) := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hS
    intro w hw
    have h := (Finset.mem_sdiff.mp ((hpieces t ht).2.2.2.1 hw)).1
    exact (Finset.mem_filter.mp h).1
  have hsem (S : Finset ℕ) (hS : S ∈ L) : PieceSemantic A Hr Hc S := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hS
    obtain ⟨hg,hm,hnp,hsub,he⟩ := hpieces t ht
    exact semantic t hg hm hnp hsub
  have hleaf := forest_leaf_charge F A Hr Hc (by omega) hrows hcols
    L hdisjointL bounds hsem
  rw [hcoverL] at hleaf
  have hbudget := BinarySupport.normalized_reads_budget N B hs back live
  have hsharing := PEqualNP.Outside.L_meta_25806.shared_name_gate_budget N B.size r
  have hmarks := PEqualNP.Outside.L_meta_25806.shared_marked_reads_budget N B.size 0 r
  simp only [Nat.add_zero] at hmarks
  have hused := PEqualNP.Outside.L_meta_25806.used_le_good_shared_bad N r bad
  have hgood : ((Finset.range N).filter (fun w => r w = 1 ∧ w ∉ bad)) = once \ bad := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_sdiff, once]
    tauto
  rw [hgood] at hused
  exact weighted_arithmetic n B.size
    (((Finset.range N).filter (fun w => 1 ≤ r w)).card) excess
    sharedNames.card sharedGates.card marked L.length (once \ bad).card bad.card
    (Table.errors F A) support hbudget.le hsharing hmarks hL hused hleaf
    (Table.badNames_budget F A)

lemma conditional_binary {n : ℕ} (F : Fin n → Fin n → Bool)
    (B : BinaryCircuit) (out : Bool → Bool) (Hr Hc : Fin n → Bool) (hn : 128 ≤ n)
    (hrows : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hcols : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x r ≠ F x u)).card = n)
    (back : Normalize.Back (n+n) B.gates) (live : Normalize.Live (n+n) B)
    (hs : 0 < B.size)
    (semantic : TreeSemantic F (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v))) B Hr Hc) :
    11*n^2 ≤ (5*B.size+20)*n+
      134*Table.errors F (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v))) := by
  have hout : 2*n ≤ B.output := by
    have h := Normalize.live_output_last (n+n) B live hs
    omega
  have support := BinarySupport.raw_reads_support n F B out hout hrows hcols
  apply conditional_normalized F _ B Hr Hc hn hrows hcols back live hs ?_ semantic
  have heq : 2*n = n+n := by omega
  rw [heq] at support
  change 2*n^2 ≤ n*((Finset.range (n+n)).filter
    (fun w => 1 ≤ BinarySupport.reads B w)).card + (n+n) +
    6*Table.errors F (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v))) at support
  omega

lemma conditional_root (n : ℕ) (F : Fin n → Fin n → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hn : 128 ≤ n)
    (hrows : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F r x ≠ F u x)).card = n)
    (hcols : ∀ r u, r ≠ u →
      2 * ((Finset.univ : Finset (Fin n)).filter (fun x => F x r ≠ F x u)).card = n)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (semantic : ∀ (B : BinaryCircuit) (out : Bool → Bool),
      Normalize.Back (n+n) B.gates → Normalize.Live (n+n) B → 0 < B.size →
      ∃ Hr Hc : Fin n → Bool,
        TreeSemantic F (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v))) B Hr Hc) :
    let e := ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun z => C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ F z.1 z.2)).card
    let b := C.gates.countP (fun gate => gate.inputs.length == 2)
    11*n^2 ≤ (5*b+20)*n+134*e := by
  let b := C.gates.countP (fun gate => gate.inputs.length == 2)
  obtain ⟨B,out,hsize,hback,hout,hlive,hreach,heval⟩ := Normalize.normalize_live (n+n) (by omega) C hfan
  let A := fun u v : Fin n => out (B.eval (PEqualNP.Represents.oneEach u v))
  have hA : (fun u v : Fin n => C.eval (PEqualNP.Represents.oneEach u v)) = A := by
    funext u v
    exact heval _ (BinarySupport.oneEach_length u v)
  change 11*n^2 ≤ (5*b+20)*n + 134*Table.errors F (fun u v => C.eval (PEqualNP.Represents.oneEach u v))
  rw [hA]
  by_cases hz : B.size = 0
  · exact UnaryAudit.empty_binary_target F B out b hz hn hrows hcols
  · have hs : 0 < B.size := by omega
    obtain ⟨Hr,Hc,hsem⟩ := semantic B out hback hlive hs
    have h := conditional_binary F B out Hr Hc hn hrows hcols hback hlive hs hsem
    have hmul := Nat.mul_le_mul_right n hsize
    change B.size ≤ b at hsize
    change 11*n^2 ≤ (5*B.size+20)*n+134*Table.errors F A at h
    nlinarith

end PEqualNP.Outside.L_meta_25806_aux.Assembly
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def binaryInputs (C : BinaryCircuit) (j : ℕ) : List ℕ :=
  ((C.gates[j]?).map (fun g => [g.left, g.right])).getD []

def binaryReadsIn (C : BinaryCircuit) (G : Finset ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ G, (binaryInputs C j).count w

def BinaryReadsBack (n : ℕ) (C : BinaryCircuit) : Prop :=
  ∀ j < C.gates.length, ∀ i ∈ binaryInputs C j, i < n + j

def BinaryIsTree (n : ℕ) (C : BinaryCircuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := binaryReadsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      (binaryInputs C j).length = 2 ∧ ∀ w ∈ binaryInputs C j, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧
      binaryReadsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

lemma binarySkeleton_output (C : BinaryCircuit) : (binarySkeleton C).output = C.output := rfl

lemma binarySkeleton_inputs (C : BinaryCircuit) (j : ℕ) :
    (gateAt (binarySkeleton C) j).inputs = binaryInputs C j := by
  simp only [binarySkeleton, gateAt, binaryInputs,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.gates[j]? <;> rfl

lemma binaryInputs_at (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length) :
    binaryInputs C j = [C.gates[j].left, C.gates[j].right] := by
  simp [binaryInputs, List.getElem?_eq_getElem hj]

lemma binaryInputs_length (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length) :
    (binaryInputs C j).length = 2 := by
  simp only [binaryInputs_at C j hj, List.length_cons, List.length_nil]

lemma binarySkeleton_readsIn (C : BinaryCircuit) (G : Finset ℕ) (w : ℕ) :
    readsIn (binarySkeleton C) G w = binaryReadsIn C G w := by
  simp only [readsIn, binaryReadsIn, binarySkeleton_inputs]

lemma binarySkeleton_readsOf (C : BinaryCircuit) (w : ℕ) :
    readsOf (binarySkeleton C) w = binaryReadsIn C (Finset.range C.size) w := by
  simp only [readsOf, binarySkeleton_size, binarySkeleton_readsIn]

lemma binarySkeleton_back_iff (n : ℕ) (C : BinaryCircuit) :
    ReadsBack n (binarySkeleton C) ↔ BinaryReadsBack n C := by
  unfold ReadsBack BinaryReadsBack
  rw [show (binarySkeleton C).gates.length = C.gates.length by simp [binarySkeleton]]
  simp only [binarySkeleton_inputs]

lemma binarySkeleton_tree (n : ℕ) (C : BinaryCircuit) (S E : Finset ℕ) :
    IsTree n (binarySkeleton C) S E ↔ BinaryIsTree n C S E := by
  simp only [IsTree, BinaryIsTree, binarySkeleton_size, binarySkeleton_readsIn,
    binarySkeleton_inputs, isBinOp, binarySkeleton_output, true_and]

end PEqualNP.Outside.L_meta_25806_aux


namespace PEqualNP.Outside.L_meta_25806_aux.Outer

open PEqualNP.MetaComplexity

def run (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op ((run gs x).getD g.left false) ((run gs x).getD g.right false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List BinaryGate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma run_init (gs hs : List BinaryGate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, List.getD_append _ _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have h := run_init [] gs x i (by simpa using hi)
  simpa [run] using h

lemma getD_snoc_length (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp

lemma run_gate (gs : List BinaryGate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op
      (if gs[j].left < x.length + j then (run gs x).getD gs[j].left false else false)
      (if gs[j].right < x.length + j then (run gs x).getD gs[j].right false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have same (k w : ℕ) (hk : k ≤ gs.length) :
        (if w < x.length + k then (run (gs ++ [g]) x).getD w false else false) =
        (if w < x.length + k then (run gs x).getD w false else false) := by
      split_ifs with h
      · exact run_init gs [g] x w (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j _ (by omega), same j _ (by omega),
        run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst j
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ _ le_rfl, same _ _ le_rfl, run_snoc]
      have hlen := run_length gs x
      rw [← hlen]
      rw [getD_snoc_length]
      congr 1
      · split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
      · split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)

def value (C : BinaryCircuit) (x : List Bool) (w : ℕ) : Bool :=
  (run C.gates x).getD w false

def inside (N : ℕ) (reg : Finset ℕ) (w : ℕ) : Prop :=
  N ≤ w ∧ w - N ∈ reg

lemma outside_agree (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (root : value C x cap = value C y cap) :
    ∀ i, i ∉ src → ¬ inside N reg i → value C x i = value C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hs hi
    by_cases low : i < N
    · unfold value
      rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      exact raw i low hs
    by_cases far : N + C.gates.length ≤ i
    · unfold value
      rw [List.getD_eq_default _ _ (by rw [run_length, hx]; exact far),
        List.getD_eq_default _ _ (by rw [run_length, hy]; exact far)]
    let j := i - N
    have jlen : j < C.gates.length := by dsimp [j]; omega
    have idx : N + j = i := by dsimp [j]; omega
    have jr : j ∉ reg := fun h => hi ⟨by omega, h⟩
    have vx := run_gate C.gates x j jlen
    have vy := run_gate C.gates y j jlen
    rw [hx] at vx
    rw [hy] at vy
    change (run C.gates x).getD i false = (run C.gates y).getD i false
    rw [← idx, vx, vy]
    have arg (w : ℕ) (hw : w = C.gates[j].left ∨ w = C.gates[j].right) :
        (if w < N + j then value C x w else false) =
        (if w < N + j then value C y w else false) := by
      split_ifs with h
      · rcases closed j jlen jr w hw with rfl | ⟨hsrc, hreg⟩
        · exact root
        · exact ih w (by omega) hsrc hreg
      · rfl
    exact congrArg₂ (C.gates[j].op)
      (arg _ (Or.inl rfl)) (arg _ (Or.inr rfl))

lemma output_agree (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (visible : C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (root : value C x cap = value C y cap) : C.eval x = C.eval y := by
  change value C x C.output = value C y C.output
  rcases visible with h | ⟨hs, hi⟩
  · simpa only [h] using root
  · exact outside_agree N C src reg cap closed x y hx hy raw root C.output hs hi

lemma unary_factor {α : Type*} (keep : α → Prop) (f g : α → Bool)
    (h : ∀ a, keep a → ∀ b, keep b → f a = f b → g a = g b) :
    ∃ out : Bool → Bool, ∀ a, keep a → g a = out (f a) := by
  classical
  refine ⟨fun b => decide (∃ a, keep a ∧ f a = b ∧ g a = true), ?_⟩
  intro a ha
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hg
    exact ⟨a, ha, rfl, hg⟩
  · rintro ⟨b, hb, hf, hg⟩
    exact (h a ha b hb hf.symm).trans hg

lemma family_factor {α : Type*} (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (visible : C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output))
    (keep : α → Prop) (input : α → List Bool)
    (hlen : ∀ a, keep a → (input a).length = N)
    (raw : ∀ a, keep a → ∀ b, keep b → ∀ i < N, i ∉ src →
      (input a).getD i false = (input b).getD i false) :
    ∃ out : Bool → Bool, ∀ a, keep a → C.eval (input a) = out (value C (input a) cap) := by
  apply unary_factor keep (fun a => value C (input a) cap) (fun a => C.eval (input a))
  intro a ha b hb he
  exact output_agree N C src reg cap closed visible (input a) (input b)
    (hlen a ha) (hlen b hb) (raw a ha b hb) he

end PEqualNP.Outside.L_meta_25806_aux.Outer

namespace PEqualNP.Outside.L_meta_25806_aux.Outer

open PEqualNP.MetaComplexity

def shadow (C : BinaryCircuit) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨C.gates.map (fun g => ⟨.and, [g.left, g.right]⟩), C.output⟩

lemma shadow_size (C : BinaryCircuit) : (shadow C).size = C.size := by
  simp [shadow, PEqualNP.CircuitLowerBounds.Circuit.size, BinaryCircuit.size]

lemma shadow_inputs (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length) :
    (NestedCover.gateAt (shadow C) j).inputs = [C.gates[j].left, C.gates[j].right] := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ (by simpa [shadow] using hj)]
  simp [shadow]

lemma no_outside_read_of_equal_counts (C : PEqualNP.CircuitLowerBounds.Circuit)
    (reg : Finset ℕ) (hreg : reg ⊆ Finset.range C.size) (w j : ℕ)
    (he : NestedCover.readsIn C reg w = NestedCover.readsIn C (Finset.range C.size) w)
    (hj : j < C.size) (hjr : j ∉ reg) : w ∉ (NestedCover.gateAt C j).inputs := by
  intro hw
  have hp := List.count_pos_iff.mpr hw
  have hs : insert j reg ⊆ Finset.range C.size :=
    Finset.insert_subset (Finset.mem_range.mpr hj) hreg
  have hh := Finset.sum_le_sum_of_subset
    (f := fun k => (NestedCover.gateAt C k).inputs.count w) hs
  rw [Finset.sum_insert hjr] at hh
  unfold NestedCover.readsIn at he
  omega

lemma closed_of_counts (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (hreg : reg ⊆ Finset.range C.size)
    (he : ∀ w ∈ src ∪ reg.image (fun j => N + j), w ≠ cap →
      NestedCover.readsIn (shadow C) reg w =
        NestedCover.readsIn (shadow C) (Finset.range (shadow C).size) w) :
    ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w) := by
  intro j hj hjr w hw
  by_cases hcap : w = cap
  · exact Or.inl hcap
  right
  have hn : w ∉ src ∪ reg.image (fun j => N + j) := by
    intro hmem
    have hno := no_outside_read_of_equal_counts (shadow C) reg
      (by simpa only [shadow_size] using hreg) w j (he w hmem hcap)
      (by simpa only [shadow_size, BinaryCircuit.size] using hj) hjr
    apply hno
    rw [shadow_inputs C j hj]
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hw
  constructor
  · intro hs
    exact hn (Finset.mem_union_left _ hs)
  · intro hi
    apply hn
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨w - N, hi.2, Nat.add_sub_of_le hi.1⟩)

lemma visible_of_internal (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (ho : ∀ w ∈ src ∪ reg.image (fun j => N + j), w ≠ cap → C.output ≠ w) :
    C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output) := by
  by_cases hc : C.output = cap
  · exact Or.inl hc
  right
  constructor
  · intro hs
    exact ho C.output (Finset.mem_union_left _ hs) hc rfl
  · intro hi
    apply ho C.output (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨C.output - N, hi.2, Nat.add_sub_of_le hi.1⟩)) hc rfl

lemma tree_family_factor {α : Type*} (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (hreg : reg ⊆ Finset.range C.size)
    (hint : ∀ w ∈ src ∪ reg.image (fun j => N + j), w ≠ cap →
      NestedCover.readsIn (shadow C) reg w = 1 ∧
      NestedCover.readsIn (shadow C) (Finset.range (shadow C).size) w = 1 ∧ C.output ≠ w)
    (keep : α → Prop) (input : α → List Bool)
    (hlen : ∀ a, keep a → (input a).length = N)
    (raw : ∀ a, keep a → ∀ b, keep b → ∀ i < N, i ∉ src →
      (input a).getD i false = (input b).getD i false) :
    ∃ out : Bool → Bool, ∀ a, keep a → C.eval (input a) = out (value C (input a) cap) := by
  apply family_factor N C src reg cap
    (closed_of_counts N C src reg cap hreg ?_)
    (visible_of_internal N C src reg cap ?_) keep input hlen raw
  · intro w hw hc
    exact (hint w hw hc).1.trans (hint w hw hc).2.1.symm
  · intro w hw hc
    exact (hint w hw hc).2.2

end PEqualNP.Outside.L_meta_25806_aux.Outer


namespace PEqualNP.Outside.L_meta_25806_aux.Causal

lemma outside_agree
    (N s top cap : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (backL : ∀ j < s, left j < N + j)
    (backR : ∀ j < s, right j < N + j)
    (evalV : ∀ j < s, V (N + j) = op j (V (left j)) (V (right j)))
    (evalW : ∀ j < s, W (N + j) = op j (W (left j)) (W (right j)))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (exterior : ∀ j < s, ¬ region (N + j) →
      (¬ src (left j) ∧ (region (left j) → left j = N + top)) ∧
      (¬ src (right j) ∧ (region (right j) → right j = N + top)))
    (top_eq : N + top < cap → V (N + top) = W (N + top)) :
    ∀ i < cap, ¬ src i → ¬ region i → V i = W i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hs hr
    by_cases low : i < N
    · exact raw i low hs
    by_cases far : N + s ≤ i
    · exact (pastV i far).trans (pastW i far).symm
    have hj : i - N < s := by omega
    have idx : N + (i - N) = i := by omega
    have cut := exterior (i - N) hj (by simpa only [idx] using hr)
    have eqL : V (left (i - N)) = W (left (i - N)) := by
      have lt : left (i - N) < i := by simpa only [idx] using backL (i - N) hj
      by_cases hin : region (left (i - N))
      · have he := cut.1.2 hin
        rw [he]
        exact top_eq (by omega)
      · exact ih _ lt (by omega) cut.1.1 hin
    have eqR : V (right (i - N)) = W (right (i - N)) := by
      have lt : right (i - N) < i := by simpa only [idx] using backR (i - N) hj
      by_cases hin : region (right (i - N))
      · have he := cut.2.2 hin
        rw [he]
        exact top_eq (by omega)
      · exact ih _ lt (by omega) cut.2.1 hin
    have v := evalV (i - N) hj
    have w := evalW (i - N) hj
    rw [idx] at v w
    rw [v, w, eqL, eqR]

lemma boundary_agree
    (N s top : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (backL : ∀ j < s, left j < N + j)
    (backR : ∀ j < s, right j < N + j)
    (evalV : ∀ j < s, V (N + j) = op j (V (left j)) (V (right j)))
    (evalW : ∀ j < s, W (N + j) = op j (W (left j)) (W (right j)))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (exterior : ∀ j < s, ¬ region (N + j) →
      (¬ src (left j) ∧ (region (left j) → left j = N + top)) ∧
      (¬ src (right j) ∧ (region (right j) → right j = N + top)))
    (w : Nat) (earlier : w < N + top) (notSrc : ¬ src w) (notRegion : ¬ region w) :
    V w = W w := by
  exact outside_agree N s top (N + top) left right op V W src region
    backL backR evalV evalW pastV pastW raw exterior (by omega) w earlier notSrc notRegion


lemma outside_agree_cut
    (N s root limit : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (evalV : ∀ j < s, V (N + j) = op j
      (if left j < N+j then V (left j) else false)
      (if right j < N+j then V (right j) else false))
    (evalW : ∀ j < s, W (N + j) = op j
      (if left j < N+j then W (left j) else false)
      (if right j < N+j then W (right j) else false))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (closed : ∀ j < s, ¬ region (N+j) →
      (left j = root ∨ (¬ src (left j) ∧ ¬ region (left j))) ∧
      (right j = root ∨ (¬ src (right j) ∧ ¬ region (right j))))
    (root_eq : root < limit → V root = W root) :
    ∀ i < limit, ¬ src i → ¬ region i → V i = W i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hs hr
    by_cases low : i < N
    · exact raw i low hs
    by_cases far : N+s ≤ i
    · exact (pastV i far).trans (pastW i far).symm
    have hj : i-N < s := by omega
    have idx : N+(i-N) = i := by omega
    have cut := closed (i-N) hj (by simpa only [idx] using hr)
    have arg (w : Nat) (hw : w = root ∨ (¬ src w ∧ ¬ region w)) :
        (if w < i then V w else false) = (if w < i then W w else false) := by
      split <;> rename_i h
      · rcases hw with rfl | ⟨hsrc,hreg⟩
        · exact root_eq (by omega)
        · exact ih w h (by omega) hsrc hreg
      · rfl
    have v := evalV (i-N) hj
    have w := evalW (i-N) hj
    rw [idx] at v w
    rw [v,w]
    rw [arg _ cut.1, arg _ cut.2]

lemma boundary_agree_cut
    (N s root : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (evalV : ∀ j < s, V (N + j) = op j
      (if left j < N+j then V (left j) else false)
      (if right j < N+j then V (right j) else false))
    (evalW : ∀ j < s, W (N + j) = op j
      (if left j < N+j then W (left j) else false)
      (if right j < N+j then W (right j) else false))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (closed : ∀ j < s, ¬ region (N+j) →
      (left j = root ∨ (¬ src (left j) ∧ ¬ region (left j))) ∧
      (right j = root ∨ (¬ src (right j) ∧ ¬ region (right j))))
    (w : Nat) (earlier : w < root) (notSrc : ¬ src w) (notRegion : ¬ region w) :
    V w = W w := by
  exact outside_agree_cut N s root root left right op V W src region
    evalV evalW pastV pastW raw closed (by omega) w earlier notSrc notRegion

end PEqualNP.Outside.L_meta_25806_aux.Causal


namespace PEqualNP.Outside.L_meta_25806_aux.Causal

lemma oneHot_getD_ne {n : Nat} (u : Fin n) (i : Nat) (hi : i ≠ u.val) :
    (List.ofFn (fun k : Fin n => decide (k = u))).getD i false = false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma oneHot_left_blank {n : Nat} (u : Fin n) (right : List Bool) (i : Nat)
    (hi : i ≠ u.val) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++ right).getD i false =
      (List.replicate n false ++ right).getD i false := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa), List.getD_append _ _ _ _ (by simpa)]
    rw [oneHot_getD_ne u i hi, List.getD_replicate false h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_ofFn, List.length_replicate]

lemma oneHot_right_blank {n m : Nat} (left : List Bool) (hlen : left.length = n)
    (v : Fin m) (i : Nat) (hi : i ≠ n + v.val) :
    (left ++ List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
      (left ++ List.replicate m false).getD i false := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]
    rw [oneHot_getD_ne v (i-n) (by omega)]
    simp [List.getD_eq_getElem?_getD]

lemma oneEach_left_raw {n m : Nat} (u : Fin n) (v : Fin m)
    (src : Nat → Prop) (hu : src u.val) (i : Nat) (hi : ¬ src i) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
    (List.replicate n false ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false := by
  apply oneHot_left_blank
  intro he
  exact hi (he.symm ▸ hu)

lemma oneEach_right_raw {n m : Nat} (u : Fin n) (v : Fin m)
    (src : Nat → Prop) (hv : src (n + v.val)) (i : Nat) (hi : ¬ src i) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.replicate m false).getD i false := by
  apply oneHot_right_blank (n := n) (m := m) _ (by simp) v i
  intro he
  exact hi (he.symm ▸ hv)

lemma left_blank_length {m : Nat} (n : Nat) (v : Fin m) :
    (List.replicate n false ++ List.ofFn (fun k : Fin m => decide (k = v))).length =
      n + m := by simp

lemma right_blank_length {n : Nat} (m : Nat) (u : Fin n) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++ List.replicate m false).length =
      n + m := by simp

end PEqualNP.Outside.L_meta_25806_aux.Causal


namespace PEqualNP.Outside.L_meta_25806_aux.Outer

open PEqualNP.MetaComplexity

lemma boundary_value_agree (N : Nat) (C : BinaryCircuit) (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src) (notRegion : ¬ inside N reg w) :
    value C x w = value C y w := by
  let gate (j : Nat) : BinaryGate := C.gates.getD j ⟨fun _ _ => false, 0, 0⟩
  have gate_eq (j : Nat) (hj : j < C.gates.length) : gate j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  refine PEqualNP.Outside.L_meta_25806_aux.Causal.boundary_agree_cut
    N C.gates.length cap (fun j => (gate j).left) (fun j => (gate j).right)
    (fun j => (gate j).op) (value C x) (value C y)
    (fun i => i ∈ src) (inside N reg) ?_ ?_ ?_ ?_ ?_ ?_
    w earlier notSrc notRegion
  · intro j hj
    have h := run_gate C.gates x j hj
    rw [hx] at h
    simpa only [gate_eq j hj, value] using h
  · intro j hj
    have h := run_gate C.gates y j hj
    rw [hy] at h
    simpa only [gate_eq j hj, value] using h
  · intro i hi
    exact List.getD_eq_default _ _ (by rw [run_length, hx]; exact hi)
  · intro i hi
    exact List.getD_eq_default _ _ (by rw [run_length, hy]; exact hi)
  · intro i hi hs
    change (run C.gates x).getD i false = (run C.gates y).getD i false
    rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    exact raw i hi hs
  · intro j hj hr
    have hjr : j ∉ reg := by simpa [inside] using hr
    rw [gate_eq j hj]
    exact ⟨closed j hj hjr _ (Or.inl rfl), closed j hj hjr _ (Or.inr rfl)⟩

lemma oneEach_boundary_left {n m : Nat} (C : BinaryCircuit)
    (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside (n+m) reg w))
    (u : Fin n) (v : Fin m) (hu : u.val ∈ src)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src)
    (notRegion : ¬ inside (n+m) reg w) :
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.ofFn (fun k : Fin m => decide (k=v))) w =
    value C (List.replicate n false ++
      List.ofFn (fun k : Fin m => decide (k=v))) w := by
  apply boundary_value_agree (n+m) C src reg cap closed _ _ (by simp) (by simp)
    ?_ w earlier notSrc notRegion
  intro i hi hsrc
  exact PEqualNP.Outside.L_meta_25806_aux.Causal.oneEach_left_raw u v
    (fun k => k ∈ src) hu i hsrc

lemma oneEach_boundary_right {n m : Nat} (C : BinaryCircuit)
    (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside (n+m) reg w))
    (u : Fin n) (v : Fin m) (hv : n+v.val ∈ src)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src)
    (notRegion : ¬ inside (n+m) reg w) :
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.ofFn (fun k : Fin m => decide (k=v))) w =
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.replicate m false) w := by
  apply boundary_value_agree (n+m) C src reg cap closed _ _ (by simp) (by simp)
    ?_ w earlier notSrc notRegion
  intro i hi hsrc
  exact PEqualNP.Outside.L_meta_25806_aux.Causal.oneEach_right_raw u v
    (fun k => k ∈ src) hv i hsrc

end PEqualNP.Outside.L_meta_25806_aux.Outer

namespace PEqualNP.Outside.L_meta_25806_aux.Semantics


lemma region_interior_congr (N : ℕ) (R S E : Finset ℕ)
    (left right : ℕ → ℕ) (op : ℕ → Bool → Bool → Bool)
    (v w : ℕ → Bool)
    (hleft : ∀ j ∈ R, left j < N + j)
    (hright : ∀ j ∈ R, right j < N + j)
    (hclosed : ∀ j ∈ R, ∀ i, i = left j ∨ i = right j →
      i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hS : ∀ i ∈ S, v i = w i)
    (hE : ∀ i ∈ E, v i = w i)
    (hv : ∀ j ∈ R, v (N + j) = op j (v (left j)) (v (right j)))
    (hw : ∀ j ∈ R, w (N + j) = op j (w (left j)) (w (right j))) :
    ∀ j ∈ R, v (N + j) = w (N + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hwire (i : ℕ) (hi : i < N + j)
        (hc : i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E) : v i = w i := by
      rcases hc with hs | ⟨k, hk, rfl⟩ | he
      · exact hS i hs
      · exact ih k (by omega) hk
      · exact hE i he
    rw [hv j hj, hw j hj]
    rw [hwire (left j) (hleft j hj) (hclosed j hj _ (Or.inl rfl)),
      hwire (right j) (hright j hj) (hclosed j hj _ (Or.inr rfl))]

lemma region_cap_congr (N : ℕ) (R S E : Finset ℕ)
    (left right : ℕ → ℕ) (op : ℕ → Bool → Bool → Bool)
    (v w : ℕ → Bool)
    (hleft : ∀ j ∈ R, left j < N + j)
    (hright : ∀ j ∈ R, right j < N + j)
    (hclosed : ∀ j ∈ R, ∀ i, i = left j ∨ i = right j →
      i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hS : ∀ i ∈ S, v i = w i)
    (hE : ∀ i ∈ E, v i = w i)
    (hv : ∀ j ∈ R, v (N + j) = op j (v (left j)) (v (right j)))
    (hw : ∀ j ∈ R, w (N + j) = op j (w (left j)) (w (right j)))
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j) :
    v root = w root := by
  rcases hroot with hs | ⟨j, hj, rfl⟩
  · exact hS root hs
  · exact region_interior_congr N R S E left right op v w
      hleft hright hclosed hS hE hv hw j hj

lemma bool_fiber_factor {X : Type*} (f : X → Bool) (t : X → Bool)
    (h : ∀ x y, t x = t y → f x = f y) :
    ∃ q : Bool → Bool, ∀ x, f x = q (t x) := by
  classical
  let q : Bool → Bool := fun b =>
    if hb : ∃ x, t x = b then f (Classical.choose hb) else false
  refine ⟨q, ?_⟩
  intro x
  have hx : ∃ y, t y = t x := ⟨x, rfl⟩
  simp only [q, dite_eq_left hx]
  exact h x (Classical.choose hx) (Classical.choose_spec hx).symm

lemma binary_region_congr (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hraw : ∀ i ∈ S, x.getD i false = y.getD i false)
    (hboundary : ∀ i ∈ E, PEqualNP.Outside.L_meta_25806_aux.Outer.value C x i = PEqualNP.Outside.L_meta_25806_aux.Outer.value C y i)
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j) :
    PEqualNP.Outside.L_meta_25806_aux.Outer.value C x root = PEqualNP.Outside.L_meta_25806_aux.Outer.value C y root := by
  let left : ℕ → ℕ := fun j => if hj : j < C.gates.length then C.gates[j].left else 0
  let right : ℕ → ℕ := fun j => if hj : j < C.gates.length then C.gates[j].right else 0
  let op : ℕ → Bool → Bool → Bool := fun j =>
    if hj : j < C.gates.length then C.gates[j].op else fun _ _ => false
  have hlen (j : ℕ) (hj : j ∈ R) : j < C.gates.length := Finset.mem_range.mp (hR hj)
  apply region_cap_congr N R S E left right op
    (PEqualNP.Outside.L_meta_25806_aux.Outer.value C x) (PEqualNP.Outside.L_meta_25806_aux.Outer.value C y) ?_ ?_ ?_ ?_
    hboundary ?_ ?_ root hroot
  · intro j hj
    simpa [left, hlen j hj] using (hback j (hlen j hj) hj).1
  · intro j hj
    simpa [right, hlen j hj] using (hback j (hlen j hj) hj).2
  · intro j hj i hi
    apply hclosed j (hlen j hj) hj i
    simpa [left, right, hlen j hj] using hi
  · intro i hi
    have hil : i < N := Finset.mem_range.mp (hS hi)
    unfold PEqualNP.Outside.L_meta_25806_aux.Outer.value
    rw [PEqualNP.Outside.L_meta_25806_aux.Outer.run_input _ _ _ (by omega),
      PEqualNP.Outside.L_meta_25806_aux.Outer.run_input _ _ _ (by omega)]
    exact hraw i hi
  · intro j hj
    have h := PEqualNP.Outside.L_meta_25806_aux.Outer.run_gate C.gates x j (hlen j hj)
    rw [hx] at h
    simpa [PEqualNP.Outside.L_meta_25806_aux.Outer.value, left, right, op, hlen j hj,
      (hback j (hlen j hj) hj).1, (hback j (hlen j hj) hj).2] using h
  · intro j hj
    have h := PEqualNP.Outside.L_meta_25806_aux.Outer.run_gate C.gates y j (hlen j hj)
    rw [hy] at h
    simpa [PEqualNP.Outside.L_meta_25806_aux.Outer.value, left, right, op, hlen j hj,
      (hback j (hlen j hj) hj).1, (hback j (hlen j hj) hj).2] using h

lemma binary_region_family_factor {X : Type*}
    (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j)
    (keep : X → Prop) (input : X → List Bool) (t : X → Bool)
    (hlen : ∀ a, keep a → (input a).length = N)
    (hraw : ∀ a, keep a → ∀ b, keep b → ∀ i ∈ S,
      (input a).getD i false = (input b).getD i false)
    (hboundary : ∀ a, keep a → ∀ b, keep b → t a = t b → ∀ i ∈ E,
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a) i = PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input b) i) :
    ∃ q : Bool → Bool, ∀ a, keep a →
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a) root = q (t a) := by
  obtain ⟨q, hq⟩ := bool_fiber_factor
    (fun a : {a : X // keep a} => PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a.val) root)
    (fun a => t a.val) (by
      intro a b hab
      exact binary_region_congr N C R S E hR hS hback hclosed
        (input a.val) (input b.val) (hlen a.val a.property) (hlen b.val b.property)
        (hraw a.val a.property b.val b.property)
        (hboundary a.val a.property b.val b.property hab) root hroot)
  exact ⟨q, fun a ha => hq ⟨a, ha⟩⟩

def bankInputRight {n : ℕ} (fixed : List Bool) (v : Fin n) : List Bool :=
  fixed ++ List.ofFn (fun j : Fin n => decide (j = v))

def bankInputLeft {n : ℕ} (u : Fin n) (fixed : List Bool) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ fixed

lemma bank_input_right_raw_agree {n : ℕ} (fixed : List Bool) (hlen : fixed.length = n)
    (S : Finset ℕ) (v w : Fin n) (hv : n + v.val ∉ S) (hw : n + w.val ∉ S) :
    ∀ i ∈ S, (bankInputRight fixed v).getD i false =
      (bankInputRight fixed w).getD i false := by
  intro i hi
  simp only [bankInputRight, List.getD_eq_getElem?_getD, List.getElem?_append, hlen]
  by_cases h : i < n
  · simp [h]
  · by_cases h' : i - n < n
    · have h₁ : (⟨i - n, h'⟩ : Fin n) ≠ v := by
        intro he
        apply hv
        have he' := congrArg Fin.val he
        have heq : n + v.val = i := by dsimp at he'; omega
        simpa [heq] using hi
      have h₂ : (⟨i - n, h'⟩ : Fin n) ≠ w := by
        intro he
        apply hw
        have he' := congrArg Fin.val he
        have heq : n + w.val = i := by dsimp at he'; omega
        simpa [heq] using hi
      simp [h, h', h₁, h₂]
    · simp [h, h']

lemma bank_input_left_raw_agree {n : ℕ} (fixed : List Bool)
    (S : Finset ℕ) (u w : Fin n) (hu : u.val ∉ S) (hw : w.val ∉ S) :
    ∀ i ∈ S, (bankInputLeft u fixed).getD i false =
      (bankInputLeft w fixed).getD i false := by
  intro i hi
  simp only [bankInputLeft, List.getD_eq_getElem?_getD,
    List.getElem?_append, List.length_ofFn]
  by_cases h : i < n
  · have h₁ : (⟨i, h⟩ : Fin n) ≠ u := by
      intro he
      apply hu
      simpa [← congrArg Fin.val he] using hi
    have h₂ : (⟨i, h⟩ : Fin n) ≠ w := by
      intro he
      apply hw
      simpa [← congrArg Fin.val he] using hi
    simp [h, h₁, h₂]
  · simp [h]

lemma binary_region_fixed_left_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (cap : ℕ) (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (fixed : List Bool) (hlen : fixed.length = n) (t : Fin n → Bool)
    (hboundary : ∀ v, n + v.val ∉ S → ∀ w, n + w.val ∉ S →
      t v = t w → ∀ i ∈ E,
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputRight fixed v) i =
        PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputRight fixed w) i) :
    ∃ q : Bool → Bool, ∀ v, n + v.val ∉ S →
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputRight fixed v) cap = q (t v) := by
  apply binary_region_family_factor (2 * n) C R S E hR hS hback hclosed cap hcap
    (fun v : Fin n => n + v.val ∉ S) (bankInputRight fixed) t
  · intro v hv
    simp [bankInputRight, hlen]
    omega
  · intro v hv w hw
    exact bank_input_right_raw_agree fixed hlen S v w hv hw
  · exact hboundary

lemma binary_region_fixed_right_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (cap : ℕ) (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (fixed : List Bool) (hlen : fixed.length = n) (t : Fin n → Bool)
    (hboundary : ∀ u, u.val ∉ S → ∀ w, w.val ∉ S →
      t u = t w → ∀ i ∈ E,
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputLeft u fixed) i =
        PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputLeft w fixed) i) :
    ∃ q : Bool → Bool, ∀ u, u.val ∉ S →
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (bankInputLeft u fixed) cap = q (t u) := by
  apply binary_region_family_factor (2 * n) C R S E hR hS hback hclosed cap hcap
    (fun u : Fin n => u.val ∉ S) (fun u => bankInputLeft u fixed) t
  · intro u hu
    simp [bankInputLeft, hlen]
    omega
  · intro u hu w hw
    exact bank_input_left_raw_agree fixed S u w hu hw
  · exact hboundary

lemma binary_region_tensor_factor {A X : Type*}
    (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (cap : ℕ) (K : A → Prop) (P : X → Prop) (input : A → X → List Bool)
    (a₀ : A) (ha₀ : K a₀)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = N + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside N R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside N R C.output))
    (hE : E.card ≤ 1)
    (hlen : ∀ a, K a → ∀ x, P x → (input a x).length = N)
    (rawInside : ∀ a, K a → ∀ x, P x → ∀ y, P y → ∀ i ∈ S,
      (input a x).getD i false = (input a y).getD i false)
    (rawOutside : ∀ x, P x → ∀ a, K a → ∀ b, K b → ∀ i < N, i ∉ S →
      (input a x).getD i false = (input b x).getD i false)
    (boundaryCommon : ∀ a, K a → ∀ x, P x → ∀ e ∈ E,
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a x) e =
        PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a₀ x) e) :
    ∃ t : X → Bool, ∃ q : A → Bool → Bool, ∃ U : X → Bool → Bool,
      ∀ a, K a → ∀ x, P x → C.eval (input a x) = U x (q a (t x)) := by
  classical
  obtain ⟨port, hport⟩ : ∃ port : ℕ, ∀ e ∈ E, e = port := by
    by_cases hnonempty : E.Nonempty
    · obtain ⟨port, hp⟩ := hnonempty
      exact ⟨port, fun e he => Finset.card_le_one.mp hE e he port hp⟩
    · exact ⟨0, fun e he => False.elim (hnonempty ⟨e, he⟩)⟩
  let t : X → Bool := fun x => PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a₀ x) port
  have inner : ∀ a, ∃ q : Bool → Bool, ∀ x, K a → P x →
      PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a x) cap = q (t x) := by
    intro a
    by_cases ha : K a
    · obtain ⟨q, hq⟩ := binary_region_family_factor N C R S E hR hS hback
        innerClosed cap hcap P (input a) t (hlen a ha) (rawInside a ha) (by
          intro x hx y hy hxy e he
          rw [boundaryCommon a ha x hx e he, boundaryCommon a ha y hy e he,
            hport e he]
          exact hxy)
      exact ⟨q, fun x _ hx => hq x hx⟩
    · exact ⟨fun _ => false, fun x hk _ => False.elim (ha hk)⟩
  choose q hq using inner
  have outer : ∀ x, ∃ U : Bool → Bool, ∀ a, K a → P x →
      C.eval (input a x) = U (PEqualNP.Outside.L_meta_25806_aux.Outer.value C (input a x) cap) := by
    intro x
    by_cases hx : P x
    · obtain ⟨U, hU⟩ := PEqualNP.Outside.L_meta_25806_aux.Outer.family_factor N C S R cap outerClosed visible
        K (fun a => input a x) (fun a ha => hlen a ha x hx) (rawOutside x hx)
      exact ⟨U, fun a ha _ => hU a ha⟩
    · exact ⟨fun _ => false, fun a _ hp => False.elim (hx hp)⟩
  choose U hU using outer
  refine ⟨t, q, U, ?_⟩
  intro a ha x hx
  rw [hU x a ha hx, hq a x ha hx]


def blankLeft {n : ℕ} (v : Fin n) : List Bool :=
  List.replicate n false ++ List.ofFn (fun k : Fin n => decide (k = v))

def blankRight {n : ℕ} (u : Fin n) : List Bool :=
  List.ofFn (fun k : Fin n => decide (k = u)) ++ List.replicate n false

lemma row_region_tensor_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ) (cap : ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside (2 * n) R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside (2 * n) R C.output))
    (hE : E.card ≤ 1) (post : Bool → Bool)
    (boundaryCommon : ∀ u : Fin n, u.val ∈ S → ∀ v : Fin n, n + v.val ∉ S →
      ∀ e ∈ E, PEqualNP.Outside.L_meta_25806_aux.Outer.value C (PEqualNP.Represents.oneEach u v) e =
        PEqualNP.Outside.L_meta_25806_aux.Outer.value C (blankLeft v) e) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ v, n + v.val ∉ S → post (C.eval (blankLeft v)) = U v (q₀ (t v))) ∧
      (∀ u, u.val ∈ S → ∀ v, n + v.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U v (q u (t v))) := by
  classical
  let K : Option (Fin n) → Prop := fun a => match a with
    | none => True
    | some u => u.val ∈ S
  let fixed : Option (Fin n) → List Bool := fun a => match a with
    | none => List.replicate n false
    | some u => List.ofFn (fun k : Fin n => decide (k = u))
  let input : Option (Fin n) → Fin n → List Bool := fun a v => bankInputRight (fixed a) v
  have fixed_length (a : Option (Fin n)) : (fixed a).length = n := by
    cases a <;> simp [fixed]
  have raw_blank (a : Option (Fin n)) (ha : K a) (v : Fin n) (i : ℕ) (hi : i ∉ S) :
      (input a v).getD i false = (blankLeft v).getD i false := by
    cases a with
    | none => rfl
    | some u =>
      exact PEqualNP.Outside.L_meta_25806_aux.Causal.oneEach_left_raw
        u v (fun j => j ∈ S) ha i hi
  obtain ⟨t, q, U, hfactor⟩ := binary_region_tensor_factor (2 * n) C R S E cap
    K (fun v : Fin n => n + v.val ∉ S) input none trivial hR hS hback innerClosed
    hcap outerClosed visible hE
    (by intro a ha v hv; simp [input, bankInputRight, fixed_length, two_mul])
    (by
      intro a ha v hv w hw
      exact bank_input_right_raw_agree (fixed a) (fixed_length a) S v w hv hw)
    (by
      intro v hv a ha b hb i hi his
      exact (raw_blank a ha v i his).trans (raw_blank b hb v i his).symm)
    (by
      intro a ha v hv e he
      cases a with
      | none => rfl
      | some u => exact boundaryCommon u ha v hv e he)
  refine ⟨t, q none, (fun u => q (some u)), (fun v b => post (U v b)), ?_, ?_⟩
  · intro v hv
    exact congrArg post (hfactor none trivial v hv)
  · intro u hu v hv
    exact congrArg post (hfactor (some u) hu v hv)

lemma col_region_tensor_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ) (cap : ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside (2 * n) R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside (2 * n) R C.output))
    (hE : E.card ≤ 1) (post : Bool → Bool)
    (boundaryCommon : ∀ v : Fin n, n + v.val ∈ S → ∀ u : Fin n, u.val ∉ S →
      ∀ e ∈ E, PEqualNP.Outside.L_meta_25806_aux.Outer.value C (PEqualNP.Represents.oneEach u v) e =
        PEqualNP.Outside.L_meta_25806_aux.Outer.value C (blankRight u) e) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ u, u.val ∉ S → post (C.eval (blankRight u)) = U u (q₀ (t u))) ∧
      (∀ v, n + v.val ∈ S → ∀ u, u.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U u (q v (t u))) := by
  classical
  let K : Option (Fin n) → Prop := fun a => match a with
    | none => True
    | some v => n + v.val ∈ S
  let fixed : Option (Fin n) → List Bool := fun a => match a with
    | none => List.replicate n false
    | some v => List.ofFn (fun k : Fin n => decide (k = v))
  let input : Option (Fin n) → Fin n → List Bool := fun a u => bankInputLeft u (fixed a)
  have fixed_length (a : Option (Fin n)) : (fixed a).length = n := by
    cases a <;> simp [fixed]
  have raw_blank (a : Option (Fin n)) (ha : K a) (u : Fin n) (i : ℕ) (hi : i ∉ S) :
      (input a u).getD i false = (blankRight u).getD i false := by
    cases a with
    | none => rfl
    | some v =>
      exact PEqualNP.Outside.L_meta_25806_aux.Causal.oneEach_right_raw
        u v (fun j => j ∈ S) ha i hi
  obtain ⟨t, q, U, hfactor⟩ := binary_region_tensor_factor (2 * n) C R S E cap
    K (fun u : Fin n => u.val ∉ S) input none trivial hR hS hback innerClosed
    hcap outerClosed visible hE
    (by intro a ha u hu; simp [input, bankInputLeft, fixed_length, two_mul])
    (by
      intro a ha u hu w hw
      exact bank_input_left_raw_agree (fixed a) S u w hu hw)
    (by
      intro u hu a ha b hb i hi his
      exact (raw_blank a ha u i his).trans (raw_blank b hb u i his).symm)
    (by
      intro a ha u hu e he
      cases a with
      | none => rfl
      | some v => exact boundaryCommon v ha u hu e he)
  refine ⟨t, q none, (fun v => q (some v)), (fun u b => post (U u b)), ?_, ?_⟩
  · intro u hu
    exact congrArg post (hfactor none trivial u hu)
  · intro v hv u hu
    exact congrArg post (hfactor (some v) hv u hu)

end PEqualNP.Outside.L_meta_25806_aux.Semantics
namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.MetaComplexity Semantics

lemma shadow_binary_reads (C : BinaryCircuit) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) (w : ℕ) :
    NestedCover.readsIn (PEqualNP.Outside.L_meta_25806_aux.Outer.shadow C) G w = binaryReadsIn C G w := by
  unfold NestedCover.readsIn binaryReadsIn
  apply Finset.sum_congr rfl
  intro j hj
  have hlen : j < C.gates.length := Finset.mem_range.mp (hG hj)
  rw [PEqualNP.Outside.L_meta_25806_aux.Outer.shadow_inputs C j hlen, binaryInputs_at C j hlen]

lemma binary_tree_topology (N : ℕ) (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree N C S E) (hback : BinaryReadsBack N C) :
    ∃ (R : Finset ℕ) (cap : ℕ),
      R ⊆ Finset.range C.gates.length ∧
      (cap ∈ S ∨ ∃ j ∈ R, cap = N + j) ∧
      (∀ j (hj : j < C.gates.length), j ∈ R →
        C.gates[j].left < N + j ∧ C.gates[j].right < N + j) ∧
      (∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
        i = C.gates[j].left ∨ i = C.gates[j].right →
          i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E) ∧
      (∀ j (hj : j < C.gates.length), j ∉ R → ∀ w,
        w = C.gates[j].left ∨ w = C.gates[j].right →
          w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside N R w)) ∧
      (C.output = cap ∨ (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside N R C.output)) ∧
      (∀ e ∈ E, e < cap ∧ e ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25806_aux.Outer.inside N R e) := by
  classical
  obtain ⟨R, cap, hR, hcap, hcapread, hE, hin, hint⟩ := htree
  refine ⟨R, cap, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp hcap with hs | hr
    · exact Or.inl hs
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hr
      exact Or.inr ⟨j, hj, he.symm⟩
  · intro j hj hreg
    constructor
    · apply hback j hj
      simp [binaryInputs_at C j hj]
    · apply hback j hj
      simp [binaryInputs_at C j hj]
  · intro j hj hreg i hi
    have hm : i ∈ binaryInputs C j := by
      simpa [binaryInputs_at C j hj] using hi
    rcases (hin j hreg).2 i hm with hw | he
    · rcases Finset.mem_union.mp hw with hs | hr
      · exact Or.inl hs
      · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inl ⟨k, hk, he.symm⟩)
    · exact Or.inr (Or.inr he)
  · apply PEqualNP.Outside.L_meta_25806_aux.Outer.closed_of_counts N C S R cap hR
    intro w hw hne
    rw [PEqualNP.Outside.L_meta_25806_aux.Outer.shadow_size,
      shadow_binary_reads C R hR w,
      shadow_binary_reads C (Finset.range C.size) (Finset.Subset.refl _) w]
    exact (hint w hw hne).1.trans (hint w hw hne).2.1.symm
  · apply PEqualNP.Outside.L_meta_25806_aux.Outer.visible_of_internal N C S R cap
    intro w hw hne
    exact (hint w hw hne).2.2
  · intro e he
    have hb := hE e he
    refine ⟨hb.2.1, ?_, ?_⟩
    · intro hs
      exact hb.1 (Finset.mem_union_left _ hs)
    · intro hr
      apply hb.1
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨e - N, hr.2, Nat.add_sub_of_le hr.1⟩)

lemma binary_tree_row_factor {n : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree (2 * n) C S E) (hback : BinaryReadsBack (2 * n) C)
    (hS : S ⊆ Finset.range (2 * n)) (hE : E.card ≤ 1) (post : Bool → Bool) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ v, n + v.val ∉ S → post (C.eval (blankLeft v)) = U v (q₀ (t v))) ∧
      (∀ u, u.val ∈ S → ∀ v, n + v.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U v (q u (t v))) := by
  obtain ⟨R, cap, hR, hcap, hbk, hin, hout, hvis, hbound⟩ :=
    binary_tree_topology (2 * n) C S E htree hback
  apply row_region_tensor_factor C R S E cap hR hS hbk hin hcap hout hvis hE post
  intro u hu v hv e he
  have hb := hbound e he
  have h := PEqualNP.Outside.L_meta_25806_aux.Outer.oneEach_boundary_left C S R cap
    (by simpa only [two_mul] using hout) u v hu e hb.1 hb.2.1
    (by simpa only [two_mul] using hb.2.2)
  exact h

lemma binary_tree_col_factor {n : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree (2 * n) C S E) (hback : BinaryReadsBack (2 * n) C)
    (hS : S ⊆ Finset.range (2 * n)) (hE : E.card ≤ 1) (post : Bool → Bool) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ u, u.val ∉ S → post (C.eval (blankRight u)) = U u (q₀ (t u))) ∧
      (∀ v, n + v.val ∈ S → ∀ u, u.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U u (q v (t u))) := by
  obtain ⟨R, cap, hR, hcap, hbk, hin, hout, hvis, hbound⟩ :=
    binary_tree_topology (2 * n) C S E htree hback
  apply col_region_tensor_factor C R S E cap hR hS hbk hin hcap hout hvis hE post
  intro v hv u hu e he
  have hb := hbound e he
  have h := PEqualNP.Outside.L_meta_25806_aux.Outer.oneEach_boundary_right C S R cap
    (by simpa only [two_mul] using hout) u v hv e hb.1 hb.2.1
    (by simpa only [two_mul] using hb.2.2)
  exact h

end PEqualNP.Outside.L_meta_25806_aux


namespace PEqualNP.Outside.L_meta_25806_aux

lemma bool_context_xor (f : Bool → Bool) (a b : Bool) :
    Bool.xor (f a) (f b) = (Bool.xor a b && Bool.xor (f false) (f true)) := by
  cases a <;> cases b <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma one_boundary_missing : ∀ (f₀ f₁ f₂ : Bool → Bool),
    ∃ p q : Bool, (p = true ∨ q = true) ∧
      ∀ (t : Bool) (c : Bool → Bool),
        ¬ (Bool.xor (c (f₁ t)) (c (f₀ t)) = p ∧
          Bool.xor (c (f₂ t)) (c (f₀ t)) = q) := by
  decide +kernel

lemma factored_triple_missing {α β : Type*} (A : α → β → Bool)
    (a b c : α) (S : Set β) (f₀ f₁ f₂ : Bool → Bool)
    (t : β → Bool) (out : β → Bool → Bool)
    (ha : ∀ x ∉ S, A a x = out x (f₀ (t x)))
    (hb : ∀ x ∉ S, A b x = out x (f₁ (t x)))
    (hc : ∀ x ∉ S, A c x = out x (f₂ (t x))) :
    ∃ p q : Bool, (p = true ∨ q = true) ∧
      ∀ x ∉ S, ¬ (Bool.xor (A b x) (A a x) = p ∧
        Bool.xor (A c x) (A a x) = q) := by
  obtain ⟨p, q, nonzero, missing⟩ := one_boundary_missing f₀ f₁ f₂
  refine ⟨p, q, nonzero, ?_⟩
  intro x hx
  rw [ha x hx, hb x hx, hc x hx]
  exact missing (t x) (out x)

lemma factored_pair_missing {α β : Type*} (A : α → β → Bool)
    (a b : α) (H : β → Bool) (S : Set β) (f₀ f₁ f₂ : Bool → Bool)
    (t : β → Bool) (out : β → Bool → Bool)
    (hH : ∀ x ∉ S, H x = out x (f₀ (t x)))
    (ha : ∀ x ∉ S, A a x = out x (f₁ (t x)))
    (hb : ∀ x ∉ S, A b x = out x (f₂ (t x))) :
    ∃ p q : Bool, (p = true ∨ q = true) ∧
      ∀ x ∉ S, ¬ (Bool.xor (A a x) (H x) = p ∧
        Bool.xor (A b x) (H x) = q) := by
  obtain ⟨p, q, nonzero, missing⟩ := one_boundary_missing f₀ f₁ f₂
  refine ⟨p, q, nonzero, ?_⟩
  intro x hx
  rw [hH x hx, ha x hx, hb x hx]
  exact missing (t x) (out x)

end PEqualNP.Outside.L_meta_25806_aux
namespace PEqualNP.Outside.L_meta_25806_aux

lemma factored_family_cap {n : ℕ} (F A : Fin n → Fin n → Bool)
    (names exceptions : Finset (Fin n)) (hn : 128 ≤ n)
    (horth : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F a x ≠ F b x)).card = n)
    (hgood : ∀ a ∈ names,
      16 * (Finset.univ.filter (fun x => F a x ≠ A a x)).card ≤ n)
    (hexc : exceptions.card ≤ 5)
    (t : Fin n → Bool) (q : Fin n → Bool → Bool) (U : Fin n → Bool → Bool)
    (hfactor : ∀ a ∈ names, ∀ x, x ∉ exceptions → A a x = U x (q a (t x))) :
    names.card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < names.card)
  obtain ⟨p, r, _, hm⟩ := one_boundary_missing (q a) (q b) (q c)
  have missing : ∀ x ∈ (Finset.univ : Finset (Fin n)), x ∉ exceptions →
      ¬ (Bool.xor (A a x) (A b x) = p ∧ Bool.xor (A a x) (A c x) = r) := by
    intro x hx he
    rw [hfactor a ha x he, hfactor b hb x he, hfactor c hc x he]
    simpa only [Bool.xor_comm] using hm (t x) (U x)
  have bound := Patterns.HadamardPatterns.triple_missing_error_bound
    Finset.univ exceptions (F a) (F b) (F c) (A a) (A b) (A c)
    (by simpa using horth a b hab) (by simpa using horth a c hac)
    (by simpa using horth b c hbc) p r missing
  have strict := Patterns.HadamardPatterns.good_triple_budget n _ _ _ _ hn
    (hgood a ha) (hgood b hb) (hgood c hc) hexc
  simp only [Finset.card_univ, Fintype.card_fin] at bound
  omega

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux

lemma Selection.rows_card {n : ℕ} (S : Finset ℕ) :
    (Selection.rows (n := n) S).card = (S.filter (fun w => w < n)).card := by
  classical
  have heq : (Selection.rows (n := n) S).image Fin.val = S.filter (fun w => w < n) := by
    ext w
    simp only [Finset.mem_image, Selection.rows, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, u.isLt⟩
    · rintro ⟨hw, hn⟩
      exact ⟨⟨w, hn⟩, hw, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Fin.val_injective]

lemma Selection.cols_card {n : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range (2*n)) :
    (Selection.cols (n := n) S).card = (S.filter (fun w => n ≤ w)).card := by
  classical
  have heq : (Selection.cols (n := n) S).image (fun v => n + v.val) =
      S.filter (fun w => n ≤ w) := by
    ext w
    simp only [Finset.mem_image, Selection.cols, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, by omega⟩
    · rintro ⟨hw, hn⟩
      have hwlt := Finset.mem_range.mp (hS hw)
      let v : Fin n := ⟨w-n, by omega⟩
      have hv : n + v.val = w := by dsimp [v]; omega
      exact ⟨v, by simpa only [hv] using hw, hv⟩
  rw [← heq, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

lemma tree_bank_caps_of_small_regions {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    (hback : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C) (hout : C.output+1=2*n+C.size)
    (t : BTree) (ht : GoodTree (2*n) C t) (hm : t.marks≤1)
    (hraw : t.privs ⊆ Finset.range (2*n))
    (hsmall : ∀ S E : Finset ℕ, S ⊆ t.privs → S.Nonempty → E.card≤1 →
      IsTree (2*n) C S E →
      (Selection.rows (n := n) S).card≤4 → (Selection.cols (n := n) S).card≤4 →
      (Selection.rows (n := n) S).card≤2 ∧ (Selection.cols (n := n) S).card≤2) :
    (Selection.rows (n := n) t.privs).card≤2 ∧
    (Selection.cols (n := n) t.privs).card≤2 := by
  classical
  rw [Selection.rows_card, Selection.cols_card _ hraw]
  change t.bankCount (fun w => w<n)≤2 ∧ t.bankCount (fun w => n≤w)≤2
  by_contra hnot
  have hlarge : 2<t.bankCount (fun w => w<n) ∨ 2<t.bankCount (fun w => n≤w) := by omega
  obtain ⟨u, hgu, hmu, hpriv, hlu, hpu, hqu⟩ :=
    BTree.good_small_violating_subtree (fun w => w<n) (fun w => n≤w) t ht hm hlarge
  have hrawu : u.privs ⊆ Finset.range (2*n) := hpriv.trans hraw
  have hne : u.privs.Nonempty := by
    by_contra hn
    have he : u.privs=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [BTree.bankCount, he] at hlu
  obtain ⟨E, he, htree⟩ := one_mark_good_isTree hback hout hgu hmu hne
  obtain ⟨hpr, hqr⟩ := hsmall u.privs E hpriv hne he htree
    (by simpa only [Selection.rows_card, BTree.bankCount] using hpu)
    (by simpa only [Selection.cols_card _ hrawu, BTree.bankCount] using hqu)
  simp only [Selection.rows_card, Selection.cols_card _ hrawu] at hpr hqr
  change u.bankCount (fun w => w<n)≤2 at hpr
  change u.bankCount (fun w => n≤w)≤2 at hqr
  omega

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux.Causal

lemma bool_pair_gap :
    ∀ a b c d : Bool, ∃ p q : Bool,
      (p,q) ≠ (false,false) ∧ (p,q) ≠ (a,b) ∧ (p,q) ≠ (c,d) := by
  decide

lemma unary_pair_relative (u : Bool → Bool) (a b c : Bool) :
    (Bool.xor (u a) (u c), Bool.xor (u b) (u c)) = (false,false) ∨
    (Bool.xor (u a) (u c), Bool.xor (u b) (u c)) =
      (Bool.xor a c, Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;>
    cases h0 : u false <;> cases h1 : u true <;> simp_all

lemma response_pair_missing (q0 qa qb : Bool → Bool) :
    ∃ p q : Bool, (p,q) ≠ (false,false) ∧
      ∀ (t : Bool) (U : Bool → Bool),
        (Bool.xor (U (qa t)) (U (q0 t)),
          Bool.xor (U (qb t)) (U (q0 t))) ≠ (p,q) := by
  obtain ⟨p,q,hz,hf,ht⟩ := bool_pair_gap
    (Bool.xor (qa false) (q0 false)) (Bool.xor (qb false) (q0 false))
    (Bool.xor (qa true) (q0 true)) (Bool.xor (qb true) (q0 true))
  refine ⟨p,q,hz,?_⟩
  intro t U
  rcases unary_pair_relative U (qa t) (qb t) (q0 t) with hzero | hsame
  · rw [hzero]
    exact Ne.symm hz
  · rw [hsame]
    cases t
    · exact Ne.symm hf
    · exact Ne.symm ht

lemma option_factor_pair_missing {I X : Type}
    (K : I → Prop) (P : X → Prop) (A : Option I → X → Bool)
    (t : X → Bool) (q : Option I → Bool → Bool) (U : X → Bool → Bool)
    (hblank : ∀ x, P x → A none x = U x (q none (t x)))
    (hrows : ∀ a, K a → ∀ x, P x → A (some a) x = U x (q (some a) (t x)))
    (out : Bool → Bool) (a b : I) (ha : K a) (hb : K b) :
    ∃ p r : Bool, (p,r) ≠ (false,false) ∧ ∀ x, P x →
      ¬ (Bool.xor (out (A (some a) x)) (out (A none x)) = p ∧
          Bool.xor (out (A (some b) x)) (out (A none x)) = r) := by
  obtain ⟨p,r,hz,hm⟩ := response_pair_missing (q none) (q (some a)) (q (some b))
  refine ⟨p,r,hz,?_⟩
  intro x hx h
  have hg := hm (t x) (fun z => out (U x z))
  apply hg
  rw [hrows a ha x hx, hrows b hb x hx, hblank x hx] at h
  exact Prod.ext h.1 h.2


lemma factored_outputs_pair_missing {X : Type}
    (P : X → Prop) (A B H : X → Bool)
    (t : X → Bool) (q0 qa qb : Bool → Bool) (U : X → Bool → Bool)
    (h0 : ∀ x, P x → H x = U x (q0 (t x)))
    (ha : ∀ x, P x → A x = U x (qa (t x)))
    (hb : ∀ x, P x → B x = U x (qb (t x))) :
    ∃ p r : Bool, (p,r) ≠ (false,false) ∧ ∀ x, P x →
      ¬ (Bool.xor (A x) (H x) = p ∧ Bool.xor (B x) (H x) = r) := by
  obtain ⟨p,r,hz,hm⟩ := response_pair_missing q0 qa qb
  refine ⟨p,r,hz,?_⟩
  intro x hx h
  apply hm (t x) (U x)
  rw [ha x hx, hb x hx, h0 x hx] at h
  exact Prod.ext h.1 h.2

end PEqualNP.Outside.L_meta_25806_aux.Causal


namespace PEqualNP.Outside.L_meta_25806_aux.Causal

lemma piece_semantic_of_factors {n : Nat}
    (A : Fin n → Fin n → Bool) (Hr Hc : Fin n → Bool)
    (R C : Finset (Fin n)) (hR : R.card ≤ 2) (hC : C.card ≤ 2)
    (rowFactor : ∃ (t : Fin n → Bool) (q0 : Bool → Bool)
      (q : Fin n → Bool → Bool) (U : Fin n → Bool → Bool),
      (∀ x, x ∉ C → Hr x = U x (q0 (t x))) ∧
      ∀ a, a ∈ R → ∀ x, x ∉ C → A a x = U x (q a (t x)))
    (colFactor : ∃ (t : Fin n → Bool) (q0 : Bool → Bool)
      (q : Fin n → Bool → Bool) (U : Fin n → Bool → Bool),
      (∀ x, x ∉ R → Hc x = U x (q0 (t x))) ∧
      ∀ a, a ∈ C → ∀ x, x ∉ R → A x a = U x (q a (t x))) :
    R.card ≤ 2 ∧ C.card ≤ 2 ∧
    (∀ a b : Fin n, R = {a,b} → a ≠ b →
      ∃ (p q : Bool) (T : Finset (Fin n)), T.card ≤ 2 ∧ ∀ x, x ∉ T →
        ¬ (Bool.xor (A a x) (Hr x) = p ∧ Bool.xor (A b x) (Hr x) = q)) ∧
    (∀ a b : Fin n, C = {a,b} → a ≠ b →
      ∃ (p q : Bool) (T : Finset (Fin n)), T.card ≤ 2 ∧ ∀ x, x ∉ T →
        ¬ (Bool.xor (A x a) (Hc x) = p ∧ Bool.xor (A x b) (Hc x) = q)) := by
  refine ⟨hR,hC,?_,?_⟩
  · intro a b hab _hne
    obtain ⟨t,q0,q,U,h0,h⟩ := rowFactor
    have ha : a ∈ R := by simp [hab]
    have hb : b ∈ R := by simp [hab]
    obtain ⟨p,r,_hz,hm⟩ := factored_outputs_pair_missing (fun x => x ∉ C)
      (A a) (A b) Hr t q0 (q a) (q b) U h0 (h a ha) (h b hb)
    exact ⟨p,r,C,hC,hm⟩
  · intro a b hab _hne
    obtain ⟨t,q0,q,U,h0,h⟩ := colFactor
    have ha : a ∈ C := by simp [hab]
    have hb : b ∈ C := by simp [hab]
    obtain ⟨p,r,_hz,hm⟩ := factored_outputs_pair_missing (fun x => x ∉ R)
      (fun x => A x a) (fun x => A x b) Hc t q0 (q a) (q b) U h0 (h a ha) (h b hb)
    exact ⟨p,r,R,hR,hm⟩

end PEqualNP.Outside.L_meta_25806_aux.Causal
namespace PEqualNP.Outside.L_meta_25806_aux

lemma factorized_good_rows_small {n : ℕ}
    (F G : Fin n → Fin n → Bool) (A T : Finset (Fin n))
    (hn : 128 ≤ n) (hT : T.card ≤ 5)
    (hdist : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F a x ≠ F b x)).card = n)
    (herror : ∀ a ∈ A,
      16 * (Finset.univ.filter (fun x => F a x ≠ G a x)).card ≤ n)
    (q : Fin n → Bool → Bool) (t : Fin n → Bool) (U : Fin n → Bool → Bool)
    (hfactor : ∀ a ∈ A, ∀ x, x ∉ T → G a x = U x (q a (t x))) :
    A.card ≤ 2 := factored_family_cap F G A T hn hdist herror hT t q U hfactor

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux.Assembly

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_25806_aux Semantics

lemma piece_semantic_of_caps {n : ℕ} (B : BinaryCircuit) (out : Bool → Bool)
    (S E : Finset ℕ) (htree : BinaryIsTree (2*n) B S E)
    (hback : BinaryReadsBack (2*n) B) (hraw : S ⊆ Finset.range (2*n))
    (hE : E.card ≤ 1)
    (hcaps : (Selection.rows (n := n) S).card ≤ 2 ∧
      (Selection.cols (n := n) S).card ≤ 2) :
    PieceSemantic (n := n) (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v)))
      (fun x => out (B.eval (blankLeft x))) (fun x => out (B.eval (blankRight x))) S := by
  apply Causal.piece_semantic_of_factors _ _ _ (Selection.rows S) (Selection.cols S)
    hcaps.1 hcaps.2
  · simpa only [Selection.rows, Selection.cols, Finset.mem_filter, Finset.mem_univ,
      true_and] using binary_tree_row_factor B S E htree hback hraw hE out
  · simpa only [Selection.rows, Selection.cols, Finset.mem_filter, Finset.mem_univ,
      true_and] using binary_tree_col_factor B S E htree hback hraw hE out

end PEqualNP.Outside.L_meta_25806_aux.Assembly

namespace PEqualNP.Outside.L_meta_25806_aux.SemanticCaps

lemma row_cap {n : ℕ} (R T : Finset (Fin n)) (F A : Fin n → Fin n → Bool)
    (hn : 128 ≤ n) (hT : T.card ≤ 4)
    (horth : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F a x ≠ F b x)).card = n)
    (hgood : ∀ a ∈ R, 16 * (Finset.univ.filter (fun x => A a x ≠ F a x)).card ≤ n)
    (q : Fin n → Bool → Bool) (t : Fin n → Bool) (U : Fin n → Bool → Bool)
    (hfactor : ∀ a ∈ R, ∀ x, x ∉ T → A a x = U x (q a (t x))) : R.card ≤ 2 := by
  apply factored_family_cap F A R T hn horth _ (by omega) t q U hfactor
  intro a ha
  simpa only [ne_comm] using hgood a ha

lemma col_cap {n : ℕ} (R T : Finset (Fin n)) (F A : Fin n → Fin n → Bool)
    (hn : 128 ≤ n) (hT : T.card ≤ 4)
    (horth : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F x a ≠ F x b)).card = n)
    (hgood : ∀ a ∈ R, 16 * (Finset.univ.filter (fun x => A x a ≠ F x a)).card ≤ n)
    (q : Fin n → Bool → Bool) (t : Fin n → Bool) (U : Fin n → Bool → Bool)
    (hfactor : ∀ a ∈ R, ∀ x, x ∉ T → A x a = U x (q a (t x))) : R.card ≤ 2 :=
  row_cap R T (fun x y => F y x) (fun x y => A y x) hn hT horth hgood q t U hfactor

end PEqualNP.Outside.L_meta_25806_aux.SemanticCaps


namespace PEqualNP.Outside.L_meta_25806_aux

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma skeleton_binary_reads (C : BinaryCircuit) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) (w : ℕ) :
    readsIn (binarySkeleton C) G w = binaryReadsIn C G w := by
  exact shadow_binary_reads C G hG w

lemma skeleton_tree_to_binary {N : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : IsTree N (binarySkeleton C) S E) : BinaryIsTree N C S E := by
  obtain ⟨R, cap, hR, hcap, hz, hE, hin, hint⟩ := htree
  have hR' : R ⊆ Finset.range C.size := by simpa only [binarySkeleton_size] using hR
  have hr : readsIn (binarySkeleton C) R = binaryReadsIn C R :=
    funext (skeleton_binary_reads C R hR')
  have hall : readsIn (binarySkeleton C) (Finset.range (binarySkeleton C).size) =
      binaryReadsIn C (Finset.range C.size) := by
    rw [binarySkeleton_size]
    exact funext (skeleton_binary_reads C _ (Finset.Subset.refl _))
  refine ⟨R, cap, hR', hcap, ?_, ?_, ?_, ?_⟩
  · simpa only [hr] using hz
  · simpa only [hr] using hE
  · intro j hj
    have hjlt : j < C.gates.length := Finset.mem_range.mp (hR' hj)
    have hji := hin j hj
    rw [binarySkeleton_gate C j hjlt] at hji
    rw [binaryInputs_at C j hjlt]
    exact hji.2
  · simpa only [hr, hall, show (binarySkeleton C).output = C.output from rfl] using hint

lemma skeleton_back_to_binary {N : ℕ} (C : BinaryCircuit)
    (hback : ReadsBack N (binarySkeleton C)) : BinaryReadsBack N C := by
  intro j hj w hw
  apply hback j (by simpa only [binarySkeleton, List.length_map] using hj) w
  rw [binarySkeleton_gate C j hj]
  simpa only [binaryInputs_at C j hj] using hw

lemma actual_tree_bank_caps {n : ℕ} (C : BinaryCircuit) (F : Fin n → Fin n → Bool)
    (post : Bool → Bool) (hn : 128≤n)
    (hrows : ∀ u v : Fin n, u≠v →
      2*(Finset.univ.filter (fun x => F u x≠F v x)).card=n)
    (hcols : ∀ u v : Fin n, u≠v →
      2*(Finset.univ.filter (fun x => F x u≠F x v)).card=n)
    (hback : ReadsBack (2*n) (binarySkeleton C))
    (hout : C.output+1=2*n+C.size)
    (t : BTree) (ht : GoodTree (2*n) (binarySkeleton C) t) (hm : t.marks≤1)
    (hraw : t.privs ⊆ Finset.range (2*n))
    (hgoodrow : ∀ u : Fin n, u.val∈t.privs →
      16*(Finset.univ.filter (fun x => post (C.eval (PEqualNP.Represents.oneEach u x))≠F u x)).card≤n)
    (hgoodcol : ∀ v : Fin n, n+v.val∈t.privs →
      16*(Finset.univ.filter (fun x => post (C.eval (PEqualNP.Represents.oneEach x v))≠F x v)).card≤n) :
    (Selection.rows (n := n) t.privs).card≤2 ∧
    (Selection.cols (n := n) t.privs).card≤2 := by
  classical
  have hout' : (binarySkeleton C).output+1=2*n+(binarySkeleton C).size := by
    simpa only [binarySkeleton_size, show (binarySkeleton C).output = C.output from rfl] using hout
  apply tree_bank_caps_of_small_regions hback hout' t ht hm hraw
  intro S E hsub hne hE htree hr hc
  have hS : S ⊆ Finset.range (2*n) := hsub.trans hraw
  have hbtree := skeleton_tree_to_binary C S E htree
  have hbb := skeleton_back_to_binary C hback
  constructor
  · obtain ⟨z, q0, q, U, hbase, hfactor⟩ := binary_tree_row_factor C S E hbtree hbb hS hE post
    apply SemanticCaps.row_cap (Selection.rows S) (Selection.cols S) F
      (fun u v => post (C.eval (PEqualNP.Represents.oneEach u v))) hn hc hrows
      (fun u hu => hgoodrow u (hsub (Finset.mem_filter.mp hu).2)) q z U
    intro u hu x hx
    apply hfactor u (Finset.mem_filter.mp hu).2 x
    simpa only [Selection.cols, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  · obtain ⟨z, q0, q, U, hbase, hfactor⟩ := binary_tree_col_factor C S E hbtree hbb hS hE post
    apply SemanticCaps.col_cap (Selection.cols S) (Selection.rows S) F
      (fun u v => post (C.eval (PEqualNP.Represents.oneEach u v))) hn hr hcols
      (fun v hv => hgoodcol v (hsub (Finset.mem_filter.mp hv).2)) q z U
    intro v hv x hx
    apply hfactor v (Finset.mem_filter.mp hv).2 x
    simpa only [Selection.rows, Finset.mem_filter, Finset.mem_univ, true_and] using hx

end PEqualNP.Outside.L_meta_25806_aux

namespace PEqualNP.Outside.L_meta_25806_aux.Assembly

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25806_aux Semantics

lemma complete_tree_semantic {n : ℕ} (F : Fin n → Fin n → Bool)
    (B : BinaryCircuit) (out : Bool → Bool) (hn : 128 ≤ n)
    (hrows : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F a x ≠ F b x)).card = n)
    (hcols : ∀ a b : Fin n, a ≠ b →
      2 * (Finset.univ.filter (fun x => F x a ≠ F x b)).card = n)
    (hback : Normalize.Back (n+n) B.gates) (hlive : Normalize.Live (n+n) B)
    (hsize : 0 < B.size) :
    ∃ Hr Hc : Fin n → Bool,
      TreeSemantic F (fun u v => out (B.eval (PEqualNP.Represents.oneEach u v))) B Hr Hc := by
  refine ⟨fun x => out (B.eval (blankLeft x)), fun x => out (B.eval (blankRight x)), ?_⟩
  intro t ht hm hne hsub
  have ht' : GoodTree (2*n) (binarySkeleton B) t := by simpa only [two_mul] using ht
  have bback : ReadsBack (2*n) (binarySkeleton B) := by
    simpa only [two_mul] using binarySkeleton_back (n+n) B hback
  have hout : B.output+1=2*n+B.size := by
    have h := Normalize.live_output_last (n+n) B hlive hsize
    change B.output = (n+n)+(B.size-1) at h
    omega
  have hout' : (binarySkeleton B).output+1=2*n+(binarySkeleton B).size := by
    simpa only [binarySkeleton_output, binarySkeleton_size] using hout
  have hraw : t.privs ⊆ Finset.range (2*n) := by
    intro w hw
    have h := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hsub hw)).1).1
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨E, hE, htree⟩ := one_mark_good_isTree bback hout' ht' hm hne
  apply piece_semantic_of_caps B out t.privs E
    ((binarySkeleton_tree (2*n) B t.privs E).mp htree)
    ((binarySkeleton_back_iff (2*n) B).mp bback) hraw hE
  apply actual_tree_bank_caps B F out hn hrows hcols bback hout t ht' hm hraw
  · intro u hu
    exact Table.row_good_of_not_badName F _ u (Finset.mem_sdiff.mp (hsub hu)).2
  · intro v hv
    exact Table.col_good_of_not_badName F _ v (Finset.mem_sdiff.mp (hsub hv)).2

end PEqualNP.Outside.L_meta_25806_aux.Assembly

theorem PEqualNP.Outside.L_meta_25806 :
∀ (n : ℕ) (F : Fin n → Fin n → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  128 ≤ n →
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin n)).filter (fun x => F u x ≠ F v x)).card = n) →
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin n)).filter (fun x => F x u ≠ F x v)).card = n) →
  (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
  let e := ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun z => C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ F z.1 z.2)).card
  let b := C.gates.countP (fun gate => gate.inputs.length == 2)
  11*n^2 ≤ (5*b+20)*n+134*e := by
  intro n F C hn hrows hcols hfan
  apply PEqualNP.Outside.L_meta_25806_aux.Assembly.conditional_root n F C hn hrows hcols hfan
  intro B out hback hlive hsize
  exact PEqualNP.Outside.L_meta_25806_aux.Assembly.complete_tree_semantic
    F B out hn hrows hcols hback hlive hsize
