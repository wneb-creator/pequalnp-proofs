import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585_aux.MixedLinear

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost PEqualNP.TopForm

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C (fun a : Fin n => decide (a = i)) w = true

lemma mem_T {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ (T C w : Finset (Fin n)) ↔ val C (fun a : Fin n => decide (a = i)) w = true := by
  simp [T]

lemma T_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext i
  rw [mem_T]
  have h := val_input C (fun a : Fin n => decide (a = i)) ⟨w, hw⟩
  change val C (fun a : Fin n => decide (a = i)) w = _ at h
  rw [h]
  simp only [decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma append_mono (w v : List Bool) (a b : Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (w ++ [a]).getD i false = true → (v ++ [b]).getD i false = true := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases heq : i = w.length
    · subst i
      have ha : a = true := by simpa using hi
      simpa [hlen] using hab ha
    · have hle : (w ++ [a]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hle] at hi
      cases hi

lemma wiresFrom_mono (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i,
      (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = true →
      (wiresFrom gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    · simpa using hlen
    · apply append_mono w v _ _ hlen h
      apply eval_mono g.op (hao g (by simp))
      intro i _
      exact h i


lemma val_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    val C x w = true → val C y w = true := by
  apply wiresFrom_mono C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) _ w
  intro i hi
  by_cases hin : i < n
  · have hx : i < (List.ofFn x).length := by simpa
    have hy : i < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact hxy ⟨i, hin⟩ hi
  · have hle : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hle] at hi
    cases hi

def Pure {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  val C (fun i => decide (i ∉ S)) w = false

lemma pure_support {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) (hp : Pure C S w) : T C w ⊆ S := by
  intro i hi
  by_contra hni
  have hmono := val_mono C hC (fun a : Fin n => decide (a = i))
    (fun a => decide (a ∉ S)) (by
      intro a ha
      have hai : a = i := of_decide_eq_true ha
      subst a
      exact decide_eq_true hni) w ((mem_T C w i).mp hi)
  unfold Pure at hp
  rw [hp] at hmono
  cases hmono

lemma gate_data {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ g a b, C.gates[j]? = some g ∧ g.inputs = [a,b] ∧ a < n+j ∧ b < n+j ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  let g := C.gates[j]
  have hg : g ∈ C.gates := List.getElem_mem hj
  have hl := hC.2.2 g hg
  obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := by
    match h : g.inputs, hl with
    | [a,b], _ => exact ⟨a,b,rfl⟩
  have hread := hC.2.1 j hj
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getElem?_eq_getElem hj,g]
  rw [hgate] at hread
  exact ⟨g,a,b,List.getElem?_eq_getElem hj,hab,hread a (by simp [hab]),
    hread b (by simp [hab]),hC.1 g hg⟩

lemma or_support {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b := by
  ext i
  rw [Finset.mem_union,mem_T,mem_T,mem_T,val_gate C _ hg,hop,hab]
  simp [GateOp.eval,operand,ha,hb]

lemma and_support {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) :
    (T C (n+j) : Finset (Fin n)) = T C a ∩ T C b := by
  ext i
  rw [Finset.mem_inter,mem_T,mem_T,mem_T,val_gate C _ hg,hop,hab]
  simp [GateOp.eval,operand,ha,hb]

lemma pure_or {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) (S : Finset (Fin n)) :
    Pure C S (n+j) ↔ Pure C S a ∧ Pure C S b := by
  simp [Pure,val_gate C _ hg,hop,hab,GateOp.eval,operand,ha,hb]

lemma pure_and {n : ℕ} (C : Circuit) {j a b : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hab : g.inputs = [a,b])
    (ha : a < n+j) (hb : b < n+j) (S : Finset (Fin n)) :
    Pure C S (n+j) ↔ Pure C S a ∨ Pure C S b := by
  simp only [Pure,val_gate C _ hg,hop,hab,GateOp.eval,List.map_cons,List.map_nil,
    List.all_cons,List.all_nil, Bool.and_true,operand,ite_eq_left ha,ite_eq_left hb]
  cases val C (fun i => decide (i ∉ S)) a <;>
    cases val C (fun i => decide (i ∉ S)) b <;> decide

lemma T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp



def Good {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ Pure C (S c) (n+j) ∧
    u ∈ T C (n+j) ∧ ∃ u0 ∈ T C (n+j), u0 < u

lemma no_below {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n+j) (hp : Pure C (S c) a)
    (hu : u ∈ T C a) (hmin : ∀ j', j' < j → ¬ Good S C c u j') :
    ∀ t ∈ T C a, ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han,Finset.mem_singleton] at hu ht
    rw [hu,ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j',rfl⟩ : ∃ j', a = n+j' := ⟨a-n,by omega⟩
    exact hmin j' (by omega) ⟨by omega,hp,hu,t,ht,hlt⟩

lemma first_good_or {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hC : IsAO2 n C) (c : Fin m) (u : Fin n) (j : ℕ)
    (hg : Good S C c u j) (hmin : ∀ j', j' < j → ¬ Good S C c u j') :
    ∃ g a b, C.gates[j]? = some g ∧ g.op = GateOp.or ∧ g.inputs = [a,b] ∧
      a < n+j ∧ b < n+j ∧ Pure C (S c) a ∧ Pure C (S c) b ∧
      (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hj,hp,hu,u0,hu0,hlt⟩ := hg
  obtain ⟨g,a,b,hg,hab,ha,hb,hop⟩ := gate_data C hC j hj
  rcases hop with hand | hor
  · have hT := and_support C hg hand hab ha hb
    rw [hT,Finset.mem_inter] at hu hu0
    rcases (pure_and C hg hand hab ha hb (S c)).mp hp with hpa | hpb
    · exact (no_below S C c u j a hj ha hpa hu.1 hmin u0 hu0.1 hlt).elim
    · exact (no_below S C c u j b hj hb hpb hu.2 hmin u0 hu0.2 hlt).elim
  · obtain ⟨hpa,hpb⟩ := (pure_or C hg hor hab ha hb (S c)).mp hp
    exact ⟨g,a,b,hg,hor,hab,ha,hb,hpa,hpb,or_support C hg hor hab ha hb⟩

lemma no_lt_aux {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (c : Fin m) (u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n+j) (hb : b < n+j)
    (hT : (T C (n+j) : Finset (Fin n)) = T C a ∪ T C b)
    (hpa : Pure C (S c) a) (hpb : Pure C (S c) b)
    (hg : Good S C c u j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j')
    (hmin' : ∀ j', j' < j → ¬ Good S C c u' j')
    (hlt : u < u') (hu'a : u' ∈ T C a) : False := by
  obtain ⟨_,_,hu,u0,hu0,hu0lt⟩ := hg
  have h1 := no_below S C c u' j a hj ha hpa hu'a hmin'
  rw [hT,Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below S C c u j b hj hb hpb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma no_lt {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (hC : IsAO2 n C)
    (c : Fin m) (u u' : Fin n) (j : ℕ) (hg : Good S C c u j) (hg' : Good S C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j') (hmin' : ∀ j', j' < j → ¬ Good S C c u' j')
    (hlt : u < u') : False := by
  obtain ⟨g,a,b,_,_,_,ha,hb,hpa,hpb,hT⟩ := first_good_or S C hC c u j hg hmin
  have hu' := hg'.2.2.1
  rw [hT,Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux S C c u u' j a b hg.1 ha hb hT hpa hpb hg hmin hmin' hlt h
  · exact no_lt_aux S C c u u' j b a hg.1 hb ha
      (by rw [hT,Finset.union_comm]) hpb hpa hg hmin hmin' hlt h

lemma inj_core {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', u0 ∈ S c → u ∈ S c →
      u0 ∈ S c' → u ∈ S c' → c = c') (C : Circuit) (hC : IsAO2 n C)
    (c : Fin m) (u : Fin n) (c' : Fin m) (u' : Fin n) (j : ℕ)
    (hg : Good S C c u j) (hg' : Good S C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good S C c u j')
    (hmin' : ∀ j', j' < j → ¬ Good S C c' u' j') : c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_,hp,hu,u0,hu0,hlt⟩ := hg
    have hsub := pure_support C hC (S c) (n+j) hp
    have hsub' := pure_support C hC (S c') (n+j) hg'.2.1
    exact hN u0 u (ne_of_lt hlt) c c' (hsub hu0) (hsub hu) (hsub' hu0) (hsub' hu)
  subst hcc
  refine ⟨rfl,?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt S C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt S C hC c u' u j hg' hg hmin' hmin h).elim

lemma pure_computes {n : ℕ} (C : Circuit) (w : ℕ) (L S : Finset (Fin n))
    (hc : ComputesOr n C w L) (hs : L ⊆ S) : Pure C S w := by
  have h := hc.2 (fun a : Fin n => decide (a ∉ S))
  change (val C (fun a : Fin n => decide (a ∉ S)) w = true ↔ _) at h
  unfold Pure
  apply Bool.eq_false_iff.mpr
  intro hv
  obtain ⟨i,hi,hi'⟩ := h.mp hv
  exact (of_decide_eq_true hi') (hs hi)

lemma leaf_min {m n : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (L : Finset (Fin n))
    (c : Fin m) (hS : ∃ w < n+C.gates.length, Pure C (S c) w ∧ L ⊆ T C w)
    (u : Fin n) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good S C c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w,hw,hpure,hT⟩ := hS
  have hu' := hT hu
  have ht' := hT ht
  by_cases hwn : w < n
  · rw [T_input C w hwn,Finset.mem_singleton] at hu' ht'
    rw [hu',ht'] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    exact hng ⟨j,by omega,hpure,hu',t,ht',hlt⟩

lemma card_le_of_unique_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, Set.Subsingleton {a | a ∈ s ∧ r a b}) : s.card ≤ t.card := by
  classical
  let f : s → β := fun a => Classical.choose (hs a.1 a.2)
  have hf (a : s) : f a ∈ t ∧ r a.1 (f a) := Classical.choose_spec (hs a.1 a.2)
  let g : s → t := fun a => ⟨f a, (hf a).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' heq
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply Subtype.ext
  exact ht (f a) (hf a).1 ⟨a.2, (hf a).2⟩ ⟨a'.2, heq'.symm ▸ (hf a').2⟩



def orGates (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    (C.gates[j]?.map fun g => isOrOp g.op).getD false = true

lemma count_gen {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', u0 ∈ S c → u ∈ S c → u0 ∈ S c' → u ∈ S c' → c = c')
    (C : Circuit) (hC : IsAO2 n C)
    (K : Finset (Fin m × Finset (Fin n)))
    (hK : ∀ k ∈ K, ∃ w < n+C.gates.length, Pure C (S k.1) w ∧ k.2 ⊆ T C w)
    (P : Finset (Σ _ : Fin m, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ (orGates C).card + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good S C q.1 q.2 j).card ≤ (orGates C).card := by
    refine card_le_of_unique_fibers
      (fun q j => Good S C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good S C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      obtain ⟨g,a,b,hg,hop,_⟩ := first_good_or S C hC q.1 q.2 (Nat.find hex)
          (Nat.find_spec hex) (fun j' hj' => Nat.find_min hex hj')
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.find_spec hex).1,?_⟩
      simp [hg,hop,isOrOp]
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core S hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good S C q.1 q.2 j).card ≤ K.card := by
    refine card_le_of_unique_fibers
      (fun q k => k.1 = q.1 ∧ q.2 ∈ k.2) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro k hk q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      have hcc : c = c' := hqc.symm.trans hqc'
      subst hcc
      have hcomp := hK k hk
      rw [hqc] at hcomp
      have h1 := leaf_min S C k.2 c hcomp u hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min S C k.2 c hcomp u' hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good S C q.1 q.2 j)
  omega

lemma pure_family_ao_bound_active {m n : ℕ} (S U : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (U p).Nonempty → ∃ w < n+C.gates.length, Pure C (S p) w ∧ U p ⊆ T C w) :
    (∑ p : Fin m, (U p).card) ≤ (orGates C).card + (Finset.univ.filter fun p => (U p).Nonempty).card := by
  classical
  have hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ p q : Fin m,
      u0 ∈ S p → u ∈ S p → u0 ∈ S q → u ∈ S q → p = q := by
    intro u0 u hne p q hp0 hpu hq0 hqu
    by_contra hpq
    have hs : ({u0, u} : Finset (Fin n)) ⊆ S p ∩ S q := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hp0, hq0⟩
      · exact Finset.mem_inter.mpr ⟨hpu, hqu⟩
    have hc : ({u0, u} : Finset (Fin n)).card = 2 := by simp [hne]
    have hle := Finset.card_le_card hs
    have hsmall := hlin p q hpq
    omega
  let A : Finset (Fin m) := Finset.univ.filter fun p => (U p).Nonempty
  let K : Finset (Fin m × Finset (Fin n)) := A.image fun p => (p,U p)
  let I : Finset (Σ _ : Fin m, Fin n) := Finset.univ.sigma U
  have hK : ∀ k ∈ K,
      ∃ w < n+C.gates.length, Pure C (S k.1) w ∧ k.2 ⊆ T C w := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact hcomp p (Finset.mem_filter.mp hp).2
  have hP : ∀ q ∈ I, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2 := by
    intro q hq
    refine ⟨(q.1,U q.1), ?_, rfl, (Finset.mem_sigma.mp hq).2⟩
    exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨q.2, (Finset.mem_sigma.mp hq).2⟩⟩, rfl⟩
  have hbound := count_gen S hN C hC K hK I hP
  have hKcard : K.card ≤ A.card := Finset.card_image_le
  dsimp [A] at hKcard
  have hIcard : I.card = ∑ p : Fin m, (U p).card := Finset.card_sigma _ _
  omega

lemma linear_family_ao_bound_active {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (S p).Nonempty → ∃ w < n+C.gates.length, ComputesOr n C w (S p)) :
    (∑ p : Fin m, (S p).card) ≤ (orGates C).card +
      (Finset.univ.filter fun p => (S p).Nonempty).card := by
  apply pure_family_ao_bound_active S S hlin C hC
  intro p hp
  obtain ⟨w,hw,hcomp⟩ := hcomp p hp
  exact ⟨w,hw,pure_computes C w (S p) (S p) hcomp (by intro i hi; exact hi),
    by rw [T_computes C w (S p) hcomp]⟩

lemma linear_family_ao_cost {m n : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (C : Circuit) (hC : IsAO2 n C)
    (hcomp : ∀ p, (S p).Nonempty → ∃ w < n+C.gates.length, ComputesOr n C w (S p)) :
    (∑ p : Fin m, ((S p).card - 1)) ≤ (orGates C).card := by
  classical
  have hcard (p : Fin m) :
      (S p).card = ((S p).card - 1) + if (S p).Nonempty then 1 else 0 := by
    by_cases hp : (S p).Nonempty
    · have hpos := Finset.card_pos.mpr hp
      simp only [ite_eq_left hp]
      omega
    · have hempty : S p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      simp [hempty]
  have hsum : (∑ p : Fin m, (S p).card) =
      (∑ p : Fin m, ((S p).card - 1)) +
        (Finset.univ.filter fun p => (S p).Nonempty).card := by
    calc
      (∑ p : Fin m, (S p).card) =
          ∑ p : Fin m, (((S p).card - 1) + if (S p).Nonempty then 1 else 0) :=
        Finset.sum_congr rfl (fun p _ => hcard p)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  have hb := linear_family_ao_bound_active S hlin C hC hcomp
  omega


end PEqualNP.Outside.L_meta_2585_aux.MixedLinear
