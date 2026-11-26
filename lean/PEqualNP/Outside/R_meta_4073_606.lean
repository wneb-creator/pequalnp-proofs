import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4073_606
    (orbit0 : ∀ (p q : List Gate) (a b : ℕ), p.length ≤ 8 → q.length ≤ 9 →
      FanInTwo ⟨p ++ q, 0⟩ → 19 ≤ b →
      let w := fun (x : Fin 10 → Bool) (i : ℕ) =>
        ((Circuit.mk q 0).wires ((Circuit.mk p 0).wires (List.ofFn x ++ [!x 0]))).getD i false
      (∀ r ∈ ([116, 402, 554] : List ℕ), w (fun i => r.testBit i.val) b = false) →
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      ∃ x, (w x a && w x b) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (orbit1 : ∀ (p q : List Gate) (a b : ℕ), p.length ≤ 8 → q.length ≤ 9 →
      FanInTwo ⟨p ++ q, 0⟩ → 19 ≤ b →
      let w := fun (x : Fin 10 → Bool) (i : ℕ) =>
        ((Circuit.mk q 0).wires ((Circuit.mk p 0).wires (List.ofFn x ++ [!x 0]))).getD i false
      (∀ r ∈ ([201, 116, 402] : List ℕ), w (fun i => r.testBit i.val) b = false) →
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      ∃ x, (w x a && w x b) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (orbit2 : ∀ (p q : List Gate) (a b : ℕ), p.length ≤ 8 → q.length ≤ 9 →
      FanInTwo ⟨p ++ q, 0⟩ → 19 ≤ b →
      let w := fun (x : Fin 10 → Bool) (i : ℕ) =>
        ((Circuit.mk q 0).wires ((Circuit.mk p 0).wires (List.ofFn x ++ [!x 0]))).getD i false
      (∀ r ∈ ([201, 773, 116] : List ℕ), w (fun i => r.testBit i.val) b = false) →
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      ∃ x, (w x a && w x b) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ));       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x1.wires (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))])).getD x8 Bool.false;       (∃ (x8 : Fin (10 : ℕ) → Bool), x7 x8 x2 = Bool.true ∧ x7 x8 x3 = Bool.false) → (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x2 = Bool.false ∧ x7 x9 x3 = Bool.true) → (∀ (x10 : Fin (10 : ℕ) → Bool), x6 x10 = Bool.true → x7 x10 x2 = Bool.true ∧ x7 x10 x3 = Bool.true) → ∃ (x11 : Fin (10 : ℕ) → Bool), x6 x11 = Bool.false ∧ x7 x11 x2 = Bool.true ∧ x7 x11 x3 = Bool.true := by
  intro C a b fan cap f w ha hb hp
  classical
  by_contra failure
  have eqn (x : Fin 10 → Bool) : (w x a && w x b) = f x := by
    cases hv : f x
    · cases h1 : w x a <;> cases h2 : w x b <;> try rfl
      exact (failure ⟨x,hv,h1,h2⟩).elim
    · obtain ⟨h1,h2⟩ := hp x hv
      simp [h1,h2]
  let sig : Fin 12 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9], ![0, 5, 8, 6, 1, 4, 7, 3, 9, 2], ![0, 5, 7, 9, 4, 1, 8, 2, 6, 3], ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6], ![0, 4, 9, 7, 5, 1, 3, 6, 2, 8], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6]]
  let old : Fin 12 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 3, 2, 4], ![0, 4, 2, 3, 1], ![0, 4, 3, 2, 1], ![2, 1, 0, 3, 4], ![3, 1, 0, 2, 4], ![2, 4, 0, 3, 1], ![3, 4, 0, 2, 1], ![2, 1, 3, 0, 4], ![3, 1, 2, 0, 4], ![2, 4, 3, 0, 1], ![3, 4, 2, 0, 1]]
  let mask : Fin 5 → ℕ := ![116, 201, 402, 554, 773]
  let rep : Fin 3 → Fin 3 → Fin 5 := ![![0, 2, 3], ![1, 0, 2], ![1, 4, 0]]
  let row (j : Fin 5) (v : Fin 10) := (mask j).testBit v.val
  have independent : ∀ j, f (row j) = false := by decide
  have fix0 : ∀ k, sig k 0 = 0 := by decide
  have inverse : ∀ k, ∃ l, ∀ i, sig l (sig k i) = i := by decide
  have rel : ∀ k j v, row j (sig k v) = row (old k j) v := by decide
  have auto (k : Fin 12) (x : Fin 10 → Bool) : f (fun i => x (sig k i)) = f x := by
    fin_cases k <;> dsimp [sig, f] <;> ac_rfl
  have same (x : Fin 10 → Bool) : f x = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by
    dsimp [f, List.any]
    ac_rfl
  have cover : ∀ z : Fin 5 → Bool, ∃ c : Bool, ∃ k : Fin 12, ∃ t : Fin 3,
      ∀ j : Fin 3, z (old k (rep t j)) = c := by decide
  obtain ⟨c,k,t,covering⟩ := cover (fun j => !(w (row j) b))
  let u := if c then a else b
  let v := if c then b else a
  have equ (x : Fin 10 → Bool) : (w x u && w x v) = f x := by
    cases hc : c <;> simpa [u,v,hc,Bool.and_comm] using eqn x
  have uv : ∃ x, w x u = true ∧ w x v = false := by
    cases hc : c
    · simpa [u,v,hc,and_comm] using hb
    · simpa [u,v,hc] using ha
  have vu : ∃ x, w x u = false ∧ w x v = true := by
    cases hc : c
    · simpa [u,v,hc,and_comm] using ha
    · simpa [u,v,hc] using hb
  have rejected (j : Fin 3) : w (row (old k (rep t j))) v = false := by
    have hc := covering j
    have he := (eqn (row (old k (rep t j)))).trans (independent _)
    cases hC : c <;> cases hB : w (row (old k (rep t j))) b <;>
      cases hA : w (row (old k (rep t j))) a <;> simp [v,hC,hA,hB] at hc he ⊢
  let move (i : ℕ) := if hi : i < 10 then (sig k ⟨i,hi⟩).val else i
  let mapped (g : Gate) : Gate := ⟨g.op, g.inputs.map move⟩
  let exec (gs : List Gate) (ws : List Bool) :=
    gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)]) ws
  let input (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]
  have length (gs : List Gate) (xs : List Bool) : (exec gs xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp [exec]
    | cons g gs ih =>
      change (exec gs (_ ++ [_])).length = _
      rw [ih]
      simp
      omega
  have read (ws : List Bool) (b' : Bool) (i : ℕ) :
      (ws ++ [b']).getD i false = if i = ws.length then b' else ws.getD i false := by
    rcases lt_trichotomy i ws.length with h | h | h
    · rw [ite_eq_right (by omega), List.getD_append _ _ _ _ h]
    · subst i; simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
  have snoc (gs : List Gate) (g : Gate) (xs : List Bool) : exec (gs ++ [g]) xs =
      exec gs xs ++ [g.op.eval (g.inputs.map fun i => (exec gs xs).getD i false)] := by
    simp [exec,List.foldl_append]
  have sync (x : Fin 10 → Bool) (gs : List Gate) (i : ℕ) :
      (exec gs (input (fun j => x (sig k j)))).getD i false =
        (exec (gs.map mapped) (input x)).getD (move i) false := by
    induction gs using List.reverseRecOn generalizing i with
    | nil =>
      simp only [List.map_nil]
      change (input _).getD i false = (input _).getD (move i) false
      by_cases hi : i < 10
      · have base (z : Fin 10 → Bool) (j : Fin 10) : (input z).getD j.val false = z j := by
          unfold input
          rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
        rw [show move i = (sig k ⟨i,hi⟩).val by simp [move,hi],
          base (fun j => x (sig k j)) ⟨i,hi⟩,base x (sig k ⟨i,hi⟩)]
      · by_cases hi' : i = 10
        · subst i; simp [input,move,List.getD_eq_getElem?_getD,fix0]
        · rw [show move i = i by simp [move,hi], List.getD_eq_default _ _ (by simp [input]; omega),
            List.getD_eq_default _ _ (by simp [input]; omega)]
    | append_singleton gs g ih =>
      let xs := exec gs (input (fun j => x (sig k j)))
      let ys := exec (gs.map mapped) (input x)
      have hlx : xs.length = 11 + gs.length := by simp [xs,length,input]
      have hly : ys.length = 11 + gs.length := by simp [ys,length,input]
      have ix : move i = ys.length ↔ i = xs.length := by
        rw [hlx,hly]; unfold move
        split <;> rename_i h
        · have := (sig k ⟨i,h⟩).isLt; omega
        · rfl
      have gateEq : g.op.eval (g.inputs.map (fun j => xs.getD j false)) =
          (mapped g).op.eval ((mapped g).inputs.map (fun j => ys.getD j false)) := by
        simp only [mapped,List.map_map]
        congr 1
        exact List.map_congr_left fun j _ => ih j
      simp only [List.map_append,List.map_cons,List.map_nil]
      rw [snoc,snoc]
      change (xs ++ [_]).getD i false = (ys ++ [_]).getD (move i) false
      rw [read,read,gateEq]
      by_cases hi : i = xs.length
      · rw [ite_eq_left hi,ite_eq_left (ix.mpr hi)]
      · rw [ite_eq_right hi,ite_eq_right (fun hh => hi (ix.mp hh))]
        exact ih i
  let p := (C.gates.map mapped).take 8
  let q := (C.gates.map mapped).drop 8
  have splitP : p ++ q = C.gates.map mapped := List.take_append_drop _ _
  have pcap : p.length ≤ 8 := by simp [p]
  have qcap : q.length ≤ 9 := by
    have h : C.gates.length ≤ 17 := cap
    simp [q]; omega
  have legal : FanInTwo ⟨p ++ q,0⟩ := by
    intro g hg
    change g ∈ p ++ q at hg
    rw [splitP] at hg
    obtain ⟨g0,h0,rfl⟩ := List.mem_map.mp hg
    simpa [mapped] using fan g0 h0
  let wire (x : Fin 10 → Bool) (i : ℕ) :=
    ((Circuit.mk q 0).wires ((Circuit.mk p 0).wires (input x))).getD i false
  have transfer (x : Fin 10 → Bool) (i : ℕ) : wire x (move i) = w (fun j => x (sig k j)) i := by
    have s := sync x C.gates i
    rw [← splitP] at s
    change (exec q (exec p (input x))).getD (move i) false =
      (exec C.gates (input (fun j => x (sig k j)))).getD i false
    simpa only [exec, List.foldl_append] using s.symm
  obtain ⟨l,hl⟩ := inverse k
  have lift (x : Fin 10 → Bool) : ∃ y : Fin 10 → Bool, (fun i => y (sig k i)) = x :=
    ⟨fun i => x (sig l i),funext fun i => congrArg x (hl i)⟩
  have huv : ∃ x, wire x (move u) = true ∧ wire x (move v) = false := by
    obtain ⟨x,hx⟩ := uv
    obtain ⟨y,hy⟩ := lift x
    exact ⟨y, by simpa [transfer,hy] using hx⟩
  have hvu : ∃ x, wire x (move u) = false ∧ wire x (move v) = true := by
    obtain ⟨x,hx⟩ := vu
    obtain ⟨y,hy⟩ := lift x
    exact ⟨y, by simpa [transfer,hy] using hx⟩
  have hr (j : Fin 3) : wire (row (rep t j)) (move v) = false := by
    rw [transfer,show (fun i => row (rep t j) (sig k i)) = row (old k (rep t j)) from
      funext (rel k (rep t j))]
    exact rejected j
  have correct (x : Fin 10 → Bool) :
      (wire x (move u) && wire x (move v)) = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by
    rw [transfer,transfer,equ,auto,same]
  have rise : ∀ (tt : Fin 3) (i : Fin 10), ∃ j : Fin 3,
      f (Function.update (row (rep tt j)) i true) = true := by decide
  have keep (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (exec gs xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change (exec gs (xs ++ [_])).getD i false = _
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]
  have dep (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      ∀ T : Finset ℕ, ∃ S : Finset ℕ, S.card ≤ gs.length + T.card ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ t ∈ T, (exec gs x).getD t false = (exec gs y).getD t false := by
    induction gs using List.reverseRecOn with
    | nil => exact fun T => ⟨T, by simp, fun x y _ _ h t ht => by simpa [exec] using h t ht⟩
    | append_singleton gs g ih =>
      intro T
      have ih' := ih (fun g' h' => hg g' (by simp [h']))
      have hlen := hg g (by simp)
      by_cases hk : n + gs.length ∈ T
      · obtain ⟨S, hS, hdet⟩ := ih' (T.erase (n + gs.length) ∪ g.inputs.toFinset)
        refine ⟨S, ?_, ?_⟩
        · have h1 := Finset.card_union_le (T.erase (n + gs.length)) g.inputs.toFinset
          have h2 := Finset.card_erase_add_one hk
          have h3 := List.toFinset_card_le g.inputs
          rw [List.length_append, List.length_singleton]
          omega
        · intro x y hx hy hxy t ht
          have hd := hdet x y hx hy hxy
          rw [snoc, snoc, read, read, length, length, hx, hy]
          by_cases htk : t = n + gs.length
          · rw [ite_eq_left htk, ite_eq_left htk]
            congr 1
            exact List.map_congr_left fun i hi => hd i (by simp [hi])
          · rw [ite_eq_right htk, ite_eq_right htk]
            exact hd t (by simp [htk, ht])
      · obtain ⟨S, hS, hdet⟩ := ih' T
        refine ⟨S, ?_, ?_⟩
        · rw [List.length_append, List.length_singleton]; omega
        · intro x y hx hy hxy t ht
          have htk : t ≠ n + gs.length := fun h => hk (h ▸ ht)
          rw [snoc, snoc, read, read, length, length, hx, hy,
            ite_eq_right htk, ite_eq_right htk]
          exact hdet x y hx hy hxy t ht
  have late : 19 ≤ move v := by
    by_contra! lo
    have pval (x : Fin 10 → Bool) : wire x (move v) = (exec p (input x)).getD (move v) false := by
      by_cases short : C.gates.length ≤ 8
      · have nilq : q = [] := List.drop_eq_nil_of_le (by simpa using short)
        change (exec q (exec p (input x))).getD (move v) false = _
        rw [nilq]; rfl
      · have plen : p.length = 8 := by simp [p]; omega
        change (exec q (exec p (input x))).getD (move v) false = _
        apply keep
        simpa [length,input,plen] using lo
    have pfan (g : Gate) (h : g ∈ p) : g.inputs.length ≤ 2 := (legal g (List.mem_append_left _ h)).2
    obtain ⟨S,hs,hd⟩ := dep 11 p pfan {move v}
    have hS : S.card ≤ 9 := by simp only [Finset.card_singleton] at hs; omega
    let origin (i : ℕ) : Fin 10 := if hi : i < 10 then ⟨i,hi⟩ else 0
    have absent : ∃ j : Fin 10, j ∉ S.image origin := by
      by_contra! allmem
      have hsub : Finset.univ ⊆ S.image origin := fun j _ => allmem j
      have bound := Finset.card_le_card hsub
      have hab := Finset.card_image_le (s := S) (f := origin)
      simp only [Finset.card_univ,Fintype.card_fin] at bound
      omega
    obtain ⟨j,no⟩ := absent
    obtain ⟨d,hdpos⟩ := rise t j
    let x := row (rep t d)
    let y := Function.update x j true
    have hx := hr d
    have hy : wire y (move v) = true := by
      exact (Bool.and_eq_true_iff.mp (((correct y).trans (same y).symm).trans hdpos)).2
    have val (z : Fin 10 → Bool) (i : Fin 10) : (input z).getD i.val false = z i := by
      unfold input
      rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have hag (i : ℕ) (hi : i ∈ S) : (input x).getD i false = (input y).getD i false := by
      have neq : origin i ≠ j := fun he => no (Finset.mem_image.mpr ⟨i,hi,he⟩)
      by_cases lt : i < 10
      · rw [val x ⟨i,lt⟩,val y ⟨i,lt⟩]
        exact (Function.update_of_ne (by simpa [origin,lt] using neq) _ _).symm
      · have nz : (0 : Fin 10) ≠ j := by simpa [origin,lt] using neq
        by_cases ei : i = 10
        · subst i; simp [input,y,Function.update_of_ne nz]
        · rw [List.getD_eq_default _ _ (by simp [input]; omega),
              List.getD_eq_default _ _ (by simp [input]; omega)]
    have eqxy := hd (input x) (input y) (by simp [input]) (by simp [input]) hag (move v) (by simp)
    rw [← pval,← pval,hy] at eqxy
    exact Bool.false_ne_true (hx.symm.trans eqxy)
  have rejects (rs : List ℕ) (h : ∀ r ∈ rs, ∃ j, r = mask (rep t j)) :
      ∀ r ∈ rs, wire (fun i => r.testBit i.val) (move v) = false := by
    intro r hr'
    obtain ⟨j,rfl⟩ := h r hr'
    exact hr j
  fin_cases t
  · obtain ⟨x,hx⟩ := orbit0 p q (move u) (move v) pcap qcap legal late
      (rejects _ (by decide)) huv hvu
    exact hx (correct x)
  · obtain ⟨x,hx⟩ := orbit1 p q (move u) (move v) pcap qcap legal late
      (rejects _ (by decide)) huv hvu
    exact hx (correct x)
  · obtain ⟨x,hx⟩ := orbit2 p q (move u) (move v) pcap qcap legal late
      (rejects _ (by decide)) huv hvu
    exact hx (correct x)
