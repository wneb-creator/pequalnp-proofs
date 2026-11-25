import PEqualNP.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.EquivFin

namespace PEqualNP.Outside.L_meta_5218_aux

open PEqualNP.CircuitLowerBounds

def wires {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

-- The all-wire monotonicity induction is adapted from PR #5770, based on Felix Li's R_meta_2130_1.
lemma prefix_order {n : ℕ} (gs : List Gate) (x y : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (hxy : x ≤ y) (i : ℕ) :
    (wires gs x).getD i false ≤ (wires gs y).getD i false := by
  let runW : List Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ gs g x, runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
    intro gs g x
    simp [runW]
  have hrun_len : ∀ gs x, (runW gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [runW]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have heval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hrun_mono : ∀ gs, (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (runW gs x).getD i false = true → (runW gs y).getD i false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => exact hle
    | append_singleton gs g ih =>
      have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
        fun g' hg' => hgs g' (List.mem_append_left _ hg')
      have ih' := ih hgs'
      have hlen_eq : (runW gs x).length = (runW gs y).length := by rw [hrun_len, hrun_len, hxy]
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
      intro i hi
      rw [hrun_snoc] at hi ⊢
      by_cases hlt : i < (runW gs x).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        exact ih' i hi
      · by_cases heq : i = (runW gs x).length
        · subst heq
          rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
          rw [hlen_eq, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
          simp only [Option.getD_some] at hi ⊢
          rcases hg with hop | hop <;> rw [hop] at hi ⊢
          · simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro b ⟨j, hj, rfl⟩
            exact ih' j (hi _ ⟨j, hj, rfl⟩)
          · simp only [heval_or, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            obtain ⟨_, ⟨j, hj, rfl⟩, htrue⟩ := hi
            exact ⟨_, ⟨j, hj, rfl⟩, ih' j htrue⟩
        · have hge : (runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)]).length ≤ i := by
            simp; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
          cases hi
  have hbits (j : Fin n) : x j = true → y j = true := Bool.le_iff_imp.mp (hxy j)
  have hin (j : ℕ) : (List.ofFn x).getD j false = true → (List.ofFn y).getD j false = true := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> simp_all
  exact Bool.le_iff_imp.mpr (hrun_mono gs hops _ _ (by simp) hin i)


private theorem frontier {n : ℕ} (limit : ℕ) (X : Finset (Fin n)) (dif : ℕ → Fin n → ℕ → Prop)
    (active : ℕ → Prop) [DecidablePred active] (pins : ℕ → Finset ℕ)
    (pinCount : ∀ k < limit, (pins k).card ≤ 2)
    (base : ∀ c w, dif 0 c w → w = c.val)
    (old : ∀ k < limit, ∀ c w, w ≠ n+k → dif (k+1) c w → dif k c w)
    (newWire : ∀ k < limit, ∀ c, dif (k+1) c (n+k) → active k ∧ ∃ w ∈ pins k, dif k c w) :
    ∀ k ≤ limit, ∀ (U : Finset ℕ), (∀ c ∈ X, ∃ w ∈ U, dif k c w) →
      X.card ≤ U.card + ((Finset.range k).filter active).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro hk U covers
    have sub : X.image Fin.val ⊆ U := by
      intro w hw
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨w,hw,hd⟩ := covers c hc
      simpa [base c w hd] using hw
    have eq : (X.image Fin.val).card = X.card := Finset.card_image_of_injective X Fin.val_injective
    simpa [←eq] using Finset.card_le_card sub
  | succ k ih =>
    intro hk U covers
    by_cases splitWire : n+k ∈ U ∧ active k
    · let V := U.erase (n+k) ∪ pins k
      have cv : ∀ c ∈ X, ∃ w ∈ V, dif k c w := by
        intro c hc
        obtain ⟨w,hw,hd⟩ := covers c hc
        by_cases e : w = n+k
        · subst w
          obtain ⟨_,v,hv,dv⟩ := newWire k (by omega) c hd
          exact ⟨v,Finset.mem_union_right _ hv,dv⟩
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hw⟩),old k (by omega) c w e hd⟩
      have hb := ih (by omega) V cv
      have hu := Finset.card_union_le (U.erase (n+k)) (pins k)
      have he := Finset.card_erase_add_one splitWire.1
      have hp := pinCount k (by omega)
      have ha : ((Finset.range (k+1)).filter active).card =
          ((Finset.range k).filter active).card + 1 := by
        simp [Finset.range_add_one, Finset.filter_insert, splitWire.2]
      dsimp [V] at hb
      omega
    · have cv : ∀ c ∈ X, ∃ w ∈ U, dif k c w := by
        intro c hc
        obtain ⟨w,hw,hd⟩ := covers c hc
        have e : w ≠ n+k := by
          rintro rfl
          exact splitWire ⟨hw,(newWire k (by omega) c hd).1⟩
        exact ⟨w,hw,old k (by omega) c w e hd⟩
      have monot := Finset.card_le_card (Finset.filter_subset_filter active (Finset.range_mono (Nat.le_succ k)))
      exact (ih (by omega) U cv).trans (Nat.add_le_add_left monot _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

private def pref {n : ℕ} (C : Circuit) (k : ℕ) (z : Fin n → Bool) :=
  wires (C.gates.take k) z

private lemma lenW {n : ℕ} (gs : List Gate) (z : Fin n → Bool) :
    (wires gs z).length = n+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih =>
    simp only [wires,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton] at *
    omega

private lemma lookupAppend (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · simp [List.getElem?_append_left h,Nat.ne_of_lt h]
  · rw [List.getElem?_append_right (by omega),List.getElem?_eq_none (by omega : w.length ≤ i)]
    by_cases eq : i=w.length
    · simp [eq]
    · simp [eq,show i-w.length ≠ 0 by omega]

private lemma next {n : ℕ} (C : Circuit) {k : ℕ} (hk : k<C.size) (z : Fin n → Bool) (w : ℕ) :
    (pref C (k+1) z).getD w false =
      if w=n+k then C.gates[k].op.eval (C.gates[k].inputs.map fun u => (pref C k z).getD u false)
      else (pref C k z).getD w false := by
  have hk' : k < C.gates.length := hk
  have hlen : (pref C k z).length = n+k := by simp [pref,lenW,Nat.min_eq_left hk'.le]
  have eq : pref C (k+1) z = pref C k z ++
      [C.gates[k].op.eval (C.gates[k].inputs.map fun u => (pref C k z).getD u false)] := by
    unfold pref wires
    rw [List.take_succ_eq_append_getElem hk',List.foldl_append]
    rfl
  rw [eq,lookupAppend,hlen]
  rfl

private lemma stable {n : ℕ} (C : Circuit) (z : Fin n → Bool) {j t : ℕ} (hjt : j ≤ t)
    (ht : t ≤ C.size) (i : ℕ) (hi : i<n+j) :
    (pref C t z).getD i false = (pref C j z).getD i false := by
  induction t, hjt using Nat.le_induction with
  | base => rfl
  | succ t h ih =>
    rw [next C (by omega) z i, if_neg (by omega)]
    exact ih (by omega)

private lemma full {n : ℕ} (C : Circuit) (z : Fin n → Bool) :
    pref C C.size z = C.wires (List.ofFn z) := by
  simp [pref,wires,Circuit.wires,Circuit.size]

private lemma finCard {m : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.range m).filter p).card = Fintype.card {j : Fin m // p j.val} := by
  classical
  let e : {j // j ∈ (Finset.range m).filter p} ≃ {j : Fin m // p j.val} :=
    { toFun := fun x => ⟨⟨x.val,Finset.mem_range.mp (Finset.mem_filter.mp x.property).1⟩,
                          (Finset.mem_filter.mp x.property).2⟩
      invFun := fun x => ⟨x.val.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val.isLt,x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  simpa using Fintype.card_congr e

private theorem solve {n : ℕ} (C : Circuit) (F : Finset (Fin n → Bool)) (X : Finset (Fin n))
    (mono : Monotone2 C)
    (piv : ∀ c ∈ X, ∃ z ∈ F, circuitFun n C z ≠ circuitFun n C (Function.update z c false)) :
    X.card ≤ Fintype.card {j : Fin C.size //
      (C.wires (List.replicate n false)).getD (n+j.val) false = false ∧
      ∃ z ∈ F, gateVal n C j.val z = true} + 1 := by
  classical
  let a (k : ℕ) := (C.wires (List.replicate n false)).getD (n+k) false = false ∧
                      ∃ z ∈ F, gateVal n C k z = true
  let d (k : ℕ) (c : Fin n) (w : ℕ) := ∃ z ∈ F, (pref C k z).getD w false ≠
                       (pref C k (Function.update z c false)).getD w false
  let P (k : ℕ) := if h : k < C.gates.length then C.gates[k].inputs.toFinset else ∅
  have count : ∀ k < C.size, (P k).card ≤ 2 := by
    intro k hk
    have h : k < C.gates.length := hk
    simpa [P,h] using (C.gates[k].inputs.toFinset_card_le.trans (mono C.gates[k] (List.getElem_mem _)).2)
  have base : ∀ c w, d 0 c w → w=c.val := by
    intro c w h
    obtain ⟨z,_,hz⟩ := h
    by_contra! e
    apply hz
    by_cases hw : w<n
    · have ne : (⟨w,hw⟩ : Fin n) ≠ c := by intro eq; exact e (congrArg Fin.val eq)
      simp [pref,wires,List.getD_eq_getElem?_getD,hw,Function.update_of_ne ne]
    · simp [pref,wires,List.getD_eq_getElem?_getD,hw]
  have old : ∀ k < C.size, ∀ c w, w ≠ n+k → d (k+1) c w → d k c w := by
    intro k hk c w e hd
    obtain ⟨z,hz,h⟩ := hd
    exact ⟨z,hz,by simpa only [next C hk,if_neg e] using h⟩
  have fresh : ∀ k < C.size, ∀ c, d (k+1) c (n+k) → a k ∧ ∃ w ∈ P k, d k c w := by
    intro k hk c hd
    obtain ⟨z,hz,h⟩ := hd
    let y := Function.update z c false
    let zero : Fin n → Bool := fun _ => false
    have yo : y ≤ z := by intro u; by_cases e : u=c <;> simp [y,e,Function.update_of_ne]
    have zo : zero ≤ y := by intro u; simp [zero]
    have hops : ∀ g ∈ C.gates.take (k+1), g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      exact (mono g (List.mem_of_mem_take hg)).1
    have hy := prefix_order (C.gates.take (k+1)) y z hops yo (n+k)
    have hzero := prefix_order (C.gates.take (k+1)) zero y hops zo (n+k)
    change (pref C (k+1) y).getD (n+k) false ≤ (pref C (k+1) z).getD (n+k) false at hy
    change (pref C (k+1) zero).getD (n+k) false ≤ (pref C (k+1) y).getD (n+k) false at hzero
    change (pref C (k+1) z).getD (n+k) false ≠ (pref C (k+1) y).getD (n+k) false at h
    have bits : (pref C (k+1) zero).getD (n+k) false = false ∧
                (pref C (k+1) z).getD (n+k) false = true := by
      exact (show ∀ (b c d : Bool), b ≤ c → c ≤ d → d ≠ c → b = false ∧ d = true by decide) _ _ _ hzero hy h
    have good (v : Fin n → Bool) : (C.wires (List.ofFn v)).getD (n+k) false =
        (pref C (k+1) v).getD (n+k) false := by
      rw [← full]
      exact stable C v (by omega) (by omega) _ (by omega)
    constructor
    · refine ⟨?_,z,hz,?_⟩
      · have h0 := (good zero).trans bits.1
        simpa [zero,List.ofFn_const] using h0
      · exact (good z).trans bits.2
    · have h' : k < C.gates.length := hk
      by_contra! hn
      apply h
      rw [next C hk, next C hk]
      simp only [ite_true,eq_self]
      apply congrArg C.gates[k].op.eval
      apply List.map_congr_left
      intro w hw
      by_contra ne
      exact hn w (by
        dsimp only [P]
        rw [dif_pos h']
        apply List.mem_toFinset.mpr
        exact hw) ⟨z,hz,ne⟩
  have covers : ∀ c ∈ X, ∃ w ∈ ({C.output} : Finset ℕ), d C.size c w := by
    intro c hc
    obtain ⟨z,hz,h⟩ := piv c hc
    refine ⟨_,Finset.mem_singleton_self _,z,hz,?_⟩
    simpa only [full,circuitFun,Circuit.eval] using h
  have b := frontier C.size X d a P count base old fresh C.size le_rfl {C.output} covers
  rw [finCard (m:=C.size) a] at b
  simpa only [Finset.card_singleton,Nat.add_comm 1] using b

end PEqualNP.Outside.L_meta_5218_aux

theorem PEqualNP.Outside.L_meta_5218 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 → Bool)) (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ x6 ∈ x4, ∃ x8 ∈ x3, PEqualNP.MetaComplexity.circuitFun x1 x2 x8 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x6 Bool.false)) → x4.card ≤ Fintype.card { x7 : Fin x2.size // (x2.wires (List.replicate x1 Bool.false)).getD (x1 + ↑x7) Bool.false = Bool.false ∧ ∃ x8 ∈ x3, PEqualNP.EdgeOwnership.gateVal x1 x2 (↑x7) x8 = Bool.true } + (1 : ℕ) := by
  exact fun _ C F X h hp => PEqualNP.Outside.L_meta_5218_aux.solve C F X h hp
