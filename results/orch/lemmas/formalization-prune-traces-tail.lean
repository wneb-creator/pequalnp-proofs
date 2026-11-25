namespace PEqualNP.Outside.L_meta_6659_aux

def MarkedTrace (n : ℕ) (D : Dag) (base : Fin n → Bool)
    (v : Fin n) (d : ℕ → Bool) : Prop :=
  (∀ i : Fin n, d i.val = decide (i = v)) ∧
  ∀ j, j < D.length → d (n + j) = if tag D j then
    (val D base (opA D j) && d (opB D j)) ||
      (d (opA D j) && val D base (opB D j))
    else d (opA D j) || d (opB D j)

lemma delete_dead_trace {n : ℕ} {D : Dag} (hS : Strict n D)
    (j : ℕ) (hj : j < D.length) (dead : fanout D (n+j) = 0)
    {base : Fin n → Bool} {v : Fin n} {d : ℕ → Bool}
    (trace : MarkedTrace n D base v d) :
    MarkedTrace n (na_del n j D) base v (fun w => d (na_up (n+j) w)) := by
  refine ⟨?_,?_⟩
  · intro i
    have eq : na_up (n+j) i.val = i.val := by unfold na_up; split_ifs <;> omega
    dsimp only
    rw [eq]
    exact trace.1 i
  · intro k hk
    have hlen := na_del_length n j D hj
    have hk' : na_up j k < D.length := by rw [hlen] at hk; unfold na_up; split_ifs <;> omega
    obtain ⟨et,ea,eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra,rb⟩ := na_no_reader dead _ hk'
    have e1 : na_up (n+j) (n+k) = n+na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n+j → na_up (n+j) (na_sh (n+j) a) = a := by
      intro a ha
      unfold na_up na_sh
      split_ifs <;> omega
    obtain ⟨ha,hb,_⟩ := na_del_strict hS j hj dead k hk
    have va := na_del_val hS j hj dead base (opA (na_del n j D) k) (by rw [hlen] at hk; omega)
    have vb := na_del_val hS j hj dead base (opB (na_del n j D) k) (by rw [hlen] at hk; omega)
    dsimp only
    rw [e1,va,vb,et,ea,eb,e2 _ ra,e2 _ rb]
    exact trace.2 _ hk'

theorem prune_live_traces_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        (∀ x : Fin n → Bool, val D' x (outW n D') = F x) ∧
         ∃ ρ : ℕ → ℕ, ρ (outW n D') = outW n D ∧
           ∀ base v d, MarkedTrace n D base v d →
             MarkedTrace n D' base v (fun w => d (ρ w)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD, id, rfl, fun _ _ _ ht => ht⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3, ρ, hρ, transport⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        refine ⟨D', h1, by omega, h3, (fun w => na_up (n+j) (ρ w)), ?_, ?_⟩
        · dsimp only
          rw [hρ]
          have ho : outW n (na_del n j D) = n + (D.length-1)-1 := by unfold outW; rw [hl]
          rw [ho]
          unfold na_up outW
          split_ifs <;> omega
        · intro base v d ht
          exact transport base v (fun w => d (na_up (n+j) w))
            (delete_dead_trace hS j hj hf0 ht)


lemma take_trace {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) (hk : k ≤ D.length)
    {base : Fin n → Bool} {v : Fin n} {d : ℕ → Bool}
    (trace : MarkedTrace n D base v d) : MarkedTrace n (D.take k) base v d := by
  refine ⟨trace.1,?_⟩
  intro j hj
  have hjk : j < k := by simpa only [List.length_take,Nat.min_eq_left hk] using hj
  have hjD : j < D.length := lt_of_lt_of_le hjk hk
  have eq : (D.take k).getD j (false,0,0) = D.getD j (false,0,0) := by
    simp [List.getD_eq_getElem?_getD,hjk]
  have et : tag (D.take k) j = tag D j := congrArg (fun g => g.1) eq
  have ea : opA (D.take k) j = opA D j := congrArg (fun g => g.2.1) eq
  have eb : opB (D.take k) j = opB D j := congrArg (fun g => g.2.2) eq
  obtain ⟨ha,hb,_⟩ := hS j hjD
  rw [et,ea,eb,val_take D base k _ (by omega) hk,val_take D base k _ (by omega) hk]
  exact trace.2 j hjD

theorem strict_live_preserves_traces {n : ℕ} (F : (Fin n → Bool) → Bool)
    (D : Dag) (o : ℕ) (hS : Strict n D)
    (hD : ∀ x, val D x o = F x)
    (hnc : ∀ b : Bool, ∃ x, F x ≠ b)
    (hnp : ∀ i : Fin n, ∃ x, F x ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∃ E : Dag, StrictLive n E ∧ E.length ≤ D.length ∧
      (∀ x, val E x (outW n E) = F x) ∧
      ∃ ρ : ℕ → ℕ, ρ (outW n E) = o ∧
        ∀ base v d, MarkedTrace n D base v d →
          MarkedTrace n E base v (fun w => d (ρ w)) := by
  obtain ⟨x, hx⟩ := hnc false
  have ho : o < n + D.length := by
    by_contra hn
    exact hx ((hD x).symm.trans (val_ge D x o (by omega)))
  have hon : n ≤ o := by
    by_contra hn
    have hi : o < n := by omega
    obtain ⟨y, hy⟩ := hnp ⟨o, hi⟩
    exact hy ((hD y).symm.trans (val_input D y o hi))
  have hne : D ≠ [] := by
    intro he
    have hz : D.length = 0 := by rw [he]; rfl
    omega
  let k := o - n + 1
  have hk : k ≤ D.length := by dsimp [k]; omega
  have hlen : (D.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk]
  have hneTake : D.take k ≠ [] := by
    intro he
    have hz : (D.take k).length = 0 := by rw [he]; rfl
    rw [hlen] at hz
    dsimp [k] at hz
    omega
  have hev : ∀ y, val (D.take k) y (outW n (D.take k)) = F y := by
    intro y
    have hout : outW n (D.take k) = o := by
      unfold outW
      rw [hlen]
      dsimp [k]
      omega
    rw [hout, val_take D y k o (by dsimp [k]; omega) hk]
    exact hD y
  obtain ⟨E,live,size,correct,ρ,out,transport⟩ := prune_live_traces_aux F hess k (D.take k) hlen
    (na_strict_take hS k) hneTake hev
  refine ⟨E,live,size.trans hk,correct,ρ,?_,?_⟩
  · rw [out]
    unfold outW
    rw [hlen]
    dsimp [k]
    omega
  · intro base v d trace
    exact transport base v d (take_trace hS k hk trace)

end PEqualNP.Outside.L_meta_6659_aux
