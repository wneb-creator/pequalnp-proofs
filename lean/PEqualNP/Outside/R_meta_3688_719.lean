import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3688_719
    (hNorm : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsAO2 x1 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x2 x8 ∧ PEqualNP.TopForm.TopForm x2 x8 ∧ x8.size ≤ x4.size)
    (hLedger : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
      x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card +
        (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ≤
        x4.size + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) ∧
      ∀ (x9 : Finset (Fin x1)),
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (x2.deleteEdges ↑(PEqualNP.TopForm.Ustar x2 x4)) x9 →
        x9.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card)
    (hNoOneJunk : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit)
      (x5 : Fin x1 → Bool),
      (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x5 x6 ≠ x5 x7) →
      PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 →
      (PEqualNP.TopForm.junk x2 x4).card ≠ (1 : ℕ))
    (hResidual : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin (n + n)))
      [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      n < E.card ∧
      (∀ u v, G.Adj u v ↔ ∃ a b : Fin n, (a, b) ∈ E ∧
        ((u = Fin.castAdd n a ∧ v = Fin.natAdd n b) ∨ (v = Fin.castAdd n a ∧ u = Fin.natAdd n b))) ∧
      PEqualNP.TopForm.NoFourCycle G ∧
      (∀ i : Fin n, (i, σ i) ∈ E) ∧
      PEqualNP.TopForm.IsLeastAO G D ∧
      PEqualNP.TopForm.TopForm G D ∧
      D.size + 1 < E.card + n ∧
      2 ≤ (PEqualNP.TopForm.junk G D).card ∧
      4 ≤ 2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card +
        (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ∧
      3 ≤ (PEqualNP.TopForm.Ustar G D).card ∧
      2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card +
        (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card <
        (PEqualNP.TopForm.Ustar G D).card +
          (PEqualNP.TopForm.Ustar G D ∩ Finset.univ.image (fun i : Fin n => s(Fin.castAdd n i, Fin.natAdd n (σ i)))).card ∧
      (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card +
        2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card +
        (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card < n + (PEqualNP.TopForm.Ustar G D).card →
      False) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro n E σ C hdense _ hrect hmatch hAO hcomp
  let m : ℕ := n + n
  let L : Fin n → Fin m := Fin.castAdd n
  let R : Fin n → Fin m := Fin.natAdd n
  have hLinj : Function.Injective L := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin m => x.val) h)
  have hRinj : Function.Injective R := by
    intro i j h
    have hv := congrArg Fin.val h
    change n + i.val = n + j.val at hv
    exact Fin.ext (by omega)
  have hLR : ∀ i j : Fin n, L i ≠ R j := by
    intro i j h
    have hv := congrArg Fin.val h
    change i.val = n + j.val at hv
    have := i.isLt
    omega
  have hparts : ∀ w : Fin m, (∃ i : Fin n, w = L i) ∨ (∃ j : Fin n, w = R j) :=
    fun w => Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) w
  let arc : Fin m → Fin m → Prop := fun u v =>
    ∃ a b : Fin n, (a, b) ∈ E ∧ u = L a ∧ v = R b
  let G : SimpleGraph (Fin m) := SimpleGraph.fromRel arc
  have hadj : ∀ u v : Fin m, G.Adj u v ↔
      ∃ a b : Fin n, (a, b) ∈ E ∧ ((u = L a ∧ v = R b) ∨ (v = L a ∧ u = R b)) := by
    intro u v
    change (u ≠ v ∧ (arc u v ∨ arc v u)) ↔ _
    constructor
    · rintro ⟨_, (⟨a, b, hE, hu, hv⟩ | ⟨a, b, hE, hv, hu⟩)⟩
      · exact ⟨a, b, hE, Or.inl ⟨hu, hv⟩⟩
      · exact ⟨a, b, hE, Or.inr ⟨hv, hu⟩⟩
    · rintro ⟨a, b, hE, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact ⟨hLR a b, Or.inl ⟨a, b, hE, rfl, rfl⟩⟩
      · exact ⟨(hLR a b).symm, Or.inr ⟨a, b, hE, rfl, rfl⟩⟩
  have hadjL : ∀ (i : Fin n) (v : Fin m), G.Adj (L i) v ↔ ∃ j : Fin n, (i, j) ∈ E ∧ v = R j := by
    intro i v
    rw [hadj]
    constructor
    · rintro ⟨a, b, hE, (⟨hi, hv⟩ | ⟨_, hi⟩)⟩
      · have heq := hLinj hi
        subst a
        exact ⟨b, hE, hv⟩
      · exact False.elim (hLR i b hi)
    · rintro ⟨j, hj, rfl⟩
      exact ⟨i, j, hj, Or.inl ⟨rfl, rfl⟩⟩
  have hadjR : ∀ (j : Fin n) (u : Fin m), G.Adj (R j) u ↔ ∃ i : Fin n, (i, j) ∈ E ∧ u = L i := by
    intro j u
    rw [hadj]
    constructor
    · rintro ⟨a, b, hE, (⟨hj, _⟩ | ⟨hu, hj⟩)⟩
      · exact False.elim (hLR a j hj.symm)
      · have heq := hRinj hj
        subst b
        exact ⟨a, hE, hu⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, j, hi, Or.inr ⟨rfl, rfl⟩⟩
  have hconn : ∀ {i j : Fin n}, (i, j) ∈ E → G.Adj (L i) (R j) :=
    fun h => (hadjL _ _).mpr ⟨_, h, rfl⟩
  let col : Fin m → Bool := fun u => decide (n ≤ u.val)
  have hcolL : ∀ i : Fin n, col (L i) = false := by
    intro i
    change decide (n ≤ i.val) = false
    exact decide_eq_false (Nat.not_le_of_lt i.isLt)
  have hcolR : ∀ j : Fin n, col (R j) = true := by
    intro j
    change decide (n ≤ n + j.val) = true
    exact decide_eq_true (Nat.le_add_right n j.val)
  have hbip : ∀ u v : Fin m, G.Adj u v → col u ≠ col v := by
    intro u v h
    rcases (hadj u v).mp h with ⟨a, b, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · rw [hcolL, hcolR]; exact Bool.false_ne_true
    · rw [hcolR, hcolL]; exact fun h' => Bool.noConfusion h'
  have h4 : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    by_contra huv
    rcases hparts a with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨k, hik, rfl⟩ := (hadjL i u).mp hu'.1
      obtain ⟨l, hil, rfl⟩ := (hadjL i v).mp hv'.1
      obtain ⟨t, htk, rfl⟩ := (hadjR k b).mp hu'.2.symm
      obtain ⟨s, hsl, he⟩ := (hadjR l (L t)).mp hv'.2.symm
      have hts := hLinj he
      subst s
      exact hrect i t k l (fun eq => hab (congrArg L eq))
        (fun eq => huv (congrArg R eq)) ⟨hik, hil, htk, hsl⟩
    · obtain ⟨k, hkj, rfl⟩ := (hadjR j u).mp hu'.1
      obtain ⟨l, hlj, rfl⟩ := (hadjR j v).mp hv'.1
      obtain ⟨t, hkt, rfl⟩ := (hadjL k b).mp hu'.2.symm
      obtain ⟨s, hls, he⟩ := (hadjL l (R t)).mp hv'.2.symm
      have hts := hRinj he
      subst s
      exact hrect k l j t (fun eq => huv (congrArg L eq))
        (fun eq => hab (congrArg R eq)) ⟨hkj, hkt, hlj, hls⟩
  have graphFun_def : ∀ (x : Fin m → Bool),
      graphFun G ∅ x = (decide (∃ a ∈ (∅ : Finset (Fin m)), x a = true) ||
        decide (∃ u v : Fin m, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  have hGraph : circuitFun m C = graphFun G ∅ := by
    funext x
    rw [hcomp x, graphFun_def x]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    congr 1
    apply propext
    constructor
    · rintro ⟨a, b, hE, ha, hb⟩
      exact ⟨L a, R b, hconn hE, ha, hb⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (hadj u v).mp huv with ⟨a, b, hE, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact ⟨a, b, hE, hu, hv⟩
      · exact ⟨a, b, hE, hv, hu⟩
  have hEdgeCard : G.edgeFinset.card = E.card := by
    let f : Fin n × Fin n → Sym2 (Fin m) := fun e => s(L e.1, R e.2)
    have hf : Function.Injective f := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
      rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, _⟩
      · exact Prod.ext (hLinj hl) (hRinj hr)
      · exact False.elim (hLR _ _ hl)
    have hEq : G.edgeFinset = E.image f := by
      ext e
      refine Sym2.inductionOn e ?_
      intro u v
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, hadj]
      constructor
      · rintro ⟨a, b, hE, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact ⟨(a, b), hE, rfl⟩
        · exact ⟨(a, b), hE, Sym2.eq_swap⟩
      · rintro ⟨⟨a, b⟩, hE, he⟩
        rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · exact ⟨a, b, hE, Or.inl ⟨hu.symm, hv.symm⟩⟩
        · exact ⟨a, b, hE, Or.inr ⟨hu.symm, hv.symm⟩⟩
    rw [hEq, Finset.card_image_of_injective _ hf]
  have hEne : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos, hEdgeCard]
    omega
  obtain ⟨D, hLeast, hTop, hDle⟩ := hNorm m G C hEne hAO hGraph
  by_contra hNotBound
  have hSmall : D.size + 1 < E.card + n := by omega
  obtain ⟨hLedIneq, hMinCov⟩ := hLedger m G D h4 hEne hLeast hTop
  let M : Finset (Sym2 (Fin m)) := Finset.univ.image (fun i : Fin n => s(L i, R (σ i)))
  let H : SimpleGraph (Fin m) := G.deleteEdges ↑(Ustar G D)
  let covers : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun T : Finset (Fin m) => ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T)
  have hCoversNe : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u _ _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨T0, hT0mem, hT0min⟩ := Finset.exists_min_image covers Finset.card hCoversNe
  have hT0cov : ∀ u v : Fin m, H.Adj u v → u ∈ T0 ∨ v ∈ T0 := (Finset.mem_filter.mp hT0mem).2
  have hIsMinT0 : IsMinCover H T0 := by
    refine ⟨hT0cov, ?_⟩
    intro T' hT'
    exact hT0min T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)
  have hT0leTops : T0.card ≤ (tops G D \ centreless G D).card := hMinCov T0 hIsMinT0
  have hMatchSub : n - (Ustar G D ∩ M).card ≤ T0.card := by
    let hit : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => s(L i, R (σ i)) ∈ Ustar G D)
    let miss : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => s(L i, R (σ i)) ∉ Ustar G D)
    have hMmap : ∀ i j : Fin n, s(L i, R (σ i)) = s(L j, R (σ j)) → i = j := by
      intro i j h
      rcases Sym2.eq_iff.mp h with ⟨hl, _⟩ | ⟨hl, _⟩
      · exact hLinj hl
      · exact False.elim (hLR _ _ hl)
    have hHitCard : hit.card = (Ustar G D ∩ M).card := by
      have hEq : Ustar G D ∩ M = hit.image (fun i : Fin n => s(L i, R (σ i))) := by
        ext e
        rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image]
        constructor
        · rintro ⟨heU, i, _, rfl⟩
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heU⟩, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨(Finset.mem_filter.mp hi).2, i, Finset.mem_univ _, rfl⟩
      rw [hEq, Finset.card_image_of_injective _ hMmap]
    have hPartCard : hit.card + miss.card = n := by
      have hdisj : Disjoint hit miss := by
        rw [Finset.disjoint_left]
        intro i hi hm
        exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hi).2
      have hunion : hit ∪ miss = Finset.univ := by
        ext i
        rw [Finset.mem_union]
        change (i ∈ Finset.univ.filter (fun i : Fin n => s(L i, R (σ i)) ∈ Ustar G D) ∨
          i ∈ Finset.univ.filter (fun i : Fin n => s(L i, R (σ i)) ∉ Ustar G D)) ↔ i ∈ Finset.univ
        rw [Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun _ => Finset.mem_univ _, fun h => (em (s(L i, R (σ i)) ∈ Ustar G D)).imp (And.intro h) (And.intro h)⟩
      have := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at this
      exact this.symm
    let pick : Fin n → Fin m := fun i => if L i ∈ T0 then L i else R (σ i)
    have hPickInj : Function.Injective pick := by
      intro i j h
      by_cases hi : L i ∈ T0 <;> by_cases hj : L j ∈ T0
      · exact hLinj (by simpa [pick, hi, hj] using h)
      · exact False.elim (hLR i (σ j) (by simpa [pick, hi, hj] using h))
      · exact False.elim ((hLR j (σ i)).symm (by simpa [pick, hi, hj] using h))
      · exact σ.injective (hRinj (by simpa [pick, hi, hj] using h))
    have hMissSub : miss.image pick ⊆ T0 := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      have hnotU : s(L i, R (σ i)) ∉ Ustar G D := (Finset.mem_filter.mp hi).2
      have hHadj : H.Adj (L i) (R (σ i)) := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hconn (hmatch i), Finset.mem_coe.not.mpr hnotU⟩
      by_cases hLmem : L i ∈ T0
      · simp [pick, hLmem]
      · have hRmem : R (σ i) ∈ T0 := (hT0cov _ _ hHadj).resolve_left hLmem
        simpa [pick, hLmem] using hRmem
    have hMissLe : miss.card ≤ T0.card := by
      have h := Finset.card_le_card hMissSub
      rwa [Finset.card_image_of_injective _ hPickInj] at h
    omega
  have hDeficit :
      (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
        (orN G D \ lam G D).card < n + (Ustar G D).card := by
    rw [hEdgeCard] at hLedIneq
    omega
  have hBudgetLt :
      2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card <
        (Ustar G D).card + (Ustar G D ∩ M).card := by
    omega
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  let stepWire : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_def : ∀ (C' : Circuit) (x : List Bool), C'.wires x = C'.gates.foldl stepWire x :=
    fun _ _ => rfl
  have size_def : ∀ (C' : Circuit), C'.size = C'.gates.length := fun _ => rfl
  have eval_def : ∀ (C' : Circuit) (x : List Bool), C'.eval x = (C'.wires x).getD C'.output false :=
    fun _ _ => rfl
  have circuitFun_def : ∀ (C' : Circuit) (x : Fin m → Bool),
      circuitFun m C' x = (C'.wires (List.ofFn x)).getD C'.output false := fun _ _ => rfl
  have gateAt_def : ∀ (C' : Circuit) (j : ℕ), gateAt C' j = C'.gates.getD j ⟨GateOp.or, []⟩ :=
    fun _ _ => rfl
  have gateVal_def : ∀ (C' : Circuit) (j : ℕ) (x : Fin m → Bool),
      gateVal m C' j x = (C'.wires (List.ofFn x)).getD (m + j) false := fun _ _ _ => rfl
  have opnd_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      opnd C' a b = (gateAt C' a).inputs.getD b.val 0 := fun _ _ _ => rfl
  have pairInput_def : ∀ (u v w : Fin m), pairInput u v w = decide (w = u ∨ w = v) :=
    fun _ _ _ => rfl
  have coneStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep m cs g = cs ++ [(g.inputs.filter (fun w => decide (m ≤ w ∧ w < m + cs.length))).flatMap
        (fun w => (w - m) :: cs.getD (w - m) [])] := by
    intro cs g
    change cs ++ [(g.inputs.filter (fun w => @decide (m ≤ w ∧ w < m + cs.length) _)).flatMap
      (fun w => (w - m) :: cs.getD (w - m) [])] = _
    congr 2
  have cones_def : ∀ (C' : Circuit), cones m C' = C'.gates.foldl (coneStep m) [] := fun _ => rfl
  have inCone_def : ∀ (C' : Circuit) (i j : ℕ), InCone m C' i j = (i ∈ (cones m C').getD j []) :=
    fun _ _ _ => rfl
  have orStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      orStep m cs g = cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (m ≤ w ∧ w < m + cs.length))).flatMap
          (fun w => cs.getD (w - m) [])
        else [])] := by
    intro cs g
    change cs ++ [cs.length :: (@ite _ (g.op = GateOp.or) (gateOpDecEq g.op GateOp.or)
      ((g.inputs.filter (fun w => @decide (m ≤ w ∧ w < m + cs.length) _)).flatMap
        (fun w => cs.getD (w - m) [])) [])] = _
    by_cases hop : g.op = GateOp.or
    · rw [ite_eq_left hop]
    · rw [ite_eq_right hop]
  have orSets_def : ∀ (C' : Circuit), orSets m C' = C'.gates.foldl (orStep m) [] := fun _ => rfl
  have orReaches_def : ∀ (C' : Circuit) (w g : ℕ),
      OrReaches m C' w g = (m ≤ w ∧ g ∈ (orSets m C').getD (w - m) []) := fun _ _ _ => rfl
  have orIn_def : ∀ (C' : Circuit) (w : ℕ) (i : Fin m),
      i ∈ orIn m C' w ↔ ((i : ℕ) = w ∨ ∃ k < C'.gates.length,
        OrReaches m C' w k ∧ (gateAt C' k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C' k).inputs) := by
    intro C' w i
    exact (@Finset.mem_filter _ _ _ Finset.univ i).trans (by simp only [Finset.mem_univ, true_and])
  have side_def : ∀ (C' : Circuit) (a : ℕ) (b : Fin 2),
      side (n := m) C' a b = orIn m C' (opnd C' a b) := fun _ _ _ => rfl
  have tops_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ tops G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧ BelowF G C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have junk_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ junk G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.and ∧
        ∃ x : Fin m → Bool, gateVal m C' j x = true ∧ graphFun G ∅ x = false := by
    intro C' j
    refine (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans ?_
    rw [Finset.mem_range]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.1, h.2.2⟩⟩
  have orN_mem : ∀ (C' : Circuit) (j : ℕ),
      j ∈ orN G C' ↔ j < C'.gates.length ∧ (gateAt C' j).op = GateOp.or ∧ ¬ BelowF G C' j := by
    intro C' j
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) j).trans (by rw [Finset.mem_range])
  have lam_mem : ∀ (C' : Circuit) (h : ℕ),
      h ∈ lam G C' ↔ h ∈ orN G C' ∧ (orIn m C' (opnd C' h 0)).Nonempty ∧
        (orIn m C' (opnd C' h 1)).Nonempty ∧ ∃ a ∈ tops G C', ∃ b : Fin 2,
          (side (n := m) C' a (1 - b)).card = 1 ∧ OrReaches m C' (opnd C' a b) h := by
    intro C' h
    exact @Finset.mem_filter _ _ _ (orN G C') h
  have centreless_mem : ∀ (C' : Circuit) (a : ℕ),
      a ∈ centreless G C' ↔ a ∈ tops G C' ∧ (side (n := m) C' a 0 = ∅ ∨ side (n := m) C' a 1 = ∅) := by
    intro C' a
    exact @Finset.mem_filter _ _ _ (tops G C') a
  have readers_mem : ∀ (C' : Circuit) (j k : ℕ),
      k ∈ readers m C' j ↔ k < C'.gates.length ∧ m + j ∈ (gateAt C' k).inputs := by
    intro C' j k
    exact (@Finset.mem_filter _ _ _ (Finset.range C'.gates.length) k).trans (by rw [Finset.mem_range])
  have starEdges_def : ∀ (C' : Circuit),
      starEdges G C' = (tops G C').biUnion (fun a => (side (n := m) C' a 0 ×ˢ side (n := m) C' a 1).image (fun p => s(p.1, p.2))) :=
    fun _ => rfl
  have Ustar_def : ∀ (C' : Circuit), Ustar G C' = G.edgeFinset \ starEdges G C' := fun _ => rfl
  have foldl_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro _ _ _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp only [stepWire, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp only [stepWire, List.length_append, List.length_singleton]; omega)]
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp only [stepWire, List.length_append, List.length_singleton]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  let val : Circuit → List Bool → ℕ → Bool := fun C' x u => (C'.wires x).getD u false
  have gateAt_eq : ∀ {C' : Circuit} {j : ℕ} (hj : j < C'.gates.length), gateAt C' j = C'.gates[j] := by
    intro C' j hj
    rw [gateAt_def]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have gateAt_mem : ∀ {C' : Circuit} {j : ℕ}, j < C'.gates.length → gateAt C' j ∈ C'.gates := by
    intro C' j hj
    rw [gateAt_eq hj]
    exact List.getElem_mem hj
  have val_input : ∀ {C' : Circuit} {x : List Bool}, x.length = m → ∀ {u : ℕ}, u < m →
      val C' x u = x.getD u false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = _
    rw [wires_def]
    exact foldl_getD_lt _ _ _ (by omega)
  have val_ge : ∀ {C' : Circuit} {x : List Bool}, x.length = m → ∀ {u : ℕ}, m + C'.gates.length ≤ u →
      val C' x u = false := by
    intro C' x hx u hu
    change (C'.wires x).getD u false = false
    apply getD_ge
    rw [wires_def, foldl_length]
    omega
  have val_gate : ∀ {C' : Circuit} {x : List Bool}, x.length = m → ∀ {j : ℕ}, j < C'.gates.length →
      val C' x (m + j) = (gateAt C' j).op.eval ((gateAt C' j).inputs.map fun i =>
        if i < m + j then val C' x i else false) := by
    intro C' x hx j hj
    rw [← hx]
    change (C'.wires x).getD (x.length + j) false = _
    rw [wires_def, gateAt_eq hj]
    exact foldl_getD_gate C'.gates x j hj
  have val_or : ∀ {C' : Circuit} {x : List Bool}, x.length = m → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.or →
      (val C' x (m + r) = true ↔ ∃ i ∈ (gateAt C' r).inputs, i < m + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_or]
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < m + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; exact Bool.noConfusion h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
  have val_and : ∀ {C' : Circuit} {x : List Bool}, x.length = m → ∀ {r : ℕ}, r < C'.gates.length →
      (gateAt C' r).op = GateOp.and →
      (val C' x (m + r) = true ↔ ∀ i ∈ (gateAt C' r).inputs, i < m + r ∧ val C' x i = true) := by
    intro C' x hx r hr hop
    rw [val_gate hx hr, hop, eval_and]
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < m + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; exact Bool.noConfusion h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2
  have val_ofFn : ∀ (C' : Circuit) (x : Fin m → Bool) (u : Fin m),
      val C' (List.ofFn x) u.val = x u := by
    intro C' x u
    rw [val_input (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]
  have gateVal_eq_val : ∀ (C' : Circuit) (j : ℕ) (x : Fin m → Bool),
      gateVal m C' j x = val C' (List.ofFn x) (m + j) := fun _ _ _ => rfl
  let shiftW : ℕ → ℕ → ℕ := fun k w => if w < m + k then w else w - 1
  let unshiftW : ℕ → ℕ → ℕ := fun k w => if w < m + k then w else w + 1
  let unshiftG : ℕ → ℕ → ℕ := fun k j => if j < k then j else j + 1
  let shiftGate : ℕ → Gate → Gate := fun k g => ⟨g.op, g.inputs.map (shiftW k)⟩
  let delDead : ℕ → Circuit → Circuit := fun k C' =>
    ⟨(C'.gates.eraseIdx k).map (shiftGate k), shiftW k C'.output⟩
  have unshiftW_shiftW : ∀ (k w : ℕ), w ≠ m + k → unshiftW k (shiftW k w) = w := by
    intro k w hne
    dsimp only [unshiftW, shiftW]
    split_ifs <;> omega
  have delDead_length : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      (delDead k C').gates.length = C'.gates.length - 1 := by
    intro k C' hk
    dsimp only [delDead]
    rw [List.length_map, List.length_eraseIdx_of_lt hk]
  have delDead_gateAt : ∀ (k : ℕ) (C' : Circuit), k < C'.gates.length →
      ∀ j, j < (delDead k C').gates.length →
      gateAt (delDead k C') j = shiftGate k (gateAt C' (unshiftG k j)) := by
    intro k C' hk j hj
    have hj_lt : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj_e : j < (C'.gates.eraseIdx k).length := by rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
    rw [gateAt_eq hj]
    dsimp only [delDead, unshiftG]
    rw [List.getElem_map]
    split_ifs with hjk
    · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (by omega)]
    · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (by omega)]
  have delDead_readsBack : ∀ (k : ℕ) (C' : Circuit), ReadsBack m C' →
      k < C'.gates.length → (∀ j < C'.gates.length, m + k ∉ (gateAt C' j).inputs) →
      ReadsBack m (delDead k C') := by
    intro k C' hRB hk hno j hj w' hw'
    rw [delDead_gateAt k C' hk j hj] at hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    have hj_len : j < C'.gates.length - 1 := by rw [← delDead_length k C' hk]; exact hj
    have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
    have hw_lt : w < m + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
    have hw_ne : w ≠ m + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
    dsimp only [shiftW]
    dsimp only [unshiftG] at hw_lt
    split_ifs at hw_lt ⊢ <;> omega
  have delDead_ao2 : ∀ (k : ℕ) (C' : Circuit), IsAO2 m C' →
      k < C'.gates.length → (∀ j < C'.gates.length, m + k ∉ (gateAt C' j).inputs) →
      IsAO2 m (delDead k C') := by
    intro k C' h hk hno
    have mapped : ∀ g ∈ (delDead k C').gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hm := List.mem_of_mem_eraseIdx hg'
      exact ⟨h.1 g' hm, by dsimp only [shiftGate]; rw [List.length_map]; exact h.2.2 g' hm⟩
    exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack k C' h.2.1 hk hno,
      fun g hg => (mapped g hg).2⟩
  have delDead_wires_eq : ∀ (k : ℕ) (C' : Circuit) (l : List Bool), l.length = m →
      ReadsBack m C' → k < C'.gates.length → (∀ j < C'.gates.length, m + k ∉ (gateAt C' j).inputs) →
      ∀ w : ℕ, val (delDead k C') l w = val C' l (unshiftW k w) := by
    intro k C' l hl hRB hk hno w
    have hRB' : ReadsBack m (delDead k C') := delDead_readsBack k C' hRB hk hno
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw_oob : m + (delDead k C').gates.length ≤ w
      · have hdl := delDead_length k C' hk
        have huw : m + C'.gates.length ≤ unshiftW k w := by dsimp only [unshiftW]; split_ifs <;> omega
        rw [val_ge hl hw_oob, val_ge hl huw]
      · by_cases hwm : w < m
        · have huw : unshiftW k w = w := by dsimp only [unshiftW]; split_ifs <;> omega
          rw [huw, val_input hl hwm, val_input hl hwm]
        · let j := w - m
          have hw_eq : w = m + j := by omega
          have hj_lt : j < (delDead k C').gates.length := by omega
          have hdl := delDead_length k C' hk
          have hj0_lt : unshiftG k j < C'.gates.length := by dsimp only [unshiftG]; split_ifs <;> omega
          have huw : unshiftW k (m + j) = m + unshiftG k j := by
            dsimp only [unshiftW, unshiftG]; split_ifs <;> omega
          rw [hw_eq, huw, val_gate hl hj_lt, val_gate hl hj0_lt, delDead_gateAt k C' hk j hj_lt]
          dsimp only [shiftGate]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hu_lt' : shiftW k u < m + j := by
            have hmem : shiftW k u ∈ (gateAt (delDead k C') j).inputs := by
              rw [delDead_gateAt k C' hk j hj_lt]
              exact List.mem_map.mpr ⟨u, hu, rfl⟩
            exact hRB' j hj_lt (shiftW k u) hmem
          have hu_lt0 : u < m + unshiftG k j := hRB (unshiftG k j) hj0_lt u hu
          have hu_ne : u ≠ m + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
          simp only [Function.comp_apply]
          rw [if_pos hu_lt', if_pos hu_lt0, ih (shiftW k u) (by omega), unshiftW_shiftW k u hu_ne]
  have leastRead : ∀ {j : ℕ}, j < D.gates.length → ¬ BelowF G D j → (readers m D j).Nonempty := by
    intro j hj hd
    have hout : D.output ≠ m + j := by
      intro heq
      apply hd
      intro x hx
      have h : val D (List.ofFn x) D.output = graphFun G ∅ x := congrFun hLeast.2.1 x
      rw [heq] at h
      exact h.symm.trans hx
    by_contra hnot
    have hno : ∀ k < D.gates.length, m + j ∉ (gateAt D k).inputs := by
      intro k hk hin
      exact hnot ⟨k, (readers_mem D j k).mpr ⟨hk, hin⟩⟩
    have heq : circuitFun m (delDead j D) = circuitFun m D := by
      funext x
      rw [circuitFun_def, circuitFun_def]
      change val (delDead j D) (List.ofFn x) (shiftW j D.output) = val D (List.ofFn x) D.output
      rw [delDead_wires_eq j D (List.ofFn x) List.length_ofFn hLeast.1.2.1 hj hno,
        unshiftW_shiftW j D.output hout]
    have hle := hLeast.2.2 (delDead j D) (delDead_ao2 j D hLeast.1 hj hno) (heq.trans hLeast.2.1)
    have hlen := delDead_length j D hj
    rw [size_def, size_def] at hle
    omega
  let OrStep : ℕ → ℕ → Prop := fun w w' =>
    ∃ k, k < D.gates.length ∧ w = m + k ∧ (gateAt D k).op = GateOp.or ∧
      w' ∈ (gateAt D k).inputs ∧ w' < m + k
  have orStep_up : ∀ {x : List Bool}, x.length = m → ∀ {w w' : ℕ},
      Relation.ReflTransGen OrStep w w' → val D x w' = true → val D x w = true := by
    intro x hx w w' h hv
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hstep _ ih =>
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
  have or_trace : ∀ {x : List Bool}, x.length = m → ∀ w : ℕ, val D x w = true →
      ∃ w', Relation.ReflTransGen OrStep w w' ∧ val D x w' = true ∧
        (w' < m ∨ ∃ h, h < D.gates.length ∧ w' = m + h ∧ (gateAt D h).op ≠ GateOp.or) := by
    intro x hx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hv
      by_cases hw : w < m
      · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
      · by_cases hlen : m + D.gates.length ≤ w
        · rw [val_ge hx hlen] at hv; exact Bool.noConfusion hv
        · obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
          have hk : k < D.gates.length := by omega
          by_cases hop : (gateAt D k).op = GateOp.or
          · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
            obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
            exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
          · exact ⟨m + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
  have pairInput_left : ∀ u v : Fin m, pairInput u v u = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inl rfl)
  have pairInput_right : ∀ u v : Fin m, pairInput u v v = true := by
    intro u v; rw [pairInput_def]; exact decide_eq_true (Or.inr rfl)
  have pairInput_true : ∀ u v w : Fin m, pairInput u v w = true ↔ w = u ∨ w = v := by
    intro u v w; rw [pairInput_def, decide_eq_true_eq]
  have graphFun_pair : ∀ u v : Fin m, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    rw [graphFun_def]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
  have operand_trace : ∀ (u v : Fin m) (p : ℕ), val D (List.ofFn (pairInput u v)) p = true →
      (∃ t : Fin m, (t = u ∨ t = v) ∧ Relation.ReflTransGen OrStep p t.val) ∨
      (∃ h, h < D.gates.length ∧ (gateAt D h).op ≠ GateOp.or ∧
        Relation.ReflTransGen OrStep p (m + h) ∧
        val D (List.ofFn (pairInput u v)) (m + h) = true) := by
    intro u v p hv
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (by simp) p hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · left
      refine ⟨⟨w', hlt⟩, ?_, hr⟩
      have h1 := val_ofFn D (pairInput u v) ⟨w', hlt⟩
      rw [show (⟨w', hlt⟩ : Fin m).val = w' from rfl, hv'] at h1
      exact (pairInput_true u v _).mp h1.symm
    · right
      exact ⟨h, hh, hop, hr, hv'⟩
  have reach_var_val : ∀ (x : Fin m → Bool) (p : ℕ) (t : Fin m),
      Relation.ReflTransGen OrStep p t.val → x t = true → val D (List.ofFn x) p = true :=
    fun x p t hr ht => orStep_up (by simp) hr (by rw [val_ofFn]; exact ht)
  have cones_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep m) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, coneStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have cones_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep m) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, m ≤ w ∧ w < m + j ∧
          (i = w - m ∨ i ∈ (gs.foldl (coneStep m) []).getD (w - m) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep m) []).length = gs.length := by rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep m (gs.foldl (coneStep m) []) g).getD k [] =
            (gs.foldl (coneStep m) []).getD k [] := by
        intro k hk
        rw [coneStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - m) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - m) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep m (gs.foldl (coneStep m) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (m ≤ w ∧ w < m + gs.length))).flatMap
              (fun w => (w - m) :: (gs.foldl (coneStep m) []).getD (w - m) []) := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - m) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - m) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep m (gs.foldl (coneStep m) []) g).getD j [] = [] := by
          rw [coneStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have inCone_iff : ∀ i j : ℕ, InCone m D i j ↔
      j < D.gates.length ∧ ∃ k, k < j ∧ m + k ∈ (gateAt D j).inputs ∧ (i = k ∨ InCone m D i k) := by
    intro i j
    have h := cones_char D.gates i j
    rw [inCone_def, cones_def, gateAt_def, h]
    constructor
    · rintro ⟨h0, w, hw, h1, h2, h3⟩
      refine ⟨h0, w - m, by omega, ?_, ?_⟩
      · have he : m + (w - m) = w := by omega
        rw [he]; exact hw
      · rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (by rw [inCone_def, cones_def]; exact h3)
    · rintro ⟨h0, k, hk, hw, h3⟩
      refine ⟨h0, m + k, hw, by omega, by omega, ?_⟩
      have he : m + k - m = k := by omega
      rw [he]
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (by rw [inCone_def, cones_def] at h3; exact h3)
  have inCone_lt : ∀ {i j : ℕ}, InCone m D i j → i < j := by
    intro i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro h
      obtain ⟨_, k, hk, _, rfl | hic⟩ := (inCone_iff i j).mp h
      · exact hk
      · exact lt_trans (ih k hk hic) hk
  have inCone_trans : ∀ {i j k : ℕ}, InCone m D i j → InCone m D j k → InCone m D i k := by
    intro i j k hij
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hjk
      obtain ⟨hklen, r, hr, hrin, rfl | hjr⟩ := (inCone_iff j k).mp hjk
      · exact (inCone_iff i k).mpr ⟨hklen, j, hr, hrin, Or.inr hij⟩
      · exact (inCone_iff i k).mpr ⟨hklen, r, hr, hrin, Or.inr (ih r hr hjr)⟩
  have inCone_has_reader : ∀ {i j : ℕ}, InCone m D i j → ∃ r ≤ j, r ∈ readers m D i := by
    intro i j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro h
      obtain ⟨hjlen, k, hk, hkin, rfl | hik⟩ := (inCone_iff i j).mp h
      · exact ⟨j, le_refl _, (readers_mem D i j).mpr ⟨hjlen, hkin⟩⟩
      · obtain ⟨r, hrle, hrmem⟩ := ih k hk hik
        exact ⟨r, by omega, hrmem⟩
  have orStep_le : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' → w' ≤ w := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact le_refl _
    | head hstep _ ih =>
      obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
      omega
  have orStep_cone : ∀ {w w' : ℕ}, Relation.ReflTransGen OrStep w w' →
      ∀ k h', w = m + k → w' = m + h' → h' = k ∨ InCone m D h' k := by
    intro w w' h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => intro k h' h1 h2; left; omega
    | @head a c hstep hrest ih =>
      intro k h' h1 h2
      obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
      have hk : k0 = k := by omega
      subst hk
      have hle := orStep_le hrest
      obtain ⟨k1, hk1⟩ : ∃ k1, c = m + k1 := ⟨c - m, by omega⟩
      subst hk1
      right
      exact (inCone_iff h' k0).mpr ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
  have operand_cone : ∀ {a p h : ℕ}, a < D.gates.length → p ∈ (gateAt D a).inputs → p < m + a →
      Relation.ReflTransGen OrStep p (m + h) → InCone m D h a := by
    intro a p h ha hin hp hr
    have hle := orStep_le hr
    obtain ⟨k1, rfl⟩ : ∃ k1, p = m + k1 := ⟨p - m, by omega⟩
    exact (inCone_iff h a).mpr ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
  have orSets_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep m) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih, orStep_def]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (orStep m) []).getD j [] ↔
        j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, m ≤ w ∧ w < m + j ∧
            i ∈ (gs.foldl (orStep m) []).getD (w - m) [])) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (orStep m) []).length = gs.length := by rw [orSets_len]; simp
      have key : ∀ k, k < gs.length →
          (orStep m (gs.foldl (orStep m) []) g).getD k [] =
            (gs.foldl (orStep m) []).getD k [] := by
        intro k hk
        rw [orStep_def]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, h3⟩
          refine ⟨by simp; omega, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
            rw [key (w - m) (by omega)]
            exact h3
        · rintro ⟨_, h3⟩
          refine ⟨h, ?_⟩
          rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
          · exact Or.inl h3
          · rw [key (w - m) (by omega)] at h3
            exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1]
        by_cases hop : g.op = GateOp.or
        · have e2 : (orStep m (gs.foldl (orStep m) []) g).getD gs.length [] =
              gs.length :: (g.inputs.filter (fun w => decide (m ≤ w ∧ w < m + gs.length))).flatMap
                (fun w => (gs.foldl (orStep m) []).getD (w - m) []) := by
            rw [orStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
            · exact ⟨by simp, Or.inl h3⟩
            · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
              rw [key (w - m) (by omega)]
              exact h3
          · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
            · exact Or.inl h3
            · rw [key (w - m) (by omega)] at h3
              exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
        · have e2 : (orStep m (gs.foldl (orStep m) []) g).getD gs.length [] = [gs.length] := by
            rw [orStep_def]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by omega)]
            simp [hlen, hop]
          rw [e2]
          simp only [List.mem_singleton]
          constructor
          · intro h3; exact ⟨by simp, Or.inl h3⟩
          · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
            · exact h3
            · exact False.elim (hop hop2)
      · have e0 : (orStep m (gs.foldl (orStep m) []) g).getD j [] = [] := by
          rw [orStep_def]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩; simp at h0; omega
  have orReaches_iff : ∀ k g : ℕ, OrReaches m D (m + k) g ↔
      k < D.gates.length ∧ (g = k ∨ ((gateAt D k).op = GateOp.or ∧
        ∃ i ∈ (gateAt D k).inputs, i < m + k ∧ OrReaches m D i g)) := by
    intro k g
    have h := orSets_char D.gates g k
    rw [orReaches_def, orSets_def, gateAt_def]
    have e : m + k - m = k := by omega
    rw [e, h]
    constructor
    · rintro ⟨_, hk, h3⟩
      refine ⟨hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
      · exact Or.inl h3
      · exact Or.inr ⟨hop, w, hw, h2, by rw [orReaches_def, orSets_def]; exact ⟨h1, h3⟩⟩
    · rintro ⟨hk, h3⟩
      refine ⟨by omega, hk, ?_⟩
      rcases h3 with h3 | ⟨hop, w, hw, h2, h1⟩
      · exact Or.inl h3
      · rw [orReaches_def, orSets_def] at h1
        exact Or.inr ⟨hop, w, hw, h1.1, h2, h1.2⟩
  have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStep w w2 →
      ∀ g, w2 = m + g → g < D.gates.length → OrReaches m D w g := by
    intro w w2 h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro g h1 hg
      subst h1
      exact (orReaches_iff g g).mpr ⟨hg, Or.inl rfl⟩
    | @head a c hstep hrest ih =>
      intro g h1 hg
      obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
      exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
  have orReaches_reach : ∀ (g w : ℕ), OrReaches m D w g →
      Relation.ReflTransGen OrStep w (m + g) ∧ g < D.gates.length := by
    intro g w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h
      rw [orReaches_def] at h
      have hmw : m ≤ w := h.1
      obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
      have h' : OrReaches m D (m + k) g := by rw [orReaches_def]; exact h
      obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h'
      rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
      · exact ⟨Relation.ReflTransGen.refl, hk⟩
      · obtain ⟨hr2, hg⟩ := ih i hlt hr
        exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
  have mem_orIn_reach : ∀ {p : ℕ} (u : Fin m), u ∈ orIn m D p → Relation.ReflTransGen OrStep p u.val := by
    intro p u hu
    rcases (orIn_def D p u).mp hu with h | ⟨k, hk, hr, hop, hin⟩
    · rw [h]
    · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
  have reach_mem_orIn : ∀ {p : ℕ} (u : Fin m), Relation.ReflTransGen OrStep p u.val → u ∈ orIn m D p := by
    intro p u hr
    apply (orIn_def D p u).mpr
    rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
    · exact Or.inl h
    · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
      exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
  have orIn_mono : ∀ {w g : ℕ}, OrReaches m D w g → orIn m D (m + g) ⊆ orIn m D w := by
    intro w g hr u hu
    exact reach_mem_orIn u ((orReaches_reach g w hr).1.trans (mem_orIn_reach u hu))
  have topData : ∀ {a : ℕ}, a ∈ tops G D → a < D.gates.length ∧ (gateAt D a).op = GateOp.and ∧ BelowF G D a :=
    fun ha => (tops_mem D _).mp ha
  have junkData : ∀ {a : ℕ}, a ∈ junk G D →
      a < D.gates.length ∧ (gateAt D a).op = GateOp.and ∧
        ∃ x : Fin m → Bool, gateVal m D a x = true ∧ graphFun G ∅ x = false :=
    fun ha => (junk_mem D _).mp ha
  have binaryInputs : ∀ {a : ℕ}, a < D.gates.length → ∃ p q, (gateAt D a).inputs = [p, q] :=
    fun ha => List.length_eq_two.mp (hLeast.1.2.2 _ (gateAt_mem ha))
  have opndMem : ∀ {a : ℕ}, a < D.gates.length → ∀ b : Fin 2, opnd D a b ∈ (gateAt D a).inputs := by
    intro a ha b
    obtain ⟨p, q, hpq⟩ := binaryInputs ha
    rw [opnd_def, hpq]
    fin_cases b <;> simp
  have opndBound : ∀ {a : ℕ}, a < D.gates.length → ∀ b : Fin 2, opnd D a b < m + a :=
    fun ha b => hLeast.1.2.1 _ ha _ (opndMem ha b)
  have andValBoth : ∀ {a : ℕ}, a < D.gates.length → (gateAt D a).op = GateOp.and →
      ∀ x : Fin m → Bool, gateVal m D a x = true ↔
        val D (List.ofFn x) (opnd D a 0) = true ∧ val D (List.ofFn x) (opnd D a 1) = true := by
    intro a ha hop x
    rw [gateVal_eq_val, val_and (by simp) ha hop]
    constructor
    · intro h
      exact ⟨(h _ (opndMem ha 0)).2, (h _ (opndMem ha 1)).2⟩
    · intro h i hi
      refine ⟨hLeast.1.2.1 a ha i hi, ?_⟩
      obtain ⟨p, q, hpq⟩ := binaryInputs ha
      rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
      · have h0 : opnd D a 0 = i := by rw [opnd_def, hpq]; rfl
        rw [← h0]; exact h.1
      · have e : i = q := List.mem_singleton.mp hq
        subst i
        have h1 : opnd D a 1 = q := by rw [opnd_def, hpq]; rfl
        rw [← h1]; exact h.2
  have andValOperands : ∀ {a : ℕ}, a < D.gates.length → (gateAt D a).op = GateOp.and →
      ∀ x : Fin m → Bool, gateVal m D a x = true ↔ ∀ b : Fin 2, val D (List.ofFn x) (opnd D a b) = true := by
    intro a ha hop x
    rw [andValBoth ha hop]
    constructor
    · intro h b; fin_cases b; exact h.1; exact h.2
    · intro h; exact ⟨h 0, h 1⟩
  have operandReachCone : ∀ {a h : ℕ}, a < D.gates.length → ∀ {b : Fin 2},
      OrReaches m D (opnd D a b) h → InCone m D h a := by
    intro a h ha b hr
    exact operand_cone ha (opndMem ha b) (opndBound ha b) (orReaches_reach h _ hr).1
  have operandOrAndJunk : ∀ {a h : ℕ}, a < D.gates.length → (gateAt D a).op = GateOp.and →
      ∀ {b : Fin 2}, OrReaches m D (opnd D a b) h → (gateAt D h).op = GateOp.and → h ∈ junk G D := by
    intro a h ha hop b hr hh
    have hlen := (orReaches_reach h _ hr).2
    have hnb : ¬ BelowF G D h := fun hb => hTop h hlen a ha hh hb hop (operandReachCone ha hr)
    have hdirty : ∃ x : Fin m → Bool, gateVal m D h x = true ∧ graphFun G ∅ x = false := by
      by_contra hne
      apply hnb
      intro x hx
      by_contra hf
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact (junk_mem D h).mpr ⟨hlen, hh, hdirty⟩
  have inputsAsOpnd : ∀ {k z : ℕ}, k < D.gates.length → z ∈ (gateAt D k).inputs → ∃ b : Fin 2, z = opnd D k b := by
    intro k z hk hz
    obtain ⟨p, q, hpq⟩ := binaryInputs hk
    rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
    · exact ⟨0, by rw [opnd_def, hpq]; rfl⟩
    · have e : z = q := List.mem_singleton.mp hq
      exact ⟨1, by rw [opnd_def, hpq]; exact e⟩
  have sideVal : ∀ {a : ℕ} {b : Fin 2} {x : Fin m → Bool} {t : Fin m},
      t ∈ side (n := m) D a b → x t = true → val D (List.ofFn x) (opnd D a b) = true := by
    intro a b x t ht hx
    rw [side_def] at ht
    exact reach_var_val x _ t (mem_orIn_reach t ht) hx
  have topAdj : ∀ {a : ℕ}, a ∈ tops G D → ∀ {u v : Fin m},
      u ∈ side (n := m) D a 0 → v ∈ side (n := m) D a 1 → G.Adj u v := by
    intro a ha u v hu hv
    obtain ⟨hl, ho, hb⟩ := topData ha
    exact (graphFun_pair u v).mp
      (hb _ ((andValBoth hl ho _).mpr ⟨sideVal hu (pairInput_left u v), sideVal hv (pairInput_right u v)⟩))
  have acceptedTop : ∀ {u v : Fin m}, G.Adj u v → ∃ a ∈ tops G D, gateVal m D a (pairInput u v) = true := by
    intro u v hadj'
    have hout : ∀ x : Fin m → Bool, val D (List.ofFn x) D.output = graphFun G ∅ x :=
      fun x => congrFun hLeast.2.1 x
    have huv : val D (List.ofFn (pairInput u v)) D.output = true := by
      rw [hout]; exact (graphFun_pair u v).mpr hadj'
    rcases operand_trace u v D.output huv with ⟨t, _, hr⟩ | ⟨a, hl, ho, hr, hv⟩
    · exfalso
      have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
      rw [hout] at h1
      exact G.irrefl ((graphFun_pair t t).mp h1)
    · have hand := (hLeast.1.1 _ (gateAt_mem hl)).resolve_right ho
      have hb : BelowF G D a := fun x hx => by
        rw [← hout x]
        exact orStep_up (by simp) hr (gateVal_eq_val D a x ▸ hx)
      exact ⟨a, (tops_mem D a).mpr ⟨hl, hand, hb⟩, hv⟩
  have operandSupport : ∀ {a : ℕ}, a < D.gates.length → (gateAt D a).op = GateOp.and →
      ∀ {b : Fin 2} {u v : Fin m}, val D (List.ofFn (pairInput u v)) (opnd D a b) = true →
      (∃ t ∈ side (n := m) D a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk G D, OrReaches m D (opnd D a b) j ∧ gateVal m D j (pairInput u v) = true := by
    intro a ha ho b u v h
    rcases operand_trace u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
    · exact Or.inl ⟨t, by rw [side_def]; exact reach_mem_orIn t hr, ht⟩
    · have hr' := reach_orReaches hr j rfl hj
      exact Or.inr ⟨j, operandOrAndJunk ha ho hr' ((hLeast.1.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
  have andRawEmpty : ∀ {j : ℕ}, (gateAt D j).op = GateOp.and → orIn m D (m + j) = ∅ := by
    intro j hj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    rcases (orIn_def D (m + j) v).mp hv with he | ⟨k, _, hr, ho, _⟩
    · have := v.isLt; omega
    · rcases (orReaches_iff j k).mp hr with ⟨_, rfl | ⟨hof, _⟩⟩
      · rw [hj] at ho; exact GateOp.noConfusion ho
      · rw [hj] at hof; exact GateOp.noConfusion hof
  have lastOrBefore : ∀ {j w : ℕ}, Relation.ReflTransGen OrStep w (m + j) →
      w = m + j ∨ ∃ r, r < D.gates.length ∧ (gateAt D r).op = GateOp.or ∧
        m + j ∈ (gateAt D r).inputs ∧ m + j < m + r ∧ Relation.ReflTransGen OrStep w (m + r) := by
    intro j w hr
    rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
    · exact Or.inl eq.symm
    · obtain ⟨r, hrlen, rfl, ho, hi, hb⟩ := hstep
      exact Or.inr ⟨r, hrlen, ho, hi, hb, hz⟩
  have lastOrOutside : ∀ {j r : ℕ}, j ∈ junk G D → r < D.gates.length → (gateAt D r).op = GateOp.or →
      m + j ∈ (gateAt D r).inputs → m + j < m + r → r ∈ orN G D \ lam G D := by
    intro j r hj hr ho hi hb
    obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
    have hNotBelow : ¬ BelowF G D r := by
      intro h
      have hvr : gateVal m D r x = true := (val_or (by simp) hr ho).mpr ⟨m + j, hi, hb, hjx⟩
      exact Bool.noConfusion (hx.symm.trans (h x hvr))
    refine Finset.mem_sdiff.mpr ⟨(orN_mem D r).mpr ⟨hr, ho, hNotBelow⟩, ?_⟩
    intro hl
    obtain ⟨_, h0, h1, _⟩ := (lam_mem D r).mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hr hi
    have hne : (orIn m D (opnd D r b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty hjop] at hne
    exact Finset.not_nonempty_empty hne
  have residualTrace : ∀ {u v : Fin m}, s(u, v) ∈ Ustar G D →
      ∃ a ∈ tops G D, gateVal m D a (pairInput u v) = true ∧ ∃ b : Fin 2, ∃ j ∈ junk G D,
        OrReaches m D (opnd D a b) j ∧ gateVal m D j (pairInput u v) = true := by
    intro u v he
    rw [Ustar_def] at he
    obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
    have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
    obtain ⟨a, ha, hv⟩ := acceptedTop adj'
    obtain ⟨hl, ho, _⟩ := topData ha
    have h := (andValOperands hl ho _).mp hv
    rcases operandSupport hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
    · rcases operandSupport hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
      · have hxy : x ≠ y := (topAdj ha hx hy).ne
        apply False.elim (miss ?_)
        rw [starEdges_def]
        refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩⟩
        rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
        · exact (hxy rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hxy rfl).elim
      · exact ⟨a, ha, hv, 1, j, hj, hr, hjv⟩
    · exact ⟨a, ha, hv, 0, j, hj, hr, hjv⟩
  have residualConnection : (Ustar G D).Nonempty →
      (centreless G D).Nonempty ∨ (orN G D \ lam G D).Nonempty := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, ha, _, b, j, hj, hr, _⟩ := residualTrace he
      rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨r, hrlen, ho, hi, hb, _⟩
      · have hz : side (n := m) D a b = ∅ := by
          rw [side_def, heq]
          exact andRawEmpty (junkData hj).2.1
        left
        refine ⟨a, (centreless_mem D a).mpr ⟨ha, ?_⟩⟩
        fin_cases b
        · exact Or.inl hz
        · exact Or.inr hz
      · exact Or.inr ⟨r, lastOrOutside hj hrlen ho hi hb⟩
  have hUstarNe : (Ustar G D).Nonempty := by
    rw [← Finset.card_pos]
    have hInterLe : (Ustar G D ∩ M).card ≤ (Ustar G D).card := Finset.card_le_card Finset.inter_subset_left
    omega
  have hJunkNe : (junk G D).Nonempty := by
    obtain ⟨e, he⟩ := hUstarNe
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨_, _, _, _, j, hj, _, _⟩ := residualTrace he
      exact ⟨j, hj⟩
  have hJunkNe1 : (junk G D).card ≠ 1 := hNoOneJunk m G D col hbip h4 hLeast
  have hJunkGe2 : 2 ≤ (junk G D).card := by
    have hpos : 0 < (junk G D).card := Finset.card_pos.mpr hJunkNe
    omega
  have hAuxGe1 : 1 ≤ 2 * (centreless G D).card + (orN G D \ lam G D).card := by
    rcases residualConnection hUstarNe with hc | ho
    · have := Finset.card_pos.mpr hc; omega
    · have := Finset.card_pos.mpr ho; omega
  have hUstarGe2 : 2 ≤ (Ustar G D).card := by
    have hInterLe : (Ustar G D ∩ M).card ≤ (Ustar G D).card := Finset.card_le_card Finset.inter_subset_left
    omega
  have readData : ∀ {j k : ℕ}, k ∈ readers m D j → k < D.gates.length ∧ m + j ∈ (gateAt D k).inputs :=
    fun hk => (readers_mem D _ _).mp hk
  have readLt : ∀ {j k : ℕ}, k ∈ readers m D j → j < k := by
    intro j k hk
    have hlt := hLeast.1.2.1 k (readData hk).1 _ (readData hk).2
    omega
  have junkNotBelow : ∀ {j : ℕ}, j ∈ junk G D → ¬ BelowF G D j := by
    intro j hj h
    obtain ⟨_, _, x, hx, hf⟩ := junkData hj
    exact Bool.false_ne_true (hf.symm.trans (h x hx))
  have emptySide : ∀ {a : ℕ}, a ∈ tops G D → ∀ {b : Fin 2}, side (n := m) D a b = ∅ → a ∈ centreless G D := by
    intro a ha b hs
    refine (centreless_mem D a).mpr ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl hs
    · exact Or.inr hs
  have classifyReader : centreless G D = ∅ → ∀ {j k : ℕ}, ¬ BelowF G D j → orIn m D (m + j) = ∅ →
      k ∈ readers m D j → k ∈ junk G D ∨ k ∈ orN G D \ lam G D := by
    intro hE j k hd hz hr
    obtain ⟨hk, hin⟩ := readData hr
    obtain ⟨b, hb⟩ := inputsAsOpnd hk hin
    have hs : side (n := m) D k b = ∅ := by rw [side_def, ← hb]; exact hz
    rcases hLeast.1.1 _ (gateAt_mem hk) with hand | hor
    · left
      have hnb : ¬ BelowF G D k := by
        intro hbelow
        have ht : k ∈ tops G D := (tops_mem D k).mpr ⟨hk, hand, hbelow⟩
        have hcen := emptySide ht hs
        rw [hE] at hcen
        exact Finset.notMem_empty _ hcen
      have hw : ∃ x : Fin m → Bool, gateVal m D k x = true ∧ graphFun G ∅ x = false := by
        by_contra hnone
        apply hnb
        intro x hx
        by_contra hf
        exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
      exact (junk_mem D k).mpr ⟨hk, hand, hw⟩
    · right
      have hnb : ¬ BelowF G D k := by
        intro hbelow
        apply hd
        intro x hx
        exact hbelow x ((val_or (by simp) hk hor).mpr ⟨_, hin, hLeast.1.2.1 k hk _ hin, hx⟩)
      refine Finset.mem_sdiff.mpr ⟨(orN_mem D k).mpr ⟨hk, hor, hnb⟩, ?_⟩
      intro hlam
      obtain ⟨_, h0, h1, _⟩ := (lam_mem D k).mp hlam
      have hn : (orIn m D (opnd D k b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, hz] at hn
      exact Finset.not_nonempty_empty hn
  have orEmpty : ∀ {r : ℕ}, (∀ w ∈ (gateAt D r).inputs, orIn m D w = ∅) → orIn m D (m + r) = ∅ := by
    intro r h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w, hw, tail⟩
    · have := u.isLt; omega
    · obtain ⟨k, _, he, _, hi, _⟩ := hw
      have e : k = r := by omega
      subst k
      have hu' := reach_mem_orIn u tail
      rw [h w hi] at hu'
      exact Finset.notMem_empty _ hu'
  have twoInputs : ∀ {r p q : ℕ}, r < D.gates.length → p ≠ q →
      p ∈ (gateAt D r).inputs → q ∈ (gateAt D r).inputs →
      ∀ {w : ℕ}, w ∈ (gateAt D r).inputs → w = p ∨ w = q := by
    intro r p q hr hpq hp hq w hw
    obtain ⟨u1, u2, hu⟩ := binaryInputs hr
    simp only [hu, List.mem_cons, List.not_mem_nil, or_false] at hp hq hw
    omega
  have hBudgetGe4 : 4 ≤ 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card := by
    by_contra hLt4
    have hJunkEq2 : (junk G D).card = 2 := by omega
    have hE : centreless G D = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSmallOr : (orN G D \ lam G D).card ≤ 1 := by omega
    obtain ⟨a, b, hab, hPair⟩ : ∃ a b : ℕ, a < b ∧ junk G D = {a, b} := by
      obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hJunkEq2
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact ⟨i, j, hlt, he⟩
      · exact ⟨j, i, hlt, he.trans (Finset.pair_comm _ _)⟩
    have ha : a ∈ junk G D := by rw [hPair]; exact Finset.mem_insert_self a {b}
    have hb : b ∈ junk G D := by rw [hPair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have noLaterJunk : ∀ {k : ℕ}, k ∈ junk G D → b < k → False := by
      intro k hk hlt
      rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    have junkReader : ∀ {j k : ℕ}, j ∈ junk G D → k ∈ readers m D j →
        k ∈ junk G D ∨ k ∈ orN G D \ lam G D :=
      fun hj hr => classifyReader hE (junkNotBelow hj) (andRawEmpty (junkData hj).2.1) hr
    obtain ⟨mg, hbm⟩ := leastRead (junkData hb).1 (junkNotBelow hb)
    have hbmLt := readLt hbm
    have hm := (junkReader hb hbm).resolve_left (fun hk => noLaterJunk hk hbmLt)
    have mUnique : ∀ {k : ℕ}, k ∈ orN G D \ lam G D → k = mg :=
      fun {k} hk => Finset.card_le_one.mp hSmallOr k hk mg hm
    have hM : orN G D \ lam G D = {mg} := by
      ext k
      exact ⟨fun hk => Finset.mem_singleton.mpr (mUnique hk),
        fun hk => Finset.mem_singleton.mp hk ▸ hm⟩
    have hB : readers m D b = {mg} := by
      ext k
      refine ⟨fun hk => Finset.mem_singleton.mpr (mUnique ?_),
        fun hk => Finset.mem_singleton.mp hk ▸ hbm⟩
      exact (junkReader hb hk).resolve_left (fun hj => noLaterJunk hj (readLt hk))
    have hmData : mg < D.gates.length ∧ (gateAt D mg).op = GateOp.or ∧ ¬ BelowF G D mg :=
      (orN_mem D mg).mp (Finset.mem_sdiff.mp hm).1
    have noAM : mg ∈ readers m D a → False := by
      intro ham
      have hmEmpty : orIn m D (m + mg) = ∅ := by
        apply orEmpty
        intro w hw
        rcases twoInputs hmData.1 (show m + a ≠ m + b by omega)
            (readData ham).2 (readData hbm).2 hw with rfl | rfl
        · exact andRawEmpty (junkData ha).2.1
        · exact andRawEmpty (junkData hb).2.1
      obtain ⟨k, hmk⟩ := leastRead hmData.1 hmData.2.2
      have hmkLt := readLt hmk
      rcases classifyReader hE hmData.2.2 hmEmpty hmk with hk | hk
      · exact noLaterJunk hk (hbmLt.trans hmkLt)
      · have := mUnique hk; omega
    have aRead : ∀ {k : ℕ}, k ∈ readers m D a → k = b := by
      intro k hk
      rcases junkReader ha hk with hj | hj
      · have hlt := readLt hk
        rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
        omega
      · exact False.elim (noAM (mUnique hj ▸ hk))
    obtain ⟨ka, hka⟩ := leastRead (junkData ha).1 (junkNotBelow ha)
    have habRead : b ∈ readers m D a := aRead hka ▸ hka
    have hA : readers m D a = {b} := by
      ext i
      exact ⟨fun hi => Finset.mem_singleton.mpr (aRead hi),
        fun hi => Finset.mem_singleton.mp hi ▸ habRead⟩
    have habCone : InCone m D a b := (inCone_iff a b).mpr
      ⟨(readData habRead).1, a, hab, (readData habRead).2, Or.inl rfl⟩
    have val_allTrue : ∀ w, w < m + D.gates.length → val D (List.ofFn (fun _ : Fin m => true)) w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hwm : w < m
        · rw [val_input (by simp) hwm]
          simp [List.getD_eq_getElem?_getD, hwm]
        · obtain ⟨j, rfl⟩ : ∃ j, w = m + j := ⟨w - m, by omega⟩
          have hj : j < D.gates.length := by omega
          rcases hLeast.1.1 _ (gateAt_mem hj) with hand | hor
          · exact (val_and (by simp) hj hand).mpr (fun i hi => by
              have hilt := hLeast.1.2.1 j hj i hi
              exact ⟨hilt, ih i hilt (by omega)⟩)
          · have hi0 := opndMem hj 0
            have hlt0 := opndBound hj 0
            exact (val_or (by simp) hj hor).mpr ⟨opnd D j 0, hi0, hlt0, ih _ hlt0 (by omega)⟩
    have not_belowF_inCone_and : ∀ {k j : ℕ}, k < D.gates.length → BelowF G D k →
        j < D.gates.length → (gateAt D j).op = GateOp.and → ¬ InCone m D k j := by
      intro k j hk hbk hj hjo hkj
      have htk := val_allTrue (m + k) (by omega)
      obtain ⟨w', hstep, _, hw'⟩ := or_trace (by simp) (m + k) htk
      rcases hw' with hlt | ⟨t, htlen, rfl, htop⟩
      · have hvar := reach_var_val (pairInput ⟨w', hlt⟩ ⟨w', hlt⟩) (m + k) ⟨w', hlt⟩ hstep (pairInput_left _ _)
        exact G.irrefl ((graphFun_pair _ _).mp (hbk _ hvar))
      · have htand := (hLeast.1.1 _ (gateAt_mem htlen)).resolve_right htop
        have htb : BelowF G D t := fun x hx => hbk x (orStep_up (by simp) hstep (gateVal_eq_val D t x ▸ hx))
        rcases orStep_cone hstep k t rfl rfl with rfl | htkc
        · exact hTop t htlen j hj htand htb hjo hkj
        · exact hTop t htlen j hj htand htb hjo (inCone_trans htkc hkj)
    have lam_monochrome : ∀ {h : ℕ}, h ∈ lam G D →
        ∃ (t : ℕ) (d : Fin 2) (z : Fin m), t ∈ tops G D ∧ side (n := m) D t (1 - d) = {z} ∧
          OrReaches m D (opnd D t d) h ∧
          ∀ v ∈ orIn m D (m + h), v ∈ side (n := m) D t d ∧ G.Adj z v ∧ col v = !(col z) := by
      intro h hh
      obtain ⟨_, _, _, t, ht, d, hcard, hreach⟩ := (lam_mem D h).mp hh
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      refine ⟨t, d, z, ht, hz, hreach, ?_⟩
      intro v hv
      have hvs : v ∈ side (n := m) D t d := by
        rw [side_def]
        exact orIn_mono hreach hv
      have hzs : z ∈ side (n := m) D t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self z
      have hadjv : G.Adj z v := by
        fin_cases d
        · exact (topAdj ht hvs hzs).symm
        · exact topAdj ht hzs hvs
      have hcolv : col v = !(col z) := by
        have hne := hbip z v hadjv
        cases hcz : col z <;> cases hcv : col v <;> rw [hcz, hcv] at hne <;>
          first | rfl | exact False.elim (hne rfl)
      exact ⟨hvs, hadjv, hcolv⟩
    have pureOr_eval : ∀ w, w < m + D.gates.length →
        (∀ g, (w = m + g ∨ ∃ g0, w = m + g0 ∧ InCone m D g g0) → (gateAt D g).op = GateOp.or) →
        ∀ x : Fin m → Bool, val D (List.ofFn x) w = true ↔ ∃ v ∈ orIn m D w, x v = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hor x
        by_cases hwm : w < m
        · let v0 : Fin m := ⟨w, hwm⟩
          have hv0 : val D (List.ofFn x) w = x v0 := val_ofFn D x v0
          rw [hv0]
          constructor
          · intro hx
            exact ⟨v0, reach_mem_orIn v0 Relation.ReflTransGen.refl, hx⟩
          · rintro ⟨v, hv, hxv⟩
            have hle := orStep_le (mem_orIn_reach v hv)
            rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨_, hstep, _⟩
            · have : v = v0 := Fin.ext he.symm
              rw [← this]; exact hxv
            · obtain ⟨k, _, hk, _, _, _⟩ := hstep
              omega
        · obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
          have hk : k < D.gates.length := by omega
          have hkop : (gateAt D k).op = GateOp.or := hor k (Or.inl rfl)
          rw [val_or (by simp) hk hkop]
          constructor
          · rintro ⟨i, hi, hlt, hvi⟩
            have hor_i : ∀ g, (i = m + g ∨ ∃ g0, i = m + g0 ∧ InCone m D g g0) → (gateAt D g).op = GateOp.or := by
              intro g hg
              apply hor g
              right
              refine ⟨k, rfl, ?_⟩
              rcases hg with rfl | ⟨g0, rfl, hgg0⟩
              · exact (inCone_iff g k).mpr ⟨hk, g, by omega, hi, Or.inl rfl⟩
              · exact (inCone_iff g k).mpr ⟨hk, g0, by omega, hi, Or.inr hgg0⟩
            obtain ⟨v, hv, hxv⟩ := (ih i hlt (by omega) hor_i x).mp hvi
            have hstep : OrStep (m + k) i := ⟨k, hk, rfl, hkop, hi, hlt⟩
            exact ⟨v, reach_mem_orIn v (Relation.ReflTransGen.head hstep (mem_orIn_reach v hv)), hxv⟩
          · rintro ⟨v, hv, hxv⟩
            have hstep := mem_orIn_reach v hv
            rcases Relation.ReflTransGen.cases_head hstep with he | ⟨i, h1, hrest⟩
            · have := v.isLt; omega
            · obtain ⟨k0, _, hek, _, hi, hlt⟩ := h1
              have : k0 = k := by omega
              subst k0
              exact ⟨i, hi, hlt, reach_var_val x i v hrest hxv⟩
    have cone_of_ab_lam : ∀ {w : ℕ},
        ((w ∈ (gateAt D a).inputs) ∨ (w ∈ (gateAt D b).inputs ∧ w ≠ m + a)) →
        (∀ g, (w = m + g ∨ ∃ g0, w = m + g0 ∧ InCone m D g g0) → g ∈ lam G D) := by
      intro w hw g hg
      have hgb : InCone m D g b := by
        rcases hw with hwa | ⟨hwb, hwne⟩
        · have hlt := hLeast.1.2.1 a (junkData ha).1 w hwa
          have hga : InCone m D g a := by
            rcases hg with rfl | ⟨g0, rfl, hgg0⟩
            · exact (inCone_iff g a).mpr ⟨(junkData ha).1, g, by omega, hwa, Or.inl rfl⟩
            · exact (inCone_iff g a).mpr ⟨(junkData ha).1, g0, by omega, hwa, Or.inr hgg0⟩
          exact inCone_trans hga habCone
        · have hlt := hLeast.1.2.1 b (junkData hb).1 w hwb
          rcases hg with rfl | ⟨g0, rfl, hgg0⟩
          · exact (inCone_iff g b).mpr ⟨(junkData hb).1, g, by omega, hwb, Or.inl rfl⟩
          · exact (inCone_iff g b).mpr ⟨(junkData hb).1, g0, by omega, hwb, Or.inr hgg0⟩
      have hglen : g < D.gates.length := by
        have := inCone_lt hgb
        have := (junkData hb).1
        omega
      have hgltb : g < b := inCone_lt hgb
      have hgnb : ¬ BelowF G D g := fun hbg =>
        not_belowF_inCone_and hglen hbg (junkData hb).1 (junkData hb).2.1 hgb
      have hgne_a : g ≠ a := by
        intro hga
        subst g
        rcases hw with hwa | ⟨hwb, hwne⟩
        · have hlt := hLeast.1.2.1 a (junkData ha).1 w hwa
          rcases hg with he | ⟨g0, he, hgg0⟩
          · omega
          · have := inCone_lt hgg0; omega
        · rcases hg with he | ⟨g0, he, hgg0⟩
          · exact hwne he
          · have hlt := hLeast.1.2.1 b (junkData hb).1 w hwb
            obtain ⟨r, hrle, hrmem⟩ := inCone_has_reader hgg0
            have hrb : r = b := aRead hrmem
            omega
      have hg_not_and : (gateAt D g).op ≠ GateOp.and := by
        intro hgop
        have hdirty : ∃ x : Fin m → Bool, gateVal m D g x = true ∧ graphFun G ∅ x = false := by
          by_contra hne
          apply hgnb
          intro x hx
          by_contra hf
          exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
        have hgj : g ∈ junk G D := (junk_mem D g).mpr ⟨hglen, hgop, hdirty⟩
        rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hgj
        rcases hgj with h1 | h2
        · exact hgne_a h1
        · omega
      have hgor : (gateAt D g).op = GateOp.or := (hLeast.1.1 _ (gateAt_mem hglen)).resolve_left hg_not_and
      have hgorN : g ∈ orN G D := (orN_mem D g).mpr ⟨hglen, hgor, hgnb⟩
      by_contra hnotlam
      have hgsdiff : g ∈ orN G D \ lam G D := Finset.mem_sdiff.mpr ⟨hgorN, hnotlam⟩
      have hgm := mUnique hgsdiff
      omega
    have wire_of_ab_mono : ∀ {w : ℕ},
        ((w ∈ (gateAt D a).inputs) ∨ (w ∈ (gateAt D b).inputs ∧ w ≠ m + a)) →
        ∃ c : Bool,
          (∀ v ∈ orIn m D w, col v = c) ∧
          (∀ x : Fin m → Bool, val D (List.ofFn x) w = true ↔ ∃ v ∈ orIn m D w, x v = true) ∧
          (∀ v1 v2 : Fin m, v1 ≠ v2 → v1 ∈ orIn m D w → v2 ∈ orIn m D w →
            ∃ t ∈ tops G D, ∃ d : Fin 2, ∃ z : Fin m,
              side (n := m) D t (1 - d) = {z} ∧ v1 ∈ side (n := m) D t d ∧ v2 ∈ side (n := m) D t d ∧
              G.Adj z v1 ∧ G.Adj z v2) := by
      intro w hw
      have hwlt : w < m + D.gates.length := by
        rcases hw with hwa | ⟨hwb, _⟩
        · have := hLeast.1.2.1 a (junkData ha).1 w hwa; have := (junkData ha).1; omega
        · have := hLeast.1.2.1 b (junkData hb).1 w hwb; have := (junkData hb).1; omega
      have hlam := cone_of_ab_lam hw
      have hor_w : ∀ g, (w = m + g ∨ ∃ g0, w = m + g0 ∧ InCone m D g g0) → (gateAt D g).op = GateOp.or :=
        fun g hg => ((orN_mem D g).mp ((lam_mem D g).mp (hlam g hg)).1).2.1
      have heval := pureOr_eval w hwlt hor_w
      by_cases hwm : w < m
      · let v0 : Fin m := ⟨w, hwm⟩
        have horin_eq : orIn m D w = {v0} := by
          ext v
          simp only [Finset.mem_singleton]
          constructor
          · intro hv
            rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨_, hstep, _⟩
            · exact Fin.ext he.symm
            · obtain ⟨k, _, hk, _, _, _⟩ := hstep; omega
          · rintro rfl
            exact reach_mem_orIn v0 Relation.ReflTransGen.refl
        refine ⟨col v0, ?_, heval, ?_⟩
        · intro v hv; rw [horin_eq, Finset.mem_singleton] at hv; subst v; rfl
        · intro v1 v2 hne hv1 hv2
          rw [horin_eq, Finset.mem_singleton] at hv1 hv2
          exact False.elim (hne (hv1.trans hv2.symm))
      · obtain ⟨h, rfl⟩ : ∃ h, w = m + h := ⟨w - m, by omega⟩
        have hhl : h ∈ lam G D := hlam h (Or.inl rfl)
        obtain ⟨t, d, z, ht, hz, _, hprop⟩ := lam_monochrome hhl
        refine ⟨!(col z), fun v hv => (hprop v hv).2.2, heval, ?_⟩
        intro v1 v2 _ hv1 hv2
        exact ⟨t, ht, d, z, hz, (hprop v1 hv1).1, (hprop v2 hv2).1, (hprop v1 hv1).2.1, (hprop v2 hv2).2.1⟩
    have b_iff_wires : ∀ x : Fin m → Bool, gateVal m D b x = true ↔
        (∀ w ∈ (gateAt D a).inputs, val D (List.ofFn x) w = true) ∧
        (∀ w ∈ (gateAt D b).inputs, w ≠ m + a → val D (List.ofFn x) w = true) := by
      intro x
      rw [gateVal_eq_val, val_and (by simp) (junkData hb).1 (junkData hb).2.1]
      constructor
      · intro h
        have ha_val : val D (List.ofFn x) (m + a) = true := (h (m + a) (readData habRead).2).2
        have ha_all := (val_and (by simp) (junkData ha).1 (junkData ha).2.1).mp ha_val
        exact ⟨fun w hw => (ha_all w hw).2, fun w hw _ => (h w hw).2⟩
      · rintro ⟨ha_all, hb_rest⟩ w hw
        refine ⟨hLeast.1.2.1 b (junkData hb).1 w hw, ?_⟩
        by_cases hwa : w = m + a
        · subst w
          exact (val_and (by simp) (junkData ha).1 (junkData ha).2.1).mpr
            (fun u hu => ⟨hLeast.1.2.1 a (junkData ha).1 u hu, ha_all u hu⟩)
        · exact hb_rest w hw hwa
    have b_rect : ∀ (c0 : Bool) (u1 u2 v1 v2 : Fin m),
        col u1 = c0 → col u2 = c0 → col v1 = !c0 → col v2 = !c0 →
        gateVal m D b (pairInput u1 v1) = true → gateVal m D b (pairInput u2 v2) = true →
        gateVal m D b (pairInput u1 v2) = true ∧ gateVal m D b (pairInput u2 v1) = true := by
      intro c0 u1 u2 v1 v2 hu1 hu2 hv1 hv2 h1 h2
      have stepW : ∀ w, ((w ∈ (gateAt D a).inputs) ∨ (w ∈ (gateAt D b).inputs ∧ w ≠ m + a)) →
          val D (List.ofFn (pairInput u1 v1)) w = true →
          val D (List.ofFn (pairInput u2 v2)) w = true →
          val D (List.ofFn (pairInput u1 v2)) w = true ∧ val D (List.ofFn (pairInput u2 v1)) w = true := by
        intro w hw hw1 hw2
        obtain ⟨cw, hcolw, hevalw, _⟩ := wire_of_ab_mono hw
        obtain ⟨x1, hx1m, hx1p⟩ := (hevalw _).mp hw1
        obtain ⟨x2, hx2m, hx2p⟩ := (hevalw _).mp hw2
        have hx1c : col x1 = cw := hcolw x1 hx1m
        have hx2c : col x2 = cw := hcolw x2 hx2m
        rcases (pairInput_true u1 v1 x1).mp hx1p with rfl | rfl <;>
          rcases (pairInput_true u2 v2 x2).mp hx2p with rfl | rfl
        · exact ⟨(hevalw _).mpr ⟨x1, hx1m, pairInput_left _ _⟩,
            (hevalw _).mpr ⟨x2, hx2m, pairInput_left _ _⟩⟩
        · have hcontra : c0 = !c0 := hu1.symm.trans (hx1c.trans (hx2c.symm.trans hv2))
          cases c0 <;> exact Bool.noConfusion hcontra
        · have hcontra : (!c0) = c0 := hv1.symm.trans (hx1c.trans (hx2c.symm.trans hu2))
          cases c0 <;> exact Bool.noConfusion hcontra
        · exact ⟨(hevalw _).mpr ⟨x2, hx2m, pairInput_right _ _⟩,
            (hevalw _).mpr ⟨x1, hx1m, pairInput_right _ _⟩⟩
      obtain ⟨ha1, hb1⟩ := (b_iff_wires _).mp h1
      obtain ⟨ha2, hb2⟩ := (b_iff_wires _).mp h2
      refine ⟨(b_iff_wires _).mpr ⟨?_, ?_⟩, (b_iff_wires _).mpr ⟨?_, ?_⟩⟩
      · intro w hw; exact (stepW w (Or.inl hw) (ha1 w hw) (ha2 w hw)).1
      · intro w hw hne; exact (stepW w (Or.inr ⟨hw, hne⟩) (hb1 w hw hne) (hb2 w hw hne)).1
      · intro w hw; exact (stepW w (Or.inl hw) (ha1 w hw) (ha2 w hw)).2
      · intro w hw hne; exact (stepW w (Or.inr ⟨hw, hne⟩) (hb1 w hw hne) (hb2 w hw hne)).2
    have b_same_v : ∀ (c0 : Bool) (u1 u2 v1 : Fin m),
        u1 ≠ u2 → col u1 = c0 → col u2 = c0 → col v1 = !c0 →
        G.Adj u1 v1 → G.Adj u2 v1 → s(u1, v1) ∈ Ustar G D →
        gateVal m D b (pairInput u1 v1) = true → gateVal m D b (pairInput u2 v1) = true →
        gateVal m D b (pairInput v1 v1) = true := by
      intro c0 u1 u2 v1 hne hu1 hu2 hv1 hadj1 hadj2 hu1U h1 h2
      have stepW : ∀ w, ((w ∈ (gateAt D a).inputs) ∨ (w ∈ (gateAt D b).inputs ∧ w ≠ m + a)) →
          val D (List.ofFn (pairInput u1 v1)) w = true →
          val D (List.ofFn (pairInput u2 v1)) w = true →
          val D (List.ofFn (pairInput v1 v1)) w = true := by
        intro w hw hw1 hw2
        obtain ⟨cw, hcolw, hevalw, htwo⟩ := wire_of_ab_mono hw
        obtain ⟨x1, hx1m, hx1p⟩ := (hevalw _).mp hw1
        obtain ⟨x2, hx2m, hx2p⟩ := (hevalw _).mp hw2
        rcases (pairInput_true u1 v1 x1).mp hx1p with rfl | rfl
        · rcases (pairInput_true u2 v1 x2).mp hx2p with rfl | rfl
          · obtain ⟨t, ht, d, z, hz, hx1s, hx2s, hz1, hz2⟩ := htwo x1 x2 hne hx1m hx2m
            have hzv : z = v1 := by
              by_contra hzn
              have hcard := h4 z v1 hzn
              have h1m : x1 ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj v1 p) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1, hadj1.symm⟩
              have h2m : x2 ∈ Finset.univ.filter (fun p => G.Adj z p ∧ G.Adj v1 p) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2, hadj2.symm⟩
              exact hne (Finset.card_le_one.mp hcard x1 h1m x2 h2m)
            subst z
            have hvs : v1 ∈ side (n := m) D t (1 - d) := by rw [hz]; exact Finset.mem_singleton_self v1
            have hstar : s(x1, v1) ∈ starEdges G D := by
              rw [starEdges_def]
              refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
              fin_cases d
              · exact Finset.mem_image.mpr ⟨(x1, v1), Finset.mem_product.mpr ⟨hx1s, hvs⟩, rfl⟩
              · exact Finset.mem_image.mpr ⟨(v1, x1), Finset.mem_product.mpr ⟨hvs, hx1s⟩, Sym2.eq_swap⟩
            rw [Ustar_def] at hu1U
            exact False.elim ((Finset.mem_sdiff.mp hu1U).2 hstar)
          · have hcontra : c0 = !c0 := hu1.symm.trans ((hcolw x1 hx1m).trans ((hcolw x2 hx2m).symm.trans hv1))
            cases c0 <;> exact Bool.noConfusion hcontra
        · exact (hevalw _).mpr ⟨x1, hx1m, pairInput_left _ _⟩
      obtain ⟨ha1, hb1⟩ := (b_iff_wires _).mp h1
      obtain ⟨ha2, hb2⟩ := (b_iff_wires _).mp h2
      exact (b_iff_wires _).mpr
        ⟨fun w hw => stepW w (Or.inl hw) (ha1 w hw) (ha2 w hw),
         fun w hw hne' => stepW w (Or.inr ⟨hw, hne'⟩) (hb1 w hw hne') (hb2 w hw hne')⟩
    have hm_nonempty : (orIn m D (m + mg)).Nonempty := by
      by_contra hme
      have hmEmpty : orIn m D (m + mg) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hme
      obtain ⟨k, hmk⟩ := leastRead hmData.1 hmData.2.2
      have hmkLt := readLt hmk
      rcases classifyReader hE hmData.2.2 hmEmpty hmk with hk | hk
      · exact noLaterJunk hk (hbmLt.trans hmkLt)
      · have := mUnique hk; omega
    obtain ⟨z0, hz0⟩ := hm_nonempty
    let col_m : Bool := col z0
    have hz0_reach : Relation.ReflTransGen OrStep (m + mg) z0.val := mem_orIn_reach z0 hz0
    have trace_edge : ∀ u v : Fin m, col u = col_m → col v = !col_m → s(u, v) ∈ Ustar G D →
        G.Adj u v ∧ G.Adj z0 v ∧ u ≠ z0 ∧
        gateVal m D b (pairInput u v) = true ∧
        ∀ w : Fin m, gateVal m D b (pairInput w v) = true → G.Adj w v := by
      intro u v hcu hcv heU
      have hadjuv : G.Adj u v := by
        rw [Ustar_def] at heU
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp heU).1
      obtain ⟨t, ht, htv_uv, d, j, hj, hreach, hjbv⟩ := residualTrace heU
      have hjb : j = b := by
        rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exfalso
          rcases lastOrBefore (orReaches_reach j _ hreach).1 with heq | ⟨r, hrlen, hop, hin, _, _⟩
          · have hs : side (n := m) D t d = ∅ := by rw [side_def, heq]; exact andRawEmpty (junkData ha).2.1
            have hbad := emptySide ht hs
            rw [hE] at hbad
            exact Finset.notMem_empty _ hbad
          · have hr' : r ∈ readers m D j := (readers_mem D j r).mpr ⟨hrlen, hin⟩
            rw [aRead hr', (junkData hb).2.1] at hop
            exact GateOp.noConfusion hop
        · rfl
      subst j
      have hReachM : Relation.ReflTransGen OrStep (opnd D t d) (m + mg) := by
        rcases lastOrBefore (orReaches_reach b _ hreach).1 with heq | ⟨r, hrlen, _, hin, _, hrm⟩
        · exfalso
          have hs : side (n := m) D t d = ∅ := by rw [side_def, heq]; exact andRawEmpty (junkData hb).2.1
          have hbad := emptySide ht hs
          rw [hE] at hbad
          exact Finset.notMem_empty _ hbad
        · have hr' : r ∈ readers m D b := (readers_mem D b r).mpr ⟨hrlen, hin⟩
          have hrmg : r = mg := Finset.mem_singleton.mp (hB ▸ hr')
          subst r
          exact hrm
      have hz0_side : z0 ∈ side (n := m) D t d := by
        rw [side_def]
        exact reach_mem_orIn z0 (hReachM.trans hz0_reach)
      have hnoOtherJunk : ∀ j' ∈ junk G D, ¬ OrReaches m D (opnd D t (1 - d)) j' := by
        intro j' hj' hr'
        have hj'b : j' = b := by
          rw [hPair, Finset.mem_insert, Finset.mem_singleton] at hj'
          rcases hj' with rfl | rfl
          · exfalso
            rcases lastOrBefore (orReaches_reach j' _ hr').1 with heq | ⟨r, hrlen, hop, hin, _, _⟩
            · have hs : side (n := m) D t (1 - d) = ∅ := by
                rw [side_def, heq]; exact andRawEmpty (junkData ha).2.1
              have hbad := emptySide ht hs; rw [hE] at hbad; exact Finset.notMem_empty _ hbad
            · have hr'' : r ∈ readers m D j' := (readers_mem D j' r).mpr ⟨hrlen, hin⟩
              rw [aRead hr'', (junkData hb).2.1] at hop
              exact GateOp.noConfusion hop
          · rfl
        subst j'
        have hReachM2 : Relation.ReflTransGen OrStep (opnd D t (1 - d)) (m + mg) := by
          rcases lastOrBefore (orReaches_reach b _ hr').1 with heq | ⟨r, hrlen, _, hin, _, hrm⟩
          · exfalso
            have hs : side (n := m) D t (1 - d) = ∅ := by
              rw [side_def, heq]; exact andRawEmpty (junkData hb).2.1
            have hbad := emptySide ht hs; rw [hE] at hbad; exact Finset.notMem_empty _ hbad
          · have hr'' : r ∈ readers m D b := (readers_mem D b r).mpr ⟨hrlen, hin⟩
            have hrmg : r = mg := Finset.mem_singleton.mp (hB ▸ hr'')
            subst r
            exact hrm
        apply hmData.2.2
        intro x hx
        have h1 : val D (List.ofFn x) (opnd D t d) = true := orStep_up (by simp) hReachM hx
        have h2 : val D (List.ofFn x) (opnd D t (1 - d)) = true := orStep_up (by simp) hReachM2 hx
        obtain ⟨htlen, htop, htb⟩ := topData ht
        have htv : gateVal m D t x = true := (andValOperands htlen htop x).mpr (fun q => by
          fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)
        exact htb x htv
      obtain ⟨htlen, htop, htb⟩ := topData ht
      have hOtherVal : val D (List.ofFn (pairInput u v)) (opnd D t (1 - d)) = true :=
        (andValOperands htlen htop _).mp htv_uv (1 - d)
      have hv_side : v ∈ side (n := m) D t (1 - d) := by
        rcases operandSupport htlen htop hOtherVal with ⟨x, hxs, hxu | hxv⟩ | ⟨j', hj', hr', _⟩
        · subst x
          have hadjz0u : G.Adj z0 u := by
            fin_cases d
            · exact topAdj ht hz0_side hxs
            · exact (topAdj ht hxs hz0_side).symm
          have hne := hbip z0 u hadjz0u
          exact False.elim (hne hcu.symm)
        · subst x; exact hxs
        · exact False.elim (hnoOtherJunk j' hj' hr')
      have hadjz0v : G.Adj z0 v := by
        fin_cases d
        · exact topAdj ht hz0_side hv_side
        · exact (topAdj ht hv_side hz0_side).symm
      have huz0 : u ≠ z0 := by
        intro heq
        subst u
        have hstar : s(z0, v) ∈ starEdges G D := by
          rw [starEdges_def]
          refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
          fin_cases d
          · exact Finset.mem_image.mpr ⟨(z0, v), Finset.mem_product.mpr ⟨hz0_side, hv_side⟩, rfl⟩
          · exact Finset.mem_image.mpr ⟨(v, z0), Finset.mem_product.mpr ⟨hv_side, hz0_side⟩, Sym2.eq_swap⟩
        rw [Ustar_def] at heU
        exact (Finset.mem_sdiff.mp heU).2 hstar
      have hReachB : Relation.ReflTransGen OrStep (opnd D t d) (m + b) :=
        (orReaches_reach b _ hreach).1
      refine ⟨hadjuv, hadjz0v, huz0, hjbv, ?_⟩
      intro w hbw
      have h1 : val D (List.ofFn (pairInput w v)) (opnd D t d) = true :=
        orStep_up (by simp) hReachB hbw
      have h2 : val D (List.ofFn (pairInput w v)) (opnd D t (1 - d)) = true :=
        sideVal hv_side (pairInput_right w v)
      have htwv : gateVal m D t (pairInput w v) = true := (andValOperands htlen htop _).mpr (fun q => by
        fin_cases d <;> fin_cases q <;> first | exact h1 | exact h2)
      exact (graphFun_pair w v).mp (htb _ htwv)
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Ustar G D).card)
    have orient : ∀ e ∈ Ustar G D, ∃ u v : Fin m, e = s(u, v) ∧ col u = col_m ∧ col v = !col_m := by
      intro e he
      induction e using Sym2.ind with
      | _ p q =>
        have hadjpq : G.Adj p q := by
          rw [Ustar_def] at he
          exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
        have hcolne := hbip p q hadjpq
        have bool_ne_not : ∀ a b : Bool, a ≠ b → b = !a := by
          intro a b h; cases a <;> cases b <;> first | rfl | exact False.elim (h rfl)
        by_cases hcp : col p = col_m
        · refine ⟨p, q, rfl, hcp, ?_⟩
          exact bool_ne_not col_m (col q) (hcp ▸ hcolne)
        · have hcp' : col p = !col_m := bool_ne_not col_m (col p) (fun h => hcp h.symm)
          have hcq' : col q = !(col p) := bool_ne_not (col p) (col q) hcolne
          refine ⟨q, p, Sym2.eq_swap, ?_, hcp'⟩
          rw [hcq', hcp', Bool.not_not]
    obtain ⟨u1, v1, rfl, hu1c, hv1c⟩ := orient e1 he1
    obtain ⟨u2, v2, rfl, hu2c, hv2c⟩ := orient e2 he2
    obtain ⟨hadj1, hz01, hu1z0, hb1, hfire1⟩ := trace_edge u1 v1 hu1c hv1c he1
    obtain ⟨hadj2, hz02, _, hb2, hfire2⟩ := trace_edge u2 v2 hu2c hv2c he2
    by_cases hu : u1 = u2
    · subst u2
      have hvne : v1 ≠ v2 := fun h => he12 (by rw [h])
      have hcard := h4 u1 z0 hu1z0
      have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1, hz01⟩
      have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj z0 p) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj2, hz02⟩
      exact hvne (Finset.card_le_one.mp hcard v1 hm1 v2 hm2)
    · by_cases hv : v1 = v2
      · subst v2
        have hbv1 := b_same_v col_m u1 u2 v1 hu hu1c hu2c hv1c hadj1 hadj2 he1 hb1 hb2
        exact G.irrefl (hfire1 v1 hbv1)
      · obtain ⟨hb12, hb21⟩ := b_rect col_m u1 u2 v1 v2 hu1c hu2c hv1c hv2c hb1 hb2
        have hadj21 : G.Adj u2 v1 := hfire1 u2 hb21
        have hadj12 : G.Adj u1 v2 := hfire2 u1 hb12
        have hcard := h4 u1 u2 hu
        have hm1 : v1 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj1, hadj21⟩
        have hm2 : v2 ∈ Finset.univ.filter (fun p => G.Adj u1 p ∧ G.Adj u2 p) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj12, hadj2⟩
        exact hv (Finset.card_le_one.mp hcard v1 hm1 v2 hm2)
  exact hResidual n E σ G D ⟨hdense, hadj, h4, hmatch, hLeast, hTop, hSmall, hJunkGe2, hBudgetGe4,
    by
      have hInterLe : (Ustar G D ∩ M).card ≤ (Ustar G D).card := Finset.card_le_card Finset.inter_subset_left
      omega,
    hBudgetLt, hDeficit⟩
