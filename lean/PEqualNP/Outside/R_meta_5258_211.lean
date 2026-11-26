import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CircuitMoves PEqualNP.HeptadCover PEqualNP.GenericRejection

-- The quadrangle-test conversion follows R_meta_5258_706. The wire monotonicity
-- induction is adapted from L_meta_4871. Seven erasures act on both outputs.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_5258_211
    (peel :
      let S := singerLines3
      let H := fun (C : Circuit) => (quadrangles S).filter fun Q => C.eval (incidenceInput Q (missLines S Q)) = true
      let good (E F : Circuit) := E.gates = F.gates ∧ Monotone2 E ∧ ReadsBack 26 E ∧
        RightOnIncidentPairs S E ∧ RightOnIncidentPairs S F ∧ Disjoint (H E) (H F) ∧ (H E).Nonempty ∧ (H F).Nonempty
      ∀ (C D : Circuit) (A B : Finset (Fin 13)), good C D → C.size < 63 →
        (∀ E F, good E F → C.size ≤ E.size) →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        A ∈ H C → B ∈ H D →
        ∃ (p l : Fin 13), p ∈ S l ∧ (∀ q ∈ [A,B], p ∉ q ∧ l ∉ missLines S q) ∧
        ∃ (g : (i : Fin 7) → Fin (C.size-i.val)) (r : Fin 7 → ℕ),
        ∀ E ∈ [C,D], ∀ X Y : Finset (Fin 13), p ∉ X → l ∉ Y →
          ((List.finRange 7).foldl (fun T i => eraseGate 26 T (g i).val (r i)) E).eval (incidenceInput X Y) = E.eval (incidenceInput X Y))
    (punctured :
      let S := singerLines3
      ∀ (p l : Fin 13) (C D : Circuit), p ∈ S l → C.gates = D.gates → Monotone2 C →
        (∀ u v, u ≠ p → v ≠ l → u ∈ S v → ∀ E ∈ [C,D], E.eval (incidenceInput {u} {v}) = true) →
        let H := fun (E : Circuit) => (quadrangles S).filter fun Q =>
          E.eval (incidenceInput (Q.erase p) ((missLines S Q).erase l)) = true
        Disjoint (H C) (H D) → (H C).Nonempty → (H D).Nonempty → 56 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) =>   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 ∧ (∀ (x9 x10 : Fin (13 : ℕ)), x9 - x10 ∈ x1 → (x8 x6 (x2 x9 x10) && x8 x7 (x2 x9 x10)) = Bool.true) ∧ (∀ (x9 : Finset (Fin (13 : ℕ))), x4 x9 → (x8 x6 (x3 x9) && x8 x7 (x3 x9)) = Bool.false) ∧ (∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x6 (x3 x9) < x8 x7 (x3 x9)) ∧ ∃ (x9 : Finset (Fin (13 : ℕ))), x4 x9 ∧ x8 x7 (x3 x9) < x8 x6 (x3 x9); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), x5 x6 x7 x8 → x6.size < (63 : ℕ) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x5 x12 x13 x14 ∧ x12.size < x6.size := by
  intro dif posRaw negRaw quad Form C u v valid small nested
  classical
  let pos (D : Circuit) (a b : ℕ) :=
    ∀ w ∈ [a,b], RightOnIncidentPairs singerLines3 ⟨D.gates,w⟩
  let Qs := quadrangles singerLines3
  let sample (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  let hit (D : Circuit) (w : ℕ) := Qs.filter
    (fun Q => (Circuit.mk D.gates w).eval (sample Q) = true)
  let live (D : Circuit) (a b : ℕ) := (hit D a).Nonempty ∧ (hit D b).Nonempty
  let val (D : Circuit) (w : ℕ) (xs : List Bool) := (D.wires xs).getD w false
  have incidence (p l : Fin 13) : p-l ∈ dif ↔ p ∈ singerLines3 l := by
    change p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l
    revert p l
    decide +kernel
  have incidenceRow (p l : Fin 13) : incidenceInput {p} {l} = posRaw p l := by
    change (List.ofFn (fun x : Fin 13 => decide (x ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun x : Fin 13 => decide (x ∈ ({l} : Finset (Fin 13))))) = _
    simp only [Finset.mem_singleton]
    rfl
  have quadrangle (Q : Finset (Fin 13)) : Q ∈ Qs ↔ quad Q := by
    have cross (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun x => x-l ∈ dif) := by
      ext x
      simp [incidence x l]
    change Q ∈ (Finset.univ.powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,cross]
    rfl
  have quadrangleRow (Q : Finset (Fin 13)) : sample Q = negRaw Q := by
    have tail : List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ dif)) := by
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      change l ∈ Finset.univ.filter (fun k => Disjoint (singerLines3 k) Q) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,← incidence]
      exact ⟨fun h p hp hi => h hi hp, fun h p hp hi => h p hi hp⟩
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ Q))) ++ _ = _
    rw [tail]
  have memHit (D : Circuit) (a : ℕ) (Q : Finset (Fin 13)) :
      Q ∈ hit D a ↔ Q ∈ Qs ∧ val D a (sample Q) = true := by
    change Q ∈ Qs.filter (fun X => val D a (sample X) = true) ↔ _
    exact Finset.mem_filter
  have strict : ∀ a b : Bool, a < b ↔ a = false ∧ b = true := by decide
  have compact (D : Circuit) (a b : ℕ) :
      Form D a b ↔ Monotone2 D ∧ ReadsBack 26 D ∧ pos D a b ∧
        Disjoint (hit D a) (hit D b) ∧ live D a b := by
    constructor
    · rintro ⟨hm,hb,hpos,hneg,hab,hba⟩
      refine ⟨hm,hb,?_,?_,?_⟩
      · intro w hw l p hinc
        have h := Bool.and_eq_true_iff.mp (hpos p l ((incidence p l).mpr hinc))
        change val D w (incidenceInput {p} {l}) = true
        rw [incidenceRow]
        rcases (show w=a ∨ w=b by simpa using hw) with rfl | rfl
        · exact h.1
        · exact h.2
      · apply Finset.disjoint_left.mpr
        intro Q ha hb
        obtain ⟨hq,ha⟩ := (memHit D a Q).mp ha
        have hb := ((memHit D b Q).mp hb).2
        rw [quadrangleRow] at ha hb
        have impossible := hneg Q ((quadrangle Q).mp hq)
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false at impossible
        simp [ha,hb] at impossible
      · obtain ⟨A,hA,hAB⟩ := hab
        obtain ⟨B,hB,hBA⟩ := hba
        refine ⟨⟨B,(memHit D a B).mpr ⟨(quadrangle B).mpr hB,?_⟩⟩,
          ⟨A,(memHit D b A).mpr ⟨(quadrangle A).mpr hA,?_⟩⟩⟩
        · rw [quadrangleRow]
          exact (strict _ _).mp hBA |>.2
        · rw [quadrangleRow]
          exact (strict _ _).mp hAB |>.2
    · rintro ⟨hm,hb,positive,disjoint,liveA,liveB⟩
      refine ⟨hm,hb,?_,?_,?_,?_⟩
      · intro p l hinc
        apply Bool.and_eq_true_iff.mpr
        have pa := positive a (by simp) l p ((incidence p l).mp hinc)
        have pb := positive b (by simp) l p ((incidence p l).mp hinc)
        change val D a (incidenceInput {p} {l}) = true at pa
        change val D b (incidenceInput {p} {l}) = true at pb
        rw [incidenceRow] at pa pb
        exact ⟨pa,pb⟩
      · intro Q hQ
        change (val D a (negRaw Q) && val D b (negRaw Q)) = false
        rw [← quadrangleRow]
        cases h : (val D a (sample Q) && val D b (sample Q)) with
        | false => rfl
        | true =>
          have bits := Bool.and_eq_true_iff.mp h
          have hq := (quadrangle Q).mpr hQ
          exact (Finset.disjoint_left.mp disjoint ((memHit D a Q).mpr ⟨hq,bits.1⟩)
            ((memHit D b Q).mpr ⟨hq,bits.2⟩)).elim
      · obtain ⟨Q, hQ⟩ := liveB
        obtain ⟨hq, bt⟩ := (memHit D b Q).mp hQ
        have af : val D a (sample Q) = false := by
          cases h : val D a (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp disjoint ((memHit D a Q).mpr ⟨hq,h⟩) hQ).elim
        refine ⟨Q,(quadrangle Q).mp hq,(strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨af,bt⟩
      · obtain ⟨Q, hQ⟩ := liveA
        obtain ⟨hq, atrue⟩ := (memHit D a Q).mp hQ
        have bf : val D b (sample Q) = false := by
          cases h : val D b (sample Q) with
          | false => rfl
          | true => exact (Finset.disjoint_left.mp disjoint hQ ((memHit D b Q).mpr ⟨hq,h⟩)).elim
        refine ⟨Q,(quadrangle Q).mp hq,(strict _ _).mpr ?_⟩
        rw [← quadrangleRow]
        exact ⟨bf,atrue⟩
  let wf (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
      (L ++ [a]).getD w false = L.getD w false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

  have getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
    simp [List.getD_eq_getElem?_getD]

  have getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
      (L ++ [a]).getD w false = false := by
    rw [List.getD_eq_default]; simp; omega

  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
      (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
      op.eval (ins.map fun i => U.getD i false) = true →
      op.eval (ins.map fun i => V.getD i false) = true := by
    rcases hop with rfl | rfl
    · change (ins.map (fun i => U.getD i false)).all id = true → (ins.map (fun i => V.getD i false)).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp, id]
      exact fun hall i hi => h i (hall i hi)
    · change (ins.map (fun i => U.getD i false)).any id = true → (ins.map (fun i => V.getD i false)).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp, id]
      intro hx
      obtain ⟨i,hi,hv⟩ := hx
      exact ⟨i,hi,h i hv⟩

  have ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
      (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
    by_cases hw : w < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
      exact hxy ⟨w, hw⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp

  have mono2 (gs : List Gate)
      (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
      ∀ U V : List Bool, U.length = V.length →
        (∀ i, U.getD i false = true → V.getD i false = true) →
        ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
    induction gs with
    | nil => intro U V _ h i; exact h i
    | cons g gs ih =>
      intro U V hlen h i
      have hg := (hleg g (by simp)).1
      have := ih (fun g' hg' => hleg g' (by simp [hg']))
        (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
        (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
          intro t
          rcases Nat.lt_trichotomy t U.length with ht | ht | ht
          · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
          · subst ht
            rw [getD_snoc_eq]
            have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
            rw [← hlen] at e2
            rw [e2]
            exact eval_mono g.op hg g.inputs U V h
          · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
      simpa [wf] using this

  obtain ⟨mono,back,hpos,sep,⟨A,hA⟩,⟨B,hB⟩⟩ := (compact C u v).mp valid
  let U : Circuit := ⟨C.gates,u⟩
  let V : Circuit := ⟨C.gates,v⟩
  have pu : RightOnIncidentPairs singerLines3 U := hpos u (by simp)
  have pv : RightOnIncidentPairs singerLines3 V := hpos v (by simp)
  let H (E : Circuit) := hit E E.output
  let good (E F : Circuit) := E.gates = F.gates ∧ Monotone2 E ∧ ReadsBack 26 E ∧
    RightOnIncidentPairs singerLines3 E ∧ RightOnIncidentPairs singerLines3 F ∧ Disjoint (H E) (H F) ∧ (H E).Nonempty ∧ (H F).Nonempty
  by_cases smaller : ∃ E, ∃ a b, Form E a b ∧ E.size < C.size
  · exact smaller
  have minimum (E F : Circuit) (ok : good E F) : U.size ≤ E.size := by
    rcases E with ⟨es,e⟩
    rcases F with ⟨fs,f⟩
    obtain ⟨eq,om,ob,oe,ofr,od,ol,orr⟩ := ok
    change es = fs at eq
    subst fs
    let W : Circuit := ⟨es,e⟩
    have ow : pos W e f := by
      intro a ha
      rcases (show a=e ∨ a=f by simpa using ha) with rfl | rfl
      · exact oe
      · exact ofr
    have pair : Form W e f := (compact W e f).mpr ⟨om,ob,ow,od,ol,orr⟩
    exact Nat.le_of_not_gt (fun lt => smaller ⟨W,e,f,pair,lt⟩)
  have original : good U V := ⟨rfl,mono,back,pu,pv,sep,⟨A,hA⟩,⟨B,hB⟩⟩
  obtain ⟨p,l,inc,away,g,r,agreement⟩ := peel U V A B original small minimum nested hA hB
  let edit (T : Circuit) (i : Fin 7) := eraseGate 26 T (g i).val (r i)
  let shrink (E : Circuit) := (List.finRange 7).foldl edit E
  have erases {T : Circuit} (i : Fin 7) (ok : (g i).val < T.size) (mt : Monotone2 T) :
      (edit T i).size + 1 = T.size ∧ Monotone2 (edit T i) := by
    change (g i).val < T.gates.length at ok
    unfold edit eraseGate
    rw [ite_eq_left ok]
    constructor
    · change (T.gates.take _ ++ (T.gates.drop _).map _).length + 1 = T.gates.length
      rw [List.length_append,List.length_take,List.length_map,List.length_drop,Nat.min_eq_left (Nat.le_of_lt ok)]
      omega
    · intro z hz
      simp only [List.mem_append,List.mem_map] at hz
      rcases hz with before | ⟨a,ha,rfl⟩
      · exact mt _ (List.mem_of_mem_take before)
      · obtain ⟨ops,len⟩ := mt _ (List.mem_of_mem_drop ha)
        exact ⟨ops,by simpa using len⟩
  have sameEdit (T T' : Circuit) (i : Fin 7) (same : T.gates = T'.gates) : (edit T i).gates = (edit T' i).gates := by
    rcases T with ⟨gs,o⟩; rcases T' with ⟨hs,b⟩; change gs = hs at same; subst hs
    unfold edit eraseGate
    split <;> rfl
  have sameFold (is : List (Fin 7)) (T T' : Circuit) (h : T.gates = T'.gates) :
      (is.foldl edit T).gates = (is.foldl edit T').gates := by
    induction is generalizing T T' with
    | nil => exact h
    | cons i is ih => exact ih _ _ (sameEdit _ _ i h)
  have same : (shrink U).gates = (shrink V).gates := sameFold _ _ _ rfl
  have priced (ix : List (Fin 7)) (T : Circuit) (pos : ℕ) (mT : Monotone2 T)
      (budget : T.size + pos = U.size) (keys : ∀ j : Fin ix.length, (ix.get j).val = pos + j.val) :
      (ix.foldl edit T).size + ix.length = T.size ∧ Monotone2 (ix.foldl edit T) := by
    induction ix generalizing T pos with
    | nil => exact ⟨by simp,mT⟩
    | cons i tail ih =>
      have first := keys ⟨0,by simp⟩
      change i.val = pos + 0 at first
      have admiss : (g i).val < T.size := by
        have z := (g i).isLt
        change (g i).val < U.size - i.val at z
        omega
      obtain ⟨cost,okay⟩ := erases i admiss mT
      have bound : (edit T i).size + (pos+1) = U.size := by omega
      have ktail (j : Fin tail.length) : (tail.get j).val = (pos+1) + j.val := by
        have z := keys ⟨j.val + 1, by simp⟩
        change (tail.get j).val = pos + (j.val+1) at z
        omega
      obtain ⟨n,filtered⟩ := ih (edit T i) (pos+1) okay bound ktail
      refine ⟨?_,filtered⟩
      change (tail.foldl edit (edit T i)).size + (tail.length+1) = T.size
      omega
  have pricedAll := priced (List.finRange 7) U 0 mono (by omega) (by intro j; simp)
  have seven : (shrink U).size + 7 = C.size := by
    change ((List.finRange 7).foldl edit U).size + 7 = U.size
    simpa only [List.length_finRange] using pricedAll.1
  have newMono : Monotone2 (shrink U) := pricedAll.2
  have lessInput (X Y : Finset (Fin 13)) (i : ℕ) :
      (incidenceInput (X.erase p) (Y.erase l)).getD i false = true → (incidenceInput X Y).getD i false = true := by
    let bits (R S : Finset (Fin 13)) (j : Fin 26) : Bool := Fin.addCases
      (fun a : Fin 13 => decide (a ∈ R)) (fun b : Fin 13 => decide (b ∈ S)) j
    have repr (R S : Finset (Fin 13)) : incidenceInput R S = List.ofFn (bits R S) := by rfl
    rw [repr,repr]
    apply ofFn_mono
    intro j
    refine Fin.addCases (m:=13) (n:=13) (motive:=fun k => bits (X.erase p) (Y.erase l) k = true → bits X Y k = true) ?_ ?_ j
    · intro a h
      simp only [bits,Fin.addCases_left] at h ⊢
      exact decide_eq_true (Finset.mem_of_mem_erase (of_decide_eq_true h))
    · intro b h
      simp only [bits,Fin.addCases_right] at h ⊢
      exact decide_eq_true (Finset.mem_of_mem_erase (of_decide_eq_true h))
  have larger (E : Circuit) (ok : Monotone2 E) (X Y : Finset (Fin 13)) :
      E.eval (incidenceInput (X.erase p) (Y.erase l)) = true → E.eval (incidenceInput X Y) = true := by
    apply mono2 E.gates ok _ _ (by change (List.ofFn _ ++ List.ofFn _).length = (List.ofFn _ ++ List.ofFn _).length; simp only [List.length_append,List.length_ofFn]) (lessInput X Y) E.output
  let shrunkHit (D : Circuit) := Qs.filter fun Q => D.eval
    (incidenceInput (Q.erase p) ((missLines singerLines3 Q).erase l)) = true
  have transfer (E : Circuit) (he : E ∈ [U,V]) (ok : Monotone2 E) (Q : Finset (Fin 13))
      (hq : Q ∈ shrunkHit (shrink E)) : E.eval (sample Q) = true := by
    have h := (Finset.mem_filter.mp hq).2
    change (shrink E).eval (incidenceInput (Q.erase p) ((missLines singerLines3 Q).erase l)) = true at h
    rw [show (shrink E).eval _ = _ from agreement E he _ _ (Finset.notMem_erase _ _) (Finset.notMem_erase _ _)] at h
    exact larger E ok _ _ h
  have keeps (E : Circuit) (hE : E ∈ [U,V]) (q : Finset (Fin 13)) (hq : q ∈ [A,B]) (legal : q ∈ Qs)
      (accepted : E.eval (sample q) = true) : q ∈ shrunkHit (shrink E) := by
    obtain ⟨hp,hl⟩ := away q hq
    apply Finset.mem_filter.mpr
    refine ⟨legal,?_⟩
    rw [Finset.erase_eq_of_notMem hp,Finset.erase_eq_of_notMem hl]
    exact (agreement E hE _ _ hp hl).trans accepted
  have projected : Disjoint (shrunkHit (shrink U)) (shrunkHit (shrink V)) := by
    apply Finset.disjoint_left.mpr
    intro Q hu hv
    have legal : Q ∈ Qs := (Finset.mem_filter.mp hu).1
    exact Finset.disjoint_left.mp sep ((memHit C u Q).mpr ⟨legal,transfer U (by simp) mono Q hu⟩)
      ((memHit C v Q).mpr ⟨legal,transfer V (by simp) mono Q hv⟩)
  have lower := punctured p l (shrink U) (shrink V) inc same newMono (by
    intro x y hxp hyl hxy E hE
    have hp : p ∉ ({x} : Finset (Fin 13)) := by simpa [eq_comm] using hxp
    have hl : l ∉ ({y} : Finset (Fin 13)) := by simpa [eq_comm] using hyl
    rcases (show E = shrink U ∨ E = shrink V by simpa using hE) with rfl | rfl
    · exact (agreement U (by simp) _ _ hp hl).trans (pu y x hxy)
    · exact (agreement V (by simp) _ _ hp hl).trans (pv y x hxy)) projected
      ⟨A,keeps U (by simp) A (by simp) ((memHit C u A).mp hA).1 ((memHit C u A).mp hA).2⟩
      ⟨B,keeps V (by simp) B (by simp) ((memHit C v B).mp hB).1 ((memHit C v B).mp hB).2⟩
  omega
