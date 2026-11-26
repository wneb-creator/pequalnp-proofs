import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

-- The last gate is active, has two internal inputs, and is AND or OR.
-- An AND input with only t previous gates needs a cover of size at most t+1.
-- Seven disjoint positive rows exclude the first five internal AND cubes.
-- The remaining ranges contain 19 AND cubes and 24 OR cubes.
-- At the smallest OR cube the first wire equals exactly one positive edge on all positive rows.
-- At the smallest remaining AND cube the first wire misses a pure colour row.
set_option maxHeartbeats 8500000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_5052_271
    (structural : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), 0<n → 0<s → (∀ i<n, (∃ r∈rows, g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows, g r=false ∧ r.testBit i=true)) →
      ∀ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k) →
      k/(n+s)<2 ∧ n≤k % (n+s) ∧ k % (n+s)+2<n+s)
    (inputCover : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), 0<n → 0<s → (∀ i<n, (∃ r∈rows, g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows, g r=false ∧ r.testBit i=true)) →
      ∀ k < n+s, ∀ a : ℕ → Bool, (∀ c∈enc2 n s g rows ++ enc2Cube n s k, ClauseSat a c) →
      ∃ S : Finset ℕ, (∀ i∈S,i<n) ∧ S.card ≤ k-n+2 ∧
        ∀ r∈rows, (g r=true ∨ a (ix n s 3 (k-n) r+1)=true) → ∃ i∈S, r.testBit i=true)
    (firstOr : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ), 0<n → 1<s → (∀ i<n, (∃ r∈rows,g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows,g r=false ∧ r.testBit i=true)) →
      ∀ k, k % (n+s)=n → k/(n+s)=1 → ∀ a : ℕ → Bool,
        (∀ c∈enc2 n s g rows ++ enc2Cube n s k,ClauseSat a c) →
        ∃ u<n, ∃ v<n, u<v ∧ (∀ r∈rows, a (ix n s 3 0 r+1)=(r.testBit u && r.testBit v)) ∧
        (∀ r∈rows,a (ix n s 3 0 r+1)=true → g r=true))
    (remaining : let pos : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
      ∀ k : ℕ, ((19≤k ∧ k≤37) ∨ (54≤k ∧ k≤77)) → ¬∃ a : ℕ → Bool,
        (∀ c∈enc2 14 26 (fun r ↦ decide (r∈pos)) (pos++neg) ++ enc2Cube 14 26 k,ClauseSat a c) ∧
        (k=19 → ¬(a (ix 14 26 3 5 127+1)=true ∧ a (ix 14 26 3 5 16256+1)=true)) ∧
        (k=54 → ∃ e∈pos,∀ r∈pos,a (ix 14 26 3 0 r+1)=decide (r=e))) :
    have x1 : List ℕ := [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];       (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x2;     have x3 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x2;     (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x2;     (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x3;   have x4 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x3;   (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x4; ∀ x3 < PEqualNP.Defs.LratEncoding.enc2CubeCount (14 : ℕ) (26 : ℕ), ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (14 : ℕ) (26 : ℕ) (fun (x5 : ℕ) => Decidable.decide (x5 ∈ x1)) (x1 ++ x2) ++ PEqualNP.Defs.LratEncoding.enc2Cube (14 : ℕ) (26 : ℕ) x3) := by
  let pos : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let neg : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
  let label := fun (r : ℕ) ↦ decide (r ∈ pos)
  let rows := pos++neg
  change ∀ k < enc2CubeCount 14 26, ¬ FormulaSat (enc2 14 26 label rows ++ enc2Cube 14 26 k)
  change ∀ k : ℕ, ((19≤k ∧ k≤37) ∨ (54≤k ∧ k≤77)) → ¬∃ a : ℕ → Bool,
        (∀ c∈enc2 14 26 label rows ++ enc2Cube 14 26 k,ClauseSat a c) ∧
        (k=19 → ¬(a (ix 14 26 3 5 127+1)=true ∧ a (ix 14 26 3 5 16256+1)=true)) ∧
        (k=54 → ∃ e∈pos,∀ r∈pos,a (ix 14 26 3 0 r+1)=decide (r=e)) at remaining
  have tests : ∀ i : Fin 14, (∃ r∈rows,label r=true ∧ r.testBit i.val=false) ∧
      (∃ r∈rows,label r=false ∧ r.testBit i.val=true) := by decide
  have rowsOK := fun (i : ℕ) (hi : i<14) ↦ tests ⟨i,hi⟩
  intro k hk hsat
  obtain ⟨op,lo,hi⟩ := structural 14 26 label rows (by decide) (by decide) rowsOK k hk hsat
  change k/40 < 2 at op
  change 14 ≤ k % 40 at lo
  change k % 40+2 < 40 at hi
  obtain ⟨a,aa⟩ := hsat
  have inRange : (19≤k ∧ k≤37) ∨ (54≤k ∧ k≤77) := by
    by_cases first : k < 40
    · obtain ⟨S,smallInputs,cost,hit⟩ := inputCover 14 26 label rows (by decide) (by decide)
        rowsOK k first a aa
      let pick := fun (i : Fin 7) ↦ ([129,514,260,4104,8208,1056,2112] : List ℕ).getD i.val 0
      have edge : ∀ i : Fin 7, pick i∈rows ∧ label (pick i)=true := by decide
      have apart : ∀ i j : Fin 7, ∀ v : Fin 14, (pick i).testBit v.val=true →
          (pick j).testBit v.val=true → i=j := by decide
      have select (i : Fin 7) : ∃ v : ↥S, (pick i).testBit v.val=true := by
        obtain ⟨v,hv,bit⟩ := hit (pick i) (edge i).1 (Or.inl (edge i).2)
        exact ⟨⟨v,hv⟩,bit⟩
      choose f marked using select
      have inj : Function.Injective f := by
        intro i j eqn
        apply apart i j ⟨(f i).val,smallInputs _ (f i).property⟩ (marked i)
        rw [eqn]
        exact marked j
      have seven : 7≤S.card := by simpa using Fintype.card_le_of_injective f inj
      rw [Nat.mod_eq_of_lt first] at lo hi
      exact Or.inl ⟨by omega,by omega⟩
    · right
      omega
  apply remaining k inRange
  refine ⟨a,aa,?_,?_⟩
  · intro tight simultaneous
    subst k
    obtain ⟨S,raw,small,hits⟩ := inputCover 14 26 label rows (by decide) (by decide) rowsOK
      19 (by decide) a aa
    have positive (r : ℕ) (hr : r∈pos) : ∃ i∈S,r.testBit i=true :=
      hits r (List.mem_append_left _ hr) (Or.inl (by simpa [label] using hr))
    let fanoRows : List ℕ := [129,257,1025,130,514,8194,260,4100,8196,136,2056,
      4104,1040,2064,8208,544,1056,4128,320,576,2112]
    let pick (i : Fin 7) : ℕ := ([129,514,260,4104,8208,1056,2112] : List ℕ).getD i.val 0
    let mate (i : Fin 7) : ℕ := ([7,9,8,12,13,10,11] : List ℕ).getD i.val 0
    let vertex (a : Fin 7 → Bool) (i : Fin 7) : ℕ := if a i then i.val else mate i
    have choices : ∀ a : Fin 7 → Bool,
        (∀ r∈fanoRows,∃ i : Fin 7,r.testBit (vertex a i)=true) →
        (∀ i : Fin 7,(127 : ℕ).testBit (vertex a i)=false) ∨
        (∀ i : Fin 7,(16256 : ℕ).testBit (vertex a i)=false) := by decide
    have colours (S : Finset ℕ) (bound : ∀ i∈S,i<14) (small : S.card≤7)
        (hit : ∀ r∈fanoRows, ∃ i∈S,r.testBit i=true) :
        (¬ ∃ i∈S,(127 : ℕ).testBit i=true) ∨ (¬ ∃ i∈S,(16256 : ℕ).testBit i=true) := by
      have edge : ∀ i : Fin 7, pick i∈fanoRows := by decide
      have apart : ∀ i j : Fin 7, ∀ v : Fin 14, (pick i).testBit v.val=true →
          (pick j).testBit v.val=true → i=j := by decide
      have decode : ∀ i : Fin 7, ∀ v : Fin 14, (pick i).testBit v.val=true →
          (if v.val<7 then i.val else mate i)=v.val := by decide
      have sel (i : Fin 7) : ∃ v : ↥S, (pick i).testBit v.val=true := by
        obtain ⟨v,hv,bit⟩ := hit (pick i) (edge i)
        exact ⟨⟨v,hv⟩,bit⟩
      choose f hf using sel
      have inj : Function.Injective f := by
        intro i j he
        apply apart i j ⟨(f i).val,bound _ (f i).property⟩ (hf i)
        rw [he]
        exact hf j
      have eqcard : Fintype.card (Fin 7) = Fintype.card ↥S :=
        Nat.le_antisymm (Fintype.card_le_of_injective f inj) (by simpa using small)
      have surj := ((Fintype.bijective_iff_injective_and_card f).2 ⟨inj,eqcard⟩).2
      let a := fun (i : Fin 7) ↦ decide ((f i).val<7)
      have value (i : Fin 7) : vertex a i=(f i).val := by
        simpa [vertex,a] using decode i ⟨(f i).val,bound _ (f i).property⟩ (hf i)
      have forward (r : ℕ) (h : ∃ v∈S,r.testBit v=true) : ∃ i : Fin 7,r.testBit (vertex a i)=true := by
        obtain ⟨v,hv,bit⟩ := h
        obtain ⟨i,eqn⟩ := surj ⟨v,hv⟩
        exact ⟨i,by simpa [value,eqn] using bit⟩
      have missing (r : ℕ) (all : ∀ i : Fin 7,r.testBit (vertex a i)=false) : ¬∃ v∈S,r.testBit v=true := by
        intro meets
        obtain ⟨i,bit⟩ := forward r meets
        rw [all i] at bit
        contradiction
      rcases choices a (fun r hr ↦ forward r (hit r hr)) with h | h
      · exact Or.inl (missing _ h)
      · exact Or.inr (missing _ h)
    rcases colours S raw (by simpa using small) positive with left | right
    · exact left (hits 127 (by decide) (Or.inr simultaneous.1))
    · exact right (hits 16256 (by decide) (Or.inr simultaneous.2))
  · intro tight
    subst k
    obtain ⟨u,hu,v,hv,order,values,forward⟩ := firstOr 14 26 label rows (by decide) (by decide)
      rowsOK 54 (by decide) (by decide) a aa
    have finitePair : ∀ u v : Fin 14, u<v →
        (∀ r∈neg,(r.testBit u.val && r.testBit v.val)=false) →
        ∃ e∈pos,∀ r∈pos,(r.testBit u.val && r.testBit v.val)=decide (r=e) := by decide
    have allOff (r : ℕ) (hr : r∈neg) : (r.testBit u && r.testBit v)=false := by
      have sep : ∀ x∈neg,label x=false := by decide
      have member : r∈rows := List.mem_append_right _ hr
      rw [←values r member]
      cases row : a (ix 14 26 3 0 r+1) with
      | false => rfl
      | true => exact (forward r member row).symm.trans (sep r hr)
    obtain ⟨e,he,correct⟩ := finitePair ⟨u,hu⟩ ⟨v,hv⟩ order allOff
    exact ⟨e,he,fun r hr ↦ (values r (List.mem_append_left _ hr)).trans (correct r hr)⟩

-- Reproducible proofs of the three general premises follow.
-- The literal conventions are those of the project LratEncoding and the LRAT Link module.
-- namespace Eric.HeawoodCube
-- open PEqualNP.Defs.LratEncoding
--
-- abbrev Holds (a : ℕ → Bool) (v : ℕ) := a (v+1) = true
-- abbrev Reads (a : ℕ → Bool) (F : List (List ℕ)) := ∀ c ∈ F, ClauseSat a c
--
-- theorem lp (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = true ↔ Holds a v := by
--   unfold litVal P Holds
--   rw [show (2*v+2)/2 = v+1 by omega, show (2*v+2)%2=0 by omega]
--   cases a (v+1) <;> decide
-- theorem lq (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = true ↔ ¬ Holds a v := by
--   unfold litVal Q Holds
--   rw [show (2*v+3)/2 = v+1 by omega, show (2*v+3)%2=1 by omega]
--   cases a (v+1) <;> decide
-- theorem lbl (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = true ↔ a (v+1) = b := by
--   cases b <;> simp [L,lp,lq,Holds]
-- theorem more (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
--     ClauseSat a (l::c) ↔ litVal a l = true ∨ ClauseSat a c := by simp [ClauseSat]
-- theorem noneSat (a : ℕ → Bool) : ¬ ClauseSat a [] := by simp [ClauseSat]
--
-- theorem wireChosen {a : ℕ → Bool} {lim : ℕ} (f : ℕ → ℕ)
--     (h : ClauseSat a ((List.range lim).map fun w ↦ P (f w))) : ∃ w < lim, Holds a (f w) := by
--   obtain ⟨l,hl,v⟩ := h
--   obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hl
--   exact ⟨w,List.mem_range.mp hw,(lp _ _).mp v⟩
--
-- variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {a : ℕ → Bool}
--
-- theorem padClauses (H : Reads a (enc2 n s g rows)) {j : ℕ} (hj : j < s) :
--     (Holds a (ix n s 7 j 0) → Holds a (ix n s 0 j 2)) ∧
--     (Holds a (ix n s 0 j 2) → Holds a (ix n s 7 j 0)) ∧
--     (Holds a (ix n s 2 j (n+j)) → Holds a (ix n s 7 j 0)) := by
--   have take (c : List ℕ) (hc : c ∈ fPad n s) : ClauseSat a c := H c (by simp [enc2,enc,hc])
--   have localGate (c : List ℕ) (h : c ∈
--       [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n+j))],
--        [Q (ix n s 7 j 0), P (ix n s 2 j (n+j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
--        [P (ix n s 7 j 0), Q (ix n s 1 j (n+j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n+j))]]) :
--       ClauseSat a c := take c (List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,h⟩)
--   refine ⟨?_,?_,?_⟩
--   · have h := localGate [Q (ix n s 7 j 0), P (ix n s 0 j 2)] (by simp)
--     simp only [more,noneSat,lp,lq,or_false] at h
--     tauto
--   · have h := localGate [P (ix n s 7 j 0), Q (ix n s 0 j 2)] (by simp)
--     simp only [more,noneSat,lp,lq,or_false] at h
--     tauto
--   · have h := localGate [P (ix n s 7 j 0), Q (ix n s 2 j (n+j))] (by simp)
--     simp only [more,noneSat,lp,lq,or_false] at h
--     tauto
--
-- theorem padBefore (H : Reads a (enc2 n s g rows)) {i : ℕ} (hi : i < s-1) :
--     Holds a (ix n s 7 (i+1) 0) → Holds a (ix n s 7 i 0) := by
--   let c := [Q (ix n s 7 (i+1) 0), P (ix n s 7 i 0)]
--   have mem : c ∈ fPre n s := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
--   have h := H c (by simp [enc2,enc,mem])
--   simp only [c,more,noneSat,lp,lq,or_false] at h
--   tauto
--
-- theorem gateRow (H : Reads a (enc2 n s g rows)) {j r : ℕ} (hj : j<s) (hr : r∈rows) :
--     Reads a (gateCl n s j r) := by
--   intro c hc
--   have mem : c ∈ fGate n s rows := List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
--     List.mem_flatMap.mpr ⟨r,hr,hc⟩⟩
--   exact H c (by simp [enc2,enc,mem])
--
-- theorem highPad (H : Reads a (enc2 n s g rows)) {j r : ℕ} (hj : j<s) (hr : r∈rows)
--     (hp : Holds a (ix n s 7 j 0)) : Holds a (ix n s 3 j r) := by
--   have ht := (padClauses H hj).1 hp
--   have h := gateRow H hj hr [Q (ix n s 0 j 2),P (ix n s 3 j r)] (by simp [gateCl])
--   simp only [more,noneSat,lp,lq,or_false] at h
--   tauto
--
-- theorem outputChosen (H : Reads a (enc2 n s g rows)) : ∃ k < n+s+1, Holds a (ix n s 6 0 k) := by
--   apply wireChosen (ix n s 6 0)
--   apply H
--   simp [enc2,enc,fOutAlo]
--
-- theorem outputRow (H : Reads a (enc2 n s g rows)) {k r : ℕ} (hk : k < n+s+1) (hr : r∈rows) :
--     Reads a (outEq n s g k r) := by
--   intro c hc
--   have mem : c ∈ fOutEq n s g rows := List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr
--     ⟨k,List.mem_range.mpr hk,hc⟩⟩
--   exact H c (by simp [enc2,enc,mem])
--
-- theorem selectedRow (H : Reads a (enc2 n s g rows)) {k r : ℕ}
--     (lo : n≤k) (hi : k<n+s) (hr : r∈rows) (sel : Holds a (ix n s 6 0 k)) :
--     a (ix n s 3 (k-n) r + 1) = g r := by
--   have h := outputRow H (by omega : k<n+s+1) hr
--     [Q (ix n s 6 0 k), L (ix n s 3 (k-n) r) (g r)] (by simp [outEq,Nat.not_lt.mpr lo,hi])
--   simp only [more,noneSat,lq,lbl,or_false] at h
--   tauto
--
-- theorem noLastPad (H : Reads a (enc2 n s g rows)) (hn : 0<n) (hs : 0<s)
--     (test : ∀ i<n, (∃ r∈rows, g r=true ∧ r.testBit i=false) ∧
--         (∃ r∈rows, g r=false ∧ r.testBit i=true)) : ¬ Holds a (ix n s 7 (s-1) 0) := by
--   intro last
--   have back (d : ℕ) : ∀ j, j+d=s-1 → j<s → Holds a (ix n s 7 j 0) := by
--     induction d with
--     | zero => intro j e _; simpa [show j=s-1 by omega] using last
--     | succ d ih =>
--       intro j e hj
--       exact padBefore H (by omega) (ih (j+1) (by omega) (by omega))
--   obtain ⟨k,hk,sel⟩ := outputChosen H
--   by_cases raw : k<n
--   · obtain ⟨r,hr,on,off⟩ := (test k raw).1
--     have h := outputRow H hk hr [Q (ix n s 6 0 k)] (by simp [outEq,raw,off,on])
--     simp [more,noneSat,lq,sel] at h
--   · by_cases gate : k<n+s
--     · obtain ⟨r,hr,off,_⟩ := (test 0 hn).2
--       have yes := highPad H (by omega : k-n<s) hr (back (s-1-(k-n)) (k-n) (by omega) (by omega))
--       have no := selectedRow H (by omega) gate hr sel
--       rw [off] at no
--       exact Bool.noConfusion (yes.symm.trans no)
--     · obtain ⟨r,hr,on,_⟩ := (test 0 hn).1
--       have h := outputRow H hk hr [Q (ix n s 6 0 k)] (by simp [outEq,raw,gate,on])
--       simp [more,noneSat,lq,sel] at h
--
-- theorem finalSelected (H : Reads a (enc2 n s g rows)) (hs : 0<s)
--     (active : ¬ Holds a (ix n s 7 (s-1) 0)) : Holds a (ix n s 6 0 (n+s-1)) := by
--   let c := [P (ix n s 6 0 (n+s-1)),P (ix n s 7 (s-1) 0)]
--   have hc : c ∈ fOut n s := by simp [fOut,Nat.ne_of_gt hs,c]
--   have h := H c (by simp [enc2,enc,hc])
--   simp only [c,more,lp,noneSat,or_false] at h
--   tauto
--
-- theorem inputRow (H : Reads a (enc2 n s g rows)) {e j r k : ℕ} (he : e=1 ∨ e=2)
--     (hgate : j<s) (hr : r∈rows) (raw : k<n) (used : Holds a (ix n s e j k)) :
--     a (ix n s (e+3) j r + 1) = r.testBit k := by
--   let c := [Q (ix n s e j k),L (ix n s (e+3) j r) (r.testBit k)]
--   have mem : c ∈ fSrcEq n s rows := List.mem_flatMap.mpr ⟨e,by simpa using he,
--     List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hgate,List.mem_flatMap.mpr ⟨r,hr,
--     List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),by simp [c,srcEq,raw]⟩⟩⟩⟩
--   have h := H c (by simp [enc2,enc,mem])
--   simp only [c,more,lq,lbl,noneSat,or_false] at h
--   tauto
--
-- theorem noRawOutputPin (H : Reads a (enc2 n s g rows)) (hs : 0<s)
--     (out : Holds a (ix n s 6 0 (n+s-1))) {k e op : ℕ} (he : e=1 ∨ e=2)
--     (raw : k<n) (pin : Holds a (ix n s e (s-1) k)) (hop : op=0 ∨ op=1)
--     (oper : Holds a (ix n s 0 (s-1) op))
--     (wits : (∃ r∈rows, g r=true ∧ r.testBit k=false) ∧
--       (∃ r∈rows, g r=false ∧ r.testBit k=true)) : False := by
--   have eval {r : ℕ} (hr : r∈rows) : a (ix n s 3 (s-1) r + 1) = g r := by
--     have hh := selectedRow H (by omega : n≤n+s-1) (by omega) hr out
--     rwa [show n+s-1-n=s-1 by omega] at hh
--   rcases hop with rfl | rfl
--   · obtain ⟨r,hr,yes,no⟩ := wits.1
--     have w : Holds a (ix n s 3 (s-1) r) := (eval hr).trans yes
--     have bad : ¬ Holds a (ix n s (e+3) (s-1) r) := by
--       intro h
--       exact Bool.noConfusion (h.symm.trans ((inputRow H he (by omega) hr raw pin).trans no))
--     have clause := gateRow H (by omega : s-1<s) hr
--       [Q (ix n s 0 (s-1) 0),Q (ix n s 3 (s-1) r),P (ix n s (e+3) (s-1) r)]
--       (by rcases he with rfl | rfl <;> simp [gateCl])
--     simp only [more,lq,lp,noneSat,or_false] at clause
--     tauto
--   · obtain ⟨r,hr,no,yes⟩ := wits.2
--     have w : ¬ Holds a (ix n s 3 (s-1) r) := by
--       intro h
--       exact Bool.noConfusion (h.symm.trans ((eval hr).trans no))
--     have good : Holds a (ix n s (e+3) (s-1) r) := (inputRow H he (by omega) hr raw pin).trans yes
--     have clause := gateRow H (by omega : s-1<s) hr
--       [Q (ix n s 0 (s-1) 1),P (ix n s 3 (s-1) r),Q (ix n s (e+3) (s-1) r)]
--       (by rcases he with rfl | rfl <;> simp [gateCl])
--     simp only [more,lq,lp,noneSat,or_false] at clause
--     tauto
--
-- theorem secondPin (H : Reads a (enc2 n s g rows)) {j : ℕ} (hj : j<s) :
--     ∃ b < n+j+1, Holds a (ix n s 2 j b) := by
--   apply wireChosen (ix n s 2 j)
--   let c := (List.range (n+j+1)).map fun w ↦ P (ix n s 2 j w)
--   have mem : c ∈ fSrcAlo n s := List.mem_flatMap.mpr ⟨2,by simp,
--     List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩⟩
--   exact H c (by simp [enc2,enc,mem])
--
-- theorem pinsOrdered (H : Reads a (enc2 n s g rows)) {j u v : ℕ} (hj : j<s) (hu : u<n+j+1)
--     (h1 : Holds a (ix n s 1 j u)) (h2 : Holds a (ix n s 2 j v)) (active : ¬ Holds a (ix n s 7 j 0)) :
--     u<v := by
--   by_contra h
--   let c := [Q (ix n s 1 j u),Q (ix n s 2 j v),P (ix n s 7 j 0)]
--   have hc : c ∈ fOrd n s := List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_flatMap.mpr
--     ⟨u,List.mem_range.mpr hu,List.mem_map.mpr ⟨v,List.mem_range.mpr (by omega),rfl⟩⟩⟩
--   have h' := H c (by simp [enc2,enc,hc])
--   simp only [c,more,lq,lp,noneSat,or_false] at h'
--   tauto
--
-- theorem prune (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hn : 0<n) (hs : 0<s)
--     (wits : ∀ i<n, (∃ r∈rows, g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows, g r=false ∧ r.testBit i=true))
--     (k : ℕ) (range : k < enc2CubeCount n s)
--     (sat : FormulaSat (enc2 n s g rows ++ enc2Cube n s k)) :
--     k/(n+s)<2 ∧ n≤k % (n+s) ∧ k % (n+s)+2<n+s := by
--   obtain ⟨a,ha⟩ := sat
--   have H : Reads a (enc2 n s g rows) := fun c hc ↦ ha c (List.mem_append_left _ hc)
--   have cube : Reads a (enc2Cube n s k) := fun c hc ↦ ha c (List.mem_append_right _ hc)
--   let u := k % (n+s)
--   let op := k/(n+s)
--   have h1c := cube [P (ix n s 1 (s-1) u)] (by simp [enc2Cube,u])
--   have hoc := cube [P (ix n s 0 (s-1) op)] (by simp [enc2Cube,op])
--   simp only [more,lp,noneSat,or_false] at h1c hoc
--   have active := noLastPad H hn hs wits
--   have out := finalSelected H hs active
--   have hop : op<3 := by
--     apply (Nat.div_lt_iff_lt_mul (by omega : 0<n+s)).mpr
--     simpa [enc2CubeCount] using range
--   have op2 : op ≠ 2 := by
--     intro eqn
--     rw [eqn] at hoc
--     exact active ((padClauses H (by omega : s-1<s)).2.1 hoc)
--   have smallOp (t : ℕ) (lt : t < 3) (ne : t ≠ 2) : t=0 ∨ t=1 := by omega
--   have hraw : n≤u := by
--     by_contra h
--     have small : u<n := by omega
--     exact noRawOutputPin H hs out (Or.inl rfl) small h1c (smallOp op hop op2) hoc (wits u small)
--   obtain ⟨v,hv,vsel⟩ := secondPin H (by omega : s-1<s)
--   have hu : u<n+s := Nat.mod_lt _ (by omega)
--   have ord := pinsOrdered H (by omega : s-1<s) (by omega : u<n+(s-1)+1) h1c vsel active
--   have lower : v ≠ n+(s-1) := by
--     intro e
--     rw [e] at vsel
--     exact active ((padClauses H (by omega : s-1<s)).2.2 vsel)
--   change op<2 ∧ n≤u ∧ u+2<n+s
--   exact ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hop) op2,hraw,by omega⟩
--
-- def signal (a : ℕ → Bool) (n s w r : ℕ) : Prop :=
--   if w<n then r.testBit w=true else
--     ¬ Holds a (ix n s 7 (w-n) 0) ∧ Holds a (ix n s 3 (w-n) r)
--
-- theorem pinChoice (H : Reads a (enc2 n s g rows)) {e j : ℕ} (he : e=1 ∨ e=2)
--     (hj : j<s) (active : ¬ Holds a (ix n s 7 j 0)) :
--     ∃ b < n+j, Holds a (ix n s e j b) := by
--   let c := (List.range (n+j+1)).map fun w ↦ P (ix n s e j w)
--   have mem : c ∈ fSrcAlo n s := List.mem_flatMap.mpr ⟨e,by simpa using he,
--     List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩⟩
--   obtain ⟨b,hb,sel⟩ := wireChosen (ix n s e j) (H c (by simp [enc2,enc,mem]))
--   refine ⟨b,?_,sel⟩
--   by_contra! low
--   have eqn : b=n+j := by omega
--   rw [eqn] at sel
--   let stop := [P (ix n s 7 j 0), Q (ix n s e j (n+j))]
--   have data : stop ∈ fPad n s := List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
--     by rcases he with rfl | rfl <;> simp [stop]⟩
--   have disj := H stop (by simp [enc2,enc,data])
--   simp only [stop,more,lp,lq,noneSat,or_false] at disj
--   tauto
--
-- theorem pinLive (H : Reads a (enc2 n s g rows)) {e j r u : ℕ} (he : e=1 ∨ e=2)
--     (hj : j<s) (hr : r∈rows) (hu : u<n+j) (sel : Holds a (ix n s e j u))
--     (on : Holds a (ix n s (e+3) j r)) : signal a n s u r := by
--   unfold signal
--   split_ifs with raw
--   · exact (inputRow H he hj hr raw sel).symm.trans on
--   · have lo : n≤u := by omega
--     have addr : n+(u-n)=u := by omega
--     have idx : u-n<j := by omega
--     let stop := [Q (ix n s 7 (u-n) 0),Q (ix n s e j (n+(u-n)))]
--     have memStop : stop ∈ fPadRd n s := List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
--       List.mem_flatMap.mpr ⟨u-n,List.mem_range.mpr idx,by rcases he with rfl | rfl <;> simp [stop]⟩⟩
--     have hp := H stop (by simp [enc2,enc,memStop])
--     simp only [stop,addr,more,lq,noneSat,or_false] at hp
--     let c := [Q (ix n s e j u),Q (ix n s (e+3) j r),P (ix n s 3 (u-n) r)]
--     have mem : c ∈ fSrcEq n s rows := List.mem_flatMap.mpr ⟨e,by simpa using he,
--       List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_flatMap.mpr ⟨r,hr,
--       List.mem_flatMap.mpr ⟨u,List.mem_range.mpr (by omega),by simp [c,srcEq,raw,hu]⟩⟩⟩⟩
--     have bit := H c (by simp [enc2,enc,mem])
--     simp only [c,more,lq,lp,noneSat,or_false] at bit
--     tauto
--
-- theorem preceding (H : Reads a (enc2 n s g rows)) (hn : 0<n) {j : ℕ} (hj : j<s) :
--     ∃ u < n+j, ∃ v < n+j, ∀ r∈rows, signal a n s (n+j) r → signal a n s u r ∨ signal a n s v r := by
--   by_cases dead : Holds a (ix n s 7 j 0)
--   · exact ⟨0,by omega,0,by omega,by simp [signal,dead]⟩
--   obtain ⟨u,hu,lu⟩ := pinChoice H (Or.inl rfl) hj dead
--   obtain ⟨v,hv,lv⟩ := pinChoice H (Or.inr rfl) hj dead
--   refine ⟨u,hu,v,hv,?_⟩
--   have op : Holds a (ix n s 0 j 0) ∨ Holds a (ix n s 0 j 1) := by
--     let c := [P (ix n s 0 j 0),P (ix n s 0 j 1),P (ix n s 0 j 2)]
--     have mem : c ∈ fOp n s := List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
--     have hh := H c (by simp [enc2,enc,mem])
--     simp only [c,more,lp,noneSat,or_false] at hh
--     have block := (padClauses H hj).2.1
--     tauto
--   intro r hr h
--   have live : Holds a (ix n s 3 j r) := by simpa [signal,dead] using h
--   have ux := pinLive H (Or.inl rfl) hj hr hu lu
--   have vx := pinLive H (Or.inr rfl) hj hr hv lv
--   change Holds a (ix n s 4 j r) → _ at ux
--   change Holds a (ix n s 5 j r) → _ at vx
--   rcases op with isAnd | isOr
--   · have cl := gateRow H hj hr [Q (ix n s 0 j 0),Q (ix n s 3 j r),P (ix n s 4 j r)] (by simp [gateCl])
--     simp only [more,lp,lq,noneSat,or_false] at cl
--     tauto
--   · have cl := gateRow H hj hr [Q (ix n s 0 j 1),Q (ix n s 3 j r),P (ix n s 4 j r),P (ix n s 5 j r)] (by simp [gateCl])
--     simp only [more,lp,lq,noneSat,or_false] at cl
--     tauto
--
-- theorem frontier (n t : ℕ) (rows : List ℕ) (lit : ℕ → ℕ → Prop)
--     (parents : ∀ j<t, ∃ u < n+j, ∃ v < n+j, ∀ r∈rows, lit (n+j) r → lit u r ∨ lit v r)
--     (W : Finset ℕ) (bounded : ∀ w∈W,w<n+t) :
--     ∃ X : Finset ℕ, (∀ w∈X,w<n) ∧ X.card≤W.card+t ∧
--       ∀ r∈rows, (∃ w∈W,lit w r) → ∃ x∈X,lit x r := by
--   induction t generalizing W with
--   | zero => exact ⟨W,by simpa using bounded,by simp,fun _ _ h ↦ h⟩
--   | succ t ih =>
--     have smaller := fun j (h : j<t) ↦ parents j (by omega)
--     by_cases mem : n+t ∈ W
--     · obtain ⟨u,hu,v,hv,read⟩ := parents t (by omega)
--       let V := insert u (insert v (W.erase (n+t)))
--       have bv : ∀ i∈V, i<n+t := by
--         intro i hv'
--         rcases Finset.mem_insert.mp hv' with rfl | rest
--         · exact hu
--         rcases Finset.mem_insert.mp rest with rfl | final
--         · exact hv
--         obtain ⟨ne,inc⟩ := Finset.mem_erase.mp final
--         have := bounded i inc
--         omega
--       obtain ⟨X,bx,cx,works⟩ := ih smaller V bv
--       refine ⟨X,bx,?_,?_⟩
--       · have a1 := Finset.card_insert_le u (insert v (W.erase (n+t)))
--         have a2 := Finset.card_insert_le v (W.erase (n+t))
--         have a3 := Finset.card_erase_of_mem mem
--         have a4 : 0<W.card := Finset.card_pos.mpr ⟨n+t,mem⟩
--         change X.card ≤ (insert u (insert v (W.erase (n+t)))).card+t at cx
--         omega
--       · rintro r hr ⟨w,hw,hwr⟩
--         apply works r hr
--         by_cases eqn : w=n+t
--         · subst w
--           rcases read r hr hwr with left | right
--           · exact ⟨u,by simp [V],left⟩
--           · exact ⟨v,by simp [V],right⟩
--         · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨eqn,hw⟩)),hwr⟩
--     · have bw : ∀ w∈W,w<n+t := by
--         intro w hw
--         have ne : w≠n+t := fun eqn ↦ mem (eqn ▸ hw)
--         have := bounded w hw
--         omega
--       obtain ⟨X,bx,cx,works⟩ := ih smaller W bw
--       exact ⟨X,bx,by omega,works⟩
--
-- theorem coverWire (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hn : 0<n) (hs : 0<s)
--     (wits : ∀ i<n, (∃ r∈rows, g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows, g r=false ∧ r.testBit i=true))
--     (k : ℕ) (width : k<n+s) (a : ℕ → Bool) (aa : ∀ c∈enc2 n s g rows ++ enc2Cube n s k, ClauseSat a c) :
--     ∃ S : Finset ℕ, (∀ i∈S,i<n) ∧ S.card ≤ k-n+2 ∧
--       ∀ r∈rows, (g r=true ∨ a (ix n s 3 (k-n) r+1)=true) → ∃ i∈S, r.testBit i=true := by
--   have H : Reads a (enc2 n s g rows) := fun c hc ↦ aa c (List.mem_append_left _ hc)
--   have B : Reads a (enc2Cube n s k) := fun c hc ↦ aa c (List.mem_append_right _ hc)
--   have pm : k % (n+s)=k := Nat.mod_eq_of_lt width
--   have pd : k/(n+s)=0 := Nat.div_eq_of_lt width
--   have pin := B [P (ix n s 1 (s-1) k)] (by simp [enc2Cube,pm])
--   have oper := B [P (ix n s 0 (s-1) 0)] (by simp [enc2Cube,pd])
--   simp only [more,lp,noneSat,or_false] at pin oper
--   have range : k<enc2CubeCount n s := by unfold enc2CubeCount; omega
--   have bounds := prune n s g rows hn hs wits k range ⟨a,aa⟩
--   rw [pm] at bounds
--   have out := finalSelected H hs (noLastPad H hn hs wits)
--   have lead (r : ℕ) (hr : r∈rows) (yes : g r=true) : signal a n s k r := by
--     have hh := selectedRow H (by omega : n≤n+s-1) (by omega) hr out
--     rw [show n+s-1-n=s-1 by omega,yes] at hh
--     have live : Holds a (ix n s 3 (s-1) r) := hh
--     have cl := gateRow H (by omega : s-1<s) hr
--       [Q (ix n s 0 (s-1) 0),Q (ix n s 3 (s-1) r),P (ix n s 4 (s-1) r)] (by simp [gateCl])
--     simp only [more,lp,lq,noneSat,or_false] at cl
--     apply pinLive H (Or.inl rfl) (by omega : s-1<s) hr (by omega : k<n+(s-1)) pin
--     change Holds a (ix n s 4 (s-1) r)
--     tauto
--   have idx : k-n<s-1 := by omega
--   have addr : n+(k-n)=k := by omega
--   let bad := [Q (ix n s 7 (k-n) 0),Q (ix n s 1 (s-1) (n+(k-n)))]
--   have badMem : bad ∈ fPadRd n s := List.mem_flatMap.mpr ⟨s-1,List.mem_range.mpr (by omega),
--     List.mem_flatMap.mpr ⟨k-n,List.mem_range.mpr idx,by simp [bad]⟩⟩
--   have cl := H bad (by simp [enc2,enc,badMem])
--   simp only [bad,addr,more,lq,noneSat,or_false] at cl
--   have kept : ¬ Holds a (ix n s 7 (k-n) 0) := cl.resolve_right (fun h ↦ h pin)
--   have additional (r : ℕ) (high : a (ix n s 3 (k-n) r+1)=true) : signal a n s k r := by
--     simpa [signal,Nat.not_lt.mpr bounds.2.1,kept,Holds] using high
--   obtain ⟨X,raw,small,hits⟩ := frontier n (k-n+1) rows (signal a n s)
--     (fun j hj ↦ preceding H hn (by omega)) {k} (by simp; omega)
--   refine ⟨X,raw,?_,?_⟩
--   · simp only [Finset.card_singleton] at small
--     omega
--   · intro r hr yes
--     obtain ⟨w,hw,high⟩ := hits r hr ⟨k,by simp,yes.elim (lead r hr) (additional r)⟩
--     exact ⟨w,hw,by simpa [signal,raw w hw] using high⟩
--
--
-- set_option maxHeartbeats 1200000 in
-- theorem firstOr (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hn : 0<n) (hs : 1<s)
--     (wits : ∀ i<n, (∃ r∈rows,g r=true ∧ r.testBit i=false) ∧ (∃ r∈rows,g r=false ∧ r.testBit i=true))
--     (k : ℕ) (pinIndex : k % (n+s)=n) (kind : k/(n+s)=1) (a : ℕ → Bool)
--     (aa : ∀ c∈enc2 n s g rows ++ enc2Cube n s k,ClauseSat a c) :
--     ∃ u<n, ∃ v<n, u<v ∧
--       (∀ r∈rows, a (ix n s 3 0 r+1)=(r.testBit u && r.testBit v)) ∧
--       (∀ r∈rows,a (ix n s 3 0 r+1)=true → g r=true) := by
--   have H : Reads a (enc2 n s g rows) := fun c hc ↦ aa c (List.mem_append_left _ hc)
--   have B : Reads a (enc2Cube n s k) := fun c hc ↦ aa c (List.mem_append_right _ hc)
--   have pin := B [P (ix n s 1 (s-1) n)] (by simp [enc2Cube,pinIndex])
--   have oper := B [P (ix n s 0 (s-1) 1)] (by simp [enc2Cube,kind])
--   simp only [more,lp,noneSat,or_false] at pin oper
--   have lasts : s-1<s := by omega
--   have zero : 0<s := by omega
--   have out := finalSelected H zero (noLastPad H hn zero wits)
--   let bad := [Q (ix n s 7 0 0),Q (ix n s 1 (s-1) (n+0))]
--   have bm : bad ∈ fPadRd n s := List.mem_flatMap.mpr ⟨s-1,List.mem_range.mpr lasts,
--     List.mem_flatMap.mpr ⟨0,List.mem_range.mpr (by omega),by simp [bad]⟩⟩
--   have cl := H bad (by simp [enc2,enc,bm])
--   simp only [bad,Nat.add_zero,more,lq,noneSat,or_false] at cl
--   have live : ¬Holds a (ix n s 7 0 0) := cl.resolve_right (fun h ↦ h pin)
--   have forward (r : ℕ) (hr : r∈rows) (z : Holds a (ix n s 3 0 r)) : g r=true := by
--     have src := H [Q (ix n s 1 (s-1) n),P (ix n s 4 (s-1) r),Q (ix n s 3 (n-n) r)] (by
--       have mem : [Q (ix n s 1 (s-1) n),P (ix n s 4 (s-1) r),Q (ix n s 3 (n-n) r)]∈fSrcEq n s rows :=
--         List.mem_flatMap.mpr ⟨1,by simp,List.mem_flatMap.mpr ⟨s-1,List.mem_range.mpr lasts,
--           List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨n,List.mem_range.mpr (by omega),
--             by simp [srcEq,show n<n+(s-1) by omega]⟩⟩⟩⟩
--       simp only [Nat.sub_self] at mem ⊢
--       simp [enc2,enc,mem])
--     have gate := gateRow H lasts hr [Q (ix n s 0 (s-1) 1),P (ix n s 3 (s-1) r),
--         Q (ix n s 4 (s-1) r)] (by simp [gateCl])
--     simp only [Nat.sub_self,more,lq,lp,noneSat,or_false] at src gate
--     have last : Holds a (ix n s 3 (s-1) r) := by tauto
--     have eqn := selectedRow H (by omega : n≤n+s-1) (by omega) hr out
--     rw [show n+s-1-n=s-1 by omega] at eqn
--     exact eqn.symm.trans last
--   obtain ⟨u,hu,hU⟩ := pinChoice H (Or.inl rfl) zero live
--   obtain ⟨v,hv,hV⟩ := pinChoice H (Or.inr rfl) zero live
--   simp only [Nat.add_zero] at hu hv
--   have ord := pinsOrdered H zero (by omega : u<n+0+1) hU hV live
--   have opGate := H [P (ix n s 0 0 0),P (ix n s 0 0 1),P (ix n s 0 0 2)] (by
--     have mem : [P (ix n s 0 0 0),P (ix n s 0 0 1),P (ix n s 0 0 2)]∈fOp n s :=
--       List.mem_map.mpr ⟨0,List.mem_range.mpr zero,rfl⟩
--     simp [enc2,enc,mem])
--   simp only [more,lp,noneSat,or_false] at opGate
--   have notOr : ¬Holds a (ix n s 0 0 1) := by
--     intro sourceOr
--     obtain ⟨r,hr,no,yes⟩ := (wits u hu).2
--     have up : Holds a (ix n s 4 0 r) := (inputRow H (Or.inl rfl) zero hr hu hU).trans yes
--     have clause := gateRow H zero hr [Q (ix n s 0 0 1),P (ix n s 3 0 r),Q (ix n s 4 0 r)] (by simp [gateCl])
--     simp only [more,lp,lq,noneSat,or_false] at clause
--     have high : Holds a (ix n s 3 0 r) := by tauto
--     exact Bool.noConfusion (no.symm.trans (forward r hr high))
--   have noTrue : ¬Holds a (ix n s 0 0 2) := fun h ↦ live ((padClauses H zero).2.1 h)
--   have isAnd : Holds a (ix n s 0 0 0) := by tauto
--   refine ⟨u,hu,v,hv,ord,?_,forward⟩
--   intro r hr
--   have gx := gateRow H zero hr
--   have left := gx _ (show [Q (ix n s 0 0 0),Q (ix n s 3 0 r),P (ix n s 4 0 r)]∈gateCl n s 0 r by simp [gateCl])
--   have right := gx _ (show [Q (ix n s 0 0 0),Q (ix n s 3 0 r),P (ix n s 5 0 r)]∈gateCl n s 0 r by simp [gateCl])
--   have both := gx _ (show [Q (ix n s 0 0 0),P (ix n s 3 0 r),Q (ix n s 4 0 r),Q (ix n s 5 0 r)]∈gateCl n s 0 r by simp [gateCl])
--   simp only [more,lp,lq,noneSat,or_false] at left right both
--   have equivalent : Holds a (ix n s 3 0 r) ↔ Holds a (ix n s 4 0 r) ∧ Holds a (ix n s 5 0 r) := by
--     clear * - left right both isAnd
--     tauto
--   have rawU := inputRow H (Or.inl rfl) zero hr hu hU
--   have rawV := inputRow H (Or.inr rfl) zero hr hv hV
--   unfold Holds at equivalent
--   change a (ix n s 4 0 r+1)=r.testBit u at rawU
--   change a (ix n s 5 0 r+1)=r.testBit v at rawV
--   rw [rawU,rawV] at equivalent
--   rw [Bool.eq_iff_iff,Bool.and_eq_true]
--   exact equivalent
--
--
-- end Eric.HeawoodCube
