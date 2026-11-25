from pathlib import Path
job=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs/results/orch/lemmas');s=(repo/'ExceptionalCoefficientBridgeFlat.lean').read_text();imports='\n'.join(l for l in s.splitlines() if l.startswith('import '));per=s[s.index('lemma sum_perm_succ'):s.index('noncomputable def fixedT')];fixed=s[s.index('noncomputable def fixedT'):s.index('noncomputable def partner')]
tail=r'''
noncomputable def normalizedT (a r : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0,1,r,0],![1,a,-a*r,0],![r,-a*r,a*r^2,0],![0,0,0,0]]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_permanent (a r z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*normalizedT a r i j)=
      24+6*(a*(1-r)^2+2*(1+r))*z+(4*a^2*r^2+2*r^2+4*r+2)*z^2 := by
  simp [perm4,Matrix.of_apply,normalizedT]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_scalar (a r : ℂ) (hne : r+1≠0)
    (hs : a*(1-r)^2+2*(1+r)=0)
    (hq : 4*a^2*r^2+2*r^2+4*r+2=0) :
    r^4-4*r^3+14*r^2-4*r+1=0 ∧
      a= -(3*r^3-11*r^2+37*r+3)/4 := by
  have hm : (r+1)^2*(r^4-4*r^3+14*r^2-4*r+1)=0 := by
    linear_combination ((1-r)^4/2)*hq-(2*a*r^4-4*a*r^3+2*a*r^2-4*r^3-4*r^2)*hs
  have hQ : r^4-4*r^3+14*r^2-4*r+1=0 :=
    (mul_eq_zero.mp hm).resolve_left (pow_ne_zero 2 hne)
  refine ⟨hQ,?_⟩
  linear_combination ((r^3-(7/2:ℂ)*r^2+12*r+(5/2:ℂ))/4)*hs+((-a*r+(3/2:ℂ)*a-2)/4)*hQ

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma normalized_direction (a r : ℂ) (hne : r+1≠0)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ)+z*normalizedT a r i j)=24) :
    r^4-4*r^3+14*r^2-4*r+1=0 ∧ normalizedT a r=fixedT r := by
  have h1 := hp 1
  have hm1 := hp (-1)
  rw [normalized_permanent] at h1 hm1
  have hs : a*(1-r)^2+2*(1+r)=0 := by
    linear_combination (1/12:ℂ)*h1-(1/12:ℂ)*hm1
  have hq : 4*a^2*r^2+2*r^2+4*r+2=0 := by
    linear_combination (1/2:ℂ)*h1+(1/2:ℂ)*hm1
  obtain ⟨hQ,ha⟩ := normalized_scalar a r hne hs hq
  have ha4 : 4*a+3*r^3-11*r^2+37*r+3=0 := by
    linear_combination 4*ha
  have h12 : -a*r=(r^3-5*r^2+15*r-3)/4 := by
    linear_combination (-r/4)*ha4+(3/4:ℂ)*hQ
  have h22 : a*r^2=(r^3-r^2-r+1)/4 := by
    linear_combination (r^2/4)*ha4+((-3*r-1)/4)*hQ
  refine ⟨hQ,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [normalizedT,fixedT,ea,em,ep]
  all_goals first | rfl | linear_combination ha | linear_combination h12 | linear_combination h22

end PEqualNP.Outside.L_gct_231.ExceptionalDirectionNormalization
'''
out=imports+'\n\nnamespace PEqualNP.Outside.L_gct_231.ExceptionalDirectionNormalization\n\nabbrev ea (x y : ℂ) : ℂ := x+y\nabbrev em (x y : ℂ) : ℂ := x*y\nabbrev ep (x : ℂ) (n : ℕ) : ℂ := x^n\n\n'+per+fixed+tail;p=job/'ExceptionalDirectionNormalization.lean';p.write_text(out.rstrip()+'\n');print('Prepared normalization',p.stat().st_size)
