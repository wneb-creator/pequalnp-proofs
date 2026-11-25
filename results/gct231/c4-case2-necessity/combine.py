from pathlib import Path
import hashlib,json
base=Path('/tmp/oec/pequalnp-pilot-75/gct231');out=base/'case2-necessity'
helper=(base/'ResultantCommonRoot.lean').read_text()
assert hashlib.sha256(helper.encode()).hexdigest()=='7f6fb46d5724abb34a448d8ffdcb44adcbf2fa988ff1202bb6e8a86d62a7886c'
core=(out/'Case2NecessaryElimination.lean').read_text()
ns='PEqualNP.Outside.L_gct_231_aux.Case2Necessity'
imports=core[:core.index('namespace ')]
corebody=core[core.index('namespace '):]
extra='''
def originalSaturation (P B sat : ℂ) : ℂ :=
  9*B^3*P*sat - 6*B^2*P^3*sat - 12*B^2*P*sat + 10*B*P^3*sat - 1

theorem raw_resultants_vanish (P B U V : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) :
    Polynomial.resultant (qEliminant P B) (lEliminant P B) 2 2 = 0 ∧
    Polynomial.resultant (qEliminant P B) (cEliminant P B) 2 3 = 0 := by
  obtain ⟨hqe, hle, hce⟩ := eliminants_vanish P B U V hq hc hF hr hl
  obtain ⟨hqdeg, hldeg, hcdeg⟩ := eliminant_degree_bounds P B
  exact ⟨resultant_zero_of_common_root _ _ V 2 2 hqdeg hldeg (by decide) hqe hle,
    resultant_zero_of_common_root _ _ V 2 3 hqdeg hcdeg (by decide) hqe hce⟩

theorem six_equations_necessary (P B U V sat : ℂ)
    (hq : originalQ P B U V = 0) (hc : originalC P B U V = 0)
    (hF : scaleCurve P B = 0) (hr : originalR P B U V = 0)
    (hl : originalL P B U V = 0) (hs : originalSaturation P B sat = 0) :
    P ≠ 0 ∧ B ≠ 0 ∧ curveLeading P ≠ 0 ∧ chartDet P B ≠ 0 ∧
    Polynomial.resultant (qEliminant P B) (lEliminant P B) 2 2 = 0 ∧
    Polynomial.resultant (qEliminant P B) (cEliminant P B) 2 3 = 0 := by
  have hs' : P * B * chartDet P B * sat - 1 = 0 := by
    unfold originalSaturation at hs
    unfold chartDet
    linear_combination hs
  obtain ⟨hP, hB, hK, hW⟩ := chart_nonzero P B sat hF hs'
  obtain ⟨hql, hqc⟩ := raw_resultants_vanish P B U V hq hc hF hr hl
  exact ⟨hP, hB, hK, hW, hql, hqc⟩
'''
assert corebody.endswith('end '+ns+'\n')
source=imports+helper[helper.index('namespace '):]+'\n'+corebody[:-len('end '+ns+'\n')]+extra+'\nend '+ns+'\n'
(out/'Case2NecessaryResultants.lean').write_text(source)
print(json.dumps({'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'bytes':len(source.encode()),'lines':len(source.splitlines()),'helper_body_preserved':helper[helper.index('namespace '):] in source},indent=2))
