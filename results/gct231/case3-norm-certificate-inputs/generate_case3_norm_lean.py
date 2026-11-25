from pathlib import Path
import json,sympy as s,hashlib
r=Path(__file__).parent;b=s.symbols('beta');loc={'beta':b}
norms=json.loads((r/'c4-case3-bezout-inputs.json').read_text());rows=json.loads((r/'c4-case3-radical-bezout-inputs.json').read_text());cert=json.loads((r/'c4-case3-radical-modular-bezout.integer-certificate.json').read_text())
def horner(poly):
 cs=s.Poly(poly,b,domain=s.QQ).all_coeffs();assert all(c.q==1 for c in cs)
 text=str(cs[0])
 for c in cs[1:]:text='('+text+' * beta '+(' + '+str(c) if c>=0 else ' - '+str(-c))+')'
 return text
parse=lambda x:s.sympify(x,locals=loc)
parts=['import PEqualNP.Defs\n\nnamespace PEqualNP.Outside.L_gct_231_aux\n\nset_option maxHeartbeats 4000000 in\nset_option maxRecDepth 4096 in\ntheorem case3_norm_obstruction (beta : ℂ)\n']
for i,key in enumerate(['first_norm','second_norm']):parts.append('    (h'+str(i)+' : '+horner(parse(norms[key]))+' = 0)\n')
parts.append('    beta + 2 = 0 ∨ 2*beta - 1 = 0 := by\n  by_cases ha : beta + 2 = 0\n  · exact Or.inl ha\n  by_cases hb : 2*beta - 1 = 0\n  · exact Or.inr hb\n')
for i,row in enumerate(rows):
 fs=[x for x in row['factors'] if s.degree(parse(x['polynomial']),b)>1];assert [x['multiplicity'] for x in fs]==[1,4]
 e,f=[horner(parse(x['polynomial'])) for x in fs]
 end=[x for x in row['factors'] if s.degree(parse(x['polynomial']),b)==1];aa,bb=[x['multiplicity'] for x in end]
 assert parse(end[0]['polynomial'])==b+2 and parse(end[1]['polynomial'])==2*b-1 and row['factor_scale']=='-1'
 parts.append(f'  let f{i} : ℂ := {e}\n  let g{i} : ℂ := {f}\n')
 parts.append(f'''  have hf{i} : (f{i}*g{i}^4)*((beta+2)^{aa}*(2*beta-1)^{bb}) = 0 := by
    dsimp only [f{i}, g{i}]
    linear_combination -h{i}
  have hc{i} : f{i}*g{i}^4 = 0 :=
    (mul_eq_zero.mp hf{i}).resolve_right (mul_ne_zero (pow_ne_zero {aa} ha) (pow_ne_zero {bb} hb))
  have hp{i} : f{i}*g{i} = 0 := by
    rcases mul_eq_zero.mp hc{i} with h | h
    · simp [h]
    · have hz : g{i} = 0 := eq_zero_of_pow_eq_zero h
      simp [hz]
  have hr{i} : {horner(parse(row['radical_other']))} = 0 := by
    dsimp only [f{i}, g{i}] at hp{i}
    linear_combination hp{i}
''')
D=int(cert['scale']);A=sum(int(x)*b**i for i,x in enumerate(cert['first_multiplier']));B=sum(int(x)*b**i for i,x in enumerate(cert['second_multiplier']))
parts.append(f'  have impossible : ({D} : ℂ) = 0 := by\n    linear_combination ({horner(A)}) * hr0 + ({horner(B)}) * hr1\n  norm_num at impossible\n\nend PEqualNP.Outside.L_gct_231_aux\n')
text=''.join(parts);assert '_root_' not in text and chr(34) not in text and 'sorry' not in text
(r/'C4Case3Norm.lean').write_text(text)
(r/'C4Case3NormAudit.lean').write_text(text+'\n#print axioms PEqualNP.Outside.L_gct_231_aux.case3_norm_obstruction\n')
print(json.dumps({'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'bytes':len(text.encode()),'lines':len(text.splitlines())}),flush=True)
