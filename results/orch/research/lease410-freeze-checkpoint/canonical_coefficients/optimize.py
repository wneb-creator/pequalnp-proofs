from pathlib import Path
import itertools,json,hashlib

base=Path('/tmp/oec/pequalnp-pilot-78/canonical_coefficients')
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
S=[[[0]*9 for _ in range(4)] for _ in range(4)]
for r in range(3):
    S[r+1][r+1][r]=2
    for i,j in [(0,r+1),(r+1,0)]:S[i][j][3+r]=1;S[i][j][6+r]=-1
for r,(i,j) in enumerate([(2,3),(1,3),(1,2)]):
    for a,b in [(i,j),(j,i)]:S[a][b][3+r]=-1;S[a][b][6+r]=3
M=[[[sum(H[i][a]*S[a][b][v]*H[b][j] for a,b in itertools.product(range(4),repeat=2)) for v in range(9)] for j in range(4)] for i in range(4)]
assert all(c%2==0 for row in M for entry in row for c in entry)
names=[f'B {i}' for i in range(3)]+[f'P {i}' for i in range(3)]+[f'D {i}' for i in range(3)]
def expression(row):
    out=''
    for c,name in zip(row,names):
        c//=2
        if not c:continue
        magnitude=(str(abs(c))+'*' if abs(c)!=1 else '')+name
        out+=('-' if c<0 else ('' if not out else '+'))+magnitude
    return '('+out+')/4'
definition='noncomputable def canonicalHadamardMatrix (B P D : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=\n  !!['+';\n    '.join(','.join(expression(e) for e in row) for row in M)+']\n\n'
lemma='''lemma canonical_reconstruct_entry (B P D : Fin 3 → ℂ) (i j : Fin 4) :
    hadamardReconstruct B P D (i,j)=canonicalHadamardMatrix B P D i j := by
  fin_cases i <;> fin_cases j <;>
    simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
      hadamardSigns,Fin.sum_univ_succ,canonicalHadamardMatrix] <;> ring

'''
body=(base/'CanonicalHomogeneousBody.lean').read_text()
marker='set_option maxHeartbeats 2400000 in\nlemma canonical_hadamard_radial_permanent'
body=body.replace(marker,definition+lemma+marker)
old='''  rw [permanent_four]
  simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
    hadamardSigns,Fin.sum_univ_succ,canonicalHadamardQuadratic,
    canonicalHadamardCubic,canonicalHadamardQuartic]
  ring'''
new='''  simp_rw [canonical_reconstruct_entry]
  rw [permanent_four]
  simp [canonicalHadamardMatrix,canonicalHadamardQuadratic,
    canonicalHadamardCubic,canonicalHadamardQuartic]
  ring'''
assert body.count(old)==1;body=body.replace(old,new)
(base/'CanonicalHomogeneousOptimizedBody.lean').write_text(body)
source='import PEqualNP.Outside.L_gct_231\n\nnamespace PEqualNP.Outside.L_gct_231\n\n'+body+'\nend PEqualNP.Outside.L_gct_231\n'
(base/'CanonicalHomogeneousOptimized.lean').write_text(source)
(base/'reconstruction-matrix-integer-fourth.json').write_text(json.dumps([[[c//2 for c in e] for e in row] for row in M])+'\n')
print(json.dumps({'body_lines':len(body.splitlines()),'source_lines':len(source.splitlines()),'source_sha256':hashlib.sha256(source.encode()).hexdigest()}))
