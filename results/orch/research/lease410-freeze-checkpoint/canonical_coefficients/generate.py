from pathlib import Path
import itertools,json,math,hashlib

BASE=Path('/tmp/oec/pequalnp-pilot-78/canonical_coefficients')
CHART=Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard/chart.json')
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]

def addterm(p,m,c):
    p[m]=p.get(m,0)+c
    if p[m]==0: del p[m]

def product(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():addterm(out,tuple(sorted(m+n)),c*d)
    return out

# Variables are B0,B1,B2,P0,P1,P2,D0,D1,D2.
# S is twice the Hadamard-coordinate perturbation, so H*S*H is 8T.
S=[[{} for _ in range(4)] for _ in range(4)]
for r in range(3):
    S[r+1][r+1]={(r,):2}
    S[0][r+1]=S[r+1][0]={(3+r,):1,(6+r,):-1}
for r,(i,j) in enumerate([(2,3),(1,3),(1,2)]):
    S[i][j]=S[j][i]={(3+r,):-1,(6+r,):3}
M=[[{} for _ in range(4)] for _ in range(4)]
for i,j in itertools.product(range(4),repeat=2):
    for a,b in itertools.product(range(4),repeat=2):
        for m,c in S[a][b].items():addterm(M[i][j],m,H[i][a]*H[b][j]*c)
    addterm(M[i][j],(),1)
total={}
for perm in itertools.permutations(range(4)):
    p={():1}
    for i in range(4):p=product(p,M[i][perm[i]])
    for m,c in p.items():addterm(total,m,c)
addterm(total,(),-24)
assert set(map(len,total))=={2,3,4}
divisors={2:64,3:256,4:128}
homogeneous={d:{m:c//divisors[d] for m,c in total.items() if len(m)==d}
             for d in divisors}
assert all(c%divisors[len(m)]==0 for m,c in total.items())

def expr(poly,names,width=105):
    terms=[]
    for m,c in sorted(poly.items()):
        counts={k:m.count(k) for k in sorted(set(m))}
        atom='*'.join(names[k]+(f'^{e}' if e>1 else '') for k,e in counts.items())
        magnitude=str(abs(c)) if not atom else (str(abs(c))+'*' if abs(c)!=1 else '')+atom
        terms.append(('-' if c<0 else '+',magnitude))
    out=[]; line=''
    for n,(sign,term) in enumerate(terms):
        part=(('-' if sign=='-' else '') if n==0 else f' {sign} ')+term
        if line and len(line)+len(part)>width:out.append(line);line='    '+part.strip()
        else:line+=part
    if line:out.append(line)
    return '\n'.join(out) or '0'

names=[f'(B {i})' for i in range(3)]+[f'(P {i})' for i in range(3)]+[f'(D {i})' for i in range(3)]
text=[]
for d,label in [(2,'Quadratic'),(3,'Cubic'),(4,'Quartic')]:
    text.append(f'def canonicalHadamard{label} (B P D : Fin 3 → ℂ) : ℂ :=\n  '+expr(homogeneous[d],names)+'\n')
text.append('''set_option maxHeartbeats 2400000 in
lemma canonical_hadamard_radial_permanent (B P D : Fin 3 → ℂ) (z : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j)) =
      24+canonicalHadamardQuadratic B P D*z^2+
        canonicalHadamardCubic B P D/2*z^3+canonicalHadamardQuartic B P D/32*z^4 := by
  rw [permanent_four]
  simp [hadamardReconstruct,hadamardTransform,hadamardCoordinateMatrix,
    hadamardSigns,Fin.sum_univ_succ,canonicalHadamardQuadratic,
    canonicalHadamardCubic,canonicalHadamardQuartic]
  ring

lemma canonical_hadamard_homogeneous_zero (B P D : Fin 3 → ℂ)
    (hp : ∀ z : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (z • B) (z • P) (z • D) (i,j))=24) :
    canonicalHadamardQuadratic B P D=0 ∧ canonicalHadamardCubic B P D=0 ∧
      canonicalHadamardQuartic B P D=0 := by
  have hh : ∀ z : ℂ, (0:ℂ)*z+canonicalHadamardQuadratic B P D*z^2+
      (canonicalHadamardCubic B P D/2)*z^3+
      (canonicalHadamardQuartic B P D/32)*z^4=0 := by
    intro z
    have h := hp z
    rw [canonical_hadamard_radial_permanent] at h
    linear_combination h
  obtain ⟨_,h2,h3,h4⟩ := quartic_all_coefficients _ _ _ _ hh
  refine ⟨h2,?_,?_⟩
  · linear_combination 2*h3
  · linear_combination 32*h4

def canonicalCoefficientCoordinates (v : Fin 9 → ℂ) (s t u : ℂ) : Fin 3 → ℂ :=
  ![v 0*s+v 1*t+v 2*u,v 3*s+v 4*t+v 5*u,v 6*s+v 7*t+v 8*u]

lemma canonicalCoefficientCoordinates_scale (v : Fin 9 → ℂ) (s t u z : ℂ) :
    canonicalCoefficientCoordinates v (z*s) (z*t) (z*u)=
      z • canonicalCoefficientCoordinates v s t u := by
  funext i
  fin_cases i <;> simp [canonicalCoefficientCoordinates] <;> ring

lemma canonical_family_homogeneous_zero (p b : Fin 9 → ℂ)
    (hp : ∀ s t u : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24) :
    ∀ s t u : ℂ,
      canonicalHadamardQuadratic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardCubic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 ∧
      canonicalHadamardQuartic (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0 := by
  intro s t u
  apply canonical_hadamard_homogeneous_zero
  intro z
  have h := hp (z*s) (z*t) (z*u)
  rw [canonicalCoefficientCoordinates_scale,canonicalCoefficientCoordinates_scale] at h
  have hd : (![z*s,z*t,z*u] : Fin 3 → ℂ)=z • ![s,t,u] := by
    funext i
    fin_cases i <;> simp
  rw [hd] at h
  exact h

lemma rank_three_flat_canonical_hadamard_family
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ p b : Fin 9 → ℂ, ∀ s t u : ℂ,
      Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
        1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
          (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24 := by
  obtain ⟨_,honto⟩ := hadamardD_bijective_on_rank_three_flat L hL hd hs hp
  obtain ⟨X,hX⟩ := honto ![1,0,0]
  obtain ⟨Y,hY⟩ := honto ![0,1,0]
  obtain ⟨Z,hZ⟩ := honto ![0,0,1]
  change hadamardD X.val=![1,0,0] at hX
  change hadamardD Y.val=![0,1,0] at hY
  change hadamardD Z.val=![0,0,1] at hZ
  let p : Fin 9 → ℂ := ![hadamardP X.val 0,hadamardP Y.val 0,hadamardP Z.val 0,
    hadamardP X.val 1,hadamardP Y.val 1,hadamardP Z.val 1,
    hadamardP X.val 2,hadamardP Y.val 2,hadamardP Z.val 2]
  let b : Fin 9 → ℂ := ![hadamardB X.val 0,hadamardB Y.val 0,hadamardB Z.val 0,
    hadamardB X.val 1,hadamardB Y.val 1,hadamardB Z.val 1,
    hadamardB X.val 2,hadamardB Y.val 2,hadamardB Z.val 2]
  refine ⟨p,b,?_⟩
  intro s t u
  let T := s • X.val+t • Y.val+u • Z.val
  have hT : T ∈ L := L.add_mem (L.add_mem (L.smul_mem s X.property)
    (L.smul_mem t Y.property)) (L.smul_mem u Z.property)
  have hD : hadamardD T=![s,t,u] := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul,hX,hY,hZ]
    funext i
    fin_cases i <;> simp
  have hB : hadamardB T=canonicalCoefficientCoordinates b s t u := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    funext i
    fin_cases i <;> simp [b,canonicalCoefficientCoordinates] <;> ring
  have hP : hadamardP T=canonicalCoefficientCoordinates p s t u := by
    dsimp [T]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    funext i
    fin_cases i <;> simp [p,canonicalCoefficientCoordinates] <;> ring
  have hr := hadamard_reconstruction T (hs T hT) (level_flat_entry_sum_zero L hp T hT)
  rw [hB,hP,hD] at hr
  rw [hr]
  exact hp T hT
''')

chart=json.loads(CHART.read_text())
pn=[f'(p {i})' for i in range(9)]+[f'(b {i})' for i in range(9)]
for n,poly in enumerate(chart['polynomials']):
    text.append(f'def canonicalGenerator{n} (p b : Fin 9 → ℂ) : ℂ :=\n  '+expr({tuple(m):c for m,c in poly},pn)+'\n')

for n,alpha in enumerate(chart['parameter_exponents']):
    d=sum(alpha);label={2:'Quadratic',3:'Cubic',4:'Quartic'}[d]
    # Top-degree finite differences isolate the selected homogeneous coefficient.
    terms=[];facts=[]
    denominator=math.prod(math.factorial(a) for a in alpha)
    for point in itertools.product(*(range(a+1) for a in alpha)):
        if point==(0,0,0):continue
        sign=(-1)**(d-sum(point)); coeff=sign*math.prod(math.comb(a,x) for a,x in zip(alpha,point))
        name='h'+''.join(map(str,point));facts.append('  have '+name+' := h '+' '.join(map(str,point)))
        terms.append(f'({coeff}/{denominator}:ℂ)*{name}')
    text.append(f'''set_option maxHeartbeats 1600000 in
lemma canonical_generator_{n}_zero (p b : Fin 9 → ℂ)
    (h : ∀ s t u : ℂ, canonicalHadamard{label}
      (canonicalCoefficientCoordinates b s t u)
      (canonicalCoefficientCoordinates p s t u) ![s,t,u]=0) :
    canonicalGenerator{n} p b=0 := by
'''+ '\n'.join(facts)+f'''
  simp [canonicalHadamard{label},canonicalCoefficientCoordinates] at '''+' '.join(f.split()[1] for f in facts)+f'''
  unfold canonicalGenerator{n}
  linear_combination '''+' + '.join(terms)+'\n')

text.append('def canonicalGenerators (p b : Fin 9 → ℂ) : Fin 31 → ℂ :=\n  !['+
    ','.join(f'canonicalGenerator{n} p b' for n in range(31))+']\n')
text.append('''lemma canonical_generators_zero (p b : Fin 9 → ℂ)
    (hp : ∀ s t u : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) =>
      1+hadamardReconstruct (canonicalCoefficientCoordinates b s t u)
        (canonicalCoefficientCoordinates p s t u) ![s,t,u] (i,j))=24) :
    ∀ i : Fin 31, canonicalGenerators p b i=0 := by
  have h := canonical_family_homogeneous_zero p b hp
  intro i
  fin_cases i
'''+''.join(f'  · simpa [canonicalGenerators] using canonical_generator_{n}_zero p b (fun s t u => (h s t u)'+{2:'.1',3:'.2.1',4:'.2.2'}[sum(alpha)]+')\n' for n,alpha in enumerate(chart['parameter_exponents'])))
text.append('''lemma rank_three_flat_has_canonical_generators_zero
    (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : Module.finrank ℂ L=3)
    (hd : Module.finrank ℂ (L.map matrixDiagonalCoordinates)=3)
    (hs : ∀ V ∈ L, ∀ i j : Fin 4, V (i,j)=V (j,i))
    (hp : ∀ V ∈ L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+V (i,j))=24) :
    ∃ p b : Fin 9 → ℂ, ∀ i : Fin 31, canonicalGenerators p b i=0 := by
  obtain ⟨p,b,h⟩ := rank_three_flat_canonical_hadamard_family L hL hd hs hp
  exact ⟨p,b,canonical_generators_zero p b h⟩
''')

body='\n'.join(text)
(BASE/'CanonicalCoefficientsBody.lean').write_text(body)
prefix='import PEqualNP.Outside.L_gct_231\n\nnamespace PEqualNP.Outside.L_gct_231\n'
(BASE/'CanonicalCoefficients.lean').write_text(prefix+'\n'+body+'\nend PEqualNP.Outside.L_gct_231\n')
(BASE/'homogeneous-polynomials.json').write_text(json.dumps({str(d):[[list(m),c] for m,c in sorted(poly.items())] for d,poly in homogeneous.items()},separators=(',',':'))+'\n')
print(json.dumps({'chart_sha256':hashlib.sha256(CHART.read_bytes()).hexdigest(),'homogeneous_terms':{d:len(p) for d,p in homogeneous.items()},'body_lines':len(body.splitlines()),'body_bytes':len(body.encode())}))
