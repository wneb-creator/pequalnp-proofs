from pathlib import Path
from collections import Counter
from itertools import product,permutations
import hashlib,json,math,re
import sympy as s

base=Path(__file__).resolve().parent.parent
source=base/'library/FullStar31.lean';text=source.read_text()
manifest=json.loads((base/'library/full-star31-manifest.json').read_text())
equations_path=base/'star-full-generate-equations.json';data=json.loads(equations_path.read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['source_sha256']
assert hashlib.sha256(equations_path.read_bytes()).hexdigest()==manifest['equation_source_sha256']
assert len(text.splitlines())==761 and len(source.read_bytes())==65775
params=data['unknowns'];variables=s.symbols(' '.join(params));ns=dict(zip(params,variables))
assert params==[f'd{i}' for i in range(9)]+[f'o{i}' for i in range(9)]
assert len(data['equations'])==len(manifest['equations'])==31
monomials=[tuple(row['monomial']) for row in data['equations']]
assert len(set(monomials))==31
assert set(monomials)=={e for e in product(range(5),repeat=3) if 2<=sum(e)<=4}
assert Counter(map(sum,monomials))=={2:6,3:10,4:15}

# Parse actual Lean matrix entries, rather than trusting the generator's copy.
matrix_text=re.search(r'noncomputable def fullStarMatrix.*?!!\[(.*?)\]\n',text,re.S).group(1)
def split_top(text,separators):
    result=[];depth=0;start=0
    for i,ch in enumerate(text):
        if ch=='(':depth+=1
        elif ch==')':depth-=1
        elif depth==0 and ch in separators:
            if text[start:i].strip():result.append(text[start:i].strip())
            start=i+1
    if text[start:].strip():result.append(text[start:].strip())
    assert depth==0
    return result
cells=split_top(matrix_text,',;');assert len(cells)==16
xyz=s.symbols('x y z');ns_xyz=ns|dict(zip(('x','y','z'),xyz))
for k,cell in enumerate(cells):
    parts=split_top(cell,' \n\t');assert parts[0]=='starAffine' and len(parts)==4
    actual=1+sum(s.sympify(a,locals=ns)*v for a,v in zip(parts[1:],xyz))
    expected=1+s.sympify(data['matrix'][k//4][k%4],locals=ns_xyz)
    assert s.expand(actual-expected)==0,('matrix mismatch',k)
print('PASS actual Lean matrix entries equal all16 reviewed JSON entries plus1')

# Audit all 24 literal permutation products in the permanent identity.
formula=re.search(r'lemma perm4_poly.*?Matrix.permanent M =\n(.*?) := by',text,re.S).group(1)
perm_terms=formula.split('+');assert len(perm_terms)==24
seen=set()
for term in perm_terms:
    entries=[tuple(map(int,pair)) for pair in re.findall(r'M (\d) (\d)',term)]
    assert len(entries)==4 and {i for i,j in entries}==set(range(4)) and {j for i,j in entries}==set(range(4))
    key=tuple(j for i,j in sorted(entries));assert key not in seen;seen.add(key)
assert seen==set(permutations(range(4)))
print('PASS permanent formula contains each permutation exactly once')

theorem=text.split('theorem full_star_primitive_equations',1)[1]
conclusion=theorem.split('(24 : MvPolynomial (Fin 3) ℂ)) :\n',1)[1].split(' := by',1)[0]
claims=conclusion.split(' ∧\n');assert len(claims)==31
op_order=re.findall(r'  · have hq : (certD\d{3}) \(Matrix.permanent',theorem)
scales=list(map(int,re.findall(r'linear_combination \(1/(\d+) : ℂ\) \* hq',theorem)))
assert len(op_order)==len(scales)==31

generic=s.symbols(' '.join(f'{a}{i}' for a in 'abcd' for i in range(3)))
gns={str(v):v for v in generic}
for index,(original,record,claim) in enumerate(zip(data['equations'],manifest['equations'],claims)):
    exponent=tuple(original['monomial']);op='certD'+''.join(map(str,exponent))
    assert record['json_index']==index and record['monomial']==list(exponent) and record['operator']==op
    original_poly=s.Poly(s.sympify(original['coefficient'],locals=ns),*variables,domain=s.QQ)
    assert all(c.q==1 for c in original_poly.coeffs())
    content=math.gcd(*(abs(int(c)) for c in original_poly.coeffs()));assert content>0
    factorial=math.prod(math.factorial(e) for e in exponent)
    assert record['integer_content']==content and record['multiindex_factorial']==factorial
    assert record['derivative_to_primitive_scale']==content*factorial==scales[index]
    assert op_order[index]==op
    claim=claim.strip();assert claim.startswith('(') and claim.endswith(') = 0')
    actual=s.Poly(s.sympify(claim[1:-5].replace('^','**'),locals=ns),*variables,domain=s.QQ)
    primitive=s.Poly(original_poly.as_expr()/content,*variables,domain=s.QQ)
    assert actual==primitive
    assert s.Poly(s.sympify(record['primitive_polynomial'],locals=ns),*variables,domain=s.QQ)==primitive
    # Count actual derivative indices in its Lean definition.
    definition=re.search(r'noncomputable def '+op+r'\b.*? :=\n(.*?)(?=\n\n)',text,re.S).group(1)
    derivative_indices=list(map(int,re.findall(r'MvPolynomial.pderiv (\d)',definition)))
    assert Counter(derivative_indices)=={i:e for i,e in enumerate(exponent) if e}
    assert 'MvPolynomial.constantCoeff' in definition
    # Independent factor-choice enumeration, not permutations of derivative labels.
    expected=0;assignment_count=0
    for choices in product((-1,0,1,2),repeat=4):
        if tuple(choices.count(i) for i in range(3))!=exponent:continue
        assignment_count+=1
        expected+=s.prod(gns[f'{a}{v}'] for a,v in zip('abcd',choices) if v>=0)
    expected*=factorial
    lemma=re.search(r'theorem '+op+r'_four\b.*?\) =\n(.*?) := by',text,re.S).group(1)
    actual_generic=s.expand(s.sympify(lemma.replace('^','**'),locals=gns))
    assert s.expand(actual_generic-expected)==0
    assert record['generic_distinct_factor_assignments']==assignment_count
    assert text.count('noncomputable def '+op+' ')==1
    for suffix in ('_add','_nat','_four'):assert text.count('theorem '+op+suffix+' ')==1
    print('PASS',index,exponent,'content',content,'factorial',factorial,'scale',scales[index],
          'factor_assignments',assignment_count)
assert not re.search(r'\bsorry\b|\baxiom\b|native_decide|_root_|"|@\[',text)
assert [line for line in text.splitlines() if line.startswith('import ')]==['import Mathlib','import PEqualNP.Defs']
assert text.count('namespace ')==1 and text.rstrip().endswith('end PEqualNP.Outside.L_gct_231_aux')
print('PASS complete source mapping/order/scaling/derivative/formatscope; Lean build NOT performed')
print('source_sha256',hashlib.sha256(source.read_bytes()).hexdigest())
print('generator_sha256',hashlib.sha256((base/'library/generate_star31.py').read_bytes()).hexdigest())
print('manifest_sha256',hashlib.sha256((base/'library/full-star31-manifest.json').read_bytes()).hexdigest())
