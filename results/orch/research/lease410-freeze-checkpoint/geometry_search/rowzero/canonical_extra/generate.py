from pathlib import Path
from fractions import Fraction
from collections import defaultdict
from functools import reduce
from math import gcd, lcm
import ast
import hashlib
import json
import re
import resource
import sys
import time

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
sys.setrecursionlimit(10000)
start=time.monotonic()
ROOT=Path('/tmp/oec/pequalnp-pilot-78')
OUT=ROOT/'geometry_search/rowzero/canonical_extra'
OUT.mkdir(parents=True,exist_ok=True)
INPUT=ROOT/'geometry_search/canonical55/input.json'
ROWMAP=ROOT/'numeric/s4-structure/rational-id-rowmap.json'
CERTS=ROOT/'numeric/s4-augmented/reduced-certificates.jsonl'
API=ROOT/'canonical_coefficients/CanonicalGeneratorCollectionBody.lean'
data=json.loads(INPUT.read_text());rowmap=json.loads(ROWMAP.read_text())
certs=[json.loads(line) for line in CERTS.read_text().splitlines() if line]
api=API.read_text()
assert data['generator_count']==55 and len(certs)==24
assert data['variables']==[f'p{i}' for i in range(9)]+[f'b{i}' for i in range(9)]
assert len(rowmap['order'])==len(rowmap['rows'])
assert sorted(rowmap['order'])==list(range(len(rowmap['rows'])))
for path in [ROWMAP,CERTS]:
    assert hashlib.sha256(path.read_bytes()).hexdigest()==data['sources'][str(path)]
polys=[{tuple(m):Fraction(c) for m,c in p} for p in data['encoded_generators']]

def add_term(poly,monomial,coefficient):
    poly[monomial]=poly.get(monomial,Fraction(0))+coefficient
    if not poly[monomial]:del poly[monomial]

def add(p,q):
    result=dict(p)
    for m,c in q.items():add_term(result,m,c)
    return result

def multiply(p,q):
    result={}
    for m,c in p.items():
        for n,d in q.items():add_term(result,tuple(sorted(m+n)),c*d)
    return result

def scale(p,c):return {m:v*c for m,v in p.items() if v*c}

names=[f'(p {i})' for i in range(9)]+[f'(b {i})' for i in range(9)]
name_to_index={f'p{i}':i for i in range(9)}|{f'b{i}':9+i for i in range(9)}

def parse_lean(expression):
    expression=re.sub(r'\(([pb]) (\d+)\)',lambda m:m[1]+m[2],expression)
    expression=expression.replace('^','**')
    expression=expression.replace(' : ℂ','')
    tree=ast.parse('('+expression+')',mode='eval').body
    def rec(node):
        if isinstance(node,ast.Constant):
            assert isinstance(node.value,int)
            return {():Fraction(node.value)} if node.value else {}
        if isinstance(node,ast.Name):return {(name_to_index[node.id],):Fraction(1)}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return scale(rec(node.operand),-1)
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Add):return add(rec(node.left),rec(node.right))
            if isinstance(node.op,ast.Sub):return add(rec(node.left),scale(rec(node.right),-1))
            if isinstance(node.op,ast.Mult):return multiply(rec(node.left),rec(node.right))
            if isinstance(node.op,ast.Div):
                denominator=rec(node.right)
                assert set(denominator)=={()} and denominator[()]!=0
                return scale(rec(node.left),1/denominator[()])
            if isinstance(node.op,ast.Pow):
                assert isinstance(node.right,ast.Constant) and isinstance(node.right.value,int)
                result={():Fraction(1)}
                for _ in range(node.right.value):result=multiply(result,rec(node.left))
                return result
        raise AssertionError(ast.dump(node))
    return rec(tree)

# Verify the frozen Lean API itself before deriving consequences from it.
for i in range(31):
    match=re.search(r'^def canonicalGenerator'+str(i)+r'\b[^\n]*:=\n(.*?)(?=\n\n)',api,re.M|re.S)
    assert match and parse_lean(match[1])==polys[i]
collection=re.search(r'^def canonicalGenerators\b.*?:=\n(.*?)(?=\n\n)',api,re.M|re.S)
assert collection
assert list(map(int,re.findall(r'canonicalGenerator(\d+) p b',collection[1])))==list(range(31))

def expression(poly,width=106,continuation='    '):
    pieces=[]
    for monomial,coefficient in sorted(poly.items()):
        assert coefficient
        absolute=abs(coefficient)
        atom='*'.join(names[i]+(f'^{monomial.count(i)}' if monomial.count(i)>1 else '')
                      for i in sorted(set(monomial)))
        if absolute.denominator==1:
            number=str(absolute.numerator)
        else:
            number=f'({absolute.numerator}/{absolute.denominator} : ℂ)'
        magnitude=atom if atom and absolute==1 else number+('*'+atom if atom else '')
        pieces.append(('-' if coefficient<0 else '+',magnitude))
    lines=[];line=''
    for i,(sign,magnitude) in enumerate(pieces):
        part=(('-' if sign=='-' else '') if i==0 else f' {sign} ')+magnitude
        if line and len(line)+len(part)>width:
            lines.append(line);line=continuation+part.strip()
        else:line+=part
    if line:lines.append(line)
    return '\n'.join(lines) or '0'

body=[];audit=[];grouped_records=[]
for i,cert in enumerate(certs):
    assert cert['target']==i and cert['degree']==4
    unscaled={tuple(rowmap['columns'][col]):Fraction(c) for col,c in cert['polynomial']}
    denominator=lcm(*(c.denominator for c in unscaled.values()))
    content=reduce(gcd,(abs(c.numerator*(denominator//c.denominator)) for c in unscaled.values()))
    factor=Fraction(denominator,content)
    assert factor==Fraction(data['extra_quartic_scales'][i])
    target=scale(unscaled,factor)
    assert target==polys[31+i] and all(c.denominator==1 for c in target.values())
    groups=defaultdict(dict)
    for row_index,coefficient in cert['certificate']:
        original_row=rowmap['order'][row_index]
        gi,monomial=rowmap['rows'][original_row]
        assert 0<=gi<31
        add_term(groups[gi],tuple(monomial),factor*Fraction(coefficient))
    groups={gi:p for gi,p in sorted(groups.items()) if p}
    combination={}
    for gi,multiplier in groups.items():
        combination=add(combination,multiply(multiplier,polys[gi]))
    assert combination==target

    target_expr=expression(target)
    assert parse_lean(target_expr)==target
    definition=f'def canonicalExtra{i} (p b : Fin 9 → ℂ) : ℂ :=\n  '+target_expr+'\n'
    body.append(definition)
    lines=['set_option maxHeartbeats 4000000 in',
           f'lemma canonical_extra_{i}_zero (p b : Fin 9 → ℂ)',
           '    (h : ∀ j : Fin 31, canonicalGenerators p b j=0) :',
           f'    canonicalExtra{i} p b=0 := by']
    for gi in groups:
        lines.append(f'  have h{gi} : canonicalGenerator{gi} p b=0 := h {gi}')
    for gi in groups:
        lines.append(f'  unfold canonicalGenerator{gi} at h{gi}')
    lines.append(f'  unfold canonicalExtra{i}')
    lines.append('  linear_combination')
    for position,(gi,multiplier) in enumerate(groups.items()):
        expr=expression(multiplier,width=100,continuation='      ')
        assert parse_lean(expr)==multiplier
        lines.append('    ('+expr+f') * h{gi}'+(' +' if position+1<len(groups) else ''))
    body.append('\n'.join(lines)+'\n')
    audit.append({'extra':i,'canonical55_index':31+i,'primitive_scale':str(factor),
                  'target_terms':len(target),'raw_certificate_terms':len(cert['certificate']),
                  'used_generators':list(groups),'grouped_multiplier_terms':sum(len(p) for p in groups.values()),
                  'max_multiplier_degree':max(len(m) for p in groups.values() for m in p),
                  'exact_identity_verified':True,'emitted_polynomials_roundtrip_verified':True})
    grouped_records.append({'extra':i,'primitive_scale':str(factor),
                            'target':[[list(m),str(c)] for m,c in sorted(target.items())],
                            'multipliers':[[gi,[[list(m),str(c)] for m,c in sorted(p.items())]]
                                           for gi,p in groups.items()]})

body.append('def canonicalExtras (p b : Fin 9 → ℂ) : Fin 24 → ℂ :=\n  !['+
            ','.join(f'canonicalExtra{i} p b' for i in range(24))+']\n')
lines=['lemma canonical_extras_zero (p b : Fin 9 → ℂ)',
       '    (h : ∀ j : Fin 31, canonicalGenerators p b j=0) :',
       '    ∀ i : Fin 24, canonicalExtras p b i=0 := by',
       '  intro i','  fin_cases i']
for i in range(24):
    lines.append(f'  · simpa [canonicalExtras] using canonical_extra_{i}_zero p b h')
body.append('\n'.join(lines)+'\n')
text='\n'.join(body)
assert not any(token in text for token in ['_root_','"','sorry','axiom','native_decide'])
assert not re.search(r'@\[',text)
assert not re.search(r'^(import|namespace|end)\b',text,re.M)
assert set(re.findall(r'^set_option (\S+)',text,re.M))=={'maxHeartbeats'}
target=OUT/'CanonicalExtraBody.lean';target.write_text(text)
(OUT/'grouped-certificates.json').write_text(json.dumps(grouped_records,indent=2)+'\n')
report={'status':'PASS exact rational source-generation audit; Lean NOT BUILT',
        'scope':'Twenty-four quartic consequences of the frozen original31 canonical generators. No infeasibility or posted theorem assertion.',
        'inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [INPUT,ROWMAP,CERTS,API]},
        'certificate_indexing':'rowmap.rows[rowmap.order[certificate_row_index]]',
        'primitive_scaling':'Both certificate multipliers and target are multiplied by canonical55.extra_quartic_scales[i].',
        'original_Lean_API_matches_all31_inputs':True,'extra_count':24,
        'source':str(target),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
        'source_lines':len(text.splitlines()),'source_bytes':len(text.encode()),
        'declaration_count':len(re.findall(r'^(?:def|lemma) ',text,re.M)),
        'all24_exact_identities_verified':True,'all_Lean_polynomials_roundtrip_verified':True,
        'details':audit,'format_scan':'PASS','seconds':time.monotonic()-start}
(OUT/'generation-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','extra_count','source_sha256','source_lines','source_bytes','declaration_count','seconds']}),flush=True)
