from pathlib import Path
import hashlib,re,json,ast
from fractions import Fraction as Q
import sympy as S
base=Path(__file__).resolve().parents[1];folder=base/'c4-small-certificates'
source=folder/'C4OpenCases01Scoped.lean';text=source.read_text()
assert hashlib.sha256(source.read_bytes()).hexdigest()=='7944028ae577f616c88a4ba2f76717c5812c9a5fc480b73199b519797296401b'
old=(folder/'C4OpenCases01.lean').read_text()
head,last=old.split('theorem c4_open_1_v_nonzero',1)
assert last.count('  · linear_combination h2\n')==1
fixed=head+'theorem c4_open_1_v_nonzero'+last.replace('  · linear_combination h2\n','')
def substantive(t):return [line for line in t.splitlines() if line.strip() and not line.startswith('set_option ')]
assert substantive(text)==substantive(fixed)
def body(t):return t.split('namespace PEqualNP.Outside.L_gct_231.trace\n',1)[1].rsplit('end PEqualNP.Outside.L_gct_231.trace',1)[0].strip()
for file in ['C4Case0Zero.lean','C4Case0Nonzero.lean']:
 assert body((folder/file).read_text()) in text
print('PASS both complete case0 bodies unchanged; only stale h2 bullet removed and numeric options scoped',flush=True)

lines=text.splitlines();decls=[]
for pos,line in enumerate(lines):
 if line.startswith('theorem '):
  assert lines[pos-2:pos]==['set_option maxHeartbeats 4000000 in','set_option maxRecDepth 4096 in']
  decls.append(line.split()[1])
assert decls==['c4_open_0_v_zero','c4_open_0_v_nonzero','c4_open_1_v_zero','c4_open_1_v_nonzero']
assert sum(line.startswith('set_option ') for line in lines)==8
assert [line for line in lines if line.startswith('import ')]==['import PEqualNP.Defs']
assert not any(token in text for token in ['sorry','axiom','native_decide','_root_','"','@['])
print('PASS allowed import, four scoped helper declarations, scoped numeric options, no prohibited syntax',flush=True)

# Reuse our independent arithmetic parser definitions, not any emitting code.
prefix=(base/'c4_compressed_review/check_lean.py').read_text().split('certificate=json.loads',1)[0]
tree=ast.parse(prefix)
tree.body=[node for node in tree.body if not (isinstance(node,ast.ImportFrom) and node.module=='verify_certificate')]
exec(compile(tree,'independent-polynomial-parser','exec'))
for case in (0,1):
 raw=json.loads((base/f'c4-nonzero-bivariate-{case}.json').read_text())
 for branch in ['v_zero','v_nonzero']:
  name=f'c4_open_{case}_{branch}'
  part=text.split('theorem '+name,1)[1].split('theorem ',1)[0]
  hypotheses=[]
  for line in part.splitlines():
   match=re.fullmatch(r'\s+\(h(\d+) : \((.*) : ℂ\) = 0\)',line)
   if not match:continue
   idx=int(match[1]);actual=evaluate(match[2])
   expected=evaluate(raw['branches'][branch][idx].replace('beta','x0').replace('gamma','x1').replace('**','^'))
   assert actual==expected,(case,branch,idx);hypotheses.append(idx)
  assert hypotheses==([0,1,2,3] if branch=='v_zero' else [0,1,3])
  if branch=='v_nonzero':assert '(h_open : x0 ^ 2 + x0 - 1 ≠ 0)' in part
  if case==1:
   proof=part.split(':= by',1)[1].split('end PEqualNP',1)[0]
   bullets=re.findall(r'^  · (.*)$',proof,re.M)
   assert bullets==(['linear_combination h0','linear_combination h1','linear_combination h2','linear_combination h3'] if branch=='v_zero' else ['linear_combination h0','linear_combination -h1','linear_combination -h3','exact h_open'])
  print('PASS exact theorem premises and wrapper correspondence',name,hypotheses,flush=True)
print('PASS corrected source; Lean compilation remains separate.',flush=True)
