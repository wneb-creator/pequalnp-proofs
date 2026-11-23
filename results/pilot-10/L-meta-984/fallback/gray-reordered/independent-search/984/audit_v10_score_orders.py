import collections, hashlib, json, re
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-10')
root=base/'independent-search/984'
paths={v:base/f'fresh-full-proof/meta984/Full984-compact-v{v}.lean' for v in [9,10]}
texts={v:p.read_text() for v,p in paths.items()}
expected='afb1f795d3d50558279cbd0f455e4aec17daa7da2badb44c0bdb8e5fe5954f98'
assert hashlib.sha256(paths[10].read_bytes()).hexdigest()==expected
frozen=json.loads((root/'raw-score-reorder.json').read_text())
assert len(frozen['graphs'])==31

def norm(s):return ''.join(s.split())
def decl(text,name):
 m=re.search(r'^def '+re.escape(name)+r'\b.*?(?=^def |^theorem |^lemma |^end |\Z)',text,re.M|re.S)
 assert m,name
 return m.group(0).strip()
def nat_list(text,name):
 s=decl(text,name)
 m=re.fullmatch(r'def '+re.escape(name)+r' : List Nat := (\[[^]\n]*\])',s)
 assert m,(name,s[:120])
 return json.loads(m.group(1))
def parse_expr(s):
 tokens=re.findall(r'sum6|r[0-9]+|[0-9]+|<|\|\||[()]|false',s)
 assert ''.join(tokens)==norm(s)
 pos=0
 def atom():
  nonlocal pos
  t=tokens[pos];pos+=1
  if t=='(':
   a=expr();assert tokens[pos]==')';pos+=1;return a
  if t=='false':return False
  assert t=='sum6',t
  args=[]
  for _ in range(6):
   t=tokens[pos];pos+=1;assert re.fullmatch(r'r[0-9]+',t);args.append(int(t[1:]))
  assert tokens[pos]=='<';pos+=1
  n=int(tokens[pos]);pos+=1
  return ('sum6',tuple(args),n)
 def expr():
  nonlocal pos
  a=atom()
  if pos<len(tokens) and tokens[pos]=='||':pos+=1;return ('or',a,expr())
  return a
 a=expr();assert pos==len(tokens)
 return a

total=0
assert sorted(g['graph'] for g in frozen['graphs'])==list(range(31))
for g in sorted(frozen['graphs'],key=lambda g:g['graph']):
 i=g['graph']
 poolpath=root/f'compact/fast_pool_{i}.json'
 pool=json.loads(poolpath.read_text())
 assert hashlib.sha256(poolpath.read_bytes()).hexdigest()==g['source_pool_sha256']
 old=nat_list(texts[9],f'C{i}_rankPool');new=nat_list(texts[10],f'C{i}_rankPool')
 assert old==g['original_rank_codes']==pool['rank_codes']
 assert new==g['proposed_rank_codes']
 assert collections.Counter(old)==collections.Counter(new)
 order=g['proposed_original_indices'];assert sorted(order)==list(range(len(old)))
 assert new==[old[j] for j in order]
 coords=nat_list(texts[10],f'C{i}_coords')
 assert coords==pool['coordinate_array']==nat_list(texts[9],f'C{i}_coords')
 score=decl(texts[10],f'C{i}_patternScore')
 m=re.fullmatch(r'def C'+str(i)+r'_patternScore : List Nat → Bool\s*\| (\[[^]]*\]) => (.*?)\s*\| masks => (.*)',score,re.S)
 assert m,i
 assert norm(m.group(1))=='['+','.join('r'+str(j) for j in range(len(coords)))+']'
 bw=pool['rank_width'];goal=pool['goal'];mask=(1<<bw)-1
 leaves=[]
 for code in new:
  ranks=tuple((code>>(j*bw))&mask for j in range(6))
  assert all(j<len(coords) for j in ranks)
  a,b,c,d,e,f=[(goal>>coords[j])&1 for j in ranks]
  x=b+c;y=2-e-f
  target=(y if d else max(x,y,x+y-1)) if a else (0 if d else x)
  assert target==3
  leaves.append(('sum6',ranks,target))
 want=False
 for leaf in reversed(leaves):want=('or',leaf,want)
 assert parse_expr(m.group(2))==want,i
 fallback=f'C{i}_rankPool.any (fastEntry (compactGoal {pool["negative_count"]} {pool["positive_count"]}) {bw} C{i}_coords masks)'
 assert norm(m.group(3))==norm(fallback)
 assert decl(texts[10],f'C{i}_patternScr')==decl(texts[9],f'C{i}_patternScr')
 total+=len(new)
 print(f'PASS graph={i} pool_size={len(new)} rank_width={bw} coords={len(coords)} exact_pool_permutation=yes exact_pattern_order=yes unchanged_guard_and_fallback=yes')
print(f'PASS all31 pools and {total} pattern clauses independently checked against frozen permutation records and compact pool files.')
print('SOURCE_SHA256 '+expected)
print('SCOPE score pools, pattern expressions, coordinate arrays, source-pool hashes, fallback definitions and wrapper guards only. Gray helper, other proof/data changes and compilation are outside this audit.')
