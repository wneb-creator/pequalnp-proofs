from pathlib import Path
import ast,datetime,hashlib,itertools,json,re,time
BASE=Path(__file__).resolve().parent
start=time.monotonic();source=(BASE/'stochastic-q2f-core.lean').read_text();tail=(BASE/'stochastic-q2f-core-tail.lean').read_text();data=json.loads((BASE/'stochastic-q2f-generator-data.json').read_text())
assert hashlib.sha256(source.encode()).hexdigest()==data['core_sha256']
assert hashlib.sha256(tail.encode()).hexdigest()==data['tail_sha256']
primitive=(BASE/'formalization-cap-seven-core.lean').read_text().split('def cap7_tripleCode',1)[0]
assert source==primitive+tail+'\nend PEqualNP.Outside.L_meta_6659_aux\n'
blocks={}
for match in re.finditer(r'(?m)^def (q2f_\w+)\b',tail):
 end=tail.find('\ndef ',match.end());blocks[match.group(1)]=tail[match.start():end if end>=0 else len(tail)]
def vector(name):
 text=blocks[name].split(':=',1)[1];left=text.index('![');right=text.rindex(']')+1
 return ast.literal_eval(text[left:right].replace('![','['))
N=vector('q2f_tripleCode');S=vector('q2f_superCode');P=vector('q2f_parentCode');cut=vector('q2f_cut');packs=[vector('q2f_pack'+str(i)) for i in range(15)]
assert N==[11,69,49] and S==[m for m in range(128) if m!=98 and m&98==98]
assert len(P)==3 and len(cut)==128 and all(len(row)==3 and all(len(v)==2 for v in row) for row in cut)
for t,row in zip(N,P):
 expected=[[m,m] for m in range(128) if m.bit_count()==2 and m&t==m]+[[m,m] for m in range(128) if m.bit_count()==4 and m&t==t]+[[a,b] for a,b in itertools.combinations([m for m in range(128) if m.bit_count()==5],2) if a&b==t]
 assert row==expected and len(row)==10
for m,row in enumerate(cut):
 if m.bit_count()==3:expected=[[x,m^x] for x in range(128) if x.bit_count()==2 and x&m==x]
 elif m.bit_count()==4:expected=[[x,m^x] for x in range(128) if x.bit_count()==2 and x&m==x and x<m^x]
 else:expected=[[0,0]]*3
 assert row==expected
assert list(map(int,re.findall(r'q2f_pack(\d+) a b c',blocks['q2f_pack'])))==list(range(15))
outside={m for m in range(128) if m.bit_count()==2 and all(m&t!=m for t in N)}
assert outside==set(map(int,re.findall(r'm = (\d+)',blocks['q2f_outside']))) and len(outside)==12
cases={(row['s'],row['a'],row['b'],row['c']):row for row in data['cases']};assert len(cases)==len(data['cases'])==4902
counts={'families':0,'size7':0,'size8_or_more':0,'shape7':0,'bad_shape7':0,'closure_operations':0};hist={}
for si,s in enumerate(S):
 assert len(packs[si])==10 and all(len(z)==10 and all(len(w)==10 for w in z) for z in packs[si])
 for a,b,c in itertools.product(range(10),repeat=3):
  raw=N+[s]+P[0][a]+P[1][b]+P[2][c];Y=set(raw);counts['families']+=1;assert len(Y)>=7
  shape=all(m.bit_count()<=2 or m in N or m==s for m in Y)
  if len(Y)>=8:counts['size8_or_more']+=1;continue
  counts['size7']+=1
  if shape:counts['shape7']+=1;continue
  counts['bad_shape7']+=1;row=cases[si,a,b,c];assert row['raw']==raw and row['S']==s
  pack=packs[si][a][b][c];assert pack==row['pack'];indices=[pack//11**j%11 for j in range(3)];K=[raw[k] if k<10 else 0 for k in indices];missing=raw[pack//1331%10]
  assert sorted(x for x in K if x)==row['known_large'];assert missing==raw[row['missing_index']]
  small={m for m in range(128) if m.bit_count()<=1 or m.bit_count()==2 and (m in outside or m in Y)};allowed=small|Y;closed=small|set(K);assert closed<=allowed and missing in Y and missing not in closed
  # Check the complete closure directly, rather than only the compressed checks.
  for x,y in itertools.product(closed,repeat=2):
   for z in (x|y,x&y):
    assert z not in allowed or z in closed,(si,a,b,c,x,y,z)
    counts['closure_operations']+=1
  for m in raw:
   if m in closed:continue
   seed=m.bit_count() in (3,4) and any(x in small and y in small for x,y in cut[m]);assert not seed
   assert all(not(x&m==x and (m^(m&x)) in small) for x in K)
  large=len([x for x in K if x]);hist[large]=hist.get(large,0)+1
assert counts['families']==15000 and counts['size7']==5307 and counts['bad_shape7']==4902
for a,b in itertools.product(range(128),repeat=2):
 A={i for i in range(7) if a>>i&1};B={i for i in range(7) if b>>i&1}
 assert {i for i in range(7) if ((a|b)%128)>>i&1}==A|B
 assert {i for i in range(7) if ((a&b)%128)>>i&1}==A&B
 assert {i for i in range(7) if ((a^(a&b))%128)>>i&1}==A-B
for pat in [r'\bsorry\b',r'\baxiom\b',r'\bnative_decide\b',r'_root_',r'"']:assert not re.search(pat,source)
report=dict(verdict='PASS independent emitted-table, finite-geometry and full-closure review',reviewed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256=data['core_sha256'],tail_sha256=data['tail_sha256'],generator_sha256=hashlib.sha256((BASE/'stochastic-q2f-generate.py').read_bytes()).hexdigest(),counts=counts,known_large_histogram=hist,bitwise_pairs_checked=16384,elapsed_seconds=time.monotonic()-start,scope='Finite generated certificate data only. No Lean compilation, generic generator-to-closure theorem, circuit transfer, q2 exclusion or full posted result is claimed.',checks=['Parsed the actual Lean numeric vectors and checked all15,000 parameter cases against independent parent/superset enumeration.','For all4,902 bad-shape seven-families, decoded the actual base11 witness, verified the missing occurring mask, and directly checked every allowed union/intersection of all closed masks.','Checked complete small-seed partition tables,12 outside pairs and all16,384 bitwise union/intersection/difference input pairs.','Reviewed compressed closure logic: small is downward closed; large small-small unions use the three seed partitions; known-small unions use the small difference; known-known pairs are explicitly checked.','Families discharged by size or shape need no witness. Every bad-shape family is checked after decoding, including the828 cases with no reachable large mask; packed value1330 legitimately also encodes that empty-large-set witness.'])
(BASE/'sat-q2f-independent-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
