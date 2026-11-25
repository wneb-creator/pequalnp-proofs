from pathlib import Path
import json,re,ast,hashlib
b=Path('results/orch9775');p=Path('lean/PEqualNP/Outside/L_meta_9775.lean');s=p.read_text();lines=s.splitlines();gap=json.loads((b/'gap.json').read_text())['gap'];sha=hashlib.sha256(p.read_bytes()).hexdigest()
def listed(name):return ast.literal_eval(next(l for l in lines if l.startswith('def '+name+' ')).split(':=',1)[1].strip())
edges=listed('edges');weights=listed('weights');ten=listed('tenMasks');eleven=listed('elevenMasks')
exact=re.search(r'theorem PEqualNP\.Outside\.L_meta_9775\s*:\s*(.*?)\s*:= by',s,re.S).group(1);compact=lambda z:re.sub(r'\s+','',z);assert compact(exact)==compact('¬ ('+gap['statement']+')')
expected_edges=ast.literal_eval(re.search(r'\(\[(.*?)\] : List',gap['statement']).group(0).split(' : List')[0][1:]);assert edges==expected_edges
perms=[]
for j in range(4):
 line=next(l for l in lines if l.startswith(f'def permFn{j} '));perms.append(ast.literal_eval(re.search(r'\((\[.*?\]) : List V\)',line).group(1)))
E={frozenset(e)for e in edges}
for q in perms:assert sorted(q)==list(range(14))and{frozenset((q[u],q[v]))for u,v in edges}==E
shifts=[(int(a),int(c),int(d),int(e),f)for a,c,d,e,f in re.findall(r'· exact shift (\d+) (\d+) graphPerm(\d+) auto(\d+) eq \(by decide \+kernel\) (\S+)',s)]
assert [x[0]for x in shifts]==eleven and len(shifts)==117
parts=json.loads((b/'reduced-case-coverage.json').read_text());cert=set(parts['cap11_compact_representatives']);private=set(parts['cap11_private_projection_representatives']);short={63,111,2213,4757}
for src,rep,pi,ai,fn in shifts:
 assert pi==ai and sum(1<<perms[pi][v]for v in range(14)if src>>v&1)==rep
 expected='Compact.excludeP'+str(rep)if rep in cert else'reject'+str(rep)if rep in private|short else'residual_exclude4293'if rep==4293 else'side'if rep==127 else None
 assert fn==expected,(src,rep,fn,expected)
for cap,expected in[(9,[]),(10,ten),(11,eleven)]:
 got=[m for m in range(16384)if all(not(m>>a&1 and m>>c&1)for a,c in edges) and 14<=m.bit_count()+cap and all(k&m!=k or 14+w<=m.bit_count()+cap for k,w in weights)];assert got==expected
transfers=re.findall(r'· exact transfer (\d+) (\d+) graphPerm(\d+) auto(\d+) eq \(by decide \+kernel\) Compact\.excludeW(\d+)',s);assert len(transfers)==2
for a,c,d,e,f in transfers:
 a,c,d,e,f=map(int,(a,c,d,e,f));assert c==f and d==e and sum(1<<perms[d][v]for v in range(14)if a>>v&1)==c
assert ten==[127,1290,4757,8488,16256]
assert [x for x in lines if x.startswith('import ')]==['import PEqualNP.Defs']
report={'verdict':'PASS for actual named finalstatement, casecoverage andtransport; lakebuildpending','source':str(p),'sha256':sha,'bytes':p.stat().st_size,'lines':len(lines),'posted_statement':'exact syntactic negation after whitespace normalization','cap9_survivors':0,'cap10_cases':ten,'cap11_cases':len(shifts),'cap11_dispatch_counts':{'Compact_orbits':len(cert),'private_orbits':len(private),'short_orbits':5,'side_orbits':1},'named_permutations':perms,'cap10_transfers':transfers,'semantic_review':'cap10 relabel uses explicitlyprovedsupport-surplusbijection; cap11 re-appliesno_empty_surplusafterrelabel; normalizedCircuit⇒strictliveDag preservesfunction/size. NoBzeroassumptionleaksintocap10.'}
(b/'named-wrapper-independent.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
