from pathlib import Path
import re,hashlib,json,ast,collections
B=Path('/tmp/oec/pequalnp-pilot-10');F=B/'fresh-full-proof/meta984';G=B/'single-not-reduction/meta984/gray-walk'
s=(F/'Full984-compact-v10.lean').read_text();old=(F/'Full984-compact-v9.lean').read_text()
def ds(t):
 ms=list(re.finditer(r'^(?:def|theorem|lemma|abbrev|structure|inductive)\s+(\w+)',t,re.M))
 return {m[1]:t[m.start():ms[k+1].start() if k+1<len(ms) else len(t)].split('\nset_option ')[0].split('\nend PEqualNP.Outside.L_meta_984.Cert')[0].strip() for k,m in enumerate(ms)}
a,d=ds(old),ds(s)
assert hashlib.sha256(s.encode()).hexdigest()=='afb1f795d3d50558279cbd0f455e4aec17daa7da2badb44c0bdb8e5fe5954f98'
assert len(s.encode())==515826 and len(s.splitlines())==6302
norm=ds((G/'GrayNormWalkSuffix984.lean').read_text());gray=ds((G/'GrayWalkSuffix984.lean').read_text());data=ds((B/'independent-theory/meta984/gray26-fallback/C26GrayData984.fragment.lean').read_text())
new=dict(norm);new['qGrayGood']=gray['qGrayGood'];new.update({n:t for n,t in data.items() if n.startswith('C26_grayRoute') or n in ['C26_grayWalk','C26_grayGood']})
assert set(d)-set(a)==set(new) and not set(a)-set(d)
for n,t in new.items():assert d[n]==t,n
for n in a.keys()&d.keys():
 if not(re.fullmatch(r'C\d+_(?:rankPool|patternScore)',n) or n in ['C26_ori','C26_ori_run']):assert a[n]==d[n],n
reorder={g['graph']:g for g in json.loads((B/'independent-search/984/raw-score-reorder.json').read_text())['graphs']}
for i in range(31):
 name=f'C{i}';before=ast.literal_eval(a[name+'_rankPool'].split(':=',1)[1].strip());after=ast.literal_eval(d[name+'_rankPool'].split(':=',1)[1].strip());g=reorder[i]
 assert before==g['original_rank_codes'] and after==g['proposed_rank_codes']
 assert collections.Counter(before)==collections.Counter(after)
 assert after==[before[j] for j in g['proposed_original_indices']] and sorted(g['proposed_original_indices'])==list(range(len(before)))
 m=json.loads((B/f'independent-search/984/compact/fast_pool_{i}.json').read_text());bw=m['rank_width'];coords=m['coordinate_array'];pat=d[name+'_patternScore'];terms=re.findall(r'\(sum6 ((?:r\d+ ){5}r\d+) < (\d+)\)',pat)
 assert len(terms)==len(after)
 for (rs,target),code in zip(terms,after):assert [int(v[1:]) for v in rs.split()]==[(code>>(bw*j))&((1<<bw)-1) for j in range(6)] and target=='3'
 assert pat.split('  | masks => ',1)[1]==a[name+'_patternScore'].split('  | masks => ',1)[1]
 print('PASS graph',i,'same score multiset, exact proposedorder, matching specialized terms; data/checks/semantics unchanged')
routes={n:ast.literal_eval(t.split(':=',1)[1].strip()) for n,t in d.items() if n.startswith('C26_grayRoute')}
walk=re.findall(r'C26_grayRoute\d+',d['C26_grayWalk'].split(':=',1)[1]);assert len(walk)==47
literal=ast.literal_eval(a['C26_literalRoutes'].split(':=',1)[1])
def action(route,v):
 for mask,shift in route:
  assert mask&(mask<<shift)==0
  z=((v>>shift)^v)&mask;v^=z^(z<<shift)
 return v
oldbasis={tuple(action(r,1<<j) for j in range(32)) for r in literal};oldbasis.add(tuple(1<<j for j in range(32)))
current=tuple(1<<j for j in range(32));visited=[current];goal=((1<<9)-1)<<9
for name in walk:
 r=routes[name];assert action(r,goal)==goal
 current=tuple(action(r,w) for w in current);visited.append(current)
assert len(set(visited))==48 and set(visited)==oldbasis
assert d['C26_ori']=='def C26_ori : List Nat → List Nat := qGrayNormOrbit C26_grayWalk'
assert d['C26_ori_run'].endswith('qGrayNormOrbit_run h C26_grayGood')
posted=json.loads((B/'desk-next-3.json').read_text())['gap']['statement'];last=s[s.index('theorem PEqualNP.Outside.L_meta_984 : '):]
assert re.sub(r'\s+',' ',last.split(' := by',1)[0].split(' : ',1)[1]).strip()==re.sub(r'\s+',' ',posted).strip()
assert re.findall(r'Cert\.C(\d+)_lower',last)==[str(i) for i in range(31)]
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit|opaque|run_tac|elab|macro|initialize)\b|_root_|"|#',s)
assert re.findall(r'^import .+$',s,re.M)==['import Mathlib','import PEqualNP.Defs']
assert re.findall(r'^namespace .+$',s,re.M)==['namespace PEqualNP.Outside.L_meta_984.Cert']
for m in re.finditer(r'^set_option (\S+) .*$',s,re.M):assert m[1] in ['maxRecDepth','maxHeartbeats','synthInstance.maxSize','synthInstance.maxHeartbeats'] and m[0].endswith(' in')
names=list(d)
for j,n in enumerate(names):
 for use in set(re.findall(r'\bC\d+_\w+\b',d[n])):assert use==n or (use in d and names.index(use)<j),(n,use)
probe=(F/'GrayReorderedGraph26OneState984.lean').read_text();pd=ds(probe)
for n,t in pd.items():
 if n not in ['C26_decoder_diagnostic','C26_gray_one_state']:assert n in d and d[n]==t,n
assert pd['C26_gray_one_state']=='theorem C26_gray_one_state : span (C26_Z 8) 1 0 = true := by decide +kernel'
assert not any(n.startswith('C26_b') or n=='C26_lower' for n in pd)
print('PASS cumulative Graywalk covers exactly old48 basisactions; each generatorvalid/goal fixed; generichelpers exact; one-state probe scope verified.')
print('PASS fullv10 static integration, all27783 finite-state checks and exact31conj statement unchanged. Bytes',len(s.encode()),'remaining512KiB',524288-len(s.encode()))
print('Probe SHA256',hashlib.sha256(probe.encode()).hexdigest())
print('Scope: source review only. Fullv10 and probe compilation/checker verdicts are separate and not claimed.')
