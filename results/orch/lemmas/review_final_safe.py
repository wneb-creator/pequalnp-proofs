from pathlib import Path
import re,ast,json,hashlib,collections
p=Path('/tmp/oec/pequalnp-pilot-182')
s=(p/'FinalSafeCandidate.lean').read_text();old=(p/'FinalCandidate.lean').read_text()
mods=(p/'final-assembly-modules.txt').read_text().splitlines()
ns='PEqualNP.Outside.L_meta_10760';ons=ns+'_first'
def normalize(t):
 return '\n'.join(l for l in t.splitlines() if not l.startswith('import ') and l.strip() not in ['namespace '+ons,'end '+ons]).strip().replace(ons,ns).replace('L_meta_10760_first','L_meta_10760')+'\n'
parts=['import PEqualNP.Defs\n\nnamespace '+ns+'\n']+[normalize((p/(m+'.lean')).read_text()) for m in mods]
last='theorem '+ns+' :\n    '+(p/'statement.txt').read_text().strip()+' :=\n  '+ns+'.replacement_from_one '+ns+'.bound13\n    ('+ns+'.live_excluded '+ns+'.all_gates_bound)\n'
parts+=['end '+ns+'\n\n',last]
before='\n'.join(parts)
conv=re.findall(r'^lemma ([^ \n:]+)(?=[^\n]*:= by decide \+kernel\s*$)',before,re.M)
after=re.sub(r'^lemma (?=[^\n]*:= by decide \+kernel\s*$)','def ',before,flags=re.M)
assert s==after,'assembly'
assert conv==(p/'final-numeric-conversions.txt').read_text().splitlines()
assert s.endswith(last) and old.endswith(last)
assert re.findall(r'^import .+$',s,re.M)==['import PEqualNP.Defs']
assert '_first' not in s and '_root_' not in s and '"' not in s
assert not re.search(r'\b(sorry|axiom|native_decide|admit|unsafe|implemented_by|run_cmd|elab|macro)\b',s)
assert not re.search(r'^\s*(axioms|constant|constants|opaque)\b',s,re.M)
assert re.findall(r'^variable .*$',s,re.M)==re.findall(r'^variable .*$',old,re.M)
opts=sorted(set(re.findall(r'^set_option (\S+)',s,re.M)))
assert set(opts)<={'maxRecDepth','maxHeartbeats','synthInstance.maxHeartbeats','maxRecDepth'}
assert all(l.endswith(' in') for l in s.splitlines() if l.startswith('set_option '))
attrs=re.findall(r'@\[([^]]*)\]',s);assert all(x=='simp' for x in attrs)
assert len(s.encode())<=512*1024
assert max(map(len,re.findall(r'(?<![\w])(?:0x[0-9a-fA-F]+|[0-9]+)(?![\w])',s)))<=22
names=re.findall(r'^(?:noncomputable )?(?:def|lemma|theorem|abbrev|structure|inductive) (\S+)',s,re.M)
assert len(names)==len(set(names)),[x for x,n in collections.Counter(names).items() if n>1]
shared=['KernelFirstEngine','KernelFirstTables','OwnSequence','OwnRows','GateCatalogue','SymmetryFirst','FirstReject','ChainFirst','TightNotFirst','TightFinalGlue']
for m in shared:
 x=normalize((p/(m+'.lean')).read_text());assert x in old,m
# Restricted parser reads only integer arithmetic and lists from actual Lean masks.
def arithmetic(t):
 node=ast.parse(t.replace('<<<','<<').replace('^','**').replace('true','True').replace('false','False'),mode='eval').body
 def go(n):
  if isinstance(n,ast.Constant):return n.value
  if isinstance(n,(ast.List,ast.Tuple)):return [go(x) for x in n.elts]
  if isinstance(n,ast.BinOp):
   a,b=go(n.left),go(n.right)
   return {ast.Pow:lambda:a**b,ast.LShift:lambda:a<<b,ast.Sub:lambda:a-b,ast.Add:lambda:a+b}[type(n.op)]()
  raise AssertionError(ast.dump(n))
 return go(node)
plan=json.loads((p/'advanced-complete-strict-plan.json').read_text())
checks=[]
for d in plan['representatives']:
 label=d['label'];isbase=label.startswith('base');i=int(label[4:] if isbase else label[3:]);tag=str(i) if isbase else '_s'+str(i)
 orig='KernelCase'+str(i) if isbase else 'KernelSymCase'+str(i)
 mod='Final'+('Base' if isbase else 'Sym')+str(i) if d['mode']=='sharded' else orig
 t=(p/(mod+'.lean')).read_text();o=(p/(orig+'.lean')).read_text()
 for name in ['gate'+tag,'prior'+tag,'owns'+tag,'codes'+tag,'shape'+tag+'_checked']:
  a=re.search(r'^(?:def|lemma) '+name+r' :[^\n]+$',o,re.M)
  b=re.search(r'^(?:def|lemma) '+name+r' :[^\n]+$',t,re.M)
  if a is None:assert b is None;continue
  assert a.group().split(' ',1)[1]==b.group().split(' ',1)[1],(label,name)
 if d['mode']=='original':checks.append({'label':label,'mode':'original'});continue
 maskexpr=re.search(r'^def masks_'+label+r' : [^\n]* := (.+)$',t,re.M).group(1)
 masks=arithmetic(maskexpr)
 assert len(masks)==d['mask_count']
 binary=[H for H,ph in masks if ph==0];unary=[(H,ph) for H,ph in masks if ph==1]
 assert len(unary)==1 and unary[0]==(0,1)
 union=0
 for H in binary:assert not (union&H);union|=H
 assert union==(1<<214)-1
 actual=[]
 for j,(H,ph) in enumerate(masks):
  decl=re.search(r'^def split_'+label+'_'+str(j)+r' : run_'+label+r' (.+) = false :=(?: by decide \+kernel|\n  chkT_count_split ([^\n]+))$',t,re.M)
  assert decl,(label,j)
  assert arithmetic(decl.group(1))==[H,ph]
  if decl.group(2) is None:actual.append((H,ph,tuple(range(13))))
  else:
   terms=decl.group(2).split();assert len(terms)==3
   stem=terms[0].removesuffix('_zero');assert terms==[stem+'_zero',stem+'_one',stem+'_more']
   expression=re.search(r'^noncomputable def '+stem+r' \(ts : List Nat\) : Bool :=\n  ([^\n]+)$',t,re.M).group(1)
   run=re.search(r'^noncomputable def run_'+label+r' \(p : Nat × Nat\) : Bool :=\n  ([^\n]+)$',t,re.M).group(1)
   residue=H.bit_length()-1;assert H==1<<residue and ph==0
   expected=run.replace('(List.range 13)','ts').replace('p.1',f'((2 ^ 1 - 1) <<< {residue})').replace('p.2','0');assert expression==expected
   for term,ts,nums in zip(terms,['[0]','[1]','((List.range 13).drop 2)'],[[0],[1],list(range(2,13))]):
    assert f'def {term} : {stem} {ts} = false := by decide +kernel' in t
    actual.append((H,ph,tuple(nums)))
 expected=[(x['H'],x['ph'],tuple(x['ts'])) for x in d['checks']]
 assert collections.Counter(actual)==collections.Counter(expected),(label,'audit mismatch')
 used=re.findall(r'^    · exact split_'+label+r'_(\d+)$',t,re.M)
 assert list(map(int,used))==list(range(len(masks)))
 strict=(p/('Strict'+('Base' if isbase else 'Sym')+str(i)+'.lean')).read_text()
 converted=re.sub(r'^lemma (?=[^\n]*:= by decide \+kernel\s*$)','def ',strict,flags=re.M)
 exceptions={'base0':[5,65],'sym6':[47],'sym9':[46]}.get(label,[])
 if not exceptions:assert t==converted,label
 checks.append({'label':label,'mode':'sharded','masks':len(masks),'numeric_checks':len(actual),'complete_binary_buckets':214,'count_split_residues':exceptions})
# Actual catalogue is acyclic and expands to precisely the 42 unordered binary gate cases.
gates={n:tuple(arithmetic(v)) for n,v in re.findall(r'^def (gate\w*) : Gt := (.+)$',s,re.M)}
cat=[];rho=[5,4,3,2,1,0,6]
for i in range(24):
 cert=re.search(r'^lemma certified'+str(i)+r' : Imp \[(gate\w*)\] 0 13 :=',s,re.M).group(1)
 tag=cert.removeprefix('gate');pr=re.search(r'^def prior'+tag+r' : List Gt := (.+)$',s,re.M)
 if pr:assert set(map(tuple,arithmetic(pr.group(1))))<=set(cat)
 cat.append(gates[cert])
 ref=re.search(r'^lemma reflected'+str(i)+r' : Imp \[(.+)\] 0 13 :=',s,re.M)
 if ref:
  f=tuple(arithmetic(ref.group(1)));assert f[0]==gates[cert][0] and sorted([rho[f[1]],rho[f[2]]])==sorted(gates[cert][1:]);cat.append(f)
final=list(map(tuple,arithmetic(re.search(r'^def finalGates : List Gt := (.+)$',s,re.M).group(1))))
assert cat==final
assert set(final)=={(op,a,b) for op in [False,True] for a in range(7) for b in range(a+1,7)} and len(final)==42
r13=arithmetic(re.search(r'^def masks13 : List \(Nat × Nat\) := (.+)$',s,re.M).group(1));assert r13[0]==[0,1]
un=0
for H,ph in r13[1:]:assert ph==0 and not (un&H);un|=H
assert un==(1<<214)-1
assert 'def optM14 : List (Nat × Nat) := [(0, 1), (FF, 0)]' in s
report={'verdict':'STATIC PASS; full named-file build and checker pending','sha256':hashlib.sha256(s.encode()).hexdigest(),'bytes':len(s.encode()),'lines':len(s.splitlines()),'size_margin_bytes':512*1024-len(s.encode()),'assembly_exact':True,'keyword_only_conversions':len(conv),'conversion_list_exact':True,'final_statement_exact_and_unconditional':True,'shared_semantic_modules_unchanged':shared,'options':opts,'attributes':attrs,'representatives':checks,'catalogue_count':len(final),'catalogue_exact_42_and_prior_dependencies':True,'root13_complete_shards':len(r13),'root14_unary_and_full_binary':True,'upstream_import_guard':'PASS'}
(p/'review-final-safe-static.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['representatives','shared_semantic_modules_unchanged','attributes']},indent=2))
print('Representative cases:',len(checks),'sharded',sum(x['mode']=='sharded' for x in checks),'numeric split checks',sum(x.get('numeric_checks',1) for x in checks))
