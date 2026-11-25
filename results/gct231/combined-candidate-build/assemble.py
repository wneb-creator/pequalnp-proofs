from pathlib import Path
import hashlib,json,re,datetime,argparse

repo=Path('/workspace/pequalnp-proofs')
base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
out=base/'integration'
named=repo/'lean/PEqualNP/Outside/L_gct_231.lean'
aux='PEqualNP.Outside.L_gct_231_aux'
parser=argparse.ArgumentParser()
parser.add_argument('--extra',action='append',default=[],help='UniqueLabel=/absolute/checked/source.lean')
parser.add_argument('--additional-import',action='append',default=[])
parser.add_argument('--output',default='L_gct_231_CombinedCandidate.lean')
parser.add_argument('--manifest-tag',default='assembly')
args=parser.parse_args()
components=[
 ('CommonPlaneIntegration',base/'library/CommonPlaneCoefficientIdentities.lean'),
 ('FactorMatchingIntegration',base/'fresh/LinearFactorMatchingFull.lean'),
 ('C4Coordinates',base/'fresh/C4CoordinateInterfaceFull.lean'),
 ('PolynomialNonsquareIntegration',base/'library/PolynomialNonsquare.lean'),
 ('IsolatedVertex',base/'isolated-vertex/IsolatedVertexAdditions.txt'),
 ('C4OpenCertificates',base/'c4-small-certificates/C4OpenCases01Scoped.lean'),
]
for item in args.extra:
    label,path=item.split('=',1)
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',label)
    components.append((label,Path(path)))
assert len({label for label,path in components})==len(components)
def sha(text):return hashlib.sha256(text.encode()).hexdigest()
def split_source(text):
    lines=text.splitlines(keepends=True)
    imports=[line.strip() for line in lines if line.startswith('import ')]
    start=next(i for i,line in enumerate(lines) if line.startswith('namespace '))
    ns=lines[start].strip().removeprefix('namespace ')
    finish=max(i for i,line in enumerate(lines) if line.strip()==f'end {ns}')
    assert not ''.join(lines[finish+1:]).strip()
    return imports,ns,''.join(lines[start+1:finish])

snapshot=out/'Named1528Snapshot.lean'
old=snapshot.read_text() if snapshot.exists() else named.read_text()
imports,ns,oldbody=split_source(old)
assert ns==aux and len(old.splitlines())==1528
if not snapshot.exists():snapshot.write_text(old)
allimports=list(imports);chunks=[];records=[]
for module in args.additional_import:
    assert module=='PEqualNP.Defs' or module=='Mathlib' or module.startswith('Mathlib.')
    imp='import '+module
    if imp not in allimports:allimports.append(imp)
for label,path in components:
    source=path.read_text();imps,namespace,body=split_source(source)
    for imp in imps:
        # The original deprecated compatibility module already provides this module.
        if imp=='import Mathlib.Basic.Complex.Basic' and 'import Mathlib.Data.Complex.Basic' in allimports:continue
        if imp not in allimports:allimports.append(imp)
    if namespace==aux:
        opening=f'section {label}\n';closing=f'end {label}\n'
        rebased=aux
    else:
        opening=f'namespace {label}\n';closing=f'end {label}\n'
        rebased=f'{aux}.{label}'
    chunks.append(opening+body+closing)
    records.append({'component':label,'path':str(path),'source_sha256':sha(source),
      'body_sha256':sha(body),'old_namespace':namespace,'new_namespace':rebased,
      'bytes':len(source.encode()),'body_preserved_bytewise':True})
candidate='\n'.join(allimports)+'\n\nnamespace '+aux+'\n'+oldbody+'\n'+''.join('\n'+c for c in chunks)+'\nend '+aux+'\n'
assert oldbody in candidate
assert candidate.count(oldbody)==1
assert len(allimports)==len(set(allimports))
assert all(line.endswith(' in') for line in candidate.splitlines() if line.startswith('set_option '))
assert not any(token in candidate for token in ['_root_','"','sorry','native_decide'])
assert not re.search(r'^\s*(axiom|initialize|#|macro|syntax|elab|attribute)\b',candidate,re.M)
stack=[];declarations={};duplicates=[]
for line_no,line in enumerate(candidate.splitlines(),1):
    if line.startswith('namespace '):stack.append(('namespace',line.split(' ',1)[1]))
    elif line.startswith('section '):stack.append(('section',line.split(' ',1)[1]))
    elif line.startswith('end '):
        typ,name=stack.pop();assert name==line.split(' ',1)[1],(line_no,name,line)
    else:
        m=re.match(r'(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)',line)
        if m:
            full='.'.join([v for kind,v in stack if kind=='namespace']+[m.group(1)])
            if full in declarations:duplicates.append((full,declarations[full],line_no))
            declarations[full]=line_no
assert not stack
assert not duplicates,duplicates
assert Path(args.output).name==args.output
target=out/args.output
assert not target.exists(), 'Use a new versioned output to preserve prior candidates.'
target.write_text(candidate)
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'candidate':str(target),'candidate_sha256':sha(candidate),'bytes':len(candidate.encode()),
 'lines':len(candidate.splitlines()),'named_source_sha256':sha(old),'named_lines':1528,
 'old_body_sha256':sha(oldbody),'old_body_preserved_bytewise':True,
 'imports':allimports,'new_imports':[p for p in allimports if p not in imports],
 'components':records,'declaration_count':len(declarations),'duplicate_declarations':duplicates,
 'static_safety_scan':'PASS','build_status':'NOT_RUN_WAITING_FOR_ROOT_MEMORY_SLOT',
 'main_theorem_present':False,
 'scope':'Preservation partial only. The posted existential theorem is absent.'}
(out/(args.manifest_tag+'-manifest.json')).write_text(json.dumps(record,indent=2)+'\n')
(out/(args.manifest_tag+'-declaration-index.json')).write_text(json.dumps(declarations,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['candidate','candidate_sha256','bytes','lines','declaration_count','new_imports','old_body_preserved_bytewise','static_safety_scan','build_status']},indent=2))
