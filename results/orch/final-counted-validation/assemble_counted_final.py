from pathlib import Path
from collections import Counter
import hashlib,json,re

P=Path('/tmp/oec/pequalnp-pilot-182')
OLD='PEqualNP.Outside.L_meta_10760_first'
NS='PEqualNP.Outside.L_meta_10760'
SOURCE=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_10760.lean')
ORIGINAL='0199ec155b8609bb2b9412fb772637b7971e9ee9d633c08f9ae388b3f08b325d'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==ORIGINAL
audit={'original_sha256':ORIGINAL,'inputs':{},'removed':[],'transformations':[]}
command=re.compile(r'^(?:(?:noncomputable|private|protected) )?(?:def|lemma|theorem|instance|structure|inductive|class|abbrev|namespace|section|end|open|variable|set_option|attribute|include|omit|export|mutual|local)\b|^@\[',re.M)

def read(name):
    path=P/(name+'.lean');b=path.read_bytes();audit['inputs'][name]=hashlib.sha256(b).hexdigest()
    s=b.decode();lines=[]
    for line in s.splitlines():
        if line.startswith('import '):continue
        if line.strip() in ['namespace '+OLD,'end '+OLD,'namespace '+NS,'end '+NS,'namespace '+NS+'.Counted','end '+NS+'.Counted']:continue
        lines.append(line)
    return '\n'.join(lines).strip().replace(OLD,NS).replace('L_meta_10760_first','L_meta_10760')+'\n'

def decl_span(s,name):
    match=re.search(r'^(?:(?:noncomputable|private|protected) )?(?:def|lemma|theorem) '+re.escape(name)+r'(?=\s|:)',s,re.M)
    if not match:raise RuntimeError('Missing declaration '+name)
    nxt=command.search(s,match.end());return match.start(),nxt.start() if nxt else len(s)

def remove(s,name,why):
    a,b=decl_span(s,name);old=s[a:b]
    audit['removed'].append({'name':name,'reason':why,'bytes':len(old.encode()),'lines':old.count('\n'),'sha256':hashlib.sha256(old.encode()).hexdigest()})
    return s[:a]+s[b:]

tight=read('TightNotFirst')
a=tight.index('def LTR ');b=tight.index('open PEqualNP.CircuitLowerBounds',a)
ltr=tight[a:b];tight=tight[:a]+tight[b:]
counted=read('CountedFirst')
a=counted.index('def MFt ');b=counted.index('lemma ltr_add ');c=counted.index('lemma live_rho_ltr ')
core=counted[a:b];middle=counted[b:c];symmetry=counted[c:]
engine=read('KernelFirstEngine')
for name in ['MF.bi','MF.gate','phase_step','one_sound','look1_sound','topC_sound']:
    engine=remove(engine,name,'replaced by exact-count soundness')
a,b=decl_span(engine,'topC_ok')
engine=engine[:a]+ltr+'\n'+core+'\ntheorem topC_ok : TopOk topC := topC_ok_unrestricted\n\n'+engine[b:]
audit['transformations'].append('Move unchanged LTR core earlier; replace original MF-threaded soundness with CountedFirst core; preserve TopOk contract via topC_ok_unrestricted.')

def counted_types(s):
    return re.sub(r'\bImp (\[[^\n]*?\]) 0 13\b',r'ImpT \1 0 13 1',s)

parts=['import PEqualNP.Defs\n\nnamespace '+NS+'\n',engine]
for name in ['KernelFirstTables','FirstReject','RootShardAdapter','Root13Safe','OwnSequence','OwnRows']:
    parts.append(read(name))
parts.append(middle)
parts.append(counted_types(read('GateCatalogue')))
parts.append(read('SymmetryFirst'))
parts.append(symmetry)
parts.append(read('CountedCases'))
root14=counted_types(read('Root14Safe')).replace('reject_one_shards ','reject_one_shards_t ')
# The unconditional lower bound assumption remains unrestricted.
root14=root14.replace('(hmin : ImpT [] 0 13 1)','(hmin : Imp [] 0 13)')
parts.append(root14)
chain=counted_types(read('ChainFirst')).replace('sym_bound ','sym_bound_t ').replace('imp_gate_swap ','impT_gate_swap ')
parts.append(chain)
parts.extend([tight,read('TightFinalGlue')])
parts.append('end '+NS+'\n\ntheorem '+NS+' :\n    '+(P/'statement.txt').read_text().strip()+' :=\n  '+NS+'.replacement_from_one '+NS+'.bound13\n    ('+NS+'.live_excluded '+NS+'.all_gates_bound)\n')
s='\n'.join(parts)
s=re.sub(r'^lemma (?=[^\n]*:= by decide \+kernel\s*$)','def ',s,flags=re.M)

# Remove only declaration leaves with no explicit references, no attributes,
# and no instance registration; repeat conservatively to remove their closure.
for iteration in range(40):
    tokens=Counter(re.findall(r'[A-Za-z_][A-Za-z_0-9]*',s));starts=list(command.finditer(s));cuts=[]
    for i,m in enumerate(starts):
        h=re.match(r'(?:(?:noncomputable|private|protected) )?(def|lemma|theorem) ([A-Za-z_][A-Za-z_0-9]*)(?=\s|:)',s[m.start():])
        if not h or tokens[h[2]]!=1:continue
        before=s[:m.start()].rstrip();prev=before.splitlines()[-1] if before else ''
        if prev.startswith('@['):continue
        end=starts[i+1].start() if i+1<len(starts) else len(s)
        cuts.append((m.start(),end,h[2]))
    if not cuts:break
    for a,b,name in reversed(cuts):
        old=s[a:b];audit['removed'].append({'name':name,'reason':'unreferenced unregistered declaration leaf, pass '+str(iteration),'bytes':len(old.encode()),'lines':old.count('\n'),'sha256':hashlib.sha256(old.encode()).hexdigest()})
        s=s[:a]+s[b:]

# Name every section/end explicitly, without changing scope boundaries.
stack=[];serial=0;lines=[]
for line in s.splitlines():
    section=re.fullmatch(r'(noncomputable )?section(?: ([A-Za-z_][A-Za-z_0-9.]*))?',line)
    namespace=re.fullmatch(r'namespace (\S+)',line)
    ending=re.fullmatch(r'end(?: (\S+))?',line)
    if section:
        name=section[2]
        if name is None:
            serial+=1;name='counted_scope_'+str(serial);line=(section[1] or '')+'section '+name
        stack.append(name)
    elif namespace:stack.append(namespace[1])
    elif ending:
        assert stack,(line,'empty scope');name=stack.pop()
        assert ending[1] is None or ending[1]==name,(ending[1],name)
        line='end '+name
    lines.append(line)
assert not stack,stack
s='\n'.join(lines)+'\n'
assert s.count('import ')==1
assert '_root_' not in s and '"' not in s and 'sorry' not in s and 'native_decide' not in s
long=re.findall(r'(?<![\w])(?:0x[0-9a-fA-F]+|[0-9]+)(?![\w])',s)
assert not [n for n in long if len(n.removeprefix('0x'))>20]
out=P/'CountedFinalCandidate.lean';out.write_text(s)
audit.update({'candidate_sha256':hashlib.sha256(s.encode()).hexdigest(),'bytes':len(s.encode()),'lines':len(s.splitlines()),'numeric_kernel_checks':s.count('decide +kernel'),'scope_names_added':serial})
(P/'counted-assembly-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==ORIGINAL
print(json.dumps({k:audit[k] for k in ['candidate_sha256','bytes','lines','numeric_kernel_checks','scope_names_added']}))
if len(s.encode())>512*1024:raise RuntimeError('Candidate exceeds 512KiB')
