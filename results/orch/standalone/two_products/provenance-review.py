from pathlib import Path
import hashlib, json, re

repo=Path('/workspace/pequalnp-proofs')
folder=repo/'results/orch/standalone/two_products'
manifest=json.loads((folder/'manifest.json').read_text())
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
candidate=folder/'TwoProductsStandalone.lean'
assert digest(candidate)==manifest['source_sha256']=='1d902852fc9202616b3ca6abdeb8d857acfb3f075c024f86b3796d81b848de1c'
assert len(candidate.read_bytes())==manifest['source_bytes']==52816
assert len(candidate.read_text().splitlines())==manifest['source_lines']==1140
sources=[repo/manifest['foundation_source'],repo/manifest['graph_source']]
assert digest(sources[0])==manifest['foundation_sha256']=='72c333a765a480d06fbae71d6afa211f788c15109a7f201eae70da7a1f798890'
assert digest(sources[1])==manifest['graph_source_sha256']=='e504f6940b327d5af4892bcb2455c6e04088f5ae7bf819b3aee9fca2e89b2903'
assert sources[1].read_bytes()==Path('/tmp/oec/pequalnp-pilot-75/library/TwoSilentProductsGraphOnly.lean').read_bytes()
assert digest(folder/'extract_standalone.py')==manifest['extraction_script_sha256']
assert digest(folder/'dependency-closure.log')==manifest['closure_log_sha256']
deps=set(re.findall(r'^DEP (\S+)',(folder/'dependency-closure.log').read_text(),re.M))
assert len(deps)==manifest['constant_closure_count']==142

header=re.compile(r'^(?:import|namespace|end|open|set_option|(?:noncomputable )?(?:private )?(?:def|lemma|theorem|abbrev))\b')
decl=re.compile(r'^(?:noncomputable )?(?:private )?(?:def|lemma|theorem|abbrev) (\S+)')

def parse(source):
    blocks=[]
    for line_no,line in enumerate(source.read_text().splitlines(True),1):
        if header.match(line): blocks.append([line_no,line])
        elif blocks: blocks[-1][1]+=line
        else: assert not line.strip() or line.lstrip().startswith('--')
    root={'nodes':[],'name':''}
    stack=[root]
    options=''
    decls={}
    for line_no,block in blocks:
        first=block.splitlines()[0]
        if first.startswith('import '): continue
        if first.startswith('namespace '):
            short=first.split()[1]
            node={'kind':'namespace','name':'.'.join(filter(None,[stack[-1]['name'],short])),
                  'opening':block,'nodes':[],'closing':''}
            stack[-1]['nodes'].append(node); stack.append(node)
        elif first.startswith('end '):
            assert len(stack)>1
            stack.pop()['closing']=block
        elif first.startswith('set_option ') or (first.startswith('open ') and first.endswith(' in')):
            options+=block
        elif decl.match(first):
            name='.'.join(filter(None,[stack[-1]['name'],decl.match(first).group(1)]))
            assert name not in decls
            node={'kind':'decl','name':name,'text':options+block,'line':line_no}
            options=''; decls[name]=node; stack[-1]['nodes'].append(node)
        else: stack[-1]['nodes'].append({'kind':'context','text':block})
    assert len(stack)==1 and not options
    return root['nodes'],decls

def active(nodes,names):
    return any(node['kind']=='decl' and node['name'] in names or
               node['kind']=='namespace' and active(node['nodes'],names) for node in nodes)

def render(nodes,names):
    text=''
    for node in nodes:
        kind=node['kind']
        if kind=='decl' and node['name'] in names or kind=='context': text+=node['text']
        elif kind=='namespace' and active(node['nodes'],names):
            text+=node['opening']+render(node['nodes'],names)+node['closing']
    return text

_,candidate_decls=parse(candidate)
allnames=set(); chunks=[]
for source,listname,count in zip(sources,['foundation-retained.txt','graph-only-retained.txt'],[34,21]):
    nodes,decls=parse(source)
    records=[line.split() for line in (folder/listname).read_text().splitlines()]
    assert len(records)==count
    names=set()
    for line,name,size in records:
        assert name in decls and name not in allnames
        original=decls[name]
        assert original['line']==int(line)
        assert len(original['text'].encode())==int(size)
        assert original['text']==candidate_decls[name]['text']
        assert name in deps or any(x.startswith(name+'._') or x.startswith(name+'.match_') for x in deps)
        names.add(name);allnames.add(name)
    chunks.append(render(nodes,names))
    print(source.name,'EXACT_DECLARATION_BODIES_PASS',count)
assert set(candidate_decls)==allnames and len(allnames)==55
assert all(name in allnames or any(name.startswith(d+'._') or name.startswith(d+'.match_') for d in allnames) for name in deps)
rendered='import Mathlib\nimport PEqualNP.Defs\n\n'+'\n'.join(chunks)
old='''open M1528.P1.S98 (W AO Least Bel aliasWire aliasGate eraseC erase_length erase_AO
  erase_wires erase_W_lt erase_gateAt_lt erase_gateAt_ge W_gate W_input W_or W_and
  gateAt_eq AO_of_IsAO2 IsAO2_of_AO prefix_W)
open M1528.P2 (OrStep OrR Leaf orStep_lt orR_le orStep_mono orR_mono orR_leaf_true orR_leaf
  orR_cone pairInput_true graphFun_pair orReaches_orR orR_orReaches mem_orIn opnd_eq nfc)
'''
assert rendered.count(old)==1
rendered=rendered.replace(old,'open M1528.P1.S98 (W AO W_gate W_input W_or W_and gateAt_eq prefix_W)\n')
assert rendered==candidate.read_text()
assert candidate.read_text().splitlines()[:2]==['import Mathlib','import PEqualNP.Defs']
assert (folder/'build.log').read_bytes()==b''
audit=(folder/'axiom-audit.log').read_text()
assert all(x in audit for x in ['propext','Classical.choice','Quot.sound'])
print('ALL_BYTES_REPRODUCED_PASS; only documented selective-open adjustments')
print('DEPENDENCY_CLOSURE_PASS',len(deps),'constants; all 55 retained declarations exactly accounted for')
print('PROVENANCE_REVIEW_PASS',manifest['source_sha256'])
print('Scope: graph-only four-side subclass; no full-gap claim, independent compilation not repeated')
