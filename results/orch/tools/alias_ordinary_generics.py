import argparse,json,re
from pathlib import Path
parser=argparse.ArgumentParser(description='Apply only independently checked ordinary-model definition equalities.')
parser.add_argument('source',type=Path);parser.add_argument('output',type=Path)
parser.add_argument('--map',type=Path,required=True);parser.add_argument('--report',type=Path,required=True)
args=parser.parse_args();source=args.source.read_text();mapping=json.loads(args.map.read_text())
choices={(r['case'],r['name']):r['target_case'] for r in mapping}
assert all(c in ['C1676','C1678'] and target=='C2444' for (c,name),target in choices.items())
command=re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|include\b|omit\b|variable\b|set_option\b|@\[|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)',re.M)
declaration=re.compile(r'^(?P<mods>(?:(?:private|protected|noncomputable)\s+)*)(?P<kind>def|abbrev)\s+(?P<name>[A-Za-z_][\w.]*)')
starts=[m.start() for m in command.finditer(source)]+[len(source)]
namespace=[];frames=[];out=[source[:starts[0]]];changed=[]
for a,b in zip(starts,starts[1:]):
 block=source[a:b];line=block.splitlines()[0];m=declaration.match(block)
 if m and len(namespace)==4 and namespace[:3]==['PEqualNP','Outside','L_meta_670']:
  case=namespace[-1];key=(case,m['name'])
  if key in choices:
   target='PEqualNP.Outside.L_meta_670.'+choices[key]+'.'+m['name']
   replacement=m['mods']+'abbrev '+m['name']+' := @'+target+'\n\n'
   changed.append({'name':'.'.join(namespace+[m['name']]),'target':target,'savedBytes':len(block.encode())-len(replacement.encode())})
   block=replacement
 out.append(block)
 if line.startswith('namespace '):frames.append(len(namespace));namespace.extend(line[10:].strip().split('.'))
 elif line.startswith(('section','noncomputable section')):frames.append(len(namespace))
 elif line.startswith('end') and frames:del namespace[frames.pop():]
result=''.join(out);args.output.write_text(result)
report={'source':str(args.source),'output':str(args.output),'beforeBytes':len(source.encode()),'afterBytes':len(result.encode()),'aliases':changed}
args.report.write_text(json.dumps(report,indent=2));print(json.dumps({k:(len(v) if k=='aliases' else v) for k,v in report.items()}))
