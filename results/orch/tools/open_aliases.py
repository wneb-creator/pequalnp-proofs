import argparse,json,pathlib,re
from collections import defaultdict
ap=argparse.ArgumentParser();ap.add_argument('source',type=pathlib.Path);ap.add_argument('output',type=pathlib.Path);ap.add_argument('--report',type=pathlib.Path,required=True);a=ap.parse_args()
s=a.source.read_text()
cmd=re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|variable\b|set_option\b|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)',re.M)
starts=[m.start() for m in cmd.finditer(s)]+[len(s)]
alias=re.compile(r'^(?:(?:private|noncomputable)\s+)*abbrev\s+(\w+)\s*:=\s*@([A-Za-z_][\w.]*)\s*$')
units=[];ns=[];frames=[];aliases={};decl_at={};ns_first={}
decl_re=re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w.]*)')
for i,(b,e) in enumerate(zip(starts,starts[1:])):
 text=s[b:e];line=text.splitlines()[0];units.append((tuple(ns),text));ns_first.setdefault(tuple(ns),i)
 dm=decl_re.match(text)
 if dm:
  dn=dm.group(1);df=dn if dn.startswith('PEqualNP.') else '.'.join(ns+[dn]);decl_at[df]=i
 m=alias.fullmatch(text.strip())
 if m:
  name,target=m.groups();own='.'.join(ns+[name]);tns,tname=target.rsplit('.',1)
  if name==tname and tuple(tns.split('.'))!=tuple(ns):aliases[i]=(tuple(ns),own,name,target,tns)
 if line.startswith('namespace '):frames.append(len(ns));ns.extend(line[len('namespace '):].strip().split('.'))
 elif line.startswith('section') or line.startswith('noncomputable section'):frames.append(len(ns))
 elif line.startswith('end') and frames:del ns[frames.pop():]
# Keep aliases named explicitly through their local namespace anywhere except alias declarations.
code='\n'.join(text for _,text in units if not alias.fullmatch(text.strip()))
qualified=set(re.findall(r'[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+',code))
def qualified_use(own):
 parts=own.split('.')
 return any('.'.join(parts[j:]) in qualified for j in range(len(parts)-1))
removed={i:v for i,v in aliases.items() if not qualified_use(v[1]) and decl_at.get(v[3],10**9)<ns_first[v[0]]}
groups=defaultdict(lambda:defaultdict(list));first={}
for i,(ns,own,name,target,tns) in removed.items():
 groups[ns][tns].append(name);first.setdefault(ns,i)
out=[s[:starts[0]]];pending=[]
for i,(ns,text) in enumerate(units):
 if text.startswith('set_option '):pending.append(text);continue
 if i in removed:
  pending=[]
  if first[ns]==i:
   for tns,names in groups[ns].items():out.append('open '+tns+' ('+' '.join(dict.fromkeys(names))+')\n')
   out.append('\n')
  continue
 out.extend(pending);pending=[];out.append(text)
out.extend(pending);result=''.join(out);a.output.write_text(result)
r={'before_bytes':len(s.encode()),'after_bytes':len(result.encode()),'aliases_removed':len(removed),'groups':sum(len(v) for v in groups.values()),'removed':[(v[1],v[3]) for v in removed.values()]}
a.report.write_text(json.dumps(r,indent=2));print(json.dumps({k:v for k,v in r.items() if k!='removed'}))
