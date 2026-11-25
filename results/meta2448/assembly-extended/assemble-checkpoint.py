from pathlib import Path
import argparse, datetime, hashlib, json, re
parser=argparse.ArgumentParser(description="Assemble checked helper bodies into a portable partial checkpoint.")
parser.add_argument("output",type=Path)
parser.add_argument("sources",nargs="+",type=Path)
a=parser.parse_args()
parts=[]; inputs=[]
for i,p in enumerate(a.sources):
    data=p.read_bytes(); source=data.decode("utf-8")
    inputs.append({"path":str(p),"sha256":hashlib.sha256(data).hexdigest(),"lines":len(source.splitlines()),"dependency_lines":[line for line in source.splitlines() if line.startswith("import ")]})
    parts.append(source if i==0 else "\n".join(line for line in source.splitlines() if not line.startswith("import "))+"\n")
source="\n".join(parts)
assert [line for line in source.splitlines() if line.startswith("import ")]==["import PEqualNP.Defs"]
assert not any(word in source for word in ["_root_",chr(34),"sorry","native_decide"])
assert not re.search(r"^\s*(axiom|instance|#)",source,re.M)
stack=[]; declarations=[]
for number,line in enumerate(source.splitlines(),1):
    m=re.fullmatch(r"namespace\s+(\S+)\s*",line)
    if m:
        stack.append(m.group(1));continue
    m=re.fullmatch(r"end\s+(\S+)\s*",line)
    if m:
        assert stack and stack[-1]==m.group(1),(number,line,stack)
        stack.pop();continue
    m=re.match(r"(?:(?:private|protected|noncomputable)\s+)?(lemma|theorem|def|abbrev)\s+([^\s(:]+)",line)
    if m:
        kind,name=m.groups();full=".".join(stack+[name])
        assert full.startswith("PEqualNP.Outside.L_meta_2448_aux.")
        declarations.append({"line":number,"kind":kind,"name":full})
assert not stack
assert len(declarations)==len({d["name"] for d in declarations})
a.output.write_text(source)
stem=a.output.with_suffix("")
manifest={"created_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"candidate":str(a.output),"sha256":hashlib.sha256(a.output.read_bytes()).hexdigest(),"lines":len(source.splitlines()),"bytes":a.output.stat().st_size,"inputs":inputs,"modification":"Unmodified first source followed by remaining checked bodies with only dependency lines removed.","target_proved":False,"kernel_checked":False,"scope":"Portable partial checkpoint only; the posted global-minimum star-profile statement remains unproved.","declarations":declarations}
Path(str(stem)+".manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
probe=a.output.with_name(a.output.stem+"Axioms.lean")
probe.write_text("import "+a.output.stem+"\n\n"+"".join("#print axioms "+d["name"]+"\n" for d in declarations))
print(json.dumps({"candidate":str(a.output),"sha256":manifest["sha256"],"lines":manifest["lines"],"bytes":manifest["bytes"],"declarations":len(declarations),"axiom_probe":str(probe)},indent=2))
