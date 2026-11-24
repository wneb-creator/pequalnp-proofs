from pathlib import Path
import sys,re,json,hashlib

START=re.compile(r'^(import|namespace|end|open|variable|include|section|set_option|lemma|theorem|def|abbrev|noncomputable|private|protected|structure|inductive|class|instance|@\[)\b')
DECL=re.compile(r'^(?:(?:noncomputable|private|protected)\s+)*(lemma|theorem|def|abbrev|structure|inductive|class|instance)\s+([^\s:{(]+)')
def norm(t): return re.sub(r'\s+',' ',t).strip().replace('theorem ','lemma ')
def digest(t): return hashlib.sha256(t.encode()).hexdigest()
def chunks(text):
    lines=text.splitlines(keepends=True)
    starts=[i for i,l in enumerate(lines) if START.match(l)]
    assert not ''.join(lines[:starts[0]]).strip()
    starts.append(len(lines))
    for i,j in zip(starts,starts[1:]):yield i+1,''.join(lines[i:j])

outpath=Path(sys.argv[1]); sources=[Path(x) for x in sys.argv[2:]]
seen={};imports=set();out=[];duplicates=[];conflicts=[];decls=[]
for path in sources:
    stack=[];pending=[]
    for line,chunk in chunks(path.read_text()):
        first=chunk.splitlines()[0]
        if first.startswith('import '):
            if first not in imports:out.append(chunk);imports.add(first)
            continue
        if first.startswith(('set_option ','open ','include ')) and chunk.strip().endswith(' in'):
            pending.append(chunk);continue
        if first.startswith('@['):
            pending.append(chunk);continue
        m=DECL.match(first)
        if m:
            kind,name=m.groups();qname='.'.join(stack+[name]);full=''.join(pending)+chunk;pending=[]
            entry={'name':qname,'source':str(path),'line':line,'kind':kind,'sha256':digest(full)}
            if qname in seen:
                old,oldfull=seen[qname]
                equal=norm(full)==norm(oldfull)
                entry['kept']=old;entry['identical_normalized']=equal
                if not equal:
                    head=re.split(r':=|\bwhere\b',chunk,maxsplit=1)[0]
                    oldhead=re.split(r':=|\bwhere\b',oldfull,maxsplit=1)[0]
                    entry['header_equal']=norm(head)==norm(oldhead)
                    entry['old_text']=oldfull;entry['new_text']=full
                    conflicts.append(entry)
                duplicates.append({k:v for k,v in entry.items() if k not in ['old_text','new_text']})
                continue
            seen[qname]=(entry,full);decls.append(entry);out.append(full);continue
        assert not pending,(path,line,'unattached options')
        out.append(chunk)
        if first.startswith('namespace '):stack.append(first.removeprefix('namespace ').strip())
        elif first.startswith('end'):
            assert stack,(path,line,'unmatched end')
            stack.pop()
        elif first.startswith('section'):raise RuntimeError('section needs explicit support')
    assert not stack and not pending,(path,stack,pending)
text=''.join(out)
outpath.write_text(text)
report={'output':str(outpath),'bytes':len(text.encode()),'lines':len(text.splitlines()),'sha256':digest(text),'sources':[{ 'path':str(p),'sha256':digest(p.read_text())} for p in sources],'declarations':decls,'duplicates':duplicates,'conflicts':conflicts}
manifest=outpath.with_suffix('.assembly.json');manifest.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'output':str(outpath),'bytes':report['bytes'],'lines':report['lines'],'declarations':len(decls),'duplicates':len(duplicates),'conflicts':len(conflicts),'manifest':str(manifest)}))
for c in conflicts:print(json.dumps({k:c[k] for k in ['name','source','line','kind','header_equal']},ensure_ascii=False))
