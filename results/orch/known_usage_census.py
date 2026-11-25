from __future__ import annotations
import argparse, ast, collections, hashlib, json, re
from pathlib import Path

ap=argparse.ArgumentParser(description='Census numeric known-bound queries and packed column selectors in the closed L-meta-670 certificate.')
ap.add_argument('source',type=Path)
ap.add_argument('candidates',type=Path)
ap.add_argument('output',type=Path)
a=ap.parse_args()
raw=a.source.read_bytes(); source=raw.decode(); lines=source.splitlines()

def require(test,message):
    if not test: raise ValueError(message)

# Every named declaration is isolated so multiline tables and finite matches are covered.
head=re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev|inductive|structure)\s+([^\s(:{]+)')
starts=[(i,head.match(line).group(1)) for i,line in enumerate(lines) if head.match(line)]
decls={}
for j,(i,name) in enumerate(starts):
    end=starts[j+1][0] if j+1<len(starts) else len(lines)
    require(name not in decls, f'duplicate declaration name {name}')
    decls[name]={'line':i+1,'text':'\n'.join(lines[i:end]),'first':lines[i]}

known={}; origin=[]
for name,d in decls.items():
    if not re.fullmatch(r'known\d+',name): continue
    m=re.fullmatch(r'(?:noncomputable )?def '+re.escape(name)+r'\s*:=\s*extendKnown (\[\]|known\d+) (\d+) (\[.*\])',d['first'])
    require(m, f'unparsed known definition {name}')
    old,limit,lit=m.groups(); limit=int(limit); carries=ast.literal_eval(lit)
    require(old=='[]' or old in known,f'unknown predecessor {old}')
    require(isinstance(carries,list),f'invalid carries {name}')
    entries=[]
    for index,pair in enumerate(carries):
        require(isinstance(pair,tuple) and len(pair)==2 and isinstance(pair[0],int) and isinstance(pair[1],list),f'bad carry {name}:{index}')
        item={'owner':name,'index':index,'id':pair[0],'bound':limit,'swaps':pair[1],'line':d['line']}
        entries.append(item);origin.append(item)
    known[name]=entries+([] if old=='[]' else known[old])
require(len(origin)>0,'no knowledge entries found')

columns={}
for name,d in decls.items():
    if not re.match(r'^(?:noncomputable )?def \w+ : List ColumnInfo :=',d['first']):continue
    lit=d['first'].split(':=',1)[1].strip()
    value=ast.literal_eval(lit)
    require(isinstance(value,list) and all(isinstance(c,tuple) and len(c)==5 and all(isinstance(x,int) and x>=0 for x in c) for c in value),f'bad columns {name}')
    columns[name]=value

forests={}
for name,d in decls.items():
    if ': Forest :=' not in d['first']:continue
    m=re.fullmatch(r'(?:noncomputable )?def '+re.escape(name)+r' : Forest := ⟨(\d+),(\d+),fun j => (\w+)\[j\]\?\.getD \(0,0\),(\w+),(\w+),(\w+),(\w+)⟩',d['first'])
    require(m,f'unparsed forest {name}')
    mask,cap,samples,cols,autos,levels,index=m.groups()
    require(cols in columns,f'unknown columns {name}')
    forests[name]={'mask':int(mask),'cap':int(cap),'columns':cols,'levels':levels,'index':index,'line':d['line']}
require(len(forests)==len(columns),'unbound or shared column table: audit manually')

queries=[]; closed_calls=[]
def query(kind,prior,q,line,**details):
    require(prior=='[]' or prior in known,f'unknown closed prior {prior}')
    rows=[] if prior=='[]' else known[prior]
    found=next((e for e in rows if e['id']==q),None)
    queries.append({'kind':kind,'prior':prior,'q':q,'line':line,'value':0 if found is None else found['bound'],'origin':None if found is None else [found['owner'],found['index']],**details})

graph_priors={}
for i,line in enumerate(lines):
    for m in re.finditer(r'graphValid\s+(\w+)\s+\(boundsBefore\s+(\[\]|known\d+)\)',line):
        forest,prior=m.groups()
        require(forest in forests,f'unknown closed forest {forest}')
        require(forest not in graph_priors or graph_priors[forest]==prior,f'forest has multiple priors {forest}')
        if forest in graph_priors:continue
        graph_priors[forest]=prior;closed_calls.append({'kind':'graphValid','forest':forest,'prior':prior,'line':i+1})
        for index,c in enumerate(columns[forests[forest]['columns']]):
            if c[2]!=0:query('column',prior,c[2],i+1,forest=forest,column_index=index,column=list(c))
    if 'cut_root' in line and 'boundsBefore' in line:
        m=re.search(r'cut_root\s+\(prior:=boundsBefore\s+(known\d+)\)\s+\(before_sound\s+(known\d+)\s+\w+\)\s+(\(\d+,\d+,\d+,\d+,\d+\))',line)
        require(m,f'unparsed cut_root line {i+1}')
        prior,previous,lit=m.groups();require(prior==previous,f'cut prior mismatch line {i+1}')
        c=ast.literal_eval(lit);closed_calls.append({'kind':'cut_root','prior':prior,'column':list(c),'line':i+1})
        if c[2]!=0:query('cut_root',prior,c[2],i+1,column=list(c))
    if 'plainA' in line and 'boundsBefore' in line:
        m=re.search(r'plainA\s+\(q:=(\d+)\)\s+\(prior:=boundsBefore\s+(known\d+)\)\s+\(before_sound\s+(known\d+)\s+\w+\)',line)
        require(m,f'unparsed plainA line {i+1}')
        q,prior,previous=m.groups();require(prior==previous,f'plainA prior mismatch line {i+1}')
        closed_calls.append({'kind':'plainA','prior':prior,'q':int(q),'line':i+1});query('plainA',prior,int(q),i+1)
    if 'boundsBefore' in line:
        recognized=any(token in line for token in ['def boundsBefore','Lower u (varsX q)','unfold boundsBefore','cut_root','graphValid','plainA'])
        require(recognized,f'unclassified boundsBefore occurrence line {i+1}: {line}')
require(set(graph_priors)==set(forests),'a forest has no closed graph validation')
closed_lines={c['line'] for c in closed_calls}
generic_bound_lines=[]
for i,line in enumerate(lines):
    occurrence_count=len(re.findall(r'\bboundsBefore\b',line))
    if not occurrence_count:continue
    require(occurrence_count==1,f'multiple boundsBefore occurrences on line {i+1}')
    if i+1 in closed_lines:continue
    stripped=line.strip()
    generic=(stripped==decls['boundsBefore']['first'] or
             stripped=='Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by' or
             stripped=='unfold boundsBefore')
    require(generic,f'unparsed non-closed boundsBefore occurrence line {i+1}')
    generic_bound_lines.append(i+1)
require(len(generic_bound_lines)==3,'unexpected generic boundsBefore occurrence count')
require(len(re.findall(r'\bboundsBefore\b',source))==len(closed_calls)+3,'boundsBefore occurrence coverage mismatch')
for i,line in enumerate(lines):
    if re.search(r'\bknown\d+\b',line):
        require(any(t in line for t in ['def known','Known ','boundsBefore','before_sound']),f'unclassified direct known-list reference line {i+1}')

# The following finite decoder exactly follows packedAt/getPairs/nodeVerified.
# It evaluates only the grammar occurring in the certificate's Nat word tables.
word_cache={}
tokenizer=re.compile(r'0x[0-9a-fA-F]+|\d+|[A-Za-z_][A-Za-z_0-9]*|[()]|<')
def word_tree(name):
    if name in word_cache:return word_cache[name]
    require(name in decls,f'unknown data word {name}')
    first=decls[name]['first']
    m=re.fullmatch(r'(?:noncomputable )?def '+re.escape(name)+r' \(i : Nat\) : Nat := (.*)',first)
    require(m,f'unsupported word table {name}')
    expr=m[1];tokens=tokenizer.findall(expr)
    require(''.join(tokens)==re.sub(r'\s+','',expr),f'unrecognized data tokens {name}')
    at=0
    def parse():
        nonlocal at
        t=tokens[at];at+=1
        if t=='(':
            r=parse();require(tokens[at]==')',f'missing ) in {name}');at+=1;return r
        if t=='if':
            require(tokens[at:at+2]==['i','<'],f'unsupported test {name}');at+=2
            limit=int(tokens[at],0);at+=1;require(tokens[at]=='then',f'missing then {name}');at+=1
            yes=parse();require(tokens[at]=='else',f'missing else {name}');at+=1
            no=parse();return (limit,yes,no)
        return int(t,0)
    tree=parse();require(at==len(tokens),f'trailing tokens {name}')
    word_cache[name]=tree;return tree

def word(name,i):
    t=word_tree(name)
    while isinstance(t,tuple):t=t[1] if i<t[0] else t[2]
    return t

def packed(name,pos,length):
    i,shift=divmod(pos,8192);lo=word(name,i)>>shift
    if shift+length>8192:lo|=word(name,i+1)<<(8192-shift)
    return lo&((1<<length)-1)

def levels(name):
    require(name in decls,f'unknown levels {name}')
    text=decls[name]['text'];rows={}
    for line in text.splitlines()[1:]:
        m=re.fullmatch(r'\s*\| (\d+) => (.+?)\s*',line)
        if m:
            k,p=m.groups()
            if p.startswith('('):
                expression=p
            else:
                require(p in decls,f'unknown packing {p}')
                expression=decls[p]['first'].split(':=',1)[1].strip()
            pm=re.fullmatch(r'\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\w+)\)',expression)
            require(pm,f'unparsed packing {p}');rows[int(k)]=tuple(map(int,pm.groups()[:7]))+(pm[8],)
        elif line.strip().startswith('|'):
            require(line.strip()=='| _ => emptyPacking',f'unparsed level alternative {name}: {line}')
    require(rows,f'no explicit levels {name}')
    return rows

packed_census=[]
for forest,info in forests.items():
    cols=columns[info['columns']];raw_length=(info['mask']&511).bit_count()
    for k,p in levels(info['levels']).items():
        require(k<=info['cap'],f'unchecked high level {forest}:{k}')
        num,depth,cw,iw,pw,offw,lw,data=p
        counts=collections.Counter();invalid=collections.Counter()
        for node in range(num):
            start=num*(10*depth+raw_length+depth)
            pos=start+num*offw+packed(data,start+node*offw,offw)
            nr=packed(data,pos,5);st=pos+5+lw
            for j in range(nr):
                value=packed(data,st+j*(cw+depth),cw+depth)
                index=value&((1<<cw)-1)
                if index<len(cols):counts[index]+=1
                else:invalid[index]+=1
        require(not invalid,f'out-of-range packed column in {forest}, level{k}: {dict(invalid)}')
        packed_census.append({'forest':forest,'level':k,'nodes':num,'rule_references':sum(counts.values()),'columns':[{'index':i,'q':cols[i][2],'references':n} for i,n in sorted(counts.items())],'out_of_range_columns':dict(invalid)})

used={tuple(q['origin']) for q in queries if q['origin'] is not None}
unused=[e for e in origin if (e['owner'],e['index']) not in used]
candidates=json.loads(a.candidates.read_text());candidate_rows=[]
for row in candidates:
    for q in row['remove']:
        matches=[e for e in origin if e['owner']==row['name'] and e['id']==q]
        require(len(matches)==1,f'ambiguous candidate {row["name"]}:{q}')
        e=matches[0];uses=[v for v in queries if v['origin']==[e['owner'],e['index']]]
        candidate_rows.append({'owner':e['owner'],'id':q,'origin_index':e['index'],'queried':bool(uses),'query_sites':uses})

def preserves(removals):
    for q in queries:
        rows=[] if q['prior']=='[]' else known[q['prior']]
        found=next((e for e in rows if (e['owner'],e['index']) not in removals and e['id']==q['q']),None)
        value=0 if found is None else found['bound']
        if value!=q['value']:return False
    return True
candidate_origins={(r['owner'],r['origin_index']) for r in candidate_rows}
unused_origins={(r['owner'],r['index']) for r in unused}
require(preserves(candidate_origins),'candidate pruning changes a numeric query')
require(preserves(unused_origins),'full unused pruning changes a numeric query')
for batch in packed_census:
    queried={q['q'] for q in queries if q.get('forest')==batch['forest']}
    require(all(c['q']==0 or c['q'] in queried for c in batch['columns']),'packed rule q lacks a static query site')

report={'source':str(a.source),'source_sha256':hashlib.sha256(raw).hexdigest(),'analysis':'Conservative complete numeric-query census for every closed graphValid column, cut_root column, and plainA call. Packed rules select existing static columns; state-hash indexes do not query known bounds. This is an offline dependency analysis, not a Lean proof or a checker acceptance.','counts':{'forests':len(forests),'column_tables':len(columns),'static_columns':sum(map(len,columns.values())),'known_entries':len(origin),'known_lists':len(known),'closed_calls':len(closed_calls),'numeric_query_sites':len(queries),'distinct_queried_ids':len({q['q'] for q in queries}),'used_origins':len(used),'unused_origins':len(unused),'candidate_entries':len(candidate_rows),'queried_candidates':sum(r['queried'] for r in candidate_rows),'packed_nodes':sum(r['nodes'] for r in packed_census),'packed_rule_references':sum(r['rule_references'] for r in packed_census)},'validation':{'all_candidate_query_values_preserved':True,'all_unused_query_values_preserved':True,'every_packed_q_has_static_query_site':True,'unclassified_boundsBefore_occurrences':0,'unclassified_direct_known_references':0,'boundsBefore_occurrences':len(closed_calls)+3,'generic_boundsBefore_lines':generic_bound_lines,'all_packed_column_indices_in_range':True},'closed_calls':closed_calls,'queries':queries,'unused_entries':unused,'candidate_review':candidate_rows,'packed_census':packed_census}
a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'source_sha256':report['source_sha256'],'counts':report['counts']},indent=2))
