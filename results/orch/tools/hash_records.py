from pathlib import Path
from collections import Counter
from functools import lru_cache
import ast,json,re,sys
from packing_parser import WordFunction
from parent_rule_analysis import parse_rows,at

FULL=(1<<512)-1
MOD=2305843009213693951
INPUTS=tuple(sum(1<<r for r in range(512) if (r>>j)&1) for j in range(9))
LOOKUP=re.compile(r'lookupWord\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+\(?\s*(\w+)\s*\)?')

def rot(n,k):
    k%=512
    return n if k==0 else ((n>>k)|(n<<(512-k)))&FULL

@lru_cache(maxsize=None)
def swap_word(value,code):
    i=code&15;j=code>>4
    a=INPUTS[i] if i<9 else 0;b=INPUTS[j] if j<9 else 0
    yes=a&(FULL^b);no=b&(FULL^a)
    delta=max(0,(1<<j)-(1<<i))%512
    return (yes&rot(value,delta)) | (no&rot(value,(-delta)%512)) | ((FULL^(yes|no))&value)

def key_word(value):
    n=value%MOD
    return n*(n+971)%MOD

def chunks(n):
    xs=[]
    while n:
        xs.append(hex(n&((1<<8192)-1)));n>>=8192
    return xs or ['0x0']

def run(path):
    source,defs,forests,rows=parse_rows(path)
    unary='codeDecor' in defs['decodeBank']
    wiredef=re.sub(r'\s+','',defs['wiresOf'])
    clipping='and_all' if 'if511<g.maskthen' in wiredef else 'and01' if 'ifg.mask=1023then' in wiredef else 'none'
    source_inputs=re.findall(r'0x[0-9a-fA-F]+',defs['inputs'])
    assert tuple(map(lambda x:int(x,16),source_inputs))==INPUTS, 'nonstandard input tables'
    bylevel={(r['forest'],r['level']):r for r in rows}
    auto_lists={}
    forest_fields={}
    for f in forests:
        fm=re.search(r',\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*⟩',defs[f])
        if fm is None:continue
        forest_fields[f]={'columns':fm.group(1),'autos':fm.group(2),'levels':fm.group(3),'index':fm.group(4)}
        name=fm.group(2)
        if name not in defs:continue
        body=defs[name].split(':=',1)[1].strip()
        begin=body.index('[');end=body.rindex(']')+1
        auto_lists[f]=tuple(tuple(x) for x in ast.literal_eval(body[begin:end]))
    @lru_cache(maxsize=None)
    def state(f,level,index):
        row=bylevel[f,level];mask=row['mask'];node=row['nodes'][index]
        bank=[v for j,v in enumerate(INPUTS) if(mask>>j)&1]
        if (clipping=='and_all' and mask>511) or (clipping=='and01' and mask==1023):
            j=(1 if mask==1023 else 2 if mask==1535 else 3) if clipping=='and_all' else 1
            a=bank[0] if bank else 0;b=bank[j] if j<len(bank) else 0
            dom=FULL^(a&b);bank=[v&dom for v in bank]
        for d in range(row['depth']):
            code=(node['ops']>>(10*d))&1023;i=code&15;j=(code>>4)&15;op=(code>>8)&3
            a=bank[i] if i<len(bank) else 0;b=bank[j] if j<len(bank) else 0
            if unary:v=FULL^a if op==2 else a|b if op==1 else a&b
            else:v=a&b if op==0 else a|b if op==1 else a&(FULL^b) if op==2 else (FULL^a)&b
            bank.append(v)
        return tuple(v for i,v in enumerate(bank) if(node['live']>>i)&1)
    @lru_cache(maxsize=None)
    def linked(f,level,index,permutation):
        values=state(f,level,index)
        # linkedSet uses reverse(perm) followed by foldr, hence original order here.
        for code in auto_lists[f][permutation]:
            values=tuple(swap_word(v,code) for v in values)
        return values
    @lru_cache(maxsize=None)
    def actual_key(f,level,index,permutation):
        return sum(key_word(v) for v in linked(f,level,index,permutation))
    tables=[];totals=Counter();seen_locations=set()
    for f in forests:
        index_name=forest_fields.get(f,{}).get('index',f+'index')
        if index_name not in defs:continue
        body=defs[index_name]
        for branch in re.finditer(r'\|\s*(\d+)\s*=>\s*(lookupWord[^\n]+)',body):
            level=int(branch.group(1));call=LOOKUP.search(branch.group(2))
            if not call:continue
            nb,slots,sw,vw,iw,pw=map(int,call.groups()[:6]);data_name=call.group(7)
            location=(f,level,data_name)
            if location in seen_locations:continue
            seen_locations.add(location)
            word=WordFunction(defs[data_name]);prev=bylevel.get((f,level-1));auto=auto_lists.get(f,())
            def old_lookup(h):
                bucket=h%nb;shift=at(word,bucket*sw,sw);r=(h//nb+shift)%slots
                value=at(word,nb*sw+r*vw,vw)
                if value>>(iw+pw) != (h//(nb*slots))%16:return None
                return value&((1<<iw)-1),(value>>iw)&((1<<pw)-1)
            candidates=set()
            for slot in range(slots):
                value=at(word,nb*sw+slot*vw,vw)
                candidates.add((value&((1<<iw)-1),(value>>iw)&((1<<pw)-1)))
            def valid(pair):return prev is not None and pair[0]<prev['count'] and pair[1]<len(auto)
            valid_pairs=[pair for pair in candidates if valid(pair)]
            records={};stats=Counter()
            for pair in valid_pairs:
                key=actual_key(f,level-1,*pair);mapped=old_lookup(key)
                if mapped is None:stats['lookup_none']+=1;continue
                if not valid(mapped):stats['lookup_invalid']+=1;continue
                mapped_key=actual_key(f,level-1,*mapped)
                if mapped_key!=key:stats['lookup_key_mismatch']+=1;continue
                if pair!=mapped:stats['equivalent_pair_redirect']+=1
                previous=records.get(key)
                if previous is not None and previous!=mapped:raise ValueError('nonfunctional original lookup')
                records[key]=mapped
            ordered=[(key,*pair) for key,pair in sorted(records.items())]
            for key,i,p in ordered:assert old_lookup(key)==(i,p)
            oldchars=sum(len(h) for h in re.findall(r'0x[0-9a-fA-F]+',defs[data_name]))
            packed=sum((i|(p<<iw))<<(j*(iw+pw)) for j,(_,i,p) in enumerate(ordered))
            entry={'forest':f,'mask':forests[f],'level':level,'previousLevel':level-1,'indexDefinition':index_name,
                   'dataName':data_name,'lookupCall':call.group(0),'params':[nb,slots,sw,vw,iw,pw],
                   'nodeWidth':iw,'permWidth':pw,'pairWidth':iw+pw,'recordCount':len(ordered),
                   'dataHexchunks':chunks(packed),'records':ordered,
                   'decodedPairs':len(candidates),'validPairs':len(valid_pairs),'stats':dict(stats),
                   'oldHexChars':oldchars,'newHexChars':sum(map(len,chunks(packed))),
                   'unaryNegationOps':unary,'clipping':clipping}
            tables.append(entry)
            totals.update({'tables':1,'decodedPairs':len(candidates),'validPairs':len(valid_pairs),'records':len(ordered),
                           'oldHexChars':oldchars,'newHexChars':entry['newHexChars'],**stats})
    all_occurrences=len(LOOKUP.findall(source));totals['lookupWordOccurrences']=all_occurrences
    return {'module':Path(path).stem,'summary':dict(totals),'tables':tables}

if __name__=='__main__':
    for arg in sys.argv[1:]:
        result=run(arg);out=Path('/tmp/oec/pequalnp-pilot-61')/(Path(arg).stem+'-hash-records.json')
        out.write_text(json.dumps(result,separators=(',',':')))
        print(result['module'],result['summary'],'output',out)
