"""Decode the actual emitted Lean text and independently replay every core."""
import hashlib
import json
import re
from pathlib import Path
from replay_core import replay

ROOT = Path('results/orch9775')
DIRECTORY = ROOT/'search/compact-final'
MASKS = [127,245,314,432,541,792,1102,1290,1548,2087,2213,2338,4183,4309,4370,4757,
         5008,5190,5316,6151,6789,7174,7426,7812,8297,8417,8488,8713,9288,9992,10401,
         10656,12481,13504,14977,16256]
FACTS = [('live','vn'),('lab','vnv'),('res','nv'),('common','vv'),('gate','ee'),
         ('reader','ben'),('es','bev'),('avoid','vmn'),('see','vvmn'),('diff','nvv')]
SCHEMES = [('self','vn'),('earlier','vn'),('labCommon','vvn'),('someRes','v'),
           ('allRes','vn'),('exposure','vm'),('exactAt','vvm'),('avoidLive','vmn'),
           ('seeLive','vvmn'),('avoidNot','vvmn'),('seeLab','vvvmn'),('diffX','nvv'),
           ('diffC','nvv'),('adjacentCommon','vvv'),('resCommon','vvn'),
           ('residual','vvnn'),('readerAny','be'),('readerLive','ben'),
           ('readerLab','benvb'),('eqLab','beevb'),('gateEq','been'),
           ('pairedExact','vvvvm')]

def numbers(text):
    if not text.strip():
        return []
    return [int(x.strip(),0) for x in text.split(',')]

def decode_constructor(number, schema):
    tag=number%32
    assert tag<len(schema)
    name, kinds=schema[tag]
    fields=[]
    for i,kind in enumerate(kinds):
        x=(number>>(5+6*i))&63
        if kind=='v': x%=14
        elif kind=='e': x%=19
        elif kind=='b': x=(x==1)
        elif kind=='m': x=MASKS[x] if x<len(MASKS) else 0
        else: assert kind=='n'
        fields.append(x)
    assert number>>(5+6*len(kinds))==0
    return [name,*fields]

def digits(number,width,count):
    result=[]
    for _ in range(count):
        result.append(number%2**width)
        number//=2**width
    assert number==0
    return result

def exact(pattern,text):
    matches=list(re.finditer(pattern,text,re.S))
    assert len(matches)==1,(pattern,len(matches))
    return matches[0]

def parse_tree(lines,name,index=0):
    line=lines[index].strip()
    branch=re.fullmatch(r'if i < (\d+) then',line)
    if branch:
        left,index=parse_tree(lines,name,index+1)
        assert lines[index].strip()=='else'
        right,index=parse_tree(lines,name,index+1)
        return ('if',int(branch[1]),left,right),index
    leaf=re.fullmatch(r'table'+name+r'_(\d+)\.getD \(i%(\d+)\) 0',line)
    assert leaf,line
    return ('table',int(leaf[1]),int(leaf[2])),index+1

def lookup(tree,index,tables):
    if tree[0]=='if':
        return lookup(tree[2] if index<tree[1] else tree[3],index,tables)
    row=tables[tree[1]]
    return row[index%tree[2]] if index%tree[2]<len(row) else 0

def audit(summary):
    name=summary['name'];path=DIRECTORY/(name+'.lean');raw=path.read_bytes();text=raw.decode()
    corepath=path.with_suffix('.json');coreraw=corepath.read_bytes();data=json.loads(coreraw)
    assert data['I']==summary['I'] and data['k']==summary['k'] and data['no_exact']==summary['weak']
    assert data['k']==data['I'].bit_count()-(4 if data['no_exact'] else 3)
    factnums=numbers(exact(r'def a'+name+r' := \(\[(.*?)\] : List Nat\)\.toArray\.map readPackedFact',text)[1])
    scheme_match=exact(r'def r'+name+r' := \(\[(.*?)\] : List Nat\)\.map (readPackedBudget|readPackedScheme)',text)
    schemenums=numbers(scheme_match[1])
    assert scheme_match[2]==('readPackedBudget' if data['no_exact'] else 'readPackedScheme')
    assert [decode_constructor(x,FACTS) for x in factnums]==data['facts']
    assert [decode_constructor(x,SCHEMES) for x in schemenums]==data['schemes']
    if not data['no_exact']:
        assert all(s[0]!='pairedExact' for s in data['schemes'])
    tables={int(m[1]):numbers(m[2]) for m in re.finditer(r'def table'+name+r'_(\d+) : List Nat := \[(.*?)\]',text)}
    assert sorted(tables)==list(range(len(tables)))
    tree_text=exact(r'def encoded'+name+r' \(i : Nat\) : Nat :=\n(.*?)\ndef book'+name,text)[1]
    lines=tree_text.splitlines();tree,used=parse_tree(lines,name);assert used==len(lines)
    cw=int(exact(r'def book'+name+r' \(i : Nat\) : Clause := let n := encoded'+name+r' i; unpackLits (\d+) \(n%64\) \(n>>>6\)',text)[1])
    for index,clause in enumerate(data['book']):
        value=lookup(tree,index,tables)
        keys=digits(value>>6,cw,value%64)
        assert [[key//2,key%2==1] for key in keys]==clause
    base=data['base_count'];total=len(data['book'])
    initial=exact(r'theorem initialClauses'+name+r' : (inputsOKBudget|inputsOK) (\d+) (\d+) a'+name+r' r'+name+r' \(baseBook book'+name+r' (\d+)\)\.toList=true := by decide \+kernel',text)
    assert initial[1]==('inputsOKBudget' if data['no_exact'] else 'inputsOK')
    assert list(map(int,initial.group(2,3,4)))==[data['k'],data['I'],base]
    rowtables={int(m[1]):numbers(m[2]) for m in re.finditer(r'def rows'+name+r'_(\d+) : List Nat := \[(.*?)\]',text)}
    assert sorted(rowtables)==list(range(len(rowtables)))
    rows=[];offset=base;previous='hbase'
    for chunk,encoded in sorted(rowtables.items()):
        checked=exact(r'theorem rowsOk'+name+'_'+str(chunk)+r' : checkRows book'+name+r' (\d+) (\d+) rows'+name+'_'+str(chunk)+r'=true := by decide \+kernel',text)
        width,start=map(int,checked.group(1,2));assert start==offset
        for value in encoded:
            units=digits(value>>(9+width),width,value%512)
            last=(value>>9)%2**width
            rows.append(units+[last])
        offset+=len(encoded)
        assert f'have h{chunk} : ValidThrough v book{name} {offset} := rows_sound {previous} rows{name}_{chunk} rowsOk{name}_{chunk}' in text
        previous='h'+str(chunk)
    assert rows==data['rows'] and offset==total
    last=exact(r'def lastUnits'+name+r' := digits (\d+) (\d+) (0x[0-9a-f]+|\d+)',text)
    width,count=int(last[1]),int(last[2]);units=digits(int(last[3],0),width,count)
    conflict=exact(r'theorem conflict'+name+r' : checkReasons book'+name+r' (\d+) (\d+) lastUnits'+name+r' 0=true := by decide \+kernel',text)
    assert int(conflict[1])==total and units+[int(conflict[2])]==data['last_hints']
    if data['no_exact']:
        assert '(z : Bzero 14 D≤1) (bp : Bplus 14 D=10)' in text
        assert f'construct_layout_budget (k:={data["k"]})' in text
        bridge='book_start_budget'
    else:
        assert '(z : Bzero 14 D=0) (bp : Bplus 14 D=11)' in text
        assert f'construct_layout (k:={data["k"]})' in text
        bridge='book_start'
    assert f'(eq : mask {data["I"]}=ineligSet 14 D) : False := by' in text
    assert f'let v := truth Z a{name}' in text
    assert f'have hbase : ValidThrough v book{name} {base} := {bridge} Z h hc z eq _ _ _ _ initialClauses{name}' in text
    assert f'exact book_end {previous} _ _ conflict{name}' in text
    assert not re.search(r'\bsorry\b|\bnative_decide\b|^\s*axiom\b|_root_|"|@\[',text,re.M)
    result=replay(data)
    result.update(name=name,lean_path=str(path),lean_sha256=hashlib.sha256(raw).hexdigest(),
                  json_path=str(corepath),json_sha256=hashlib.sha256(coreraw).hexdigest(),
                  bytes=len(raw),packed_text_roundtrip=True,book_lookup_tree_checked=True,
                  exact_theorem_budget_checked=True)
    statuspath=DIRECTORY/'checks'/(name+'.result.json')
    if statuspath.exists():
        status=json.loads(statuspath.read_text())
        result['lean_check_record']=dict(exit_code=status['exit_code'],sha256=status['sha256'],
                                         matches_exact_source=status['sha256']==result['lean_sha256'])
    else:
        result['lean_check_record']=None
    return result

if __name__=='__main__':
    summaries=json.loads((DIRECTORY/'summary.json').read_text())
    assert len({s['name'] for s in summaries})==len(summaries)
    records=[]
    for summary in summaries:
        result=audit(summary);records.append(result)
        print(json.dumps(result),flush=True)
    report={'scope':'Independent packed-text roundtrip, scheme reconstruction, dictionary RUP replay; Lean status only for exact matching source hashes.',
            'payloads':len(records),'records':records}
    (ROOT/'review-rup/compact-final-independent-validation.json').write_text(json.dumps(report,indent=2)+'\n')
