#!/usr/bin/env python3
"""Replace untrusted perfect-hash hints with sorted compact pair hints.

Certificate state membership checks remain unchanged. JSON is generated against
the original module by hash_records.py, independently of any Packing codec.
"""
import argparse
import json
import re
from pathlib import Path
from packing_parser import definitions

HELPERS = '''
def sortedIndexKey (g : Forest) (k iw code : Nat) : Nat :=
  let perm := (g.autos[code >>> iw]?).getD []
  keySet ((stateSet g k (code &&& ((1 <<< iw)-1))).map
    (movedWord (perm.map swapRows).reverse))
def sortedSeek (get key : Nat → Nat) (target : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let code := get mid
      let value := key code
      if target == value then some code
      else if target < value then sortedSeek get key target fuel lo mid
      else sortedSeek get key target fuel (mid+1) hi
    else none
def sortedLookup (g : Forest) (k count iw pw : Nat) (data : Nat → Nat)
    (h : Nat) : Option (Nat × Nat) :=
  let get := fun i => packedAt data (i*(iw+pw)) (iw+pw)
  (sortedSeek get (sortedIndexKey g k iw) h (Nat.log2 (count+1)+1) 0 count).map
    (fun code => (code &&& ((1 <<< iw)-1), code >>> iw))
'''

def word_function(chunks, left=0, right=None):
    if right is None: right = len(chunks)
    if right-left == 1: return chunks[left]
    mid = (left+right)//2
    return f'if i < {mid} then ({word_function(chunks,left,mid)}) else ({word_function(chunks,mid,right)})'

def transform(source, records):
    decls = definitions(source)
    tables = records['tables']
    edits = {}
    by_index = {}
    by_data = {}
    for t in tables:
        by_index.setdefault(t['indexDefinition'], []).append(t)
        chunks = t['dataHexchunks'] or ['0']
        new = f"def {t['dataName']} (i : Nat) : Nat := {word_function(chunks)}\n"
        old = by_data.setdefault(t['dataName'],new)
        assert old == new, ('different data layout',t['dataName'])
    for name,new in by_data.items(): edits[decls[name]] = new
    for index, group in by_index.items():
        forest = group[0]['forest']
        assert all(t['forest']==forest for t in group)
        base = forest+'SortedBase'
        base_decl = re.sub(r'^def\s+'+re.escape(forest)+r'\b', 'def '+base, decls[forest])
        base_decl, count = re.subn(r',\s*'+re.escape(index)+r'\s*⟩', ',fun _ _ => none⟩',base_decl)
        assert count==1, ('forest index constructor',forest)
        index_decl = decls[index]
        for t in group:
            new_call = f"sortedLookup {base} {t['previousLevel']} {t['recordCount']} {t['nodeWidth']} {t['permWidth']} {t['dataName']}"
            assert index_decl.count(t['lookupCall'])==1, ('lookup occurrence',t['lookupCall'])
            index_decl = index_decl.replace(t['lookupCall'],new_call)
        edits[decls[index]] = base_decl+index_decl
    edits[decls['stateSet']] = decls['stateSet']+HELPERS
    for old,new in edits.items():
        assert source.count(old)==1, ('declaration occurrence',old[:100])
        source=source.replace(old,new)
    return source

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path)
    parser.add_argument('records',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    old=args.source.read_text()
    new=transform(old,json.loads(args.records.read_text()))
    args.output.write_text(new)
    print(json.dumps({'source':str(args.source),'output':str(args.output),'oldBytes':len(old.encode()),'newBytes':len(new.encode()),'savedBytes':len(old.encode())-len(new.encode())}))

if __name__=='__main__':main()
