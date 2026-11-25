import argparse
import hashlib
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('source', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--prefix', type=Path)
p.add_argument('--report', type=Path)
a = p.parse_args()
s = a.source.read_text()
original = s
changes = []

def decl(name, replacement):
    global s
    pat = re.compile(r'^(?:structure|def) ' + re.escape(name) + r'\b[\s\S]*?(?=^(?:def|theorem|lemma|structure|abbrev|end|set_option)\b)', re.M)
    m = pat.search(s)
    assert m, name
    changes.append({'name': name, 'old': m.group(), 'new': replacement + '\n\n'})
    s = s[:m.start()] + replacement + '\n\n' + s[m.end():]

def rooms(name, free=False):
    params = '(S : Finset Sig) (T H : Sig)' if free else '(S : Finset Sig) (T : Sig)'
    implicit = '{S T H}' if free else '{S T}'
    app = name + (' S T H' if free else ' S T')
    total = '(bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n' if free else '∃ v, owns v p n'
    return f'''abbrev {name} {params} :=
  {{ owns : Sig → Row → Row → Prop //
    (∀ p n, bit p T=true → bit n T=false → {total}) ∧
    (∀ {{v p n}}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false) ∧
    (∀ {{v w p n}}, owns v p n → owns w p n → v=w) ∧
    (∀ {{v p n p' n'}}, owns v p n' → owns v p' n → owns v p n) }}
abbrev {name}.owns {implicit} (D : {app}) := D.val
abbrev {name}.total {implicit} (D : {app}) := D.property.1
abbrev {name}.valid {implicit} (D : {app}) :
    ∀ {{v p n}}, D.owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false := D.property.2.1
abbrev {name}.unique {implicit} (D : {app}) :
    ∀ {{v w p n}}, D.owns v p n → D.owns w p n → v=w := D.property.2.2.1
abbrev {name}.rect {implicit} (D : {app}) :
    ∀ {{v p n p' n'}}, D.owns v p n' → D.owns v p' n → D.owns v p n := D.property.2.2.2
def {name}.mk {implicit} (owns : Sig → Row → Row → Prop)
    (total : ∀ p n, bit p T=true → bit n T=false → {total})
    (valid : ∀ {{v p n}}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false)
    (unique : ∀ {{v w p n}}, owns v p n → owns w p n → v=w)
    (rect : ∀ {{v p n p' n'}}, owns v p n' → owns v p' n → owns v p n) : {app} :=
  ⟨owns,total,valid,unique,rect⟩'''

decl('KWRooms', rooms('KWRooms'))
decl('FreeRooms', rooms('FreeRooms', True))
decl('SingleFactor', '''abbrev SingleFactor (S : Finset Sig) (T : Sig) :=
  Σ inner : Finset Sig, Σ outer : Finset Sig, Σ pivot : Sig,
    { rooms : KWRooms inner pivot × FreeRooms outer T pivot //
      inner ∪ outer = S ∧ Disjoint inner outer }
abbrev SingleFactor.inner {S T} (F : SingleFactor S T) := F.1
abbrev SingleFactor.outer {S T} (F : SingleFactor S T) := F.2.1
abbrev SingleFactor.pivot {S T} (F : SingleFactor S T) := F.2.2.1
abbrev SingleFactor.cover {S T} (F : SingleFactor S T) := F.2.2.2.property.1
abbrev SingleFactor.apart {S T} (F : SingleFactor S T) := F.2.2.2.property.2
abbrev SingleFactor.inside {S T} (F : SingleFactor S T) := F.2.2.2.val.1
abbrev SingleFactor.outside {S T} (F : SingleFactor S T) := F.2.2.2.val.2
def SingleFactor.mk {S T} (inner outer : Finset Sig) (pivot : Sig)
    (cover : inner ∪ outer = S) (apart : Disjoint inner outer)
    (inside : KWRooms inner pivot) (outside : FreeRooms outer T pivot) : SingleFactor S T :=
  ⟨inner,outer,pivot,⟨inside,outside⟩,cover,apart⟩''')
decl('PanelProof', '''abbrev PanelProof := Σ arity : Nat, { tags : List PanelTag // panelClosed arity tags }
abbrev PanelProof.arity (pc : PanelProof) := pc.1
abbrev PanelProof.tags (pc : PanelProof) := pc.2.val
abbrev PanelProof.closed (pc : PanelProof) : panelClosed pc.arity pc.tags := pc.2.property''')
decl('kwLeaf', '''def kwLeaf (T : Sig) : KWRooms {T} T :=
  KWRooms.mk (fun v p n => v=T ∧ bit p T=true ∧ bit n T=false)
    (fun p n hp hn => ⟨T,rfl,hp,hn⟩)
    (by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩)
    (by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm)
    (by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩)''')
decl('freeFrom', '''def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h :=
  FreeRooms.mk D.owns (fun p n hp hn => Or.inr (D.total p n hp hn))
    D.valid D.unique D.rect''')
decl('freeHide', '''def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h :=
  FreeRooms.mk (fun v p n => v≠h ∧ D.owns v p n)
    (by
      intro p n hp hn
      rcases D.total p n hp hn with yes | ⟨v,hv⟩
      · exact Or.inl yes
      · by_cases eq : v=h
        · exact Or.inl (eq ▸ (D.valid hv).2)
        · exact Or.inr ⟨v,eq,hv⟩)
    (by
      rintro v p n ⟨ne,hv⟩
      exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩)
    (fun h1 h2 => D.unique h1.2 h2.2)
    (fun a b => ⟨a.1,D.rect a.2 b.2⟩)''')
decl('factorOfTree', '''def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T :=
  SingleFactor.mk S ∅ T (by simp) (by simp) D
    (FreeRooms.mk (fun _ _ _ => False)
      (fun p n hp hn => Or.inl ⟨hp,hn⟩)
      (fun h => h.elim) (fun h _ => h.elim) (fun h _ => h.elim))''')

fork = '''  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }'''
for name in ['KWRooms','FreeRooms']:
    replacement = f'''  refine {name}.mk (fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)) ?_ ?_ ?_ ?_'''
    assert fork in s
    s = s.replace(fork, replacement, 1)
    changes.append({'name':name+' fork constructor','old':fork,'new':replacement})

repls = [
('exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩',
 'exact SingleFactor.mk _ F.outer F.pivot eq apart (kwFork hd ha hb (by simp [z]) old) F.outside'),
('exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,\n      freeFork hd ha hb (by simp [z]) old⟩',
 'exact SingleFactor.mk F.inner _ F.pivot ((Finset.union_comm _ _).trans eq) apart.symm F.inside\n      (freeFork hd ha hb (by simp [z]) old)'),
('refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1\'⟩',
 'refine SingleFactor.mk {a} ((insert a (insert b U)).erase a) a ?_ ?_ (kwLeaf a) (freeHide H1\')')]
for old,new in repls:
    assert s.count(old)==1, old
    s=s.replace(old,new)
    changes.append({'name':'SingleFactor constructor','old':old,'new':new})

assert not re.search(r'^(?:structure|inductive|instance)\b',s,re.M)
assert re.findall(r'0x[0-9a-fA-F]+',s)==re.findall(r'0x[0-9a-fA-F]+',original)
assert s[s.index('theorem PEqualNP.Outside.L_meta_670 :'):]==original[original.index('theorem PEqualNP.Outside.L_meta_670 :'):]
a.output.write_text(s)
if a.prefix:
    marker='def g15d3'
    assert marker in s
    # All generic KW and panel proofs occur before the first forest's packed data.
    prefix=s[:s.index(marker)]+'\nend PEqualNP.Outside.L_meta_670\n'
    a.prefix.write_text(prefix)
if a.report:
    a.report.write_text(json.dumps({'source':str(a.source),'output':str(a.output),'source_sha256':hashlib.sha256(original.encode()).hexdigest(),'output_sha256':hashlib.sha256(s.encode()).hexdigest(),'source_bytes':len(original.encode()),'output_bytes':len(s.encode()),'hex_literals_unchanged':True,'final_theorem_unchanged':True,'changes':changes},indent=2))
print(json.dumps({'output_bytes':len(s.encode()),'output_sha256':hashlib.sha256(s.encode()).hexdigest(),'changes':len(changes)}))
