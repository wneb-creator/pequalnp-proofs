from pathlib import Path
import json,itertools,hashlib,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
job=Path(__file__).resolve().parent
D=[0,1,3,9]
rows=[]
for p in range(13):
 for d in D:rows.append((True,{p,13+(d-p)%13}))
for k in range(4):
 for xs in reversed(list(itertools.combinations(range(13),k))):
  s=set(xs);t={l for l in range(13) if all((p+l)%13 not in D for p in s)}
  rows.extend([(False,s|{13+l for l in t}),(False,t|{13+p for p in s})])
assert len(rows)==808 and sum(b for b,_ in rows)==52
words=[sum((1<<r) for r,(_,ones) in enumerate(rows) if i in ones) for i in range(26)]
header='''import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3773_aux.InputWords

open PEqualNP.GenericRejection

def D : Finset (Fin 13) := {0,1,3,9}
def disj (s : Finset (Fin 13)) :=
  Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p+l ∉ D
def edges := (List.finRange 13).flatMap fun p =>
  ([0,1,3,9] : List (Fin 13)).map fun d =>
    (true, incidenceInput {p} {d-p})
def small := (List.range 4).flatMap fun k =>
  ((List.finRange 13).sublistsLen k).map List.toFinset
def ordinary := small.flatMap fun s =>
  [(false, incidenceInput s (disj s)), (false, incidenceInput (disj s) s)]
def rows := edges ++ ordinary
def word (i : Fin 26) : ℕ :=
  (rows.map fun r => r.2.getD i.val false).foldr Nat.bit 0

def literals : List ℕ :=
  ['''+',\n   '.join(map(str,words))+''']

'''
lemmas=''
for i,n in enumerate(words):
 lemmas+=f'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nlemma word_{i} : word {i} = {n} := by decide +kernel\n\n'
tail='lemma word_eq (i : Fin 26) : word i = literals.getD i.val 0 := by\n  fin_cases i\n'+''.join('  · exact word_'+str(i)+'\n' for i in range(26))+'''
lemma words_eq : List.ofFn word = literals := by
  apply List.ext_getElem
  · simp [literals]
  · intro i hi hj
    have h : i < 26 := by simpa using hi
    simpa only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some] using word_eq ⟨i,h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma labels_eq : (rows.map Prod.fst).foldr Nat.bit 0 = 4503599627370495 := by
  decide +kernel

'''
end='end PEqualNP.Outside.L_meta_3773_aux.InputWords\n'
(job/'Meta3773InputWords.lean').write_text(header+lemmas+tail+end)
(job/'Meta3773InputWord0.lean').write_text(header+lemmas[:lemmas.index('set_option maxRecDepth',1)]+end)
data={'row_count':len(rows),'positive_count':52,'small_subset_order':'reverse lexicographic combinations within each cardinality0..3, exactly List.sublistsLen','words':words,'expected':(1<<52)-1}
(job/'meta3773-input-words.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'source_sha256':hashlib.sha256((header+lemmas+tail+end).encode()).hexdigest(),'rows':len(rows),'words':len(words)}))
