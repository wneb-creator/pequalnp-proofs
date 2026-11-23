from pathlib import Path
import re

root = Path('/tmp/oec/pequalnp-pilot-14')
source = (root / 'toolchain/CheckedCompressed1007.lean').read_text()
start = source.index('def frontierData :')
end = source.index('def tableData :', start)
counts_text = source[source.index('def frontierCount :'):start]
counts = {(int(k), int(t)): int(n) for k,t,n in re.findall(r'\| (\d+), (\d+) => (\d+)', counts_text)}
entries = re.findall(r'\| (\d+), (\d+) => (0x[0-9a-f]+)', source[start:end])
raws = [153, 219, 267, 309, 323, 376, 442, 519]
packed_entries = []
for ks,ts,hs in entries:
    k,t,h = int(ks),int(ts),int(hs,16)
    width = 8+10*(12-k)
    n = k+1-t
    packed = 0
    for i in range(counts[k,t]):
        row = (h >> (10*n*i)) & ((1 << (10*n))-1)
        ids = []
        while row:
            ids.append(row & 1023)
            row >>= 10
        assert ids == sorted(ids)
        mask = sum(1 << j for j,x in enumerate(raws) if x in ids)
        extra = [x for x in ids if x not in raws]
        assert len(extra) <= 12-k
        code = mask + sum(x << (8+10*j) for j,x in enumerate(extra))
        decoded = sorted([x for j,x in enumerate(raws) if code & (1 << j)] +
                         [(code >> (8+10*j)) & 1023 for j in range(12-k)
                          if (code >> (8+10*j)) & 1023])
        assert decoded == ids
        packed |= code << (width*i)
    packed_entries.append(f'  | {k}, {t} => {hex(packed)}')

helper = '''def frontierRawIds : List Nat := [153,219,267,309,323,376,442,519]

def frontierIds : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, v => if v = 0 then [] else (v &&& 1023) :: frontierIds n (v >>> 10)

def insertFrontier (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertFrontier a bs

def sortFrontier : List Nat → List Nat
  | [] => []
  | a :: xs => insertFrontier a (sortFrontier xs)

def frontierCodes : Nat → Nat → Nat
'''+ '\n'.join(packed_entries) + '''
  | _, _ => 0

def frontierRead (k t i : Nat) : List Nat :=
  let width := 8 + 10*(12-k)
  let code := (frontierCodes k t >>> (width*i)) &&& (2^width-1)
  let rs := (List.range 8).filterMap fun j =>
    if code.testBit j then some (frontierRawIds.getD j 0) else none
  sortFrontier (rs ++ frontierIds (12-k) (code >>> 8))

def frontierState (k t i : Nat) : List Sig :=
  (frontierRead k t i).map readWire

'''
candidate = source[:start] + helper + source[end:]
(root / 'FrontierCompressed1007.lean').write_text(candidate)
(root / 'FrontierCompressedBlock.lean').write_text(helper)
olddef = source[start:source.index('def frontierState',start)].replace('def frontierData', 'def oldFrontierData')
checks = []
for ks,ts,_ in entries:
    k,t=int(ks),int(ts)
    checks.append(f'''set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
example : ∀ i : Fin {counts[k,t]}, frontierRead {k} {t} i.val =
    frontierIds ({k}+1-{t}) ((oldFrontierData {k} {t} >>> (10*({k}+1-{t})*i.val)) &&&
      (2^(10*({k}+1-{t}))-1)) := by decide +kernel
''')
test = 'import Mathlib.Tactic\n\nnamespace FrontierPackingTest\n\n'+olddef+helper[:helper.index('def frontierState')]+ '\n'.join(checks)+'\nend FrontierPackingTest\n'
(root / 'FrontierPackingTest.lean').write_text(test)
print('candidate bytes',len(candidate.encode()),'saved',len(source.encode())-len(candidate.encode()))
print('all',sum(counts.values()),'rows independently decoded exactly in Python; Lean equality checks pending')
