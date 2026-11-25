from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
starts=list(re.finditer(r'^(?:def|lemma|structure|inductive|abbrev|namespace|end|open|variable|set_option|noncomputable)\b',s,re.M))
blocks={}
for i,m in enumerate(starts):
 block=s[m.start():starts[i+1].start() if i+1<len(starts) else len(s)]
 n=re.match(r"(?:def|structure)\s+([\w']+)",block)
 if n:blocks[n.group(1)]=block.strip()
blocks['main']='''def main (args : List String) : IO Unit := do
  let projections := if args.contains "all" then grpSix ++ extendedSeeds
    else if args.contains "pair" then grpSix ++ tg0 ++ grp5
    else grpSix ++ tg0
  let before ← IO.monoMsNow
  IO.println s!"START {args} projections={projections.length}"
  (← IO.getStdout).flush
  if args.contains "regress" then
    for e in [(15,1),(23,4),(15,2),(23,5),(64,10)] do
      let result := okE [] (pr extendedSeeds e.1) e
      IO.println s!"REGRESSION {e} {result}"
      (← IO.getStdout).flush
  else
    let result := if args.contains "root13" then okE [] projections (0,13)
      else if args.contains "root14" then okE [] projections (0,14)
      else !chk [] projections 0 13 1 FF 1
    let after ← IO.monoMsNow
    IO.println s!"RESULT {args} {result} elapsed_ms={after-before}"
    (← IO.getStdout).flush
'''
needed={'main'}
while True:
 new=needed | {token for name in needed for token in re.findall(r"[\w']+",blocks[name]) if token in blocks}
 if new==needed:break
 needed=new
out='import Std\n\nnamespace NativeEngine\n\n'
out+='\n\n'.join(block for name,block in blocks.items() if name in needed and name!='main')
out+='\n\nend NativeEngine\n\nopen NativeEngine\n\n'+blocks['main']+'\n'
out=out.replace('ℕ','Nat')
Path(sys.argv[2]).write_text(out)
print('reachable declarations',len(needed),'bytes',len(out.encode()))
