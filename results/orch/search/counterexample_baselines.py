import argparse
import json
from pathlib import Path
from counterexample_q3_repair import LINES,NINPUT

def analyze(circuit):
    patterns=[1<<i for i in range(NINPUT)]
    patterns += [((1<<13)-1)^sum(1<<p for p in LINES[l]) for l in range(13)]
    patterns += [(((1<<13)-1)<<13)^sum(1<<(13+l) for l in range(13) if p in LINES[l]) for p in range(13)]
    words=[sum(1<<t for t,mask in enumerate(patterns) if mask>>i&1) for i in range(NINPUT)]
    for op,a,b in circuit:words.append(words[a]&words[b] if op else words[a]|words[b])
    missing_rows=[l for l in range(13) if not any(not(w>>(26+l)&1) and all(w>>p&1 for p in LINES[l]) for w in words)]
    missing_columns=[p for p in range(13) if not any(not(w>>(39+p)&1) and all(w>>(13+l)&1 for l in range(13) if p in LINES[l]) for w in words)]
    row_pencil=any(all(p in LINES[l] for l in missing_rows) for p in range(13))
    column_line=any(all(p in LINES[l] for p in missing_columns) for l in range(13))
    return dict(missing_rows=missing_rows,missing_columns=missing_columns,row_pencil=row_pencil,
                column_line=column_line,violates_proposed_necessary_filter=min(len(missing_rows),len(missing_columns))<4 or row_pencil or column_line)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--log',required=True);ap.add_argument('--out',required=True);args=ap.parse_args()
    root=Path(args.root);reports=[]
    for line in Path(args.log).read_text().splitlines():
        try:r=json.loads(line)
        except json.JSONDecodeError:continue
        if r.get('status')!=10:continue
        d=json.loads((root/f'trial-{r["trial"]:04d}-round-{r["round"]}.json').read_text())
        report=dict(trial=r['trial'],round=r['round'],false_boundaries=r['false_positive_boundaries'],**analyze(d['circuit']))
        reports.append(report)
    Path(args.out).write_text(json.dumps(reports,indent=2)+'\n')
    print(json.dumps(dict(candidates=len(reports),violating=sum(r['violates_proposed_necessary_filter'] for r in reports),best=min(reports,key=lambda r:r['false_boundaries']) if reports else None)))

if __name__=='__main__':main()
