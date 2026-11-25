#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
import random
import time

from factor_partition import evaluate_graphs, full_check

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--seconds',type=float,default=5)
    parser.add_argument('--passes',type=int,default=1)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    representatives = data['representatives']
    rng = random.Random(70)
    started = time.monotonic()
    best = best_nontrivial = None
    scored = []
    done = False
    for repetition in range(args.passes):
        for index,pair in enumerate(representatives):
            if time.monotonic()-started > args.seconds:
                done = True
                break
            result,nontrivial = evaluate_graphs(pair['h'],pair['k'],rng)
            scored.append({'pass':repetition,'orbit':index,'size':result['size'],
                           'nontrivial_size':None if nontrivial is None else nontrivial['size']})
            for candidate in [result,nontrivial]:
                if candidate is not None:
                    candidate['orbit'] = index
                    candidate['additions'] = [pair['x'],pair['y']]
            if best is None or result['size'] < best['size']:
                best = result
                print(json.dumps({'event':'best','size':best['size'],'orbit':index,
                                  'shadow_edges':best['shadow_edge_count'],'seconds':time.monotonic()-started}),flush=True)
            if nontrivial is not None and (best_nontrivial is None or nontrivial['size'] < best_nontrivial['size']):
                best_nontrivial = nontrivial
                print(json.dumps({'event':'nontrivial_best','size':nontrivial['size'],'orbit':index,
                                  'shadow_edges':nontrivial['shadow_edge_count'],'seconds':time.monotonic()-started}),flush=True)
            if best['size'] <= 26:
                done = True
                break
        if done:
            break
    full_check(best)
    if best_nontrivial:
        full_check(best_nontrivial)
    output = {'duration_seconds':time.monotonic()-started,'scored':scored,'best':best,
              'best_nontrivial':best_nontrivial,'total_orbits':len(representatives)}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'event':'done','seconds':output['duration_seconds'],'evaluations':len(scored),
                      'best':best['size'],'best_nontrivial':None if best_nontrivial is None else best_nontrivial['size']}),flush=True)

if __name__ == '__main__':
    main()
