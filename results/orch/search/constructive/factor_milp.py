#!/usr/bin/env python3
"""Time-bounded joint rectangle selection; objective is only a scoring proxy."""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

from factor_partition import EDGES, TARGET, candidates, full_check, rectangle, shadow_count, synthesize

def select(h,k,alpha,seconds):
    options = candidates(h,k)
    masks = sorted({(side,c[side]) for c in options for side in range(2) if c[side].bit_count()>1})
    mask_index = {mask:len(options)+i for i,mask in enumerate(masks)}
    flag_start = len(options)+len(masks)
    nv = flag_start+21
    objective = np.zeros(nv)
    objective[:len(options)] = 2
    for (side,mask),i in mask_index.items():
        objective[i] = 1+alpha*(mask.bit_count()-2)
    objective[flag_start:] = .001
    rows = []
    lower = []
    upper = []
    def constraint(entries,lo,hi):
        rows.append(entries)
        lower.append(lo)
        upper.append(hi)
    universe = h | k << 49
    while universe:
        bit = universe & -universe
        constraint({i:1 for i,c in enumerate(options) if c[3]&bit},1,np.inf)
        universe ^= bit
    for i,(a,b,flags,cover) in enumerate(options):
        for side,mask in enumerate((a,b)):
            if mask.bit_count()>1:
                constraint({i:1,mask_index[side,mask]:-1},-np.inf,0)
        if flags == 3:
            edges = rectangle(a,b)
            for j,(u,v) in enumerate(EDGES):
                if edges >> (7*u+v-7) & 1:
                    constraint({i:1,flag_start+j:-1},-np.inf,0)
    constraint({flag_start+j:1 for j in range(21)},-np.inf,18)
    ii,jj,vv = [],[],[]
    for i,row in enumerate(rows):
        for j,v in row.items():
            ii.append(i)
            jj.append(j)
            vv.append(v)
    matrix = coo_matrix((vv,(ii,jj)),shape=(len(rows),nv)).tocsc()
    result = milp(objective,integrality=np.ones(nv),bounds=Bounds(0,1),
                  constraints=LinearConstraint(matrix,np.asarray(lower),np.asarray(upper)),
                  options={'time_limit':seconds,'mip_rel_gap':0.02,'presolve':True})
    meta = {'solver_status':int(result.status),'message':str(result.message),
            'proxy_objective':None if result.fun is None else float(result.fun)}
    if result.x is None:
        return None,meta
    chosen = [c for i,c in enumerate(options) if result.x[i]>.5]
    covered = 0
    common = 0
    for a,b,flags,cover in chosen:
        covered |= cover
        if flags == 3:
            common |= rectangle(a,b)
    assert covered & (h | k << 49) == (h | k << 49)
    assert common.bit_count() <= 18
    circuit = synthesize(chosen)
    circuit['shadow_edge_count'] = shadow_count(circuit)
    circuit['factor_edge_counts'] = [h.bit_count(),k.bit_count()]
    return circuit,meta

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--seconds',type=float,default=90)
    parser.add_argument('--per-case',type=float,default=1)
    args = parser.parse_args()
    representatives = json.loads(args.input.read_text())['representatives']
    started = time.monotonic()
    best = best_nontrivial = None
    records = []
    stop = False
    for alpha in (.5,0,1):
        for index,pair in enumerate(representatives):
            remaining = args.seconds-(time.monotonic()-started)
            if remaining<=0:
                stop = True
                break
            result,meta = select(pair['h'],pair['k'],alpha,min(args.per_case,remaining))
            meta.update({'orbit':index,'alpha':alpha,'size':None if result is None else result['size']})
            records.append(meta)
            if result is None:
                continue
            result['orbit'] = index
            result['alpha'] = alpha
            result['additions'] = [pair['x'],pair['y']]
            if best is None or result['size']<best['size']:
                best = result
                print(json.dumps({'event':'best','size':result['size'],'shadow':result['shadow_edge_count'],
                                  'orbit':index,'seconds':time.monotonic()-started}),flush=True)
            if result['shadow_edge_count']<=18 and (best_nontrivial is None or result['size']<best_nontrivial['size']):
                best_nontrivial = result
            if result['size']<=26:
                stop = True
                break
        if stop:
            break
    if best:
        full_check(best)
    if best_nontrivial:
        full_check(best_nontrivial)
    output = {'duration_seconds':time.monotonic()-started,'records':records,'best':best,
              'best_nontrivial':best_nontrivial}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'event':'done','seconds':output['duration_seconds'],'cases':len(records),
                      'best':None if best is None else best['size'],
                      'best_nontrivial':None if best_nontrivial is None else best_nontrivial['size']}),flush=True)

if __name__ == '__main__':
    main()
