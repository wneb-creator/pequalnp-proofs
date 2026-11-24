#!/usr/bin/env python3
"""Peer semantic audit of retained S04 witnesses; no producer-file changes."""
import hashlib
import itertools
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'S04'
names=['selected-ancestry-birth-bound.md','selected-birth-subfamily-corollary.md',
       'filter_selected_birth_patterns_v3.py','selected-birth-patterns-v3.json']
files=[dict(path=str(SOURCE/n),sha256=hashlib.sha256((SOURCE/n).read_bytes()).hexdigest()) for n in names]
data=json.loads((SOURCE/'selected-birth-patterns-v3.json').read_text())
E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
N=[{v if u==x else u for u,v in E if x in(u,v)} for x in range(11)]
relations_checked=0;subfamilies_checked=0
for group in data['results']:
    assert group['input']=={0:258,1:800}[group['r']]
    assert (group['excluded'],group['remaining'])=={0:(99,159),1:(230,570)}[group['r']]
    assert group['excluded']==sum(row['excluded'] for row in group['families'])
    for row in group['families']:
        S=[{v for v in range(11) if s>>v&1} for s in row['supports']]
        owners=[next((v for v,n in enumerate(N) if s<=n),None) for s in S]
        assert owners==row['owners']
        H={e for e in E if any(not set(e)&s for s in S)}
        stars=[set() if o is None else {tuple(sorted((o,v))) for v in s} for s,o in zip(S,owners)]
        for case in row['relation_cases']:
            rel={tuple(p) for p in case['ancestry']};term={i for i in range(3) if not any(a==i for a,b in rel)}
            assert all(owners[a] is not None for a,b in rel)
            K=set(H)
            for i in set(range(3))-term:K|=stars[i]
            strict=bool(K) and all(owners[i] is None or not stars[i]<=K for i in term)
            assert sorted(term)==case['terminal'] and sorted(K)==[tuple(e) for e in case['forced_birth_edges']]
            assert strict==case['strict_guard'] and len(K)+len(term)+int(strict)==case['lower_bound']
            witness=case['subfamily_position_witness'];p=witness['positions']
            assert len(set(p))==3 and all(p[a]<p[b] for a,b in rel)
            checks=witness['subfamily_birth_bounds'];assert len(checks)==7
            for check in checks:
                chosen=set(check['chosen']);t={i for i in chosen if not any(a==i and b in chosen for a,b in rel)}
                required={e for e in E if any(not set(e)&S[i] for i in chosen)}
                for i in chosen-t:required|=stars[i]
                bonus=bool(required) and all(owners[i] is None or not stars[i]<=required for i in t)
                lower=len(required)+len(t)+int(bonus)
                last=max(p[i] for i in chosen)
                outside={i for i in range(3) if i not in chosen and p[i]<last and not any((i,j) in rel for j in chosen)}
                upper=last+1-len(outside)-int(any(a in outside and b in outside for a,b in rel))
                assert [tuple(e) for e in check['forced_edges']]==sorted(required)
                assert check['lower_bound']==lower and check['upper_bound']==upper and lower<=upper
                assert check['strict_guard']==bonus and check['terminals']==sorted(t)
                subfamilies_checked+=1
            assert case['newly_rejected']==(case['lower_bound']>17)
            relations_checked+=1
out=dict(verdict='PASS_MATHEMATICAL_PROOFS_SOURCE_REVIEW_AND_STORED_WITNESS_AUDIT',files=files,
    reviewer_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    relations_independently_rechecked=relations_checked,subfamily_unions_independently_rechecked=subfamilies_checked,
    mathematical_findings=[
      'Nonterminal firstAND forces the entire unique-owner star; edge sets must be unioned.',
      'Only selected ancestry maxima are deleted; other selected outputs remain ordinary core gates.',
      'NonemptyK plus at least one missing terminal-star edge is sufficient for strictness, and correctly guarded.',
      'Subfamily proof does not require that a subfamily itself be a minimal product; fullcover and incomparable supports suffice.',
      'Union upper bound subtracts only selected outputs outside every chosen cone and the one possible distinct outside firstAND.',
      'v3 code uses these exact guards, set unions, chronological inequalities and previous conservative owner/raw conventions.'],
    limitations=[
      'Stored successful relations and all seven union bounds independently recomputed; no second full absent-position census run by S01.',
      'Exhaustiveness follows reviewed finite loop structure and S04 separate recomputation; no new solver/Lean/global result.'],
    proposed_counts=[dict(r=0,excluded=99,remaining=159),dict(r=1,excluded=230,remaining=570)],
    solver_run=False,Lean_build=False)
(ROOT/'s04-selected-birth-peer-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('files','mathematical_findings','limitations')}))
