#!/usr/bin/env python3
from pathlib import Path
from collections import defaultdict,Counter
import json
from parent_rule_analysis import parse_rows

ROOT=Path('/workspace/pequalnp-proofs')
OUT=Path('/tmp/oec/pequalnp-pilot-61')

def analyze(case):
    _,defs,_,rows=parse_rows(ROOT/f'lean/PEqualNP/Outside/L_meta_{case}.lean')
    unary='codeDecor' in defs
    by={(r['forest'],r['level']):r for r in rows}
    old={r['name']:r for r in json.loads((OUT/f'L_meta_{case}-parent-rules.json').read_text())}
    summaries=[];total=Counter()
    for r in sorted(rows,key=lambda r:r['depth']):
        d,cw,n,raw=r['depth'],r['cw'],r['count'],r['raw_length'];previous=by.get((r['forest'],r['level']+1))
        parent_count=previous['count'] if previous else 0;pw=parent_count.bit_length() if d else 0;iw=max(0,(n-1).bit_length())
        parents=defaultdict(list)
        if previous:
            for j,x in enumerate(previous['nodes']):parents[x['ops']].append(j)
        offsets=[];rule_offsets={};payload_size=0;exceptions=[];nodes=[]
        for i,x in enumerate(r['nodes']):
            R=set(x['rules']);candidates=[];compatible=[];drops=0
            if d:
                prefix=x['ops']&((1<<(10*(d-1)))-1);code=(x['ops']>>(10*(d-1)))&1023;a=code&15;b=(code>>4)&15;op=code>>8
                candidates=parents[prefix];low=x['live']&((1<<(raw+d-1))-1)
                used=(1<<a) if unary and op==2 else (1<<a)|(1<<b)
                if x['live']>>(raw+d-1)==1:
                    compatible=[j for j in candidates if (previous['nodes'][j]['live']&used)==used and previous['nodes'][j]['live']|low==previous['nodes'][j]['live'] and (previous['nodes'][j]['live']^low)&~used==0]
            choices=compatible or candidates
            if choices:
                parent=min(choices,key=lambda j:(len(R-previous['nodes'][j]['live_inherited']),len(previous['nodes'][j]['live_inherited'])))
                inherited=previous['nodes'][parent]['live_inherited'];new=R-inherited
                if compatible:
                    live=previous['nodes'][parent]['live'];drops=((live>>a)&1 and not((x['live']>>a)&1))|(((live>>b)&1 and not((x['live']>>b)&1))<<1)
            else:parent=parent_count;inherited=set();new=R
            is_exception=(d>0 and not compatible) or (d==0 and x['live']!=(1<<raw)-1)
            if is_exception:exceptions.append(i)
            x['live_inherited']=inherited|R
            new_rules=tuple(sorted(new))
            if new_rules not in rule_offsets:
                rule_offsets[new_rules]=payload_size;payload_size+=5+len(new_rules)*(cw+d)
            offsets.append(rule_offsets[new_rules]);nodes.append({'parent':parent,'drops':int(drops),'exception':is_exception,'new_rules':new_rules})
        ow=max(offsets,default=0).bit_length();width=pw+12 if d else 0
        new_bits=n*width+n*ow+payload_size+len(exceptions)*(iw+10*d+raw+d)
        old_row=old[r['name']];old_bits=old_row['totalBits']+old_row['exceptionCount']*(iw+10*d)
        stats={'name':r['name'],'nodes':n,'depth':d,'old_bits':old_bits,'new_bits':new_bits,'saving_bits':old_bits-new_bits,'new_exceptions':len(exceptions),'old_exceptions':old_row['exceptionCount'],'old_payload_bits':old_row['payloadBits'],'new_payload_bits':payload_size,'old_offset_bits':n*old_row['offsetWidth'],'new_offset_bits':n*ow,'nodes_data':nodes}
        summaries.append(stats)
        total.update({k:v for k,v in stats.items() if isinstance(v,int)})
    return {'case':case,'summary':dict(total),'levels':summaries}

def main():
    results=[analyze(i) for i in [2444,4338,1674,5120,1676,1677,1678]]
    totals=Counter()
    for result in results:totals.update(result['summary'])
    report={'totals':dict(totals),'cases':results}
    (OUT/'parent-live-codec-analysis.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'totals':dict(totals),'cases':[{'case':r['case'],'summary':r['summary']} for r in results]},indent=2))

if __name__=='__main__':main()
