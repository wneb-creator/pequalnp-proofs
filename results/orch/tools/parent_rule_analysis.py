from pathlib import Path
from collections import defaultdict,Counter
import re,json,sys
from packing_parser import parse_module

def at(word,pos,length):
    if not length:return 0
    i,shift=divmod(pos,8192)
    value=word(i)>>shift
    if shift+length>8192:value|=word(i+1)<<(8192-shift)
    return value&((1<<length)-1)

def parse_rows(path):
    source,defs,forests,rows=parse_module(path)
    for row in rows:
        n=row['count'];d=row['depth'];cw=row['cw'];ow=row['offw'];lw=row['lw'];word=row['word']
        row['level']=int(re.search(r'l(\d+)$',row['name']).group(1))
        sw=11*d+row['raw_length'];start=row['prefix_bits'];payload=start+n*ow
        row['nodes']=[]
        for i in range(n):
            record=at(word,i*sw,sw);ops=record&((1<<(10*d))-1);live=record>>(10*d)
            pos=payload+at(word,start+i*ow,ow);nr=at(word,pos,5);pos+=5+lw
            rules=tuple((at(word,pos+j*(cw+d),cw),at(word,pos+j*(cw+d)+cw,d)) for j in range(nr))
            row['nodes'].append({'ops':ops,'live':live,'rules':rules})
    return source,defs,forests,rows

def analyze(path):
    source,defs,forests,rows=parse_rows(path)
    bylevel={(r['forest'],r['level']):r for r in rows}
    totals=Counter();details=[]
    for row in sorted(rows,key=lambda r:r['depth']):
        n=row['count'];d=row['depth'];cw=row['cw'];prev=bylevel.get((row['forest'],row['level']+1))
        pmap=defaultdict(list)
        if prev is not None:
            for j,node in enumerate(prev['nodes']):pmap[node['ops']].append(j)
        counts=Counter()
        for i,node in enumerate(row['nodes']):
            R=set(node['rules']);parents=pmap[node['ops']&((1<<(10*max(0,d-1)))-1)] if d else []
            counts['full_rule_pairs']+=len(node['rules']);counts['full_rule_bits']+=5+len(node['rules'])*(cw+d)
            cols=set(c for c,p in R)
            counts['column_only_bits']+=5+len(cols)*cw
            counts['column_enumerated_candidates']+=len(cols)*(1<<d)
            counts['nodes']+=1
            if parents:
                first=parents[0];P=set(prev['nodes'][first]['rules'])
                counts['first_common_pairs']+=len(R&P);counts['first_symdiff_pairs']+=len(R^P)
                counts['first_subset_delta_bits']+=5+len(prev['nodes'][first]['rules'])+len(R-P)*(cw+d)
                lifted=P|{(c,p|(1<<(d-1))) for c,p in P}
                counts['first_lift_delta_bits']+=5+2*len(prev['nodes'][first]['rules'])+len(R-lifted)*(cw+d)
                choice=min(parents,key=lambda j:(len(R-prev['nodes'][j]['inherited']),len(prev['nodes'][j]['inherited'])))
                inherited=prev['nodes'][choice]['inherited'];new=R-inherited
                counts['ancestor_new_pairs']+=len(new)
                counts['ancestor_delta_bits']+=5+len(new)*(cw+d)
                node['parent']=choice;node['new_rules']=sorted(new);node['inherited']=inherited|R
            else:
                counts['first_subset_delta_bits']+=5+len(R)*(cw+d)
                counts['first_lift_delta_bits']+=5+len(R)*(cw+d)
                counts['ancestor_new_pairs']+=len(R);counts['ancestor_delta_bits']+=5+len(R)*(cw+d)
                node['parent']=None;node['new_rules']=sorted(R);node['inherited']=R
            counts['inherited_candidates']+=len(node['inherited'])
            counts['max_inherited_candidates']=max(counts['max_inherited_candidates'],len(node['inherited']))
        totals.update({k:v for k,v in counts.items() if not k.startswith('max_')})
        totals['max_inherited_candidates']=max(totals['max_inherited_candidates'],counts['max_inherited_candidates'])
        details.append({'name':row['name'],'summary':dict(counts),'nodes':[{'parent':x['parent'],'new_rules':x['new_rules']} for x in row['nodes']]})
    return dict(totals),details

if __name__=='__main__':
    for arg in sys.argv[1:]:
        totals,details=analyze(arg)
        output=Path('/tmp/oec/pequalnp-pilot-61')/(Path(arg).stem+'-rule-delta.json')
        output.write_text(json.dumps({'totals':totals,'levels':details},separators=(',',':')))
        print(Path(arg).stem,json.dumps(totals))
