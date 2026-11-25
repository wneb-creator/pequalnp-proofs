from pathlib import Path
HERE=Path(__file__).resolve().parent
s=(HERE/'search_feature_essential_suppressed_archive.cpp').read_text()
helper='''
int critical_junk_count(const Circuit& c){
 auto full=values(c);array<bool,N+G> used{};used[N+G-1]=true;
 for(int k=G-1;k>=0;k--)if(used[N+k])used[c[k].a]=used[c[k].b]=true;
 int count=0;
 for(int k=0;k<G;k++){
  auto g=c[k];if(!used[N+k]||g.op!=0||g.a==g.b)continue;
  bool dirty=false;for(int w=0;w<W;w++)dirty|=(full[N+k][w]&~target[w]&~full[N+G-1][w])!=0;
  if(!dirty)continue;
  auto zero=full;zero[N+k]={};
  for(int j=k+1;j<G;j++){auto h=c[j];for(int w=0;w<W;w++)zero[N+j][w]=h.op?(zero[h.a][w]|zero[h.b][w]):(zero[h.a][w]&zero[h.b][w]);}
  int lost=0;for(int w=0;w<W;w++)lost+=popcount(target[w]&full[N+G-1][w]&~zero[N+G-1][w]);
  if(lost<2)continue;
  Circuit left=c,right=c;left[k]={1,g.a,g.a};right[k]={1,g.b,g.b};
  if(values(left)[N+G-1]==full[N+G-1][w]){};
 }
 return count;
}
'''
helper=helper.replace('if(values(left)[N+G-1]==full[N+G-1][w]){};','if(values(left)[N+G-1]==full[N+G-1]||values(right)[N+G-1]==full[N+G-1])continue;\n  count++;')
s=s.replace('\npair<int,int> errors(',helper+'\npair<int,int> errors(',1)
s=s.replace('4*(mixed>0)+2*(wr>0)','4*(critical_junk_count(c)>=2)+2*(wr>0)')
s=s.replace('auto suppressed=essential_suppressed_dirty_witness(pool[i]);f<<','auto suppressed=essential_suppressed_dirty_witness(pool[i]);int critical_count=critical_junk_count(pool[i]);f<<')
s=s.replace('<<mx<<",\\\"essential_suppressed_dirty','<<mx<<",\\\"critical_junk_count\\\":"<<critical_count<<",\\\"essential_suppressed_dirty')
needle='if(have_suppressed)dump(current,prefix+"-suppressed-best.json");'
warm='''
  bool have_critical=critical_junk_count(current)>=2;int best_critical=have_critical?wrong:100000;Circuit critical_champion=current;
  if(have_critical)dump(current,prefix+"-critical-best.json");
  for(int first=1;first<min(3,int(seeds.size()));first++){
   Circuit warm=seed(first);auto output=values(warm)[N+G-1];auto e=errors(output);
   if(e.first||singletons(output)||!accept_shape(warm))continue;
   if(e.second==0){dump(warm,prefix+"-solution.json");cout<<"SOLUTION in retained warm champion"<<endl;return 0;}
   if(e.second<global_best){global_best=e.second;champion=warm;}
   if(essential_suppressed_dirty_witness(warm).first&&e.second<best_suppressed){have_suppressed=true;best_suppressed=e.second;suppressed_champion=warm;dump(warm,prefix+"-suppressed-best.json");}
   if(critical_junk_count(warm)>=2&&e.second<best_critical){have_critical=true;best_critical=e.second;critical_champion=warm;dump(warm,prefix+"-critical-best.json");}
  }
  cout<<"WARM CHAMPIONS ordinary "<<global_best<<" essential "<<best_suppressed<<" critical "<<best_critical<<endl;
'''
assert needle in s;s=s.replace(needle,needle+warm)
needle='int optimum=initial_errors.second,ties=0,neutral_ties=0;'
insert='''if(initial_errors.second<best_critical&&critical_junk_count(current)>=2){have_critical=true;best_critical=initial_errors.second;critical_champion=current;dump(current,prefix+"-critical-best.json");cout<<"CRITICAL JUNK BEST false "<<best_critical<<" sweep "<<sweeps<<endl;}
   '''
assert needle in s;s=s.replace(needle,insert+needle)
needle='if(wrong<global_best){global_best=wrong;champion=current;'
insert='''if(wrong<best_critical&&critical_junk_count(current)>=2){have_critical=true;best_critical=wrong;critical_champion=current;dump(current,prefix+"-critical-best.json");cout<<"CRITICAL JUNK BEST false "<<best_critical<<" sweep "<<sweeps<<endl;}
   '''
assert needle in s;s=s.replace(needle,insert+needle)
s=s.replace('if(ri(2))current=have_suppressed&&ri(2)?suppressed_champion:champion;','if(ri(2))current=have_critical&&ri(3)==0?critical_champion:(have_suppressed&&ri(2)?suppressed_champion:champion);')
needle='if(duration==-4){'
insert='''if(duration==-5){ofstream out(prefix+"-critical-fixtures.json");out<<"[\\n";for(size_t i=0;i<seeds.size();i++){
   assert(seeds[i].size()<=G);Circuit c;int count=0;for(auto g:seeds[i])c[count++]=g;while(count<G){int previous=N+count-1;c[count++]={1,previous,previous};}
   out<<"{\\\"index\\\":"<<i<<",\\\"critical_junk_count\\\":"<<critical_junk_count(c)<<"}"<<(i+1<seeds.size()?",":"")<<"\\n";
  }out<<"]\\n";cout<<"Wrote critical-junk fixtures "<<seeds.size()<<endl;return 0;}
 '''
assert needle in s;s=s.replace(needle,insert+needle)
(HERE/'search_feature_three_champions.cpp').write_text(s)
