// Two-gate contextual resynthesis. The inner gate must have exactly one use.
long long pairCalls=0, pairOptions=0, pairMoves=0, pairOpChangingOptions=0;
bool neutralPairCare(Net& c, std::mt19937& rng, int fixedJ=-1, int fixedH=-1, int fixedBias=-1) {
  ++pairCalls;
  eval(c);
  if(lastRaw || words>MAXWORDS)return false;
  auto live=activeMask(c);
  std::array<int,WIRES> uses{};
  for(auto g:c){++uses[g.a];++uses[g.b];}
  std::vector<std::pair<int,int>> choices;
  for(int j=0;j<GATES;++j)if(live[j])
    for(int h:{c[j].a,c[j].b})
      if(h>=INPUTS && uses[h]==1)choices.push_back({j,h-INPUTS});
  if(choices.empty())return false;
  auto [j,h]=choices[rng()%choices.size()];
  if(fixedJ>=0){
    if(std::find(choices.begin(),choices.end(),std::pair{fixedJ,fixedH})==choices.end())std::abort();
    j=fixedJ;h=fixedH;
  }
  std::array<RV,WIRES> vals{};
  for(int i=0;i<WIRES;++i)for(int k=0;k<words;++k)vals[i][k]=val[i*words+k];
  RV full{};
  for(int k=0;k<words;++k)full[k]=masks[k];
  std::array<RV,2> outs;
  for(int b=0;b<2;++b){
    auto v=vals;v[INPUTS+j]=b?full:RV{};
    for(int z=j+1;z<GATES;++z)v[INPUTS+z]=rcomb(c[z].op,v[c[z].a],v[c[z].b]);
    outs[b]=v.back();
  }
  RV care{};
  for(int k=0;k<words;++k){
    care[k]=outs[0][k]^outs[1][k];
    if((outs[0][k]^target[k])&~care[k]&masks[k])return false;
  }
  Gate oldh=c[h],oldj=c[j],pickh=oldh,pickj=oldj;
  if(oldh.a>oldh.b)std::swap(oldh.a,oldh.b);
  if(oldj.a>oldj.b)std::swap(oldj.a,oldj.b);
  bool preferOpChange=fixedBias<0?rng()%2:fixedBias!=0;
  unsigned seen=0;
  for(int a=0;a<INPUTS+h;++a)for(int b=a;b<INPUTS+h;++b)for(int oi=0;oi<2;++oi){
    RV hv=rcomb(oi,vals[a],vals[b]);
    for(int cc=0;cc<INPUTS+j;++cc)if(cc!=INPUTS+h)for(int oo=0;oo<2;++oo){
      Gate gh{oi,a,b},gj{oo,std::min(INPUTS+h,cc),std::max(INPUTS+h,cc)};
      if(gh==oldh && gj==oldj)continue;
      bool opChanging=oi!=oldh.op || oo!=oldj.op;
      if(preferOpChange && !opChanging)continue;
      bool ok=true;
      for(int k=0;k<words;++k){
        U v=oo?hv[k]|vals[cc][k]:hv[k]&vals[cc][k];
        if((v^target[k])&care[k]){ok=false;break;}
      }
      if(!ok)continue;
      ++pairOptions;pairOpChangingOptions+=opChanging;
      if(rng()%++seen==0){pickh=gh;pickj=gj;}
    }
  }
  if(!seen)return false;
  Net next=c;next[h]=pickh;next[j]=pickj;
  if(!valid(next))std::abort();
  eval(next);
  if(lastRaw){std::cerr<<"ERROR neutral pair care contract failed"<<std::endl;std::abort();}
  c=next;++pairMoves;return true;
}
