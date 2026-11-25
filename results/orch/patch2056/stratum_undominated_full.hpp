int lastViolations=0,lastNonread=0,lastShared=0,lastNested=0,lastDominated=0;
void classifyStratumCore(const Net& c){
  auto live=activeMask(c);
  std::array<bool,WIRES> clean{};
  std::array<U,WIRES> positive{},point{},line{},joint{};
  for(int w=0;w<WIRES;++w){
    clean[w]=true;
    for(int k=0;k<words;++k)if(val[w*words+k]&negative[k])clean[w]=false;
    positive[w]=val[w*words]&target[0];
  }
  for(int i=0;i<INPUTS;++i){
    if(i<INPUTS/2)point[i]=positive[i];else line[i]=positive[i];
  }
  lastViolations=0;
  for(int j=0;j<GATES;++j){
    auto g=c[j];int w=INPUTS+j;
    if(g.op){point[w]=point[g.a]|point[g.b];line[w]=line[g.a]|line[g.b];joint[w]=joint[g.a]|joint[g.b];}
    else joint[w]=(point[g.a]&line[g.b])|(line[g.a]&point[g.b]);
    if(live[j])lastViolations+=g.op?(clean[g.a]!=clean[g.b]):(clean[g.a]||clean[g.b]);
  }
  lastNonread=std::popcount(target[0]&~joint.back());
  // Frontier bits cover all70 gate indices; every AND ends an OR-only path.
  std::array<std::array<U,2>,WIRES> frontier{};
  for(int j=GATES-1;j>=0;--j)if(live[j]){
    auto g=c[j];
    if(g.op){
      for(int k=0;k<2;++k){frontier[g.a][k]|=frontier[INPUTS+j][k];frontier[g.b][k]|=frontier[INPUTS+j][k];}
    }else if(positive[INPUTS+j]){
      U bit=U(1)<<(j%64);frontier[g.a][j/64]|=bit;frontier[g.b][j/64]|=bit;
    }
  }
  std::array<U,2> dirtyBits{};
  for(int j=0;j<GATES;++j)if(live[j]&&!c[j].op&&!clean[INPUTS+j]&&positive[INPUTS+j])dirtyBits[j/64]|=U(1)<<(j%64);
  lastShared=lastNested=0;
  for(int j=0;j<GATES;++j)if((dirtyBits[j/64]>>(j%64))&1){
    auto f=frontier[INPUTS+j];
    lastShared+=std::popcount(f[0])+std::popcount(f[1])>=2;
    lastNested+=bool((f[0]&dirtyBits[0])|(f[1]&dirtyBits[1]));
  }
}
// Only an already-live earlier wire may dominate: activating a dead subgraph
// could increase the reachable gate count used by this exact-state search.
bool hasEarlierLiveDominance(const Net& c){
  auto live=activeMask(c);
  for(int j=0;j<GATES;++j)if(live[j]){
    int w=INPUTS+j;U p=val[w*words]&target[0];
    for(int a=0;a<w;++a)if(a<INPUTS||live[a-INPUTS]){
      if(p&~val[a*words])continue;
      bool dominates=true;
      for(int k=0;k<words;++k)if(val[a*words+k]&negative[k]&~val[w*words+k]){dominates=false;break;}
      if(dominates)return true;
    }
  }
  return false;
}
void classifyStratum(const Net& c){
  classifyStratumCore(c);
  lastDominated=0;
  // The expensive refinement is needed only after the cheap class filters pass.
  if(lastRaw==0&&lastViolations==0&&lastNonread>0&&lastShared>0)
    lastDominated=hasEarlierLiveDominance(c);
}
bool inStratum(){return lastRaw==0&&lastViolations==0&&lastNonread>0&&lastShared>0&&!lastDominated;}

