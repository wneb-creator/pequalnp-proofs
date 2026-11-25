#include <ctime>
#define main existingMain
#include "full_variable70_undominated.cpp"
#undef main
void emitControl(const Net& c,int record){
  eval(c);classifyStratum(c);auto gs=compact(c);
  std::cout<<"{\"record\":"<<record<<",\"raw\":"<<lastRaw<<",\"violations\":"<<lastViolations<<",\"nonread\":"<<lastNonread<<",\"shared\":"<<lastShared<<",\"nested\":"<<lastNested<<",\"dominated\":"<<lastDominated<<",\"output\":"<<INPUTS+gs.size()-1<<",\"gates\":[";
  for(int j=0;j<(int)gs.size();++j){if(j)std::cout<<',';auto g=gs[j];std::cout<<'['<<g.op<<','<<g.a<<','<<g.b<<']';}
  std::cout<<"]}"<<std::endl;
}
int main(int argc,char**argv){
  if(argc!=2)return 2;
  char command[]="control",seconds[]="-1",seed[]="205671";
  char*args[]={command,argv[1],seconds,seed};
  int result=existingMain(4,args);if(result)return result;
  std::mt19937 rng(205671);int eligible=0,nested=0;std::vector<int>eligibleIDs;
  for(int j=0;j<(int)nonlinearSeeds.size();++j){
    Net c=pad(nonlinearSeeds[j]);emitControl(c,j);
    if(inStratum()){++eligible;nested+=lastNested>0;eligibleIDs.push_back(j);}
  }
  if(eligible!=572 || nested!=104)return 3;
  Net high{};for(auto&g:high)g={1,0,0};
  high[0]={1,0,1};high[1]={1,13,14};high[2]={0,26,27};
  high[64]={0,28,0};high[65]={0,28,13};high[66]={1,90,91};high[69]={1,92,92};
  emitControl(high,10000);if(lastShared!=1 || lastNested!=0)return 4;
  Net barrier=high;
  barrier[64]={0,28,2};barrier[65]={1,90,0};barrier[66]={0,91,13};barrier[67]={0,28,14};barrier[69]={1,92,93};
  emitControl(barrier,10001);if(lastShared!=0)return 5;
  auto copyLiteral=[&](bool absorption){
    std::vector<Gate> gs;
    if(absorption){gs.push_back({1,13,14});gs.push_back({0,13,26});}
    else gs.push_back({0,13,13});
    int prefix=gs.size(),alias=INPUTS+prefix-1;
    auto map=[&](int w){return w==13?alias:(w<INPUTS?w:w+prefix);};
    for(auto g:nonlinearSeeds.back())gs.push_back({g.op,map(g.a),map(g.b)});
    return pad(gs);
  };
  Net copied=copyLiteral(false);emitControl(copied,11000);
  if(lastRaw||lastViolations||!lastNonread||!lastShared||!lastDominated||inStratum())return 6;
  Net absorbed=copyLiteral(true);emitControl(absorbed,11001);
  if(lastRaw||lastViolations||!lastNonread||!lastShared||!lastDominated||inStratum())return 7;
  std::vector<Gate> extra;std::vector<int> mapping(INPUTS+nonlinearSeeds[182].size());
  std::iota(mapping.begin(),mapping.begin()+INPUTS,0);
  for(int j=0;j<(int)nonlinearSeeds[182].size();++j){
    auto g=nonlinearSeeds[182][j];Gate mapped{g.op,mapping[g.a],mapping[g.b]};
    if(j==2)extra.push_back(mapped);
    mapping[INPUTS+j]=INPUTS+extra.size();extra.push_back(mapped);
  }
  Net deadDuplicate=pad(extra);emitControl(deadDuplicate,11002);
  if(!inStratum()||lastDominated)return 8;
  std::cerr<<"PASS literal-copy, absorption-copy rejection and inactive-duplicate acceptance"<<std::endl;
  Net c=pad(nonlinearSeeds[0]);
  for(int j=0;j<1000;++j){
    if(j%50==0)c=scatterSpareSlots(pad(nonlinearSeeds[rng()%nonlinearSeeds.size()]),rng);
    Net next=c;mutate(next,rng);if(valid(next))c=next;
    emitControl(c,20000+j);
  }
  std::cerr<<"PASS755 seed classes,572 eligible/104 nested; high-bit frontier and zero-positive AND barrier controls;1000 mutant metric records"<<std::endl;
  auto evalWithoutRefinement=[&](const Net& net){
    for(int j=0;j<GATES;++j){auto g=net[j];for(int k=0;k<words;++k)val[(INPUTS+j)*words+k]=g.op?(val[g.a*words+k]|val[g.b*words+k]):(val[g.a*words+k]&val[g.b*words+k]);}
    lastRaw=0;for(int k=0;k<words;++k)lastRaw+=std::popcount((val[(WIRES-1)*words+k]^target[k])&masks[k]);
    lastLive=activeCount(net);classifyStratumCore(net);
  };
  volatile int sink=0;const int rounds=10000;
  auto started=std::clock();
  for(int j=0;j<rounds;++j){auto net=pad(nonlinearSeeds[eligibleIDs[j%eligibleIDs.size()]]);evalWithoutRefinement(net);sink=sink+lastShared;}
  double before=double(std::clock()-started)/CLOCKS_PER_SEC;started=std::clock();
  for(int j=0;j<rounds;++j){auto net=pad(nonlinearSeeds[eligibleIDs[j%eligibleIDs.size()]]);eval(net);sink=sink+lastShared;if(!inStratum())return 9;}
  double after=double(std::clock()-started)/CLOCKS_PER_SEC;
  std::cerr<<"BENCH evaluations="<<rounds<<" core_cpu_seconds="<<before<<" refined_cpu_seconds="<<after<<" ratio="<<after/before<<" sink="<<sink<<std::endl;
  return 0;
}
