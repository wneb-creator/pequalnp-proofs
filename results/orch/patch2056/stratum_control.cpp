#define main existingMain
#include "full_variable70_stratum.cpp"
#undef main
void emitControl(const Net& c,int record){
  eval(c);classifyStratum(c);auto gs=compact(c);
  std::cout<<"{\"record\":"<<record<<",\"raw\":"<<lastRaw<<",\"violations\":"<<lastViolations<<",\"nonread\":"<<lastNonread<<",\"shared\":"<<lastShared<<",\"nested\":"<<lastNested<<",\"output\":"<<INPUTS+gs.size()-1<<",\"gates\":[";
  for(int j=0;j<(int)gs.size();++j){if(j)std::cout<<',';auto g=gs[j];std::cout<<'['<<g.op<<','<<g.a<<','<<g.b<<']';}
  std::cout<<"]}"<<std::endl;
}
int main(int argc,char**argv){
  if(argc!=2)return 2;
  char command[]="control",seconds[]="-1",seed[]="205671";
  char*args[]={command,argv[1],seconds,seed};
  int result=existingMain(4,args);if(result)return result;
  std::mt19937 rng(205671);int eligible=0,nested=0;
  for(int j=0;j<(int)nonlinearSeeds.size();++j){
    Net c=pad(nonlinearSeeds[j]);emitControl(c,j);
    if(inStratum()){++eligible;nested+=lastNested>0;}
  }
  if(eligible!=572 || nested!=104)return 3;
  Net high{};for(auto&g:high)g={1,0,0};
  high[0]={1,0,1};high[1]={1,13,14};high[2]={0,26,27};
  high[64]={0,28,0};high[65]={0,28,13};high[66]={1,90,91};high[69]={1,92,92};
  emitControl(high,10000);if(lastShared!=1 || lastNested!=0)return 4;
  Net barrier=high;
  barrier[64]={0,28,2};barrier[65]={1,90,0};barrier[66]={0,91,13};barrier[67]={0,28,14};barrier[69]={1,92,93};
  emitControl(barrier,10001);if(lastShared!=0)return 5;
  Net c=pad(nonlinearSeeds[0]);
  for(int j=0;j<1000;++j){
    if(j%50==0)c=scatterSpareSlots(pad(nonlinearSeeds[rng()%nonlinearSeeds.size()]),rng);
    Net next=c;mutate(next,rng);if(valid(next))c=next;
    emitControl(c,20000+j);
  }
  std::cerr<<"PASS755 seed classes,572 eligible/104 nested; high-bit frontier and zero-positive AND barrier controls;1000 mutant metric records"<<std::endl;
  return 0;
}
