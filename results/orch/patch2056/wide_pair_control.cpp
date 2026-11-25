#define main existingMain
#include "full_variable70_pair.cpp"
#undef main
int main(int argc, char** argv) {
 if(argc!=2)return 2;
 char command[]="control", seconds[]="-1", seed[]="205690";
 char* args[]={command,argv[1],seconds,seed};
 int result=existingMain(4,args);if(result)return result;
 std::mt19937 rng(205690);
 {
  Net c=pad(nonlinearSeeds.back());
  bool controlled=false;
  for(int j=0;j<GATES && !controlled;j++)if(c[j].op==1)
   for(int w:{c[j].a,c[j].b})if(w>=INPUTS && c[w-INPUTS].op==1){
    int h=w-INPUTS, other=c[j].a==w?c[j].b:c[j].a;
    int uses=0;for(auto g:c)uses+=(g.a==w)+(g.b==w);
    if(uses!=1 || other>=INPUTS+h)continue;
    Net explicitRewrite=c;
    auto inner=c[h];
    explicitRewrite[h]={1,inner.b,other};explicitRewrite[j]={1,inner.a,w};
    eval(explicitRewrite);if(lastRaw)return 11;
    if(!neutralPairCare(c,rng,j,h,0))return 12;
    if(c[j]==pad(nonlinearSeeds.back())[j] && c[h]==pad(nonlinearSeeds.back())[h])return 13;
    eval(c);if(lastRaw)return 14;
    controlled=true;break;
   }
  if(!controlled)return 15;
  std::cerr<<"PASS explicit OR reassociation and forced two-gate resynthesis positive controls"<<std::endl;
 }
 {
  Net big=pad(nonlinearSeeds.back());
  if(!expandBig(big,rng))return 18;
  eval(big);if(lastRaw || lastLive!=68)return 19;
  Net small=pad(nonlinearSeeds.back());
  if(!expandSmall(small,rng))return 20;
  eval(small);if(lastRaw || lastLive<65 || lastLive>66)return 21;
  std::cerr<<"PASS full baseline64-to-68 CNF and64-to-65/66 distributive expansions"<<std::endl;
 }
 for(auto gs:nonlinearSeeds){
  Net c=pad(gs);
  for(int j=0;j<5;j++){
   Net prior=c;
   neutralPairCare(c,rng);
   bool changedOp=false;for(int k=0;k<GATES;k++)changedOp|=prior[k].op!=c[k].op;
   if(changedOp)show(c,"operator-change",j,0);
   if(!valid(c))return 3;
   eval(c);if(lastRaw)return 4;
   auto packed=pad(compact(c));eval(packed);if(lastRaw)return 5;
   if(lastLive<=63){show(c,"HIT",j,0);return 0;}
  }
 }
 for(auto gs:nonlinearSeeds){
  Net c=pad(gs);
  for(int j=0;j<100;j++){
   auto shuffled=scatterSpareSlots(c,rng);
   if(compact(shuffled)!=compact(c))return 16;
   eval(shuffled);if(lastRaw)return 17;
   c=shuffled;
  }
 }
 std::cerr<<"PASS65100 spare-slot rebuilds preserve the compact DAG exactly"<<std::endl;
 std::ifstream file(argv[1]);std::vector<int> rows;int row;while(file>>row)rows.push_back(row);
 Net c=pad(nonlinearSeeds[0]);
 for(int j=0;j<100;j++){
  c=scatterSpareSlots(c,rng);
  neutralPairCare(c,rng);
  if(scalarErrors(c,rows))return 7;
 }
 std::cerr<<"PASS3255 all-row pair replacements and100 scalar differential controls; calls="<<pairCalls<<" options="<<pairOptions<<" moves="<<pairMoves<<" opchanging_options="<<pairOpChangingOptions<<std::endl;
 return 0;
}
