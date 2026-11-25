#define main existingMain
#include "full_variable66_plus.cpp"
#undef main
#include "neutral_care_full.hpp"
int main(int argc, char** argv) {
 if(argc!=2)return 2;
 char command[]="control", seconds[]="-1", seed[]="205690";
 char* args[]={command,argv[1],seconds,seed};
 int result=existingMain(4,args);if(result)return result;
 std::mt19937 rng(205690);
 for(auto gs:nonlinearSeeds){
  Net c=pad(gs);
  for(int j=0;j<100;j++){
   neutralCare(c,rng);
   if(!valid(c))return 3;
   eval(c);if(lastRaw)return 4;
   auto packed=pad(compact(c));eval(packed);if(lastRaw)return 5;
   if(lastLive<=63){show(c,"HIT",j,0);return 0;}
  }
 }
 std::ifstream file(argv[1]);std::vector<int> rows;int row;while(file>>row)rows.push_back(row);
 Net c=pad(nonlinearSeeds[0]);
 for(int j=0;j<1000;j++){
  neutralCare(c,rng);
  if(scalarErrors(c,rows))return 7;
 }
 std::cerr<<"PASS10500 all-row neutral replacements and1000 scalar differential controls; calls="<<neutralCalls<<" options="<<neutralOptions<<" moves="<<neutralMoves<<std::endl;
 return 0;
}
