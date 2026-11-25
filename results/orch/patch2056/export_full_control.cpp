#define main optimizer_main
#include "full_variable66_plus.cpp"
#undef main
int main(int argc,char**argv){int result=optimizer_main(argc,argv);if(result)return result;Net c=pad(nonlinearSeeds[0]);while(shrinkExact(c))c=pad(compact(c));show(c,"control",0,0);return 0;}
