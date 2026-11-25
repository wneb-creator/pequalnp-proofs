#define main pg3_block_search_main
#include "block.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=2)return 2;std::ifstream f(argv[1]);uint32_t m;
 for(int j=0;j<52;++j){f>>m;edges[j]={std::countr_zero(m&((1<<13)-1)),std::countr_zero(m>>13)};}
 rngstate=138258308;
 for(int i=0;i<1054;++i){uint64_t removed;
  if(i==0)removed=0;else if(i==1)removed=POS;else if(i<54)removed=uint64_t(1)<<(i-2);
  else {removed=rnd()&POS;if(i%3==0)removed&=rnd();if(i%3==1)removed|=rnd()&POS;}
  std::cout<<removed<<" "<<matching(removed)<<"\n";
 }
}
