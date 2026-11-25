#define main stochastic_main
#include "stochastic.cpp"
#undef main
int main(int argc,char**argv){
 int maxedits=argc>1?std::stoi(argv[1]):1;
 for(int x=0;x<1024;x++){for(int j=0;j<10;j++)if(x>>j&1)init[j][x/64]|=uint64_t(1)<<(x%64);bool y=false;for(auto [a,b]:edges)y|=(x>>a&1)&&(x>>b&1);if(y)target[x/64]|=uint64_t(1)<<(x%64);}
 std::ifstream in("/tmp/oec/pequalnp-pilot-98/search/best-98.txt");std::string s;getline(in,s);Circuit base;int j;for(int i=0;i<19;i++)in>>j>>base.g[i].op>>base.g[i].a>>base.g[i].b;
 auto t0=std::chrono::steady_clock::now();uint64_t steps=0;int best=eval(base);std::cout<<"baseline "<<best<<std::endl;
 for(int notsrc=0;notsrc<12;notsrc++)for(int g1=3;g1<19;g1++)for(int op1=0;op1<2;op1++)for(int a1=0;a1<10+g1;a1++){
  auto c=base;c.g[2]={2,notsrc,0};c.g[g1]={op1,a1,12};int e=eval(c);steps++;
  if(e<best){best=e;save(c,e,steps,"/tmp/oec/pequalnp-pilot-98/search/best-repair.txt");std::cout<<"best "<<e<<" steps "<<steps<<std::endl;if(!e)return 0;}
  if(maxedits<2)continue;
  for(int g2=0;g2<19;g2++)if(g2!=2&&g2!=g1)for(int op2=0;op2<2;op2++)for(int a2=0;a2<10+g2;a2++)for(int b2=a2;b2<10+g2;b2++){
   auto d=c;d.g[g2]={op2,a2,b2};e=eval(d);steps++;
   if(e<best){best=e;save(d,e,steps,"/tmp/oec/pequalnp-pilot-98/search/best-repair.txt");std::cout<<"best "<<e<<" steps "<<steps<<std::endl;if(!e)return 0;}
  }
 }
 std::cout<<"END best "<<best<<" steps "<<steps<<" elapsed "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<std::endl;
}
