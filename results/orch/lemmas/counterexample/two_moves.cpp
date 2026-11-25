#define main stochastic_main
#include "search.cpp"
#undef main
int main(){
 for(int x=0;x<1024;++x){
  for(int a=0;a<10;++a)if(x>>a&1)wires[a][x/64]|=uint64_t(1)<<(x%64);
  bool f=false;for(auto [a,b]:edges)if((x>>a&1)&&(x>>b&1))f=true;
  if(f)target[x/64]|=uint64_t(1)<<(x%64);
 }
 Circuit base={{{1,7,1},{1,1,4},{1,8,0},{1,7,12},{0,5,13},{1,9,0},{1,4,2},{0,11,15},{1,1,9},{1,18,8},{0,6,19},{1,9,2},{0,10,21},{1,8,16},{0,3,23},{1,14,24},{1,25,22},{1,26,17},{1,27,20}}};
 uint64_t checked=0;int best=1024;Circuit champion{};
 for(int n=0;n<19;++n)for(int u=0;u<10+n;++u){
  Circuit c=base;c[n]={2,u,u};
  for(int g=0;g<19;++g)if(g!=n)for(int op=0;op<2;++op)for(int a=0;a<10+g;++a)for(int b=a;b<10+g;++b){
   c[g]={op,a,b};int value=score(c);++checked;
   if(value<best){best=value;champion=c;printf("checked %llu ",(unsigned long long)checked);print(c,value);}
   if(value==0)return 0;
   c[g]=base[g];
  }
 }
 printf("DONE checked=%llu best=%d\n",(unsigned long long)checked,best);print(champion,best);
}
