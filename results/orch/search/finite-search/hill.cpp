#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
struct G {int op,a,b;};
constexpr int N=6,K=9;
using C=std::array<G,K>;
uint64_t input[N],target=0,critical=0;
std::mt19937_64 rng(4871);
int score(const C& c, int weight){
 uint64_t w[N+K];int dx[N+K],dy[N+K];
 for(int i=0;i<N;i++){w[i]=input[i];dx[i]=(i==1);dy[i]=(i==0);}
 for(int j=0;j<K;j++){auto [op,a,b]=c[j];int z=N+j;
 if(op==0){w[z]=w[a]|w[b];dx[z]=dx[a]|dx[b];dy[z]=dy[a]|dy[b];}
 else {w[z]=w[a]&w[b];dx[z]=(((w[a]>>1)&1)&dx[b])|(dx[a]&((w[b]>>1)&1));dy[z]=(((w[a]>>2)&1)&dy[b])|(dy[a]&((w[b]>>2)&1));}}
 return std::popcount((w[N+K-1]^target)&critical)*weight+dx[N+K-1]+dy[N+K-1];}
int main(int argc,char**argv){
 int secs=argc>1?atoi(argv[1]):120;
 int edges[][2]={{0,1},{0,5},{2,1},{2,3},{4,3},{4,5}};
 auto fn=[&](int s){for(auto&e:edges)if((s>>e[0]&1)&&(s>>e[1]&1))return true;return false;};
 for(int s=0;s<(1<<N);s++){for(int i=0;i<N;i++)if(s>>i&1)input[i]|=uint64_t(1)<<s;if(fn(s))target|=uint64_t(1)<<s;}
 for(auto&e:edges)critical|=uint64_t(1)<<((1<<e[0])|(1<<e[1]));
 for(int s=0;s<(1<<N);s++)if(!fn(s)){bool max=true;for(int i=0;i<N;i++)if(!(s>>i&1)&&!fn(s|(1<<i)))max=false;if(max)critical|=uint64_t(1)<<s;}
 C seed={G{0,1,5},G{1,0,6},G{0,1,3},G{1,2,8},G{0,3,5},G{1,4,10},G{0,7,9},G{0,11,12},G{0,11,13}};
 auto start=std::chrono::steady_clock::now();uint64_t iters=0;int best=1000;
 std::uniform_real_distribution<double> unif(0,1);
 for(int run=0;;run++){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>secs)break;
  C c=seed;int weight=run%3+1;
  if(run%3==0)for(int j=0;j<K;j++){c[j]={int(rng()%2),int(rng()%(N+j)),int(rng()%(N+j))};if(c[j].a==c[j].b)c[j].b=(c[j].b+1)%(N+j);}
  int cur=score(c,weight);
  for(int step=0;step<200000;step++){
   int j=rng()%K;G old=c[j];int mut=rng()%3;if(mut==0)c[j].op^=1;else if(mut==1)c[j].a=rng()%(N+j);else c[j].b=rng()%(N+j);
   if(c[j].a==c[j].b){c[j]=old;continue;}
   int next=score(c,weight);double temp=0.12+1.2*(1-double(step)/200000);
   if(next<=cur||unif(rng)<exp((cur-next)/temp))cur=next;else c[j]=old;
   iters++;
   if(cur==0){std::cout<<"FOUND run="<<run<<" iters="<<iters<<"\n";for(auto g:c)std::cout<<g.op<<" "<<g.a<<" "<<g.b<<"\n";return 0;}
   if(cur<best){best=cur;std::cout<<"best="<<best<<" run="<<run<<" iters="<<iters<<std::endl;}
  }
 }
 std::cout<<"NO WITNESS iters="<<iters<<" best="<<best<<"\n";
}
