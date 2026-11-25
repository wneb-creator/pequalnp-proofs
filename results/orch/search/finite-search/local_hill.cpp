#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
struct G{int op,a,b;};
std::mt19937_64 rng(281932);
int main(int argc,char**argv){
 std::ifstream in(argv[1]);int n,k,nr,c0,c1;uint64_t target;in>>n>>k>>nr>>c0>>c1>>target;
 std::vector<uint64_t> input(n);std::vector<int> idx(n),idy(n);for(int i=0;i<n;i++)in>>input[i]>>idx[i]>>idy[i];
 std::vector<G>seed(k);for(auto&g:seed)in>>g.op>>g.a>>g.b;if(!in){std::cerr<<"bad profile\n";return 2;}
 int secs=argc>2?atoi(argv[2]):120;
 auto score=[&](const std::vector<G>&c,int weight){
  uint64_t w[100];int dx[100],dy[100];for(int i=0;i<n;i++){w[i]=input[i];dx[i]=idx[i];dy[i]=idy[i];}
  for(int j=0;j<k;j++){auto[op,a,b]=c[j];int z=n+j;
   if(op==0){w[z]=w[a]|w[b];dx[z]=dx[a]|dx[b];dy[z]=dy[a]|dy[b];}
   else{w[z]=w[a]&w[b];dx[z]=(((w[a]>>c0)&1)&dx[b])|(dx[a]&((w[b]>>c0)&1));dy[z]=(((w[a]>>c1)&1)&dy[b])|(dy[a]&((w[b]>>c1)&1));}}
  return std::popcount(w[n+k-1]^target)*weight+dx[n+k-1]+dy[n+k-1];};
 auto start=std::chrono::steady_clock::now();uint64_t iters=0;int best=1000;std::uniform_real_distribution<double>unif(0,1);
 for(int run=0;;run++){
  if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>secs)break;
  auto c=seed;int weight=run%4+1;
  if(run%3==0)for(int j=0;j<k;j++){c[j]={int(rng()%2),int(rng()%(n+j)),int(rng()%(n+j))};if(c[j].a==c[j].b)c[j].b=(c[j].b+1)%(n+j);}
  int cur=score(c,weight);
  for(int step=0;step<200000;step++){
   int j=rng()%k;G old=c[j];int mut=rng()%3;if(mut==0)c[j].op^=1;else if(mut==1)c[j].a=rng()%(n+j);else c[j].b=rng()%(n+j);
   if(c[j].a==c[j].b){c[j]=old;continue;}
   int next=score(c,weight);double temp=0.1+1.3*(1-double(step)/200000);
   if(next<=cur||unif(rng)<exp((cur-next)/temp))cur=next;else c[j]=old;iters++;
   if(cur==0){std::cout<<"FOUND run="<<run<<" iters="<<iters<<"\n";for(auto g:c)std::cout<<g.op<<" "<<g.a<<" "<<g.b<<"\n";return 0;}
   if(cur<best){best=cur;std::cout<<"best="<<best<<" run="<<run<<" iters="<<iters<<std::endl;}
  }
 }
 std::cout<<"NO WITNESS iters="<<iters<<" best="<<best<<"\n";
}
