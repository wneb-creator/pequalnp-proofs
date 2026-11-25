#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <random>
using U=unsigned long long;
constexpr U target=0xfe80e880fe008000ULL;
constexpr int N=12;
struct Gate { int a,b,op; };
using Net=std::array<Gate,N>;
std::mt19937_64 rng(178831);
int ri(int n){return rng()%n;}
int score(const Net& g){
  U v[6+N]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,
    0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,
    0xffff0000ffff0000ULL,0xffffffff00000000ULL};
  for(int i=0;i<N;i++) v[6+i]=g[i].op?(v[g[i].a]|v[g[i].b]):(v[g[i].a]&v[g[i].b]);
  return std::popcount(v[5+N]^target);
}
Net initial(){
  Net n={Gate{0,1,0},Gate{6,2,1},Gate{6,4,1},Gate{0,1,1},Gate{2,8,0},
   Gate{7,5,0},Gate{11,4,1},Gate{9,12,0},Gate{13,10,1},Gate{14,3,0},Gate{15,15,1}};
  for(int i=10;i<N;i++) n[i]={5+i,5+i,1};
  return n;
}
void print(const Net& n,int s,long long iter){
 printf("score=%d iterations=%lld\n",s,iter);
 for(int i=0;i<N;i++)printf("%d: %c %d %d\n",6+i,n[i].op?'|':'&',n[i].a,n[i].b);
 fflush(stdout);
}
int main(int argc,char**argv){
 int seconds=argc>1?atoi(argv[1]):120;
 auto start=std::chrono::steady_clock::now();
 Net best=initial(); int bs=score(best); long long iter=0;
 print(best,bs,iter);
 for(int restart=0;;restart++){
  Net cur=restart%4?best:initial(); int cs=score(cur);
  if(restart%8==0){for(int i=0;i<N;i++)cur[i]={ri(6+i),ri(6+i),ri(2)}; cs=score(cur);}
  for(int step=0;step<100000;step++){
   iter++;
   Net next=cur;
   int mutations=1+(ri(100)<10)+(ri(100)<3);
   for(int k=0;k<mutations;k++){
    int i=ri(N),which=ri(3);
    if(which==0)next[i].a=ri(6+i);
    else if(which==1)next[i].b=ri(6+i);
    else next[i].op^=1;
   }
   int ns=score(next);
   double temp=0.15+0.9*(1.0-(step%10000)/10000.0);
   if(ns<=cs || std::generate_canonical<double,32>(rng)<std::exp((cs-ns)/temp)){cur=next;cs=ns;}
   if(ns<bs){best=next;bs=ns;print(best,bs,iter);if(bs==0)return 0;}
  }
  if(std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count()>=seconds)break;
 }
 print(best,bs,iter); return 1;
}
