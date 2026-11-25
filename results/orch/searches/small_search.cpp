#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>
using U=uint64_t;
struct Gate {int a,b;bool op;};
int P,L,N,depthmax;
U wires[30]; Gate gates[20];
std::map<U,std::pair<int,int>> targets;
std::array<U,20> counts{};
void dfs(int d){
 int n=N+d;
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int op=0;op<2;op++){
  U w=op?(wires[a]|wires[b]):(wires[a]&wires[b]);
  bool old=false;for(int i=0;i<n;i++)if(wires[i]==w){old=true;break;}if(old)continue;
  // Adjacent independent gates commute. Keep their value order canonical.
  if(d && b<n-1 && w<wires[n-1])continue;
  wires[n]=w;gates[d]={a,b,bool(op)};counts[d]++;
  auto it=targets.find(w);
  if(it!=targets.end() && d+1<it->second.first){
   std::cout<<"COUNTEREXAMPLE graph mask "<<it->second.second<<" size "<<d+1<<" star bound "<<it->second.first<<std::endl;
   for(int j=0;j<=d;j++)std::cout<<gates[j].a<<" "<<gates[j].b<<" "<<gates[j].op<<"\n";
   std::exit(2);
  }
  if(d+1<depthmax)dfs(d+1);
 }
}
int main(int argc,char**argv){
 P=std::atoi(argv[1]);L=std::atoi(argv[2]);N=P+L;depthmax=std::atoi(argv[3]);
 if(N>6)return 3;
 for(int i=0;i<N;i++)for(int x=0;x<(1<<N);x++)if(x>>i&1)wires[i]|=U(1)<<x;
 for(int m=1;m<(1<<(P*L));m++){
  bool c4=false;
  for(int p=0;p<P;p++)for(int q=p+1;q<P;q++){
   int shared=0;for(int l=0;l<L;l++)shared+=((m>>(p*L+l)&1)&&(m>>(q*L+l)&1));
   if(shared>1)c4=true;
  }if(c4)continue;
  int tau=N;
  for(int s=0;s<(1<<N);s++){
   bool cover=true;
   for(int p=0;p<P;p++)for(int l=0;l<L;l++)if((m>>(p*L+l)&1)&&!(s>>p&1)&&!(s>>(P+l)&1))cover=false;
   if(cover)tau=std::min(tau,__builtin_popcount(unsigned(s)));
  }
  U f=0;
  for(int p=0;p<P;p++)for(int l=0;l<L;l++)if(m>>(p*L+l)&1)f|=wires[p]&wires[P+l];
  targets[f]={__builtin_popcount(unsigned(m))+tau-1,m};
 }
 std::cout<<"P "<<P<<" L "<<L<<" target graphs "<<targets.size()<<" max gates "<<depthmax<<std::endl;
 auto start=std::chrono::steady_clock::now();dfs(0);
 for(int d=0;d<depthmax;d++)std::cout<<"size "<<d+1<<" canonical circuits "<<counts[d]<<"\n";
 std::cout<<"No counterexample in enumerated circuits. Seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
