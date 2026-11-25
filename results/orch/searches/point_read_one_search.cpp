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
U wires[30]; Gate gates[20]; U states[2][30]; U ma,mb,me; int ors[30];
std::map<U,std::pair<int,int>> targets;
std::array<U,20> counts{};
void dfs(int d){
 int n=N+d;
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int op=0;op<2;op++){
  U w=op?(wires[a]|wires[b]):(wires[a]&wires[b]);

  // Adjacent independent gates commute. Keep their value order canonical.
  if(d && b<n-1 && w<wires[n-1])continue;
  wires[n]=w;gates[d]={a,b,bool(op)};counts[d]++; ors[d+1]=ors[d]+op;
  for(int orient=0;orient<2;orient++){
   U sa=states[orient][a],sb=states[orient][b];
   U ab=(((sa&ma)<<1)|((sa&me)>>1))&(sb&mb);
   U ba=(sa&mb)&(((sb&ma)<<1)|((sb&me)>>1));
   states[orient][n]=op?(sa|sb):((sa&sb&mb)|((ab|ba)<<1));
  }
  auto it=targets.find(w);
  if(it!=targets.end())for(int orient=0;orient<2;orient++){
   int witnessed=__builtin_popcountll(states[orient][n]&me);
   if(witnessed>ors[d+1]+1){
    std::cout<<"COUNTEREXAMPLE point-read-one bridge graph mask "<<it->second.second<<" gates "<<d+1<<" ors "<<ors[d+1]<<" witnessed edges "<<witnessed<<" orientation "<<orient<<std::endl;
    for(int j=0;j<=d;j++)std::cout<<gates[j].a<<" "<<gates[j].b<<" "<<gates[j].op<<"\n";
    std::exit(2);
   }
  }
  if(d+1<depthmax)dfs(d+1);
 }
}
int main(int argc,char**argv){
 P=std::atoi(argv[1]);L=std::atoi(argv[2]);N=P+L;depthmax=std::atoi(argv[3]);
 if(N>6)return 3;
 for(int p=0;p<P;p++)for(int l=0;l<L;l++){
  int bit=3*(p*L+l);ma|=U(1)<<bit;mb|=U(1)<<(bit+1);me|=U(1)<<(bit+2);
  states[0][p]|=U(1)<<bit;states[0][P+l]|=U(1)<<(bit+1);
  states[1][P+l]|=U(1)<<bit;states[1][p]|=U(1)<<(bit+1);
 }
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
 std::cout<<"Point-read-one bound bridge, both orientations; P "<<P<<" L "<<L<<" target graphs "<<targets.size()<<" max gates "<<depthmax<<std::endl;
 auto start=std::chrono::steady_clock::now();dfs(0);
 for(int d=0;d<depthmax;d++)std::cout<<"size "<<d+1<<" canonical circuits "<<counts[d]<<"\n";
 std::cout<<"No counterexample in enumerated circuits. Seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
