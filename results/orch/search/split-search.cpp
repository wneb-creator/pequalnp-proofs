#include <algorithm>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <vector>
using U=uint64_t;
struct Wire { U f; int col; };
struct Op { int op,a,b; };
struct Target { int edges,tau,bound,mask,best=999; };
int p,l,n,K; U explored[16]={};
Wire wires[32]; Op ops[16];
std::unordered_map<U,Target> targets;
U mkfun(int mask){U f=0; for(int x=0;x<(1<<n);x++) for(int a=0;a<p;a++) for(int b=0;b<l;b++) if((mask>>(a*l+b)&1)&&(x>>a&1)&&(x>>(p+b)&1)) f|=U(1)<<x; return f;}
int tau(int mask){int best=n;for(int s=0;s<(1<<n);s++){if(std::popcount((unsigned)s)>=best)continue;bool ok=1;for(int a=0;a<p;a++)for(int b=0;b<l;b++)if((mask>>(a*l+b)&1)&&!(s>>a&1)&&!(s>>(p+b)&1))ok=0;if(ok)best=std::popcount((unsigned)s);}return best;}
bool c4free(int mask){for(int a=0;a<p;a++)for(int aa=a+1;aa<p;aa++){int common=0;for(int b=0;b<l;b++)if((mask>>(a*l+b)&1)&&(mask>>(aa*l+b)&1))common++;if(common>=2)return false;}return true;}
bool lesswire(Wire a, Wire b){return a.f<b.f||(a.f==b.f&&a.col<b.col);}
void search(int d){
 int m=n+d;
 for(int a=0;a<m;a++)for(int b=a;b<m;b++)for(int op=0;op<2;op++){
  Wire w{op?(wires[a].f|wires[b].f):(wires[a].f&wires[b].f),op?(wires[a].col|wires[b].col):0};
  if(w.col==3)continue;
  if(d&&b<m-1&&lesswire(w,wires[m-1]))continue;
  bool duplicate=false;for(int i=0;i<m;i++)if(w.f==wires[i].f&&w.col==wires[i].col){duplicate=true;break;}if(duplicate)continue;
  explored[d+1]++;
  wires[m]=w;ops[d]={op,a,b};
  auto it=targets.find(w.f);
  if(it!=targets.end()){
   it->second.best=std::min(it->second.best,d+1);
   int ac=0,oc=0;for(int j=0;j<=d;j++)if(ops[j].op)oc++;else ac++;
   if(ac<it->second.tau || oc<it->second.edges-1){std::cout<<"SPLIT FAILURE AND="<<ac<<" OR="<<oc<<std::endl;std::cout<<"COUNTEREXAMPLE p="<<p<<" l="<<l<<" E="<<it->second.mask<<" edges="<<it->second.edges<<" tau="<<it->second.tau<<" gates="<<d+1<<std::endl;for(int j=0;j<=d;j++)std::cout<<n+j<<" "<<(ops[j].op?"OR":"AND")<<" "<<ops[j].a<<" "<<ops[j].b<<std::endl;std::exit(42);}
  }
  if(d+1<K)search(d+1);
 }
}
int main(int argc,char**argv){p=std::atoi(argv[1]);l=std::atoi(argv[2]);K=std::atoi(argv[3]);n=p+l;if(n>6||p*l>20)return 2;
 for(int i=0;i<n;i++){wires[i]={0,i<p?1:2};for(int x=0;x<(1<<n);x++)if(x>>i&1)wires[i].f|=U(1)<<x;}
 for(int mask=1;mask<(1<<(p*l));mask++)if(c4free(mask)){int e=std::popcount((unsigned)mask),t=tau(mask);targets.emplace(mkfun(mask),Target{e,t,e+t-1,mask});}
 std::cout<<"START p="<<p<<" l="<<l<<" gates<="<<K<<" targets="<<targets.size()<<std::endl;
 auto start=std::chrono::steady_clock::now();search(0);
 for(int k=1;k<=K;k++)std::cout<<"enumerated gate count "<<k<<": "<<explored[k]<<"\n";
 int bounded=0,attained=0;for(auto [f,t]:targets){if(t.bound<=K+1)bounded++;if(t.best==t.bound)attained++;}
 std::cout<<"No counterexample. Full below-bound coverage for "<<bounded<<" targets; exact bound witnessed for "<<attained<<" targets. Seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
