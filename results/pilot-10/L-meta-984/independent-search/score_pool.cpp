#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
struct State { int layer,index,width; std::vector<uint32_t> p,n; bool covered=false,unscorable=false; };
struct Code { int a,b,c,d,e,f; };
int score(const State& s,const Code& c){
 uint32_t A=s.p[c.a],B=s.p[c.b],C=s.p[c.c],D=s.n[c.d],E=s.n[c.e],F=s.n[c.f];
 return std::popcount(~D&B)+std::popcount(~D&C)+std::popcount(A&~E)+std::popcount(A&~F)-std::popcount(A&~D&(B|C)&~(E&F));
}
int scalar(bool a,bool b,bool c,bool d,bool e,bool f){ int x=int(b)+int(c), y=int(!e)+int(!f); return a ? (d ? y : std::max(x,std::max(y,x+y-1))) : (d ? 0:x); }
int main(int argc,char**argv){
 assert(argc==3); std::ifstream in(argv[1]); std::ofstream out(argv[2]); assert(in&&out);
 std::mt19937 rng(98428);
 for(int trial=0;trial<10000;trial++){
  State s; s.width=1+rng()%12; s.p.resize(3); s.n.resize(3); uint32_t mask=(1u<<s.width)-1;
  for(auto&x:s.p)x=rng()&mask; for(auto&x:s.n)x=rng()&mask;
  int sum=0; for(int i=0;i<s.width;i++)sum+=scalar(s.p[0]>>i&1,s.p[1]>>i&1,s.p[2]>>i&1,s.n[0]>>i&1,s.n[1]>>i&1,s.n[2]>>i&1);
  assert(sum==score(s,{0,1,2,0,1,2}));
 }
 int count,np,nn; in>>count>>np>>nn; std::vector<State> states(count);
 for(auto&s:states){in>>s.layer>>s.index>>s.width; s.p.resize(np);s.n.resize(nn); for(auto&x:s.p)in>>x;for(auto&x:s.n)in>>x; assert(s.width==s.layer+1&&s.width<32);}
 assert(in); std::vector<Code> pool; int tried=0, covered=0;
 for(int round=0;round<64&&tried<500;){
  int seed=-1; for(int i=0;i<count;i++)if(!states[i].covered&&!states[i].unscorable){seed=i;break;}
  if(seed<0)break; tried++;
  std::vector<Code> candidates;
  for(int a=0;a<np;a++)for(int b=0;b<np;b++)for(int c=b;c<np;c++)for(int d=0;d<nn;d++)for(int e=0;e<nn;e++)for(int f=e;f<nn;f++){
   Code z{a,b,c,d,e,f}; if(score(states[seed],z)<3)candidates.push_back(z);
  }
  if(candidates.empty()){states[seed].unscorable=true; if(tried%25==0)std::cout<<"unscorable_seeds="<<tried<<" covered="<<covered<<'\n'<<std::flush;continue;}
  std::shuffle(candidates.begin(),candidates.end(),rng);if(candidates.size()>512)candidates.resize(512);
  std::vector<int> sample; for(int t=0;t<2048;t++){int i=rng()%count;if(!states[i].covered)sample.push_back(i);}
  int best=-1,bestcount=-1;
  for(int j=0;j<(int)candidates.size();j++){int hits=0;for(int i:sample)hits+=score(states[i],candidates[j])<3;if(hits>bestcount){best=j;bestcount=hits;}}
  assert(best>=0);Code chosen=candidates[best];pool.push_back(chosen);round++;
  int gained=0;std::array<int,32> layers{};
  for(auto&s:states)if(!s.covered&&score(s,chosen)<3){s.covered=true;gained++;layers[s.layer]++;}
  covered+=gained;out<<chosen.a<<' '<<chosen.b<<' '<<chosen.c<<' '<<chosen.d<<' '<<chosen.e<<' '<<chosen.f<<'\n'<<std::flush;
  std::cout<<"pool="<<pool.size()<<" seed_layer="<<states[seed].layer<<" seed_index="<<states[seed].index<<" gained="<<gained<<" covered="<<covered<<" remaining="<<count-covered<<" perlayer=";
  for(int s=0;s<32;s++)if(layers[s])std::cout<<s<<':'<<layers[s]<<',';std::cout<<'\n'<<std::flush;
 }
 std::cout<<"DONE states="<<count<<" pool="<<pool.size()<<" covered="<<covered<<" remaining="<<count-covered<<" seeds="<<tried<<" formula_checks=10000\n";
}
