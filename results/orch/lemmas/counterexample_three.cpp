#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using U=uint64_t;
using State=std::array<U,8>;
struct Hash { size_t operator()(const State& s) const { size_t h=0; for(U x:s){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;x^=x>>31;h^=x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);} return h; }};
struct Info {std::array<U,720> images; U canonical;};
std::array<std::array<int,64>,720> assignments;
std::unordered_map<U,Info> functions;
const Info& info(U f) {
 auto it=functions.find(f); if(it!=functions.end())return it->second;
 Info r; r.canonical=~U(0);
 for(int p=0;p<720;p++){U z=0,b=f;while(b){int i=std::countr_zero(b);b&=b-1;z|=U(1)<<assignments[p][i];}r.images[p]=z;r.canonical=std::min(r.canonical,z);}
 return functions.emplace(f,std::move(r)).first->second;
}
State canonical(State s,int n) {
 std::array<const Info*,8> inf;
 for(int i=0;i<n;i++)inf[i]=&info(s[i]);
 State best;best.fill(~U(0));
 for(int p=0;p<720;p++){
  U first=~U(0);for(int i=0;i<n;i++)first=std::min(first,inf[i]->images[p]);
  if(first>best[0])continue;
  State a{};for(int i=0;i<n;i++)a[i]=inf[i]->images[p];
  std::sort(a.begin(),a.begin()+n);
  if(a<best)best=a;
 }
 return best;
}
int cover(int e){int ans=6;for(int t=0;t<64;t++){bool ok=true;for(int p=0;p<3;p++)for(int l=0;l<3;l++)if((e>>(3*p+l)&1)&& !(t>>p&1)&&!(t>>(3+l)&1))ok=false;if(ok)ans=std::min(ans,std::popcount(unsigned(t)));}return ans;}
int main(int argc,char**argv){
 int maxdepth=argc>1?std::stoi(argv[1]):6;
 std::array<int,6> perm={0,1,2,3,4,5};int pi=0;
 do{for(int x=0;x<64;x++){int y=0;for(int i=0;i<6;i++)if(x>>i&1)y|=1<<perm[i];assignments[pi][x]=y;}pi++;}while(std::next_permutation(perm.begin(),perm.end()));
 std::array<U,6> vars{};for(int i=0;i<6;i++)for(int x=0;x<64;x++)if(x>>i&1)vars[i]|=U(1)<<x;
 std::unordered_map<U,std::array<int,3>> targets;
 for(int e=1;e<512;e++){
  bool c4=false;for(int p=0;p<3;p++)for(int q=p+1;q<3;q++)if(std::popcount(unsigned((e>>(3*p))&(e>>(3*q))&7))>=2)c4=true;
  if(c4)continue;
  U f=0;for(int p=0;p<3;p++)for(int l=0;l<3;l++)if(e>>(3*p+l)&1)f|=vars[p]&vars[3+l];
  targets[info(f).canonical]={e,std::popcount(unsigned(e))+cover(e)-1,0};
 }
 std::cout<<"target_classes="<<targets.size()<<std::endl;
 std::unordered_set<State,Hash> states;states.insert(State{});
 auto start=std::chrono::steady_clock::now();
 for(int depth=1;depth<=maxdepth;depth++){
  std::unordered_set<State,Hash> next,raw;
  for(const auto&s:states){
   std::array<U,14> available{};for(int i=0;i<6;i++)available[i]=vars[i];for(int i=0;i<depth-1;i++)available[6+i]=s[i];
   for(int a=0;a<6+depth-1;a++)for(int b=a+1;b<6+depth-1;b++)for(int op=0;op<2;op++){
    U f=op?available[a]|available[b]:available[a]&available[b];
    if(std::find(available.begin(),available.begin()+6+depth-1,f)!=available.begin()+6+depth-1)continue;
    auto t=targets.find(info(f).canonical);if(t!=targets.end()&&!t->second[2]){t->second[2]=depth;std::cout<<"found edge_mask="<<t->second[0]<<" minimum="<<depth<<" clean_upper="<<t->second[1]<<std::endl;}
    if(depth==maxdepth)continue;
    State ns=s;ns[depth-1]=f;std::sort(ns.begin(),ns.begin()+depth);
    if(raw.insert(ns).second)next.insert(canonical(ns,depth));
   }
  }
  states=std::move(next);
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
  std::cout<<"depth="<<depth<<" states="<<states.size()<<" raw="<<raw.size()<<" functions="<<functions.size()<<" seconds="<<seconds<<std::endl;
  bool done=true;for(const auto&[f,t]:targets)if(!t[2])done=false;if(done)break;
 }
 for(const auto&[f,t]:targets)std::cout<<"result edge_mask="<<t[0]<<" minimum="<<t[2]<<" clean_upper="<<t[1]<<std::endl;
}
