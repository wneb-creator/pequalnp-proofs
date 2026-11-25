#include <array>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>
using U=__uint128_t;
struct H {size_t operator()(U a) const {return (uint64_t)a ^ ((uint64_t)(a>>64)*0x9e3779b97f4a7c15ULL);}};
struct G {int op,a,b;};
std::array<U,7> inp,t;
std::chrono::steady_clock::time_point start;
long long nodes[5]={};
int limit=300;
bool found=false,timed=false;
std::vector<G> trail;
int maskof(U v){for(int i=0;i<7;i++)if(v==t[i])return 1<<i;return 0;}
int closure(std::vector<U>&v,std::vector<G>&g,int mask){
 int orig=v.size();int newmask=0;G via[7];
 for(int a=0;a<orig;a++){
  U q=~v[a];int m=maskof(q);if(m&&!(m&mask)){int k=__builtin_ctz(m);via[k]={2,a,0};newmask|=m;}
  for(int b=a+1;b<orig;b++)for(int op=0;op<2;op++){
   q=op?(v[a]&v[b]):(v[a]|v[b]);m=maskof(q);if(m&&!(m&mask)){int k=__builtin_ctz(m);via[k]={op,a,b};newmask|=m;}
  }
 }
 for(int i=0;i<7;i++)if(newmask&(1<<i)){v.push_back(t[i]);g.push_back(via[i]);}
 return mask|newmask;
}
void dfs(std::vector<U> v,std::vector<G> g,int mask,int depth){
 nodes[depth]++;
 if((nodes[depth]&65535)==0){if(std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count()>=limit){timed=true;return;}}
 mask=closure(v,g,mask);
 if(mask==127){std::cout<<"FOUND depth="<<depth<<" gates="<<g.size()<<std::endl;for(size_t i=0;i<g.size();i++)std::cout<<7+i<<" "<<g[i].op<<" "<<g[i].a<<" "<<g[i].b<<std::endl;found=true;return;}
 if(depth==4)return;
 std::unordered_set<U,H> seen(v.begin(),v.end());
 int n=v.size();
 auto attempt=[&](U q,G z){
  if(maskof(q)||!seen.insert(q).second)return;
  auto w=v;auto h=g;w.push_back(q);h.push_back(z);dfs(std::move(w),std::move(h),mask,depth+1);
 };
 attempt(U(0),{3,0,0});
 if(!found&&!timed)attempt(~U(0),{4,0,0});
 for(int a=0;a<n&&!found&&!timed;a++){
  attempt(~v[a],{2,a,0});
  for(int b=a+1;b<n&&!found&&!timed;b++){
   attempt(v[a]|v[b],{0,a,b});if(found||timed)break;
   attempt(v[a]&v[b],{1,a,b});
  }
 }
 if(depth==1){std::cout<<"PROGRESS nodes=";for(auto z:nodes)std::cout<<z<<",";std::cout<<" seconds="<<std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now()-start).count()<<std::endl;}
}
int main(int argc,char**argv){
 if(argc>1)limit=std::stoi(argv[1]);
 for(int i=0;i<7;i++)for(int x=0;x<128;x++)if((x>>i)&1)inp[i]|=U(1)<<x;
 std::vector<std::vector<int>> supports={{1,3},{0,6},{1,5,6},{0,4,5},{3,4,6},{2,3,5},{1,2,4}};
 for(int i=0;i<7;i++)for(int j:supports[i])t[i]|=inp[j];
 start=std::chrono::steady_clock::now();
 dfs(std::vector<U>(inp.begin(),inp.end()),{},0,0);
 std::cout<<"DONE found="<<found<<" timed="<<timed<<" nodes=";for(auto z:nodes)std::cout<<z<<",";std::cout<<std::endl;
}
