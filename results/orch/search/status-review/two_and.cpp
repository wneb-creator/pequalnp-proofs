#include <array>
#include <vector>
#include <unordered_map>
#include <iostream>
#include <cstdint>
#include <algorithm>
struct T{uint64_t tt;int a,b,uses;};
int main(){
 std::array<uint64_t,6> v{};for(int i=0;i<6;++i)for(int x=0;x<64;++x)if(x>>i&1)v[i]|=1ULL<<x;
 std::array<uint64_t,64> sums{};for(int s=0;s<64;++s)for(int i=0;i<6;++i)if(s>>i&1)sums[s]|=v[i];
 std::unordered_map<uint64_t,int> graphs;
 for(int mask=0;mask<512;++mask){bool c4=false;for(int a=0;a<3;++a)for(int b=a+1;b<3;++b){int common=0;for(int j=0;j<3;++j)common+=((mask>>(3*a+j))&1)&&((mask>>(3*b+j))&1);if(common>=2)c4=true;}
  if(c4)continue;int cover=7;for(int s=0;s<64;++s){bool ok=true;for(int i=0;i<3;++i)for(int j=0;j<3;++j)if((mask>>(3*i+j)&1)&&!(s>>i&1)&&!(s>>(3+j)&1))ok=false;if(ok)cover=std::min(cover,__builtin_popcount((unsigned)s));}
  if(cover<3)continue;uint64_t tt=0;for(int i=0;i<3;++i)for(int j=0;j<3;++j)if(mask>>(3*i+j)&1)tt|=v[i]&v[3+j];graphs[tt]=mask;
 }
 std::cout<<"C4free 3x3 graphs tau3="<<graphs.size()<<"\n";
 uint64_t count=0;
 for(int s=1;s<64;++s)for(int t=s+1;t<64;++t){uint64_t u=sums[s]&sums[t];std::vector<T> ops;for(int a=0;a<64;++a){ops.push_back({sums[a],a,0,0});ops.push_back({sums[a]|u,a,0,1});}
  std::sort(ops.begin(),ops.end(),[](T a,T b){return a.tt<b.tt;});ops.erase(std::unique(ops.begin(),ops.end(),[](T a,T b){return a.tt==b.tt;}),ops.end());
  for(int a=0;a<(int)ops.size();++a)for(int b=a+1;b<(int)ops.size();++b){++count;uint64_t w=ops[a].tt&ops[b].tt;for(int out=0;out<2;++out){uint64_t z=out?(w|u):w;auto it=graphs.find(z);if(it!=graphs.end())std::cout<<"FOUND mask="<<it->second<<" first="<<s<<","<<t<<" second="<<ops[a].a<<"+"<<ops[a].uses<<","<<ops[b].a<<"+"<<ops[b].uses<<" out="<<out<<"\n";}}
 }
 std::cout<<"finished pairs="<<count<<"\n";
}
