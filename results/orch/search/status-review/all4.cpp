#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <algorithm>
#include <chrono>
struct V {uint16_t t; uint8_t d;};
struct G {int a,b; char op;};
std::array<V,16> w;
std::array<G,12> gates;
uint16_t target;
std::array<int,262144> mincost;
uint64_t count=0;
int limit=0;
bool found=false;
V op(V a,V b,bool aand){
 if(!aand)return {uint16_t(a.t|b.t),uint8_t(a.d|b.d)};
 int da = (((a.t>>1)&1) && (b.d&1)) || ((a.d&1) && ((b.t>>1)&1));
 int db = (((a.t>>2)&1) && (b.d&2)) || ((a.d&2) && ((b.t>>2)&1));
 return {uint16_t(a.t&b.t),uint8_t(da | (db<<1))};
}
bool dfs(int k){
 ++count;
 if(k==limit)return false;
 int n=4+k;
 for(int a=0;a<n;++a)for(int b=a+1;b<n;++b)for(bool aand:{false,true}){
  V v=op(w[a],w[b],aand);
  // A completely duplicated signature never needs a third representative.
  int reps=0;
  for(int j=0;j<n;++j) if(w[j].t==v.t && w[j].d==v.d) ++reps;
  if(reps>=2)continue;
  w[n]=v; gates[k]={a,b,aand?'&':'|'};
  mincost[(int(v.t)<<2)|v.d]=std::min(mincost[(int(v.t)<<2)|v.d],k+1);
  if(false){
   std::cout<<"found "<<k+1<<" gates\n";
   for(int j=0;j<=k;++j)std::cout<<4+j<<" "<<gates[j].a<<" "<<gates[j].op<<" "<<gates[j].b<<"\n";
   return true;
  }
  if(dfs(k+1))return true;
 }
 return false;
}
int main(int argc,char** argv){
 for(int a=0;a<4;++a){w[a]={0,uint8_t(a==0?2:a==1?1:0)};for(int x=0;x<16;++x)if((x>>a)&1)w[a].t|=1<<x;}
 target=(w[0].t&w[1].t)|(w[0].t&w[2].t)|(w[1].t&w[3].t);
 limit=argc>1?std::atoi(argv[1]):4;
 auto start=std::chrono::steady_clock::now();
 mincost.fill(99);
 found=dfs(0);
 for(int mask=1;mask<64;++mask){uint16_t t=0;int e=0;for(int a=0;a<4;++a)for(int b=a+1;b<4;++b){if(mask>>e&1)t|=w[a].t&w[b].t;++e;}if(!(mask&1))continue;int normal=99;for(int d=0;d<4;++d)normal=std::min(normal,mincost[(int(t)<<2)|d]);int dbl=mincost[int(t)<<2];std::cout<<"graph="<<mask<<" ordinary="<<normal<<" double="<<dbl<<"\n";}
 std::cout<<"limit="<<limit<<" found="<<found<<" states="<<count<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";
}
