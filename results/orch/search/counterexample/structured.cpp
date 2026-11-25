#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <cstdint>
using namespace std;
struct Gate {int op,a,b;};
uint64_t value(const Gate&g,const array<uint64_t,18>&w){return g.op==0?w[g.a]&w[g.b]:g.op==1?w[g.a]|w[g.b]:~w[g.a];}
vector<Gate> candidates(int n){vector<Gate>v;for(int i=0;i<n;i++){v.push_back({2,i,0});for(int j=0;j<i;j++){v.push_back({0,i,j});v.push_back({1,i,j});}}return v;}
int main(){
 array<uint64_t,18>w{};for(int x=0;x<64;x++)for(int j=0;j<6;j++)if(x>>j&1)w[j]|=1ull<<x;
 uint64_t M=(w[0]&w[3])|(w[1]&w[4])|(w[2]&w[5]);
 const int tri[4][3]={{1,3,5},{0,1,2},{0,4,5},{3,2,4}};
 auto c1=candidates(14),c2=candidates(15);long long checks=0;
 for(int config=0;config<81;config++){
  int z=config;vector<Gate>base;
  for(int t=0;t<4;t++){int omit=z%3;z/=3;int a=tri[t][(omit+1)%3],b=tri[t][(omit+2)%3],c=tri[t][omit];base.push_back({1,a,b});w[6+2*t]=w[a]|w[b];base.push_back({1,6+2*t,c});w[7+2*t]=w[6+2*t]|w[c];}
  uint64_t D=w[13];
  auto hit=[&](vector<Gate>g,int out){
   int neg=0;for(auto a:g)neg+=a.op==2;
   if(neg&&((w[out]&D)==M)){
    cout<<"FOUND config="<<config<<" extra="<<g.size()<<" out="<<out<<endl;
    ofstream f("/tmp/oec/pequalnp-pilot-95/counterexample/structured-witness.txt");int i=6;for(auto a:base)f<<i++<<" "<<a.op<<" "<<a.a<<" "<<a.b<<"\n";for(auto a:g)f<<i++<<" "<<a.op<<" "<<a.a<<" "<<a.b<<"\n";return true;
   }return false;
  };
  for(auto a:c1){w[14]=value(a,w);if(hit({a},14))return 0;
   for(auto b:c2){w[15]=value(b,w);if(hit({a,b},15))return 0;
    Gate c{2,15,0};w[16]=value(c,w);checks++;if(hit({a,b,c},16))return 0;
    for(int j=0;j<15;j++)for(int op=0;op<2;op++){
     if(a.op!=2&&b.op!=2)continue;
     c={op,15,j};w[16]=value(c,w);checks++;if(hit({a,b,c},16))return 0;
    }
   }
  }
  cout<<"config="<<config<<" checked="<<checks<<endl;
 }
 cout<<"NO WITNESS checks="<<checks<<endl;
}
