#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <tuple>
#include <vector>

struct TT { uint64_t a=0,b=0; bool operator==(const TT&)const=default; };
TT And(TT x,TT y){return{x.a&y.a,x.b&y.b};}
TT Or(TT x,TT y){return{x.a|y.a,x.b|y.b};}
TT Not(TT x){return{~x.a,~x.b};}
struct G{int op,a,b;};
constexpr int B=17;
std::array<TT,B+4> values;
std::array<int,B+4> dependencies;
std::array<G,4> gates;
TT target;
uint64_t prefixes=0,attempts=0;
int currentVariant=0;

TT eval(G g){return g.op==0?And(values[g.a],values[g.b]):g.op==1?Or(values[g.a],values[g.b]):Not(values[g.a]);}
std::vector<G> options(int n,bool needsPrevious=false){
  std::vector<G> out;
  for(int a=0;a<n;++a){
    if(!needsPrevious||a>=B)out.push_back({2,a,0});
    for(int b=a+1;b<n;++b)if(!needsPrevious||b>=B){out.push_back({0,a,b});out.push_back({1,a,b});}
  }
  return out;
}
bool fresh(TT t,int n){for(int j=0;j<n;++j)if(values[j]==t)return false;return true;}
void found(int count){
  std::cout<<"FOUND "<<count<<" gates prefixes "<<prefixes<<" attempts "<<attempts<<std::endl;
  std::ofstream f("local-repair-result.json");
  f<<"{\"variant\":"<<currentVariant<<",\"base_variables\":[0,2,3,5,6,9,4],\"base_shared\":[\"A\",\"B\",\"C\",\"D\",\"seed\",\"false\",\"pairA\",\"pairB\",\"pairC\",\"pairD\"],\"gates\":[";
  for(int i=0;i<count;++i){auto[op,a,b]=gates[i];if(i)f<<",";f<<"[\""<<(op==0?"and":op==1?"or":"not")<<"\","<<a;if(op!=2)f<<","<<b;f<<"]";}
  f<<"],\"output\":"<<B+count-1<<"}\n";
}
int main(){
  auto start=std::chrono::steady_clock::now();
  for(int x=0;x<128;++x){
    auto bit=[&](int j){return bool(x>>j&1);};
    auto set=[&](TT&t){if(x<64)t.a|=uint64_t(1)<<x;else t.b|=uint64_t(1)<<(x-64);};
    for(int j=0;j<7;++j)if(bit(j))set(values[j]);
    if(bit(0)||bit(1)||bit(4))set(values[7]);
    if(bit(2)||bit(3)||bit(4))set(values[8]);
    if(bit(1)||bit(3)||bit(5))set(values[9]);
    if(bit(0)||bit(2)||bit(5))set(values[10]);
    if(bit(0)&&bit(1))set(values[11]);
    bool matching=(bit(0)&&bit(3))||(bit(1)&&bit(2))||(bit(4)&&bit(5));
    if(matching||(bit(6)&&(bit(0)||bit(2)||bit(5))))set(target);
  }
  const auto first=options(B),second=options(B+1),third=options(B+2,true);
  const int triples[4][3]={{0,1,4},{2,3,4},{1,3,5},{0,2,5}};
  const int choices[3][2]={{0,1},{0,2},{1,2}};
  for(int trial=0;trial<81;++trial){
  currentVariant=(trial+78)%81;
  int digits=currentVariant;
  for(int k=0;k<4;++k){
    int choice=digits%3;digits/=3;
    values[13+k]=Or(values[triples[k][choices[choice][0]]],values[triples[k][choices[choice][1]]]);
  }
  std::set<std::pair<uint64_t,uint64_t>> firstSeen;
  for(auto g1:first){
    TT f1=eval(g1);if(!fresh(f1,B)||!firstSeen.emplace(f1.a,f1.b).second)continue;
    values[B]=f1;dependencies[B]=1;gates[0]=g1;
    if(f1==target){found(1);return 0;}
    std::set<std::pair<uint64_t,uint64_t>> secondSeen;
    for(auto g2:second){
      TT f2=eval(g2);if(!fresh(f2,B+1)||!secondSeen.emplace(f2.a,f2.b).second)continue;
      values[B+1]=f2;gates[1]=g2;dependencies[B+1]=2|dependencies[g2.a]|(g2.op==2?0:dependencies[g2.b]);
      ++prefixes;
      if(f2==target){found(2);return 0;}
      for(auto g3:third){
        ++attempts;
        TT f3=eval(g3);gates[2]=g3;
        if(f3==target){found(3);return 0;}
        int dep3=4|dependencies[g3.a]|(g3.op==2?0:dependencies[g3.b]);
        bool superset=And(f3,target)==target,subset=Or(f3,target)==target;
        if(!(superset||subset||Not(f3)==target))continue;
        values[B+2]=f3;
        if(Not(f3)==target&&dep3==7){gates[3]={2,B+2,0};found(4);return 0;}
        for(int j=0;j<B+2;++j){
          if((dep3|dependencies[j])!=7)continue;
          if(superset&&And(f3,values[j])==target){gates[3]={0,B+2,j};found(4);return 0;}
          if(subset&&Or(f3,values[j])==target){gates[3]={1,B+2,j};found(4);return 0;}
        }
      }
    }
  }
  std::cout<<"variant "<<currentVariant<<" no repair, cumulative prefixes "<<prefixes<<" candidates "<<attempts<<std::endl;
  }
  std::cout<<"NO REPAIR within the fixed shared signals and four gates; prefixes "<<prefixes<<" candidates "<<attempts<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
  return 2;
}
