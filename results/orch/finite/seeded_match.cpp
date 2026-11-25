#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <unordered_set>
#include <vector>
#include <chrono>

using U = uint64_t;
struct Step { int op, a, b; };
struct PairHash { size_t operator()(std::array<U,2> const &a) const { return a[0] ^ (a[1]+0x9e3779b97f4a7c15ULL+(a[0]<<6)+(a[0]>>2)); } };
struct TripleHash { size_t operator()(std::array<U,3> const &a) const { U h=0; for(U v:a)h^=v+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);return h; } };
std::vector<U> base;
U goal;
U mask=~U(0);
uint64_t seen[5]={};
std::vector<std::pair<U,Step>> choices(std::vector<U> const &bank) {
  std::vector<std::pair<U,Step>> out;
  for(int i=0;i<(int)bank.size();i++) {
    out.push_back({(~bank[i])&mask,{2,i,i}});
    for(int j=0;j<i;j++) {
      out.push_back({bank[i]&bank[j],{0,j,i}});
      out.push_back({bank[i]|bank[j],{1,j,i}});
    }
  }
  std::sort(out.begin(),out.end(),[](auto const &a,auto const &b){return a.first<b.first;});
  out.erase(std::unique(out.begin(),out.end(),[](auto const &a,auto const &b){return a.first==b.first;}),out.end());
  out.erase(std::remove_if(out.begin(),out.end(),[&](auto const &x){return std::find(bank.begin(),bank.end(),x.first)!=bank.end();}),out.end());
  return out;
}
bool hit(std::vector<U> const &bank,std::vector<Step> const &path) {
  for(int i=0;i<(int)bank.size();i++) {
    if(bank[i]==goal) {
      puts("FOUND");for(auto q:path)printf("%d %d %d\n",q.op,q.a,q.b);printf("output %d\n",i);return true;
    }
  }
  return false;
}
bool one(std::vector<U> const &b,std::vector<Step> const &p) {
  for(int i=0;i<(int)b.size();i++) {
    if(((~b[i])&mask)==goal) { auto q=p;q.push_back({2,i,i});auto c=b;c.push_back(goal);return hit(c,q); }
    for(int j=0;j<i;j++) {
      if((b[i]&b[j])==goal || (b[i]|b[j])==goal) {
        auto q=p;q.push_back({(b[i]&b[j])==goal?0:1,j,i});auto c=b;c.push_back(goal);return hit(c,q);
      }
    }
  }
  return false;
}
int main(int argc,char **argv) {
  int depth=argc>1?std::atoi(argv[1]):3;
  base={0,~U(0)};
  for(int i=0;i<6;i++) { U w=0;for(int r=0;r<64;r++)if((r>>i)&1)w|=U(1)<<r;base.push_back(w); }
  U a=base[2],b=base[3],c=base[4],d=base[5],e=base[6],f=base[7];
  base.push_back(b|c|e);base.push_back(a|d|e);base.push_back(a|c|f);base.push_back(b|d|f);
  if(argc>2) { base.push_back(b|d);base.push_back(c|e);base.push_back(c|f);base.push_back(d|e); }
  goal=(a&b)|(c&d)|(e&f);
  if(argc>3) {
    std::vector<int> rows={0,63,3,12,48};
    for(int i=0;i<8;i++)rows.push_back((1<<((i&1)?1:0))|(1<<((i&2)?3:2))|(1<<((i&4)?5:4)));
    auto project=[&](U x){U y=0;for(size_t i=0;i<rows.size();i++)if((x>>rows[i])&1)y|=U(1)<<i;return y;};
    for(U &x:base)x=project(x);
    goal=project(goal);
    mask=(U(1)<<rows.size())-1;
  }
  printf("goal %llu\n",(unsigned long long)goal);
  for(size_t i=0;i<base.size();i++)printf("base %zu %llu\n",i,(unsigned long long)base[i]);
  if(hit(base,{}) || one(base,{}))return 0;
  auto first=choices(base);
  printf("first %zu\n",first.size());fflush(stdout);
  std::unordered_set<std::array<U,2>,PairHash> pairSeen;
  std::unordered_set<std::array<U,3>,TripleHash> tripleSeen;
  for(auto [v,q]:first) {
    auto b1=base;b1.push_back(v);std::vector<Step> p1={q};
    if(one(b1,p1))return 0;
    for(auto [w,r]:choices(b1)) {
      std::array<U,2> key={v,w};std::sort(key.begin(),key.end());
      if(!pairSeen.insert(key).second)continue;
      auto b2=b1;b2.push_back(w);auto p2=p1;p2.push_back(r);
      if(one(b2,p2))return 0;
      if(depth<4)continue;
      for(auto [z,t]:choices(b2)) {
        std::array<U,3> k3={v,w,z};std::sort(k3.begin(),k3.end());
        if(!tripleSeen.insert(k3).second)continue;
        auto b3=b2;b3.push_back(z);auto p3=p2;p3.push_back(t);
        if(one(b3,p3))return 0;
      }
    }
  }
  printf("EXHAUSTED depth %d pairs %zu triples %zu\n",depth,pairSeen.size(),tripleSeen.size());
}
