#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using U = std::uint64_t;
struct Gate { int op, a, b; };
U target;
std::uint64_t prefixes=0, checked_final_pairs=0;
std::vector<Gate> path, answer;

bool present(const std::vector<U>& v,U x) {
  return std::find(v.begin(),v.end(),x)!=v.end();
}
bool search(std::vector<U>& v,int budget) {
  ++prefixes;
  if(present(v,target)){answer=path;return true;}
  if(!budget)return false;
  int n=static_cast<int>(v.size());
  if(budget==1) {
    for(int a=0;a<n;++a)for(int b=a+1;b<n;++b) {
      checked_final_pairs+=2;
      if((v[a]&v[b])==target){answer=path;answer.push_back({0,a,b});return true;}
      if((v[a]|v[b])==target){answer=path;answer.push_back({1,a,b});return true;}
    }
    return false;
  }
  std::vector<U> generated;
  for(int a=0;a<n;++a)for(int b=a+1;b<n;++b)for(int op=0;op<2;++op) {
    U value=op?(v[a]|v[b]):(v[a]&v[b]);
    if(present(v,value)||present(generated,value))continue;
    generated.push_back(value);
    v.push_back(value);path.push_back({op,a,b});
    if(search(v,budget-1))return true;
    path.pop_back();v.pop_back();
  }
  return false;
}

int main(int argc,char** argv) {
  int maxgates=argc>1?std::stoi(argv[1]):7;
  auto started=std::chrono::steady_clock::now();
  std::vector<U> input(6,0);
  for(int i=0;i<6;++i)for(int x=0;x<64;++x)
    if(x>>i&1)input[i]|=(U(1)<<x);
  target=0;
  std::vector<std::pair<int,int>> edges;
  for(int a=0;a<3;++a)for(int b=0;b<3;++b)if(a!=b) {
    edges.push_back({a,3+b});target|=input[a]&input[3+b];
  }
  int cases=0;
  for(int cover=0;cover<64;++cover) {
    bool valid=true;
    for(auto [a,b]:edges)if(!(cover>>a&1)&&!(cover>>b&1))valid=false;
    if(!valid)continue;
    bool minimal=true;
    for(int v=0;v<6;++v)if(cover>>v&1) {
      int smaller=cover&~(1<<v);bool ok=true;
      for(auto [a,b]:edges)if(!(smaller>>a&1)&&!(smaller>>b&1))ok=false;
      if(ok)minimal=false;
    }
    if(!minimal)continue;
    std::vector<U> values=input;path.clear();
    int roots=0;
    for(int v=0;v<6;++v)if(cover>>v&1) {
      U star=0;std::vector<int> leaves;
      for(auto [a,b]:edges) {
        if(a==v){star|=input[b];leaves.push_back(b);}
        if(b==v){star|=input[a];leaves.push_back(a);}
      }
      if(leaves.size()!=2)return 3;
      values.push_back(star);path.push_back({1,leaves[0],leaves[1]});++roots;
    }
    auto p0=prefixes,c0=checked_final_pairs;
    bool found=search(values,maxgates-roots);
    std::cout<<"cover="<<cover<<" roots="<<roots<<" remaining="<<(maxgates-roots)
             <<" prefixes="<<(prefixes-p0)<<" final_pairs="<<(checked_final_pairs-c0)
             <<" found="<<found<<std::endl;
    ++cases;
    if(found) {
      std::cout<<"CANDIDATE"<<std::endl;
      for(auto g:answer)std::cout<<g.op<<" "<<g.a<<" "<<g.b<<std::endl;
      return 1;
    }
  }
  std::cout<<"FINITE_CANONICAL_SEARCH_UNSAT cases="<<cases<<" prefixes="<<prefixes
           <<" final_pairs="<<checked_final_pairs<<" seconds="
           <<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()
           <<std::endl;
}
