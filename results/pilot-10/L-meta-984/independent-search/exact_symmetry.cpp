#include <algorithm>
#include <bit>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <vector>
int main(int argc,char**argv){
 assert(argc==2);std::ifstream in(argv[1]);assert(in);int cases;in>>cases;
 auto start=std::chrono::steady_clock::now();
 for(int test=0;test<cases;test++){
  int graph,nn,np,count;in>>graph>>nn>>np>>count;uint32_t negmask=(1u<<nn)-1;
  std::map<int,std::set<std::vector<uint32_t>>> images;std::map<int,int> original;uint64_t permutations=0;
  for(int state=0;state<count;state++){
   int layer,width;in>>layer>>width;std::vector<uint32_t> cols(width);for(auto&v:cols)in>>v;original[layer]++;
   std::map<std::pair<int,int>,std::vector<uint32_t>> grouped;
   for(auto v:cols)grouped[{std::popcount(v&negmask),std::popcount(v>>nn)}].push_back(v);
   std::vector<std::vector<uint32_t>> groups;for(auto&[color,values]:grouped){std::sort(values.begin(),values.end());groups.push_back(values);}
   std::vector<uint32_t> order,best;bool first=true;
   std::function<void(int)> visit=[&](int g){
    if(g==(int)groups.size()){
     permutations++;std::vector<uint32_t> rows(nn+np);
     for(int j=0;j<width;j++)for(int r=0;r<nn+np;r++)rows[r]|=((order[j]>>r)&1)<<j;
     std::sort(rows.begin(),rows.begin()+nn);std::sort(rows.begin()+nn,rows.end());
     rows.insert(rows.begin(),width);
     if(first||rows<best){best=std::move(rows);first=false;}return;
    }
    auto&values=groups[g];do{order.insert(order.end(),values.begin(),values.end());visit(g+1);order.resize(order.size()-values.size());}while(std::next_permutation(values.begin(),values.end()));
   };
   visit(0);assert(!first);images[layer].insert(best);
  }
  int unique=0;for(auto&[layer,keys]:images)unique+=keys.size();
  std::cout<<"{\"graph\":"<<graph<<",\"graph_quotient_states\":"<<count<<",\"full_signed_row_isomorphism_classes\":"<<unique<<",\"column_permutations_examined\":"<<permutations<<",\"layers\":[";
  bool first=true;for(auto&[layer,num]:original){if(!first)std::cout<<',';first=false;std::cout<<"{\"layer\":"<<layer<<",\"before\":"<<num<<",\"after\":"<<images[layer].size()<<'}';}
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cout<<"],\"elapsed_seconds\":"<<seconds<<"}\n"<<std::flush;
 }
}
