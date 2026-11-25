#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <unordered_map>
#include <vector>

// Exact minimum-formula dynamic programming on a complete extremal sample.
// A found circuit must still be independently evaluated on all assignments.
int main(int argc,char**argv) {
  if(argc!=4&&argc!=5) return 2;
  std::ifstream in(argv[1]);
  int rows,inputs,maxcost;uint32_t goal;
  in>>rows>>inputs>>goal>>maxcost;
  const uint32_t size=1u<<rows, full=size-1;
  std::vector<uint8_t> cost(size,255),op(size,255);
  std::vector<uint32_t> left(size),right(size);
  std::vector<int> input_id(size,-1);
  std::vector<std::vector<uint32_t>> bucket(maxcost+1);
  for(int i=0;i<inputs;i++) {
    uint32_t v;in>>v;
    if(cost[v]==255){cost[v]=0;input_id[v]=i;bucket[0].push_back(v);}
  }
  auto start=std::chrono::steady_clock::now();
  double limit=std::stod(argv[3]);uint64_t pairs=0;bool found=cost[goal]==0;
  auto seconds=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  for(int d=1;d<=maxcost&&!found;d++) {
    for(int a=0;a<=d-1-a&&!found;a++) {
      int b=d-1-a;
      for(size_t i=0;i<bucket[a].size()&&!found;i++) {
        uint32_t x=bucket[a][i];
        size_t first=a==b?i+1:0;
        for(size_t j=first;j<bucket[b].size();j++) {
          uint32_t y=bucket[b][j];pairs++;
          uint32_t v=x&y;
          if(v&&v!=full&&cost[v]==255) {
            cost[v]=d;op[v]=0;left[v]=x;right[v]=y;bucket[d].push_back(v);
            if(v==goal){found=true;break;}
          }
          v=x|y;
          if(v&&v!=full&&cost[v]==255) {
            cost[v]=d;op[v]=1;left[v]=x;right[v]=y;bucket[d].push_back(v);
            if(v==goal){found=true;break;}
          }
          if((pairs&0xffffff)==0&&seconds()>limit) {
            std::cout<<"TIME_LIMIT cost="<<d<<" pairs="<<pairs<<" seconds="<<seconds()<<std::endl;
            return 0;
          }
        }
      }
    }
    std::cout<<"cost="<<d<<" new="<<bucket[d].size()<<" pairs="<<pairs<<" seconds="<<seconds()<<std::endl;
  }
  if(!found)std::cout<<"NO_FORMULA_UP_TO "<<maxcost<<std::endl;
  if(argc==5) {
    std::ofstream seeds(argv[4]);seeds<<'[';bool comma=false;int total=0;
    for(uint32_t v=1;v<size;v++)if(cost[v]>=1&&cost[v]<=4) {
      std::unordered_map<uint32_t,uint32_t> wr;
      struct S{uint8_t op;uint32_t a,b;};std::vector<S> gs;
      std::function<uint32_t(uint32_t)> go=[&](uint32_t u)->uint32_t {
        if(input_id[u]>=0)return input_id[u];
        auto it=wr.find(u);if(it!=wr.end())return it->second;
        uint32_t a=go(left[u]),b=go(right[u]);gs.push_back({op[u],a,b});
        return wr[u]=inputs+gs.size()-1;
      };
      uint32_t out=go(v);
      if(comma)seeds<<',';comma=true;total++;
      seeds<<"{\"value\":"<<v<<",\"formula_cost\":"<<int(cost[v])<<",\"output\":"<<out<<",\"gates\":[";
      for(size_t j=0;j<gs.size();j++){if(j)seeds<<',';seeds<<"[\""<<(gs[j].op?"or":"and")<<"\","<<gs[j].a<<','<<gs[j].b<<']';}
      seeds<<"]}";
    }
    seeds<<"]\n";std::cout<<"HELPER_SEEDS "<<total<<std::endl;
  }
  // Meet in the middle at the output. Shared canonical subexpressions between
  // the two children are counted once, even when their formula costs add up to
  // more than the requested circuit budget.
  std::vector<uint32_t> mark(size);uint32_t epoch=0;
  int best_dag=100000;uint32_t best_a=0,best_b=0;uint8_t best_op=0;
  std::function<int(uint32_t)> count=[&](uint32_t v)->int {
    if(input_id[v]>=0||mark[v]==epoch)return 0;
    mark[v]=epoch;
    return 1+count(left[v])+count(right[v]);
  };
  auto inspect=[&](uint32_t a,uint32_t b,uint8_t o) {
    if(a==goal||b==goal||a==b||cost[a]==255||cost[b]==255)return;
    epoch++;int z=1+count(a)+count(b);
    if(z<best_dag){best_dag=z;best_a=a;best_b=b;best_op=o;}
  };
  for(uint32_t a=1;a<size;a++)if(cost[a]!=255&&a!=goal) {
    if((a|goal)==goal) {
      uint32_t t=a;
      while(true){inspect(a,(goal^a)|t,1);if(!t)break;t=(t-1)&a;}
    }
    if((a&goal)==goal) {
      uint32_t free=full^a,t=free;
      while(true){inspect(a,goal|t,0);if(!t)break;t=(t-1)&free;}
    }
  }
  if(best_dag==100000){std::cout<<"NO_ROOT_DECOMPOSITION"<<std::endl;return 0;}
  cost[goal]=cost[best_a]+cost[best_b]+1;op[goal]=best_op;left[goal]=best_a;right[goal]=best_b;
  std::cout<<"ROOT_MITM dag="<<best_dag<<" formula="<<int(cost[goal])<<std::endl;
  struct Gate{uint8_t op;uint32_t a,b;};std::vector<Gate> gates;
  std::vector<int> wires(size,-1);
  std::function<uint32_t(uint32_t)> emit=[&](uint32_t v)->uint32_t {
    if(wires[v]>=0)return wires[v];
    if(input_id[v]>=0)return wires[v]=input_id[v];
    uint32_t a=emit(left[v]),b=emit(right[v]);
    gates.push_back({op[v],a,b});return wires[v]=inputs+gates.size()-1;
  };
  uint32_t out=emit(goal);
  std::ofstream result(argv[2]);
  result<<"{\"formula_gates\":"<<int(cost[goal])<<",\"dag_gates\":"<<gates.size()<<",\"inputs\":"<<inputs<<",\"output\":"<<out<<",\"gates\":[";
  for(size_t i=0;i<gates.size();i++){
    if(i)result<<',';
    result<<"[\""<<(gates[i].op?"or":"and")<<"\","<<gates[i].a<<','<<gates[i].b<<']';
  }
  result<<"]}\n";
  std::cout<<"FOUND formula="<<int(cost[goal])<<" dag="<<gates.size()<<" seconds="<<seconds()<<std::endl;
}
