#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <unordered_map>
#include <vector>

struct DP {
  uint32_t size,full;std::vector<uint8_t> cost,op;std::vector<uint32_t> left,right;
  std::vector<std::vector<uint32_t>> bucket;
  explicit DP(uint32_t s):size(s),full(s-1),cost(s),op(s),left(s),right(s),bucket(12){}
  bool solve(const std::vector<uint32_t>& ins,int cap,uint32_t goal) {
    std::fill(cost.begin(),cost.end(),255);for(auto&b:bucket)b.clear();
    for(auto v:ins)if(cost[v]==255){cost[v]=0;bucket[0].push_back(v);}
    if(cost[goal]==0)return true;
    for(int d=1;d<=cap;d++)for(int a=0;a<=d-1-a;a++) {
      int b=d-1-a;
      for(size_t i=0;i<bucket[a].size();i++) {
        uint32_t x=bucket[a][i];size_t first=a==b?i+1:0;
        for(size_t j=first;j<bucket[b].size();j++) {
          uint32_t y=bucket[b][j],v=x&y;
          if(v&&v!=full&&cost[v]==255){cost[v]=d;op[v]=0;left[v]=x;right[v]=y;bucket[d].push_back(v);if(v==goal)return true;}
          v=x|y;
          if(v&&v!=full&&cost[v]==255){cost[v]=d;op[v]=1;left[v]=x;right[v]=y;bucket[d].push_back(v);if(v==goal)return true;}
        }
      }
    }
    return false;
  }
};

int main(int argc,char**argv) {
  if(argc<5||argc>6)return 2;
  std::ifstream input(argv[1]);int rows,ni,unused;uint32_t goal;
  input>>rows>>ni>>goal>>unused;std::vector<uint32_t> ins(ni);for(auto&v:ins)input>>v;
  double limit=std::stod(argv[4]);size_t skip=argc==6?std::stoull(argv[5]):0;
  auto start=std::chrono::steady_clock::now();
  auto seconds=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  DP base(1u<<rows),work(1u<<rows);base.solve(ins,7,goal);
  std::vector<uint32_t> cases;int initial[8]={};
  for(int d=7;d>=4;d--)for(uint32_t v=1;v<base.size;v++)if(base.cost[v]==d){cases.push_back(v);initial[d]++;}
  std::cout<<"CASES "<<cases.size()<<" skip="<<skip<<" costs4="<<initial[4]<<" costs5="<<initial[5]<<" costs6="<<initial[6]<<" costs7="<<initial[7]<<std::endl;
  int completed[8]={};size_t done=skip;bool found=false;uint32_t found_helper=0;
  struct Gate{uint8_t op;uint32_t a,b;};std::vector<Gate> gates;uint32_t out=0;
  double next_report=10;
  for(size_t i=skip;i<cases.size();i++) {
    if(seconds()>=limit)break;
    uint32_t h=cases[i];int d=base.cost[h];auto inputs=ins;inputs.push_back(h);
    bool ok=work.solve(inputs,10-d,goal);completed[d]++;done=i+1;
    if(ok) {
      std::unordered_map<uint32_t,uint32_t> wires;for(int j=0;j<ni;j++)wires[ins[j]]=j;
      std::function<uint32_t(uint32_t,DP&)> emit=[&](uint32_t v,DP& p)->uint32_t {
        auto it=wires.find(v);if(it!=wires.end())return it->second;
        uint32_t a=emit(p.left[v],p),b=emit(p.right[v],p);gates.push_back({p.op[v],a,b});
        return wires[v]=ni+gates.size()-1;
      };
      emit(h,base);out=emit(goal,work);found=true;found_helper=h;
      std::cout<<"FOUND helper="<<h<<" helper_cost="<<d<<" paid_gates="<<gates.size()<<" done="<<done<<" seconds="<<seconds()<<std::endl;
      break;
    }
    if(seconds()>=next_report){std::cout<<"PROGRESS done="<<done<<" total="<<cases.size()<<" cost="<<d<<" seconds="<<seconds()<<std::endl;next_report=seconds()+10;}
  }
  std::ofstream summary(argv[2]);summary<<"{\"total_cases\":"<<cases.size()<<",\"skip\":"<<skip<<",\"next_index\":"<<done<<",\"found\":"<<(found?"true":"false")<<",\"seconds\":"<<seconds()<<",\"completed_by_cost\":[";
  for(int d=4;d<=7;d++){if(d>4)summary<<',';summary<<completed[d];}summary<<"]}\n";
  if(found) {
    if(gates.size()>10)return 3;
    std::ofstream witness(argv[3]);witness<<"{\"inputs\":"<<ni<<",\"helper_value\":"<<found_helper<<",\"paid_size\":"<<gates.size()<<",\"output\":"<<out<<",\"gates\":[";
    for(size_t i=0;i<gates.size();i++){if(i)witness<<',';witness<<"[\""<<(gates[i].op?"or":"and")<<"\","<<gates[i].a<<','<<gates[i].b<<']';}witness<<"]}\n";
  }
  std::cout<<"FINISHED done="<<done<<" total="<<cases.size()<<" seconds="<<seconds()<<" found="<<found<<std::endl;
  return found?10:0;
}
