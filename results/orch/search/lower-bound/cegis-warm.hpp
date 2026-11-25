#include <algorithm>
#include <limits>
#include <map>
#include <queue>
#include <tuple>

struct WarmBuilder {
  std::vector<Gate> gates;
  std::map<unsigned,int> sums;
  WarmBuilder() {
    for (int i=0;i<14;++i) sums[1u<<i]=i;
    append(0,1,true); sums[3]=14;
    append(0,2,true); sums[5]=15;
  }
  int append(int a,int b,bool is_or) {
    if(a>b) std::swap(a,b);
    gates.push_back({a,b,is_or}); return 13+(int)gates.size();
  }
  int raw_sum(unsigned wanted) {
    if(auto it=sums.find(wanted);it!=sums.end()) return it->second;
    std::vector<std::pair<unsigned,int>> usable;
    for(auto entry:sums) if((entry.first & wanted)==entry.first) usable.push_back(entry);
    std::vector<int> dist(1<<14,-1), previous(1<<14,-1), used(1<<14,-1);
    std::queue<unsigned> pending; pending.push(0);dist[0]=0;
    while(!pending.empty() && dist[wanted]<0) {
      unsigned m=pending.front();pending.pop();
      for(auto entry:usable) {
        unsigned next=m|entry.first;
        if(dist[next]>=0) continue;
        dist[next]=dist[m]+1; previous[next]=m; used[next]=entry.second; pending.push(next);
      }
    }
    if(dist[wanted]<0) throw std::runtime_error("raw sum is unreachable");
    std::vector<int> wires;
    for(unsigned m=wanted;m;m=previous[m]) wires.push_back(used[m]);
    std::reverse(wires.begin(),wires.end());
    int wire=wires.front(); unsigned mask=0;
    for(auto entry:sums) if(entry.second==wire) {mask=entry.first;break;}
    for(int i=1;i<(int)wires.size();++i) {
      unsigned next=0;
      for(auto entry:sums) if(entry.second==wires[i]) {next=entry.first;break;}
      mask|=next;
      if(auto it=sums.find(mask);it!=sums.end()) wire=it->second;
      else {wire=append(wire,wires[i],true);sums[mask]=wire;}
    }
    if(mask!=wanted) throw std::runtime_error("raw sum mask mismatch");
    return wire;
  }
};

std::vector<Gate> lex_order(const std::vector<Gate>& original) {
  std::vector<Gate> result;
  std::vector<int> renamed(14+original.size(),-1);
  for(int i=0;i<14;++i) renamed[i]=i;
  for(int i=0;i<2;++i) {result.push_back(original[i]);renamed[14+i]=14+i;}
  while(result.size()<original.size()) {
    int best=-1; std::tuple<int,int,bool> best_key;
    Gate selected_gate{};
    for(int i=2;i<(int)original.size();++i) {
      if(renamed[14+i]>=0) continue;
      auto gate=original[i];
      if(renamed[gate.left]<0 || renamed[gate.right]<0) continue;
      gate.left=renamed[gate.left];gate.right=renamed[gate.right];
      if(gate.left>gate.right) std::swap(gate.left,gate.right);
      auto key=std::make_tuple(gate.left,gate.right,gate.is_or);
      if(best<0 || key<best_key) {best=i;best_key=key;selected_gate=gate;}
    }
    if(best<0) throw std::runtime_error("warm graph is cyclic");
    renamed[14+best]=14+result.size();result.push_back(selected_gate);
  }
  if(renamed.back()!=(int)renamed.size()-1) throw std::runtime_error("warm output reordered away from end");
  for(int i=1;i<(int)result.size();++i) {
    auto a=result[i-1],b=result[i];
    if(b.right!=13+i && std::make_tuple(a.left,a.right,a.is_or)>std::make_tuple(b.left,b.right,b.is_or))
      throw std::runtime_error("warm lex order failed");
  }
  return result;
}

std::vector<Gate> warm_candidate(const std::vector<Row>& rows,int budget,int& unpadded_size) {
  unsigned neighbors[7];for(auto& n:neighbors) n=127;
  for(auto row:rows) if(row.active && !row.expected)
    for(int right=0;right<7;++right) if(row.mask&(1u<<(7+right)))
      neighbors[right] &= ~(row.mask&127);
  std::map<unsigned,unsigned> groups;
  for(int right=0;right<7;++right) {
    if(!neighbors[right]) throw std::runtime_error("empty supergraph column");
    groups[neighbors[right]]|=1u<<(right+7);
  }
  WarmBuilder builder;
  std::vector<unsigned> masks;
  for(auto group:groups) masks.push_back(group.first);
  std::sort(masks.begin(),masks.end(),[](unsigned a,unsigned b) {
    return std::make_pair(__builtin_popcount(a),a)<std::make_pair(__builtin_popcount(b),b);
  });
  for(unsigned mask:masks) builder.raw_sum(mask);
  std::vector<int> terms;
  for(auto group:groups) terms.push_back(builder.append(builder.raw_sum(group.first),builder.raw_sum(group.second),false));
  int output=terms.front();
  for(int i=1;i<(int)terms.size();++i) output=builder.append(output,terms[i],true);
  unpadded_size=builder.gates.size();
  auto result=lex_order(builder.gates);
  for(auto row:rows) if(row.active && evaluate(result,row.mask)!=row.expected)
    throw std::runtime_error("warm supergraph violates an active row");
  if(unpadded_size>budget) return {};
  while((int)result.size()<budget) {int last=13+result.size();result.push_back({last,last,true});}
  return result;
}

void apply_phases(CaDiCaL::Solver& solver,const std::vector<GateVars>& structure,const std::vector<Gate>& gates) {
  if(gates.empty()) return;
  for(int i=0;i<(int)gates.size();++i) {
    const auto gate=gates[i];const auto& vars=structure[i];
    solver.phase(gate.is_or?vars.op:-vars.op);
    for(int w=0;w<(int)vars.left.size();++w) {
      solver.phase(w==gate.left?vars.left[w]:-vars.left[w]);
      solver.phase(w==gate.right?vars.right[w]:-vars.right[w]);
    }
  }
}
