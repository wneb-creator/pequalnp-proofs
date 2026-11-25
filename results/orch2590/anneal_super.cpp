#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <random>
#include <string>
#include <utility>
#include <vector>

struct Gate { int op, a, b; };
struct Net { std::vector<Gate> gs; int out; };
struct Problem {
  int n;
  std::vector<std::pair<int,int>> edges;
  std::vector<unsigned> rows;
  std::array<uint64_t, 64> inputs{};
  uint64_t mask=0, targetMask=0;
  bool target(unsigned x) const {
    for(auto [a,b]:edges) if((x>>a&1)&&(x>>b&1)) return true;
    return false;
  }
  explicit Problem(const std::string &path) {
    std::ifstream in(path); int m;
    if(!(in>>n>>m) || n>=20) throw std::runtime_error("invalid graph");
    for(int j=0;j<m;++j){int a,b;in>>a>>b;edges.emplace_back(a,b);}
    for(unsigned x=0;x<(1u<<n);++x) {
      bool y=target(x), maximal=!y;
      if(!y) for(int i=0;i<n;++i) if(!(x>>i&1)&&!target(x|(1u<<i))) {maximal=false;break;}
      if((y&&__builtin_popcount(x)==2)||maximal) rows.push_back(x);
    }
    if(rows.size()>64) throw std::runtime_error("too many rows");
    mask=rows.size()==64?~uint64_t(0):((uint64_t(1)<<rows.size())-1);
    for(unsigned r=0;r<rows.size();++r){
      if(target(rows[r])) targetMask|=uint64_t(1)<<r;
      for(int i=0;i<n;++i) if(rows[r]>>i&1) inputs[i]|=uint64_t(1)<<r;
    }
  }
  uint64_t eval(const Net &net) const {
    auto v=inputs;
    for(unsigned g=0;g<net.gs.size();++g) {
      auto [op,a,b]=net.gs[g];
      v[n+g]=op?(v[a]|v[b]):(v[a]&v[b]);
    }
    return v[net.out];
  }
  int readOneEdges(const Net &net) const {
    std::array<uint64_t,64> left{},right{},both{};
    for(unsigned e=0;e<edges.size();++e){left[edges[e].first]|=uint64_t(1)<<e;right[edges[e].second]|=uint64_t(1)<<e;}
    for(unsigned g=0;g<net.gs.size();++g){auto [op,a,b]=net.gs[g];int w=n+g;
      if(op){left[w]=left[a]|left[b];right[w]=right[a]|right[b];both[w]=both[a]|both[b];}
      else {both[w]=(left[a]&right[b])|(right[a]&left[b]);}
    }
    return __builtin_popcountll(both[net.out]);
  }
  unsigned verify(const Net &net) const {
    if(n+net.gs.size()>64 || net.out<0 || net.out>=n+int(net.gs.size()))
      throw std::runtime_error("invalid output or net capacity");
    unsigned failures=0;
    for(unsigned x=0;x<(1u<<n);++x) {
      std::array<bool,64> v{};
      for(int i=0;i<n;++i)v[i]=(x>>i)&1;
      for(unsigned g=0;g<net.gs.size();++g) {
        auto [op,a,b]=net.gs[g];
        if(a<0||b<0||a>=n+int(g)||b>=n+int(g)||op<0||op>1)
          throw std::runtime_error("invalid net");
        v[n+g]=op?(v[a]||v[b]):(v[a]&&v[b]);
      }
      failures+=v[net.out]!=target(x);
    }
    return failures;
  }
};

Net readNet(const std::string &path,int n) {
  Net net;net.out=-1;std::ifstream f(path);std::string token;
  while(f>>token){
    if(token=="output"){if(!(f>>net.out))throw std::runtime_error("invalid output record");}
    else{Gate g;g.op=std::stoi(token);if(!(f>>g.a>>g.b))throw std::runtime_error("invalid gate record");net.gs.push_back(g);}
  }
  if(net.out<0)net.out=n+int(net.gs.size())-1;
  return net;
}
void save(const Net &net,const std::string &path) {
  std::ofstream f(path);for(auto g:net.gs)f<<g.op<<" "<<g.a<<" "<<g.b<<"\n";
  f<<"output "<<net.out<<"\n";
}
Net deletion(const Net &base,int n,int at,int operand) {
  Net r; int old=n+at, replacement=operand?base.gs[at].b:base.gs[at].a;
  auto map=[&](int w){if(w==old)w=replacement;return w>old?w-1:w;};
  for(unsigned i=0;i<base.gs.size();++i)if(int(i)!=at){auto g=base.gs[i];g.a=map(g.a);g.b=map(g.b);r.gs.push_back(g);}
  r.out=map(base.out);return r;
}
int main(int argc,char**argv) {
  if(argc!=8){std::cerr<<"usage: anneal_super graph baseline seconds seed output-prefix frozen-prefix seed-manifest\n";return 2;}
  Problem p(argv[1]);Net base=readNet(argv[2],p.n);
  if(p.verify(base)){std::cerr<<"baseline verification failed\n";return 3;}
  const double seconds=std::stod(argv[3]);const uint64_t seed=std::stoull(argv[4]);
  const int frozen=std::stoi(argv[6]);
  if(frozen<0||frozen+1>=int(base.gs.size()))throw std::runtime_error("invalid frozen prefix");
  std::mt19937_64 rng(seed); const std::string prefix=argv[5];
  const auto start=std::chrono::steady_clock::now();
  auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::vector<Net> starts,archive;
  int best=1000;Net bestNet;uint64_t nearKinds=0;
  int bestNonreadErrors=1000;std::vector<Net> nonreadArchive;
  uint64_t iterations=0,restarts=0,neutral=0;
  double nextReport=10;
  auto observe=[&](const Net &net,uint64_t result){
    int errors=__builtin_popcountll(result^p.targetMask);
    if(errors==1){uint64_t bit=result^p.targetMask;if(!(nearKinds&bit)){
      nearKinds|=bit;int row=__builtin_ctzll(bit);save(net,prefix+"-near-"+std::to_string(row)+".txt");
      std::cout<<"new_near elapsed="<<elapsed()<<" row="<<row<<" input="<<p.rows[row]
        <<" target="<<p.target(p.rows[row])<<" total_kinds="<<__builtin_popcountll(nearKinds)<<"\n"<<std::flush;
    }}
    if(errors<best){best=errors;bestNet=net;save(net,prefix+"-best.txt");
      std::cout<<"best elapsed="<<elapsed()<<" errors="<<best<<" iterations="<<iterations<<" restarts="<<restarts<<"\n"<<std::flush;
      archive.clear();archive.push_back(net);
    }else if(errors==best){if(archive.size()<128)archive.push_back(net);
      else if(rng()%64==0)archive[rng()%archive.size()]=net;}
    int nonread=__builtin_popcountll(result&p.targetMask)-p.readOneEdges(net);
    if(nonread>0&&errors<bestNonreadErrors){bestNonreadErrors=errors;nonreadArchive.clear();save(net,prefix+"-nonread-best.txt");
      std::cout<<"nonread_best elapsed="<<elapsed()<<" errors="<<errors<<" nonread_edges="<<nonread<<"\n"<<std::flush;}
    if(nonread>0&&errors==bestNonreadErrors){if(nonreadArchive.size()<128)nonreadArchive.push_back(net);
      else if(rng()%64==0)nonreadArchive[rng()%nonreadArchive.size()]=net;}
    if(errors==0){unsigned bad=p.verify(net);std::cout<<"EXACT rows="<<p.rows.size()<<" all_assignments_failures="<<bad<<"\n"<<std::flush;
      if(bad)throw std::runtime_error("extremal verification contradiction");
      save(net,prefix+"-witness.txt");return true;}
    return false;
  };
  std::cout<<"seed="<<seed<<" inputs="<<p.n<<" gates="<<base.gs.size()-1<<" rows="<<p.rows.size()<<" baseline_all_assignments=PASS\n"<<std::flush;
  for(unsigned g=frozen;g<base.gs.size();++g)for(int side=0;side<2;++side){
    starts.push_back(deletion(base,p.n,g,side));if(observe(starts.back(),p.eval(starts.back())))return 0;
  }
  starts.clear();
  std::ifstream manifest(argv[7]);std::string seedPath;
  while(std::getline(manifest,seedPath)){if(seedPath.empty())continue;
    Net net=readNet(seedPath,p.n);
    if(net.gs.size()+1!=base.gs.size())throw std::runtime_error("seed size mismatch");
    unsigned failures=p.verify(net);
    if((p.eval(net)&p.targetMask)!=p.targetMask)throw std::runtime_error("seed rejects positive edge");
    starts.push_back(net);
    std::cout<<"import_seed index="<<starts.size()-1<<" all_failures="<<failures<<"\n"<<std::flush;
    if(observe(net,p.eval(net)))return 0;
  }
  if(starts.empty())throw std::runtime_error("empty seed manifest");
  const int epoch=100000;
  while(elapsed()<seconds){
    ++restarts;
    Net current=starts[rng()%starts.size()];
    bool demandNonread=false;
    int positiveWeight=16+int(rng()%16), negativeWeight=1;
    auto score=[&](const Net &net,uint64_t v){uint64_t wrong=v^p.targetMask;
      int penalty=demandNonread&&(__builtin_popcountll(v&p.targetMask)==p.readOneEdges(net))?3:0;
      return positiveWeight*__builtin_popcountll(wrong&p.targetMask)+
        negativeWeight*__builtin_popcountll(wrong&(~p.targetMask)&p.mask)+penalty;};
    int currentScore=score(current,p.eval(current));
    double initialTemperature=0.5+double(rng()%800)/100.;
    for(int step=0;step<epoch;++step){
      ++iterations;Net candidate=current;
      int mutations=(rng()%100<82)?1:((rng()%4==0)?3:2);
      for(int j=0;j<mutations;++j){
        int index=frozen+rng()%(candidate.gs.size()-frozen);int kind=rng()%10;
        auto &g=candidate.gs[index];
        if(kind<4)g.a=rng()%(p.n+index);
        else if(kind<8)g.b=rng()%(p.n+index);
        else if(kind==8)g.op^=1;
        else if(rng()%4==0)candidate.out=rng()%(p.n+candidate.gs.size());
        else if(rng()%2==0&&index+1<int(candidate.gs.size())&&
          candidate.gs[index+1].a!=p.n+index&&candidate.gs[index+1].b!=p.n+index){
          std::swap(candidate.gs[index],candidate.gs[index+1]);
          auto swapWire=[&](int w){if(w==p.n+index)return w+1;if(w==p.n+index+1)return w-1;return w;};
          for(unsigned j=index+2;j<candidate.gs.size();++j){candidate.gs[j].a=swapWire(candidate.gs[j].a);candidate.gs[j].b=swapWire(candidate.gs[j].b);}
          candidate.out=swapWire(candidate.out);
        }else {g.a=rng()%(p.n+index);g.b=rng()%(p.n+index);g.op=rng()%2;}
      }
      uint64_t value=p.eval(candidate);int candidateScore=score(candidate,value);
      double temperature=initialTemperature*std::pow(0.025,double(step)/epoch);
      int delta=candidateScore-currentScore;
      if(delta<=0||double(rng()>>11)*0x1.0p-53<std::exp(-double(delta)/temperature)){
        neutral+=delta==0;current=std::move(candidate);currentScore=candidateScore;
        if(observe(current,value))return 0;
      }
      if((iterations&65535)==0){double time=elapsed();
        if(time>=nextReport){std::cout<<"progress elapsed="<<time<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<" neutral="<<neutral<<" archive="<<archive.size()<<"\n"<<std::flush;nextReport=time+10;}
        if(time>=seconds)break;
      }
    }
  }
  std::cout<<"DONE elapsed="<<elapsed()<<" iterations="<<iterations<<" restarts="<<restarts<<" best="<<best<<" best_all_failures="<<p.verify(bestNet)<<"\n"<<std::flush;
  return 1;
}
