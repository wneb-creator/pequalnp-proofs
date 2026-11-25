#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>

struct Gate {int a,b;bool is_or;};
using Net=std::vector<Gate>;
struct Graph {
  std::string name;int p,l,n,tau,budget,best=10000;
  std::vector<std::pair<int,int>> edges;
  std::vector<unsigned> covers,cases;
  uint64_t inputs[16]{},target;
};
std::mt19937_64 rng(4675163);
std::vector<Graph> graphs;

bool prepare(Graph& g) {
  g.n=g.p+g.l;g.tau=g.n;
  for(unsigned s=0;s<(1u<<g.n);++s) {
    bool cover=true,independent=true;
    for(auto [a,b]:g.edges) {
      if(!(s&(1u<<a))&&!(s&(1u<<b)))cover=false;
      if((s&(1u<<a))&&(s&(1u<<b)))independent=false;
    }
    if(cover) {
      int k=__builtin_popcount(s);
      if(k<g.tau) {g.tau=k;g.covers.clear();}
      if(k==g.tau)g.covers.push_back(s);
    }
    if(independent) {
      bool maximal=true;
      for(int v=0;v<g.n;++v)if(!(s&(1u<<v))) {
        bool neighbor=false;
        for(auto [a,b]:g.edges)if((a==v&&(s&(1u<<b)))||(b==v&&(s&(1u<<a))))neighbor=true;
        if(!neighbor){maximal=false;break;}
      }
      if(maximal)g.cases.push_back(s);
    }
  }
  for(auto [a,b]:g.edges)g.cases.insert(g.cases.begin(),(1u<<a)|(1u<<b));
  if(g.cases.size()>64)return false;
  g.budget=g.edges.size()+g.tau-2;
  if(g.budget<2||g.budget>60)return false;
  for(int i=0;i<g.n;++i)for(unsigned k=0;k<g.cases.size();++k)if(g.cases[k]&(1u<<i))g.inputs[i]|=uint64_t(1)<<k;
  g.target=(uint64_t(1)<<g.edges.size())-1;
  return true;
}

Net seed(const Graph& g) {
  unsigned cover=g.covers[rng()%g.covers.size()];
  std::vector<int> centres;
  for(int i=0;i<g.n;++i)if(cover&(1u<<i))centres.push_back(i);
  std::shuffle(centres.begin(),centres.end(),rng);
  std::vector<std::vector<int>> leaves(g.n);
  for(auto [a,b]:g.edges) {
    if((cover&(1u<<a))&&(!(cover&(1u<<b))||rng()%2))leaves[a].push_back(b);
    else leaves[b].push_back(a);
  }
  Net full;std::vector<int> outputs;std::vector<int> removable;
  for(int c:centres) {
    if(leaves[c].empty())std::abort();
    std::shuffle(leaves[c].begin(),leaves[c].end(),rng);
    int w=leaves[c][0];
    for(unsigned j=1;j<leaves[c].size();++j){int next=g.n+full.size();removable.push_back(full.size());full.push_back({w,leaves[c][j],true});w=next;}
    outputs.push_back(g.n+full.size());full.push_back({c,w,false});
  }
  while(outputs.size()>1) {
    std::shuffle(outputs.begin(),outputs.end(),rng);
    int a=outputs.back();outputs.pop_back();int b=outputs.back();outputs.pop_back();
    outputs.push_back(g.n+full.size());full.push_back({a,b,true});
  }
  if(int(full.size())!=g.budget+1||removable.empty())std::abort();
  int remove=removable[rng()%removable.size()];int replacement=rng()%2?full[remove].a:full[remove].b;
  auto remap=[&](int w){if(w==g.n+remove)w=replacement;return w>g.n+remove?w-1:w;};
  Net net;for(int j=0;j<int(full.size());++j)if(j!=remove)net.push_back({remap(full[j].a),remap(full[j].b),full[j].is_or});
  return net;
}

struct Quality {int positive,negative,mixed,active;};
Quality quality(const Graph& g,const Net& net) {
  uint64_t values[80];unsigned colors[80];bool active[80]{};
  active[g.n+g.budget-1]=true;
  for(int j=g.budget-1;j>=0;--j)if(active[g.n+j]){active[net[j].a]=true;active[net[j].b]=true;}
  for(int i=0;i<g.n;++i){values[i]=g.inputs[i];colors[i]=i<g.p?1:2;}
  int mixed=0,activity=0;
  for(int j=0;j<g.budget;++j) {
    auto z=net[j];
    values[g.n+j]=z.is_or?(values[z.a]|values[z.b]):(values[z.a]&values[z.b]);
    colors[g.n+j]=z.is_or?(colors[z.a]|colors[z.b]):0;
    if(active[g.n+j]){mixed+=colors[g.n+j]==3;++activity;}
  }
  return {__builtin_popcountll(g.target&~values[g.n+g.budget-1]),
    __builtin_popcountll(values[g.n+g.budget-1]&~g.target),mixed,activity};
}

void witness(const Graph& g,const Net& net) {
  std::cout<<"WITNESS "<<g.name<<" p="<<g.p<<" l="<<g.l<<" output="<<g.n+g.budget-1<<" expected="<<g.budget+1<<'\n';
  for(auto [a,b]:g.edges)std::cout<<"EDGE "<<a<<' '<<b-g.p<<'\n';
  for(auto z:net)std::cout<<(z.is_or?"OR ":"AND ")<<z.a<<' '<<z.b<<'\n';
  std::cout.flush();
}

void add(Graph g){if(prepare(g))graphs.push_back(g);}
int main(int argc,char**argv) {
  int seconds=argc>1?std::atoi(argv[1]):600;
  for(int k=3;k<=6;++k){Graph g;g.name="cycle"+std::to_string(2*k);g.p=g.l=k;for(int a=0;a<k;++a){g.edges.emplace_back(a,k+a);g.edges.emplace_back(a,k+(a+1)%k);}add(g);}
  {Graph g;g.name="theta333";g.p=g.l=4;for(int i=1;i<4;++i){g.edges.emplace_back(0,4+i);g.edges.emplace_back(i,4+i);g.edges.emplace_back(i,4);}add(g);}
  for(int count:{5,6}){Graph g;g.name="subdivisionK4_"+std::to_string(count);g.p=4;g.l=count;int b=4;for(int a=0;a<4;++a)for(int aa=a+1;aa<4;++aa)if(b<4+count){g.edges.emplace_back(a,b);g.edges.emplace_back(aa,b);++b;}add(g);}
  std::set<uint64_t> used;
  for(auto [p,l]:{std::pair{5,5},std::pair{5,6},std::pair{6,6}})for(int trial=0,accepted=0;trial<10000&&accepted<16;++trial){
    std::vector<std::pair<int,int>> candidates;for(int a=0;a<p;++a)for(int b=0;b<l;++b)candidates.emplace_back(a,p+b);std::shuffle(candidates.begin(),candidates.end(),rng);
    Graph g;g.p=p;g.l=l;bool adj[16][16]{};
    for(auto [a,b]:candidates){bool four=false;for(int aa=0;aa<p;++aa)for(int bb=p;bb<p+l;++bb)if(aa!=a&&bb!=b&&adj[a][bb]&&adj[aa][bb]&&adj[aa][b])four=true;if(!four){g.edges.emplace_back(a,b);adj[a][b]=true;}}
    bool good=true;for(int v=0;v<p+l;++v){int degree=0;for(auto [a,b]:g.edges)degree+=a==v||b==v;if(degree<2)good=false;}
    uint64_t mask=0;for(auto [a,b]:g.edges)mask|=uint64_t(1)<<(a*l+b-p);
    if(!good||!used.insert(mask|(uint64_t(p)<<56)|(uint64_t(l)<<60)).second)continue;
    g.name="random"+std::to_string(p)+"x"+std::to_string(l)+"_"+std::to_string(accepted);
    if(prepare(g)){graphs.push_back(g);++accepted;}
  }
  for(const auto& g:graphs)std::cout<<"GRAPH "<<g.name<<" p="<<g.p<<" l="<<g.l<<" E="<<g.edges.size()<<" tau="<<g.tau<<" budget="<<g.budget<<" cases="<<g.cases.size()<<std::endl;
  auto started=std::chrono::steady_clock::now();uint64_t iterations=0,restarts=0;
  while(std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<seconds) {
    Graph& g=graphs[restarts%graphs.size()];++restarts;Net current=seed(g);
    int weights[]={10,25,50,100,200,400};int neg=weights[rng()%6],act=rng()%4==0?1:0;
    auto score=[&](Quality q){return 100*q.positive+neg*q.negative+300*q.mixed+act*q.active;};
    int best=score(quality(g,current));
    for(int local=0;local<100000;++local){Net candidate=current;int changes=1+(rng()%8==0)+(rng()%32==0?2:0);for(int k=0;k<changes;++k){int j=rng()%g.budget,kind=rng()%3;if(kind==0)candidate[j].is_or=!candidate[j].is_or;else if(kind==1)candidate[j].a=rng()%(g.n+j);else candidate[j].b=rng()%(g.n+j);}
      Quality q=quality(g,candidate);int value=score(q),exact=q.positive+q.negative+100*q.mixed;++iterations;
      if(exact<g.best){g.best=exact;std::cout<<"BEST "<<g.name<<" errors="<<exact<<" positive="<<q.positive<<" negative="<<q.negative<<" mixed="<<q.mixed<<" active="<<q.active<<std::endl;}
      if(exact==0){witness(g,candidate);return 1;}
      if(value<=best||(rng()%1000==0&&value<=best+200)){current=std::move(candidate);best=value;}
    }
    if(restarts%500==0)std::cout<<"PROGRESS restarts="<<restarts<<" iterations="<<iterations<<std::endl;
  }
  std::cout<<"NO WITNESS restarts="<<restarts<<" iterations="<<iterations<<" graphs="<<graphs.size()<<std::endl;
}
