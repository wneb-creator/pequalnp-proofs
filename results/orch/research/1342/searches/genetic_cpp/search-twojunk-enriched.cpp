#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <sys/resource.h>
#include <vector>
using U = uint64_t;
struct Gate { int op, a, b; };
struct Circuit { std::array<Gate,40> g{}; int output=0; };
struct Problem {
  int P,L,n,s; std::vector<std::pair<int,int>> edges;
  std::vector<std::pair<unsigned,bool>> rows; std::vector<unsigned> covers;
  std::array<U,16> inputs{}; U target=0, mask=0;
};
std::mt19937_64 rng;
int randn(int n) { return int(rng()%unsigned(n)); }
bool truth(const Problem& p,unsigned x) {
  for(auto [a,b]:p.edges) if((x&(1u<<a))&&(x&(1u<<b)))return true;
  return false;
}
Problem make_problem(std::string name) {
  Problem p;
  if(name=="theta") {
    p.P=p.L=4;
    p.edges={{0,5},{0,6},{0,7},{1,4},{1,7},{2,4},{2,6},{3,4},{3,5}};
  } else if(name=="fano") {
    p.P=p.L=7;
    for(int a=0;a<7;a++)for(int b=0;b<7;b++) {
      int d=(a-b+7)%7;if(d==0||d==1||d==3)p.edges.emplace_back(a,7+b);
    }
  } else if(name=="eleven") {
    p.P=11;p.L=0;
    p.edges={{0,9},{0,10},{1,4},{1,8},{2,5},{2,10},{3,6},{3,7},{4,8},{4,10},{5,8},{5,9},{6,7},{6,10},{7,9},{8,9}};
  } else throw std::runtime_error("unknown problem");
  p.n=p.P+p.L;
  int tau=p.n;
  for(unsigned x=0;x<(1u<<p.n);x++) {
    bool cover=true;for(auto [a,b]:p.edges)if(!(x&(1u<<a))&&!(x&(1u<<b)))cover=false;
    if(cover) {
      int k=std::popcount(x);
      if(k<tau){tau=k;p.covers.clear();}
      if(k==tau)p.covers.push_back(x);
    }
  }
  p.s=int(p.edges.size())+tau-2;
  for(auto [a,b]:p.edges)p.rows.emplace_back((1u<<a)|(1u<<b),true);
  for(unsigned x=0;x<(1u<<p.n);x++)if(!truth(p,x)) {
    bool maximal=true;
    for(int i=0;i<p.n;i++)if(!(x&(1u<<i))&&!truth(p,x|(1u<<i)))maximal=false;
    if(maximal)p.rows.emplace_back(x,false);
  }
  if(name=="eleven") {
    std::array<std::vector<unsigned>,16> unique;
    for(unsigned x=0;x<(1u<<p.n);x++) {
      int count=0,last=0;
      for(int i=0;i<int(p.edges.size());i++){auto[a,b]=p.edges[i];if((x&(1u<<a))&&(x&(1u<<b))){count++;last=i;}}
      if(count==1&&std::popcount(x)>2)unique[last].push_back(x);
    }
    for(int i=0;i<16;i++)if(!unique[i].empty())p.rows.emplace_back(unique[i][randn(unique[i].size())],true);
    while(p.rows.size()<64) {
      int i=randn(16);if(unique[i].empty())continue;unsigned x=unique[i][randn(unique[i].size())];
      if(std::none_of(p.rows.begin(),p.rows.end(),[&](auto row){return row.first==x;}))p.rows.emplace_back(x,true);
    }
  }
  if(p.rows.size()>64)throw std::runtime_error("fitness mask exceeds 64 bits");
  for(size_t j=0;j<p.rows.size();j++) {
    auto [x,y]=p.rows[j];p.mask|=U(1)<<j;
    if(y)p.target|=U(1)<<j;
    for(int i=0;i<p.n;i++)if(x&(1u<<i))p.inputs[i]|=U(1)<<j;
  }
  return p;
}
U evaluate(const Problem& p,const Circuit& c,int* junk=nullptr,int* activejunk=nullptr,int* duplicates=nullptr) {
  int j=0,aj=0,dups=0;
  std::array<bool,64> used{};used[c.output]=true;
  if(activejunk)for(int i=p.s-1;i>=0;i--)if(used[p.n+i])used[c.g[i].a]=used[c.g[i].b]=true;
  std::array<U,64> w{};
  std::copy_n(p.inputs.begin(),p.n,w.begin());
  for(int i=0;i<p.s;i++) {
    const auto& g=c.g[i];
    w[p.n+i]=g.op?(w[g.a]|w[g.b]):(w[g.a]&w[g.b]);
    if(!g.op&&(w[p.n+i]&p.mask&~p.target)){j++;if(used[p.n+i])aj++;}
    if(duplicates){for(int k=0;k<p.n+i;k++)if((w[k]&((U(1)<<40)-1))==(w[p.n+i]&((U(1)<<40)-1))){dups++;break;}}
  }
  if(junk)*junk=j;
  if(activejunk)*activejunk=aj;
  if(duplicates)*duplicates=dups;
  return w[c.output]&p.mask;
}
int active(const Problem& p,const Circuit& c,std::array<int,40>* list=nullptr) {
  std::array<bool,64> used{};used[c.output]=true;int count=0;
  for(int i=p.s-1;i>=0;i--)if(used[p.n+i]) {
    if(list)(*list)[count]=i;
    count++;
    used[c.g[i].a]=used[c.g[i].b]=true;
  }
  return count;
}
Circuit seed_circuit(const Problem& p) {
  unsigned cover=p.covers[randn(p.covers.size())];
  std::array<std::vector<int>,16> leaves;
  for(auto [a,b]:p.edges) {
    bool aa=cover&(1u<<a),bb=cover&(1u<<b);
    int center=aa&&bb?(randn(2)?a:b):(aa?a:b);
    leaves[center].push_back(center==a?b:a);
  }
  std::vector<int> centers;for(int i=0;i<p.n;i++)if(!leaves[i].empty())centers.push_back(i);
  std::shuffle(centers.begin(),centers.end(),rng);
  std::vector<Gate> gs;std::vector<int> stars;
  auto gate=[&](int op,int a,int b){gs.push_back({op,a,b});return p.n+int(gs.size())-1;};
  auto fold_or=[&](std::vector<int> xs) {
    while(xs.size()>1) {
      int j=randn(xs.size());int a=xs[j];xs.erase(xs.begin()+j);
      j=randn(xs.size());int b=xs[j];xs.erase(xs.begin()+j);
      xs.push_back(gate(1,a,b));
    }
    return xs[0];
  };
  for(int center:centers)stars.push_back(gate(0,center,fold_or(leaves[center])));
  int output=fold_or(stars);
  if(int(gs.size())!=p.s+1)throw std::runtime_error("canonical size mismatch");
  int removed=randn(gs.size());int wire=p.n+removed;
  int replacement=randn(2)?gs[removed].a:gs[removed].b;
  auto remap=[&](int a){return a==wire?replacement:a-(a>wire);};
  Circuit c;int k=0;
  for(int i=0;i<int(gs.size());i++)if(i!=removed) {
    c.g[k++]={gs[i].op,remap(gs[i].a),remap(gs[i].b)};
  }
  c.output=remap(output);return c;
}

Circuit known_seed(const Problem& p,int variant) {
 Circuit c;int k=0;
 auto gate=[&](int op,int a,int b){c.g[k++]={op,a,b};return p.n+k-1;};
 auto OR=[&](int a,int b){return gate(1,a,b);};
 auto AND=[&](int a,int b){return gate(0,a,b);};
 int ja=OR(7,10),jb=OR(6,9),j=AND(ja,jb);
 int t1=OR(5,10),u1=OR(t1,j),a=AND(2,u1);
 int t2=OR(9,10),b=AND(0,t2);
 int t3=OR(8,j),u3=OR(4,5),d=AND(t3,u3);
 int t4=OR(4,8),u4=OR(1,j),e=AND(t4,u4);
 int t5=OR(6,7),u5=variant?OR(3,j):3,f=AND(u5,t5);
 int ab=OR(a,b),de=OR(d,e),abde=OR(ab,de);c.output=OR(abde,f);
 while(k<p.s)gate(randn(2),randn(p.n+k),randn(p.n+k));
 if(k!=p.s)throw std::runtime_error("known seed size mismatch");
 return c;
}


Circuit rich_seed(const Problem& p) {
 std::vector<Gate> gs={
{1,1,4},
{1,1,8},
{0,11,12},
{1,4,8},
{0,13,14},
{1,3,6},
{1,3,7},
{0,16,17},
{1,6,7},
{0,18,19},
{1,2,8},
{1,21,9},
{0,5,22},
{1,0,7},
{1,24,8},
{0,9,25},
{1,0,2},
{1,27,4},
{1,28,6},
{0,10,29},
{1,15,20},
{1,31,23},
{1,32,26},
{1,33,30}};
 int output=34;
 while(int(gs.size())>p.s) {
   int r=randn(gs.size()),wire=p.n+r,replacement=randn(2)?gs[r].a:gs[r].b;
   auto map=[&](int a){return a==wire?replacement:a-(a>wire);};
   std::vector<Gate> h;
   for(int i=0;i<int(gs.size());i++)if(i!=r)h.push_back({gs[i].op,map(gs[i].a),map(gs[i].b)});
   output=map(output);gs=h;
 }
 Circuit c;std::copy(gs.begin(),gs.end(),c.g.begin());c.output=output;return c;
}


Circuit prefix_seed(const Problem& p) {
 std::vector<Gate> gs={
{1,8,0},
{1,9,4},
{0,11,12},
{1,8,9},
{0,13,14},
{1,7,10},
{1,6,9},
{0,16,17},
{1,6,7},
{1,3,18},
{0,19,20},
{1,4,8},
{0,1,22},
{1,2,14},
{0,5,24},
{1,0,2},
{1,26,4},
{0,10,27},
{1,15,21},
{1,29,23},
{1,30,25},
{1,31,28}};
 int output=32;
 while(int(gs.size())>p.s) {
   int r;do{r=3+randn(gs.size()-3);}while(r==5||r==6||r==7);
   int wire=p.n+r,replacement=randn(2)?gs[r].a:gs[r].b;
   auto map=[&](int a){return a==wire?replacement:a-(a>wire);};
   std::vector<Gate> h;
   for(int i=0;i<int(gs.size());i++)if(i!=r)h.push_back({gs[i].op,map(gs[i].a),map(gs[i].b)});
   output=map(output);gs=h;
 }
 Circuit c;std::copy(gs.begin(),gs.end(),c.g.begin());c.output=output;return c;
}

Circuit random_circuit(const Problem& p) {
  Circuit c;for(int i=0;i<p.s;i++)c.g[i]={randn(2),randn(p.n+i),randn(p.n+i)};
  c.output=p.n+p.s-1;return c;
}
void reorder(const Problem& p,Circuit& c) {
  Circuit d;std::array<int,64> mapping;mapping.fill(-1);
  std::iota(mapping.begin(),mapping.begin()+p.n,0);
  std::array<bool,40> done{};
  for(int k=0;k<p.s;k++) {
    std::array<int,40> available;int count=0;
    for(int i=0;i<p.s;i++)if(!done[i]&&mapping[c.g[i].a]>=0&&mapping[c.g[i].b]>=0)available[count++]=i;
    if(!count)throw std::runtime_error("cycle in legal genome");
    int i=available[randn(count)];done[i]=true;auto g=c.g[i];
    d.g[k]={g.op,mapping[g.a],mapping[g.b]};mapping[p.n+i]=p.n+k;
  }
  d.output=mapping[c.output];c=d;
}
void mutate(const Problem& p,Circuit& c,int mode) {
  std::array<int,40> acts;int count=active(p,c,&acts);
  int changes=1+(randn(100)<22)+(randn(100)<7);
  for(int r=0;r<changes;r++) {
    if(randn(100)<2) {c.output=randn(p.n+p.s);continue;}
    int i=(count&&randn(100)<85)?acts[randn(count)]:randn(p.s);
    int field=randn(3);
    if(field==0)c.g[i].op^=1;
    else if(field==1)c.g[i].a=randn(p.n+i);
    else c.g[i].b=randn(p.n+i);
  }
  if(mode>=2&&randn(256)==0)reorder(p,c);
}
bool full_validate(const Problem& p,const Circuit& c) {
  for(int i=0;i<p.s;i++)if(c.g[i].a<0||c.g[i].b<0||c.g[i].a>=p.n+i||c.g[i].b>=p.n+i)return false;
  for(unsigned x=0;x<(1u<<p.n);x++) {
    std::array<bool,64>w{};for(int i=0;i<p.n;i++)w[i]=x&(1u<<i);
    for(int i=0;i<p.s;i++){auto g=c.g[i];w[p.n+i]=g.op?(w[g.a]||w[g.b]):(w[g.a]&&w[g.b]);}
    if(w[c.output]!=truth(p,x))return false;
  }
  return true;
}
void save(const Problem& p,const Circuit& c,const std::string& path,int errors,U mismatch,unsigned long long attempts) {
  std::ofstream o(path);o<<"{\n\"P\":"<<p.P<<",\"L\":"<<p.L<<",\"size\":"<<p.s<<",\"errors\":"<<errors<<",\"output\":"<<c.output<<",\"attempts\":"<<attempts<<",\n\"edges\":[";
  for(size_t i=0;i<p.edges.size();i++){if(i)o<<",";o<<"["<<p.edges[i].first<<","<<p.edges[i].second<<"]";}
  int junk=0;evaluate(p,c,&junk);o<<"],\n\"junk\":"<<junk<<",\n\"gates\":[";
  for(int i=0;i<p.s;i++){if(i)o<<",";auto g=c.g[i];o<<"["<<g.op<<","<<g.a<<","<<g.b<<"]";}
  o<<"],\n\"wrong_rows\":[";bool first=true;
  for(size_t i=0;i<p.rows.size();i++)if(mismatch&(U(1)<<i)){if(!first)o<<",";first=false;o<<"["<<p.rows[i].first<<","<<p.rows[i].second<<"]";}
  o<<"]\n}\n";
}
int main(int argc,char**argv) {
  if(argc!=6){std::cerr<<"usage: search eleven|theta|fano seconds seed mode output.json\n";return 2;}
  std::string name=argv[1];int seconds=std::stoi(argv[2]);unsigned long long seed=std::stoull(argv[3]);int mode=std::stoi(argv[4]);
  if(seconds<1||seconds>60)throw std::runtime_error("burst limit 1..60 seconds");
  struct rlimit memory{900ULL*1024*1024,900ULL*1024*1024};setrlimit(RLIMIT_AS,&memory);
  struct rlimit cpu{(rlim_t)seconds+10,(rlim_t)seconds+10};setrlimit(RLIMIT_CPU,&cpu);
  rng.seed(seed);auto p=make_problem(name);
  auto start=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
  std::cout<<"START "<<name<<" seed="<<seed<<" mode="<<mode<<" target_size="<<p.s<<" rows="<<p.rows.size()<<" covers="<<p.covers.size()<<std::endl;
  std::array<bool,64> savedRows{};
  int best=10000,weight=1;double nextLog=10,nextRestart=0;unsigned long long attempts=0,accepted=0,restarts=0;
  Circuit current,bestc;U cur=0;int score=0;
  std::array<Circuit,64> archive;int archived=0;
  auto weighted=[&](U value,int junk,int aj,int dups){int err=std::popcount((value^p.target)&p.target)+weight*std::popcount((value^p.target)&~p.target);return 16*err+(mode==3?2*std::abs(junk-2)+2*std::abs(aj-2):0)+dups;};
  while(true) {
    double t=elapsed();if(t>=seconds)break;
    if(t>=nextRestart) {
      weight=1+randn(3);
      if(archived&&randn(100)<35)current=archive[randn(archived)];
      else if(name=="eleven"&&randn(100)<95)current=prefix_seed(p);
      else if(name=="eleven"&&randn(100)<40)current=rich_seed(p);
      else if(name=="eleven"&&randn(100)<60)current=known_seed(p,randn(2));
      else current=randn(100)<95?seed_circuit(p):random_circuit(p);
      for(int i=0;i<p.s;i++)while(current.g[i].a==current.g[i].b)current.g[i].b=randn(p.n+i);
      if(mode>=1)reorder(p,current);
      int junk,aj,dups;cur=evaluate(p,current,&junk,&aj,&dups);score=weighted(cur,junk,aj,dups);restarts++;
      nextRestart=t+(mode==0?.15:.4)+(rng()%400)/1000.;
    }
    Circuit candidate=current;mutate(p,candidate,mode);
    bool equal=false;for(int i=0;i<p.s;i++)if(candidate.g[i].a==candidate.g[i].b)equal=true;
    if(equal)continue;
    int junk,aj,dups;U value=evaluate(p,candidate,&junk,&aj,&dups);int es=std::popcount(value^p.target);int ws=weighted(value,junk,aj,dups);attempts++;
    if(ws<=score||(mode==1&&randn(20000)==0)||(mode>=2&&ws<=score+4&&randn(10000)==0)) {
      current=candidate;cur=value;score=ws;accepted++;
    }
    if(es==1&&junk==2&&aj==2&&dups==0){int row=std::countr_zero(value^p.target);if(!savedRows[row]){savedRows[row]=true;save(p,candidate,std::string(argv[5])+".row-"+std::to_string(row)+".json",es,value^p.target,attempts);std::cout<<"IRREDUNDANT_TWO_JUNK_NEAR row="<<row<<" attempts="<<attempts<<std::endl;}}
    if(es<best) {
      best=es;bestc=candidate;archived=0;
      save(p,candidate,argv[5],best,value^p.target,attempts);
      std::cout<<"BEST errors="<<best<<" junk="<<junk<<" duplicate_columns="<<dups<<" active="<<active(p,candidate)<<" attempts="<<attempts<<" elapsed="<<t<<std::endl;
      if(best==0) {
        bool ok=full_validate(p,candidate);std::cout<<"ZERO_FITNESS full_truth="<<ok<<" junk="<<junk<<" assignments="<<(1u<<p.n)<<std::endl;
        return ok?0:3;
      }
    }
    if(es==best&&junk==2&&aj==2&&dups==0&&randn(128)==0) {archive[randn(64)]=candidate; if(archived<64)archive[archived++]=candidate;}
    if(t>=nextLog){std::cout<<"PROGRESS seconds="<<t<<" attempts="<<attempts<<" accepted="<<accepted<<" best="<<best<<" restarts="<<restarts<<std::endl;nextLog+=10;}
  }
  struct rusage u{};getrusage(RUSAGE_SELF,&u);
  std::cout<<"FINISH seconds="<<elapsed()<<" attempts="<<attempts<<" best="<<best<<" restarts="<<restarts<<" rss_kib="<<u.ru_maxrss<<" status=heuristic_no_witness"<<std::endl;
  return 0;
}
